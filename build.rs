// Copyright © 2016–2018 University of Malta

// This program is free software: you can redistribute it and/or
// modify it under the terms of the GNU Lesser General Public License
// as published by the Free Software Foundation, either version 3 of
// the License, or (at your option) any later version.
//
// This program is distributed in the hope that it will be useful, but
// WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU
// General Public License for more details.
//
// You should have received a copy of the GNU Lesser General Public
// License and a copy of the GNU General Public License along with
// this program. If not, see <http://www.gnu.org/licenses/>.

use std::env;
use std::ffi::OsString;
use std::fs::{self, File};
use std::io::{Result as IoResult, Write};
use std::path::{Path, PathBuf};
use std::process::Command;

struct Environment {
    out_dir: PathBuf,
    rustc: OsString,
}

fn main() {
    let env = Environment {
        out_dir: PathBuf::from(cargo_env("OUT_DIR")),
        rustc: cargo_env("RUSTC"),
    };
    env.check_feature("int_128", TRY_INT_128, "i128_type, i128");
    env.check_feature("try_from", TRY_TRY_FROM, "try_from");
    env.check_ffi_panic_aborts();
    if env::var_os("CARGO_FEATURE_GMP_MPFR_SYS").is_some() {
        let bits = env::var_os("DEP_GMP_LIMB_BITS")
            .expect("DEP_GMP_LIMB_BITS not set by gmp-mfpr-sys");
        let bits = bits
            .to_str()
            .expect("DEP_GMP_LIMB_BITS contains unexpected characters");
        if bits != "32" && bits != "64" {
            panic!("Limb bits not 32 or 64: \"{}\"", bits);
        }
        println!("cargo:rustc-cfg=gmp_limb_bits_{}", bits);
    }
}

impl Environment {
    fn check_feature(&self, name: &str, contents: &str, features: &str) {
        let try_dir = self.out_dir.join(format!("try_{}", name));
        let filename = format!("try_{}.rs", name);
        create_dir_or_panic(&try_dir);

        enum Iteration {
            Stable,
            Unstable,
        }

        for i in &[Iteration::Stable, Iteration::Unstable] {
            let s;
            let file_contents = match *i {
                Iteration::Stable => contents,
                Iteration::Unstable => {
                    s = format!("#![feature({})]\n{}", features, contents);
                    &s
                }
            };
            create_file_or_panic(&try_dir.join(&filename), file_contents);
            let mut cmd = Command::new(&self.rustc);
            cmd.current_dir(&try_dir)
                .args(&[&filename, "--emit=dep-info,metadata"]);
            println!("$ cd {:?}", try_dir);
            println!("$ {:?}", cmd);
            let status = cmd
                .status()
                .unwrap_or_else(|_| panic!("Unable to execute: {:?}", cmd));
            if status.success() {
                println!("cargo:rustc-cfg={}", name);
                if let Iteration::Unstable = *i {
                    println!("cargo:rustc-cfg=nightly_{}", name);
                }
                break;
            }
        }

        remove_dir_or_panic(&try_dir);
    }

    fn check_ffi_panic_aborts(&self) {
        let ident = "ffi_panic_aborts";
        let contents = TRY_FFI_PANIC_ABORTS;
        let try_dir = self.out_dir.join(format!("try_{}", ident));
        let filename = format!("try_{}.rs", ident);
        create_dir_or_panic(&try_dir);
        create_file_or_panic(&try_dir.join(&filename), contents);
        let mut cmd = Command::new(&self.rustc);
        cmd.current_dir(&try_dir)
            .args(&[&filename, "-o", "out.exe"]);
        println!("$ cd {:?}", try_dir);
        println!("$ {:?}", cmd);
        let status = cmd
            .status()
            .unwrap_or_else(|_| panic!("Unable to execute: {:?}", cmd));
        assert!(status.success(), "Compiling failed: {:?}", cmd);
        cmd = Command::new(try_dir.join("out.exe"));
        println!("$ {:?}", cmd);
        let status = cmd
            .status()
            .unwrap_or_else(|_| panic!("Unable to execute: {:?}", cmd));
        remove_dir_or_panic(&try_dir);
        // If panic aborts, status.success() is false.
        if !status.success() {
            println!("cargo:rustc-cfg=ffi_panic_aborts");
        }
    }
}

fn cargo_env(name: &str) -> OsString {
    env::var_os(name).unwrap_or_else(|| {
        panic!("environment variable not found: {}, please use cargo", name)
    })
}

fn remove_dir(dir: &Path) -> IoResult<()> {
    if !dir.exists() {
        return Ok(());
    }
    assert!(dir.is_dir(), "Not a directory: {:?}", dir);
    println!("$ rm -r {:?}", dir);
    fs::remove_dir_all(dir)
}

fn remove_dir_or_panic(dir: &Path) {
    remove_dir(dir)
        .unwrap_or_else(|_| panic!("Unable to remove directory: {:?}", dir));
}

fn create_dir(dir: &Path) -> IoResult<()> {
    println!("$ mkdir -p {:?}", dir);
    fs::create_dir_all(dir)
}

fn create_dir_or_panic(dir: &Path) {
    create_dir(dir)
        .unwrap_or_else(|_| panic!("Unable to create directory: {:?}", dir));
}

fn create_file_or_panic(filename: &Path, contents: &str) {
    println!("$ printf '%s' {:?}... > {:?}", &contents[0..20], filename);
    let mut file = File::create(filename)
        .unwrap_or_else(|_| panic!("Unable to create file: {:?}", filename));
    file.write_all(contents.as_bytes())
        .unwrap_or_else(|_| panic!("Unable to write to file: {:?}", filename));
}

const TRY_INT_128: &str = r#"// try_int_128.rs
use std::i128;
fn main() {
    let _: i128 = 1i128;
    let _: u128 = 1u128;
    let _ = i128::MIN;
}
"#;

const TRY_TRY_FROM: &str = r#"// try_try_from.rs
use std::convert::TryFrom;
fn main() {
    let _ = i8::try_from(1u64);
}
"#;

const TRY_FFI_PANIC_ABORTS: &str = r#"// try_ffi_panic_aborts.rs
extern "C" fn ffi_panic() {
    panic!();
}

type Handler = Option<unsafe extern "C" fn(i: i32)>;
extern "C" {
    pub fn signal(signum: i32, handler: Handler) -> Handler;
}
extern "C" fn handler(_: i32) {
    std::process::exit(3);
}

fn main() {
    // catch some signals and exit(3) instead
    unsafe {
        // SIGILL
        signal(4, Some(handler));
        // unix SIGABRT
        signal(6, Some(handler));
        // windows SIGABRT
        signal(22, Some(handler));
    }
    let _ = std::panic::catch_unwind(|| ffi_panic());
}
"#;
