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

fn main() {
    let out_dir = PathBuf::from(cargo_env("OUT_DIR"));
    if has_int_128(&out_dir) {
        println!("cargo:rustc-cfg=int_128");
    }
    if env::var_os("CARGO_FEATURE_GMP_MPFR_SYS").is_some() {
        let bits = env::var_os("DEP_GMP_LIMB_BITS")
            .expect("DEP_GMP_LIMB_BITS not set by gmp-mfpr-sys");
        let bits = bits.to_str()
            .expect("DEP_GMP_LIMB_BITS contains unexpected characters");
        if bits != "32" && bits != "64" {
            panic!("Limb bits not 32 or 64: \"{}\"", bits);
        }
        println!("cargo:rustc-cfg=gmp_limb_bits_{}", bits);
    }
}

fn has_int_128(out_dir: &Path) -> bool {
    let rustc = cargo_env("RUSTC");
    let try_dir = out_dir.join("try_int_128");
    create_dir_or_panic(&try_dir);
    create_file_or_panic(&try_dir.join("try_int_128.rs"), TRY_INT_128_RS);
    let mut cmd = Command::new(&rustc);
    cmd.current_dir(&try_dir).arg("try_int_128.rs");
    println!("$ {:?}", cmd);
    let status = cmd.status()
        .unwrap_or_else(|_| panic!("Unable to execute: {:?}", cmd));
    remove_dir_or_panic(&try_dir);
    status.success()
}

fn cargo_env(name: &str) -> OsString {
    env::var_os(name).unwrap_or_else(|| {
        panic!(
            "environment variable not found: {}, please use cargo",
            name
        )
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
    println!(
        "$ printf '%s' {:?}... > {:?}",
        &contents[0..20],
        filename
    );
    let mut file = File::create(filename)
        .unwrap_or_else(|_| panic!("Unable to create file: {:?}", filename));
    file.write_all(contents.as_bytes())
        .unwrap_or_else(|_| panic!("Unable to write to file: {:?}", filename));
}

const TRY_INT_128_RS: &'static str = r#"// try_int_128.rs
fn main() {
    let _ = 1i128;
    let _ = 1u128;
}
"#;
