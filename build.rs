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
use std::process::Command;

fn main() {
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

    if !rustc_later_eq(1, 24) {
        println!("cargo:rustc-cfg=need_ffi_panic_check");
    }
}

fn rustc_later_eq(major: i32, minor: i32) -> bool {
    let rustc = cargo_env("RUSTC");
    let output = Command::new(rustc)
        .arg("--version")
        .output()
        .expect("unable to run rustc --version");
    let version =
        String::from_utf8(output.stdout).expect("unrecognized rustc version");
    if !version.starts_with("rustc ") {
        panic!("unrecognized rustc version: {}", version);
    }
    let remain = &version[6..];
    let dot = remain.find('.').expect("unrecognized rustc version");
    let ver_major = remain[0..dot]
        .parse::<i32>()
        .expect("unrecognized rustc version");
    if ver_major < major {
        return false;
    } else if ver_major > major {
        return true;
    }
    let remain = &remain[dot + 1..];
    let dot = remain.find('.').expect("unrecognized rustc version");
    let ver_minor = remain[0..dot]
        .parse::<i32>()
        .expect("unrecognized rustc version");
    ver_minor >= minor
}

fn cargo_env(name: &str) -> OsString {
    env::var_os(name).unwrap_or_else(|| {
        panic!("environment variable not found: {}, please use cargo", name)
    })
}
