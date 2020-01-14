// Copyright © 2016–2019 University of Malta

// Copying and distribution of this file, with or without
// modification, are permitted in any medium without royalty provided
// the copyright notice and this notice are preserved. This file is
// offered as-is, without any warranty.

#![allow(dead_code)]
#![allow(unused_variables)]
#![cfg_attr(feature = "fail-on-warnings", deny(warnings))]

use std::{
    env,
    ffi::OsString,
    fs::{self, File},
    io::{Result as IoResult, Write},
    path::{Path, PathBuf},
    process::{Command, Stdio},
};

struct Environment {
    out_dir: PathBuf,
    rustc: OsString,
}

fn main() {
    let env = Environment {
        out_dir: PathBuf::from(cargo_env("OUT_DIR")),
        rustc: cargo_env("RUSTC"),
    };
    if env::var_os("CARGO_FEATURE_GMP_MPFR_SYS").is_some() {
        let bits =
            env::var_os("DEP_GMP_LIMB_BITS").expect("DEP_GMP_LIMB_BITS not set by gmp-mfpr-sys");
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
    fn check_feature(&self, name: &str, contents: &str, nightly_features: Option<&str>) {
        let try_dir = self.out_dir.join(format!("try_{}", name));
        let filename = format!("try_{}.rs", name);
        create_dir_or_panic(&try_dir);
        println!("$ cd {:?}", try_dir);

        enum Iteration {
            Stable,
            Unstable,
        }
        for i in &[Iteration::Stable, Iteration::Unstable] {
            let s;
            let file_contents = match *i {
                Iteration::Stable => contents,
                Iteration::Unstable => match nightly_features {
                    Some(features) => {
                        s = format!("#![feature({})]\n{}", features, contents);
                        &s
                    }
                    None => continue,
                },
            };
            create_file_or_panic(&try_dir.join(&filename), file_contents);
            let mut cmd = Command::new(&self.rustc);
            cmd.current_dir(&try_dir)
                .stdout(Stdio::null())
                .stderr(Stdio::null())
                .args(&[&filename, "--emit=dep-info,metadata"]);
            println!("$ {:?} >& /dev/null", cmd);
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
}

fn cargo_env(name: &str) -> OsString {
    env::var_os(name)
        .unwrap_or_else(|| panic!("environment variable not found: {}, please use cargo", name))
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
    remove_dir(dir).unwrap_or_else(|_| panic!("Unable to remove directory: {:?}", dir));
}

fn create_dir(dir: &Path) -> IoResult<()> {
    println!("$ mkdir -p {:?}", dir);
    fs::create_dir_all(dir)
}

fn create_dir_or_panic(dir: &Path) {
    create_dir(dir).unwrap_or_else(|_| panic!("Unable to create directory: {:?}", dir));
}

fn create_file_or_panic(filename: &Path, contents: &str) {
    println!("$ printf %s {:?}... > {:?}", &contents[0..20], filename);
    let mut file =
        File::create(filename).unwrap_or_else(|_| panic!("Unable to create file: {:?}", filename));
    file.write_all(contents.as_bytes())
        .unwrap_or_else(|_| panic!("Unable to write to file: {:?}", filename));
}
