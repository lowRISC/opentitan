// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

extern crate bindgen;

use bindgen::builder;
use std::env;
use std::fs::{self};
use std::path::Path;

fn main() {
    let source_root = env::var("MESON_SOURCE_ROOT").unwrap();
    let build_root = env::var("MESON_BUILD_ROOT").unwrap();
    let out_dir = env::var("OUT_DIR").unwrap();

    generate_bindings(source_root, build_root, out_dir);
}

fn generate_bindings(source_root: String, build_root: String, out_dir: String) {
    let mut binding_builder = builder()
        .raw_line("use riscv32_c_types;")
        .ctypes_prefix("riscv32_c_types")
        .clang_arg("--target=riscv32")
        .clang_args(&["-I", &source_root])
        .clang_args(&["-I", &build_root]);

    let dif_path = Path::new(&source_root).join("sw/device/lib/dif");
    let dif_build_meson = dif_path.join("meson.build");
    println!("cargo:rerun-if-changed={}", dif_build_meson.to_str().unwrap());

    let files = fs::read_dir(dif_path).unwrap();
    for file in files {
        let path = file.unwrap().path();
        if let Some(e) = path.extension() {
            let path = path.to_str().unwrap();
            if e == "h" {
                binding_builder = binding_builder.header(path);
                // Rerun the generator script if DIFs headers change.
                println!("cargo:rerun-if-changed={}", path);
            }
        }
    }

    let out_file = Path::new(&out_dir).join("ot_dif_bindings.rs");
    binding_builder.generate().unwrap().write_to_file(out_file).unwrap();
}
