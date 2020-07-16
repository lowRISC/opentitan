// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This build script relies on a number of meson build system environment
// variables:
//    - MESON_SOURCE_ROOT:
//      The full path to the source code top directory.
//    - MESON_BUILD_ROOT:
//      The full path to the build top directory.
//    - OUT_DIR:
//      The full path to the directory where the output(s) must be written.
//
// This script finds all C header files in specified directories by combining
// `MESON_SOURCE_ROOT` with a relative path. It then generates rust bindings
// for the found C header files, the generated file is stored in `OUT_DIR`.
// This script also links against the relevant libraries.

extern crate bindgen;

use std::env;
use std::fs;
use std::path::Path;

static DIF_RELATIVE_PATH: &str = "sw/device/lib/dif";
static LIBBASE_RELATIVE_PATH: &str = "sw/device/lib/base";

fn main() {
    let source_root = env::var("MESON_SOURCE_ROOT").expect("no MESON_SOURCE_ROOT env variable");

    let build_root = env::var("MESON_BUILD_ROOT").expect("no MESON_BUILD_ROOT env variable");

    let out_dir = env::var("OUT_DIR").expect("no OUT_DIR env variable");

    generate_bindings(&source_root, &out_dir);

    // Link against specified OT DIF libraries.
    let dif_path = Path::new(&build_root).join(DIF_RELATIVE_PATH);
    let dif_path = dif_path
        .to_str()
        .expect("failed to create DIF libraries path string");

    libraries_link(dif_path, &["uart_ot"]);

    // Link against specified libbase libraries.
    let libbase_path = Path::new(&build_root).join(LIBBASE_RELATIVE_PATH);
    let libbase_path = libbase_path
        .to_str()
        .expect("failed to create libbase libraries path string");

    libraries_link(libbase_path, &["mmio_ot"]);
}

fn libraries_link(path: &str, libs: &[&str]) {
    for lib in libs {
        println!("cargo:rustc-link-search={}", path);
        println!("cargo:rustc-link-lib={}", lib);
    }
}

fn generate_bindings(source_root: &str, out_dir: &str) {
    let mut binding_builder = bindgen::builder()
        .raw_line("use riscv32_c_types;")
        .ctypes_prefix("riscv32_c_types")
        .clang_arg("--target=riscv32")
        .clang_args(&["-I", &source_root])
        .derive_default(true)
        .prepend_enum_name(false)
        .rustfmt_bindings(true)
        .size_t_is_usize(true)
        .use_core();

    let dif_path = Path::new(&source_root).join(DIF_RELATIVE_PATH);
    let dif_build_meson = dif_path.join("meson.build");
    let dif_build_meson = dif_build_meson
        .to_str()
        .expect("failed to create DIF meson.build path string");

    println!("cargo:rerun-if-changed={}", dif_build_meson);

    let dif_files = fs::read_dir(dif_path).expect("failed to create DIF directory path object");

    // Find all of the DIF headers, and add them to the bindgen builder "state".
    for file in dif_files {
        let full_file_path = file.expect("file is not open").path();

        if let Some(extension) = full_file_path.extension() {
            let full_file_name = full_file_path
                .to_str()
                .expect("failed to get the full file name string");

            if extension == "h" {
                binding_builder = binding_builder.header(full_file_name);

                // Rerun the generator script if DIFs headers change.
                println!("cargo:rerun-if-changed={}", full_file_name);
            }
        }
    }

    let out_file = Path::new(&out_dir).join("ot_dif_bindings.rs");
    binding_builder
        .generate()
        .expect("failed to generate the bindings")
        .write_to_file(out_file)
        .expect("failed to create the output file");
}
