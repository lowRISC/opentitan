fn main() {
    println!("cargo:rerun-if-changed=layout.ld");
    println!("cargo:rerun-if-changed=../third_party/tock/boards/kernel_layout.ld");
}
