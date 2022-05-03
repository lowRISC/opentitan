//! An extremely simple libtock-rs example. Just prints out a message
//! using the Console capsule, then terminates.

#![no_main]
#![no_std]
use core::fmt::Write;
use libtock2::console::Console;
use libtock2::runtime::{set_main, stack_size};

set_main! {main}
stack_size! {0x100}

fn main() {
    writeln!(Console::writer(), "Hello world!").unwrap();
}
