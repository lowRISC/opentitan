// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

mod command_dispatch;
mod hjson_compound_deser;

use proc_macro_error::proc_macro_error;

/// Derives the `CommandDispatch` trait for a NewType enum.
///
/// Derive this on purely interior nodes in the opentitantool command hierarchy
/// (that is: nodes whose only purpose is to dispatch down to the next layer
/// in the command heirarchy).  The automatic derivation simply calls the
/// `run` method on the next layer in the command hierarchy.
///
/// Imagine that you have structs `World` and `People` which implement
/// "Hello World" and "Hello People" commands.  You would create Newtype
/// variants inside of a `Hello` enum and derive `CommandDispatch` to
/// generate the dispatch layer for this interior node in the command hierarchy:
///
/// ```
/// #[derive(StructOpt, CommandDispatch)]
/// pub enum Hello {
///     World(World),
///     People(People),
/// }
///
/// // The derived code is as follows:
/// impl opentitanlib::app::command::CommandDispatch for Hello {
///     fn run(
///         &self,
///         context: &dyn std::any::Any,
///         backend: &mut dyn opentitanlib::transport::Transport
///     ) -> anyhow::Result<Option<Box<dyn erased_serde::Serialize>>> {
///         match self {
///             Hello::World(ref __field) => __field.run(context, backend),
///             Hello::People(ref __field) => __field.run(context, backend),
///         }
///     }
/// }
/// ```
#[proc_macro_derive(CommandDispatch)]
#[proc_macro_error]
pub fn derive_command_dispatch(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    crate::command_dispatch::command_dispatch_impl(input)
}

/// Derives the `HjsonCompoundDeser` trait for a struct.
///
/// Many HJSON config files non-standard ways of representing the data in certain fields. Hex
/// constants, meta fields such as "<random>", and named constants all look like strings to serde,
/// but they can represent entirely different data types. This macro exists to make the process of
/// deserializing these HJSON objects into Rust structs more ergonomic.
///
/// When `#[derive(HjsonCompoundDeser)]` is declared on a struct definition it does the following:
///   1. Creates a companion struct that wraps each field as an `HjsonField` type that holds the
///      intermediate state for the field.
///   2. 
///
/// ```
/// #[derive(HjsonCompoundDeser)]
/// struct MyConfigData {
///     // A u32 that can be deserialized either from an HJSON number or parsed from a string.
///     foo: u32,
///     // A u32 that can be deserialized either from an HJSON number or parsed as a hex string.
///     #[format("Hexidecimal")]
///     bar: u32,
///     // A regular HJSON string.
///     baz: String,
/// }
///
/// // This will produce a hidden companion struct that is serde deserializable.
/// struct HjsonExpanded {
///     foo: HjsonField<u32, FromContext>,
///     bar: HjsonField<u32, Hexidecimal>,
///     baz: HjsonField<String, FromContext>,
/// }
///
/// ```
#[proc_macro_derive(HjsonCompoundDeser, attributes(format))]
#[proc_macro_error]
pub fn derive_hjson_compound_deser(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    crate::hjson_compound_deser::derive_hjson_compound_deser_impl(input)
}
