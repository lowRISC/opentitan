// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use proc_macro2::TokenStream;
use proc_macro_error::{abort, proc_macro_error};
use quote::quote;
use syn::{parse_macro_input, Data, DataEnum, DeriveInput, Fields, Ident, Variant};

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
/// #[derive(Subcommand, CommandDispatch)]
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
///     ) -> anyhow::Result<Option<Box<dyn serde_annotate::Annotate>>> {
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
    let input = parse_macro_input!(input as DeriveInput);

    match &input.data {
        Data::Enum(e) => dispatch_enum(&input.ident, e).into(),
        _ => abort!(
            input.ident.span(),
            "CommandDispatch is only implemented for enums"
        ),
    }
}

fn dispatch_enum(name: &Ident, e: &DataEnum) -> TokenStream {
    let arms = e
        .variants
        .iter()
        .map(|variant| dispatch_variant(name, variant))
        .collect::<Vec<_>>();

    // We wrap the derived code inside an anonymous const block to give the
    // `extern crate` references a local namespace that wont pollute the
    // global namespace.
    quote! {
        const _: () = {
            extern crate opentitanlib;
            extern crate anyhow;
            extern crate erased_serde;

            impl opentitanlib::app::command::CommandDispatch for #name {
                fn run(
                    &self,
                    context: &dyn std::any::Any,
                    backend: &opentitanlib::app::TransportWrapper,
                ) -> anyhow::Result<Option<Box<dyn serde_annotate::Annotate>>> {
                    match self {
                        #(#arms),*
                    }
                }
            }
        };
    }
}

fn dispatch_variant(name: &Ident, variant: &Variant) -> TokenStream {
    let ident = &variant.ident;
    let unnamed_len = match &variant.fields {
        Fields::Unnamed(u) => u.unnamed.len(),
        _ => abort!(
            variant.ident.span(),
            "CommandDispatch is only implemented for Newtype variants"
        ),
    };
    if unnamed_len != 1 {
        abort!(
            variant.ident.span(),
            "CommandDispatch is only implemented for Newtype variants"
        );
    }
    quote! {
        #name::#ident(ref __field) =>
            opentitanlib::app::command::CommandDispatch::run(__field, context, backend)
    }
}
