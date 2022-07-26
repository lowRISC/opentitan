// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use proc_macro2::TokenStream;
use proc_macro_error::abort;
use quote::quote;
use syn::{parse_macro_input, Data, DataEnum, DeriveInput, Fields, Ident, Variant};

pub(crate) fn command_dispatch_impl(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
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
                ) -> anyhow::Result<Option<Box<dyn erased_serde::Serialize>>> {
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
