use proc_macro2::TokenStream;
use quote::quote;
use syn::{parse_macro_input, Data, DataEnum, DeriveInput, Fields, Ident, Variant};

#[proc_macro_derive(CommandDispatch)]
pub fn derive_command_dispatch(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let input = parse_macro_input!(input as DeriveInput);

    let expanded = match &input.data {
        Data::Enum(e) => dispatch_enum(&input.ident, e),
        _ => unimplemented!("CommandDispatch is only implemented for enums"),
    };
    proc_macro::TokenStream::from(expanded)
}

fn dispatch_enum(name: &Ident, e: &DataEnum) -> TokenStream {
    let arms = e
        .variants
        .iter()
        .map(|variant| dispatch_variant(name, variant))
        .collect::<Vec<_>>();

    quote! {
        impl crate::command::CommandDispatch for #name {
            fn run(&self, backend: &mut dyn opentitanlib::transport::Transport) -> anyhow::Result<Option<Box<dyn erased_serde::Serialize>>> {
                match self {
                    #(#arms),*
                }
            }
        }
    }
}

fn dispatch_variant(name: &Ident, variant: &Variant) -> TokenStream {
    let ident = &variant.ident;
    let unnamed = match &variant.fields {
        Fields::Unnamed(u) => u.unnamed.iter().collect::<Vec<_>>(),
        _ => unimplemented!("CommandDispatch is only implemented for Newtype variants"),
    };
    if unnamed.len() != 1 {
        unimplemented!("CommandDispatch is only implemented for Newtype variants");
    }
    quote! {
        #name::#ident(ref __field) => __field.run(backend)
    }
}
