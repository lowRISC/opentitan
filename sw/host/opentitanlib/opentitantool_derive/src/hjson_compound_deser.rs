use proc_macro2::TokenStream;
use proc_macro_error::abort;
use quote::quote;
use syn::{
    parse_macro_input, Data, DataStruct, DeriveInput, Field, Ident, Lit, Meta, NestedMeta, Type,
};

pub fn derive_hjson_compound_deser_impl(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let input = parse_macro_input!(input as DeriveInput);

    match &input.data {
        Data::Struct(s) => dispatch_struct(s, &input.ident).into(),
        _ => abort!(
            input.ident.span(),
            "HjsonCompoundDeser is only implemented for structs"
        ),
    }
}

fn dispatch_struct(s: &DataStruct, name: &Ident) -> TokenStream {
    let packed_fields = s
        .fields
        .iter()
        .map(|field| pack_field(field))
        .collect::<Vec<_>>();

    let unpacked_fields = s
        .fields
        .iter()
        .map(|field| {
            let ident = &field.ident;
            quote! {#ident}
        })
        .collect::<Vec<_>>();

    // Construct a companion struct that has the same layout but with all fields replaced with
    // `HjsonField<Type, Formatter>`. When deserializing using serde this will be the struct that
    // should be deserialized so that the fields are properly formatted and we can handle special
    // values like named constants and meta fields such as "<random>".
    quote! {
        const _: () = {
            extern crate deser_hjson;
            extern crate serde;
            extern crate anyhow;

            #[derive(serde::Deserialize)]
            struct HjsonExpanded {
                #(#packed_fields),*
            }

            impl HjsonUnpack<#name> for HjsonExpanded {
                fn unpack_value(&self, backend: &mut DeserBackend) -> anyhow::Result<#name> {
                    Ok(#name {
                        #(#unpacked_fields: self.#unpacked_fields.unpack_value(backend)?),*
                    })
                }
            }

            impl HjsonCompoundDeser for #name {
                fn from_str(s: &str, backend: &mut DeserBackend) -> anyhow::Result<#name> {
                    let expanded: HjsonExpanded = deser_hjson::from_str(s)?;
                    expanded.unpack_value(backend)
                }
            }

            impl<'de, F: HjsonFormatter<#name>> Deserialize<'de> for HjsonField<#name, F> {
                fn deserialize<D>(deserializer: D) -> Result<HjsonField<#name, F>, D::Error>
                    where
                D: Deserializer<'de>,
                {
                    struct Visitor;
                    impl<'a> de::Visitor<'a> for Visitor {
                        type Value = HjsonExpanded;

                        fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
                            formatter.write_fmt(format_args!("a value parsable to {}", type_name::<#name>()))
                        }

                        fn visit_newtype_struct<D>(self, deserializer: D) -> Result<Self::Value, D::Error>
                        where
                            D: Deserializer<'a>,
                        {
                            HjsonExpanded::deserialize(deserializer)
                        }

                    }
                    Ok(HjsonField::<#name, F> {
                        val: HjsonFieldType::Nested(
                                 Box::new(
                                     deserializer.deserialize_newtype_struct(
                                         stringify!{#name},
                                         Visitor {})?
                                     )
                                 ),
                        formatter: Default::default(),
                    })
                }
            }
            unparsable_from_context!(#name);
            unparsable_from_context!(HjsonExpanded);
        };
    }
}

fn pack_field(field: &Field) -> TokenStream {
    // The identifier for this field.
    let ident = &field.ident;
    // The type for this field.
    let ty = &field.ty;
    // The formatter, if any, that will be used in post-deserialization parsing.
    let formatter = field.attrs.iter().find(|a| a.path.is_ident("format"));
    // A marker to indicate nested structs.
    let nested = field.attrs.iter().find(|a| a.path.is_ident("nested"));

    // Extract the formatter type from #[formatter("my::formatter::Path")].
    let format_trait = if let Some(formatter) = formatter {
        let meta = match formatter.parse_meta() {
            Ok(meta) => meta,
            Err(e) => abort!(formatter, e),
        };
        match meta {
            Meta::List(meta) => {
                if meta.nested.len() != 1 {
                    abort!(
                        meta,
                        "expected a single argument, got {}",
                        meta.nested.len()
                    );
                }
                match meta.nested.first().unwrap() {
                    NestedMeta::Lit(Lit::Str(lit)) => {
                        let format_ty: Type = lit.parse().unwrap();
                        quote! { crate::util::hjson::HjsonField<#ty, #format_ty> }
                    }
                    bad => abort!(bad, "expected string literal"),
                }
            }
            bad => abort!(bad, "unrecognized attribute"),
        }
    } else {
        // Fields that don't specify a formatter are parsed contextually. For example, "0xABCD"
        // for String fields will be left as a string, where for u32 fields it will be parsed as a
        // hex value, "1234" will get parsed as a decimal value, ect.
        quote! { crate::util::hjson::HjsonField<#ty, FromContext> }
    };

    quote! {
        #ident: #format_trait
    }
}
