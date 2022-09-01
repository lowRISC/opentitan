// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/// Creates C-like enums which preserve unknown (un-enumerated) values.
///
/// If you wanted an enum like:
/// ```
/// #[repr(u32)]
/// pub enum HardenedBool {
///     True = 0x739,
///     False = 0x146,
///     Unknown(u32),
/// }
/// ```
///
/// Where the `Unknown` discriminator would be the catch-all for any
/// non-enumerated values, you can use `with_unknown!` as follows:
///
/// ```
/// with_unknown! {
///     pub enum HardenedBool: u32 {
///         True = 0x739,
///         False = 0x14d,
///     }
/// }
/// ```
///
/// This "enum" can be used later in match statements:
/// ```
/// match foo {
///     HardenedBool::True => do_the_thing(),
///     HardenedBool::False => do_the_opposite_thing(),
///     HardenedBool(x) => panic!("Oh noes! {} is neither True nor False!", x),
/// }
/// ```
///
/// Behind the scenes, `with_unknown!` implements a newtype struct and
/// creates associated constants for each of the enumerated values.
/// The struct also implements `Copy`, `Clone`, `PartialEq`, `Eq`,
/// `PartialOrd`, `Ord`, `Hash`, `Debug` and `Display` (including the hex,
/// octal and binary versions).
///
/// In addition, `serde::Serialize` and `serde::Deserialize` are
/// implemented.  The serialized form is a string for known values and an
/// integer for all unknown values.
#[macro_export]
macro_rules! with_unknown {
    (
        $(
            $(#[$outer:meta])*
            $vis:vis enum $Enum:ident: $type:ty {
                $(
                    $(#[$inner:meta])*
                    $enumerator:ident = $value:expr,
                )*
            }
        )*
    ) => {$(
        $(#[$outer])*
        #[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
        #[repr(transparent)]
        $vis struct $Enum(pub $type);

        #[allow(non_upper_case_globals)]
        impl $Enum {
            $(
                $(#[$inner])*
                $vis const $enumerator: $Enum = $Enum($value);
            )*
        }

        impl From<$Enum> for $type {
            fn from(v: $Enum) -> $type {
                v.0
            }
        }

        // Implement the various display traits.
        $crate::__impl_fmt_unknown!(Display, "{}", "{}", $Enum { $($enumerator),* });
        $crate::__impl_fmt_unknown!(LowerHex, "{:x}", "{:#x}", $Enum { $($enumerator),* });
        $crate::__impl_fmt_unknown!(UpperHex, "{:X}", "{:#X}", $Enum { $($enumerator),* });
        $crate::__impl_fmt_unknown!(Octal, "{:o}", "{:#o}", $Enum { $($enumerator),* });
        $crate::__impl_fmt_unknown!(Binary, "{:b}", "{:#b}", $Enum { $($enumerator),* });

        // Manually implement Serialize and Deserialize to have tight control over how
        // the struct is serialized.
        const _: () = {
            use serde::ser::{Serialize, Serializer};
            use serde::de::{Deserialize, Deserializer, Error, Visitor};
            use std::convert::TryFrom;

            impl Serialize for $Enum {
                /// Serializes the enumerated values.  All named discriminants are
                /// serialized to strings.  All unknown values are serialized as
                /// integers.
                fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
                where
                    S: Serializer,
                {
                    match *self {
                        $(
                            $Enum::$enumerator => serializer.serialize_str(stringify!($enumerator)),
                        )*
                        $Enum(value) => value.serialize(serializer),
                    }
                }
            }

            // The `EnumVistor` assists in deserializing the value.
            struct EnumVisitor;
            impl<'de> Visitor<'de> for EnumVisitor {
                type Value = $Enum;

                fn expecting(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
                    f.write_str(concat!("A valid enumerator of ", stringify!($Enum)))
                }

                fn visit_str<E: Error>(self, value: &str) -> Result<Self::Value, E> {
                    match value {
                        $(
                            stringify!($enumerator) => Ok($Enum::$enumerator),
                        )*
                        _ => Err(E::custom(format!("unrecognized: {}", value))),
                    }
                }
                $crate::__expand_visit_fn!(visit_i8, i8, $Enum, $type);
                $crate::__expand_visit_fn!(visit_i16, i16, $Enum, $type);
                $crate::__expand_visit_fn!(visit_i32, i32, $Enum, $type);
                $crate::__expand_visit_fn!(visit_i64, i64, $Enum, $type);
                $crate::__expand_visit_fn!(visit_u8, u8, $Enum, $type);
                $crate::__expand_visit_fn!(visit_u16, u16, $Enum, $type);
                $crate::__expand_visit_fn!(visit_u32, u32, $Enum, $type);
                $crate::__expand_visit_fn!(visit_u64, u64, $Enum, $type);
            }

            impl<'de> Deserialize<'de> for $Enum {
                /// Deserializes the value by forwarding to `deserialize_any`.
                /// `deserialize_any` will forward strings to the string visitor
                /// and forward integers to the appropriate integer visitor.
                fn deserialize<D>(deserializer: D) -> Result<$Enum, D::Error>
                where
                    D: Deserializer<'de>,
                {
                    deserializer.deserialize_any(EnumVisitor)
                }
            }
        };
    )*};
}

#[macro_export]
macro_rules! __expand_visit_fn {
    ($visit_func:ident, $ser_type:ty, $Enum:ident, $enum_type:ty) => {
        fn $visit_func<E>(self, value: $ser_type) -> Result<Self::Value, E>
        where
            E: Error,
        {
            match <$enum_type>::try_from(value) {
                Ok(v) => Ok($Enum(v)),
                Err(_) => Err(E::custom(format!(
                    "cannot convert {:?} to {}({})",
                    value,
                    stringify!($Enum),
                    stringify!($enum_type)
                ))),
            }
        }
    };
}

// Helper macro for implementing the various formatting traits.
#[macro_export]
macro_rules! __impl_fmt_unknown {
    (
        $Trait:ident, $Fmt:literal, $Alt:literal, $Enum:ident {
            $($enumerator:ident),*
        }
    ) => {
        impl std::fmt::$Trait for $Enum {
            fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
                match *self {
                    $(
                        $Enum::$enumerator => write!(f, "{}", stringify!($enumerator)),
                    )*
                    $Enum(value) => {
                        if f.alternate() {
                            write!(f, concat!(stringify!($Enum), "(", $Alt, ")"), value)
                        } else {
                            write!(f, concat!(stringify!($Enum), "(", $Fmt, ")"), value)
                        }
                    }
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use anyhow::Result;
    use serde::{Deserialize, Serialize};

    with_unknown! {
        pub enum HardenedBool: u32 {
            True = 0x739,
            False = 0x14d,
        }

        // Check the top-level repeat in the macro.
        enum Misc: u8 {
            X = 0,
            Y = 1,
            Z = 2,
        }
    }

    #[test]
    fn test_display() -> Result<()> {
        let t = HardenedBool::True;
        assert_eq!(t.to_string(), "True");

        let f = HardenedBool::False;
        assert_eq!(f.to_string(), "False");

        let j = HardenedBool(0x6A);
        assert_eq!(j.to_string(), "HardenedBool(106)");
        assert_eq!(format!("{:x}", j), "HardenedBool(6a)");
        assert_eq!(format!("{:#x}", j), "HardenedBool(0x6a)");
        assert_eq!(format!("{:X}", j), "HardenedBool(6A)");
        assert_eq!(format!("{:o}", j), "HardenedBool(152)");
        assert_eq!(format!("{:b}", j), "HardenedBool(1101010)");
        assert_eq!(format!("{:#b}", j), "HardenedBool(0b1101010)");
        Ok(())
    }

    #[derive(Debug, Serialize, Deserialize, PartialEq, Eq)]
    struct SomeBools {
        a: HardenedBool,
        b: HardenedBool,
        c: HardenedBool,
    }

    #[test]
    fn test_conversion() -> Result<()> {
        let t = HardenedBool::True;
        let x = HardenedBool(12345);
        assert_eq!(u32::from(t), 0x739);
        assert_eq!(u32::from(x), 12345);
        Ok(())
    }

    #[test]
    fn test_serde() -> Result<()> {
        let b = SomeBools {
            a: HardenedBool::True,
            b: HardenedBool::False,
            c: HardenedBool(0x6a),
        };
        let json = serde_json::to_string(&b)?;
        assert_eq!(json, r#"{"a":"True","b":"False","c":106}"#);

        let de = serde_json::from_str::<SomeBools>(&json)?;
        assert_eq!(de, b);
        Ok(())
    }

    #[test]
    fn test_serde_error() -> Result<()> {
        let json = r#"{"a":"True","b":"False","c":-1}"#;
        let de = serde_json::from_str::<SomeBools>(json);
        let err = de.unwrap_err().to_string();
        assert_eq!(
            err,
            "cannot convert -1 to HardenedBool(u32) at line 1 column 30"
        );
        Ok(())
    }
}
