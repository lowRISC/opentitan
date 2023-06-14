// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

//! Parser for cryptolib test fixtures.
//!
//! This file consumes `.c` files and performs a very basic parse on them
//! to extract the test vector type and any annotations on it.
//!
//! This library expects the `.c` file to contain a struct definition
//! conforming to the following reduced grammar, modulo whitespace.
//!
//! ```text
//! // cryptotest:struct
//! // Comments...
//! typedef struct $name? {
//!   // Comments...
//!   $type $field;
//!   // More fields...
//! } $name;
//! ```
//!
//! Here, `// Comments...` is any number of single-line comments, `$field` is any
//! valid C identifier, and `$type` is one of the following:
//! - `bool`
//! - `uint8_t`, `uint16_t`, `uint32_t`, `uint64_t`
//! - `int8_t`, `int16_t`, `int32_t`, `int64_t`
//! - `size_t`
//! - `const char *` (always a NUL-terminated string).
//!
//! In the future, this list will include enumerations defined in the cryptolib's ABI.
//!
//! Additionally, the following compound types are recognized:
//! - `$Int field[N];`, where `$Int` is a non-`const char *` type above and N is an
//!   integer literal.
//! - `const $Int *field;`, for a variable-length array of integers.
//! - `const char *const *field;`, for a variable-length array of strings.
//! - `const $Int (*field)[N];`, for a variable-length array of fixed arrays of ints.
//!
//! Comments that do not begin with `// cryptotest:` are ignored; the rest are parsed
//! as annotations.

use once_cell::sync::Lazy;
use regex::Regex;

/// A test vector struct.
///
/// See the [module docs](self) for information on the grammar.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Struct {
    /// The name of the struct (as specified by the `typedef`).
    pub name: String,
    /// The struct's fields.
    pub fields: Vec<Field>,
    /// Any `// cryptotest:` annotations at the top of the struct.
    pub annots: Vec<Annotation>,
}

/// A field of a [`Struct`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Field {
    /// The name of the field.
    pub name: String,
    /// The type of the field.
    pub ty: FieldType,
    /// Any `// cryptotest:` annotations on this field.
    pub annots: Vec<Annotation>,
}

/// A [`Field`]'s type.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FieldType {
    /// An array field, represented by a raw `const` pointer. The length of
    /// the array must be specified by another field of the struct
    /// via `// cryptotest:len`.
    Array(Scalar),
    /// A scalar field, consisting of a single value.
    Scalar(Scalar),
}

/// An integer type recognized by cryptotest.
///
/// Not only does this include the `stdint.h` types, but it also includes cryptolib
/// enum types known a priori to the parser.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum Int {
    Bool,
    U8,
    U16,
    U32,
    U64,
    I8,
    I16,
    I32,
    I64,
    Size,
}

impl Int {
    /// Parses an `Int` from its C name.
    pub fn from_name(name: &str) -> Result<Self, Error> {
        match name {
            "bool" => Ok(Int::Bool),
            "uint8_t" => Ok(Int::U8),
            "uint16_t" => Ok(Int::U16),
            "uint32_t" => Ok(Int::U32),
            "uint64_t" => Ok(Int::U64),
            "int8_t" => Ok(Int::I8),
            "int16_t" => Ok(Int::I16),
            "int32_t" => Ok(Int::I32),
            "int64_t" => Ok(Int::I64),
            "size_t" => Ok(Int::Size),
            _ => Err(Error::UnknownIntType(name)),
        }
    }
}

/// A scalar type, i.e., types that do not have external size information.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Scalar {
    /// An [`Int`] type.
    Int(Int),
    /// A vector type, i.e. a fixed-length array, of some kind of integer.
    Vec(Int, usize),
    /// A C-style (i.e., NUL-terminated) string, represented as a `const char*`
    /// pointer.
    CStr,
}

/// An annotation recognized by the parser for specifying how cryptotest should
/// interpret fields.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Annotation {
    /// The `cryptotest:struct` directive at the top of a struct that is used to
    /// find where the struct starts.
    Struct,
    /// The `cryptotest:len` directive that must be present on each array
    /// field, which specifies which field specifies its length. The length present
    /// at runtime may be specified in units of single bits, bytes, or 32-bit words.
    Len(String, LenUnit),
}

/// A length unit used by [`Annotation::Len`].
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum LenUnit {
    Bits,
    Bytes,
    Words,
}

// The "grammar" above is designed to be so simple we can parse it with a pile of
// regular expressions.
static STRUCT_START: Lazy<Regex> =
    Lazy::new(|| Regex::new(r"^typedef\s+struct\s+([a-zA-Z_][0-9a-zA-Z_]*)?\s*\{").unwrap());
static STRUCT_END: Lazy<Regex> =
    Lazy::new(|| Regex::new(r"^}\s*([a-zA-Z_][0-9a-zA-Z_]*)\s*;").unwrap());
static INT_FIELD: Lazy<Regex> =
    Lazy::new(|| Regex::new(r"^([a-zA-Z_][0-9a-zA-Z_]*)\s+([a-zA-Z_][0-9a-zA-Z_]*)\s*;").unwrap());
static STRING_FIELD: Lazy<Regex> =
    Lazy::new(|| Regex::new(r"^const\s+char\s*\*\s*([a-zA-Z_][0-9a-zA-Z_]*)\s*;").unwrap());
static VECTOR_FIELD: Lazy<Regex> = Lazy::new(|| {
    Regex::new(r"^([a-zA-Z_][0-9a-zA-Z_]*)\s+([a-zA-Z_][0-9a-zA-Z_]*)\s*\[\s*(\w+)\s*\]\s*;")
        .unwrap()
});
static INT_ARRAY_FIELD: Lazy<Regex> = Lazy::new(|| {
    Regex::new(r"^const\s+([a-zA-Z_][0-9a-zA-Z_]*)\s*\*\s*([a-zA-Z_][0-9a-zA-Z_]*)\s*;").unwrap()
});
static STRING_ARRAY_FIELD: Lazy<Regex> = Lazy::new(|| {
    Regex::new(r"^const\s+char\s*\*\s*const\s*\*\s*([a-zA-Z_][0-9a-zA-Z_]*)\s*;").unwrap()
});
static VECTOR_ARRAY_FIELD: Lazy<Regex> = Lazy::new(|| {
    Regex::new(r"^const\s+([a-zA-Z_][0-9a-zA-Z_]*)\s*\(\s*\*\s*([a-zA-Z_][0-9a-zA-Z_]*)\s*\)\s*\[\s*(\w+)\s*\]\s*;").unwrap()
});

const STRUCT_COMMENT: &str = "// cryptotest:struct\n";

/// An error produced by [`Struct::parse()`].
#[derive(Debug, thiserror::Error, PartialEq, Eq)]
pub enum Error<'c> {
    #[error("missing `// cryptotest:struct` comment")]
    NoStructFound,
    #[error("missing `typedef struct {{` prologue")]
    MissingStructPrologue,
    #[error("missing `}} name;` epilogue")]
    MissingStructEpilogue,
    #[error("unknown integer type: `{0}`")]
    UnknownIntType(&'c str),
    #[error(transparent)]
    BadInt(#[from] std::num::ParseIntError),
    #[error("expected a field but found something else")]
    ExpectedField,
    #[error("unknown array length unit: `{0}`")]
    UnknownLenUnit(&'c str),
    #[error("unknown annotation: `{0}`")]
    UnknownAnnotation(&'c str),
}

impl Struct {
    /// Parses a `Struct` from the given C file. This will only parse the first
    /// `cryptolib:struct` encountered.
    pub fn parse(mut c_file: &str) -> Result<Struct, Error> {
        // First, find the struct.
        let struct_start = c_file.find(STRUCT_COMMENT).ok_or(Error::NoStructFound)?;
        c_file = &c_file[struct_start..];
        let mut annots = Vec::new();
        for comment in munch_comments(&mut c_file) {
            if let Some(annot) = parse_annotation(comment)? {
                annots.push(annot);
            }
        }

        // Next, find and tear off the struct header.
        let header = STRUCT_START
            .find(c_file)
            .ok_or(Error::MissingStructPrologue)?;
        c_file = &c_file[header.end()..];

        // Now, parse as many fields as we can.
        let mut fields = Vec::new();
        loop {
            c_file = c_file.trim_start();
            let mut annots = Vec::new();
            for comment in munch_comments(&mut c_file) {
                if let Some(annot) = parse_annotation(comment)? {
                    annots.push(annot);
                }
            }

            if let Some(field) = INT_FIELD.captures(c_file) {
                c_file = &c_file[field.get(0).unwrap().end()..];
                let int = field.get(1).unwrap().as_str();
                let name = field.get(2).unwrap().as_str();
                fields.push(Field {
                    name: name.to_string(),
                    ty: FieldType::Scalar(Scalar::Int(Int::from_name(int)?)),
                    annots,
                });
            } else if let Some(field) = STRING_FIELD.captures(c_file) {
                c_file = &c_file[field.get(0).unwrap().end()..];
                let name = field.get(1).unwrap().as_str();
                fields.push(Field {
                    name: name.to_string(),
                    ty: FieldType::Scalar(Scalar::CStr),
                    annots,
                });
            } else if let Some(field) = VECTOR_FIELD.captures(c_file) {
                c_file = &c_file[field.get(0).unwrap().end()..];
                let int = field.get(1).unwrap().as_str();
                let name = field.get(2).unwrap().as_str();
                let count = field.get(3).unwrap().as_str();
                fields.push(Field {
                    name: name.to_string(),
                    ty: FieldType::Scalar(Scalar::Vec(Int::from_name(int)?, count.parse()?)),
                    annots,
                });
            } else if let Some(field) = INT_ARRAY_FIELD.captures(c_file) {
                c_file = &c_file[field.get(0).unwrap().end()..];
                let int = field.get(1).unwrap().as_str();
                let name = field.get(2).unwrap().as_str();
                fields.push(Field {
                    name: name.to_string(),
                    ty: FieldType::Array(Scalar::Int(Int::from_name(int)?)),
                    annots,
                });
            } else if let Some(field) = STRING_ARRAY_FIELD.captures(c_file) {
                c_file = &c_file[field.get(0).unwrap().end()..];
                let name = field.get(1).unwrap().as_str();
                fields.push(Field {
                    name: name.to_string(),
                    ty: FieldType::Array(Scalar::CStr),
                    annots,
                });
            } else if let Some(field) = VECTOR_ARRAY_FIELD.captures(c_file) {
                c_file = &c_file[field.get(0).unwrap().end()..];
                let int = field.get(1).unwrap().as_str();
                let name = field.get(2).unwrap().as_str();
                let count = field.get(3).unwrap().as_str();
                fields.push(Field {
                    name: name.to_string(),
                    ty: FieldType::Array(Scalar::Vec(Int::from_name(int)?, count.parse()?)),
                    annots,
                });
            } else if c_file.starts_with('}') {
                break;
            } else {
                return Err(Error::ExpectedField);
            }
        }

        let end = STRUCT_END
            .captures(c_file)
            .ok_or(Error::MissingStructEpilogue)?;

        Ok(Struct {
            name: end.get(1).unwrap().as_str().to_string(),
            fields,
            annots,
        })
    }
}

/// Strips any leading `//` comments from the start of `c_file`, and returns them,
/// including the `//` prefix.
fn munch_comments<'a>(c_file: &mut &'a str) -> Vec<&'a str> {
    let mut comments = Vec::new();
    loop {
        *c_file = c_file.trim_start();
        if !c_file.starts_with("//") {
            return comments;
        }
        let comment_end = c_file.find('\n').unwrap_or(c_file.len());
        let (comment, rest) = c_file.split_at(comment_end);
        comments.push(comment);
        *c_file = rest;
    }
}

fn parse_annotation(comment: &str) -> Result<Option<Annotation>, Error> {
    let comment = match comment.strip_prefix("// cryptotest:") {
        Some(comment) => comment,
        None => return Ok(None),
    };

    match comment.split(' ').collect::<Vec<_>>().as_slice() {
        ["struct"] => Ok(Some(Annotation::Struct)),
        ["len", field, units] => {
            let units = match *units {
                "bits" => LenUnit::Bits,
                "bytes" => LenUnit::Bytes,
                "words" => LenUnit::Words,
                _ => return Err(Error::UnknownLenUnit(units)),
            };
            Ok(Some(Annotation::Len(field.to_string(), units)))
        }
        _ => Err(Error::UnknownAnnotation(comment)),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn empty() {
        assert!(Struct::parse("").is_err())
    }

    #[test]
    fn missing_prologue() {
        assert!(Struct::parse("// cryptotest:struct").is_err())
    }

    #[test]
    fn missing_typedef() {
        assert!(Struct::parse("// cryptotest:struct\nstruct").is_err())
    }

    #[test]
    fn empty_struct() {
        assert_eq!(
            Struct::parse(
                "
                // cryptotest:struct
                typedef struct {} foo_t;
            "
            ),
            Ok(Struct {
                name: "foo_t".to_string(),
                fields: vec![],
                annots: vec![Annotation::Struct],
            })
        )
    }

    #[test]
    fn missing_name() {
        assert!(Struct::parse(
            "
            // cryptotest:struct
            typedef struct {};
            "
        )
        .is_err())
    }

    #[test]
    fn int_field() {
        assert_eq!(
            Struct::parse(
                "
                // cryptotest:struct
                typedef struct foo {
                    // My cool field!
                    uint32_t x;
                } foo_t;
                "
            ),
            Ok(Struct {
                name: "foo_t".to_string(),
                fields: vec![Field {
                    name: "x".to_string(),
                    ty: FieldType::Scalar(Scalar::Int(Int::U32)),
                    annots: vec![],
                }],
                annots: vec![Annotation::Struct],
            })
        )
    }

    #[test]
    fn missing_field_name() {
        assert!(Struct::parse(
            "
            // cryptotest:struct
            typedef struct {
                uint32_t;
            };
            "
        )
        .is_err())
    }

    #[test]
    fn char_field() {
        assert!(Struct::parse(
            "
            // cryptotest:struct
            typedef struct {
                char is_not_allowed;
            };
            "
        )
        .is_err())
    }

    #[test]
    fn bad_annotation() {
        assert!(Struct::parse(
            "
            // cryptotest:struct
            typedef struct {
                // cryptotest:omelette
                uint32_t something;
            };
            "
        )
        .is_err())
    }

    #[test]
    fn all_int_fields() {
        assert_eq!(
            Struct::parse(
                "
                // cryptotest:struct
                typedef struct foo {
                    bool b;
                    uint8_t u8;
                    uint16_t u16;
                    uint32_t u32;
                    uint64_t u64;
                    int8_t i8;
                    int16_t i16;
                    int32_t i32;
                    int64_t i64;
                    size_t sz;
                } foo_t;
                "
            ),
            Ok(Struct {
                name: "foo_t".to_string(),
                fields: vec![
                    Field {
                        name: "b".to_string(),
                        ty: FieldType::Scalar(Scalar::Int(Int::Bool)),
                        annots: vec![],
                    },
                    Field {
                        name: "u8".to_string(),
                        ty: FieldType::Scalar(Scalar::Int(Int::U8)),
                        annots: vec![],
                    },
                    Field {
                        name: "u16".to_string(),
                        ty: FieldType::Scalar(Scalar::Int(Int::U16)),
                        annots: vec![],
                    },
                    Field {
                        name: "u32".to_string(),
                        ty: FieldType::Scalar(Scalar::Int(Int::U32)),
                        annots: vec![],
                    },
                    Field {
                        name: "u64".to_string(),
                        ty: FieldType::Scalar(Scalar::Int(Int::U64)),
                        annots: vec![],
                    },
                    Field {
                        name: "i8".to_string(),
                        ty: FieldType::Scalar(Scalar::Int(Int::I8)),
                        annots: vec![],
                    },
                    Field {
                        name: "i16".to_string(),
                        ty: FieldType::Scalar(Scalar::Int(Int::I16)),
                        annots: vec![],
                    },
                    Field {
                        name: "i32".to_string(),
                        ty: FieldType::Scalar(Scalar::Int(Int::I32)),
                        annots: vec![],
                    },
                    Field {
                        name: "i64".to_string(),
                        ty: FieldType::Scalar(Scalar::Int(Int::I64)),
                        annots: vec![],
                    },
                    Field {
                        name: "sz".to_string(),
                        ty: FieldType::Scalar(Scalar::Int(Int::Size)),
                        annots: vec![],
                    },
                ],
                annots: vec![Annotation::Struct],
            })
        )
    }

    #[test]
    fn vec_field() {
        assert_eq!(
            Struct::parse(
                "
                // cryptotest:struct
                typedef struct foo {
                    uint32_t key[25];
                    uint8_t bytes[1];
                    bool flag;
                    int8_t more_bytes[9001];
                } foo_t;
                "
            ),
            Ok(Struct {
                name: "foo_t".to_string(),
                fields: vec![
                    Field {
                        name: "key".to_string(),
                        ty: FieldType::Scalar(Scalar::Vec(Int::U32, 25)),
                        annots: vec![],
                    },
                    Field {
                        name: "bytes".to_string(),
                        ty: FieldType::Scalar(Scalar::Vec(Int::U8, 1)),
                        annots: vec![],
                    },
                    Field {
                        name: "flag".to_string(),
                        ty: FieldType::Scalar(Scalar::Int(Int::Bool)),
                        annots: vec![],
                    },
                    Field {
                        name: "more_bytes".to_string(),
                        ty: FieldType::Scalar(Scalar::Vec(Int::I8, 9001)),
                        annots: vec![],
                    },
                ],
                annots: vec![Annotation::Struct],
            })
        )
    }

    #[test]
    fn missing_vec_field_name() {
        assert!(Struct::parse(
            "
            // cryptotest:struct
            typedef struct {
                uint32_t[4];
            };
            "
        )
        .is_err())
    }

    #[test]
    fn transposed_vec_field_name() {
        assert!(Struct::parse(
            "
            // cryptotest:struct
            typedef struct {
                uint32_t[4] foo;
            };
            "
        )
        .is_err())
    }

    #[test]
    fn non_literal_vec_len() {
        assert!(Struct::parse(
            "
            // cryptotest:struct
            typedef struct {
                uint32_t foo[kLen];
            };
            "
        )
        .is_err())
    }

    #[test]
    fn cstr_field() {
        assert_eq!(
            Struct::parse(
                "
                // cryptotest:struct
                typedef struct foo {
                    bool flag;
                    const char *plaintext;
                } foo_t;
                "
            ),
            Ok(Struct {
                name: "foo_t".to_string(),
                fields: vec![
                    Field {
                        name: "flag".to_string(),
                        ty: FieldType::Scalar(Scalar::Int(Int::Bool)),
                        annots: vec![],
                    },
                    Field {
                        name: "plaintext".to_string(),
                        ty: FieldType::Scalar(Scalar::CStr),
                        annots: vec![],
                    },
                ],
                annots: vec![Annotation::Struct],
            })
        )
    }

    #[test]
    fn missing_cstr_const() {
        assert!(Struct::parse(
            "
            // cryptotest:struct
            typedef struct {
                char *mut_str;
            };
            "
        )
        .is_err())
    }

    #[test]
    fn missing_cstr_star() {
        assert!(Struct::parse(
            "
            // cryptotest:struct
            typedef struct {
                const char mut_str;
            };
            "
        )
        .is_err())
    }

    #[test]
    fn cstr_right_const() {
        assert!(Struct::parse(
            "
            // cryptotest:struct
            typedef struct {
                char *const mut_str;
            };
            "
        )
        .is_err())
    }

    #[test]
    fn int_array_field() {
        assert_eq!(
            Struct::parse(
                "
                // cryptotest:struct
                typedef struct foo {
                    size_t word_count;
                    // cryptotest:len word_count words
                    const uint32_t *ciphertext;
                } foo_t;
                "
            ),
            Ok(Struct {
                name: "foo_t".to_string(),
                fields: vec![
                    Field {
                        name: "word_count".to_string(),
                        ty: FieldType::Scalar(Scalar::Int(Int::Size)),
                        annots: vec![],
                    },
                    Field {
                        name: "ciphertext".to_string(),
                        ty: FieldType::Array(Scalar::Int(Int::U32)),
                        annots: vec![Annotation::Len("word_count".to_string(), LenUnit::Words)],
                    },
                ],
                annots: vec![Annotation::Struct],
            })
        )
    }

    #[test]
    fn missing_int_array_const() {
        assert!(Struct::parse(
            "
            // cryptotest:struct
            typedef struct {
                size_t word_count;
                // cryptotest:len word_count words
                uint32_t *mut;
            };
            "
        )
        .is_err())
    }

    #[test]
    fn mystery_len() {
        assert!(Struct::parse(
            "
            // cryptotest:struct
            typedef struct {
                size_t word_count;
                // cryptotest:len word_count mystery
                uint32_t *mut;
            };
            "
        )
        .is_err())
    }

    #[test]
    fn vec_array_field() {
        assert_eq!(
            Struct::parse(
                "
                // cryptotest:struct
                typedef struct foo {
                    size_t word_count;
                    // cryptotest:len word_count bytes
                    const uint32_t (*keys)[32];
                } foo_t;
                "
            ),
            Ok(Struct {
                name: "foo_t".to_string(),
                fields: vec![
                    Field {
                        name: "word_count".to_string(),
                        ty: FieldType::Scalar(Scalar::Int(Int::Size)),
                        annots: vec![],
                    },
                    Field {
                        name: "keys".to_string(),
                        ty: FieldType::Array(Scalar::Vec(Int::U32, 32)),
                        annots: vec![Annotation::Len("word_count".to_string(), LenUnit::Bytes)],
                    },
                ],
                annots: vec![Annotation::Struct],
            })
        )
    }

    #[test]
    fn missing_vec_array_const() {
        assert!(Struct::parse(
            "
            // cryptotest:struct
            typedef struct {
                size_t word_count;
                // cryptotest:len word_count bytes
                uint32_t (*keys)[32];
            };
            "
        )
        .is_err())
    }

    #[test]
    fn missing_vec_array_star() {
        assert!(Struct::parse(
            "
            // cryptotest:struct
            typedef struct {
                size_t word_count;
                // cryptotest:len word_count bytes
                uint32_t (keys)[32];
            };
            "
        )
        .is_err())
    }

    #[test]
    fn missing_vec_array_parens() {
        assert!(Struct::parse(
            "
            // cryptotest:struct
            typedef struct {
                size_t word_count;
                // cryptotest:len word_count bytes
                uint32_t *keys[32];
            };
            "
        )
        .is_err())
    }

    #[test]
    fn cstr_array_field() {
        assert_eq!(
            Struct::parse(
                "
                // cryptotest:struct
                typedef struct foo {
                    size_t word_count;
                    // cryptotest:len word_count bytes
                    const char* const* sonnets;
                } foo_t;
                "
            ),
            Ok(Struct {
                name: "foo_t".to_string(),
                fields: vec![
                    Field {
                        name: "word_count".to_string(),
                        ty: FieldType::Scalar(Scalar::Int(Int::Size)),
                        annots: vec![],
                    },
                    Field {
                        name: "sonnets".to_string(),
                        ty: FieldType::Array(Scalar::CStr),
                        annots: vec![Annotation::Len("word_count".to_string(), LenUnit::Bytes)],
                    },
                ],
                annots: vec![Annotation::Struct],
            })
        )
    }

    #[test]
    fn missing_cstr_array_inner_const() {
        assert!(Struct::parse(
            "
            // cryptotest:struct
            typedef struct {
                size_t word_count;
                // cryptotest:len word_count bytes
                char* const* sonnets;
            };
            "
        )
        .is_err())
    }

    #[test]
    fn missing_cstr_array_outer_const() {
        assert!(Struct::parse(
            "
            // cryptotest:struct
            typedef struct {
                size_t word_count;
                // cryptotest:len word_count bytes
                const char** sonnets;
            };
            "
        )
        .is_err())
    }

    #[test]
    fn missing_cstr_array_outer_star() {
        assert!(Struct::parse(
            "
            // cryptotest:struct
            typedef struct {
                size_t word_count;
                // cryptotest:len word_count bytes
                const char* const sonnets;
            };
            "
        )
        .is_err())
    }

    #[test]
    fn missing_cstr_array_inner_star() {
        assert!(Struct::parse(
            "
            // cryptotest:struct
            typedef struct {
                size_t word_count;
                // cryptotest:len word_count bytes
                const char const* sonnets;
            };
            "
        )
        .is_err())
    }
}
