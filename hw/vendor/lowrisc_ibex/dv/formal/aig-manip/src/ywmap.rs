// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// Original author: Louis-Emile Ploix
// SPDX-License-Identifier: Apache-2.0

use serde::Deserialize;

use crate::vmap::VMapWire;

#[derive(Deserialize, Debug)]
#[allow(dead_code)]
pub struct YWWire {
    pub input: usize,
    pub offset: usize,
    pub path: [String; 1],
}

#[derive(Deserialize)]
#[allow(dead_code)]
/// Represents a parsed .ywmap file, which is just JSON in the below format.
/// For some reason names are always singleton arrays, I don't know why.
pub struct YWMap {
    pub asserts: Vec<[String; 1]>,
    pub assumes: Vec<[String; 1]>,
    pub inputs: Vec<YWWire>,
    pub seqs: Vec<YWWire>,
    pub inits: Vec<YWWire>,
}

impl YWMap {
    pub fn parse(reader: impl std::io::BufRead) -> YWMap {
        serde_json::from_reader(reader).expect("Could not parse YW json")
    }

    /// Assertions in .ywmap files have a lot of junk around them.
    /// This transforms "$\\top.prop$18" into just "prop".
    fn decode_name(s: &str) -> &str {
        let (_, chunk) = s.rsplit_once('.').unwrap_or(("", s));
        let (chunk, _) = chunk.split_once('$').unwrap_or((chunk, ""));
        chunk
    }

    /// Construct wires suitable for appending to a vmap for this ywmap
    pub fn vmap_wires(&self, aig: &aig::Aig) -> impl Iterator<Item = VMapWire> {
        self.asserts
            .iter()
            .enumerate()
            .map(|(i, x)| (aig.bads[i], x))
            .map(|(i, x)| VMapWire {
                // Note that asserts are really "bads" in the AIG file,
                // so they should be inverted.
                index: (i.node_id() << 1) | (!i.compl() as usize),
                offset: 0,
                path: YWMap::decode_name(&x[0]).to_string(),
            })
            .chain(
                self.assumes
                    .iter()
                    .enumerate()
                    .map(|(i, x)| (aig.constraints[i], x))
                    .map(|(i, x)| VMapWire {
                        index: (i.node_id() << 1) | (i.compl() as usize),
                        offset: 0,
                        path: YWMap::decode_name(&x[0]).to_string(),
                    }),
            )
    }
}
