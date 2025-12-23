// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// Original author: Louis-Emile Ploix
// SPDX-License-Identifier: Apache-2.0

use std::collections::HashMap;

use aig::AigEdge;

#[derive(Debug)]
pub struct VMapWire {
    pub index: usize,
    pub offset: usize,
    pub path: String,
}

impl VMapWire {
    pub fn aig_edge(&self) -> AigEdge {
        AigEdge::new(self.index >> 1, self.index & 1 != 0)
    }
}

/// Represents a parsed vmap file, which have the following format:
/// input [index] [offset] [name]
/// ...
/// invlatch [index] [offset] [name]
/// ...
/// wire [index] [offset] [name]
/// ...
/// We only care about wires for now.
pub struct VMap {
    pub wires: Vec<VMapWire>,
}

impl VMap {
    pub fn parse(reader: impl std::io::BufRead) -> VMap {
        let mut vmap = VMap { wires: Vec::new() };
        for line in reader.lines() {
            let line = line.expect("read failed");
            if line.starts_with("wire ") {
                let [index, offset, name] = line[5..]
                    .splitn(3, " ")
                    .collect::<Vec<_>>()
                    .try_into()
                    .expect("malformed vmap");
                if !name.starts_with("$") {
                    vmap.wires.push(VMapWire {
                        index: index.parse::<usize>().expect("expected number"),
                        offset: offset.parse().expect("expected number"),
                        path: name.to_string(),
                    })
                }
            }
        }
        vmap
    }
}

#[derive(Debug)]
pub struct VMapWireGroup<'a> {
    pub path: &'a str,
    pub own_name: &'a str,
    /// Bits are ordered MSB to LSB
    pub bits: Vec<&'a VMapWire>,
}

impl<'a> VMapWireGroup<'a> {
    pub fn aig_edges(&self) -> impl Iterator<Item = AigEdge> {
        self.bits.iter().map(|x| x.aig_edge())
    }
}

#[derive(Debug)]
/// A vmap file with hierarchy, i.e. module paths are parsed out
pub struct WireHierarchy<'a> {
    pub wires: Vec<VMapWireGroup<'a>>,
    pub modules: HashMap<&'a str, WireHierarchy<'a>>,
}

impl VMap {
    pub fn to_hierarchy(&'_ self) -> WireHierarchy<'_> {
        /// Recursively group by prefix
        fn to_hierarchy_from<'a>(wires: &[&'a VMapWire], depth: usize) -> WireHierarchy<'a> {
            let mut new_wires = HashMap::<_, Vec<_>>::new();
            let mut modules = HashMap::<_, Vec<_>>::new();

            for wire in wires {
                if wire.path.starts_with("$") {
                    continue;
                }
                let mut split = wire.path.splitn(depth + 2, ".").skip(depth);
                let fst = split.next().expect("name too short?");
                let snd = split.next();
                if let Some(_) = snd {
                    modules.entry(fst).or_default().push(*wire);
                } else {
                    new_wires.entry(wire.path.as_str()).or_default().push(*wire);
                }
            }

            WireHierarchy {
                wires: new_wires
                    .into_iter()
                    .map(|(path, mut bits)| {
                        bits.sort_by(|a, b| b.offset.cmp(&a.offset));
                        let own_name = match path.rsplit_once('.') {
                            None => path,
                            Some((_, name)) => name,
                        };
                        VMapWireGroup {
                            path,
                            own_name,
                            bits,
                        }
                    })
                    .collect(),
                modules: modules
                    .into_iter()
                    .map(|(name, wires)| (name, to_hierarchy_from(&wires, depth + 1)))
                    .collect(),
            }
        }

        to_hierarchy_from(&self.wires.iter().collect::<Vec<_>>(), 0)
    }
}

#[derive(Debug)]
pub struct WireExtractionInstruction<'a> {
    #[allow(dead_code)]
    pub group: &'a VMapWireGroup<'a>,
    pub edges: Vec<AigEdge>,
    pub idcode: vcd::IdCode,
}

impl<'a> WireHierarchy<'a> {
    pub fn walk<F: FnMut(&'a VMapWireGroup<'a>)>(&'a self, f: &mut F) {
        for group in &self.wires {
            f(group);
        }
        for (_, module) in self.modules.iter() {
            module.walk(f);
        }
    }

    pub fn find(&self, path: &[&str]) -> Option<&VMapWireGroup<'a>> {
        if path.len() == 1 {
            return self.wires.iter().find(|x| x.own_name == path[0]);
        }
        self.modules.get(path[0])?.find(&path[1..])
    }

    /// Construct a VCD header from these instructions, and construct a map of how to update them
    /// at each simulation step.
    pub fn append_to_vcd(
        &'a self,
        vcd: &mut vcd::Writer<impl std::io::Write>,
        extraction: &mut Vec<WireExtractionInstruction<'a>>,
    ) -> std::io::Result<()> {
        for wire in &self.wires {
            let idcode = vcd.add_wire(wire.bits.len() as u32, wire.own_name)?;
            extraction.push(WireExtractionInstruction {
                group: wire,
                edges: wire.aig_edges().collect(),
                idcode,
            });
        }

        for (name, module) in &self.modules {
            if module.wires.len() != 0 || module.modules.len() != 0 {
                vcd.add_module(name)?;
                module.append_to_vcd(vcd, extraction)?;
                vcd.upscope()?;
            }
        }
        Ok(())
    }

    /// The set of AIG indices with names
    pub fn named_aiger_vars(&self) -> HashMap<usize, &'a VMapWireGroup<'_>> {
        let mut named_wires = HashMap::new();
        self.walk(&mut |group| {
            for bit in &group.bits {
                named_wires.insert(bit.index >> 1, group);
            }
        });
        named_wires
    }
}
