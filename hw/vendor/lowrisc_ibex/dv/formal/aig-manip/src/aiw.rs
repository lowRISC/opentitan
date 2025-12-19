// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// Original author: Louis-Emile Ploix
// SPDX-License-Identifier: Apache-2.0

use aig::TernarySimulate;

use crate::bitvec::BitVec;

/// Represents a parse AIW file.
/// AIW files have the following structure:
/// 1
/// [0-9]+b
/// initial state of FFs as a list of 0s and 1s
/// one line of inputs for each cycle, also a list of 0s and 1s
pub struct AigerWitness {
    pub initial_state: BitVec,
    pub inputs: Vec<BitVec>,
}

impl AigerWitness {
    pub fn parse(reader: impl std::io::BufRead) -> std::io::Result<AigerWitness> {
        let mut witness = AigerWitness {
            initial_state: BitVec::new(),
            inputs: Vec::new(),
        };

        let mut lines = reader.lines();
        assert_eq!(lines.next().expect("malformed witness file")?.as_str(), "1");
        lines.next().expect("malformed witness file")?;

        witness.initial_state = lines
            .next()
            .expect("malformed witness file")?
            .chars()
            .map(|c| match c {
                '0' => false,
                '1' => true,
                _ => panic!(),
            })
            .collect();

        while let line = lines.next().expect("malformed witness file")?
            && line != "."
        {
            witness.inputs.push(
                line.chars()
                    .map(|c| match c {
                        '0' => false,
                        '1' => true,
                        _ => panic!(),
                    })
                    .collect(),
            );
        }

        Ok(witness)
    }

    /// Construct a simulation of just the initial state
    pub fn init_simulation<'a>(&self, aig: &'a aig::Aig) -> TernarySimulate<'a> {
        TernarySimulate::new(&aig, self.initial_state.iter().map(|x| x.into()).collect())
    }

    /// Run a simulation for step steps
    pub fn simulate_to_step<'a>(&self, aig: &'a aig::Aig, step: usize) -> TernarySimulate<'a> {
        let mut sim = self.init_simulation(aig);
        for step in self.inputs.iter().take(step) {
            sim.simulate(step.iter().map(|x| x.into()).collect());
        }
        sim
    }
}
