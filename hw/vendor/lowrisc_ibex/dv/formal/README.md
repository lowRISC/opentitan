# End-to-End Formal Verification of Ibex Trace Equivalence against the Sail Model

## Building & Running the flow

Prerequisites:
- Nix (`https://zero-to-nix.com/start/install`)
- Cadence Jasper
  If Jasper is not found on you PATH, `nix develop` will refuse to enter the development shell.

Getting started:
- Clone this repository
- `cd dv/formal`

### Reproducible Build

This flow is intended for users who wish to run the formal flow as-is using the pinned external dependencies (psgen, sail, riscv-sail etc.)

Build instructions:
- `nix develop .#formal`
- `make` invokes Jasper in batch-mode, and attempts to prove everything, which is meant for regressions.
- `make jg` invokes Jasper interactively, halting after sourcing the contents of `verify.tcl`.

After `make jg`, Jasper should start up and should execute the commands in the TCL file.
You can see the different steps of the proof in the `Task Tree` tab.
Then, you can prove each step in order by right clicking on them and clicking `Prove Task`.
Some tasks may take longer than others and you can select specific properties in the `Property Table` and prove them individually by right clicking and selecting `Prove Property`.
Some steps require a lot of RAM and CPU so we recommend closing any other resource-heavy programs running on your computer.
A machine with 128 GiB of RAM and 32 cores was used to complete the proof.
To avoid manually running each step you can also use the `prove_lemmas` command inside the TCL command interface located below your session window.

### Development Builds

Users who wish to do development on this flow should use the below steps.
This will allow changes to both the local files and the external dependencies (psgen, sail, riscv-sail), and to run the intermediate build steps manually.

Build instructions:
- Identical to the Reproducible Build steps, but use `nix develop .#formal-dev`.

Invoking `make jg` using the provided makefile would run the following steps, which can also be executed manually:
- `make fusesoc` fetches the necessary RTL using the FuseSoC tool and makes a local copy inside `build/`.
  This also creates a filelist (`.scr`) that Jasper knows how to ingest.
  This step also patches the Ibex RTL with the changes described [in the section below](#rtl-changes).
- `make psgen` to build the SV for the proofs given in `thm/`
- `make sv` to build the SV translation of the Sail compiler.
  Will invoke `buildspec.py`, which can be configured to adjust which instructions are defined.
  By default all of them are, this is correct but slow.
- `jg verify.tcl` invokes Jasper interactively, sourcing the configuration & run script.
  Requires the above two steps to be executed first.

Local versions of the external dependencies can be modified and linked into the build via Environment Variables as follows:
- psgen: (`https://github.com/mndstrmr/psgen`)
  - Clone the repository to a local directory \<psgen-dir\> : `git clone https://github.com/mndstrmr/psgen`
  - Make local changes...
  - Build in place with `nix develop --command bash -c "go build"`
  - In the formal-dev shell:
    - Add new psgen binary to head of path with `export PATH=<psgen-dir>:$PATH`
- lowRISC Sail: (`https://github.com/lowrisc/sail` on the `lowrisc` branch).
  - Clone the repository to a local directory \<sail-dir\> : `git clone --branch lowrisc https://github.com/lowrisc/sail`
  - Make local changes...
  - Build in place with `nix develop github:lowrisc/ibex#lowrisc_sail --command bash -c "dune build --release && dune install --prefix ."`
  - In the formal-dev shell:
    - Add new Sail binary to head of path with `export PATH=<sail-dir>/bin:$PATH`
    - Update `LOWRISC_SAIL_SRC` to point to the source root with `export LOWRISC_SAIL_SRC=<sail-dir>`.
- sail-riscv: (`https://github.com/lowrisc/sail-riscv`)
  - Clone the repository to a local directory \<sail-riscv-dir\> (`git clone https://github.com/lowrisc/sail-riscv`).
  - Make local changes...
  - In the formal-dev shell:
    - Update `LOWRISC_SAIL_RISCV_SRC` to point to the source root with `export LOWRISC_SAIL_RISCV_SRC=<sail-riscv-dir>`.

## Conclusivity
All properties are currently known to be conclusive, with the exception of M-Types.
The later stages (Memory, Top, RegMatch and Wrap and some Liveness) generally take longer.

This means that (up to base case) Ibex is trace equivalent to the Sail (i.e. where the Sail main function is run in a loop).
This means:
- If one takes a sequence of instructions and ran Ibex on them, the same memory operations in the same order would be produced by running the Sail main function in a loop.
- We do not prove that the instruction executed with a given PC was loaded with that PC.
- We haven't proven that Ibex resets correctly, if it doesn't there is no trace equivalence.

## RTL Changes
- `ResetAll = 1` is required for now (instead of `ResetAll = Lockstep`)

## Code Tour
### Top Level Goals
The top level objective is to get proofs for `Wrap`, `Live`, `Load`, `Store` and `NoMem`.
These properties are themselves enough to prove trace equivalence (see below).
They are intended to be simple and human interpretable, you should be able to convince yourself that those properties together imply specification conformance of Ibex (ignoring the holes listed below).
- `Wrap` proves that on each invocation of the specification (each time `spec_en` is high) the new inputs to the spec are consistent with the previous outputs of the spec.
- `Live` proves that you will always eventually get a `spec_en` event, (i.e. it's not possible to avoid comparing with the spec).
  This is done by finding a very conservative but finite bound on the amount of time between spec `spec_en`.
- `Load` and `Store` prove that the requests made to memory are correct, given a common spec/Ibex starting state.
  `Wrap`+`Live` proves that that starting state is actually the same.
  They are written only in terms of top level signals, and `instr_will_progress`, which directly implies `spec_en`.
- `NoMem` checks that non memory instructions don't make memory requests.

Everything else (about 1,000 properties) exist to help `Wrap` converge.

Immediately below `Wrap` we have `Top`, which asserts that when any instruction retires it does so correctly.
This is proved with a big case split, where we check the same for each individual instruction.
Most of the work goes into proving those properties with many many invariants.

### Helpers
Most Ibex specific helpers can be found in `thm/ibex.proof`, it's a mess of invariants that help the model checker significantly.
Each one was at some point obtained by analysing some kind of k-induction trace, or just by thinking about why a property can't be easily proved in its current state.

The standout part of that file is `Memory`.
It is the central graph induction used to prove that memory operations are well behaved.
The definitions of the nodes are fairly clear, though their invariants can be complex.
They are however fairly intuitive with some thought.

Arguably the most important helpers are those in `thm/riscv.proof` that individually check each instruction or type of instruction.
They pretty much all check the same thing:
The RF addr/WE is correct, the RF data is correct, the CSRs are correct, and the PC is correct.
Most also have `use structure_fast`, which is a great help.

That file also contains checks for non-instructions like IRQs, illegal instructions and fetch errors.
They are checked in largely similar ways.

Towards the end of `riscv.proof` we have Top, RegMatch and Wrap.
Wrap is the goal.
Top is the statement: 'every instruction is correct', and RegMatch is to help Wrap with the otherwise difficult RegA and RegB properties.

The other helpers are in `btype.proof` and `mem.proof`, which mostly just contain more graph inductions for properties that can otherwise be difficult to prove.

### Liveness
The final property of `Wrap` is `Live`, which essentially proves that there will be infinite points of comparison between Ibex and the spec.
It is this signal which means you don't have to trust that `spec_en` means anything.
`Live` is difficult to prove.
Ideally it would say `always (s_eventually spec_en)`, but in practice it has to enforce a strict bound, since proving `s_eventually` properties is quite difficult: `always (##[0:N] spec_en)`.
You can find this value for `N` in `Wrap`, at the time of writing it's 212, essentially, meaning that an instruction must move to writeback at least once in 212 cycles.
This is obviously an extremely weak bound, but that's fine since any finite bound is sufficient to prove liveness.

The proof of `Live` is fairly neat, and can be found in `riscv.proof`.
It composes many properties about smaller time bounds into one large property, which conservatively just adds them all up.
The major difficulty in particular is proving that if an instruction is killed, then the next one will not be.
There are also issues with long running instructions and events (divide, memory, WFI).

By default live (and the liveness lemmas) are commented out, since it currently only applies when `TIME_LIMIT = 1`.

## Guide to Bug Hunting
When you are looking to check you haven't introduced a bug you should be careful not to accidentally assume the absence of any bugs.

**Either prove each task in order, or run a bounded check on the property you are interested in, but do so outside of the proof structure, i.e. in the `<embedded>` task.**

It is enough to check `Wrap`, `Load*` and `Store*`.
That said it might be more convenient to check a lower level property.
- If you've changed the behaviour of an instruction (either its GPRs, CSRs, PC or whatever else) you should probably be checking the properties for that instruction or class of instructions.
  Alternatively you could check the `Top` properties.
- If you've changed the behaviour of interrupts check the `IRQ` properties.
- If you've changed PMP, or other memory related things check `FetchErr` as well as the data memory properties.
- Pipeline control issues are only directly checked by `Wrap`, though will likely be picked up by something else.

## Proof Holes

1. Some CSRs are not checked.
   See `ex_is_checkable_csr` in `top.sv` for the full list.
   They are not checked either because they aren't specified, can't be specified or because I haven't got around to adding them yet.
   Some should be easy to check.
   When a CSR instruction touches one of those CSRs the next round of checks is essentially just disabled, anything can happen and verification will assume at the next `spec_en`.
2. Bus errors are assumed not to occur.
   They are not specified, though the bigger issue is that they would be hard to prove correctness of.
3. There are no NMIs or fast IRQs, since there are not specified.
4. We forbid attempting to enter debug mode, as this is also not specified.
5. We assume `ResetAll` and no clock gating.
   Both of these could be fixed with probably fairly little effort.
6. I don't check that Ibex ever handles interrupts.
   If it does handle an interrupt, it does so correctly.
7. I haven't proved security, I have proved correctness, or more specifically specification conformance.
   If there is a bug in the spec, or a side channel somewhere, I will not find it.
8. There is currently no proof of correctness of instruction fetch, i.e. when IF returns an instruction with a given PC, it has not been proved that that instruction was actually loaded from memory with that PC.
   This was proved for CHERIoT-Ibex and could probably be easily proved here too.
9. Ibex has not been proved to reset to the correct state, there's no reason it couldn't be.

The precise configuration of Ibex can be found in `top.sv`, but is mostly the default with the following exceptions:
- 4 PMP Regions, enabled
- `BranchTargetALU = 1`
- `ResetAll = 1` (but `SecureIbex = 0`)
In particular, this means we have
- `RV32MFast`
- `RV32BNone` (Hence we are missing some instructions.
  This might be a good place for future work, it should be not terribly difficult to extend this)
- `RegFileFF`

The following are not holes per se, but are limitations, needed to obtain convergence of liveness or others:
1. Memory grants/responses are bounded to take at most `TIME_LIMIT` cycles in `protocol/mem.sv`.
   Removing this restriction would be hard.
   That number is 10 at time of writing, but `Wrap` and `Live` have only been tested with 1. See below for more on that.
2. WFI instructions may not currently be entered if they couldn't ever be exited in `protocol/irqs.sv`.
   This probably should be legal behaviour, but without it liveness is false.
   There could probably instead be a specific carve-out for this case, since it's also legal behaviour.
3. If a WFI is entered it must be interrupted within `WFI_BOUND` cycles, in `protocol/irqs.sv`.
   An `s_eventually` equivalent would be nice but in practice is very difficult to prove properties with.
4. When an interrupt is fired, that interrupt must remain fired until a memory request is granted (i.e. as if it was some MMIO operation), in `protocol/irqs.sv`.
   This might be removable.

## Wrap Around
The formal work includes `Wrap` properties.
They check that each time the specification is 'used' the inputs to the specification equal its outputs the last time it was read.

Wrap properties have currently only been tested with `TIME_LIMIT = 1`, which is way lower than is ideal.
Higher numbers do probably work, but I have no idea how long they will take.
If JG is doing its job properly it shouldn't matter at all.
The liveness properties will fail for higher time limits (this should be easy but fiddly to fix! They would ideally have limits written in terms of `TIME_LIMIT` and `WFI_BOUND`), so they are commented out by default.

While the implications of such a property are intuitive, we can be satisfying formal too.
Define five functions:
1. The specification function $\text{Spec} : S \times I \to S$ maps an architectural state and input to the next architectural state.
   It does not matter what is meant by 'next' here, but in our case $\text{Spec}$ steps through either an illegal instruction, an interrupt or a regular instruction.
2. $\text{SpecOut} : S \times I \to O$ maps an architectural state and input to an output (i.e. memory outputs).
3. $\text{Ibex} : A \times I \to A$ maps one micro-architectural state and input to the next micro-architectural state, where 'next' is equivalent to 'next' for $\text{Spec}$ and might span multiple clock cycles.
4. $\text{IbexOut} : S \times I \to O$ maps a micro-architectural state and input to an output.
5. $\text{abs} : A \to S$ maps a micro-architectural state to an architectural state.

The memory assertions (`Load`, `Store`, `NoMem`) prove the following statement, for any micro-architectural state $a$ and input $i$:
```math
\text{SpecOut}(\text{abs}(a), i) = \text{IbexOut}(a, i)
```

The assertions with prefix `Wrap_` (using essentially every other property we have as lemmas) prove the following statement:
```math
\text{Spec}(\text{abs}(a), i) = \text{abs}(\text{Ibex}(a, i))
```
If $a_0$ is the reset micro-architectural state we have, by a straightforward induction, that for a sequence of $n$ inputs $I$,
```math
\text{Spec}^n(\text{abs}(a_0), I) = \text{abs}(\text{Ibex}^n(a_0, I))
```
Where I here denote $f^{n + 1}(a, I)$ to be the left fold of `f` over `I` using `a` initially, i.e. in Haskell syntax `foldl f a I`.
Combined we derive that
```math
\text{SpecOut}(\text{abs}(\text{Ibex}^n (a_0, I)), i) = \text{SpecOut}(\text{Spec}^n (\text{abs}(a_0), I), i) = \text{IbexOut}(\text{Ibex}^n (a_0, I), i)
```

Finally, we will (but have not yet attempted to) prove that $\text{abs}(a_0) = s_0$, where $s_0$ is the initial state of the specification:
```math
\text{SpecOut}(\text{Spec}^n (s_0, I), i) = \text{IbexOut}(\text{Ibex}^n (a_0, I), i)
```

With that we can conclude that for any sequence of $n$ steps the outputs will remain the same between the specification and Ibex, proving their complete equivalence, so long as there are infinite such steps, which the `Live` property proves.

Note a few things:
1. We do not implicitly rely on (or define) 'correctness' for $\text{abs}$.
   Satisfying the above propositions is sufficient.
   In practice it will need to be 'correct' in some sense for $\text{Spec}$ to make use of it.
2. We do not need to prove that the internal signals of Ibex mean anything, e.g. we have no explicit interpretation of the register file, the pipeline or anything else.
   To be convinced that I am correct you need to trust only that `Wrap`, `Live`, `Load`, `Store`, `NoMem` say what I claim they do above.
   If I am wrong about my interpretation about internal signals, it does not matter.
3. In practice there are steps we cannot prove equivalence across (i.e. accessing CSRs we don't have a specification for).
   In such cases we just disable the next check and resume after that.

