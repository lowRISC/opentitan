# Plan: Building the EarlGrey CW310 Bitstream with Open-Source Tools

## Important Clarification: FPGA Part

The CW310 "Bergen Board" uses a **Xilinx Kintex-7 XC7K410T** (`xc7k410tfbg676-1`).
This is a **7-series** part, not UltraScale. (The "K410T" refers to the Kintex-7
410T, not a Kintex UltraScale part.) This is good news: 7-series has the most
mature open-source FPGA toolchain support of any Xilinx family.

The CW340 "Luna Board" (which uses a Kintex UltraScale KU095) is a different
story and does NOT have a viable open-source bitstream path today.

---

## Current Build Flow (Proprietary)

```
Bazel --> FuseSoC --> Edalize --> Vivado (synthesis + P&R + bitstream)
```

Key files:
- FuseSoC core:    hw/top_earlgrey/chip_earlgrey_cw310.core
- Bazel target:    hw/bitstream/vivado/BUILD (target: fpga_cw310)
- Constraints:     hw/top_earlgrey/data/{pins_cw310.xdc, clocks.xdc, placement.xdc}
- Top-level RTL:   hw/top_earlgrey/rtl/autogen/chip_earlgrey_cw310.sv
- Xilinx clkgen:   hw/top_earlgrey/rtl/clkgen_xil7series.sv (uses MMCME2_ADV)
- Xilinx USR_ACC:  hw/top_earlgrey/rtl/usr_access_xil7series.sv (uses USR_ACCESSE2)
- Xilinx prims:    hw/ip/prim_xilinx/rtl/*.sv (RAMB36, clock buffers, I/O pads)
- Generic prims:   hw/ip/prim_generic/rtl/*.sv (technology-agnostic equivalents)

Build command: `./bazelisk.sh build //hw/bitstream/vivado:fpga_cw310_test_rom`

---

## Proposed Open-Source Tool Chain

```
Yosys (+ Surelog/UHDM) --> nextpnr-xilinx (openXC7) --> FASM --> Project X-Ray --> .bit
```

| Stage             | Proprietary Tool | Open-Source Replacement          |
|-------------------|------------------|----------------------------------|
| SV Frontend       | Vivado           | Surelog (UHDM plugin for Yosys)  |
| Synthesis         | Vivado           | Yosys (`synth_xilinx -family xc7`) |
| Place & Route     | Vivado           | nextpnr-xilinx (openXC7)        |
| Bitstream Gen     | Vivado           | FASM + Project X-Ray (prjxray)   |
| FPGA Programming  | Vivado HW Mgr    | openFPGALoader                   |
| Memory Splicing   | Xilinx updatemem | Custom script or fpga-tool-perf  |

### Tool Versions / Projects

- **Yosys**: https://github.com/YosysHQ/yosys -- synthesis targeting xc7
- **Surelog + UHDM**: https://github.com/chipsalliance/Surelog and
  https://github.com/chipsalliance/UHDM -- SystemVerilog frontend for Yosys
- **yosys-uhdm-plugin**: https://github.com/chipsalliance/synlig (formerly
  yosys-f4pga-plugins) -- bridges Surelog into Yosys
- **nextpnr-xilinx / openXC7**: https://github.com/openXC7/nextpnr-xilinx --
  place & route for Xilinx 7-series using Project X-Ray databases
- **Project X-Ray (prjxray)**: https://github.com/f4pga/prjxray -- bitstream
  database for Xilinx 7-series (includes the XC7K410T)
- **openFPGALoader**: https://github.com/trabucayre/openFPGALoader -- JTAG
  programming utility

---

## Implementation Plan

### Phase 1: Standalone Proof-of-Concept (Outside Bazel)

Build the bitstream manually using command-line tools to validate the full flow
works before integrating into the build system.

#### Step 1.1: Install Open-Source Toolchain

Required tools (install from source or via packages):

```bash
# Yosys (with Xilinx support)
# Surelog + UHDM (SystemVerilog frontend)
# synlig (Yosys plugin for Surelog/UHDM)
# nextpnr-xilinx (openXC7 fork, with prjxray database)
# prjxray (Project X-Ray -- 7-series bitstream tools + database)
# prjxray-db (prebuilt database, must include xc7k410t)
# openFPGALoader (JTAG programmer)
```

The openXC7 project provides an integrated install flow:
https://github.com/openXC7/openXC7-env

**Key risk**: The XC7K410T is the largest Kintex-7 part. Verify that the
prjxray-db database includes it. As of 2024, prjxray-db covers `xc7k325t` and
`xc7k410t` among others, but the 410T may have less extensive fuzzing coverage
than smaller parts like the `xc7a35t`.

#### Step 1.2: Collect RTL Source File List

FuseSoC resolves all `.core` file dependencies transitively. Extract the
complete list of SystemVerilog sources:

```bash
# Use FuseSoC to list all files for the CW310 target
fusesoc --cores-root=hw run --target=synth --setup \
    lowrisc:systems:chip_earlgrey_cw310

# The resolved file list will be in the generated .eda.yml
# Alternatively, use the Edalize API to dump the file list
```

This will produce ~500+ .sv files from hw/ip/*, hw/top_earlgrey/*, and
hw/vendor/*.

#### Step 1.3: Address Xilinx-Specific Primitives

The design uses `PRIM_DEFAULT_IMPL=prim_pkg::ImplXilinx` for synthesis, which
selects Xilinx-optimized versions of RAM, ROM, clock gating, etc. from
`hw/ip/prim_xilinx/`. These are generally well-supported by Yosys's
`synth_xilinx` since they instantiate standard Xilinx primitives (RAMB36E1,
BUFG, etc.) that Yosys knows how to handle.

**Primitives that need attention:**

| Primitive | File | Issue | Solution |
|-----------|------|-------|----------|
| MMCME2_ADV | clkgen_xil7series.sv | Xilinx hard macro for clock generation | Yosys treats as black box; nextpnr places it. Supported by prjxray. |
| USR_ACCESSE2 | usr_access_xil7series.sv | Xilinx config primitive | Yosys treats as black box; nextpnr places it. May need manual handling or stub. |
| RAMB36E1 | prim_xilinx_ram_1p.sv | Block RAM | Fully supported by Yosys synth_xilinx + nextpnr + prjxray |
| BUFG | clkgen_xil7series.sv | Global clock buffer | Supported |
| IBUF/OBUF/IOBUF | prim_xilinx_pad_wrapper.sv | I/O buffers | Supported by synth_xilinx |
| IBUF_IBUFDISABLE | prim_xilinx_pad_wrapper.sv | I/O with disable | May need fallback to plain IBUF |

**Action items:**
1. Keep `PRIM_DEFAULT_IMPL=prim_pkg::ImplXilinx` (the Xilinx prims use
   standard 7-series cells that Yosys understands)
2. Create a stub or wrapper for `USR_ACCESSE2` if Yosys/nextpnr doesn't
   support it (return constant 32'h0 as fallback)
3. Test that `IBUF_IBUFDISABLE` is handled; if not, replace with `IBUF`
4. Verify MMCME2_ADV is correctly handled as a black-box through the flow

#### Step 1.4: Handle SystemVerilog Compilation

OpenTitan uses advanced SystemVerilog constructs extensively:
- Packages, interfaces, parameterized modules
- `generate` blocks, `typedef`, `enum`, `struct`, `union`
- Assertions (can be stripped)

**Approach**: Use Surelog/synlig as the SystemVerilog frontend:

```bash
# Option A: synlig (integrated Surelog+UHDM+Yosys)
synlig -p "
    read_systemverilog -DPRIM_DEFAULT_IMPL=prim_pkg::ImplXilinx \
        -DAST_BYPASS_CLK \
        -DSYNTHESIS \
        [list of .sv files in dependency order]
    synth_xilinx -family xc7 -top chip_earlgrey_cw310
    write_json earlgrey_cw310.json
"
```

```bash
# Option B: Standard Yosys with UHDM plugin
yosys -m uhdm -p "
    read_uhdm earlgrey_cw310.uhdm   # pre-compiled by Surelog
    synth_xilinx -family xc7 -top chip_earlgrey_cw310
    write_json earlgrey_cw310.json
"
```

**Fallback**: If Surelog can't handle certain constructs, use `sv2v`
(https://github.com/zachjs/sv2v) to convert SystemVerilog to Verilog first,
then use Yosys's native `read_verilog`.

#### Step 1.5: Convert Constraints (XDC to PCF/SDC)

Yosys/nextpnr-xilinx uses a different constraint format than Vivado XDC:

- **Pin constraints**: Convert XDC `set_property PACKAGE_PIN` to nextpnr's
  XDC-subset format or a Python constraints script
- **Timing constraints**: Convert `create_clock` from `clocks.xdc`
- **I/O standards**: Convert `IOSTANDARD` properties
- **Placement constraints**: May need to be dropped or converted

nextpnr-xilinx actually supports a subset of XDC for pin assignments, so the
existing `pins_cw310.xdc` may work with minimal changes. The `clocks.xdc` and
`placement.xdc` files may need adaptation.

Write a conversion script:
```python
# xdc_to_nextpnr.py
# Parse set_property -dict { PACKAGE_PIN XX IOSTANDARD YY } [get_ports { ZZ }]
# Output in nextpnr-compatible XDC subset format
```

#### Step 1.6: Run Place & Route

```bash
# Generate chip database for xc7k410t (if not pre-built)
python3 nextpnr-xilinx/xilinx/python/bbaexport.py \
    --device xc7k410tfbg676-1 \
    --bba xc7k410t.bba
nextpnr-xilinx --chipdb xc7k410t.bin

# Run place & route
nextpnr-xilinx \
    --chipdb xc7k410t.bin \
    --xdc pins_cw310_converted.xdc \
    --netlist earlgrey_cw310.json \
    --fasm earlgrey_cw310.fasm \
    --top chip_earlgrey_cw310
```

**Key risk**: The XC7K410T is a large device. nextpnr-xilinx may have long
runtimes and high memory usage (potentially 16-32+ GB RAM). The chip database
file alone may be several GB.

#### Step 1.7: Generate Bitstream

```bash
# Convert FASM to frames
${XRAY_UTILS_DIR}/fasm2frames.py \
    --part xc7k410tfbg676-1 \
    --db-root ${XRAY_DATABASE_DIR}/kintex7 \
    earlgrey_cw310.fasm \
    > earlgrey_cw310.frames

# Convert frames to bitstream
${XRAY_TOOLS_DIR}/xc7frames2bit \
    --part_file ${XRAY_DATABASE_DIR}/kintex7/xc7k410t/part.yaml \
    --part_name xc7k410tfbg676-1 \
    --frm_file earlgrey_cw310.frames \
    --output_file earlgrey_cw310.bit
```

#### Step 1.8: Program and Test

```bash
# Program CW310 via JTAG using openFPGALoader
openFPGALoader --board cw310 earlgrey_cw310.bit

# Or specify the FPGA directly
openFPGALoader --cable ft232 --fpga-part xc7k410t earlgrey_cw310.bit
```

---

### Phase 2: Integration into OpenTitan Build System

Once the manual flow works, integrate it into the Bazel + FuseSoC build.

#### Step 2.1: Create a New FuseSoC Target for Open-Source Synthesis

Add a new target in `chip_earlgrey_cw310.core`:

```yaml
  synth_opensource:
    default_tool: yosys  # or a custom backend
    filesets:
      - files_rtl_cw310
      - files_constraints_opensource  # converted constraints
    toplevel: chip_earlgrey_cw310
    parameters:
      - BootRomInitFile
      - OtpCtrlMemInitFile
      - PRIM_DEFAULT_IMPL=prim_pkg::ImplXilinx
      - AST_BYPASS_CLK=true
    tools:
      yosys:
        arch: xilinx
        output_format: json
```

FuseSoC's Edalize layer already has a Yosys backend, though it may need
extension for the nextpnr-xilinx + prjxray steps.

#### Step 2.2: Create a New Bazel Build Target

Add to `hw/bitstream/BUILD` or create `hw/bitstream/opensource/BUILD`:

```python
fusesoc_build(
    name = "fpga_cw310_opensource",
    srcs = ["//hw:rtl_files", ...],
    cores = ["//hw:cores"],
    systems = ["lowrisc:systems:chip_earlgrey_cw310"],
    target = "synth_opensource",
    output_groups = {
        "bitstream": ["synth-yosys/earlgrey_cw310.bit"],
    },
    tags = ["manual"],
)
```

This would require extending `fusesoc.bzl` to handle a non-Vivado PATH
(currently hardcoded to look up the `vivado` binary path at line 99 of
`rules/fusesoc.bzl`).

#### Step 2.3: Create a Custom Edalize Backend (if needed)

If FuseSoC/Edalize doesn't natively support the full
Yosys->nextpnr-xilinx->prjxray pipeline, create a custom backend or a wrapper
script that chains the tools:

```bash
#!/bin/bash
# opensource_synth.sh -- wraps the full open-source FPGA flow
set -e

# 1. Synthesis (Yosys + Surelog)
synlig -p "read_systemverilog $SV_FILES; synth_xilinx -family xc7 -top $TOP; write_json $OUT.json"

# 2. Place & Route (nextpnr-xilinx)
nextpnr-xilinx --chipdb $CHIPDB --xdc $XDC --netlist $OUT.json --fasm $OUT.fasm

# 3. Bitstream (prjxray)
fasm2frames.py --part $PART --db-root $DB $OUT.fasm > $OUT.frames
xc7frames2bit --part_file $PART_YAML --frm_file $OUT.frames --output_file $OUT.bit
```

---

### Phase 3: Resolve Known Challenges

#### Challenge 1: SystemVerilog Complexity

OpenTitan is one of the most complex open-source SystemVerilog designs. Surelog
may fail on certain constructs. Antmicro has been working on this
(https://antmicro.com/blog/2023/03/adapting-opentitan-for-fpga-prototyping-and-tooling-development/)
but it remains a work in progress.

**Mitigation**: Use `sv2v` as a preprocessing step to convert SV to plain
Verilog before Yosys synthesis. This has been demonstrated to work on
significant portions of OpenTitan.

#### Challenge 2: Design Size vs. Tool Maturity

The XC7K410T is the largest Kintex-7 part. Most openXC7 community testing has
been on smaller Artix-7 parts. The 410T may exercise untested corners of the
tools.

**Mitigation**: Start with a stripped-down OpenTitan configuration (remove
peripherals to reduce utilization) and incrementally add back blocks.

#### Challenge 3: MMCME2_ADV Support

The MMCME2_ADV (mixed-mode clock manager) is critical for clock generation.
nextpnr-xilinx and prjxray do support MMCME2_ADV for 7-series, but the
configuration fuzz coverage may be incomplete for all parameter combinations.

**Mitigation**: Verify the specific MMCME2_ADV configuration used in
`clkgen_xil7series.sv` (100 MHz in, 24 MHz / 48 MHz / 250 kHz out) is
covered by prjxray's database. If not, consider generating the clock
externally on the CW310 board and bypassing the MMCM.

#### Challenge 4: Memory Initialization (Boot ROM / OTP)

The Vivado flow initializes BRAMs from VMEM files at synthesis time and
supports post-build splicing via `updatemem`. The open-source flow would need:

1. BRAM initialization via Yosys `$readmemh` support (already works)
2. A replacement for `updatemem` for post-build memory patching
   - prjxray includes tools for BRAM content manipulation
   - Or: re-run synthesis each time (slower but simpler)

#### Challenge 5: Timing Closure

Yosys + nextpnr-xilinx do not have accurate timing models for 7-series. The
design may not meet timing at the target frequencies (24 MHz main clock). At
24 MHz this is relatively relaxed, so timing closure may be achievable even
without perfect timing models.

**Mitigation**: The CW310's clock is generated by an on-board PLL and can be
configured to lower frequencies if needed for initial bring-up.

---

## Summary: Feasibility Assessment

| Aspect | Assessment |
|--------|-----------|
| **Overall feasibility** | Possible but significant effort required |
| **FPGA family support** | XC7K410T is 7-series = best open-source support |
| **Synthesis (Yosys)** | Mature for 7-series architecture |
| **SystemVerilog frontend** | Biggest risk -- Surelog/synlig still maturing for complex SV |
| **Place & Route** | openXC7/nextpnr-xilinx works but untested at this scale |
| **Bitstream generation** | prjxray covers 7-series including K410T |
| **FPGA programming** | openFPGALoader supports CW310 |
| **Build system integration** | FuseSoC + Edalize have Yosys backends; needs extension |
| **Prior art** | Antmicro has partial results; no full EarlGrey bitstream from OSS tools yet |

**Recommended approach**: Start with Phase 1 (standalone proof-of-concept)
using the `sv2v` path to avoid SystemVerilog frontend issues, targeting a
minimal EarlGrey configuration. Once that works end-to-end, incrementally
add the full design and integrate into the Bazel build system.

---

## Quick-Start Commands (Phase 1)

```bash
# 1. Install toolchain (example using openXC7-env)
git clone https://github.com/openXC7/openXC7-env
cd openXC7-env && make

# 2. Collect source files from FuseSoC
cd /path/to/opentitan
fusesoc --cores-root=hw run --target=synth --setup lowrisc:systems:chip_earlgrey_cw310

# 3. Convert SV to Verilog (workaround for SV complexity)
sv2v --define=SYNTHESIS --define=AST_BYPASS_CLK \
     --define=PRIM_DEFAULT_IMPL=prim_pkg::ImplXilinx \
     [all .sv files] -w output_dir/

# 4. Synthesize with Yosys
yosys -p "
    read_verilog output_dir/*.v
    synth_xilinx -family xc7 -top chip_earlgrey_cw310
    write_json earlgrey_cw310.json
"

# 5. Place & Route
nextpnr-xilinx --chipdb xc7k410t.bin \
    --xdc hw/top_earlgrey/data/pins_cw310.xdc \
    --netlist earlgrey_cw310.json \
    --fasm earlgrey_cw310.fasm

# 6. Generate bitstream
fasm2frames.py --part xc7k410tfbg676-1 --db-root $PRJXRAY_DB/kintex7 \
    earlgrey_cw310.fasm > earlgrey_cw310.frames
xc7frames2bit --part_file $PRJXRAY_DB/kintex7/xc7k410t/part.yaml \
    --frm_file earlgrey_cw310.frames \
    --output_file earlgrey_cw310.bit

# 7. Program
openFPGALoader --board cw310 earlgrey_cw310.bit
```
