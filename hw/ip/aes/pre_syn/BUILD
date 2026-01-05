# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

package(default_visibility = ["//visibility:public"])

# All sources including the dependencies from the AES.
filegroup(
    name = "full_aes_srcs",
    srcs = glob(["**"]) + [
        "//hw/ip/aes:rtl_files",
        "//hw/ip/csrng:rtl_files",
        "//hw/ip/edn:rtl_files",
        "//hw/ip/entropy_src:rtl_files",
        "//hw/ip/keymgr:rtl_files",
        "//hw/ip/lc_ctrl:rtl_files",
        "//hw/ip/prim:rtl_files",
        "//hw/ip/prim_generic:rtl_files",
        "//hw/ip/prim_xilinx:rtl_files",
        "//hw/ip/tlul:rtl_files",
        "//hw/top_earlgrey:rtl_files",
    ],
)

filegroup(
    name = "tcl_files",
    srcs = glob(["tcl/*.tcl"]),
)

filegroup(
    name = "python_files",
    srcs = glob(["python/*.py"]),
)

# An experimental synthesis target using the open-source yosys
# synthesizer with the open-source skywater pdk for the aes.
# It does not produce tape-out quality netlists and area/timing numbers
# it generates are not representative of what would be achievable with a
# tape-out quality flow.
# Note that the default Bazel target does not provide timing reports.
# Change LR_SYNTH_TIMING_RUN in syn_setup for those results.
genrule(
    name = "aes_synthesis",
    srcs = [
        ":full_aes_srcs",
        "syn_setup.sh",
        "syn_yosys.sh",
        "aes_lr_synth_conf.tcl",
        ":python_files",
        ":tcl_files",
        "@sv2v//:sv2v_bin",
        "@yosys//:yosys_bin",
        "@yosys//:data",
        "@sky130_fd_sc_hd//:libs",
    ],
    outs = [
        "aes_netlist.v",
        "synthesis_outputs.tar.gz",
        "aes.pre_map.v",
        "area.rpt",
        "syn.log",
    ],
    cmd = """
        cp $(location syn_setup.sh) .
        cp $(location syn_yosys.sh) .
        cp $(location aes_lr_synth_conf.tcl) .

        mkdir -p tcl
        cp $(locations :tcl_files) tcl/

        mkdir -p python
        cp $(locations :python_files) python/

        cp $(locations @sky130_fd_sc_hd//:libs) .
        SV2V_PATH=$(location @sv2v//:sv2v_bin)
        export PATH=$$(dirname $$SV2V_PATH):$$PATH

        YOSYS_PATH=$(location @yosys//:yosys_bin)
        YOSYS_BIN_DIR=$$(dirname $$YOSYS_PATH)
        export PATH=$$YOSYS_BIN_DIR:$$PATH

        sed -i 's|export LR_SYNTH_SRC_DIR=.*|export LR_SYNTH_SRC_DIR="hw/ip/aes"|' syn_yosys.sh

        mkdir -p syn_out

        export LR_SYNTH_CELL_LIBRARY_PATH=sky130_fd_sc_hd__tt_025C_1v80.lib
        export LR_SYNTH_CELL_LIBRARY_NAME=sky130_fd_sc_hd

        if ! ./syn_yosys.sh syn_out/build > synthesis.log 2>&1; then
            tail -n 100 synthesis.log
            exit 1
        fi

        # Main Netlist
        cp syn_out/build/generated/aes_netlist.v $(location aes_netlist.v)
        # Pre-Mapping Netlist
        cp syn_out/build/generated/aes.pre_map.v $(location aes.pre_map.v)
        # Area Report
        cp syn_out/build/reports/area.rpt $(location area.rpt)
        # Yosys Log
        cp syn_out/build/log/syn.log $(location syn.log)
        # Synthesis Outputs
        tar -czf $(location synthesis_outputs.tar.gz) -C syn_out/build .
    """,
    tags = ["manual"],
)

# Similar to the aes_synthesis target but for the core.
genrule(
    name = "aes_cipher_core_synthesis",
    srcs = [
        ":full_aes_srcs",
        "syn_setup.sh",
        "syn_yosys.sh",
        "aes_lr_synth_conf.tcl",
        ":python_files",
        ":tcl_files",
        "@sv2v//:sv2v_bin",
        "@yosys//:yosys_bin",
        "@yosys//:data",
        "@sky130_fd_sc_hd//:libs",
    ],
    outs = [
        "aes_cipher_core_netlist.v",
        "aes_cipher_core_outputs.tar.gz",
        "aes_cipher_core.pre_map.v",
        "aes_cipher_core_area.rpt",
        "aes_cipher_core_syn.log",
    ],
    cmd = """
        cp $(location syn_setup.sh) .
        cp $(location syn_yosys.sh) .
        SV2V_PATH=$(location @sv2v//:sv2v_bin)
        export PATH=$$(dirname $$SV2V_PATH):$$PATH
        YOSYS_PATH=$(location @yosys//:yosys_bin)
        export PATH=$$(dirname $$YOSYS_PATH):$$PATH
        mkdir -p tcl python syn_out
        cp $(locations :tcl_files) tcl/
        cp $(locations :python_files) python/
        cp $(locations @sky130_fd_sc_hd//:libs) .

        # Override syn_setup.sh
        cat >> syn_setup.sh <<EOF
export LR_SYNTH_IP_NAME=aes_cipher_core
export LR_SYNTH_TOP_MODULE=aes_cipher_core
export LR_SYNTH_TIMING_RUN=0
export LR_SYNTH_FLATTEN=1
EOF

        cp $(location aes_lr_synth_conf.tcl) aes_cipher_core_lr_synth_conf.tcl

        sed -i 's|export LR_SYNTH_SRC_DIR=.*|export LR_SYNTH_SRC_DIR="hw/ip/aes"|' syn_yosys.sh

        export LR_SYNTH_CELL_LIBRARY_PATH=sky130_fd_sc_hd__tt_025C_1v80.lib
        export LR_SYNTH_CELL_LIBRARY_NAME=sky130_fd_sc_hd

        if ! ./syn_yosys.sh syn_out/build > synthesis.log 2>&1; then
            tail -n 100 synthesis.log
            exit 1
        fi

        cp syn_out/build/generated/aes_cipher_core_netlist.v $(location aes_cipher_core_netlist.v)
        cp syn_out/build/generated/aes_cipher_core.pre_map.v $(location aes_cipher_core.pre_map.v)
        cp syn_out/build/reports/area.rpt $(location aes_cipher_core_area.rpt)
        cp syn_out/build/log/syn.log $(location aes_cipher_core_syn.log)
        tar -czf $(location aes_cipher_core_outputs.tar.gz) -C syn_out/build .
    """,
    tags = ["manual"],
)
