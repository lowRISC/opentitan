#!/bin/bash

# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# This script drives the experimental Yosys synthesis flow. More details can be found in README.md

set -e
set -o pipefail

error () {
    echo >&2 "$@"
    exit 1
}

teelog () {
    tee "$LR_SYNTH_OUT_DIR/log/$1.log"
}

if [ ! -f syn_setup.sh ]; then
    error "No syn_setup.sh file: see README.md for instructions"
fi

#-------------------------------------------------------------------------
# setup flow variables
#-------------------------------------------------------------------------
source syn_setup.sh

#-------------------------------------------------------------------------
# prepare output folders
#-------------------------------------------------------------------------
mkdir -p "$LR_SYNTH_OUT_DIR/generated"
mkdir -p "$LR_SYNTH_OUT_DIR/log"
mkdir -p "$LR_SYNTH_OUT_DIR/reports/timing"

rm -f syn_out/latest
ln -s "${LR_SYNTH_OUT_DIR#syn_out/}" syn_out/latest

#-------------------------------------------------------------------------
# use sv2v to convert all SystemVerilog files to Verilog
#-------------------------------------------------------------------------
export LR_SYNTH_SRC_DIR="../../$LR_SYNTH_IP_NAME"

# Get OpenTitan dependency sources.
OT_DEP_SOURCES=(
    "$LR_SYNTH_SRC_DIR"/../tlul/rtl/tlul_adapter_reg.sv
    "$LR_SYNTH_SRC_DIR"/../tlul/rtl/tlul_err.sv
    "$LR_SYNTH_SRC_DIR"/../tlul/rtl/tlul_cmd_intg_chk.sv
    "$LR_SYNTH_SRC_DIR"/../tlul/rtl/tlul_rsp_intg_gen.sv
    "$LR_SYNTH_SRC_DIR"/../tlul/rtl/tlul_data_integ_dec.sv
    "$LR_SYNTH_SRC_DIR"/../tlul/rtl/tlul_data_integ_enc.sv
    "$LR_SYNTH_SRC_DIR"/../prim/rtl/prim_secded_inv_64_57_dec.sv
    "$LR_SYNTH_SRC_DIR"/../prim/rtl/prim_secded_inv_64_57_enc.sv
    "$LR_SYNTH_SRC_DIR"/../prim/rtl/prim_secded_inv_39_32_dec.sv
    "$LR_SYNTH_SRC_DIR"/../prim/rtl/prim_secded_inv_39_32_enc.sv
    "$LR_SYNTH_SRC_DIR"/../prim/rtl/prim_sparse_fsm_flop.sv
    "$LR_SYNTH_SRC_DIR"/../prim/rtl/prim_subreg.sv
    "$LR_SYNTH_SRC_DIR"/../prim/rtl/prim_subreg_ext.sv
    "$LR_SYNTH_SRC_DIR"/../prim/rtl/prim_subreg_shadow.sv
    "$LR_SYNTH_SRC_DIR"/../prim/rtl/prim_subreg_arb.sv
    "$LR_SYNTH_SRC_DIR"/../prim/rtl/prim_alert_sender.sv
    "$LR_SYNTH_SRC_DIR"/../prim/rtl/prim_diff_decode.sv
    "$LR_SYNTH_SRC_DIR"/../prim/rtl/prim_lc_sync.sv
    "$LR_SYNTH_SRC_DIR"/../prim/rtl/prim_sync_reqack_data.sv
    "$LR_SYNTH_SRC_DIR"/../prim/rtl/prim_sync_reqack.sv
    "$LR_SYNTH_SRC_DIR"/../prim/rtl/prim_packer_fifo.sv
    "$LR_SYNTH_SRC_DIR"/../prim/rtl/prim_lfsr.sv
    "$LR_SYNTH_SRC_DIR"/../prim/rtl/prim_flop_2sync.sv
    "$LR_SYNTH_SRC_DIR"/../prim/rtl/prim_cdc_rand_delay.sv
    "$LR_SYNTH_SRC_DIR"/../prim/rtl/prim_reg_we_check.sv
    "$LR_SYNTH_SRC_DIR"/../prim/rtl/prim_onehot_check.sv
    "$LR_SYNTH_SRC_DIR"/../prim/rtl/prim_mubi4_sender.sv
    "$LR_SYNTH_SRC_DIR"/../prim/rtl/prim_fifo_sync_cnt.sv
    "$LR_SYNTH_SRC_DIR"/../prim_generic/rtl/prim_generic_flop.sv
    "$LR_SYNTH_SRC_DIR"/../prim_xilinx/rtl/prim_xilinx_flop.sv
    "$LR_SYNTH_SRC_DIR"/../prim_xilinx/rtl/prim_xilinx_flop_en.sv
    "$LR_SYNTH_SRC_DIR"/../prim_xilinx/rtl/prim_xilinx_buf.sv
    "$LR_SYNTH_SRC_DIR"/../prim_xilinx/rtl/prim_xilinx_xor2.sv
    "$LR_SYNTH_SRC_DIR"/../prim_xilinx/rtl/prim_xilinx_and2.sv
    "$LR_SYNTH_SRC_DIR"/../tlul/rtl/tlul_adapter_sram.sv
    "$LR_SYNTH_SRC_DIR"/../tlul/rtl/tlul_sram_byte.sv
    "$LR_SYNTH_SRC_DIR"/../tlul/rtl/tlul_socket_1n.sv
    "$LR_SYNTH_SRC_DIR"/../tlul/rtl/tlul_err_resp.sv
    "$LR_SYNTH_SRC_DIR"/../tlul/rtl/tlul_fifo_sync.sv
    "$LR_SYNTH_SRC_DIR"/../prim/rtl/prim_intr_hw.sv
    "$LR_SYNTH_SRC_DIR"/../prim/rtl/prim_edn_req.sv
    "$LR_SYNTH_SRC_DIR"/../prim/rtl/prim_fifo_sync.sv
    "$LR_SYNTH_SRC_DIR"/../prim/rtl/prim_arbiter_fixed.sv
    "$LR_SYNTH_SRC_DIR"/../prim/rtl/prim_packer.sv
    "$LR_SYNTH_SRC_DIR"/../prim/rtl/prim_count.sv
    "$LR_SYNTH_SRC_DIR"/../prim/rtl/prim_double_lfsr.sv
    "$LR_SYNTH_SRC_DIR"/../prim/rtl/prim_onehot_mux.sv
    "$LR_SYNTH_SRC_DIR"/../prim/rtl/prim_onehot_enc.sv
    "$LR_SYNTH_SRC_DIR"/../prim/rtl/prim_blanker.sv
    "$LR_SYNTH_SRC_DIR"/../prim/rtl/prim_crc32.sv
    "$LR_SYNTH_SRC_DIR"/../prim/rtl/prim_xoshiro256pp.sv
    "$LR_SYNTH_SRC_DIR"/../prim/rtl/prim_ram_1p_scr.sv
    "$LR_SYNTH_SRC_DIR"/../prim/rtl/prim_ram_1p_adv.sv
    "$LR_SYNTH_SRC_DIR"/../prim_generic/rtl/prim_generic_ram_1p.sv
    "$LR_SYNTH_SRC_DIR"/../prim/rtl/prim_subst_perm.sv
    "$LR_SYNTH_SRC_DIR"/../prim/rtl/prim_prince.sv
)

# Get OpenTitan dependency packages.
OT_DEP_PACKAGES=(
    "$LR_SYNTH_SRC_DIR"/../../top_earlgrey/rtl/*_pkg.sv
    "$LR_SYNTH_SRC_DIR"/../edn/rtl/*_pkg.sv
    "$LR_SYNTH_SRC_DIR"/../entropy_src/rtl/*_pkg.sv
    "$LR_SYNTH_SRC_DIR"/../lc_ctrl/rtl/*_pkg.sv
    "$LR_SYNTH_SRC_DIR"/../tlul/rtl/*_pkg.sv
    "$LR_SYNTH_SRC_DIR"/../prim/rtl/*_pkg.sv
    "$LR_SYNTH_SRC_DIR"/../keymgr/rtl/*_pkg.sv
    "$LR_SYNTH_SRC_DIR"/../otp_ctrl/rtl/*_pkg.sv
)

# Convert OpenTitan dependency sources.
for file in "${OT_DEP_SOURCES[@]}"; do
    module=`basename -s .sv $file`

    # Skip packages
    if echo "$module" | grep -q '_pkg$'; then
        continue
    fi

    sv2v \
        --define=SYNTHESIS --define=SYNTHESIS_MEMORY_BLACK_BOXING --define=YOSYS \
        "${OT_DEP_PACKAGES[@]}" \
        -I"$LR_SYNTH_SRC_DIR"/../prim/rtl \
        $file \
        > $LR_SYNTH_OUT_DIR/generated/${module}.v

    # Make sure auto-generated primitives are resolved to generic or Xilinx-specific primitives
    # where available.
    sed -i 's/prim_flop/prim_xilinx_flop/g'              $LR_SYNTH_OUT_DIR/generated/${module}.v
    sed -i 's/prim_xilinx_flop_2sync/prim_flop_2sync/g'  $LR_SYNTH_OUT_DIR/generated/${module}.v
    sed -i 's/prim_sec_anchor_flop/prim_xilinx_flop/g'   $LR_SYNTH_OUT_DIR/generated/${module}.v
    sed -i 's/prim_buf/prim_xilinx_buf/g'                $LR_SYNTH_OUT_DIR/generated/${module}.v
    sed -i 's/prim_sec_anchor_buf/prim_xilinx_buf/g'     $LR_SYNTH_OUT_DIR/generated/${module}.v
    sed -i 's/prim_xor2/prim_xilinx_xor2/g'              $LR_SYNTH_OUT_DIR/generated/${module}.v
    sed -i 's/prim_and2/prim_xilinx_and2/g'              $LR_SYNTH_OUT_DIR/generated/${module}.v
    sed -i 's/prim_ram_1p/prim_generic_ram_1p/g'         $LR_SYNTH_OUT_DIR/generated/${module}.v

    # Remove calls to $value$plusargs(). Yosys doesn't seem to support this.
    sed -i '/$value$plusargs(.*/d' $LR_SYNTH_OUT_DIR/generated/${module}.v
done

# Rename the prim_sparse_fsm_flop module. For some reason, sv2v decides to append a suffix.
sed -i 's/module prim_sparse_fsm_flop_.*/module prim_sparse_fsm_flop \(/g' \
    $LR_SYNTH_OUT_DIR/generated/prim_sparse_fsm_flop.v

# Get and convert core sources.
for file in "$LR_SYNTH_SRC_DIR"/rtl/*.sv; do
    module=`basename -s .sv $file`

    # Skip packages
    if echo "$module" | grep -q '_pkg$'; then
        continue
    fi

    sv2v \
        --define=SYNTHESIS \
        "${OT_DEP_PACKAGES[@]}" \
        "$LR_SYNTH_SRC_DIR"/rtl/*_pkg.sv \
        -I"$LR_SYNTH_SRC_DIR"/../prim/rtl \
        $file \
        > $LR_SYNTH_OUT_DIR/generated/${module}.v

    # Make sure auto-generated primitives are resolved to generic or Xilinx-specific primitives
    # where available.
    sed -i 's/prim_flop/prim_xilinx_flop/g'              $LR_SYNTH_OUT_DIR/generated/${module}.v
    sed -i 's/prim_xilinx_flop_2sync/prim_flop_2sync/g'  $LR_SYNTH_OUT_DIR/generated/${module}.v
    sed -i 's/prim_sec_anchor_flop/prim_xilinx_flop/g'   $LR_SYNTH_OUT_DIR/generated/${module}.v
    sed -i 's/prim_buf/prim_xilinx_buf/g'                $LR_SYNTH_OUT_DIR/generated/${module}.v
    sed -i 's/prim_sec_anchor_buf/prim_xilinx_buf/g'     $LR_SYNTH_OUT_DIR/generated/${module}.v
    sed -i 's/prim_xor2/prim_xilinx_xor2/g'              $LR_SYNTH_OUT_DIR/generated/${module}.v
    sed -i 's/prim_and2/prim_xilinx_and2/g'              $LR_SYNTH_OUT_DIR/generated/${module}.v
    sed -i 's/prim_ram_1p/prim_generic_ram_1p/g'         $LR_SYNTH_OUT_DIR/generated/${module}.v

    # Rename prim_sparse_fsm_flop instances. For some reason, sv2v decides to append a suffix.
    sed -i 's/prim_sparse_fsm_flop_.*/prim_sparse_fsm_flop \#(/g' \
        $LR_SYNTH_OUT_DIR/generated/${module}.v

    # Remove the StateEnumT parameter from prim_sparse_fsm_flop instances. Yosys doesn't seem to
    # support this.
    sed -i '/\.StateEnumT(logic \[.*/d' $LR_SYNTH_OUT_DIR/generated/${module}.v
    sed -i '/\.StateEnumT_otbn_pkg.*Width.*(.*/d' $LR_SYNTH_OUT_DIR/generated/${module}.v
done

#-------------------------------------------------------------------------
# run Yosys synthesis
#-------------------------------------------------------------------------
yosys -c ./tcl/yosys_run_synth.tcl |& teelog syn || {
    error "Failed to synthesize RTL with Yosys"
}

#-------------------------------------------------------------------------
# run static timing analysis
#-------------------------------------------------------------------------
if [[ $LR_SYNTH_TIMING_RUN == 1 ]] ; then
    sta ./tcl/sta_run_reports.tcl |& teelog sta || {
        error "Failed to run static timing analysis"
    }

    ./translate_timing_rpts.sh
fi

#-------------------------------------------------------------------------
# report kGE number
#-------------------------------------------------------------------------
python/get_kge.py $LR_SYNTH_CELL_LIBRARY_PATH $LR_SYNTH_OUT_DIR/reports/area.rpt
