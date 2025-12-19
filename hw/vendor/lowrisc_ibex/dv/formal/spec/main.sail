// Copyright lowRISC contributors.
// Copyright 2024 University of Oxford, see also CREDITS.md.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// Original author: Louis-Emile Ploix
// SPDX-License-Identifier: Apache-2.0

/*
This file contains the main function which is 'invoked' by the SystemVerilog.
main is equivalent to the Sail step function, it has some differences however:
1. It uses the decompress function we added.
2. It can operate in one of three modes, based on what it has been told to do by the SV.
   This is done for a couple of reasons:
   1. It's difficult to compare IRQ handling, since ibex takes them later than the Sail would. This is OK since it's not really
      fair to enforce that IRQs are handled between any two specific instructions, so long as it is eventually.
   2. The three modes are a useful case analysis we can make. This means that to prove correctness of an I-Type instruction, for example, we
      can more easily separate out the check for instruction fetch correctness, which makes things faster and avoids repeated work.
*/

union FetchResult = {
  F_Ext_Error : ext_fetch_addr_error,      /* For extensions */
  F_Base      : word,                      /* Base ISA */
  F_RVC       : half,                      /* Compressed ISA */
  F_Error     : (ExceptionType, xlenbits)  /* standard exception and PC */
}

function isRVC(h : bits(16)) -> bool = ~ (h[1 .. 0] == 0b11)

// modified version of what one can find in riscv_fetch.sail
val altFetch : (bits(16), bits(16)) -> FetchResult
function altFetch(ilo: bits(16), ihi: bits(16)) -> FetchResult =
  match mem_read_i(Execute(), PC, if isRVC(ilo) then 2 else 4) {
    MemException(a, e) => F_Error(e, a),
    MemValue(()) => if isRVC(ilo) then F_RVC(ilo) else F_Base(ihi @ ilo)
  }


enum MainMode = { MAIN_IDEX, MAIN_IFERR, MAIN_IRQ }
enum MainResult = { MAINRES_OK, MAINRES_IFERR_1, MAINRES_IFERR_2, MAINRES_NOIFERR, MAINRES_IRQ, MAINRES_NOIRQ }

function main(insn_bits, mode) : (bits(32), MainMode) -> MainResult = {
  let insn = if isRVC(insn_bits[15..0]) then {
    instbits = 0x0000 @ insn_bits[15..0];
    encdec_compressed(insn_bits[15..0])
  } else {
    instbits = insn_bits;
    encdec(insn_bits)
  };

  let irq = dispatchInterrupt(cur_privilege);
  let f : FetchResult = altFetch(insn_bits[15..0], insn_bits[31..16]);

  let res : MainResult = match mode {
    MAIN_IDEX => {
      match decompress(insn) {
        Some(decompressed) => {
          let _ = execute(decompressed);
        },
        None() => ()
      };

      match f {
        F_Ext_Error(e)   => MAINRES_IFERR_1,
        F_Error(e, addr) => MAINRES_IFERR_2,
        F_RVC(h) => MAINRES_OK,
        F_Base(w) => MAINRES_OK
      }
    },
    MAIN_IFERR => {
      match f {
        F_Ext_Error(e)   => {
          ext_handle_fetch_check_error(e);
          MAINRES_OK
        },
        F_Error(e, addr) => {
          handle_mem_exception(addr, e);
          MAINRES_OK
        },
        F_RVC(h) => MAINRES_NOIFERR,
        F_Base(w) => MAINRES_NOIFERR
      }
    },
    MAIN_IRQ => {
      match irq {
        Some(intr, priv) => {
          handle_interrupt(intr, priv);
          MAINRES_OK
        },
        None() => MAINRES_NOIRQ
      }
    }
  };

  res
}
