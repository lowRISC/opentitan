// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class kmac_error_vseq extends kmac_app_vseq;

  `uvm_object_utils(kmac_error_vseq)
  `uvm_object_new

  virtual function string convert2string();
    return {$sformatf("en_kmac_err: %0b\n", en_kmac_err),
            $sformatf("kmac_err_type: %0s\n", kmac_err_type.name()),
            $sformatf("err_sw_cmd_seq_st: %0s\n", err_sw_cmd_seq_st.name()),
            $sformatf("err_sw_cmd_seq_cmd: %0s\n", err_sw_cmd_seq_cmd.name()),
            super.convert2string()};
  endfunction

  virtual task pre_start();
    disable_err_c.constraint_mode(0);
    en_app_c.constraint_mode(0);
    super.pre_start();
  endtask

  constraint en_err_c {
    en_kmac_err dist {
      0 :/ 3,
      1 :/ 7
    };
  }

  constraint kmac_err_type_c {
    if (en_kmac_err) {
      (kmac_err_type inside
          {kmac_pkg::ErrNone, kmac_pkg::ErrKeyNotValid, kmac_pkg::ErrWaitTimerExpired}) == 0;
    } else {
      kmac_err_type == kmac_pkg::ErrNone;
    }

    (kmac_err_type == kmac_pkg::ErrSwPushedMsgFifo) -> (en_app == 1);

    (kmac_err_type == kmac_pkg::ErrSwIssuedCmdInAppActive) -> (en_app == 1);

    (kmac_err_type == kmac_pkg::ErrIncorrectFunctionName) -> (kmac_en == 1);

    (kmac_err_type == kmac_pkg::ErrUnexpectedModeStrength) -> (en_app == 0);

    (kmac_err_type == kmac_pkg::ErrSwCmdSequence) -> (en_app == 0);
  }

endclass
