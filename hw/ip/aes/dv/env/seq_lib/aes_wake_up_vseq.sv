// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// basic wake up sequence in place to verify that environment is hooked up correctly.
// static test that is running same data set every time
class aes_wake_up_vseq extends aes_base_vseq;
  `uvm_object_utils(aes_wake_up_vseq)

  `uvm_object_new


  parameter bit       ENCRYPT = 1'b0;
  parameter bit       DECRYPT = 1'b1;

  bit [3:0] [31:0]    plain_text       = 128'hDEADBEEFEEDDBBAABAADBEEFDEAFBEAD;
  logic [255:0]       init_key [2]     = '{256'h0000111122223333444455556666777788889999AAAABBBBCCCCDDDDEEEEFFFF, 256'h0};
  bit [3:0] [31:0]    cypher_text;
  bit [3:0] [31:0]    decrypted_text;
  logic [3:0] [31:0]  read_text;
  string              str="";
  bit                 do_b2b = 0;


  task body();

    `uvm_info(`gfn, $sformatf("STARTING AES SEQUENCE"), UVM_LOW)


    `DV_CHECK_RANDOMIZE_FATAL(this)

    `uvm_info(`gfn, $sformatf(" \n\t ---|setting operation to encrypt"), UVM_HIGH)
    // set operation to encrypt
    set_operation(ENCRYPT);

    `uvm_info(`gfn, $sformatf(" \n\t ---| WRITING INIT KEY \n\t ----| SHARE0 %02h \n\t ---| SHARE1 %02h ", init_key[0], init_key[1]), UVM_HIGH)
    write_key(init_key, do_b2b);
    cfg.clk_rst_vif.wait_clks(20);

    `uvm_info(`gfn, $sformatf(" \n\t ---| ADDING PLAIN TEXT"), UVM_HIGH)

    add_data(plain_text, do_b2b);

    cfg.clk_rst_vif.wait_clks(20);
    // poll status register

    `uvm_info(`gfn, $sformatf("\n\t ---| Polling for data register %s",
                              ral.status.convert2string()), UVM_DEBUG)

    csr_spinwait(.ptr(ral.status.output_valid) , .exp_data(1'b1));
    read_data(cypher_text, do_b2b);
    // read output
    `uvm_info(`gfn, $sformatf("\n\t ------|WAIT 0 |-------"), UVM_HIGH)
    cfg.clk_rst_vif.wait_clks(20);

    // set aes to decrypt
    set_operation(DECRYPT);
    cfg.clk_rst_vif.wait_clks(20);
    `uvm_info(`gfn, $sformatf("\n\t ---| WRITING INIT KEY \n\t ----| SHARE0 %02h \n\t ---| SHARE1 %02h ", init_key[0], init_key[1]), UVM_HIGH)
    write_key(init_key, do_b2b);
    cfg.clk_rst_vif.wait_clks(20);
    `uvm_info(`gfn, $sformatf("\n\t ---| WRITING CYPHER TEXT"), UVM_HIGH)
    add_data(cypher_text, do_b2b);


    `uvm_info(`gfn, $sformatf("\n\t ---| Polling for data %s", ral.status.convert2string()),
              UVM_DEBUG)

    cfg.clk_rst_vif.wait_clks(20);
    csr_spinwait(.ptr(ral.status.output_valid) , .exp_data(1'b1));
    read_data(decrypted_text, do_b2b);
    //need scoreboard disable
    foreach(plain_text[i]) begin
      if(plain_text[i] != decrypted_text[i]) begin
        str = $sformatf(" \n\t ---| OH NOO TEST FAILED AT POS %d|--- \n \t DECRYPTED: \t %02h \n\t Plaintext: \t %02h ",
                        i, decrypted_text[i], plain_text[i]);
        `uvm_fatal(`gfn, $sformatf("%s",str));
      end

    end
    foreach(decrypted_text[i]) begin
      `uvm_info(`gfn,
                $sformatf("\n\t ----| decrypted text elememt [%d] : %02h", i, decrypted_text[i]), UVM_HIGH)
    end

    `uvm_info(`gfn, $sformatf(" \n\t ---| YAY TEST PASSED |--- \n \t "), UVM_NONE)
  endtask : body
endclass : aes_wake_up_vseq
