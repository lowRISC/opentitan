// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// basic wake up sequence in place to verify that environment is hooked up correctly.
// static test that is running same data set every time
class aes_wake_up_vseq extends aes_base_vseq;
  `uvm_object_utils(aes_wake_up_vseq)

  `uvm_object_new

  bit [31:0]  plain_text[$]   = {32'hDEADBEEF, 32'hEEDDBBAA, 32'hBAADBEEF, 32'hDEAFBEAD};
  logic [255:0] init_key      = 256'h0000111122223333444455556666777788889999AAAABBBBCCCCDDDDEEEEFFFF;
  bit [31:0]    cypher_text[$];
  bit [31:0]    decrypted_text[$];
  logic [31:0]  read_text[$];

  string  str="";





  task body();

    `uvm_info(`gfn, $sformatf("STARTING AES SEQUENCE"), UVM_LOW)
    `DV_CHECK_RANDOMIZE_FATAL(this)
    `uvm_info(`gfn, $sformatf("running aes sanity sequence"), UVM_LOW)

    `uvm_info(`gfn, $sformatf(" \n\t ---|setting mode to encrypt"), UVM_LOW)
    // set mode to encrypt
    set_mode(ENCRYPT);


    `uvm_info(`gfn, $sformatf(" \n\t ---| WRITING INIT KEY  %02h", init_key), UVM_LOW)

    write_key(init_key);
    cfg.clk_rst_vif.wait_clks(20);

    `uvm_info(`gfn, $sformatf(" \n\t ---| ADDING PLAIN TEXT"), UVM_LOW)

    add_data(plain_text);

    cfg.clk_rst_vif.wait_clks(20);
    // poll status register

    `uvm_info(`gfn, $sformatf("\n\t ---| Polling for data register %s",
                              ral.status.convert2string()), UVM_DEBUG)

    read_data(cypher_text);

    // read output
    `uvm_info(`gfn, $sformatf("\n\t ------|WAIT 0 |-------"), UVM_LOW)
    cfg.clk_rst_vif.wait_clks(20);

    // set aes to decrypt
    set_mode(DECRYPT);
    cfg.clk_rst_vif.wait_clks(20);
    `uvm_info(`gfn, $sformatf("\n\t ---|WRITING INIT KEY FOR DECRYPT: %02h", init_key), UVM_LOW)
    write_key(init_key);
    cfg.clk_rst_vif.wait_clks(20);
    `uvm_info(`gfn, $sformatf("\n\t ---| WRITING CYPHER TEXT"), UVM_LOW)
    add_data(cypher_text);

    `uvm_info(`gfn, $sformatf("\n\t ---| Polling for data %s", ral.status.convert2string()),
              UVM_DEBUG)

    cfg.clk_rst_vif.wait_clks(20);

    read_data(decrypted_text);
    foreach(decrypted_text[i]) begin
      `uvm_info(`gfn, $sformatf("\n\t ----| decrypted text elememt [%d] : %02h", i, decrypted_text[i]), UVM_LOW)
    end

    foreach(plain_text[i]) begin
      if(plain_text[i] != decrypted_text[i]) begin
        str = $sformatf(" \n\t ---| OH NOO TEST FAILED AT POS %d|--- \n \t DECRYPTED: \t %02h \n\t Plaintext: \t %02h ",
                        i, decrypted_text[i], plain_text[i]);
        `uvm_fatal(`gfn, $sformatf("%s",str));
      end

    end

    `uvm_info(`gfn, $sformatf(" \n\t ---| YAY TEST PASSED |--- \n \t "), UVM_NONE)
  endtask : body
endclass : aes_wake_up_vseq
