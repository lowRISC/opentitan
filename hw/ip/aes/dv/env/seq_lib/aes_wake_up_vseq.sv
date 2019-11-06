// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// basic sanity test vseq
class aes_wake_up_vseq extends aes_base_vseq;
  `uvm_object_utils(aes_wake_up_vseq)

  `uvm_object_new

  logic [127:0] plain_text   = 128'hDEADBEEFEEDDBBAABAADBEEFDEAFBEAD;
  logic [255:0] init_key     = 256'h0000111122223333444455556666777788889999AAAABBBBCCCCDDDDEEEEFFFF;
  logic [127:0] cypher_text, decrypted_text;

  task body();
    
    `uvm_info(`gfn, $sformatf("STARTING AES SEQUENCE"), UVM_DEBUG);
    `DV_CHECK_RANDOMIZE_FATAL(this)
    `uvm_info(`gfn, $sformatf("running aes sanity sequence"), UVM_DEBUG);

    wait(200ns);
    `uvm_info(`gfn, $sformatf(" \n\t ---|setting mode to encrypt"), UVM_DEBUG);
    // set mode to encrypt
    set_mode(ENCRYPT);
    wait(200ns);
   `uvm_info(`gfn, $sformatf(" \n\t ---| WRITING INIT KEY"), UVM_DEBUG);
    // add init key
    write_key(init_key);
    wait(200ns);
   `uvm_info(`gfn, $sformatf(" \n\t ---| ADDING PLAIN TEXT"), UVM_DEBUG);
   // for() begin
    add_data(plain_text);
    // poll status regster
    // end
    wait(200ns);
    // poll status register
     `uvm_info(`gfn, $sformatf("\n\t ---| Polling for data register %s", ral.status.convert2string()), UVM_DEBUG);
    poll_output_reg(cypher_text);
    `uvm_info(`gfn, $sformatf("\n\t ---|cypher text : %02h", cypher_text), UVM_DEBUG);
    // read output
    wait(2000ns);
    // set aes to decrypt
    set_mode(DECRYPT);

    `uvm_info(`gfn, $sformatf("\n\t ---|WRITING INIT KEY FOR DECRYPT: %02h", init_key), UVM_DEBUG);
    write_key(init_key);

    `uvm_info(`gfn, $sformatf("\n\t ---| WRITING CYPHER TEXT %02h", cypher_text), UVM_DEBUG);
    add_data(cypher_text);
    `uvm_info(`gfn, $sformatf("\n\t ---| Polling for data %s", ral.status.convert2string()), UVM_DEBUG);
    poll_output_reg(decrypted_text);

      if(decrypted_text == plain_text) begin
        `uvm_info(`gfn, $sformatf(" \n\t ---| YAY TEST PASSED |--- \n \t DECRYPTED: \t %02h \n\t Plaintext: \t %02h ", decrypted_text, plain_text), UVM_NONE);
      end else begin
        `uvm_fatal(`gfn, $sformatf(" \n\t ---| NOO TEST FAILED |--- \n \t DECRYPTED: \t %02h \n\t Plaintext: \t %02h ", decrypted_text, plain_text));
      end
   
    
        `uvm_info(`gfn, $sformatf("DATA ADDED "), UVM_DEBUG);
      wait(2000ns);
      

      
  endtask : body

 // virtual task start_encryption();
 //   csr_wr(.csr(ral.key), .value(32'hDEADBEEF));
 // endtask // start_encryption
  

endclass : aes_wake_up_vseq



/* ### TASK LIST ####
 * Randomize init key values
 * add radom key to all 256 bits before doing a encoding/decoding
 *

*/
