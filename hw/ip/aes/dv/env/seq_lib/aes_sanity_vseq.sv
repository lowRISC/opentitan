// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// basic sanity test vseq
class aes_sanity_vseq extends aes_base_vseq;
  `uvm_object_utils(aes_sanity_vseq)

  `uvm_object_new

  task body();
    
    `uvm_info(`gfn, $sformatf("STARTING AES SEQUENCE"), UVM_LOW);
    `DV_CHECK_RANDOMIZE_FATAL(this)
    `uvm_info(`gfn, $sformatf("running aes sanity sequence"), UVM_LOW);

    wait(200ns);
      

      
  endtask : body

 // virtual task start_encryption();
 //   csr_wr(.csr(ral.key), .value(32'hDEADBEEF));
 // endtask // start_encryption
  

endclass : aes_sanity_vseq



/* ### TASK LIST ####
 * Randomize init key values
 * add radom key to all 256 bits before doing a encoding/decoding
 *

*/
