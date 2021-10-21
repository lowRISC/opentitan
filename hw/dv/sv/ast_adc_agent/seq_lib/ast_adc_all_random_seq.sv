// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Send a random item to each of the ADC channels and wait for response
class ast_adc_all_random_seq extends ast_adc_base_seq ;
  

  // Array of values to send to the respective channels
  rand ast_adc_value_sarray_t data;
  
  // Responses from the respective request channels
  REQ responses [AdcChannels];
  
  // Transaction  IDs to wait for
  int transaction_ids[AdcChannels];

  `uvm_object_utils_begin(ast_adc_all_random_seq)
    `uvm_field_sarray_int(data, UVM_DEFAULT)
    `uvm_field_sarray_object(responses, UVM_DEFAULT)
    `uvm_field_sarray_int(transaction_ids, UVM_DEFAULT)
  `uvm_object_utils_end

  `uvm_object_new

  virtual task body();
    
    // Send the requests and wait for responses
    for(int channel=0; channel<AdcChannels; channel++) begin
      `uvm_do_with(req, {
        channel == local::channel;
        data    == local::data[local::channel]; 
        })

      // Save transaction ID
      transaction_ids[channel] = req.get_transaction_id();
    end
    
    // Wait for responses
    for(int channel=0; channel<AdcChannels; channel++) begin
      get_response(responses[channel] , transaction_ids[channel]);
      `uvm_info(`gfn, {"Got response: ", responses[channel].sprint()} , UVM_HIGH)
    end

  endtask

endclass
