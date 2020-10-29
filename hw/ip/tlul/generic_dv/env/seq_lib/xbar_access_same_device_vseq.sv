// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// test all hosts to access same device
// randomly pick one device, if host can acess this device, change it to only access this device
// repeat above for a few times
class xbar_access_same_device_vseq extends xbar_random_vseq;

  `uvm_object_utils(xbar_access_same_device_vseq)
  `uvm_object_new

  // more req to hit max outstanding number
  function void pre_randomize();
    min_req_cnt = 200;
    max_req_cnt = 300;
    super.pre_randomize();
  endfunction

  virtual function void update_host_seq();
    int device_id = $urandom_range(0, xbar_devices.size - 1);

    if (cfg.en_cov) cov.same_device_access_cg.sample(device_id);
    `uvm_info(`gfn, $sformatf("Picked device (%0s) for all hosts to access",
              xbar_devices[device_id].device_name), UVM_HIGH)

    // change host to only access the picked device
    foreach (host_seq[i]) begin
      // if the selected device_id is a valid ID for this host, only store this id to use
      if (device_id inside {host_seq[i].valid_device_id}) begin
        host_seq[i].valid_device_id.delete();
        host_seq[i].valid_device_id.push_back(device_id);
        `uvm_info(`gfn, $sformatf("Host (%0s) only accesses device (%0s)",
                  host_seq[i].get_name(), xbar_devices[device_id].device_name), UVM_HIGH)
      end
    end
  endfunction

endclass
