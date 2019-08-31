// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
class xbar_factory;

  function xbar_seq_base get_xbar_seq(string name);
    if (name == "host_dir_seq") begin
      host_dir_seq ob;
      ob = new("host_dir_seq");
      return ob;
    end else if (name == "host_rand_seq") begin
      host_rand_seq ob;
      ob = new("host_rand_seq");
      return ob;
    end else if (name == "host_socket1n_seq") begin
      host_socket1n_seq ob;
      ob = new("host_socket1n_seq");
      return ob;
    end

  endfunction : get_xbar_seq

endclass
