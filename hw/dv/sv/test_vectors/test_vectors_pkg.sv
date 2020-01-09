// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// this package reads test vector files, and parses msg, key, and expect digest
package test_vectors_pkg;
  // dep packages
  import uvm_pkg::*;

  // macro includes
  `include "uvm_macros.svh"

  // declare string and vectors
  string header           = "test vector pkg";
  string sha_file_list[]  = {"SHA256ShortMsg.rsp", "SHA256LongMsg.rsp"};
  string hmac_file_list[] = {"HMAC_RFC4868.rsp"};
  string test_vectors_dir;

  typedef struct {
    int        msg_length_byte;
    bit [7:0]  msg[];
    bit [31:0] keys[8];
    bit [31:0] exp_digest[8];
  } test_vectors_t;

  // convert a data of string to an array of bytes
  function automatic void str_to_bytes(string str, output bit [7:0] bytes[]);
    int array_size = str.len() / 2;
    `uvm_info(header, $sformatf("str_to_bytes: string = %s, len = %0d", str, array_size), UVM_HIGH)
    bytes = new[array_size];
    foreach (bytes[i]) begin
      string tmp_str = str.substr(i * 2, i * 2 + 1);
      bytes[i] = tmp_str.atohex();
    end
  endfunction : str_to_bytes

  // this funciton gets vector path from plusargs, next function open the file with path provided
  // separate to two functions for the user flexbility to hard-code path or use plusargs
  function automatic void get_test_vectors_path(input string file_name, output string path);
    if (test_vectors_dir == "") begin
      if (!$value$plusargs("test_vectors_dir=%s", test_vectors_dir)) begin
        `uvm_fatal(header, "Cannot find $plusarg for the test_vectors_dir.")
      end
    end
    path = {test_vectors_dir, "/", file_name};
  endfunction : get_test_vectors_path

  function automatic void open_file(input string path, output int fd);
    fd = $fopen(path, "r");
    if (!fd) begin
      `uvm_fatal(header, $sformatf("Cannot access file: %s", path))
    end else begin
      `uvm_info(header, $sformatf("input test vector path is %s", path), UVM_HIGH)
    end
  endfunction : open_file

  // parse sha/hmac msg, key (if hmac_en), msg length, and exp_digest from a test vectors file
  // support test vectors files with a nist vector format
  function automatic void parse_sha_hmac(bit hmac_en, int index,
                                         ref test_vectors_t parsed_vectors[]);
    int        fd;
    bit [7:0]  bytes[];
    string     name, str_data, test_vectors_path;

    if (hmac_en) get_test_vectors_path(hmac_file_list[index], test_vectors_path);
    else get_test_vectors_path(sha_file_list[index], test_vectors_path);

    open_file(test_vectors_path, fd);

    while (!$feof(fd)) begin
      // read each line split by "="
      // Example "Len = 1304": name = "Len", str_data = "1304"
      void'($fscanf(fd, "%s = %s", name, str_data));
      if (name == "Len") begin
        test_vectors_t vector;
        // get msg length
        vector.msg_length_byte = str_data.atoi() / 8;

        // get key if hmac_en
        if (hmac_en) begin
          void'($fscanf(fd, "%s = %s", name, str_data));
          str_to_bytes(str_data, bytes);
          vector.keys = {>>byte{bytes}};
        end

        // get msg
        void'($fscanf(fd, "%s = %s", name, str_data));
        // special handle for msg length = 0
        // nist vectors format is: Msg = 00, but since len = 0, actual wr msg should be empty
        if (vector.msg_length_byte != 0) str_to_bytes(str_data, vector.msg);

        // get expected digest
        void'($fscanf(fd, "%s = %s", name, str_data));
        str_to_bytes(str_data, bytes);
        vector.exp_digest = {>>byte{bytes}};

        // add the parsed vector to the output
        parsed_vectors = {parsed_vectors, vector};
      end
    end
    $fclose(fd);
  endfunction : parse_sha_hmac

endpackage
