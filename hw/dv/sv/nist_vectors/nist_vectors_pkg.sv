// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// this package reads the NIST vector files, and parses msg, key, and expect digest
package nist_vectors_pkg;
  // dep packages
  import uvm_pkg::*;

  // macro includes
  `include "uvm_macros.svh"

  // declare string and vectors
  string header          = "nist vector pkg";
  string sha_file_list[] = {"SHA256ShortMsg.rsp", "SHA256LongMsg.rsp"};
  string nist_vectors_dir;

  typedef struct {
    int        msg_length_byte;
    bit [7:0]  msg[];
    bit [31:0] keys[8];
    bit [31:0] exp_digest[8];
  } nist_vectors_t;

  // convert a data of string to an array of bytes
  function automatic void str_to_bytes(string str, output bit [7:0] bytes[]);
    int array_size = str.len() / 2;
    `uvm_info(header, $sformatf("str_to_bytes: string = %s, len = %0d", str, array_size), UVM_HIGH)
    bytes = new[array_size];
    foreach (bytes[i]) bytes[i] = str.substr(i * 2, i * 2 + 1).atohex();
  endfunction : str_to_bytes

  // this funciton gets vector path from plusargs, next function open the file with path provided
  // separate to two functions for the user flexbility to hard-code path or use plusargs.
  function automatic void get_nist_vectors_path(input string file_name, output string path);
    if (nist_vectors_dir == "") begin
      if (!$value$plusargs("nist_vectors_dir=%s", nist_vectors_dir)) begin
        `uvm_fatal(header, "Cannot find $plusarg for the nist_vectors_dir.")
      end
    end
    path = {nist_vectors_dir, file_name};
  endfunction : get_nist_vectors_path

  function automatic void open_file(input string path, output int fd);
    fd = $fopen(path, "r");
    if (!fd) begin
      `uvm_fatal(header, $sformatf("Cannot access file: %s", path))
    end else begin
      `uvm_info(header, $sformatf("input nist vector path is %s", path), UVM_HIGH)
    end
  endfunction : open_file

  // parse sha msg, msg length, and exp_digest from a nist vectors file
  function automatic void parse_sha(input int index, ref nist_vectors_t parsed_vectors[]);
    int        fd;
    bit [7:0]  bytes[];
    string     name, str_data, nist_vectors_path;

    get_nist_vectors_path(sha_file_list[index], nist_vectors_path);

    open_file(nist_vectors_path, fd);

    while (!$feof(fd)) begin
      // read each line split by "="
      // Example "Len = 1304": name = "Len", str_data = "1304"
      void'($fscanf(fd, "%s = %s", name, str_data));
      if (name == "Len") begin
        nist_vectors_t sha_vector;
        // get msg length
        sha_vector.msg_length_byte = str_data.atoi() / 8;

        // get msg
        void'($fscanf(fd, "%s = %s", name, str_data));
        // special handle for msg length = 0
        // nist vectors format is: Msg = 00, but since len = 0, actual wr msg should be empty
        if (sha_vector.msg_length_byte != 0) str_to_bytes(str_data, sha_vector.msg);

        // get expected digest
        void'($fscanf(fd, "%s = %s", name, str_data));
        str_to_bytes(str_data, bytes);
        sha_vector.exp_digest = {>>byte{bytes}};

        // add the parsed vector to the output
        parsed_vectors = {parsed_vectors, sha_vector};
      end
    end
    $fclose(fd);
  endfunction : parse_sha

endpackage
