// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This package reads in NIST test vector files, and parses all relevant information for each
// test vector into a `test_vectors_t` struct.
//
// As of right now, this package is meant only for use with the HMAC and KMAC HWIPs.

package test_vectors_pkg;
  // dep packages
  import uvm_pkg::*;
  import str_utils_pkg::*;

  // macro includes
  `include "uvm_macros.svh"

  // declare string and vectors
  string header                 = "test_vectors_pkg";
  string sha_file_list[]        = {"vectors/sha/sha256/SHA256ShortMsg.rsp",
                                   "vectors/sha/sha256/SHA256LongMsg.rsp"
                                  };
  string hmac_file_list[]       = {"vectors/hmac/HMAC_RFC4868.rsp"};
  string sha3_224_file_list[]   = {"vectors/sha/sha3/SHA3_224ShortMsg.rsp",
                                   "vectors/sha/sha3/SHA3_224LongMsg.rsp"
                                  };
  string sha3_256_file_list[]   = {"vectors/sha/sha3/SHA3_256ShortMsg.rsp",
                                   "vectors/sha/sha3/SHA3_256LongMsg.rsp"
                                  };
  string sha3_384_file_list[]   = {"vectors/sha/sha3/SHA3_384ShortMsg.rsp",
                                   "vectors/sha/sha3/SHA3_384LongMsg.rsp"
                                  };
  string sha3_512_file_list[]   = {"vectors/sha/sha3/SHA3_512ShortMsg.rsp",
                                   "vectors/sha/sha3/SHA3_512LongMsg.rsp"
                                  };
  string shake_128_file_list[]  = {"vectors/xof/shake/SHAKE128ShortMsg.rsp",
                                   "vectors/xof/shake/SHAKE128LongMsg.rsp",
                                   "vectors/xof/shake/SHAKE128VariableOut.rsp"
                                  };
  string shake_256_file_list[]  = {"vectors/xof/shake/SHAKE256ShortMsg.rsp",
                                   "vectors/xof/shake/SHAKE256LongMsg.rsp",
                                   "vectors/xof/shake/SHAKE256VariableOut.rsp"
                                  };
  string cshake_file_list[]     = {"vectors/xof/cshake/CSHAKE128Ex1.rsp",
                                   "vectors/xof/cshake/CSHAKE256Ex1.rsp"
                                  };
  string kmac_file_list[]       = {"vectors/xof/kmac/KMAC128Ex1.rsp",
                                   "vectors/xof/kmac/KMAC256Ex1.rsp"
                                  };
  string kmac_xof_file_list[]   = {"vectors/xof/kmac/KMAC128XOFEx1.rsp",
                                   "vectors/xof/kmac/KMAC256XOFEx1.rsp"
                                  };
  string test_vectors_dir;

  typedef struct {
    // Security strenght of the algorithm.
    int security_strength;

    // Length of the input message in bytes.
    // For reporting purposes.
    int msg_length_byte;

    // The input message as a byte array for variable length input.
    bit [7:0] msg[];

    // Length of the input key in word (4 bytes).
    int key_length_word;

    // The input key array (if applicable), represented as an array of 4-byte elements.
    // This is ok since all acceptable key sizes for HMAC/KMAC are 4-byte-aligned.
    bit [31:0] keys[];

    // Output length in bytes;
    int digest_length_byte;

    // The expected digest as a byte array for variable length output.
    bit [7:0] exp_digest[];

    // The function name, represented as a string. Used for CSHAKE.
    string function_name_str;

    // The customization string. Used for CSHAKE and KMAC.
    string customization_str;
  } test_vectors_t;

  // Converts a string to an array of bytes.
  //
  // Note that we cannot use the str_utils_pkg::str_to_bytes() implementation here.
  // The str_utils_pkg implementation is intended for general purpose usage to convert some
  // arbitrary string, such as "abcd" into a stream of 4 bytes.
  //
  // However in the test_vectors_pkg, the test vector strings we parse in are string
  // representations of the intended bytestream to begin with, e.g. if we parse in
  // the string "0a1b" it should directly translate to the bytestream {0x0a, 0x1b}.
  //
  // This functionality is achieved by this custom byte conversion function.
  function automatic void str_to_bytes(string str, output bit [7:0] bytes[]);
    int array_size = str.len() / 2;
    `uvm_info(header, $sformatf("str_to_bytes: string = %s, len = %0d", str, array_size), UVM_HIGH)
    bytes = new[array_size];
    foreach (bytes[i]) begin
      string tmp_str = str.substr(i * 2, i * 2 + 1);
      bytes[i] = tmp_str.atohex();
    end
  endfunction : str_to_bytes

  // This function parses strings of the form "<stringA> = <stringB>" found in test vector files,
  // extracting <stringA> and <stringB> to the outputs.
  // It is assumed that the input string is formatted correctly.
  // Some examples of how test vector files format these strings are as follows:
  //
  // 1) Len = 128
  // 2) S = Email Signature
  function automatic void get_entry_and_data(string line, output string entry, output string value);
    string entries[$];

    str_split(.s(line), .result(entries), .delim("="));

    entry = entries.pop_front();
    value = entries.pop_front();

  endfunction : get_entry_and_data

  // This function gets the top level directory of the test vectors from a runtime plusarg.
  function automatic void get_test_vectors_path(input string file_name, output string path);
    if (test_vectors_dir == "") begin
      if (!$value$plusargs("test_vectors_dir=%s", test_vectors_dir)) begin
        `uvm_fatal(header, "Cannot find $plusarg for the test_vectors_dir.")
      end
    end
    path = {test_vectors_dir, "/", file_name};
  endfunction : get_test_vectors_path

  // This function opens the file at the given path, and outputs its file descriptor.
  function automatic void open_file(input string path, output int fd);
    fd = $fopen(path, "r");
    if (!fd) begin
      `uvm_fatal(header, $sformatf("Cannot access file: %s", path))
    end else begin
      `uvm_info(header, $sformatf("input test vector path is %s", path), UVM_HIGH)
    end
  endfunction : open_file

  // This function parses all NIST test vectors for SHA256/HMAC/SHA3SHAKE/CSHAKE/KMAC.
  //
  // The test vectors for these algorithms can be formatted in a variety of ways:
  //
  // 1) This format is used for SHA256/SHA3 test vectors.
  //
  // Len = ...
  // Msg = ...
  // MD = ...
  //
  // 2) This format is used for HMAC test vectors.
  //
  // Len = ...
  // Key = ...
  // Msg = ...
  // MD = ...
  //
  // 3) This format is used for SHAKE test vectors with standard output digest length.
  // Note that the security strength and output length are specified once at the top of the file,
  // and will apply to every test vector in the corresponding file.
  //
  // [SecurityStrength = ...]
  // [Outputlen = ...]
  //
  // Len = ...
  // Msg = ...
  // Output = ...
  //
  // 4) This format is used for SHAKE test vectors with variable output digest length.
  // Note that the security strength and input message length are specified once at the top of the
  // file and will apply to every test vector in the corresponding file.
  //
  // [SecurityStrength = ...]
  // [Input Length = ...]
  //
  // COUNT = ...
  // OutputLen = ...
  // Msg = ...
  // Output = ...
  //
  // 5) This format is used for CSHAKE test vectors.
  // The security strength is specified in brackets at the top of the file and will apply to every
  // test vector in the corresponding file.
  //
  // [SecurityStrength = ...]
  //
  // N = ...
  // S = ...
  // MsgLen = ...
  // Msg = ...
  // OutputLen = ...
  // Output = ...
  //
  // 6) This format is used for KMAC test vectors.
  // The security strength is specified in brackets at the top of the file and will apply to every
  // test vector in the corresponding file.
  //
  // [SecurityStrength = ...]
  //
  // S = ...
  // KeyLen = ...
  // Key = ...
  // MsgLen = ...
  // Msg = ...
  // OutputLen = ...
  // Output = ...
  //
  //
  // This function is capable of parsing every type of test vector shown above.
  //
  // This function will read in each line of the test vector file, and will store the relevant
  // information for each vector into a `test_vectors_t` struct, appending the new object to the
  // `parsed_vectors` queue once it is complete.
  //
  // We know that a test vector object is complete once we parse an "<MD/Output> = ..." line,
  // as the single consistency in all NIST test vectors is that the output data is the last entry of
  // each test vector description.
  function automatic void get_hash_test_vectors(
    string             test_name,
    ref test_vectors_t parsed_vectors[],
    input bit          reverse_key = 1
  );
    int fd;
    bit [7:0] bytes[];
    string line, entry_name, entry_data, path;
    int bracket_end_idx;

    // Useful if the test vector file has a global security strength specified at the top.
    int global_security_strength = 0;

    // Useful if the test vector file has a global input length specified at the top.
    int global_input_length_bits = 0;

    // Useful if the test vector file has a global output length specified at the top.
    int global_output_length_bits = 0;

    test_vectors_t vector;

    // Open the test vector file.
    get_test_vectors_path(test_name, path);
    open_file(path, fd);

    while (!$feof(fd)) begin
      // Get the next line
      $fgets(line, fd);

      // Get global security strength, input length, output length
      if (line.getc(0) == "[") begin
        bracket_end_idx = str_find(line, "]");
        if (bracket_end_idx == -1) begin
          `uvm_fatal(header, $sformatf("Malformed string in %s: %s", test_name, line))
        end
        line = line.substr(1, bracket_end_idx-1);
        if (str_find(line, "=") > 0) begin
          get_entry_and_data(line, entry_name, entry_data);
          // Globally set information should not be an empty string
          if (entry_data == "") begin
            `uvm_fatal(header, $sformatf("Malformed string in %s: %s", test_name, line))
          end

          case (entry_name)
            "SecurityStrength": begin
              global_security_strength = entry_data.atoi();
              vector.security_strength = global_security_strength;
            end
            "L", "Outputlen", "OutputLen", "OutputLength": begin
              global_output_length_bits = entry_data.atoi();
            end
            "Inputlen", "InputLen", "InputLength": begin
              global_input_length_bits = entry_data.atoi();
            end
            default: begin
              // If for some reason we see a matching line format but incorrect information,
              // continue to read in the next line of the file.
              continue;
            end
          endcase
        end
      end else if (str_find(line, "=") > 0) begin
        // Line read in did not contain global information.
        // We can now search for actual test vector data.
        //
        // Note that we will only ever meet this condition once we have finished reading any global
        // information at the top of the test vector file.

        get_entry_and_data(line, entry_name, entry_data);

        // If there is a global input length, we know that we are parsing a variable length SHAKE
        // test vector file.  // Thus it is guaranteed that the input length will not be set anywhere else.
        if (global_input_length_bits != 0) begin
          vector.msg_length_byte = global_input_length_bits / 8;
        end else if (global_output_length_bits != 0) begin
          // If there is a global output length, we know that we are parsing a known-length SHAKE
          // test vector file.
          // Thus it is guaranteed that the output length will not be set anywhere else.
          vector.digest_length_byte = global_output_length_bits / 8;
        end

        case (entry_name)
          "N": begin
            // The function name, only used for CSHAKE.
            vector.function_name_str = entry_data;
          end
          "S": begin
            // The customization string, only used for CSHAKE and KMAC.
            vector.customization_str = entry_data;
          end
          "Len", "MsgLen": begin
            // Input message length in bits.
            //
            // If a global input length is defined, this case will never be reached.
            vector.msg_length_byte = entry_data.atoi() / 8;
          end
          "Msg": begin
            // The input message.
            // If an empty message is desired, we need to manually clear the message array,
            // as NIST defines an empty message as 8'h00 (which will produce an incorect digest).
            if (vector.msg_length_byte == 0) begin
              vector.msg.delete();
            end else begin
              str_to_bytes(entry_data, vector.msg);
            end
          end
          "KeyLen": begin
            vector.key_length_word = entry_data.atoi() / 32;
          end
          "Key": begin
            str_to_bytes(entry_data, bytes);
            // If no keyword `KeyLen` but has `Key`, use the default key len: 256 bits
            if (vector.key_length_word == 0) vector.key_length_word = 8;
            vector.keys = new[vector.key_length_word];
            for (int i = 0; i < vector.key_length_word; i++) begin
              bit [7:0] key_bytes[] = new[4];
              // parsed key will always be a multiple of 4 bytes
              for (int j = 0; j < 4; j++) begin
                key_bytes[j] = bytes[i*4 + j];
              end
              if (reverse_key) vector.keys[i] = {<< byte {key_bytes}};
              else             vector.keys[i] = {>> byte {key_bytes}};

              // Streaming operations using the `with` syntax is currently unsupported by
              // the Verible linter (Issue #5280).
              // Comment this out for now, and uncomment once Verible support is added.
              //
              //vector.keys[i] = {<< byte {bytes with [i*4 +: 4]}};
            end
          end
          "Outputlen", "OutputLen": begin
            // Output digest length in bits
            //
            // If a global output length is defined, this case will never be reached.
            vector.digest_length_byte = entry_data.atoi() / 8;
          end
          "MD", "Output": begin
            str_to_bytes(entry_data, vector.exp_digest);

            // The output is the last entry for each test vector, so now
            // we need to add the completed test_vector object to the list.
            parsed_vectors = {parsed_vectors, vector};
          end
          default: begin
            continue;
          end
        endcase
      end else begin
        continue;
      end
    end

    $fclose(fd);

  endfunction : get_hash_test_vectors

endpackage
