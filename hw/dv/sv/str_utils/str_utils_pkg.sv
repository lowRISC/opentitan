// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package str_utils_pkg;
  `include "dv_macros.svh"

  string msg_id = "str_utils_pkg";

  // Returns 1 if string 's' has substring 'sub' within the given index range. 0 Otherwise.
  function automatic bit str_has_substr(string s, string sub, int range_lo = 0, int range_hi = -1);
    if (range_hi < 0 || range_hi >= s.len()) range_hi = s.len() - 1;
    for (int i = range_lo; i <= (range_hi - sub.len() + 1); i++) begin
      if (s.substr(i, i + sub.len() - 1) == sub) begin
        return 1;
      end
    end
    return 0;
  endfunction : str_has_substr

  // Returns 1 when string 's' starts with substring 'sub'.
  function automatic bit str_starts_with(string s, string sub);
    return s.substr(0, sub.len() - 1) == sub;
  endfunction

  // Returns 1 when string 's' ends with substring 'sub'.
  function automatic bit str_ends_with(string s, string sub);
    return s.substr(s.len() - sub.len(), s.len() - 1) == sub;
  endfunction

  // Returns the index of first occurrence of string 'sub' within string 's''s given index range.
  // Returns -1 otherwise.
  function automatic int str_find(string s, string sub, int range_lo = 0, int range_hi = -1);
    if (range_hi < 0 || range_hi >= s.len()) range_hi = s.len() - 1;
    for (int i = range_lo; i <= (range_hi - sub.len() + 1); i++) begin
      if (s.substr(i, i + sub.len() - 1) == sub) begin
        return i;
      end
    end
    return -1;
  endfunction : str_find

  // Returns the index of last occurrence of string 'sub' within string 's''s given index range.
  // Returns -1 otherwise.
  function automatic int str_rfind(string s, string sub, int range_lo = 0, int range_hi = -1);
    if (range_hi < 0 || range_hi >= s.len()) range_hi = s.len() - 1;
    for (int i = (range_hi - sub.len() + 1); i >= range_lo; i--) begin
      if (s.substr(i, i + sub.len() - 1) == sub) begin
        return i;
      end
    end
    return -1;
  endfunction : str_rfind

  // Find the first match string 'sub' in 's' and replace it with 'new_sub'.
  // TODO: Add support for global replacement.
  function automatic string str_replace(string s, string sub, string new_sub);
    string str_before_sub, str_after_sub;
    int lo_idx = str_find(s, sub);

    // check sub string exists
    `DV_CHECK_NE_FATAL(lo_idx, -1, $sformatf("sub string %s doesn't exist in %s", sub, s), msg_id)

    // the new_str contains 3 portions {str_before_sub, new_sub, str_after_sub}
    if (lo_idx > 0) str_before_sub = s.substr(0, lo_idx - 1);
    if (lo_idx + sub.len() < s.len()) str_after_sub = s.substr(lo_idx + sub.len(), s.len() - 1);

    return {str_before_sub, new_sub, str_after_sub};
  endfunction : str_replace

  // Strips a given set of characters in string 's'.
  //
  // The set of characters to strip is provided as a string. If not set, all whitespace characters
  // are stripped by default. Stripping is done at both ends, unless the user turns off the
  // stripping from one of the ends.
  function automatic string str_strip(string s,
                                      string chars = " \t\n",
                                      bit lstrip = 1'b1,
                                      bit rstrip = 1'b1);
    byte chars_q[$];
    if (chars == "") return s;
    foreach (chars[i]) chars_q.push_back(chars.getc(i));

    if (lstrip) begin
      int i = 0;
      while (s.getc(i) inside {chars_q}) i++;
      s = s.substr(i, s.len() - 1);
    end

    if (rstrip) begin
      int i = s.len() - 1;
      while (s.getc(i) inside {chars_q}) i--;
      s = s.substr(0, i);
    end
    return s;
  endfunction : str_strip

  // Splits the input `string` on the given single-character delimiter `delim`.
  //
  // The split tokens are pushed into the `result` queue. The whitespaces on each split token are
  // stripped by default, which can be turned off.
  // TODO: allow arbitrary length delimiter.
  function automatic void str_split(input  string s,
                                    output string result[$],
                                    input  byte   delim = " ",
                                    input  bit    strip_whitespaces = 1'b1);
    string sub;
    bit in_quotes;
    result = {};
    foreach (s[i]) begin
      if (s[i] == "\"") begin
        in_quotes = !in_quotes;
      end
      if ((s.getc(i) == delim) && !in_quotes) begin
        if (strip_whitespaces) sub = str_strip(sub);
        if (sub != "") result.push_back(sub);
        sub = "";
      end else begin
        sub = {sub, s[i]};
      end
      if (i == s.len() - 1) begin
        if (strip_whitespaces) sub = str_strip(sub);
        if (sub != "") result.push_back(sub);
      end
    end
  endfunction : str_split

  // Returns a string concatenated from the provided queue of strings 's'.
  //
  // The concatenation is performed using the 'delim' arg as the delimiter.
  function automatic string str_join(string s[$], string delim = " ");
    string str;
    foreach (s[i]) begin
      str = {str, s[i], delim};
    end
    if (str != "") begin
      str = str.substr(0, str.len() - delim.len() - 1);
    end
    return str;
  endfunction : str_join

  // Cuts sections (such as comments) from string s starting and ending with provided substrings.
  //
  // start_delim: substring representing the start of section to be removed (e.g. "//", "/*").
  // end_delim: substring representing the end of the section to be removed (e.g. "\n", "*/").
  // remove_start_delim: include the start_delim substring in the removal.
  // remove_end_delim: include the end_delim substring in the removal.
  function automatic string str_remove_sections(string s,
                                                string start_delim,
                                                string end_delim,
                                                bit remove_start_delim = 1,
                                                bit remove_end_delim = 1);
      int start_idx, end_idx;
      start_idx = str_utils_pkg::str_find(s, start_delim);
      while (start_idx != -1) begin
        int rm_start_idx, rm_end_idx;
        rm_start_idx = remove_start_delim ? start_idx : start_idx + start_delim.len() - 1;
        end_idx = str_utils_pkg::str_find(s, end_delim, .range_lo(start_idx + start_delim.len()));
        if (end_idx == -1) break;
        rm_end_idx = remove_end_delim ? end_idx + end_delim.len() - 1 : end_idx - 1;
        s = str_utils_pkg::str_replace(s, s.substr(rm_start_idx, rm_end_idx), "");
        start_idx = str_utils_pkg::str_find(s, start_delim, .range_lo(end_idx + end_delim.len()));
      end
      return s;
  endfunction

  // Converts a string to an array of bytes.
  function automatic void str_to_bytes(string s, output byte bytes[]);
    bytes = new[s.len()];
    foreach (bytes[i]) begin
      bytes[i] = s.getc(i);
    end
  endfunction : str_to_bytes

  // Converts an array of bytes to a string.
  function automatic string bytes_to_str(byte bytes[]);
    string s;
    foreach (bytes[i]) begin
      s = {s, string'(bytes[i])};
    end
    return s;
  endfunction

  /************************/
  /* File path functions. */
  /************************/

  // Returns the dirname of the file.
  //
  // Examples:
  // path/to/foo.bar    => path/to
  // path/to/foo/bar    => path/to/foo
  // path/to/foo/bar/   => path/to/foo
  // path/to/foo/bar/.  => path/to/foo/bar
  // /                  => /
  function automatic string str_path_dirname(string filename);
    int idx;
    string dirname;

    if (filename == "/") return filename;
    filename = str_strip(.s(filename), .chars("/"), .lstrip(1'b0));
    idx = str_rfind(.s(filename), .sub("/"));
    if (idx == -1) idx = filename.len();
    if (idx == 0) idx++;
    dirname = filename.substr(0, idx - 1);
    return dirname;
  endfunction : str_path_dirname

  // Returns the basename of the file.
  //
  // Optionally, it takes a bit flag to drop the extension from the basename if desired.
  // Examples:
  // path/to/foo.bar    => (foo.bar, foo)
  // path/to/foo/bar    => (bar, bar)
  // path/to/foo/bar/   => (bar, bar)
  // path/to/foo/bar/.  => (., .)
  // /                  => (/, /)
  function automatic string str_path_basename(string filename, bit drop_extn = 1'b0);
    int idx;
    string basename;

    if (filename == "/") return filename;
    filename = str_strip(.s(filename), .chars("/"), .lstrip(1'b0));
    idx = str_rfind(.s(filename), .sub("/"));
    basename = filename.substr(idx + 1, filename.len() - 1);

    if (basename == ".") return basename;
    if (drop_extn) begin
      idx = str_find(.s(basename), .sub("."));
      if (idx == -1) idx = basename.len();
      basename = basename.substr(0, idx - 1);
    end
    return basename;
  endfunction : str_path_basename

endpackage
