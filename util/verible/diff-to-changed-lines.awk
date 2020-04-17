#!/usr/bin/awk -f
# Copyright 2020 The Verible Authors.
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#      http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

# Converts a unified-diff into file names and their modified line ranges.
# This supports reading the output of 'git diff', but should handle most
# variants of diffs.
# Note, however, that git diffs shows files as being prefixed with "a/" and "b/",
# so the caller of this script will need to adjust filenames accordingly.
# The output style of line ranges is suitable for 'verilog_format --lines=...'
#
# usage: awk -f (this_script) < file.diff
#
# Changed lines are those that start with '+' in unified diffs.
# Ranges can be compact: N,P-Q
# Prints one file per line, e.g.:
#   abc.sv 5,10-12,18,21-22
#   xyz.sv 232-245
# New files (diffed vs. /dev/null) will appear without line ranges:
#   new_file.sv
#
# TODO(fangism): use or write a proper diff/patch-reader library (C++)

BEGIN {
  expect_filename = 0;
  active_range = 0;
  seen_file = 0;
}

# Detect whether this entry is a new file.
/^---/ {
  is_new_file = ($2 == "/dev/null");
}

# contains filename at $2
/^+++/ {
  if (expect_filename) {
    filename = $2;
    if (seen_file) print "";
    printf(filename " ");
    expect_filename = 0;
    seen_range = 0;
    seen_file = 1;
  }
}

# given:
# @@ -L,J +R,K
# R is the next starting line number in the next chunk
/^@@ / {
  split($3, a, ",");
  left_current_line = substr(a[1], 2) - 1;
  right_current_line = left_current_line;
  active_range = 0;
}

# seen in 'git diff'
# diff before-file after-file
/^diff/ {
  auto_flush_range();
  expect_filename = 1;
}

# seen in 'p4 diff'
# ==== //depot/...#N - /local/path/to/file ====
/^==== .* ====$/ {
  auto_flush_range();
  expect_filename = 1;
}


# + lines are after change only
/^+/ {
  if (!expect_filename) {
    ++right_current_line;
    if (!active_range) {
      modified_from = right_current_line;
    }
    active_range = 1;
  }
}

# print the most recent completed range
function flush_range() {
  if (!is_new_file) {
    if (seen_range) printf(",");
    modified_to = right_current_line;
    if (modified_from == modified_to) printf(modified_from);
    else printf(modified_from "-" modified_to);
  }
  seen_range = 1;
  active_range = 0;
}

function auto_flush_range() {
  if (active_range) {
    flush_range();
  }
}

# <space> lines in unified diffs are common to both before/after
/^ / {
  auto_flush_range();
  ++left_current_line;
  ++right_current_line;
}

# - lines are before change only
/^-/ {
  auto_flush_range();
  ++left_current_line;
}

END {
  # if diff ends with an active range, print it.
  auto_flush_range();
  print "";
}
