# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Merge coverage with IMC, across tests, scopes and previous regression runs.

# Set the input coverage directories across all available scopes and previous runs,
# using the env var 'cov_db_dirs' (which is a space separated list of directories).
# Append each of these directories with /* wildcard at the end to allow the tool to
# find all available test databases.
set cov_db_dirs_env [string trim $::env(cov_db_dirs) " \""]
foreach i $cov_db_dirs_env { append cov_db_dirs "[string trim $i]/* "; }
puts "Input coverage directories:\n$cov_db_dirs"

# Set the output directory for the merged database using the env var 'cov_merge_db_dir'.
# The supplied env var may have quotes or spaces that needs to be trimmed.
puts "Output directory for merged coverage:"
set cov_merge_db_dir [string trim $::env(cov_merge_db_dir) " \""]

# Run the merge command.
merge $cov_db_dirs -out $cov_merge_db_dir -overwrite
