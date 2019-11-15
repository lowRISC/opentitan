---
title: "util/vendor.py: Vendor-in Components"
---

Not all code contained in this repository is actually developed within this repository.
Code which we include from external sources is placed in `vendor` sub-directories (e.g. `hw/vendor`) and copied over from upstream sources.
The process of copying the upstream sources is called vendoring, and it is automated by the `util/vendor` tool.

The `util/vendor` tool can go beyond simply copying in source files: it can patch them, it can export patches from commits in a Git repository, and it can commit the resulting changes with a meaningful commit message.

## Tool usage overview

```text
usage: vendor [-h] [--refresh-patches] [--commit] [--verbose] file

vendor, copy source code from upstream into this repository

positional arguments:
  file               vendoring description file (*.vendor.hjson)

optional arguments:
  -h, --help         show this help message and exit
  --refresh-patches  Refresh the patches from the patch repository
  --commit, -c       Commit the changes
  --verbose, -v      Verbose
```

## The vendor description file

For each vendored-in component a description file must be created, which serves as input to the `util/vendor` tool.
The vendor description file is stored in `vendor/<vendor>_<name>.vendor.hjson`.
By convention all imported code is named `<vendor>_<name>`, with `<vendor>` typically being the GitHub user or organization name, and `<name>` the project name.
It is recommended to use only lower-case characters.

A full commented example of a vendor description file is given below.
All relative paths are relative to the description file.
Optional parts can be removed if they are not used.

```
// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
{
  // Name of the vendored-in project
  name: "pulp_riscv_dbg",

  // Target directory: typically equal to the name
  // All imported code is copied into this directory
  target_dir: "pulp_riscv_dbg",

  // Git upstream source code repository
  upstream: {
    // Upstream Git repository URL. HTTPS URLs are preferred.
    url: "https://github.com/pulp-platform/riscv-dbg",
    // Upstream revision or branch. Can be a commit hash or a branch name.
    rev: "pulpissimo_integration",
  },

  // Optional: Apply patches from the following directory to the upstream
  // sources
  patch_dir: "patches/pulp_riscv_dbg",

  // Optional: Update patches in |patch_dir| from a Git repository
  // If util/vendor is run with --refresh-patches, all commits in the repository
  // at |url| between |rev_base| and |rev_patched| are exported into the
  // |patch_dir|, replacing all existing patches.
  patch_repo: {
    url: "git@github.com:lowRISC/riscv-dbg.git",
    rev_base: "pulpissimo_integration",
    rev_patched: "ot",
  },

  // Optional: Exclude files or directories from the upstream sources
  // The standard glob wildcards (*, ?, etc.) are supported
  exclude_from_upstream: [
    "src/dm_top.sv",
    "src_files.yml",
  ]
}
```

If only the contents of a single subdirectory (including its children) of an upstream repository are to be copied in, the optional `only_subdir` key of can be used in the `upstream` section to specify the subdirectory to be copied in.
The contents of that subdirectory will populate the `target_dir` directly (without any intervening directory levels).

In the example vendor description file below, the mpsse directory is populated from the chromiumos platform2 repository, extracting just the few files in the trunks/ftdi subdirectory.

```
// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
{
  name: "mpsse",
  target_dir: "mpsse",

  upstream: {
    url: "https://chromium.googlesource.com/chromiumos/platform2/",
    rev: "master",
    only_subdir: "trunks/ftdi",
  },
}
```

## Examples

### Update code and commit the new code
```command
$ cd $REPO_TOP
$ ./util/vendor.py hw/vendor/google_riscv-dv.vendor.hjson -v --commit
```
