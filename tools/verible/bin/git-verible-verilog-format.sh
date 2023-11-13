#!/usr/bin/env bash
# git-verible-verilog-format.sh
#
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

script_name="$(basename $0)"
script_dir="$(realpath $(dirname $0))"

formatter="$(which verible-verilog-format)" || \
  formatter="$script_dir"/verible-verilog-format

patch_tool="$(which verible-patch-tool)" || \
  patch_tool="$script_dir"/verible-patch-tool

function usage() {
  cat <<EOF
$0:
Performs incremental file formatting (verible-verilog-format) based on current diffs.
New files explicitly git-add-ed by the user are wholly formatted.

Actions:
  1) Runs 'git add -u' to stage currently modified files to the index.
     To format new files (wholly), 'git add' those before calling this script.
  2) Runs 'git diff -u --cached' to generate a unified diff.
  3) Diff is scanned to determine added or modified lines in each file.
  4) Invokes 'verible-verilog-format --inplace' on all touched or new Verilog files,
     but does not 'git add' so the changes may be examined and tested.
     Formatting can be easily undone with:
       'git diff | git apply --reverse -'.

usage: $0 [script options] [-- [verible-verilog-format options]]
  (no positional arguments)
  Run from anywhere inside a git project tree.

script options: (options with arguments can be: --flag=VALUE or --flag VALUE)
  --help | -h : print help and exit
  --verbose | -v : execute verbosely
  --dry-run : stop before running formatter, and print formatting commands
  --formatter TOOL : path to verible-verilog-format binary
       [using: $formatter]
  -- : stops option processing, and forwards remaining args as flags to the
       underlying --formatter tool.
EOF
}

# self-identify message coming from this script
function msg()  {
  echo "[$script_name] " "$@"
}

verbose=0
dry_run=0
# 'args' will be forwarded to the formatter as additional tool options
args=()

# option processing
for opt
do
  # handle: --option arg
  if test -n "$prev_opt"
  then
    eval $prev_opt=\$opt
    prev_opt=
    shift
    continue
  fi
  case $opt in
    *=?*) optarg=$(expr "X$opt" : '[^=]*=\(.*\)') ;;
    *=) optarg= ;;
  esac
  case $opt in
    -- ) shift ; break ;; # stop option processing
    --help | -h ) { usage ; exit ;} ;;
    --verbose | -v ) verbose=1 ;;
    --formatter ) prev_opt=formatter ;;
    --formatter=* ) formatter="$optarg" ;;
    --dry-run ) dry_run=1 ;;
    --* | -* ) msg "Unknown option: $opt" ; exit 1 ;;
    *) args=("${args[@]}" "$opt") ;;
  esac
  shift
done

# Check some requirements.
[[ -x "$formatter" ]] || {
  msg "*** Unable to find executable 'verible-verilog-format'."
  msg "  Please specify formatter with: --formatter TOOL."
  exit 1
}
[[ -x "$patch_tool" ]] || {
  msg "*** Required executable '$patch_tool' is missing."
  exit 1
}

# collect remainder after stopping option processing
args=("${args[@]}" "$@")

function verbose_command() {
  if [[ "$dry_run" = 1 ]] || [[ "$verbose" = 1 ]]
  then
    msg "[command]: $@"
  fi

  [[ "$dry_run" = 1 ]] || "$@" || \
    msg "Note: '$@' failed with status: $?"
}

# Switch to git root directory, so relative paths will be correct.
cd "$(git rev-parse --show-toplevel)"
msg "Working from git root: $PWD"

tempdir="$(mktemp -d --tmpdir "tmp.$script_name.XXXXXXX")"
msg "Temporary files in: $tempdir"

# Save current workspace in git index.
git add -u
# Examine current differences for changed lines.
# Strip the 'b/' from git diffs.
# Format only changed lines for each file, one file at a time.
git diff -u --cached | \
  tee "$tempdir"/git-cached.diff | \
  "$patch_tool" changed-lines - | \
  sed -e 's|^b/||' | \
  tee "$tempdir"/file-lines.txt | \
  while read filename lines
  do
    # Check file extension: skip non-Verilog files.
    case "$filename" in
      *.v | *.vh | *.sv | *.svh ) ;;
      * ) continue ;;
    esac

    # If $lines is blank, that implies a new file (format entire file).
    # Otherwise it is the argument to --lines.
    lines_flag=()
    [[ -z "$lines" ]] || lines_flag=("--lines=$lines")

    # Format one file at a time.
    format_command=("$formatter" --inplace "$filename" "${lines_flag[@]}" "${args[@]}")
    verbose_command "${format_command[@]}"
    # Ignore exit statuses and keep going.
  done

if [[ "$dry_run" = 0 ]]
then
  cat <<EOF
[$script_name] Done formatting.  You could run:
  'git status' to see what files were formatted.
  'git diff' to see detailed formatting changes.
  'git add -u' to accept formatting changes for commit.
  'git diff | git apply --reverse -' to undo formatting changes.
EOF
else
  msg "Stopping before formatting due to --dry-run."
fi

