#!/usr/bin/env bash
# verible-verilog-format-changed-lines-interactive.sh.

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
script_dir="$(dirname $0)"

# Look first for support scripts/binaries installed alongside this script.
# Fall back to searching in current PATH.

# This is the script that drives interactive patching.
interactive_patch_script="$script_dir"/verible-transform-interactive.sh
[[ -x "$interactive_patch_script" ]] || \
  interactive_patch_script="$(which verible-transform-interactive.sh)"

# This is Verible's patch-based utility.
patch_tool="$script_dir"/verible-patch-tool
[[ -x "$patch_tool" ]] || patch_tool="$(which verible-patch-tool)"

# This is Verible's Verilog formatter.
formatter="$script_dir"/verible-verilog-format
[[ -x "$formatter" ]] || formatter="$(which verible-verilog-format)"

# version control system
# auto-detect by default
rcs=auto
baserev=
files=()

function usage() {
  cat <<EOF
$0:
Interactively prompts user to accept/reject formatter tool changes,
based only on touched lines of code in a revision-controlled workspace.

Usage: $script_name [script_options] [FILES...]

Run this from a version-controlled directory.
If FILES is empty, scan for all Verilog files under the current directory.

script options:
  --help, -h : print help and exit
  --rcs TOOL : revision control system [default:$rcs]
      Supported: p4,git,hg
  --base REV : Revision to diff against [default: git:HEAD hg:.]
      See tool-specific help for version specifiers:
          git help revisions
          hg help revisions
EOF
}

function msg()  {
  echo "[$script_name] " "$@"
}

# generic option processing
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
  case "$opt" in
    *=?*) optarg=$(expr "X$opt" : '[^=]*=\(.*\)') ;;
    *=) optarg= ;;
  esac
  case $opt in
    -- ) shift ; break ;; # stop option processing
    --help | -h ) { usage ; exit ;} ;;
    --rcs ) prev_opt=rcs ;;
    --rcs=* ) rcs="$optarg" ;;
    --base ) prev_opt=baserev ;;
    --base=* ) baserev="$optarg" ;;
    --* | -* ) msg "Unknown option: $opt" ; exit 1 ;;
    # Positional arguments [optional] are files.
    *) files+=( "$opt" ) ;;
  esac
  shift
done

# attempt to infer version control system (p4,svn,git,cvs,hg,...)
# Note: these tests are sensitive to "$PWD"
if [[ "$rcs" == "auto" ]]
then
  if git status
  then
    rcs=git
  elif hg root
  then
    rcs=hg
  else
    # p4 is tricky to detect due to the concept of default clients,
    # so leave it last position, if all else fails.
    rcs=p4
  fi > /dev/null 2>&1
fi

# Set default rev to 'dot' (parent) or HEAD. User can override
# to a different revision if they want (eg p4head)
case "$rcs" in
  git) baserev=${baserev:-HEAD} ;;
  hg) baserev=${baserev:-.} ;;
esac

function p4_touched_files() {
  # Result is already absolute paths to local files.
  p4 whatsout
}

function git_touched_files() {
  # Get added/modified files that are tracked.
  # See git help diff.
  # readlink: resolve absolute path to eliminate sensitivity to "$PWD"
  # Since 'git status' doesn't allow passing in a revision, use git diff instead
  # of status. But that gives a root-relative path, so cd to the root first
  (cd $(git rev-parse --show-toplevel) ;
    git diff --name-only --diff-filter=AM "$baserev" | xargs readlink -f
  )
}

function hg_touched_files() {
  # Get added/modified files that are tracked.
  # See hg help status
  hg status --no-status -am --rev "$baserev" | xargs readlink -f
}

# Set commands based on version control system
case "$rcs" in
  p4) touched_files=p4_touched_files
      # force use of traditional text 'diff', not some other UI-diff tool
      single_file_diff=(P4DIFF=diff p4 diff -d-u "{}") ;;
  git) touched_files=git_touched_files
      single_file_diff=(git diff -u --cached "$baserev" "{}") ;;
  hg) touched_files=hg_touched_files
      single_file_diff=(hg diff -g --rev "$baserev" "{}") ;;
  *) { msg "Unsupported version control system: $rcs" ; exit 1;} ;;
esac

# If files is unspecified, scan for all locally modified files.
if [[ "${#files[@]}" == 0 ]]
then
  # File extensions are currently hardcoded to Verilog files.
  files=($("$touched_files" | grep -e '\.sv$' -e '\.v$' -e '\.svh$' -e '\.vh$' ))
fi

# Note about --per-file-transform-flags:
# The file name is stripped away to yield only line numbers, which is why
# this still works with git-diffs, which contain a/ and b/ prefixes in
# filenames.  The file name used for applying changes is still the one from
# "${files[@]}".
interact_command=("$interactive_patch_script" \
  --patch-tool "$patch_tool" \
  --per-file-transform-flags='--lines=$('"${single_file_diff[*]}"' | '"$patch_tool"' changed-lines - | cut -d" " -f2)' \
  -- "$formatter" \
  -- "${files[@]}" )

msg "interact command: ${interact_command[@]}"
exec "${interact_command[@]}"
