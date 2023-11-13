#!/usr/bin/env bash
# verible-transform-interactive.sh
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
script_dir="$(dirname $0)"

patch_tool="$(which verible-patch-tool)" || \
  patch_tool="$script_dir"/verible-patch-tool

function usage() {
  cat <<EOF
$0:
Runs a transformative tool (e.g. formatter) and prompts the user to apply
each change.

Usage: $script_name [script_options] -- transform_command -- files...

The '--'s are required for separating groups of tokens.

The 'transform_command' should result in printing transformed output to stdout,
not modify-in-place.

script options:
  --help, -h : print help and exit
  --demo : display instructional demo
  --verbose, -v : run verbosely
  --dry-run : produce patch from transform, but do not apply it.
  --patch-tool TOOL : path to verible-patch-tool
      [$patch_tool]
  --per-file-transform-flags TEMPLATE : command used append additional flags to
      the transform command per file.  Use {} as a placeholder for the file name.
      The TEMPLATE value will be eval'd using the shell.
      e.g. to pass incremental formatting line-ranges to tools that accept it:
        --per-file-transform-flags='--lines=\$(p4 diff -d-u {} | $patch_tool changed-lines - | cut -d" " -f2)'
        --per-file-transform-flags='--lines=\$(git diff -u --cached {} | $patch_tool changed-lines - | cut -d" " -f2)'

EOF
}

function demo() {
  cat <<DEOF
### Runnable demo of $script_name

### paste into terminal:

cat > test1.txt <<EOF
aaa
 bbb
  ccc
 ddd
eee
EOF

cat > test2.txt <<EOF
  eee
 ddd
ccc
 bbb
  aaa
EOF
$script_name -- grep -v ccc -- test1.txt test2.txt

### answer prompts with y/n

cat test1.txt

cat test2.txt
DEOF
}

# self-identify message coming from this script
# print this messages to stdout, intended for the user to see
function msg()  {
  echo "[$script_name] " "$@"
}

dry_run=0
verbose=0

# script option processing
transform_sep=0
per_file_transform_flags=""
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
    -- ) transform_sep=1; shift ; break ;; # stop option processing
    --help | -h ) { usage ; exit ;} ;;
    --demo ) { demo ; exit ;} ;;
    --verbose | -v ) verbose=1 ;;
    --patch-tool ) prev_opt=patch_tool ;;
    --patch-tool=* ) patch_tool="$optarg" ;;
    --dry-run ) dry_run=1 ;;
    --per-file-transform-flags ) prev_opt=per_file_transform_flags ;;
    --per-file-transform-flags=* ) per_file_transform_flags="$optarg" ;;
    # TODO(fangism): --backup=.EXT backup files first
    # TODO(fangism): --diff-options forwarded to diff
    --* | -* ) msg "Unknown option: $opt" ; exit 1 ;;
    # This script expects no positional arguments.
    *) { msg "Unexpected positional argument: $opt" ; usage ; exit 1 ;} ;;
  esac
  shift
done

# Check requirements.
[[ -x "$patch_tool" ]] || {
  msg "*** Unable to find executable 'verible-patch-tool'."
  msg "  Please specify with: --patch-tool TOOL."
  exit 1
}

[[ "$transform_sep" = 1 ]] || {
  msg "Expecting -- followed by transform command, but missing."
  exit 1
}

# command+options collection
files_sep=0
transform_command=()
for opt
do
  case "$opt" in
    -- ) files_sep=1; shift ; break ;; # stop option processing
    # This script expects no positional arguments.
    *) transform_command+=( "$opt" ) ;;
  esac
  shift
done

[[ "${#transform_command[@]}" -ge 1 ]] || {
  msg "Transform command must be non-empty."
  exit 1
}

[[ "$files_sep" = 1 ]] || {
  msg "Expecting -- followed by list of files, but missing."
  exit 1
}

msg "Transformation: ${transform_command[@]}"

# Remaining arguments "$@" are files.
files=("$@")

tempdir="$(mktemp -d -t "tmp.$script_name.XXXXXXX")"
msg "Temporary files in: $tempdir"

# These messages are only intended for debugging and tracing.
function log()  {
  echo "[$script_name] " "$@" >> "$tempdir"/interactive.log
}

# Transform one file at a time, and aggregate into one large patch.
for f in "${files[@]}"
do
  mkdir -p "$tempdir/$(dirname "$f")"

  extra_flags=()
  if [[ -n "$per_file_transform_flags" ]]
  then
    expanded_flags="$(echo "$per_file_transform_flags" | sed -e "s|{}|$f|g")"
    log "expanded per-file flags to: $expanded_flags"
    eval extra_flags_text=\"$expanded_flags\"
    IFS=' ' read -r -a extra_flags <<< "$extra_flags_text"
  fi

  log "${transform_command[@]}" "${extra_flags[@]}" "$f" ">" "$tempdir/$f"
  "${transform_command[@]}" "${extra_flags[@]}" "$f" > "$tempdir/$f"
  # ignore exit statuses

  # Capture differences to stdout (and patchfile).
  # TODO(fangism): forward --diff-options
  diff -U 1 "$f" "$tempdir/$f"
done | \
  sed -e "s|+++ $tempdir/|+++ NEW/|" > "$tempdir"/interactive.patch

msg "Cumulative patch (affects ${#files[@]} files): $tempdir/interactive.patch"

[[ "$dry_run" = 0 ]] || {
  msg "--dry-run: Halting before applying patch."
}

# Interactively prompt user to select changes to keep.
# Only in this step will any files be modified in-place.
exec "$patch_tool" apply-pick "$tempdir"/interactive.patch
