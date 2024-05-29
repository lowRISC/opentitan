#!/bin/bash
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

function usage() {
  echo "Convert a binary file to a C array."
  echo
  echo "$1 [--input FILE] [--output FILE] [--name C_IDENT]"
  echo
  echo "    -i|--input FILE: Input file to convert to C"
  echo "    -o|--output FILE: Output file name.  Defaults to input name with .h appended"
  echo "    -n|--name C_IDENT: Name of the array."
  echo "    -?|-h|--help: This message."
  echo
}

DIR="$(dirname "$0")"

FILE=""
OUTPUT=""
NAME=""

while [[ $# -gt 0 ]]; do
  case "$1" in
    -i|--input)
      shift
      FILE="$1"
      shift
      ;;
    -o|--output)
      shift
      OUTPUT="$1"
      shift
      ;;
    -n|--name)
      shift
      NAME="$1"
      shift
      ;;
    -\?|-h|--help)
      usage $0
      exit 1
      ;;
    *)
      echo "Unknown argument: $1"
      exit 1
      ;;
  esac
done

if [[ -z ${OUTPUT} ]]; then
  OUTPUT="${FILE}.h"
fi
if [[ -z ${NAME} ]]; then
  base=$(basename ${FILE})
  NAME=$(echo ${base} | sed -e "s/[^A-Za-z0-9_]/_/g")
fi

echo -n "" > ${OUTPUT}
echo "// Copyright lowRISC contributors (OpenTitan project)." >> ${OUTPUT}
echo "// Licensed under the Apache License, Version 2.0, see LICENSE for details." >> ${OUTPUT}
echo "// SPDX-License-Identifier: Apache-2.0" >> ${OUTPUT}
echo "" >> ${OUTPUT}
echo "// clang-format off" >> ${OUTPUT}
echo "const unsigned char ${NAME}[] = {" >> ${OUTPUT}
hexdump -vf "${DIR}/c.hexdump" ${FILE} | sed -e "s/0x  ,/     /g" >> ${OUTPUT}
echo "};" >> ${OUTPUT}
echo "// clang-format on" >> ${OUTPUT}
