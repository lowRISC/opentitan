#! /bin/sh
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

printf "Job $1 exited with code $2\n"
if [ $2 -eq 0 ]
then
  printf "Successfully completed\n"
  printf "Job $1 done\n"
else
  printf "Job $1 failed with error code $2\n"
fi
cwd=$(realpath .)
printf "<$cwd> was used as the working directory\n"
exit $2
