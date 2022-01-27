# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

database -shm -open waves.shm -default
probe -create -shm tb -depth all -all -mem
run
exit
