# Copyright (c) 2022 ETH Zurich and University of Bologna
# Copyright and related rights are licensed under the Solderpad Hardware
# License, Version 0.51 (the "License"); you may not use this file except in
# compliance with the License.  You may obtain a copy of the License at
# http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
# or agreed to in writing, software, hardware and materials distributed under
# this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
# CONDITIONS OF ANY KIND, either express or implied. See the License for the
# specific language governing permissions and limitations under the License.
#
#

# Name of the program $(PROGRAM).c will be added as a source file
PROGRAM = flash_prelaod_hello_world
PROGRAM_DIR := $(shell dirname $(realpath $(lastword $(MAKEFILE_LIST))))
# Any extra source files to include in the build. Use the upper case .S
# extension for assembly files

utils_dir = $(PROGRAM_DIR)/inc/
directories = drivers/inc drivers/src string_lib/inc string_lib/src 
EXTRA_SRCS = $(foreach d, $(directories), -I$(utils_dir)$d)

include ${PROGRAM_DIR}/../../common/common.mk
