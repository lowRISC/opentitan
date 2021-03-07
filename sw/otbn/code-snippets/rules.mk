# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

#####################################################################
#
# THIS IS A TEMPORARY SOLUTION
#
# Eventually, the software team is going to have a Meson-based flow
# for building OTBN software. When that exists, this code will go
# away.
#
#####################################################################

# A make fragment for assembling and linking the code snippets. This is
# included by ./Makefile, but can be included in other Makefiles too.
#
# The following variables must be set:
#
#    variable                      | description
#  --------------------------------+----------------------------------------
#    otbn-code-snippets-obj-dir    | Output directory for built objects
#    otbn-code-snippets-bin-dir    | Output directory for built binaries
#    otbn-code-snippets-util-dir   | Path to directory containing OTBN tooling
#
# The following variables may be set:
#
#    variable                      | description
#  --------------------------------+----------------------------------------
#    otbn-code-snippets-as         | Path to otbn-as (defaults to util dir)
#    otbn-code-snippets-ld         | Path to otbn-ld (defaults to util dir)
#
# The ugly "otbn-code-snippets-" prefix on variable names is so that this file
# can be included in other Makefiles without breaking anything.

ifndef otbn-code-snippets-obj-dir
$(error otbn-code-snippets-obj-dir not set.)
endif
ifndef otbn-code-snippets-bin-dir
$(error otbn-code-snippets-bin-dir not set.)
endif
ifndef otbn-code-snippets-util-dir
$(error otbn-code-snippets-util-dir not set.)
endif

# Default values for optional variables
otbn-code-snippets-as ?= $(otbn-code-snippets-util-dir)/otbn-as
otbn-code-snippets-ld ?= $(otbn-code-snippets-util-dir)/otbn-ld

# Get the list of all assembly files in this directory. Strip away directory
# and extension to get basenames (used for objects and binaries).
otbn-code-snippets-path      := $(dir $(realpath $(lastword $(MAKEFILE_LIST))))
otbn-code-snippets-asm-paths := $(wildcard $(otbn-code-snippets-path)*.s)
otbn-code-snippets-asm-basenames := $(notdir $(otbn-code-snippets-asm-paths))
otbn-code-snippets-basenames     := $(otbn-code-snippets-asm-basenames:.s=)

$(sort $(otbn-code-snippets-obj-dir) $(otbn-code-snippets-bin-dir)):
	mkdir -p $@

# Calculate lists of object and ELF files
otbn-code-snippets-objects := \
  $(foreach b,$(otbn-code-snippets-basenames),\
            $(otbn-code-snippets-obj-dir)/$(b).o)
otbn-code-snippets-elfs := \
  $(foreach b,$(otbn-code-snippets-basenames),\
            $(otbn-code-snippets-bin-dir)/$(b).elf)

# Define rules for assembling the source code to make objects
$(otbn-code-snippets-objects): \
  $(otbn-code-snippets-obj-dir)/%.o: \
  $(otbn-code-snippets-path)%.s $(otbn-code-snippets-as) \
   | $(otbn-code-snippets-obj-dir)
	$(otbn-code-snippets-as) -o $@ $<

# Define rules for linking objects to make ELFs
$(otbn-code-snippets-elfs): \
  $(otbn-code-snippets-bin-dir)/%.elf: \
  $(otbn-code-snippets-obj-dir)/%.o $(otbn-code-snippets-ld) \
   | $(otbn-code-snippets-bin-dir)
	$(otbn-code-snippets-ld) -o $@ $(otbn-ldflags) $< $(otbn-libs)

#
# Define any file-specific flags or dependencies
#

# rsa_1024_dec_test depends on code defined in modexp.s
$(otbn-code-snippets-bin-dir)/rsa_1024_dec_test.elf: \
  $(otbn-code-snippets-obj-dir)/modexp.o
$(otbn-code-snippets-bin-dir)/rsa_1024_dec_test.elf: \
  otbn-libs += $(otbn-code-snippets-obj-dir)/modexp.o

# rsa_1024_enc_test depends on code defined in modexp.s
$(otbn-code-snippets-bin-dir)/rsa_1024_enc_test.elf: \
  $(otbn-code-snippets-obj-dir)/modexp.o
$(otbn-code-snippets-bin-dir)/rsa_1024_enc_test.elf: \
  otbn-libs += $(otbn-code-snippets-obj-dir)/modexp.o

# p256 curve point test depends on p256init, p256isoncurve, defined in p256.s
$(otbn-code-snippets-bin-dir)/p256_curve_point_test.elf: \
  $(otbn-code-snippets-obj-dir)/p256.o
$(otbn-code-snippets-bin-dir)/p256_curve_point_test.elf: \
  otbn-libs += $(otbn-code-snippets-obj-dir)/p256.o

# p256 scalar mult test depends on p256init, p256scalarmult, defined in p256.s
$(otbn-code-snippets-bin-dir)/p256_scalar_mult_test.elf: \
  $(otbn-code-snippets-obj-dir)/p256.o
$(otbn-code-snippets-bin-dir)/p256_scalar_mult_test.elf: \
  otbn-libs += $(otbn-code-snippets-obj-dir)/p256.o

# p256 ECDSA sign test depends on p256init, p256sign, defined in p256.s
$(otbn-code-snippets-bin-dir)/p256_ecdsa_sign_test.elf: \
  $(otbn-code-snippets-obj-dir)/p256.o
$(otbn-code-snippets-bin-dir)/p256_ecdsa_sign_test.elf: \
  otbn-libs += $(otbn-code-snippets-obj-dir)/p256.o

# p256 ECDSA verify test depends on p256init, p256verify, defined in p256.s
$(otbn-code-snippets-bin-dir)/p256_ecdsa_verify_test.elf: \
  $(otbn-code-snippets-obj-dir)/p256.o
$(otbn-code-snippets-bin-dir)/p256_ecdsa_verify_test.elf: \
  otbn-libs += $(otbn-code-snippets-obj-dir)/p256.o

# p256_ecdsa depends on p256init, p256verify, p256sign, defined in p256.s
$(otbn-code-snippets-bin-dir)/p256_ecdsa.elf: \
  $(otbn-code-snippets-obj-dir)/p256.o
$(otbn-code-snippets-bin-dir)/p256_ecdsa.elf: \
  otbn-libs += $(otbn-code-snippets-obj-dir)/p256.o

# p256 point addition test depends on proj_add defined in p256.s
$(otbn-code-snippets-bin-dir)/p256_proj_add_test.elf: \
  $(otbn-code-snippets-obj-dir)/p256.o
$(otbn-code-snippets-bin-dir)/p256_proj_add_test.elf: \
  otbn-libs += $(otbn-code-snippets-obj-dir)/p256.o

# rsa depends on code defined in modexp.s
$(otbn-code-snippets-bin-dir)/rsa.elf: \
  $(otbn-code-snippets-obj-dir)/modexp.o
$(otbn-code-snippets-bin-dir)/rsa.elf: \
  otbn-libs += $(otbn-code-snippets-obj-dir)/modexp.o

# p384_proj_add depends on barrett384_p384 defined in barrett384_p384.s
$(otbn-code-snippets-bin-dir)/p384_proj_add.elf: \
  $(otbn-code-snippets-obj-dir)/barrett384_p384.o
$(otbn-code-snippets-bin-dir)/p384_proj_add.elf: \
  otbn-libs += $(otbn-code-snippets-obj-dir)/barrett384_p384.o

# p384_proj_add_test depends on p384_proj_add defined in p384_proj_add.s
$(otbn-code-snippets-bin-dir)/p384_proj_add_test.elf: \
  $(otbn-code-snippets-obj-dir)/p384_proj_add.o \
  $(otbn-code-snippets-obj-dir)/barrett384_p384.o
$(otbn-code-snippets-bin-dir)/p384_proj_add_test.elf: \
  otbn-libs += $(otbn-code-snippets-obj-dir)/p384_proj_add.o \
  $(otbn-code-snippets-obj-dir)/barrett384_p384.o
