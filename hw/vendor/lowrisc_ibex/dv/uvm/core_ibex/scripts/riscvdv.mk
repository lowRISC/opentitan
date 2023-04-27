# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

###############################################################################

CORE-CONFIG-STAMP = $(METADATA-DIR)/core.config.stamp
core_config: $(CORE-CONFIG-STAMP)
core-config-var-deps := IBEX_CONFIG

INSTR-GEN-BUILD-STAMP = $(METADATA-DIR)/instr.gen.build.stamp
instr_gen_build: $(METADATA-DIR)/instr.gen.build.stamp
instr-gen-build-var-deps := SIMULATOR SIGNATURE_ADDR  # Rebuild if these change

instr_gen_run: $(riscvdv-test-asms)

riscvdv-test-asms +=
riscvdv-test-bins +=

###############################################################################
# Configure the templated file riscv-dv uses to know the parameterized features available
#

core-config-vars-path := $(BUILD-DIR)/.cc.vars.mk
-include $(core-config-vars-path)
core-config-var-prereq = \
  $(call vars-prereq, \
     gen, \
     Generate core configuration file, \
     $(core-config-var-deps))

$(CORE-CONFIG-STAMP): \
  $(core-config-var-prereq) ./riscv_dv_extension/riscv_core_setting.tpl.sv \
  scripts/render_config_template.py \
  | $(BUILD-DIR)
	@echo Generating core configuration file
	$(verb)env PYTHONPATH=$(PYTHONPATH) \
	  scripts/render_config_template.py \
	    --dir-metadata $(METADATA-DIR) \
	    $(EXT_DIR)/riscv_core_setting.tpl.sv > $(EXT_DIR)/riscv_core_setting.sv
	$(call dump-vars,$(core-config-vars-path),gen,$(core-config-var-deps))
	@touch $@

###############################################################################
# Build the Random Instruction Generator
#

ig-build-vars-path := $(BUILD-DIR)/.instr_gen.vars.mk
-include $(ig-build-vars-path)
instr-gen-build-vars-prereq = \
  $(call vars-prereq, \
     gen, \
     building instruction generator, \
     $(instr-gen-build-var-deps))

$(METADATA-DIR)/instr.gen.build.stamp: \
  $(instr-gen-build-vars-prereq) $(riscv-dv-files) $(CORE-CONFIG-STAMP) \
  scripts/build_instr_gen.py \
  | $(BUILD-DIR)
	@echo Building randomized test generator
	$(verb)env PYTHONPATH=$(PYTHONPATH) \
	  scripts/build_instr_gen.py \
	    --dir-metadata $(METADATA-DIR)
	$(call dump-vars,$(ig-build-vars-path),gen,$(instr-gen-build-var-deps))
	@touch $@

###############################################################################
# Run the random instruction generator
#
# Make use of static-pattern rules to extract the TDS
# https://www.gnu.org/software/make/manual/html_node/Static-Usage.html#Static-Usage
#
# targets …: target-pattern: prereq-patterns …
#         recipe
#         …

$(riscvdv-test-asms): $(TESTS-DIR)/%/$(asm-stem): \
  $(INSTR-GEN-BUILD-STAMP) $(TESTLIST) scripts/run_instr_gen.py
	@echo Running randomized test generator to create assembly file $@
	$(verb)env PYTHONPATH=$(PYTHONPATH) \
	scripts/run_instr_gen.py \
	  --dir-metadata $(METADATA-DIR) \
	  --test-dot-seed $*

