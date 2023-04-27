# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

###############################################################################

TB-COMPILE-STAMP = $(METADATA-DIR)/tb.compile.stamp
rtl_tb_compile: $(METADATA-DIR)/tb.compile.stamp
rtl-tb-compile-var-deps := SIMULATOR COV WAVES # Rebuild if these change

rtl_sim_run: $(rtl-sim-logs)

check_logs: $(comp-results)

FCOV-STAMP = $(METADATA-DIR)/fcov.stamp
riscv_dv_fcov: $(METADATA-DIR)/fcov.stamp

MERGE-COV-STAMP = $(METADATA-DIR)/merge.cov.stamp
merge_cov: $(METADATA-DIR)/merge.cov.stamp

REGR-LOG-STAMP = $(METADATA-DIR)/regr.log.stamp
collect_results: $(METADATA-DIR)/regr.log.stamp

rtl-sim-logs +=
comp-results +=

###############################################################################
# Compile ibex core TB
#
# Note that this doesn't depend on the seed: the DUT doesn't depend on which
# test we're running!

tb-compile-vars-path := $(BUILD-DIR)/.tb.vars.mk
-include $(tb-compile-vars-path)
tb-compile-vars-prereq = $(call vars-prereq,comp,compiling TB,$(rtl-tb-compile-var-deps))

$(METADATA-DIR)/tb.compile.stamp: \
  $(tb-compile-vars-prereq) $(all-verilog) $(all-cpp) $(risc-dv-files) \
  scripts/compile_tb.py yaml/rtl_simulation.yaml \
  | $(BUILD-DIR)
	@echo Building RTL testbench
	$(verb)env PYTHONPATH=$(PYTHONPATH) \
	scripts/compile_tb.py \
	  --dir-metadata $(METADATA-DIR)
	$(call dump-vars,$(tb-compile-vars-path),comp,$(rtl-tb-compile-var-deps))
	@touch $@

###############################################################################
# Run ibex RTL simulation with random or directed test and uvm stimulus

$(rtl-sim-logs): $(TESTS-DIR)/%/$(rtl-sim-logfile): \
  $(TB-COMPILE-STAMP) $(TESTS-DIR)/%/test.bin scripts/run_rtl.py
	@echo Running RTL simulation at $(@D)
	$(verb)env PYTHONPATH=$(PYTHONPATH) \
	scripts/run_rtl.py \
	  --dir-metadata $(METADATA-DIR) \
	  --test-dot-seed $*

###############################################################################
# Gather RTL sim results, and parse logs for errors

$(comp-results): $(TESTS-DIR)/%/trr.yaml: \
  $(TESTS-DIR)/%/$(rtl-sim-logfile) scripts/check_logs.py
	@echo Collecting simulation results and checking logs of testcase at $@
	$(verb)env PYTHONPATH=$(PYTHONPATH) \
	scripts/check_logs.py \
	  --dir-metadata $(METADATA-DIR) \
	  --test-dot-seed $*

###############################################################################
# Generate RISCV-DV functional coverage
# TODO(udi) - add B extension

# When COV == 0 this step (and the merge step below) still run, but just
# generate a stamp file without performing the coverage related actions. This is
# to allow the final collect_results.py step to run where COV == 0 (as it needs
# to declare coverage as a dependency to ensure it gets run after coverage merge
# when COV == 1).
$(METADATA-DIR)/fcov.stamp: $(comp-results) \
  scripts/get_fcov.py
ifeq ($(COV), 1)
	@echo Generating RISCV_DV functional coverage
	$(verb)env PYTHONPATH=$(PYTHONPATH) \
	scripts/get_fcov.py \
	  --dir-metadata $(METADATA-DIR)
endif
	@touch $@

###############################################################################
# Merge all output coverage directories
# Any coverage databases generated from the riscv_dv_fcov target will be merged
# as well.

$(METADATA-DIR)/merge.cov.stamp: $(FCOV-STAMP) \
  scripts/merge_cov.py
ifeq ($(COV), 1)
	@echo Merging all recorded coverage data into a single report
	$(verb)env PYTHONPATH=$(PYTHONPATH) \
	scripts/merge_cov.py \
	  --dir-metadata $(METADATA-DIR)
endif
	@touch $@

###############################################################################
# Generate the summarized regression log

$(METADATA-DIR)/regr.log.stamp: scripts/collect_results.py $(comp-results) $(MERGE-COV-STAMP)
	@echo Collecting up results of tests into report regr.log
	$(verb)env PYTHONPATH=$(PYTHONPATH) \
	./scripts/collect_results.py \
	  --dir-metadata $(METADATA-DIR)
	@touch $@
