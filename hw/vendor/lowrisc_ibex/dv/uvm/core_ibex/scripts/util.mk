# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

###############################################################################
######## EXAMPLE OF VARIABLE DUMPING ############
# This target depends on the vendored in code in $(GEN_DIR). It also depends on the
# values of the following Makefile variables (we want to regenerate things if,
# for example, the simulator changes).

# To achieve this variable tracking, we dump each of the variables to a Makefile
# fragment and try to load it up the next time around. This done with the
# utility function "dump-vars" at the end of the recipe.
#
# To create the dependency, we must do the following two things before each
# target:
#
# First, load up the saved variable values from the last time around. If this
# fails, it's no problem: we'll assume that the previous run either doesn't
# exist or something went wrong.
  # ig-build-vars-path := $(BUILD-DIR)/.instr_gen.vars.mk
  # -include $(ig-build-vars-path)

# Next, compare the current variables to those we just loaded. This uses the
# utility function "vars-prereq". It creates a variable which evaluates to the
# (phony) FORCE if the two sets of variables do not match.
#
# Note that we define it with '=', not ':=', so we don't evaluate if we're not
# trying to run the instr_gen_build target.
  # instr-gen-build-vars-prereq = \
  #   $(call vars-prereq, \
  #      gen, \
  #      building instruction generator, \
  #      $(instr-gen-build-var-deps))

# Finally, $(instr-gen-build-vars-prereq) becomes a dependency of our target.
################## END EXAMPLE ###################

###############################################################################
# Utility functions.
#
# If VS is a list of variable names, P is a path and X is a string, then $(call
# dump-vars,P,X,VS) will expand to a list of 'file' commands that write each
# variable to P in Makefile syntax, but with "last-X-" prepended. At the start
# of the file, we also define last-X-vars-loaded to 1. You can use this to
# check whether there was a dump file at all.
#
# Note that this doesn't work by expanding to a command. Instead, *evaluating*
# dump-vars causes the variables to be dumped.
dump-var  = $(file >>$(1),last-$(2)-$(3) := $($(3)))
dump-vars = $(file >$(1),last-$(2)-vars-loaded := .) \
            $(foreach name,$(3),$(call dump-var,$(1),$(2),$(name)))

# equal checks whether two strings are equal, evaluating to '.' if they are and
# '' otherwise.
both-empty = $(if $(1),,$(if $(2),,.))
find-find = $(if $(and $(findstring $(1),$(2)),$(findstring $(2),$(1))),.,)
equal = $(or $(call both-empty,$(1),$(2)),$(call find-find,$(1),$(2)))

# var-differs is used to check whether a variable has changed since it was
# dumped. If it has changed, the function evaluates to '.' (with some
# whitespace) and prints a message to the console; if not, it evaluates to ''.
#
# Call it as $(call var-differs,X,TGT,V).
var-differs = \
  $(if $(call equal,$(strip $($(3))),$(strip $(last-$(1)-$(3)))),,\
       .$(info Repeating $(2) because variable $(3) has changed value.))

# vars-differ is used to check whether several variables have the same value as
# they had when they were dumped. If we haven't loaded the dumpfile, it
# silently evaluates to '!'. Otherwise, if all the variables match, it
# evaluates to '.'. If not, it evaluates to '.' and prints some messages to the
# console explaining why a rebuild is happening.
#
# Call it as $(call vars-differ,X,TGT,VS).
vars-differ-lst = $(foreach v,$(3),$(call var-differs,$(1),$(2),$(v)))
vars-differ-sp = \
  $(if $(last-$(1)-vars-loaded),\
       $(if $(strip $(call vars-differ-lst,$(1),$(2),$(3))),.,),\
       !)
vars-differ = $(strip $(call vars-differ-sp,$(1),$(2),$(3)))

# A phony target which can be used to force recompilation.
.PHONY: FORCE
FORCE:

# vars-prereq is empty if every variable in VS matches the last run (loaded
# with tag X), otherwise it is set to FORCE (which will force a recompile and
# might print a message to the console explaining why we're rebuilding TGT).
#
# Call it as $(call vars-prereq,X,TGT,VS)
vars-prereq = $(if $(call vars-differ,$(call strip,$(1)),$(2),$(3)),FORCE,)

# This expands to '@' if VERBOSE is 0 or not set, and to the empty
# string otherwise. Prefix commands with it in order that they only
# get printed when VERBOSE.
verb = $(if $(filter-out 0,$(VERBOSE)),,@)
