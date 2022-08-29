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
