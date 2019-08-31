LINT_TOOL := verilator --lint-only

# Setting IP_NAME and PRJ_DIR. Assuming Makefile located at `hw/ip/<ip_name>/dv`
IP_DIR    := $(shell dirname $(realpath $(lastword $(MAKEFILE_LIST))))
wordslist := $(subst /, ,${IP_DIR})
IP_NAME   := $(lastword ${wordslist})
#IP_NAME  := $(word $(words ${wordslist}),${wordslist})

export PRJ_DIR:= $(realpath ${IP_DIR}/../../..)

lint:
	${LINT_TOOL} -f rtl/deps.f -f rtl/${IP_NAME}.f --top-module rv_dm
	${LINT_TOOL} -f rtl/deps.f -f rtl/${IP_NAME}.f --top-module dmi_jtag
