PULP_APP = stimuli

PULP_APP_FC_SRCS = stimuli.c
PULP_APP_SRCS = support_func.c matmul.c

PULP_CFLAGS += -O3 -g3
PULP_CFLAGS += -mno-memcpy

XLEN:=32

PULP_CFLAGS += -DNUM_CORES=8 -DUSE_INTRINSICS -DTHR=0.004f -DFIXED -DFP32 -DCHECK

PULP_CFLAGS += -fno-tree-vectorize

ifdef print_results
PULP_CFLAGS += -DPRINT_RESULTS
endif

ifdef verbose
PULP_CFLAGS += -DVERBOSE
endif

ifdef stats
PULP_CFLAGS += -DSTATS
endif

include ../../common_pulp/common_pulp.mk



