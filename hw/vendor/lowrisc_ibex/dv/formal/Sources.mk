SAIL_XLEN := riscv_xlen32.sail

SAIL_CHECK_SRCS = riscv_addr_checks_common.sail riscv_addr_checks.sail riscv_misa_ext.sail
SAIL_DEFAULT_INST = riscv_insts_base.sail riscv_insts_cext.sail riscv_insts_mext.sail riscv_insts_zicsr.sail

SAIL_SEQ_INST  = $(SAIL_DEFAULT_INST) riscv_jalr_seq.sail

SAIL_SEQ_INST_SRCS  = riscv_insts_begin.sail $(SAIL_SEQ_INST) riscv_insts_end.sail

SAIL_SYS_SRCS =  riscv_csr_map.sail
SAIL_SYS_SRCS += riscv_sys_exceptions.sail
SAIL_SYS_SRCS += riscv_sync_exception.sail
SAIL_SYS_SRCS += riscv_csr_ext.sail
SAIL_SYS_SRCS += riscv_sys_control.sail

PRELUDE = prelude.sail $(SAIL_XLEN) prelude_mem_metadata.sail prelude_mem.sail

SAIL_REGS_SRCS = riscv_reg_type.sail riscv_regs.sail riscv_pc_access.sail riscv_sys_regs.sail
SAIL_REGS_SRCS += riscv_pmp_regs.sail riscv_pmp_control.sail
SAIL_REGS_SRCS += riscv_ext_regs.sail $(SAIL_CHECK_SRCS)

SAIL_ARCH_SRCS = $(PRELUDE)
SAIL_ARCH_SRCS += riscv_types_common.sail riscv_types_ext.sail riscv_types.sail
SAIL_ARCH_SRCS += riscv_vmem_types.sail $(SAIL_REGS_SRCS) $(SAIL_SYS_SRCS) riscv_platform.sail
SAIL_ARCH_SRCS += riscv_mem.sail

SAIL_SRCS      = $(addprefix $(SAIL_RISCV_MODEL_DIR)/,$(SAIL_ARCH_SRCS) $(SAIL_SEQ_INST_SRCS))