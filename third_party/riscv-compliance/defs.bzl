# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

"""Helper macros for generating RISC-V compliance test targets."""

load(
    "//rules:opentitan_test.bzl",
    "cw310_params",
    "opentitan_functest",
    "verilator_params",
)

def rv_compliance_test(name, arch):
    test_file = "@riscv-compliance//:riscv-test-suite/{}/src/{}.S".format(arch, name)
    reference_output = "@riscv-compliance//:riscv-test-suite/{}/references/{}.reference_output".format(arch, name)
    expected_signature = "{}.expected_signature.S".format(name)

    native.genrule(
        name = "{}_expected_signature".format(name),
        srcs = [reference_output],
        outs = [expected_signature],
        cmd = """
        echo "kExpectedSignature:" >> $@
        echo ".global kExpectedSignature" >> $@
        perl -pe 's/([a-fA-F0-9]+)/.word 0x$$1/' \
          $(location {}) \
          >> $@
        """.format(reference_output),
    )

    opentitan_functest(
        name = name,
        srcs = [
            test_file,
            expected_signature,
            "compliance_main.c",
            "compliance_main.S",
        ],
        cw310 = cw310_params(
            interface = "hyper310",
        ),
        verilator = verilator_params(
            timeout = "long",
        ),
        linkopts = ["-Wl,--no-relax"],
        deps = [
            "//sw/device/lib/testing/test_framework:ottf_main",
            "@riscv-compliance//:riscv-test-env",
        ],
    )

TESTS = {
    "rv32i": [
        "I-ADD-01",
        "I-ADDI-01",
        "I-AND-01",
        "I-ANDI-01",
        "I-AUIPC-01",
        "I-BEQ-01",
        "I-BGE-01",
        "I-BGEU-01",
        "I-BLT-01",
        "I-BLTU-01",
        "I-BNE-01",
        "I-DELAY_SLOTS-01",

        # TODO(lowrisc/opentitan#11876): Failing for unnknown reasons.
        #"I-EBREAK-01",
        "I-ECALL-01",
        "I-ENDIANESS-01",
        "I-IO-01",
        "I-JAL-01",
        "I-JALR-01",
        "I-LB-01",
        "I-LBU-01",
        "I-LH-01",
        "I-LHU-01",
        "I-LUI-01",
        "I-LW-01",

        # TODO(lowrisc/ibex#100): These tests are broken due to flaws in
        # riscv-compliance rather than Ibex/OpenTitan.
        #"I-MISALIGN_JMP-01",
        #"I-MISALIGN_LDST-01",

        # TODO(lowrisc/opentitan#11876): Failing for unnknown reasons.
        #"I-NOP-01",
        "I-OR-01",
        "I-ORI-01",
        "I-RF_size-01",
        "I-RF_width-01",
        # TODO(lowrisc/opentitan#11968): Failing do to sign-extension issue.
        #"I-RF_x0-01",
        "I-SB-01",
        "I-SH-01",
        "I-SLL-01",
        "I-SLLI-01",
        "I-SLT-01",
        "I-SLTI-01",
        "I-SLTIU-01",
        "I-SLTU-01",
        "I-SRA-01",
        "I-SRAI-01",
        "I-SRL-01",
        "I-SRLI-01",
        "I-SUB-01",
        "I-SW-01",
        "I-XOR-01",
        "I-XORI-01",
    ],
    "rv32im": [
        "DIV",
        "DIVU",
        "MUL",
        "MULH",
        "MULHSU",
        "MULHU",
        "REM",
        "REMU",
    ],
    "rv32imc": [
        "C-ADD",
        "C-ADDI",
        "C-ADDI16SP",
        "C-ADDI4SPN",
        "C-AND",
        "C-ANDI",
        "C-BEQZ",
        "C-BNEZ",
        "C-J",
        "C-JAL",
        "C-JALR",
        "C-JR",
        "C-LI",
        "C-LUI",
        "C-LW",
        "C-LWSP",
        "C-MV",
        "C-OR",
        "C-SLLI",
        "C-SRAI",
        "C-SRLI",
        "C-SUB",
        "C-SW",
        "C-SWSP",
        "C-XOR",
    ],
    "rv32Zicsr": [
        "I-CSRRC-01",
        "I-CSRRCI-01",
        "I-CSRRS-01",
        "I-CSRRSI-01",
        "I-CSRRW-01",
        "I-CSRRWI-01",
    ],
}
