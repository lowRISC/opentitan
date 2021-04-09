#!/usr/bin/python3

## Summary:
## This Python script will create regression_list.json file which was referred by by .metrics.json
## Limitation:
## Only generate tests targeted for build "rv32imc"
##
## Note: Currently available testlists 
##   <rootDir>/yaml/base_testlist.yaml
##   <rootDir>/yaml/cov_testlist.yaml
##   <rootDir>/target/rv64gcv/testlist.yaml
##   <rootDir>/target/rv64gc/testlist.yaml
##   <rootDir>/target/rv32imcb/testlist.yaml
##   <rootDir>/target/multi_harts/testlist.yaml
##   <rootDir>/target/rv64imc/testlist.yaml
##   <rootDir>/target/rv32imc/testlist.yaml
##   <rootDir>/target/rv64imcb/testlist.yaml
##   <rootDir>/target/ml/testlist.yaml
##   <rootDir>/target/rv32i/testlist.yaml

import json

runCmdBase = "cd /mux-flow/results; python3 <rootDir>/run.py --test TESTNAME --simulator dsim --iss spike --seed <seed> --so --out <rootDir>/out --verbose; <rootDir>/scripts/check-status $?; rm -fr <rootDir>/out/dsim"

## Based on testlist located in <rootDir>/yaml/base_testlist.yaml
base_testList = ["riscv_arithmetic_basic_test",
            "riscv_rand_instr_test",
            "riscv_jump_stress_test",
            "riscv_loop_test",
            "riscv_rand_jump_test",
            "riscv_mmu_stress_test",
            "riscv_no_fence_test",
            "riscv_illegal_instr_test",
            "riscv_ebreak_test",
            "riscv_ebreak_debug_mode_test",
            "riscv_full_interrupt_test",
            ## remove, will cause incomplete sim, need customized RTL
            ##"riscv_csr_test",
            "riscv_unaligned_load_store_test"]

## Based on testlist located in <rootDir>/target/rv32imc/testlist.yaml
rv32imc_testList = [
        "riscv_non_compressed_instr_test",
        "riscv_hint_instr_test",
        "riscv_pmp_test"
        ]

metricsList = []

## Note: Build is targeting rv32imc only.
for testName in base_testList + rv32imc_testList:
        test = {}
        test["name"] = testName
        test["build"] = "rv32imc"
        test["cmd"] = runCmdBase.replace("TESTNAME", testName)
        test["wavesCmd"] = test["cmd"]
        test["logFile"] = "simulation.log"
        test["isPass"] = "Test passed"
        test["metricsFile"] = "metrics.db"
        test["seed"] = "random"
            
        metricsList.append(test)

with open("regression_list.json", "w") as f:
    json.dump(metricsList, f)
