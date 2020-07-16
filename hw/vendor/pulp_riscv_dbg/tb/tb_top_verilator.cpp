// Copyright 2018 Robert Balas <balasr@student.ethz.ch>
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.


// Top level wrapper for a verilator RI5CY testbench
// Contributor: Robert Balas <balasr@student.ethz.ch>

#include "svdpi.h"
#include "Vtb_top_verilator__Dpi.h"
#include "Vtb_top_verilator.h"
#include "verilated_vcd_c.h"
#include "verilated.h"

#include <iostream>
#include <iomanip>
#include <fstream>
#include <exception>
#include <cstdio>
#include <cstdint>
#include <cerrno>

void dump_memory();
double sc_time_stamp();

static vluint64_t t = 0;
Vtb_top_verilator *top;

int main(int argc, char **argv, char **env)
{
    Verilated::commandArgs(argc, argv);
    Verilated::traceEverOn(true);
    top = new Vtb_top_verilator();

    svSetScope(svGetScopeFromName(
        "TOP.tb_top_verilator.mm_ram_i.dp_ram_i"));
    Verilated::scopesDump();

#ifdef VCD_TRACE
    VerilatedVcdC *tfp = new VerilatedVcdC;
    top->trace(tfp, 99);
    tfp->open("verilator_tb.vcd");
#endif
    top->fetch_enable_i = 1;
    top->clk_i          = 0;
    top->rst_ni         = 0;

    top->eval();
    dump_memory();

    while (!Verilated::gotFinish()) {
        if (t > 40)
            top->rst_ni = 1;
        top->clk_i = !top->clk_i;
        top->eval();
#ifdef VCD_TRACE
        tfp->dump(t);
#endif
        t += 5;
    }
#ifdef VCD_TRACE
    tfp->close();
#endif
    delete top;
    exit(0);
}

double sc_time_stamp()
{
    return t;
}

void dump_memory()
{
    errno = 0;
    std::ofstream mem_file;
    svLogicVecVal addr = {0};

    mem_file.exceptions(std::ofstream::failbit | std::ofstream::badbit);
    try {
        mem_file.open("memory_dump.bin");
        for (size_t i = 0; i < 1048576; i++) {
            addr.aval    = i;
            uint32_t val = read_byte(&addr);
            mem_file << std::setfill('0') << std::setw(2) << std::hex << val
                     << std::endl;
        }
        mem_file.close();

        std::cout << "finished dumping memory" << std::endl;

    } catch (std::ofstream::failure e) {
        std::cerr << "exception opening/reading/closing file memory_dump.bin\n";
    }
}
