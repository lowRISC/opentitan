# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from collections import Counter
import typing
from typing import Dict, List, Optional, Tuple

from elftools.dwarf.dwarfinfo import DWARFInfo  # type: ignore
from elftools.elf.elffile import ELFFile  # type: ignore
from elftools.elf.sections import SymbolTableSection  # type: ignore
from tabulate import tabulate

from .insn import BEQ, BNE, ECALL, JAL, JALR, LOOP, LOOPI
from .isa import OTBNInsn
from .state import OTBNState


class ExecutionStats:
    def __init__(self, program: List[OTBNInsn]) -> None:
        # Executed program (the contents of the instruction memory).
        self.program = program

        self.stall_count = 0
        self.insn_histo = Counter()  # type: typing.Counter[str]
        self.func_calls = []  # type: List[Dict[str, int]]
        self.loops = []  # type: List[Dict[str, int]]

        # Histogram indexed by the length of the (extended) basic block.
        self.basic_block_histo = Counter()  # type: typing.Counter[int]
        self.ext_basic_block_histo = Counter()  # type: typing.Counter[int]

        self._current_basic_block_len = 0
        self._current_ext_basic_block_len = 0

    def get_insn_count(self) -> int:
        '''Get the number of executed instructions.'''
        return sum(self.insn_histo.values())

    def record_stall(self) -> None:
        '''Record a single stall cycle.'''
        self.stall_count += 1

    def _insn_at_addr(self, addr: int) -> Optional[OTBNInsn]:
        '''Get the instruction at a given address.'''
        assert addr % 4 == 0
        assert addr >= 0
        word_addr = addr >> 2
        return self.program[word_addr]

    def record_insn(self,
                    insn: OTBNInsn,
                    state_bc: OTBNState) -> None:
        '''Record the execution of an instruction.

        insn is the currently executed instruction. state_bc is the state of
        OTBN before the instruction is committed.

        '''
        pc = state_bc.pc

        is_jump = isinstance(insn, JAL) or isinstance(insn, JALR)
        is_branch = isinstance(insn, BEQ) or isinstance(insn, BNE)

        # Instruction histogram
        self.insn_histo[insn.insn.mnemonic] += 1

        # Function calls
        # - Direct function calls: jal x1, <offset>
        # - Indirect function calls: jalr x1, <grs1>, 0
        if is_jump and insn.grd == 1:  # type: ignore
            call_stack = state_bc.peek_call_stack()
            if call_stack:
                caller_func = call_stack[0]
            else:
                caller_func = 0  # (start address)

            self.func_calls.append({
                'call_site': pc,
                'caller_func': caller_func,
                'callee_func': state_bc.get_next_pc(),
            })

        # Loops
        if isinstance(insn, LOOP) or isinstance(insn, LOOPI):
            assert state_bc.in_loop()
            iterations = state_bc.loop_stack.stack[-1].loop_count
            self.loops.append({
                'loop_addr': pc,
                'loop_len': insn.bodysize,
                'iterations': iterations,
            })

        last_in_loop_body = state_bc.loop_stack.is_last_insn_in_loop_body(pc)

        # Basic blocks
        #
        # A basic block is a linear sequence of code ending with an instruction
        # that can potentially change the control flow: a jump, a branch, the
        # last instruction in a loop (LOOP or LOOPI) body, or an ECALL. The
        # length of the basic block equals the number of instructions within
        # the basic block.
        self._current_basic_block_len += 1
        if (is_jump or is_branch or last_in_loop_body or
                isinstance(insn, ECALL)):

            self.basic_block_histo[self._current_basic_block_len] += 1
            self._current_basic_block_len = 0

        # Extended basic blocks
        #
        # An extended basic block is a sequence of one or more basic blocks
        # which can be statically determined at compile time. Extended basic
        # blocks end with a branch, the last instruction in a LOOP body, or an
        # ECALL instruction.

        # Determine if the current instruction is the last instruction in a
        # LOOP body (only LOOP, not LOOPI!).
        finishing_loop = False
        if last_in_loop_body:
            loop_insn_addr = state_bc.loop_stack.stack[-1].get_loop_insn_addr()
            last_insn = self._insn_at_addr(loop_insn_addr)
            finishing_loop = isinstance(last_insn, LOOP)

        self._current_ext_basic_block_len += 1
        if is_branch or finishing_loop or isinstance(insn, ECALL):
            self.ext_basic_block_histo[self._current_ext_basic_block_len] += 1
            self._current_ext_basic_block_len = 0


def _dwarf_decode_file_line(dwarf_info: DWARFInfo,
                            address: int) -> Optional[Tuple[str, int]]:
    # Go over all the line programs in the DWARF information, looking for
    # one that describes the given address.
    for CU in dwarf_info.iter_CUs():
        # First, look at line programs to find the file/line for the address
        lineprog = dwarf_info.line_program_for_CU(CU)
        prevstate = None
        for entry in lineprog.get_entries():
            # We're interested in those entries where a new state is assigned
            if entry.state is None:
                continue
            if entry.state.end_sequence:
                # if the line number sequence ends, clear prevstate.
                prevstate = None
                continue
            # Looking for a range of addresses in two consecutive states that
            # contain the required address.
            if ((prevstate and
                 prevstate.address <= address < entry.state.address)):
                raw_name = lineprog['file_entry'][prevstate.file - 1].name
                filename = raw_name.decode('utf-8')
                line = prevstate.line
                return filename, line
            prevstate = entry.state
    return None


def _get_addr_symbol_map(elf_file: ELFFile) -> Dict[int, str]:
    section = elf_file.get_section_by_name('.symtab')

    if not isinstance(section, SymbolTableSection):
        return {}

    return {sym.entry.st_value: sym.name for sym in section.iter_symbols()}


class ExecutionStatAnalyzer:
    # Assumed clock frequency of OTBN, in MHz.
    FREQ_MHZ = 100

    def __init__(self, stats: ExecutionStats, elf_file_path: str):
        self._elf_file = ELFFile(open(elf_file_path, 'rb'))
        self._stats = stats
        self._addr_symbol_map = _get_addr_symbol_map(self._elf_file)

    def _describe_imem_addr(self, address: int) -> str:
        symbol_name = None
        if address in self._addr_symbol_map:
            symbol_name = self._addr_symbol_map[address]
        else:
            # |func_addr| is the largest possible |sym_addr| which is at most
            # |address|.
            func_addr = 0
            for sym_addr in self._addr_symbol_map.keys():
                if sym_addr <= address and sym_addr > func_addr:
                    func_addr = sym_addr
            func_name = self._addr_symbol_map[func_addr]
            symbol_name = func_name + f"+{address - func_addr:#x}"

        file_line = None
        if self._elf_file.has_dwarf_info():
            dwarf_info = self._elf_file.get_dwarf_info()
            file_line = _dwarf_decode_file_line(dwarf_info, address)

        add_info = []
        if symbol_name:
            add_info.append(f"{symbol_name}")
        if file_line:
            add_info.append(f"at {file_line[0]}:{file_line[1]}")

        str = f"{address:#x}"
        if add_info:
            str += ' (' + ' '.join(add_info) + ')'
        return str

    def dump(self) -> str:
        out = ""
        out += "\n"
        out += "Execution time\n"
        out += "--------------\n"
        out += self._dump_execution_time()
        out += "\n\n"
        out += "Instruction frequencies\n"
        out += "-----------------------\n"
        out += self._dump_insn_histo()
        out += "\n\n"
        out += "Basic block statistics\n"
        out += "----------------------\n"
        out += self._dump_basic_block_stats()
        out += "\n\n"
        out += "Function call statistics\n"
        out += "------------------------\n"
        out += self._dump_function_call_stats()
        out += "\n\n"
        out += "Loop statistics\n"
        out += "---------------\n"
        out += self._dump_loop_stats()
        out += "\n"

        return out

    def _dump_execution_time(self) -> str:
        insn_count = self._stats.get_insn_count()
        stall_count = self._stats.stall_count
        stall_percent = stall_count / insn_count * 100
        cycles = insn_count + stall_count
        time_ms = cycles / (self.FREQ_MHZ * 1e6) * 1e3

        out = f"OTBN executed {insn_count} instructions in {cycles} cycles.\n"

        out += f"The execution stalled for {stall_count} cycles "
        out += f"({stall_percent:.01f} percent).\n"

        out += f"The execution would take {time_ms:.02f} ms "
        out += f"@ {self.FREQ_MHZ} MHz.\n"
        return out

    def _dump_insn_histo(self) -> str:
        return tabulate(self._stats.insn_histo.most_common(),
                        headers=['instruction', 'count']) + "\n"

    def _dump_basic_block_stats(self) -> str:
        out = []
        out += ["", "Number of instructions within a basic block", ""]
        out += [tabulate(sorted(self._stats.basic_block_histo.items()),
                         headers=['# of instr.', 'frequency'])]
        out += ['', '']
        out += ["Number of instructions within an extended basic block", ""]
        out.append(tabulate(sorted(self._stats.ext_basic_block_histo.items()),
                   headers=['# of instr.', 'frequency']))
        return '\n'.join(out)

    def _dump_function_call_stats(self) -> str:
        '''Dump function call statistics'''

        if not self._stats.func_calls:
            return "No functions were called.\n"

        out = ""

        # Build function call graphs and a call site index
        # caller-indexed == forward, callee-indexed == reverse
        #
        # The call graphs are on function granularity; the call sites
        # dictionary is indexed by the called function, but uses the call site
        # as value.
        callgraph = {}  # type: Dict[int, typing.Counter[int]]
        rev_callgraph = {}  # type: Dict[int, typing.Counter[int]]
        rev_callsites = {}  # type: Dict[int, typing.Counter[int]]
        for c in self._stats.func_calls:
            if c['caller_func'] not in callgraph:
                callgraph[c['caller_func']] = Counter()
            callgraph[c['caller_func']][c['callee_func']] += 1

            if c['callee_func'] not in rev_callgraph:
                rev_callgraph[c['callee_func']] = Counter()
            rev_callgraph[c['callee_func']][c['caller_func']] += 1

            if c['callee_func'] not in rev_callsites:
                rev_callsites[c['callee_func']] = Counter()
            rev_callsites[c['callee_func']][c['call_site']] += 1

        total_leaf_calls = 0
        total_calls_to_funcs_with_one_callsite = 0
        total_func_calls = 0
        for rev_callee_func, rev_caller_funcs in rev_callgraph.items():
            has_one_callsite = False
            func = self._describe_imem_addr(rev_callee_func)
            out += f"Function {func}\n"
            out += "  is called from the following functions\n"
            for rev_caller_func, cnt in rev_caller_funcs.most_common():
                func = self._describe_imem_addr(rev_caller_func)
                out += f"    * {cnt} times by function {func}\n"
            out += "  from the following call sites\n"
            for rc, cnt in rev_callsites[rev_callee_func].most_common():
                func = self._describe_imem_addr(rc)
                out += f"    * {cnt} times from {func}\n"

            has_one_callsite = len(rev_callsites[rev_callee_func]) == 1

            out += "  calls\n"
            if rev_callee_func not in callgraph:
                out += "    no other function (leaf function).\n"

                if not has_one_callsite:
                    # We don't count it as leaf function call if it has only
                    # one call site to prevent double-counting these as
                    # optimization opportunity.
                    total_leaf_calls += sum(rev_caller_funcs.values())
            else:
                caller_funcs = callgraph[rev_callee_func]
                for caller_func, cnt in caller_funcs.most_common():
                    func = self._describe_imem_addr(caller_func)
                    out += f"    * {cnt} times function {func}\n"
            out += "\n"

            if has_one_callsite:
                total_calls_to_funcs_with_one_callsite += (
                    rev_caller_funcs.most_common()[0][1])

            total_func_calls += sum(rev_caller_funcs.values())
        out += "\n"

        # Function call statistics
        total_calls_req_call = (total_func_calls - total_leaf_calls -
                                total_calls_to_funcs_with_one_callsite)
        out += f"Of a total of {total_func_calls} function calls, there were\n"
        out += (f"  {total_calls_to_funcs_with_one_callsite} function calls "
                f"to a function with only one call site (call/ret can be "
                f"replaced with static jumps)\n")
        out += (f"  {total_leaf_calls} leaf function calls "
                f"(no function prologue/epilogue needed)\n")
        out += (f"Overall, {total_calls_req_call} of {total_func_calls} "
                f"({(total_calls_req_call / total_func_calls * 100):.02f} "
                f"percent) calls need full function call semantics.\n")

        return out

    def _dump_loop_stats(self) -> str:
        loops = self._stats.loops
        loop_cnt = len(loops)

        out = f"Loops: {loop_cnt}\n"

        if loop_cnt != 0:
            loop_len_values = [loop['loop_len'] for loop in loops]
            loop_len_min = min(loop_len_values)
            loop_len_max = max(loop_len_values)
            loop_len_avg = sum(loop_len_values) / loop_cnt

            loop_iterations_values = [loop['iterations'] for loop in loops]
            loop_iterations_min = min(loop_iterations_values)
            loop_iterations_max = max(loop_iterations_values)
            loop_iterations_avg = sum(loop_iterations_values) / loop_cnt

            out += "Loop body length (instructions): "
            out += f"min: {loop_len_min}, max: {loop_len_max}, "
            out += f"avg: {loop_len_avg:.02f}\n"

            out += f"Number of iterations: min: {loop_iterations_min}, "
            out += f"max: {loop_iterations_max}, "
            out += f"avg: {loop_iterations_avg:.02f}\n"

        return out
