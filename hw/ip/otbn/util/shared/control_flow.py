#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from typing import Dict, List, Set, Tuple

from .decode import OTBNProgram
from .insn_yaml import Insn
from .section import CodeSection


class ControlLoc:
    '''Base class for control-flow locations.

    Represents a normal PC that a branch or jump instruction could link to.
    '''
    def __init__(self, pc: int) -> None:
        self.pc = pc

    @classmethod
    def is_special(cls) -> bool:
        return False

    def pretty(self) -> str:
        return '{:#x}'.format(self.pc)


class ImemEnd(ControlLoc):
    '''Represents the end of instruction memory.'''
    def __init__(self) -> None:
        super().__init__(-1)

    @classmethod
    def is_special(cls) -> bool:
        return True

    def pretty(self) -> str:
        return '<imem end>'


class Ret(ControlLoc):
    '''Represents the location at the top of the call stack.'''
    def __init__(self) -> None:
        super().__init__(-1)

    @classmethod
    def is_special(cls) -> bool:
        return True

    def pretty(self) -> str:
        return 'RET'


class Ecall(ControlLoc):
    '''Represents program termination as a result of an ecall.'''
    def __init__(self) -> None:
        super().__init__(-1)

    @classmethod
    def is_special(cls) -> bool:
        return True

    def pretty(self) -> str:
        return 'ECALL'


class LoopStart(ControlLoc):
    '''Represents the start of a loop.

    The `loop_start_pc` is the first PC of the loop body, and the `loop_end_pc`
    is the last PC of the loop body.
    '''
    def __init__(self, loop_start_pc: int, loop_end_pc: int):
        super().__init__(loop_start_pc)
        self.loop_start_pc = loop_start_pc
        self.loop_end_pc = loop_end_pc

    @classmethod
    def is_special(cls) -> bool:
        return True

    def pretty(self) -> str:
        return '<loop from {:#x}-{:#x}>'.format(self.loop_start_pc,
                                                self.loop_end_pc)


class Cycle(ControlLoc):
    '''Represents a control flow that loops back to a previous PC.

    This is not represented as a normal ControlLoc because it's convenient to
    catch these cyclic control flows rather than follow the jump/branch and
    potentially cause an infinite loop; with this structure, the control-flow
    graph remains a DAG.
    '''
    @classmethod
    def is_special(cls) -> bool:
        return True

    def pretty(self) -> str:
        return '<cycle: back to {:#x}>'.format(self.pc)


class LoopEnd(Cycle):
    '''Represents the end of a loop (looping back to the start).

    Contains the LoopStart instance we're looping back to.
    '''
    def __init__(self, loop_start: LoopStart):
        super().__init__(loop_start.loop_start_pc)
        self.loop_start = loop_start

    def pretty(self) -> str:
        return '<loop end: back to {:#x}>'.format(
            self.loop_start.loop_start_pc)


class ControlGraph:
    '''Represents the control flow graph of (part of) an OTBN program.

    The `start` PC is the entrypoint of the control-flow graph.

    The `graph` dictionary maps PCs to 2-item tuples. Not all PCs are in
    `graph`; only ones that are jumped, branched, or looped to in the control
    flow starting at `start`. The 2-item tuple for each PC is as follows:
        - 0: the CodeSection that starts at the PC. It is guaranteed to be 0
          or more straightline instructions, followed by a final
          non-straightline instruction.
        - 1: a list of the various control-flow locations that can be reached
          *after* the CodeSection has run.  For example, a CodeSection ending
          in a BNE instruction would have two ControlLocs in its list, and a
          CodeSection ending in `ret` would have a single Ret() instance in its
          list.
    '''
    def __init__(self, start: int, graph: Dict[int, Tuple[CodeSection,
                                                          List[ControlLoc]]]):
        for pc, (sec, _) in graph.items():
            assert sec.start == pc
        self.start = start
        self.graph = graph

    def get_entry(self, pc: int) -> Tuple[CodeSection, List[ControlLoc]]:
        '''Returns the entry in the graph for the given PC.

        Raises a ValueError if the PC is not in the graph.
        '''
        try:
            return self.graph[pc]
        except KeyError:
            graph_pcs = [hex(pc) for pc in self.graph.keys()]
            raise ValueError(
                'PC {:#x} not found in control graph (PCs in graph are: {})'.
                format(pc, graph_pcs)) from None

    def get_section(self, pc: int) -> CodeSection:
        '''Returns the CodeSection for the given PC.

        Raises a ValueError if the PC is not in the graph.
        '''
        return self.get_entry(pc)[0]

    def get_edges(self, pc: int) -> List[ControlLoc]:
        '''Returns the edges for the section starting at pc.

        Raises a ValueError if the PC is not in the graph.
        '''
        return self.get_entry(pc)[1]

    def get_cycle_starts(self) -> Set[int]:
        '''Returns start PCs of all marked cycles in the graph.'''
        out = set()
        for pc, entry in self.graph.items():
            for edge in entry[1]:
                if isinstance(edge, Cycle):
                    out.add(edge.pc)
        return out

    def _pretty_lines(self,
                      program: OTBNProgram,
                      entry_pc: int,
                      concise: bool,
                      already_printed: Set[int],
                      call_stack: List[int] = []) -> List[Tuple[int, str]]:
        '''Returns lines for pretty-printing.

        Returns each line as an (int,str) pair, where the int is the indent
        level.
        '''
        out = []
        sec, edges = self.get_entry(entry_pc)
        symbols = [s for s in program.get_symbols_for_pc(entry_pc) if s != '']
        pcs_to_print = list(range(sec.start, sec.end + 4, 4))
        if entry_pc in already_printed and not concise:
            if len(symbols) > 0:
                out.append((0, '<{}> (see above)'.format(', '.join(symbols))))
            else:
                out.append(
                    (0, '{:#x}..{:#x} (see above)'.format(entry_pc, sec.end)))
            pcs_to_print = []
        elif len(symbols) > 0:
            out.append((0, '<{}>'.format(', '.join(symbols))))
        if concise:
            # only print last insn
            out.append((0, '...'))
            pcs_to_print = [sec.end]
        for pc in pcs_to_print:
            insn = program.get_insn(pc)
            operands = program.get_operands(pc)
            disassembly = insn.disassemble(pc, operands)
            out.append((0, '{:#x}: {}'.format(pc, disassembly)))
            already_printed.add(sec.start)
        # Indent if we have more than 1 non-special edge, excluding LoopEnds
        # (i.e. if this is a branch)
        non_special_edges = [
            loc for loc in edges
            if not (loc.is_special() or isinstance(loc, LoopEnd))
        ]
        child_indent = 0 if len(non_special_edges) <= 1 else 2
        if any(map(lambda loc: isinstance(loc, LoopEnd), edges)):
            child_indent = -2
        for loc in edges:
            if isinstance(loc, LoopEnd):
                out.append((0, loc.pretty()))
                continue
            if len(non_special_edges) > 1:
                last_insn = program.get_insn(sec.end)
                out.append((0, '-> (branch from {:#x}: {})'.format(
                    sec.end, last_insn.mnemonic)))
            if loc.is_special():
                out.append((child_indent, loc.pretty()))
                if isinstance(loc, Ret) and len(call_stack) > 0:
                    # pop the call stack and print flow after return to caller
                    out += [(indent - 2, line)
                            for indent, line in self._pretty_lines(
                                program, call_stack[0], concise,
                                already_printed, call_stack[1:])]
                if isinstance(loc, LoopStart):
                    out += [(indent + child_indent + 2, line)
                            for indent, line in self._pretty_lines(
                                program, loc.loop_start_pc, concise,
                                already_printed, call_stack)]
            else:
                insn = program.get_insn(sec.end)
                operands = program.get_operands(sec.end)
                if insn.mnemonic == 'jal' and operands['grd'] == 1:
                    # push to the call stack
                    call_stack = [sec.end + 4] + call_stack
                    child_indent += 2
                out += [
                    (indent + child_indent, line)
                    for indent, line in self._pretty_lines(
                        program, loc.pc, concise, already_printed, call_stack)
                ]
        return out

    def pretty(self,
               program: OTBNProgram,
               indent: int = 0,
               concise: bool = False) -> str:
        '''Returns string for pretty-printing.'''
        lines = self._pretty_lines(program, self.start, concise, set())
        lines = [(indent + lindent, line) for (lindent, line) in lines]
        line_strings = [
            '{}{}'.format(' ' * lindent, line) for (lindent, line) in lines
        ]
        return '\n'.join(line_strings)


def _clip_to_32(value: int) -> int:
    '''Truncates a number to 32 bits.'''
    return value & ((1 << 32) - 1)


def _get_next_control_locations(insn: Insn, operands: Dict[str, int],
                                pc: int) -> List[ControlLoc]:
    '''Given a control-flow instruction, returns the possible destinations.

    Raises a RuntimeError if the instruction is not a recognized control-flow
    instruction, or if some unsupported construct is encountered.
    '''
    if insn.mnemonic == 'beq' or insn.mnemonic == 'bne':
        branch_dst = _clip_to_32(operands['offset'])
        # Branch can either go to branch_dst or next PC
        return [ControlLoc(branch_dst), ControlLoc(pc + 4)]
    elif insn.mnemonic == 'jal':
        jump_dst = _clip_to_32(operands['offset'])
        return [ControlLoc(jump_dst)]
    elif insn.mnemonic == 'jalr':
        if operands['grs1'] != 1:
            # This is a function call through a pointer e.g. `jal x1,
            # <addr>, 0`; not currently supported
            raise RuntimeError(
                'Cannot create control graph because of a function '
                'call from a pointer at PC {:#x}: {}\nThis is '
                'permitted by OTBN but not supported by this check.'.format(
                    pc, insn.disassemble(pc, operands)))
        if operands['offset'] != 0:
            raise RuntimeError(
                'Cannot create control graph because of a nonzero offset for '
                'JALR at PC {:#x}: {}.\nThis is permitted by OTBN but not '
                'supported by this check.'.format(
                    pc, insn.disassemble(pc, operands)))
        # This jump returns to whatever's on top of the call stack
        return [Ret()]
    elif insn.mnemonic == 'loopi' or insn.mnemonic == 'loop':
        loop_end_pc = pc + (operands['bodysize'] * 4)
        return [LoopStart(pc + 4, loop_end_pc)]
    elif insn.mnemonic == 'ecall':
        return [Ecall()]

    raise RuntimeError('Unrecognized control flow instruction '
                       '(straight-line=false) at PC {:#x}: {}'
                       .format(pc, insn.disassemble(pc, operands)))


def _populate_control_graph(graph: ControlGraph, program: OTBNProgram,
                            start_pc: int,
                            loop_stack: List[LoopStart]) -> None:
    '''Populates input control flow graph starting from start_pc.

    The `loop_stack` argument holds the LoopStart instances for all the loops
    that enclose the start_pc, with the innermost loop first. This routine
    checks only for the innermost loop's end PC; if the loops are incorrectly
    nested, it will not warn. However, it will raise a RuntimeError if the loop
    stack size (8) is exceeded.

    This function will not record cycles in the control graph with the Cycle
    instance; run _fix_cycles afterward.
    '''
    LOOP_STACK_SIZE = 8

    if start_pc in graph.graph:
        # Nothing to do; this section has already been populated.
        return

    # Top element of the loop stack, if any:
    loop = loop_stack[0] if len(loop_stack) > 0 else None

    # Follow straightline code until we get to a control flow instruction, the
    # end of the loop body, or the end of imem
    for pc in range(start_pc, program.max_pc() + 4, 4):

        # Special handling for reaching the end of a loop body
        if loop is not None and pc == loop.loop_end_pc:
            # Finished the loop; add the current section and connect it to a
            # LoopEnd instance as well as the next pc, then recurse on the next
            # PC.
            sec = CodeSection(start_pc, pc)
            graph.graph[start_pc] = (sec, [LoopEnd(loop), ControlLoc(pc + 4)])
            _populate_control_graph(graph, program, pc + 4, loop_stack[1:])
            return

        insn = program.get_insn(pc)
        if insn.straight_line:
            continue
        operands = program.get_operands(pc)
        section = CodeSection(start_pc, pc)
        locs = _get_next_control_locations(insn, operands, pc)
        if start_pc in graph.graph:
            raise RuntimeError
        graph.graph[start_pc] = (section, locs)

        # Recurse on next control-flow locations.
        for loc in locs:
            if not loc.is_special():
                # Destination is just a normal PC
                _populate_control_graph(graph, program, loc.pc, loop_stack)
            elif isinstance(loc, LoopStart):
                if len(loop_stack) >= LOOP_STACK_SIZE - 1:
                    loop_start_pcs = [
                        loop.loop_start_pc for loop in [loc] + loop_stack
                    ]
                    raise RuntimeError(
                        'Loop stack overflow at PC {} (loop stack includes '
                        'loops starting at the following PCs: {})'.format(
                            pc, loop_start_pcs))
                _populate_control_graph(graph, program, loc.loop_start_pc,
                                        [loc] + loop_stack)
            elif isinstance(loc, ImemEnd) or isinstance(
                    loc, Ecall) or isinstance(loc, Ret):
                # Nothing more to do
                pass
            else:
                raise ValueError(
                    'Control-flow location of type {} is special '
                    'but does not have a recognized special type.'.format(
                        type(loc)))

        # If this was a jump that pushed to the call stack, we need to also
        # populate the control graph for what happens after we return from the
        # jump
        if insn.mnemonic == 'jal' and operands['grd'] == 1:
            _populate_control_graph(graph, program, pc + 4, loop_stack)

        return

    # If we get here, we've reached the max PC
    graph.graph[start_pc] = (CodeSection(start_pc,
                                         program.max_pc()), [ImemEnd()])
    return


def _label_cycles(program: OTBNProgram, graph: ControlGraph, start_pc: int,
                  visited_pcs: Set[int]) -> None:
    '''Creates Cycle edges to remove cyclic control flow from the graph.

    Modifies graph in place. Works by replacing edges that loop back to an
    already-traversed part of the control flow with a Cycle instance.
    '''
    sec, edges = graph.get_entry(start_pc)
    for pc in sec:
        visited_pcs.add(pc)
    for i in range(len(edges)):
        edge = edges[i]
        if isinstance(edge, Ret) or isinstance(edge, ImemEnd) or isinstance(
                edge, Ecall):
            # Cannot possibly loop back
            continue
        elif isinstance(edge, Cycle):
            # Done; no need to traverse or replace
            continue
        if edge.pc in visited_pcs:
            # Replace with Cycle instance and do not traverse
            edges[i] = Cycle(edge.pc)
        else:
            _label_cycles(program, graph, edge.pc, visited_pcs.copy())


def _fix_cycles(program: OTBNProgram, graph: ControlGraph) -> None:
    '''Labels cycles and splits them from other CodeSections in the graph.

    Modifies graph in place.
    '''
    _label_cycles(program, graph, graph.start, set())
    cycle_start_pcs = graph.get_cycle_starts()
    # The new_entries dictionary will have the same structure as graph.graph.
    new_entries = {}
    for start_pc in graph.graph:
        sec, edges = graph.get_entry(start_pc)
        for pc in sec:
            if pc in cycle_start_pcs and pc != sec.start:
                # Split this section and create a new edge leading to the cycle
                new_entries[start_pc] = (CodeSection(start_pc,
                                                     pc), [ControlLoc(pc)])
                break
    graph.graph.update(new_entries)


def _make_control_graph(program: OTBNProgram, start_pc: int) -> ControlGraph:
    '''Constructs a control flow graph with start_pc as the entrypoint.

    Assumes the loop stack is empty at start_pc.
    '''
    graph = ControlGraph(start_pc, {})
    _populate_control_graph(graph, program, start_pc, [])
    _fix_cycles(program, graph)
    return graph


def program_control_graph(program: OTBNProgram) -> ControlGraph:
    '''Constructs a control flow graph representing an entire program.'''
    return _make_control_graph(program, program.min_pc())


def subroutine_control_graph(program: OTBNProgram,
                             subroutine: str) -> ControlGraph:
    '''Control flow graph from the given symbol to the first unmatched `ret`.

    The control flow graph finishes when either an `ecall` instruction is
    reached or a `ret` returns to the caller of the subroutine.
    '''
    start_pc = program.get_pc_at_symbol(subroutine)
    return _make_control_graph(program, start_pc)
