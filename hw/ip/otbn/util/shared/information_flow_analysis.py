#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from typing import Dict, List, Optional, Set, Tuple

from .cache import Cache, CacheEntry
from .constants import ConstantContext, get_op_val_str
from .control_flow import ControlLoc, ControlGraph, Ecall, ImemEnd, LoopStart, LoopEnd, Ret
from .decode import OTBNProgram
from .information_flow import InformationFlowGraph
from .insn_yaml import Insn

# Calls to _get_iflow return results in the form of a tuple with entries:
#   used constants: a set containing the names of input constants the
#                   results depend on; passing a different constants state with
#                   these entries unchanged should not change the results
#   return iflow:   an information-flow graph for any paths ending in a return
#                   to the address that is on top of the call stack at the
#                   original PC
#   end iflow:      an information-flow graph for any paths that lead to the
#                   end of the entire program (i.e. ECALL instruction or end of
#                   IMEM)
#   constants:      known constants that are in common between all "return"
#                   iflow paths (i.e. the constants that a caller can always
#                   rely on)
#   control deps:   a dictionary whose keys are the information-flow nodes
#                   whose values at the start PC influence the control flow of
#                   the program; the value is a set of PCs of control-flow
#                   instructions through which the node influences the control
#                   flow
IFlowResult = Tuple[Set[str], InformationFlowGraph, InformationFlowGraph,
                    ConstantContext, Dict[str, Set[int]]]


class IFlowCacheEntry(CacheEntry[ConstantContext, IFlowResult]):
    '''Represents an entry in the cache for _get_iflow.

    The key for the cache entry is the values of certain constants in the input
    `constants` dictionary for the _get_iflow call that produced the cached
    result. Only constants that were actually used in the process of computing
    the result are stored in the key; if another call to _get_iflow has the
    same values for those constants but different values for others, the result
    should not change.
    '''
    def is_match(self, constants: ConstantContext) -> bool:
        for k, v in self.key.values.items():
            if constants.get(k) != v:
                return False
        return True


class IFlowCache(Cache[int, ConstantContext, IFlowResult]):
    '''Represents the cache for _get_iflow.

    The index of the cache is the start PC for the call to _get_iflow. If this
    index and the values of the constants used in the call match a new call,
    the cached result is returned.
    '''
    pass


# The information flow of a subroutine is represented as a tuple whose entries
# are a subset of the IFlowResult tuple entries; in particular, it has the form
# (return iflow, end iflow, control deps).
SubroutineIFlow = Tuple[InformationFlowGraph, InformationFlowGraph,
                        Dict[str, Set[int]]]

# The information flow of a full program is the same as for a subroutine,
# except with no "return" information flow. Since the call stack is empty
# at the start, we're not expecting any return paths!
ProgramIFlow = Tuple[InformationFlowGraph, Dict[str, Set[int]]]


def _build_iflow_insn(
        insn: Insn, op_vals: Dict[str, int], pc: int,
        constants: ConstantContext) -> Tuple[Set[str], InformationFlowGraph]:
    '''Constructs the information-flow graph for a single instruction.

    Raises a ValueError if the information-flow graph cannot be constructed
    (for instance, because an indirect reference cannot be resolved).

    Returns the graph and the set of constants that the graph depends on; if a
    different constants dictionary was passed to this function that had the
    same values for those particular locations, then the resulting graph would
    be unchanged.
    '''
    # Check that the required-constant registers are constant here
    constant_deps = insn.iflow.required_constants(op_vals)
    for const in constant_deps:
        if const not in constants:
            raise ValueError(
                'Could not construct information flow because {} is '
                'not a known constant at PC {:#x}: {}'
                '\nKnown constants: {}'
                '\nIf the register is in fact a constant, you may '
                'need to add constant-tracking support for more '
                'instructions.'.format(const, pc,
                                       insn.disassemble(pc, op_vals),
                                       list(constants.values.keys())))

    return constant_deps, insn.iflow.evaluate(op_vals, constants.values)


def _get_insn_control_deps(insn: Insn, op_vals: Dict[str, int]) -> Set[str]:
    '''Returns names of regs that influence control flow for instruction.

    The x1 (call stack) special register is not returned if it's used as the
    function pointer for JALR.
    '''
    if insn.straight_line:
        return set()
    elif insn.mnemonic in ['beq', 'bne']:
        # both compared values influence control flow
        grs1_name = get_op_val_str(insn, op_vals, 'grs1')
        grs2_name = get_op_val_str(insn, op_vals, 'grs2')
        return {grs1_name, grs2_name}
    elif insn.mnemonic == 'jalr':
        if op_vals['grs1'] == 1:
            return set()
        # jump destination register influences control flow
        grs1_name = get_op_val_str(insn, op_vals, 'grs1')
        return {grs1_name}
    elif insn.mnemonic == 'loop':
        # loop #iterations influences control flow
        grs_name = get_op_val_str(insn, op_vals, 'grs')
        return {grs_name}
    elif insn.mnemonic in ['ecall', 'jal', 'loopi']:
        # these all rely only on immediates
        return set()
    # Should not get here
    raise ValueError('Unexpected control flow instruction: {}'.format(
        insn.mnemonic))


def _build_iflow_straightline(
        program: OTBNProgram, start_pc: int, end_pc: int,
        constants: ConstantContext) -> Tuple[Set[str], InformationFlowGraph]:
    '''Constructs the information-flow graph for a straightline code section.

    Returns two values:
    - The set of constants (at the start instruction) that the graph depends on
    - The information-flow graph

    The instruction at end_pc is included in the calculation. Errors upon
    encountering a control-flow instruction. Updates `constants` to hold the
    constant values after the section has finished.
    '''
    iflow = InformationFlowGraph.empty()
    constant_deps = set()

    for pc in range(start_pc, end_pc + 4, 4):
        insn = program.get_insn(pc)
        op_vals = program.get_operands(pc)

        assert insn.straight_line

        used_constants, insn_iflow = _build_iflow_insn(insn, op_vals, pc,
                                                       constants)
        for const in used_constants:
            constant_deps.update(iflow.sources(const))

        # Compose iflow with the information flow from this instruction
        iflow = iflow.seq(insn_iflow)

        # Update constants to their values after the instruction
        constants.update_insn(insn, op_vals)

    return constant_deps, iflow


def _get_constant_loop_iterations(insn: Insn, op_vals: Dict[str, int],
                                  constants: ConstantContext) -> Optional[int]:
    '''Given a loop instruction, returns the number of iterations if constant.

    If the number of iterations is not constant, returns None.
    '''
    # Get number of iterations (must be a constant)
    if insn.mnemonic == 'loopi':
        return op_vals['iterations']
    elif insn.mnemonic == 'loop':
        reg_name = get_op_val_str(insn, op_vals, 'grs')
        return constants.get(reg_name)

    # Should not get here!
    assert False


def _get_iflow_cache_update(pc: int, constants: ConstantContext,
                            result: IFlowResult, cache: IFlowCache) -> None:
    '''Updates the cache for _get_iflow.'''
    used_constants = result[0]
    used_constant_values = {}
    for name in used_constants:
        assert name in constants
        used_constant_values[name] = constants.values[name]

    cache.add(pc, IFlowCacheEntry(ConstantContext(used_constant_values),
                                  result))

    return


def _update_control_deps(current_deps: Dict[str, Set[int]],
                         iflow: InformationFlowGraph,
                         new_deps: Dict[str, Set[int]]) -> None:
    '''Update control-flow dependencies to include new data.

    The `current_deps` and `new_deps` dictionaries are assumed to hold
    information-flow nodes mapped to the PCs at which the nodes' starting
    values may influence control flow. The iflow graph is the information flow
    from the start PC of `current_deps` to the start PC of `new_deps`.

    This routine updates `current_deps` so that if a particular node is a
    *source* of one of the nodes in `new_deps`, then PCs in the `new_deps`
    entry are added to the entry of the source in `current_deps`.

    Updates `current_deps` in place. Does not modify `new_deps`.
    '''
    for node, pcs in new_deps.items():
        for source_node in iflow.sources(node):
            current_deps.setdefault(source_node, set()).update(pcs)
    return


def _get_iflow_update_state(
        rec_result: IFlowResult, iflow: InformationFlowGraph,
        program_end_iflow: InformationFlowGraph, used_constants: Set[str],
        control_deps: Dict[str, Set[int]]) -> InformationFlowGraph:
    '''Update the internal state of _get_iflow after a recursive call.

    The `used_constants` and `control_deps` state elements are updated in
    place, but the new `program_end_iflow` is returned. The `iflow` input is
    not modified.
    '''
    rec_used_constants, _, rec_program_end_iflow, _, rec_control_deps = rec_result

    # Update the used constants and control-flow dependencies
    for const in rec_used_constants:
        used_constants.update(iflow.sources(const))
    _update_control_deps(control_deps, iflow, rec_control_deps)

    # Update information flow results for paths where the program ends
    program_end_iflow.update(iflow.seq(rec_program_end_iflow))

    return program_end_iflow


def _get_iflow(program: OTBNProgram, graph: ControlGraph, start_pc: int,
               start_constants: ConstantContext, loop_end_pc: Optional[int],
               cache: IFlowCache) -> IFlowResult:
    '''Gets the information-flow graphs for paths starting at start_pc.

    Returns None for the return and/or end iflow if there are no paths ending
    in RET or the program end, respectively.

    Raises a ValueError if an indirect reference cannot be resolved, or if a
    loop has a number of iterations that can't be resolved to a compile-time
    constant.

    Caches results from recursive calls (updating input cache). Does not modify
    start_constants.
    '''
    cached = cache.lookup(start_pc, start_constants)
    if cached is not None:
        return cached

    constants = start_constants.copy()

    # The combined information flow for all paths leading to the end of the
    # subroutine (i.e. a RET, not counting RETS that happen after jumps within
    # the subroutine at start_pc). Initialize as nonexistent() because no paths
    # have yet been found.
    return_iflow = InformationFlowGraph.nonexistent()

    # The combined information flow for all paths leading to the end of the
    # program (i.e. an ECALL or the end of IMEM)
    program_end_iflow = InformationFlowGraph.nonexistent()

    # The control-flow nodes whose values at the start PC influence control
    # flow (and the PCs of the control-flow instructions they influence)
    control_deps: Dict[str, Set[int]] = {}

    section = graph.get_section(start_pc)
    edges = graph.get_edges(start_pc)

    # If we're crossing the loop end PC, we must do so at the end of the
    # section. In this case, we do not pass the end of the loop; we treat the
    # end of the loop like a RET instruction.
    if loop_end_pc is not None and loop_end_pc in section:
        assert loop_end_pc == section.end
        loop_end_pc = None
        edges = [Ret()]

    # Get the information flow, used constants, and known constants at the end
    # of the straightline block (not including the last instruction). Note that
    # _build_iflow_straightline updates the `constants` dictionary in-place.
    used_constants, iflow = _build_iflow_straightline(program, section.start,
                                                      section.end - 4,
                                                      constants)

    # Get the instruction/operands at the very end of the block (i.e. the
    # control-flow instruction) for special handling
    last_insn = program.get_insn(section.end)
    last_op_vals = program.get_operands(section.end)

    last_insn_used_constants, last_insn_iflow = _build_iflow_insn(
        last_insn, last_op_vals, section.end, constants)

    # Update used constants to include last instruction
    for const in last_insn_used_constants:
        used_constants.update(iflow.sources(const))

    # Update control_deps to include last instruction
    last_insn_control_deps = {
        node: {section.end}
        for node in _get_insn_control_deps(last_insn, last_op_vals)
    }
    _update_control_deps(control_deps, iflow, last_insn_control_deps)

    # Update information-flow to include last instruction
    iflow = iflow.seq(last_insn_iflow)

    if last_insn.mnemonic in ['loopi', 'loop']:
        # Special handling for loops; reject non-constant #iterations, and run
        # loop body #iterations times
        iterations = _get_constant_loop_iterations(last_insn, last_op_vals,
                                                   constants)
        if iterations is None:
            raise ValueError(
                'LOOP instruction on a register that is not a '
                'known constant at PC {:#x} (known constants: {}). If '
                'the register is in fact a constant, you may need to '
                'add constant-tracking support for more instructions.'.format(
                    section.end, constants.values.keys()))

        # A loop instruction should result in exactly one edge of type
        # LoopStart; check that assumption before we rely on it
        assert len(edges) == 1 and isinstance(edges[0], LoopStart)
        body_loc = edges[0]

        # Update the constants to include the loop instruction
        constants.update_insn(last_insn, last_op_vals)

        # Recursive calls for each iteration
        for _ in range(iterations):
            body_result = _get_iflow(program, graph, body_loc.loop_start_pc,
                                     constants, body_loc.loop_end_pc, cache)

            # Update program_end_iflow, used constants, and control_deps
            program_end_iflow = _get_iflow_update_state(
                body_result, iflow, program_end_iflow, used_constants,
                control_deps)

            # Update constants and get information flow for paths that loop
            # back to the start ("return")
            _, body_return_iflow, _, constants, _ = body_result

            # Compose current iflow with the flow for paths that hit the end of
            # the loop
            iflow = iflow.seq(body_return_iflow)

        # Set the next edges to the instruction after the loop ends
        edges = [ControlLoc(body_loc.loop_end_pc + 4)]
    elif last_insn.mnemonic == 'jal' and last_op_vals['grd'] == 1:
        # Special handling for jumps; recursive call for jump destination, then
        # continue at pc+4

        # Jumps should produce exactly one non-special edge; check that
        # assumption before we rely on it
        assert len(edges) == 1 and not edges[0].is_special()
        jump_loc = edges[0]
        jump_result = _get_iflow(program, graph, jump_loc.pc, constants, None,
                                 cache)

        # Update program_end_iflow, used constants, and control_deps
        program_end_iflow = _get_iflow_update_state(jump_result, iflow,
                                                    program_end_iflow,
                                                    used_constants,
                                                    control_deps)

        # Update constants and get information flow for return paths
        _, jump_return_iflow, _, constants, _ = jump_result

        # Compose current iflow with the flow for the jump's return paths
        iflow = iflow.seq(jump_return_iflow)

        # Set the next edges to the instruction after the jump returns
        edges = [ControlLoc(section.end + 4)]
    else:
        # Update the constants to include the last instruction
        constants.update_insn(last_insn, last_op_vals)

    # We're only returning constants that are the same in all RET branches
    common_constants = None

    for loc in edges:
        if isinstance(loc, Ecall) or isinstance(loc, ImemEnd):
            # Ecall or ImemEnd nodes are expected to be the only edge
            assert len(edges) == 1
            # Clear common constants; there are no return branches here
            common_constants = ConstantContext.empty()
            program_end_iflow.update(iflow)
        elif isinstance(loc, Ret):
            if loop_end_pc is not None:
                raise RuntimeError(
                    'RET before end of loop at PC {:#x} (loop end PC: '
                    '{:#x})'.format(section.end, loop_end_pc))
            # Ret nodes are expected to be the only edge
            assert len(edges) == 1
            # Since this is the only edge, common_constants must be unset
            common_constants = constants
            return_iflow.update(iflow)
        elif isinstance(loc, LoopStart) or isinstance(loc, LoopEnd):
            # We shouldn't hit a loop instances here; those cases (a loop
            # instruction or the end of a loop) are all handled earlier
            raise RuntimeError(
                'Unexpected loop edge (type {}) at PC {:#x}'.format(
                    type(loc), section.end))
        elif not loc.is_special():
            # Just a normal PC; recurse
            result = _get_iflow(program, graph, loc.pc, constants, loop_end_pc,
                                cache)

            # Update program_end_iflow, used constants, and control_deps
            program_end_iflow = _get_iflow_update_state(
                result, iflow, program_end_iflow, used_constants, control_deps)

            # Get information flow for return paths and new constants
            _, rec_return_iflow, _, rec_constants, _ = result

            # Take values on which existing and recursive constants agree
            if common_constants is None:
                common_constants = rec_constants
            else:
                common_constants.intersect(rec_constants)

            #  Update return_iflow with the current iflow composed with return
            #  paths
            return_iflow.update(iflow.seq(rec_return_iflow))
        else:
            raise RuntimeError(
                'Unexpected next control location type at PC {:#x}: {}'.format(
                    section.end, type(loc)))

    # There should be at least one edge, and all edges should set
    # common_constants to some non-None value
    assert common_constants is not None

    # Update used_constants to include any constant dependencies of
    # common_constants, since common_constants will be cached
    used_constants.update(
        return_iflow.sources_for_any(common_constants.values.keys()))

    # Strip special register x0 from both sources and sinks of graphs returned.
    return_iflow.remove_source('x0')
    return_iflow.remove_sink('x0')
    program_end_iflow.remove_source('x0')
    program_end_iflow.remove_sink('x0')
    control_deps.pop('x0', None)

    # Update the cache and return
    out = (used_constants, return_iflow, program_end_iflow, common_constants,
           control_deps)
    _get_iflow_cache_update(start_pc, start_constants, out, cache)
    return out


def check_acyclic(graph: ControlGraph) -> None:
    '''Checks for (non LOOP/LOOPI) cycles in control-flow graph.

    If there are such cycles, we need to raise an error and not proceed; the
    control-flow traversal would infinite-loop.
    '''
    cycles = graph.get_cycles(graph.start)
    if cycles:
        msg = [
            'One or more cycles found in control-flow graph at the following PCs:'
        ]
        for pc, links in cycles.items():
            msg.append('{:#x} <-> {}'.format(
                pc, ','.join(['{:#x}'.format(link) for link in links])))
        msg.append('Analyzing cyclic control flow outside of LOOP/LOOPI '
                   'instructions is not currently supported.')
        raise ValueError('\n'.join(msg))
    return


def get_subroutine_iflow(program: OTBNProgram, graph: ControlGraph,
                         subroutine_name: str) -> SubroutineIFlow:
    '''Gets the information-flow graphs for the subroutine.

    Returns three items:
    1. The combined information flow for control paths that return from the
       subroutine to its caller (None if there are no such paths)
    2. The combined information flow for control paths ending in the end of the
       program (e.g. ECALL or the end of IMEM) (None if there are no such
       paths)
    3. The information-flow nodes whose values at the start of the subroutine
       influence its control flow.
    '''
    check_acyclic(graph)
    start_pc = program.get_pc_at_symbol(subroutine_name)
    _, ret_iflow, end_iflow, _, control_deps = _get_iflow(
        program, graph, start_pc, ConstantContext.empty(), None, IFlowCache())
    if not (ret_iflow.exists or end_iflow.exists):
        raise ValueError('Could not find any complete control-flow paths when '
                         'analyzing subroutine.')
    return ret_iflow, end_iflow, control_deps


def get_program_iflow(program: OTBNProgram,
                      graph: ControlGraph) -> ProgramIFlow:
    '''Gets the information-flow graph for the whole program.

    Returns two items:
    1. The combined information flow for control paths ending in the end of the
       program (e.g. ECALL or the end of IMEM)
    2. The information-flow nodes whose values at the start of the subroutine
       influence its control flow.
    '''
    check_acyclic(graph)
    _, ret_iflow, end_iflow, _, control_deps = _get_iflow(
        program, graph, program.min_pc(), ConstantContext.empty(), None,
        IFlowCache())
    if ret_iflow.exists:
        # No paths from imem_start should end in RET
        raise ValueError('Unexpected information flow for paths ending in RET '
                         'when analyzing whole program.')
    assert end_iflow.exists
    return end_iflow, control_deps


def stringify_control_deps(program: OTBNProgram,
                           control_deps: Dict[str, Set[int]]) -> List[str]:
    '''Compute string representations of nodes that influence control flow.

    Returns a list of strings, each representing one node that influences
    control flow according to the input dictionary. The input is a dictionary
    whose keys are information-flow nodes and whose values are the PCs at which
    these nodes influence the control flow of the program.

    Example:
      input: {'x2' : {0x44, 0x55}, 'x3': {0x44}}
      output: ['x2 (via beq at 0x44, bne at 0x55)', 'x3 (via beq at 0x44)']
    '''
    out = []
    for node, pcs in control_deps.items():
        pc_strings = []
        if len(pcs) == 0:
            continue
        for pc in pcs:
            insn = program.get_insn(pc)
            pc_strings.append('{} at PC {:#x}'.format(insn.mnemonic, pc))
        out.append('{} (via {})'.format(node, ', '.join(pc_strings)))
    return out
