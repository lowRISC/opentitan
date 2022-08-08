#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from copy import deepcopy
from typing import Dict, List, Optional, Set, Tuple

from .cache import Cache, CacheEntry
from .constants import ConstantContext, get_op_val_str
from .control_flow import ControlLoc, ControlGraph, Cycle, Ecall, ImemEnd, LoopStart, Ret
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
#   cycles:         Information-flow subgraphs for any control-flow cycles
#                   (indexed by cycle start index).
#   control deps:   a dictionary whose keys are the information-flow nodes
#                   whose values at the start PC influence the control flow of
#                   the program; the value is a set of PCs of control-flow
#                   instructions through which the node influences the control
#                   flow
IFlowResult = Tuple[Set[str], InformationFlowGraph, InformationFlowGraph,
                    Optional[ConstantContext], Dict[int, InformationFlowGraph],
                    Dict[str, Set[int]]]


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
        return constants.includes(self.key)


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
        constant_deps.update(iflow.sources_for_any(used_constants))

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
    used_constant_values = ConstantContext.empty()
    for name in used_constants:
        value = constants.get(name)
        assert value is not None
        used_constant_values.set(name, value)

    cache.add(pc, IFlowCacheEntry(used_constant_values, result))

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
        constants: ConstantContext, cycles: Dict[int, InformationFlowGraph],
        control_deps: Dict[str, Set[int]]) -> InformationFlowGraph:
    '''Update the internal state of _get_iflow after a recursive call.

    `iflow` is not modified.
    `program_end_iflow` is updated in-place.
    `used_constants` is updated in-place.
    `constants` is updated in-place.
    `cycles` is updated in-place.
    `control_deps` is updated in-place.

    The new information-flow graph for paths ending in a return to the caller
    (return_iflow) is composed with `iflow` and returned. The caller will
    likely need to adjust `iflow` using this value, but how varies by use case.
    '''
    rec_used_constants = rec_result[0]
    rec_return_iflow = rec_result[1]
    rec_end_iflow = rec_result[2]
    rec_constants = rec_result[3]
    rec_cycles = rec_result[4]
    rec_control_deps = rec_result[5]

    # Update the used constants and control-flow dependencies
    used_constants.update(iflow.sources_for_any(rec_used_constants))
    _update_control_deps(control_deps, iflow, rec_control_deps)

    # Update the cycles
    for pc, cycle_iflow in rec_cycles.items():
        cycles.setdefault(pc, InformationFlowGraph.nonexistent()).update(
            iflow.seq(cycle_iflow))

    # Update the constants to keep only those that are either unmodified in the
    # return-path information flow or returned by the recursive call.
    constants.removemany(rec_return_iflow.all_sinks())
    if rec_constants is not None:
        constants.values.update(rec_constants.values)

    # Update information flow results for paths where the program ends
    program_end_iflow.update(iflow.seq(rec_end_iflow))

    return iflow.seq(rec_return_iflow)


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

    constants = deepcopy(start_constants)

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

    # Cycle starts that are accessible from this PC.
    cycles: Dict[int, InformationFlowGraph] = {}

    # If this PC is the start of a cycle, then initialize the information flow
    # for the cycle with an empty graph (since doing nothing is a valid
    # traversal of the cycle).
    if start_pc in graph.get_cycle_starts():
        cycles[start_pc] = InformationFlowGraph.empty()

    section = graph.get_section(start_pc)
    edges = graph.get_edges(start_pc)

    # If we're crossing the loop end PC, we must do so at the end of the
    # section. In this case, we do not pass the end of the loop; we treat the
    # end of the loop like a RET instruction.
    if loop_end_pc is not None and loop_end_pc in section:
        assert loop_end_pc == section.end
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
    used_constants.update(
        last_insn_iflow.sources_for_any(last_insn_used_constants))

    # Update control_deps to include last instruction
    last_insn_control_deps = {
        node: {section.end}
        for node in _get_insn_control_deps(last_insn, last_op_vals)
    }
    _update_control_deps(control_deps, iflow, last_insn_control_deps)

    # Update information-flow to include last instruction
    iflow = iflow.seq(last_insn_iflow)

    if last_insn.mnemonic in ['loopi', 'loop']:
        # A loop instruction should result in exactly one edge of type
        # LoopStart; check that assumption before we rely on it
        assert len(edges) == 1 and isinstance(edges[0], LoopStart)
        body_loc = edges[0]

        # Try to get the number of loop iterations.
        iterations = _get_constant_loop_iterations(last_insn, last_op_vals,
                                                   constants)

        # Update the constants to include the loop instruction
        constants.update_insn(last_insn, last_op_vals)

        if iterations is not None:
            # If the number of iterations is constant, perform recursive calls
            # for each iteration
            for _ in range(iterations):
                body_result = _get_iflow(program, graph,
                                         body_loc.loop_start_pc, constants,
                                         body_loc.loop_end_pc, cache)

                iflow = _get_iflow_update_state(body_result, iflow,
                                                program_end_iflow,
                                                used_constants, constants,
                                                cycles, control_deps)

            # Set the next edges to the instruction after the loop ends
            edges = [ControlLoc(body_loc.loop_end_pc + 4)]

    elif last_insn.mnemonic == 'jal' and last_op_vals['grd'] == 1:
        # Special handling for jumps; recursive call for jump destination, then
        # continue at pc+4
        constants.update_insn(last_insn, last_op_vals)

        # Jumps should produce exactly one non-special edge; check that
        # assumption before we rely on it
        assert len(edges) == 1 and not edges[0].is_special()
        jump_loc = edges[0]
        jump_result = _get_iflow(program, graph, jump_loc.pc, constants, None,
                                 cache)
        iflow = _get_iflow_update_state(jump_result, iflow, program_end_iflow,
                                        used_constants, constants, cycles,
                                        control_deps)

        # Get information flow for return paths
        _, jump_return_iflow, _, _, _, _ = jump_result

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
            program_end_iflow.update(iflow)
        elif isinstance(loc, Ret):
            if loop_end_pc is not None and loop_end_pc != section.end:
                raise RuntimeError(
                    'RET before end of loop at PC {:#x} (loop end PC: '
                    '{:#x})'.format(section.end, loop_end_pc))
            # Ret nodes are expected to be the only edge
            assert len(edges) == 1
            # Since this is the only edge, common_constants must be unset
            common_constants = constants
            return_iflow.update(iflow)
        elif isinstance(loc, Cycle):
            # Add the flow from start PC to this cyclic PC to the existing
            # flow, if any.
            cycles.setdefault(loc.pc,
                              InformationFlowGraph.nonexistent()).update(iflow)
        elif isinstance(loc, LoopStart) or not loc.is_special():
            # Just a normal PC; recurse
            result = _get_iflow(program, graph, loc.pc, constants, loop_end_pc,
                                cache)

            # Defensively copy constants so they don't cross between branches
            local_constants = deepcopy(constants)
            rec_return_iflow = _get_iflow_update_state(result, iflow,
                                                       program_end_iflow,
                                                       used_constants,
                                                       local_constants, cycles,
                                                       control_deps)

            # If there were any return paths, take values on which existing and
            # recursive constants agree.
            if rec_return_iflow.exists:
                if common_constants is None:
                    common_constants = local_constants
                else:
                    common_constants = common_constants.intersect(local_constants)

            # Update return_iflow with the current iflow composed with return
            # paths
            return_iflow.update(rec_return_iflow)
        else:
            raise RuntimeError(
                'Unexpected next control location type at PC {:#x}: {}'.format(
                    section.end, type(loc)))

    # Update used_constants to include any constant dependencies of
    # common_constants, since common_constants will be cached
    if common_constants is not None:
        # If there is no return branch, we would expect common_constants to be
        # None.
        assert return_iflow.exists
        used_constants.update(
            return_iflow.sources_for_any(common_constants.values.keys()))

    # If this PC is the start of one of the cycles we're currently processing,
    # see if it can be finalized.
    if start_pc in cycles:
        cycle_iflow = cycles[start_pc]

        # Find which constants are "stable" (unmodified throughout all paths in
        # the cycle)
        stable_constants = ConstantContext.empty()
        for k, v in start_constants.values.items():
            if k not in cycle_iflow.all_sinks():
                stable_constants.set(k, v)

        # If any start constants were modified during the cycle; do a recursive
        # call with only the unmodified constants, and return that.
        if not stable_constants.includes(start_constants):
            return _get_iflow(program, graph, start_pc, stable_constants,
                              loop_end_pc, cache)

        # If all starting constants were stable, just loop() the information
        # flow graph for this cycle to get the combined flow for all paths that
        # cycle back to this point (including no cycling, i.e. the empty graph).
        cycle_iflow = cycle_iflow.loop()

        # The final information flow for all paths is the graph of any valid
        # traversals of the cycle, sequentially composed with the return or
        # end-program paths from here.
        return_iflow = cycle_iflow.seq(return_iflow)
        program_end_iflow = cycle_iflow.seq(program_end_iflow)
        for pc in cycles:
            if pc == start_pc:
                continue
            cycles[pc] = cycle_iflow.seq(cycles[pc])

        # Control-flow dependencies must also be updated to include the
        # dependencies stemming from any valid traversal of the cycle
        new_control_deps: Dict[str, Set[int]] = {}
        _update_control_deps(new_control_deps, cycle_iflow, control_deps)
        control_deps = new_control_deps

        # Remove this cycle from the cycles dict, since it is now resolved.
        del cycles[start_pc]

    # Strip special register x0 from both sources and sinks of graphs returned.
    return_iflow.remove_source('x0')
    return_iflow.remove_sink('x0')
    program_end_iflow.remove_source('x0')
    program_end_iflow.remove_sink('x0')
    control_deps.pop('x0', None)

    # Update the cache and return
    out = (used_constants, return_iflow, program_end_iflow, common_constants,
           cycles, control_deps)

    _get_iflow_cache_update(start_pc, start_constants, out, cache)
    return out


def get_subroutine_iflow(program: OTBNProgram, graph: ControlGraph,
        subroutine_name: str, start_constants: Dict[str,int]) -> SubroutineIFlow:
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
    if 'x0' in start_constants and start_constants['x0'] != 0:
        raise ValueError('The x0 register is always 0; cannot require '
                f'x0={start_constants["x0"]}')
    start_constants['x0'] = 0
    constants = ConstantContext(start_constants)
    start_pc = program.get_pc_at_symbol(subroutine_name)
    _, ret_iflow, end_iflow, _, cycles, control_deps = _get_iflow(
        program, graph, start_pc, constants, None, IFlowCache())
    if cycles:
        for pc in cycles:
            print(cycles[pc].pretty())
            print('---')
        raise RuntimeError('Unresolved cycles; start PCs: {}'.format(', '.join(
            ['{:#x}'.format(pc) for pc in cycles.keys()])))
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
    _, ret_iflow, end_iflow, _, cycles, control_deps = _get_iflow(
        program, graph, program.min_pc(), ConstantContext.empty(), None,
        IFlowCache())
    if cycles:
        raise RuntimeError('Unresolved cycles; start PCs: {}'.format(', '.join(
            ['{:#x}'.format(k) for k in cycles.keys()])))
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
