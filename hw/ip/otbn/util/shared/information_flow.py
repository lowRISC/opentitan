# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from copy import deepcopy
from typing import Any, Dict, Iterable, List, Optional, Sequence, Set, Tuple

from serialize.parse_helpers import check_keys, check_list, check_str

from .operand import Operand, RegOperandType

FLAG_NAMES = ['c', 'm', 'l', 'z']
SPECIAL_REG_NAMES = ['mod', 'acc']
READONLY = ['x0']


class InformationFlowGraph:
    '''Represents an information flow graph.

    The graph is represented as a `flow` dictionary mapping each "sink" node to
    a set of "source" nodes. Nodes are represented as strings. All nodes which
    are modified at all in the information flow should be represented as sinks
    in the `flow` dictionary. If a node does not appear, that means that it is
    unmodified.

    Note that it is possible for a sink node to be mapped to an empty set; that
    means the sink is overwritten with a constant value, and information is not
    flowing to it from any nodes (including its own previous value).
    '''
    def __init__(self, flow: Dict[str, Set[str]], exists: bool = True):
        self.flow = flow

        # Should not be modified directly. See the nonexistent() method
        # documentation for details of what this flag means.
        self.exists = exists

    @staticmethod
    def empty() -> 'InformationFlowGraph':
        '''Represents the graph for a path in which nothing is modified.

        For instance, if a block of code could be executed or not depending on
        the processor state, then the path where the block is not executed
        would be an empty() graph. Then, one could use update() to get a graph
        representing the combination of the two possibilities.
        '''
        return InformationFlowGraph({})

    @staticmethod
    def nonexistent() -> 'InformationFlowGraph':
        '''Represents the graph for a nonexistent path.

        There is an important distinction between this and an "empty" graph. In
        particular, for any graph G, G.update(nonexistent) = G, which is not
        the case for a merely "empty" graph; since the update() method is
        combining all possible paths, an empty graph means we need to consider
        that all nodes might be unmodified, while a nonexistent graph has no
        possible paths and therefore no effect.

        A nonexistent graph can be thought of as "None", but handling it
        directly within the class reduces the need for None checks.

        For instance, imagine we want to represent the information flow for
        only paths of a program that end in RET. If no paths from the current
        point end in RET (because, for instance, all paths end the program with
        ECALL), then a nonexistent graph would represent the information flow.
        '''
        return InformationFlowGraph({}, False)

    def sources(self, sink: str) -> Set[str]:
        '''Returns all sources for the given sink.'''
        # if the sink does not appear, it is unmodified, meaning its only
        # source is itself
        return self.flow.get(sink, {sink})

    def sinks(self, source: str) -> Set[str]:
        '''Returns all sinks for the given source.'''
        out = set()
        for sink in self.flow:
            if source in self.flow[sink]:
                out.add(sink)
        if source not in self.flow:
            # Implicitly, the source is unmodified and depends on itself
            out.add(source)
        return out

    def all_sources(self) -> Set[str]:
        '''Returns all sources in the graph.'''
        out: Set[str] = set()
        return out.union(*self.flow.values())

    def all_sinks(self) -> Set[str]:
        '''Returns all sinks in the graph.'''
        return set(self.flow.keys())

    def sources_for_any(self, sinks: Iterable[str]) -> Set[str]:
        '''Returns all nodes that are a source for any of the given sinks.'''
        out: Set[str] = set()
        return out.union(*(self.sources(s) for s in sinks))

    def sinks_for_any(self, sinks: Iterable[str]) -> Set[str]:
        '''Returns all nodes that are a sink for any of the given sources.'''
        out: Set[str] = set()
        return out.union(*(self.sinks(s) for s in sinks))

    def remove_source(self, node: str) -> None:
        '''Removes the node from the graph anywhere it appears as a source.

        If the node is not a source in the graph, does nothing.
        '''
        for sources in self.flow.values():
            sources.discard(node)

    def remove_sink(self, node: str) -> None:
        '''Removes the node from the graph anywhere it appears as a sink.

        If the node is not a sink in the graph, does nothing.
        '''
        self.flow.pop(node, None)

    def update(self, other: 'InformationFlowGraph') -> None:
        '''Updates self to include the information flow from other.

        Every sink that appears in either or both graphs will, in the updated
        self, have sources formed from the union of its sources in both graphs.
        Sinks that appear in only one graph will have sources formed of the
        union of their sources in the graph in which they appear and themselves
        (because a sink not appearing in a graph implicitly means the value is
        unchanged).

        Important note: updating with an empty graph will not be a no-op. An
        empty graph implies everything remains unmodified, so combining an
        empty graph with something that *overwrites* a value (i.e. a graph with
        a sink whose sources do not include itself) will add the "value doesn't
        change" information flow (i.e. the sink will be added to its own
        sources).

        Does not modify other.
        '''
        if not other.exists:
            # If the other graph is nonexistent, then this is a no-op.
            return

        if not self.exists:
            # Updating a nonexistent graph with another graph should return the
            # other graph; since we need to modify self, we change this graph's
            # flow to match other's.
            self.flow = deepcopy(other.flow)
            self.exists = other.exists
            return

        for sink, sources in other.flow.items():
            if sink not in self.flow:
                # implicitly, a non-updated value depends only on itself (NOT
                # an empty set, which would indicate a value that is
                # overwritten with a constant)
                self.flow[sink] = {sink}
            self.flow[sink].update(sources)

        return

    def seq(self, other: 'InformationFlowGraph') -> 'InformationFlowGraph':
        '''Performs sequential composition of information flow graphs.

        Returns the information flow graph that results from self sequentially
        composed with other. For example, if these are the two graphs (b and c
        being the sinks of self and e and d being the sinks of other):

          self:        other:
            a,d -> b     b   -> e
            a,b -> c     f   -> d
                         b,c -> c

        ...then the result of this operation will be:

            a,d   -> e
            f     -> d
            a,b,d -> c

        Defensively copies all source sets for the new graph.
        '''
        if not self.exists or not other.exists:
            # If either this or the other graph is nonexistent, then the
            # sequence is nonexistent.
            return InformationFlowGraph.nonexistent()

        flow = {}
        for sink, sources in other.flow.items():
            new_sources = set()
            for source in sources:
                if source in self.flow:
                    new_sources.update(self.flow[source])
                else:
                    # source is not a sink in self's flow; assume it stays
                    # constant
                    new_sources.add(source)
            flow[sink] = new_sources

        for sink, sources in self.flow.items():
            if sink not in flow:
                # sink is not updated in other's flow
                flow[sink] = sources.copy()

        return InformationFlowGraph(flow)

    def __deepcopy__(self,
                     memo: Optional[Dict[int, Any]]) -> 'InformationFlowGraph':
        flow = deepcopy(self.flow, memo)
        return InformationFlowGraph(flow, self.exists)

    def loop(self, max_iterations: int = 1000) -> 'InformationFlowGraph':
        '''Returns graph representing all possible repetitions of seq() of this
        graph with itself.

        The graph will be the combination of all possible chainings of this
        graph with itself, including 0 chainings (i.e. an empty graph). The
        result will be equivalent to:

        g = InformationFlowGraph({})
        for _ in range(infinity):
            g.update(g.seq(g))

        It is important to ensure that the total number of nodes in the set is
        limited, otherwise the computation could infinite-loop; the computation
        stops when the update becomes a no-op (signalling that the graph has
        stabilized), which is only guaranteed to happen if the node set is
        finite. By default, an error will be produced after a certain maximum
        number of iterations, but the caller can override this by setting
        `max_iterations` to None.

        Returns a new graph; the input graph is unmodified.
        '''
        if not self.exists:
            # Looping a nonexistent graph results in a nonexistent graph.
            return InformationFlowGraph.nonexistent()

        graph = InformationFlowGraph.empty()
        ctr = 0
        while (max_iterations is None or ctr < max_iterations):
            old = deepcopy(graph)
            graph.update(graph.seq(self))
            if (old == graph):
                # Graph has stabilized; further iterations will not change it.
                return graph
            ctr += 1

        raise RuntimeError(
            'Maximum number of iterations ({}) exceeded when looping '
            'information-flow graph. Is the set of possible nodes larger '
            'than the maximum iterations?'.format(max_iterations))

    def clobbered(self) -> str:
        '''Return a human-readable description of clobbered registers and flags.

        For example:
        clobbered registers: x3 to x5, w2 to w10, acc
        clobbered flag groups: FG0
        '''
        if not self.exists:
            return 'Nonexistent information-flow graph (no possible paths).'

        def _combine_ranges(nums: List[int]) -> List[Tuple[int, int]]:
            '''Convert a list of numbers into a list of ranges.

            For example, [1, 3, 4, 5] would become [(1, 1), (3,5)].
            '''
            if len(nums) == 0:
                return []

            ranges = []
            start = nums[0]
            end = nums[0]
            for n in nums[1:]:
                if n == end + 1:
                    end = n
                else:
                    ranges.append((start, end))
                    start = n
                    end = n
            ranges.append((start, end))
            return ranges

        def _stringify_range(prefix: str, r: Tuple[int, int]) -> str:
            start, end = r
            if start == end:
                return f'{prefix}{start}'
            return f'{prefix}{start} to {prefix}{end}'

        # First transform the nodes into a list of special registers plus
        # registers that may get represented as a range, stored as numbers.
        special = []
        flag_groups = set()
        wregs = []
        xregs = []
        for sink in sorted(self.flow.keys()):
            if sink == 'dmem' or sink == 'x1':
                # Not real registers or flags, ignore
                continue
            elif sink.startswith('w') and sink[1:].isdigit():
                wregs.append(int(sink[1:]))
            elif sink.startswith('x') and sink[1:].isdigit():
                xregs.append(int(sink[1:]))
            elif sink.startswith('fg0'):
                flag_groups.add('FG0')
            elif sink.startswith('fg1'):
                flag_groups.add('FG1')
            else:
                special.append(sink)

        # Combine the ranges.
        w_ranges = _combine_ranges(sorted(wregs))
        x_ranges = _combine_ranges(sorted(xregs))

        # Stringify ranges
        regs = [_stringify_range('x', r) for r in x_ranges]
        regs += [_stringify_range('w', r) for r in w_ranges]
        regs += special
        regs_line = '* clobbered registers: ' + ', '.join(regs)
        flags_str = 'none' if len(flag_groups) == 0 else ', '.join(sorted(list(flag_groups)))
        flags_line = '* clobbered flag groups: ' + flags_str
        return regs_line + '\n' + flags_line

    def pretty(self, indent: int = 0) -> str:
        '''Return a human-readable representation of the graph.'''
        if not self.exists:
            return 'Nonexistent information-flow graph (no possible paths).'

        prefix = ' ' * indent
        flow_strings = {
            sink: ','.join(sorted(sources))
            for sink, sources in self.flow.items()
        }
        max_source_chars = max([len(s) for s in flow_strings.values()],
                               default=0)
        lines = []
        for sink in sorted(self.flow.keys()):
            sources_str = flow_strings[sink]
            padding = ' ' * (max_source_chars - len(sources_str))
            lines.append('{}{}{} -> {}'.format(prefix, sources_str, padding,
                                               sink))
        return '\n'.join(lines)

    def __eq__(self, other: object) -> bool:
        '''Compare two information flow graphs for equality.

        Two graphs are considered equal iff the underlying flow dictionaries
        are equal.
        '''
        if not isinstance(other, InformationFlowGraph):
            return False
        return self.flow == other.flow


class InsnInformationFlowNode:
    '''Represents an information flow node whose value may depend on operands.
    '''
    def required_constants(self, op_vals: Dict[str, int]) -> Set[str]:
        '''Returns the names of regs that must be constant for `evaluate()`.

        For instance, for an indirect reference of a WDR via a GPR, the GPR's
        value must be constant for the node to be evaluated. Subclasses that
        require constants override this method.
        '''
        return set()

    def evaluate(self, op_vals: Dict[str, int],
                 constant_regs: Dict[str, int]) -> str:
        '''Determines information flow graph for the instruction.

        Evaluates the information-flow node according to the given operand
        values. The `constant_regs` dictionary is only used to access values in
        `self.required_constants()`; changes to other values will have no
        effect.
        '''
        raise NotImplementedError()


class InsnRegOperandNode(InsnInformationFlowNode):
    '''Represents a specific register operand for an instruction.'''
    def __init__(self, op: Operand):
        if not isinstance(op.op_type, RegOperandType):
            raise ValueError(
                'Attempt to construct a register-operand information flow '
                'node from a non-register operand {} of type {}'.format(
                    op.name, op.op_type))
        self.op = op
        self.is_wide = op.op_type.reg_type == 'wdr'

    def evaluate(self, op_vals: Dict[str, int],
                 constant_regs: Dict[str, int]) -> str:
        if self.op.name not in op_vals:
            raise ValueError(
                'Operand {} not found in provided operand values: {}'.format(
                    self.op.name, op_vals.keys()))
        return self.op.op_type.op_val_to_str(op_vals[self.op.name], None)


def _eval_indirect_wdr(gpr: str, constant_regs: Dict[str, int]) -> str:
    if gpr not in constant_regs:
        raise RuntimeError(
            'Cannot analyze information flow; cannot determine which '
            'WDR is referenced by non-constant GPR {} (constant regs '
            'are: {})'.format(gpr, constant_regs.keys()))
    wdr_idx = constant_regs[gpr]
    return 'w{}'.format(wdr_idx)


class InsnIndirectWDRNode(InsnInformationFlowNode):
    '''Represents an indirect reference to a WDR via a GPR.'''
    def __init__(self, op: Operand):
        if not isinstance(op.op_type, RegOperandType):
            raise ValueError(
                'Attempt to construct an indirect-WDR operand information '
                'flow node from a non-register operand {} of type {}'.format(
                    op.name, op.op_type))
        if not op.op_type.reg_type == 'gpr':
            raise ValueError(
                'Attempt to construct an indirect-WDR operand information '
                'flow node from a non-GPR register operand {} of type {}'.
                format(op.name, op.op_type.reg_type))
        self.op = op

    def _get_gpr_name(self, op_vals: Dict[str, int]) -> str:
        if self.op.name not in op_vals:
            raise ValueError(
                'Operand {} not found in provided operand values: {}'.format(
                    self.op.name, op_vals.keys()))
        return self.op.op_type.op_val_to_str(op_vals[self.op.name], None)

    def required_constants(self, op_vals: Dict[str, int]) -> Set[str]:
        return {self._get_gpr_name(op_vals)}

    def evaluate(self, op_vals: Dict[str, int],
                 constant_regs: Dict[str, int]) -> str:
        gpr = self._get_gpr_name(op_vals)
        return _eval_indirect_wdr(gpr, constant_regs)


class InsnGroupFlagNode(InsnInformationFlowNode):
    '''Represents a flag node whose group depends on the flag_group operand.'''
    def __init__(self, flag: str):
        flag = flag.lower()
        if flag not in FLAG_NAMES:
            raise ValueError(
                'Invalid flag name: "{}". Valid names are: {}'.format(
                    flag, FLAG_NAMES))
        self.flag = flag
        self.constant_dependent = False

    def evaluate(self, op_vals: Dict[str, int],
                 constant_regs: Dict[str, int]) -> str:
        if 'flag_group' not in op_vals:
            raise ValueError(
                'Operand flag_group not found in provided operand values: {}'.
                format(op_vals.keys()))
        return 'fg{}-{}'.format(op_vals['flag_group'], self.flag)


class InsnConstantNode(InsnInformationFlowNode):
    '''Represents instruction node whose value does not depend on operands.'''
    def __init__(self, node: str):
        self.node = node
        self.constant_dependent = False

    def evaluate(self, op_vals: Dict[str, int],
                 constant_regs: Dict[str, int]) -> str:
        return self.node


def _parse_iflow_nodes(
        node: str, what: str,
        operands: List[Operand]) -> List[InsnInformationFlowNode]:
    '''Parses information flow node(s) from the instruction description.

    Valid information flow nodes are one of the following:
    - the name of a *register* operand from the operands list
    - "wref-<reg operand name>" for instructions where a WDR is indirectly
      accessed via a GPR; in this case <reg operand name> is the GPR and must
      be in the operands list
    - one of the special strings "dmem", "acc", or "mod"
    - a flag (represented as "<flag group>-<flag>", where <flag group> can
      be either "fg0", "fg1", or (if the instruction has a flag_group
      operand) simply "flags" to select the current flag group, and <flag>
      can be l, c, m, z, or "all".

    Raises a ValueError if the node does not have a valid format.
    '''
    node = node.lower()

    # Check if node is a register operand
    for op in operands:
        if node == op.name:
            if not isinstance(op.op_type, RegOperandType):
                raise RuntimeError(
                    'Information-flow node {} matches operand name, but '
                    'operand type is not a register (type {}). Note that '
                    'immediate operands cannot be information-flow nodes.'.
                    format(node, type(op.op_type)))
            return [InsnRegOperandNode(op)]

    # Check if node is an indirect reference to a WDR through a GPR
    if node.startswith('wref-'):
        gpr = node[len('wref-'):]
        for op in operands:
            if gpr == op.name:
                if not (isinstance(op.op_type, RegOperandType) and
                        op.op_type.reg_type == 'gpr'):
                    raise RuntimeError(
                        'Operand {} in indirect reference {} is not a GPR '
                        '(type {}). Only GPRs can be indirect references.'.
                        format(gpr, node, type(op.op_type)))
                return [InsnIndirectWDRNode(op)]
        raise RuntimeError(
            'Could not find GPR operand corresponding to {} when decoding '
            'indirect reference {}. Operand names: {}'.format(
                gpr, node, ', '.join([op.name for op in operands])))

    # Check if node is a special string
    if node == 'dmem' or node in SPECIAL_REG_NAMES:
        return [InsnConstantNode(node)]

    # Try to interpret node as a flag or set of flags
    node_split = node.split('-')
    if len(node_split) != 2:
        raise ValueError('Cannot parse information flow node {} for {}'.format(
            node, what))
    flag_group_str, flag = node_split

    # Case where flag group depends on the flag_group operand
    if flag_group_str == 'flags':
        if flag == 'all':
            return [InsnGroupFlagNode(flag) for flag in FLAG_NAMES]
        return [InsnGroupFlagNode(flag)]
    elif flag_group_str == 'fg0' or flag_group_str == 'fg1':
        if flag == 'all':
            return [
                InsnConstantNode('{}-{}'.format(flag_group_str, flag))
                for flag in FLAG_NAMES
            ]
        return [InsnConstantNode('{}-{}'.format(flag_group_str, flag))]
    else:
        raise ValueError('Cannot parse information flow node {} for {}'.format(
            node, what))


class InsnInformationFlowTest:
    '''Wrapper class for tests for information-flow rules.'''
    def __init__(self, as_string: str, operand: str, value: int):
        self.as_string = as_string
        self.operand = operand
        self.value = value

    def check(self, op_vals: Dict[str, int]) -> bool:
        # Should be overridden by subclasses
        raise NotImplementedError()

    def __repr__(self) -> str:
        return 'InsnInformationFlowTest: {}'.format(self.as_string)


class EqTest(InsnInformationFlowTest):
    '''Tests that the operand is equal to the value.'''
    def check(self, op_vals: Dict[str, int]) -> bool:
        return op_vals[self.operand] == self.value


class NotEqTest(InsnInformationFlowTest):
    '''Tests that the operand is not equal to the value.'''
    def check(self, op_vals: Dict[str, int]) -> bool:
        return not (op_vals[self.operand] == self.value)


class GeqTest(InsnInformationFlowTest):
    '''Tests that the operand is greater than or equal to the value.'''
    def check(self, op_vals: Dict[str, int]) -> bool:
        return op_vals[self.operand] >= self.value


class LeqTest(InsnInformationFlowTest):
    '''Tests that the operand is less than or equal to the value.'''
    def check(self, op_vals: Dict[str, int]) -> bool:
        return op_vals[self.operand] <= self.value


class MultiTest(InsnInformationFlowTest):
    '''Combination of multiple tests.'''
    def __init__(self, tests: List[InsnInformationFlowTest]):
        self.tests = tests

    def check(self, op_vals: Dict[str, int]) -> bool:
        return all(t.check(op_vals) for t in self.tests)


def _parse_iflow_test(test_yml: object, what: str,
                      operands: List[Operand]) -> InsnInformationFlowTest:
    '''Parses an item in the "test" list of a YAML information-flow rule.

    Tests are expected to be strings of the form "<operand> <comparison>
    <value>", where:
      - <operand> is the name of one of the instruction's operands
      - <comparison> is "==", "!=", ">=", or "<="
      - <value> is an integer that is within the allowed range of values
        for this operand (for instance, for a flag group it would be 0 or 1,
        and for a register it would be between 0 and 31).

    Returns a function that takes operand values as input and returns true if
    the test passes.
    '''
    test = check_str(test_yml, what)
    test = test.lower()
    test_split = test.split(' ')
    if len(test_split) != 3:
        raise ValueError(
            'Invalid information flow test format (expected "<operand> '
            '<comparison> <value>"): got {} (for {})'.format(test, what))
    opname, comparison, value_str = test_split

    opnames = [op.name for op in operands]
    if opname not in opnames:
        raise ValueError(
            'Invalid information flow test format for {}: operand {} not '
            'found in operands list: {}'.format(what, opname, opnames))

    try:
        value = int(value_str, 0)
    except ValueError:
        raise ValueError(
            'Value {} in test {} for {} must be an integer.'.format(
                value_str, test, what))

    constructors = {
        '==': EqTest,
        '!=': NotEqTest,
        '>=': GeqTest,
        '<=': LeqTest,
    }
    constructor = constructors.get(comparison, None)
    if constructor is None:
        raise ValueError('Unrecognized comparison {} for {}'.format(
            comparison, what))
    return constructor(test, opname, value)


class InsnInformationFlowRule:
    '''A rule describing a single step of information flowing to one or more
       nodes from one or more nodes.'''
    def __init__(self, flows_to: Sequence[InsnInformationFlowNode],
                 flows_from: Sequence[InsnInformationFlowNode],
                 test: InsnInformationFlowTest):
        self.flows_to = flows_to
        self.flows_from = flows_from
        self.test = test

    def required_constants(self, op_vals: Dict[str, int]) -> Set[str]:
        '''Returns the names of regs that must be constant for `evaluate()`.'''
        out = set()
        for node in self.flows_to:
            out.update(node.required_constants(op_vals))
        for node in self.flows_from:
            out.update(node.required_constants(op_vals))
        return out

    def evaluate(self, op_vals: Dict[str, int],
                 constant_regs: Dict[str, int]) -> InformationFlowGraph:
        if not self.test.check(op_vals):
            # Rule is not triggered
            return InformationFlowGraph.nonexistent()
        sources = set()
        for node in self.flows_from:
            sources.add(node.evaluate(op_vals, constant_regs))
        flow = {}
        for node in self.flows_to:
            dest = node.evaluate(op_vals, constant_regs)
            if dest in READONLY:
                # No information will actually flow to this node, because it is
                # not writeable; skip.
                continue
            flow[dest] = sources.copy()
        return InformationFlowGraph(flow)

    @staticmethod
    def from_yaml(yml: object, what: str,
                  insn_operands: List[Operand]) -> 'InsnInformationFlowRule':
        rule = check_keys(yml, what, ['to', 'from'], ['test'])

        to_what = '"to" list for {}'.format(what)
        flows_to = []
        for node_yml in check_list(rule['to'], to_what):
            node_what = 'node {} in {}'.format(node_yml, to_what)
            nodes = _parse_iflow_nodes(check_str(node_yml, node_what),
                                       node_what, insn_operands)
            flows_to.extend(nodes)

        from_what = '"from" list for {}'.format(what)
        flows_from = []
        for node_yml in check_list(rule['from'], from_what):
            node_what = 'node {} in {}'.format(node_yml, from_what)
            nodes = _parse_iflow_nodes(check_str(node_yml, node_what),
                                       node_what, insn_operands)
            flows_from.extend(nodes)

        test_yml = rule.get('test', None)
        if test_yml is None:
            tests = []
        else:
            test_what = 'test field for {}'.format(what)
            tests = [
                _parse_iflow_test(t, test_what, insn_operands)
                for t in check_list(test_yml, test_what)
            ]
        return InsnInformationFlowRule(flows_to, flows_from, MultiTest(tests))


class InsnInformationFlow:
    '''Represents information flow for a single instruction.'''
    def __init__(self, rules: List[InsnInformationFlowRule]) -> None:
        self.rules = rules

    def required_constants(self, op_vals: Dict[str, int]) -> Set[str]:
        '''Returns the names of regs that must be constant for `evaluate()`.'''
        return {
            const
            for rule in self.rules
            for const in rule.required_constants(op_vals)
        }

    def evaluate(self, op_vals: Dict[str, int],
                 constant_regs: Dict[str, int]) -> InformationFlowGraph:
        graph = InformationFlowGraph.nonexistent()
        for rule in self.rules:
            rule_graph = rule.evaluate(op_vals, constant_regs)
            graph.update(rule_graph)

        return graph

    @staticmethod
    def from_yaml(yml: Optional[object], what: str,
                  insn_operands: List[Operand]) -> 'InsnInformationFlow':

        if yml is None:
            # Default behavior: all source registers flow to all destination
            # registers, no other information flow or special registers
            sources = [
                InsnRegOperandNode(op) for op in insn_operands if
                isinstance(op.op_type, RegOperandType) and op.op_type.is_src()
            ]
            dests = [
                InsnRegOperandNode(op) for op in insn_operands
                if isinstance(op.op_type, RegOperandType) and
                op.op_type.is_dest()
            ]
            return InsnInformationFlow(
                [InsnInformationFlowRule(dests, sources, MultiTest([]))])

        rule_list = check_list(yml, what)
        rules = []
        for idx, rule_yml in enumerate(rule_list):
            rule_what = 'rule at index {} for {}'.format(idx, what)
            rule = InsnInformationFlowRule.from_yaml(rule_yml, rule_what,
                                                     insn_operands)
            rules.append(rule)
        return InsnInformationFlow(rules)
