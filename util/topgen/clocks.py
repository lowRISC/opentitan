# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from typing import Dict, List, NamedTuple, Tuple

from .lib import Name


def _yn_to_bool(yn: object) -> bool:
    yn_str = str(yn)
    if yn_str.lower() == 'yes':
        return True
    if yn_str.lower() == 'no':
        return False
    raise ValueError('Unknown yes/no value: {!r}.'.format(yn))


def _bool_to_yn(val: bool) -> str:
    return 'yes' if val else 'no'


def _to_int(val: object) -> int:
    if isinstance(val, int):
        return val
    return int(str(val))


def _check_choices(val: str, what: str, choices: List[str]) -> str:
    if val in choices:
        return val
    raise ValueError(
        f'{what} is {val!r}, which is none of the expected values: {choices}.')


class UnmanagedClock:
    '''An unmanaged clock (input to the top-level).'''

    def __init__(self, raw: Dict[str, object]):
        self.name = str(raw['name'])
        self.signal_name = f'clk_{self.name}_i'
        self.cg_en_signal = f'cg_en_{self.name}_i'

    def _asdict(self) -> Dict[str, object]:
        return {
            'name': self.name,
            'signal_name': self.signal_name,
            'cg_en_signal': self.cg_en_signal
        }


class SourceClock:
    '''A clock source (input to the top-level).'''

    def __init__(self, raw: Dict[str, object]):
        self.name = str(raw['name'])
        self.aon = _yn_to_bool(raw['aon'])
        self.freq = _to_int(raw['freq'])
        self.ref = raw.get('ref', False)

    def _asdict(self) -> Dict[str, object]:
        return {
            'name': self.name,
            'aon': _bool_to_yn(self.aon),
            'freq': str(self.freq),
            'ref': self.ref
        }


class DerivedSourceClock(SourceClock):
    '''A derived source clock (divided down from some other clock).'''

    def __init__(self, raw: Dict[str, object], sources: Dict[str,
                                                             SourceClock]):
        super().__init__(raw)
        self.div = _to_int(raw['div'])
        self.src = sources[str(raw['src'])]

    def _asdict(self) -> Dict[str, object]:
        ret = super()._asdict()
        ret['div'] = str(self.div)
        ret['src'] = self.src.name
        return ret


class ClockSignal:
    '''A clock signal in the design.'''

    def __init__(self, name: str, src: SourceClock):
        self.name = name
        self.src = src
        self.endpoints: List[Tuple[str, str]] = []

    def add_endpoint(self, ep_name: str, ep_port: str) -> None:
        self.endpoints.append((ep_name, ep_port))


class Group:

    def __init__(self, raw: Dict[str, object], what: str):
        self.name = str(raw['name'])
        self.src = str(raw['src'])
        self.sw_cg = _check_choices(str(raw['sw_cg']), 'sw_cg for ' + what,
                                    ['yes', 'no', 'hint'])
        if self.src == 'yes' and self.sw_cg != 'no':
            raise ValueError(f'Clock group {self.name} has an invalid '
                             f'combination of src and sw_cg: {self.src} and '
                             f'{self.sw_cg}, respectively.')

        self.unique = _yn_to_bool(raw.get('unique', 'no'))
        if self.sw_cg == 'no' and self.unique:
            raise ValueError(f'Clock group {self.name} has an invalid '
                             f'combination with sw_cg of {self.sw_cg} and '
                             f'unique set.')

        self.clocks = {}  # type: Dict[str, ClockSignal]

    def add_clock(self, clk_name: str, src: SourceClock) -> ClockSignal:
        # Duplicates are ok, so long as they have the same source.
        sig = self.clocks.get(clk_name)
        if sig is not None:
            if sig.src is not src:
                raise ValueError(f'Cannot add clock {clk_name} to group '
                                 f'{self.name} with source {src.name}: the '
                                 f'clock is there already with source '
                                 f'{sig.src.name}.')
        else:
            sig = ClockSignal(clk_name, src)
            self.clocks[clk_name] = sig

        return sig

    def _asdict(self) -> Dict[str, object]:
        return {
            'name': self.name,
            'src': self.src,
            'sw_cg': self.sw_cg,
            'unique': _bool_to_yn(self.unique),
            'clocks':
            {name: sig.src.name
             for name, sig in self.clocks.items()}
        }


class TypedClocks(NamedTuple):
    # External clocks that are consumed only inside the clkmgr and are fed from
    # an external ast source.
    ast_clks: Dict[str, ClockSignal]

    # Clocks fed through clkmgr but not disturbed in any way. This maintains
    # the clocking structure consistency. This includes two groups of clocks:
    #
    #   - Clocks fed from the always-on source
    #   - Clocks fed to the powerup group
    ft_clks: Dict[str, ClockSignal]

    # Non-feedthrough clocks that have no software control. These clocks are
    # root-gated and the root-gated clock is then exposed directly in clocks_o.
    rg_clks: Dict[str, ClockSignal]

    # Non-feedthrough clocks that have direct software control. These are
    # root-gated, but (unlike rg_clks) then go through a second clock gate
    # which is controlled by software.
    sw_clks: Dict[str, ClockSignal]

    # Non-feedthrough clocks that have "hint" software control (with a feedback
    # mechanism to allow blocks to avoid being suspended when they are not
    # idle).
    hint_clks: Dict[str, ClockSignal]

    # A list of the of non-always-on clock sources that are exposed without
    # division, sorted by name. This doesn't include clock sources that are
    # only used to derive divided clocks (we might gate the divided clocks, but
    # don't bother gating the upstream source).
    rg_srcs: List[str]

    # A diction of the clock families.
    # The key for each is root clock, while the list contains all the clocks
    # of the family, inclusive of itself.
    # For example
    # 'io': ['io', 'io_div2', 'io_div4']
    parent_child_clks: Dict[str, List]

    def all_clocks(self) -> Dict[str, ClockSignal]:
        ret = {}
        ret.update(self.ft_clks)
        ret.update(self.hint_clks)
        ret.update(self.rg_clks)
        ret.update(self.sw_clks)
        return ret

    def hint_names(self) -> Dict[str, str]:
        '''Return a dictionary with hint names for the hint clocks

        These are used as enum items that name the clock hint signals. The
        insertion ordering in this dictionary is important because it gives the
        mapping from enum name to index.

        '''
        # A map from endpoint to the list of hint clocks that it uses.
        ep_to_hints = {}
        for sig in self.hint_clks.values():
            for ep, port_name in sig.endpoints:
                ep_to_hints.setdefault(ep, []).append(sig.name)

        # A map from hint clock name to the associated enumeration name which
        # will appear in hint_names_e in clkmgr_pkg.sv. Note that this is
        # ordered alphabetically by endpoint: the precise ordering shouldn't
        # matter, but it's probably nicer to keep endpoints' signals together.
        hint_names = {}
        for ep, clks in sorted(ep_to_hints.items()):
            for clk in sorted(clks):
                # Remove any "clk" prefix
                clk_name = Name.from_snake_case(clk).remove_part('clk')
                hint_name = Name(['hint']) + clk_name
                hint_names[clk] = hint_name.as_camel_case()

        return hint_names


class UnmanagedClocks:
    '''Unmanaged clock connections for the chip.'''

    def __init__(self, raw: List[object]):
        self.clks = {clk['name']: UnmanagedClock(clk) for clk in raw}

    def _asdict(self) -> Dict[str, object]:
        return self.clks

    def get_clock_by_signal_name(self, signal_name: str) -> UnmanagedClock:
        for clock in self.clks.values():
            if clock.signal_name == signal_name:
                return clock
        raise ValueError(f"No clock defined with signal name {signal_name}") from None


class Clocks:
    '''Clock connections for the chip.'''

    def __init__(self, raw: Dict[str, object]):
        self.hier_paths = {}
        assert isinstance(raw['hier_paths'], dict)
        for grp_src, path in raw['hier_paths'].items():
            self.hier_paths[str(grp_src)] = str(path)

        assert isinstance(raw['srcs'], list)
        self.srcs = {}
        for r in raw['srcs']:
            clk = SourceClock(r)
            self.srcs[clk.name] = clk

        self.derived_srcs = {}
        assert isinstance(raw['derived_srcs'], list)
        for r in raw['derived_srcs']:
            clk = DerivedSourceClock(r, self.srcs)
            self.derived_srcs[clk.name] = clk

        self.all_srcs = self.srcs.copy()
        self.all_srcs.update(self.derived_srcs)

        self.groups = {}
        assert isinstance(raw['groups'], list)
        for idx, raw_grp in enumerate(raw['groups']):
            assert isinstance(raw_grp, dict)
            grp = Group(raw_grp, f'clocks.groups[{idx}]')
            self.groups[grp.name] = grp

    def _asdict(self) -> Dict[str, object]:
        return {
            'hier_paths': self.hier_paths,
            'srcs': list(self.srcs.values()),
            'derived_srcs': list(self.derived_srcs.values()),
            'groups': list(self.groups.values())
        }

    def add_clock_to_group(self, grp: Group, clk_name: str,
                           src_name: str) -> ClockSignal:
        src = self.all_srcs.get(src_name)
        if src is None:
            raise ValueError(f'Cannot add clock {clk_name} to group '
                             f'{grp.name}: the given source name is '
                             f'{src_name}, which is unknown.')
        return grp.add_clock(clk_name, src)

    def get_clock_by_name(self, name: str) -> object:
        ret = self.all_srcs.get(name)
        if ret is None:
            raise ValueError(f'{name} is not a valid clock')
        return ret

    def reset_signals(self) -> List[str]:
        '''Return the list of clock reset signal names.

        These signals are inputs to the clock manager (from the reset
        manager).
        '''
        ret = []
        for src in self.srcs.values():
            ret.append(f'rst_{src.name}_ni')
        for src in self.derived_srcs.values():
            ret.append(f'rst_{src.name}_ni')
        return ret

    def typed_clocks(self) -> TypedClocks:
        '''Split the clocks by type.'''
        ast_clks = {}
        ft_clks = {}
        rg_clks = {}
        sw_clks = {}
        hint_clks = {}
        rg_srcs_set = set()
        parent_child_clks = {}

        for grp in self.groups.values():
            if grp.name == 'powerup':
                # All clocks in the "powerup" group are considered feed-throughs.
                ft_clks.update(grp.clocks)
                continue

            for clk, sig in grp.clocks.items():
                if grp.src == "ext":
                    ast_clks[clk] = sig
                    continue

                if sig.src.aon:
                    # Any always-on clock is a feedthrough
                    ft_clks[clk] = sig
                    continue

                rg_srcs_set.add(sig.src.name)

                if grp.sw_cg == 'no':
                    # A non-feedthrough clock with no software control
                    rg_clks[clk] = sig
                    continue

                if grp.sw_cg == 'yes':
                    # A non-feedthrough clock with direct software control
                    sw_clks[clk] = sig
                    continue

                # The only other valid value for the sw_cg field is "hint", which
                # means a non-feedthrough clock with "hint" software control.
                assert grp.sw_cg == 'hint'
                hint_clks[clk] = sig
                continue

        # Define a canonical ordering for rg_srcs.
        rg_srcs = list(sorted(rg_srcs_set))

        # Define a list for each "family" of clocks
        for name, clk in self.srcs.items():
            if not clk.aon:
                parent_child_clks[name] = [name]

        for name, clk in self.derived_srcs.items():
            parent_child_clks[clk.src.name].append(name)

        return TypedClocks(ast_clks=ast_clks,
                           ft_clks=ft_clks,
                           rg_clks=rg_clks,
                           sw_clks=sw_clks,
                           hint_clks=hint_clks,
                           rg_srcs=rg_srcs,
                           parent_child_clks=parent_child_clks)

    def make_clock_to_group(self) -> Dict[str, Group]:
        '''Return a map from clock name to the group containing the clock.'''
        c2g = {}
        for grp in self.groups.values():
            for clk_name in grp.clocks.keys():
                c2g[clk_name] = grp
        return c2g

    def all_derived_srcs(self) -> List[str]:
        '''Return a list of all the clocks used as the source for derived clocks'''

        srcs = []

        for derived in self.derived_srcs.values():
            if derived.src.name not in srcs:
                srcs.append(derived.src.name)

        return srcs
