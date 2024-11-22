# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from typing import Dict, Optional, List
from .clocks import Clocks


class ResetItem:
    '''Individual resets'''
    def __init__(self, hier: Dict[str, str], raw: Dict[str, object], clocks: Clocks):
        if not raw['name']:
            raise ValueError('Reset has no name')

        self.name = raw['name']
        self.gen = raw.get('gen', True)
        self.rst_type = raw.get('type', 'top')

        self.path = ""
        if self.rst_type == 'top':
            self.path = f"{hier['top']}rst_{self.name}_n"
            self.lpg_path = f"{hier['lpg']}{self.name}"
        elif self.rst_type == 'ext':
            self.path = f"{hier['ext']}{self.name}"

        self.shadow_path = ""
        if self.rst_type == 'top':
            self.shadow_path = f"{hier['top']}rst_{self.name}_shadowed_n"
            self.shadow_lpg_path = f"{hier['lpg']}{self.name}_shadowed"

        # to be constructed later
        self.domains = []
        self.shadowed = False

        self.parent = raw.get('parent', "")

        # This can be a source clock or a derived source
        if self.rst_type != 'ext':
            self.clock = clocks.get_clock_by_name(raw['clk'])
        else:
            self.clock = None

        self.sw = bool(raw.get('sw', 0))

    def _asdict(self) -> Dict[str, object]:
        ret = {
            'name': self.name,
            'gen': self.gen,
            'type': self.rst_type,
            'domains': self.domains,
            'shadowed': self.shadowed,
            'sw': self.sw,
            'path': self.path
        }

        if self.parent:
            ret['parent'] = self.parent

        if self.clock:
            ret['clock'] = self.clock.name

        return ret


class Resets:
    '''Resets for the chip'''
    def __init__(self, raw: Dict[str, object], clocks: Clocks):
        self.hier_paths = {}
        assert isinstance(raw['hier_paths'], dict)
        for rst_src, path in raw['hier_paths'].items():
            self.hier_paths[str(rst_src)] = str(path)

        assert isinstance(raw['nodes'], list)

        self.nodes = {}
        for node in raw['nodes']:
            assert isinstance(node, dict)
            reset = ResetItem(self.hier_paths, node, clocks)
            self.nodes[reset.name] = reset

    def _asdict(self) -> Dict[str, object]:
        ret = {
            'hier_paths': self.hier_paths,
            'nodes': list(self.nodes.values())
        }

        return ret

    def get_reset_by_name(self, name: str) -> ResetItem:

        ret = self.nodes.get(name, None)
        if ret:
            return ret
        else:
            raise ValueError(f'{name} is not a defined reset')

    def mark_reset_shadowed(self, name: str):
        '''Mark particular reset as requiring shadow'''

        reset = self.get_reset_by_name(name)
        reset.shadowed = True

    def get_reset_domains(self, name: str):
        '''Get available domains for a reset'''

        return self.get_reset_by_name(name).domains

    def get_clocks(self) -> list:
        '''Get associated clocks'''

        clocks = {}
        for reset in self.nodes.values():
            if reset.rst_type != 'ext':
                clocks[reset.clock.name] = 1

        return list(clocks)

    def get_generated_resets(self) -> list:
        '''Get generated resets and return reset object
        '''
        return [reset
                for reset in self.nodes.values()
                if reset.gen]

    def get_top_resets(self) -> list:
        '''Get resets pushed to the top level'''

        return [reset
                for reset in self.nodes.values()
                if reset.rst_type == 'top']

    def get_sw_resets(self) -> list:
        '''Get software controlled resets'''

        return [reset.name
                for reset in self.nodes.values()
                if reset.sw]

    def get_path(self, name: str, domain: Optional[str], shadow = False) -> str:
        '''Get path to reset'''

        reset = self.get_reset_by_name(name)
        if reset.rst_type == 'int':
            raise ValueError(f'Reset {name} is not a reset exported from rstmgr')

        if reset.rst_type == 'ext':
            return reset.path

        if shadow:
            path = reset.shadow_path
        else:
            path = reset.path

        if domain:
            path += f'[rstmgr_pkg::Domain{domain}Sel]'

        return path

    def get_lpg_path(self, name: str, domain: Optional[str], shadow = False) -> str:
        '''Get path to lpg indication signals'''

        reset = self.get_reset_by_name(name)
        if reset.rst_type == 'int':
            raise ValueError(f'Reset {name} is not a reset exported from rstmgr')

        if reset.rst_type == 'ext':
            raise ValueError(f'External reset {name} cannot be associated with an LPG')

        if shadow:
            path = reset.shadow_lpg_path
        else:
            path = reset.lpg_path

        if domain:
            path += f'[rstmgr_pkg::Domain{domain}Sel]'

        return path

    def get_unused_resets(self, domains: list) -> Dict[str, str]:
        '''Get unused resets'''

        top_resets = [reset
                      for reset in self.nodes.values()
                      if reset.rst_type == 'top']

        ret = {}
        for reset in top_resets:
            for dom in domains:
                if dom not in reset.domains:
                    ret[f'rst_{reset.name}_n[{domains.index(dom)}]'] = \
                        f'{reset.path}[rstmgr_pkg::Domain{dom}Sel]'

                    if reset.shadowed:
                        ret[f'rst_{reset.name}_shadowed_n[{domains.index(dom)}]'] = \
                            f'{reset.shadow_path}[rstmgr_pkg::Domain{dom}Sel]'

        return ret

    def add_reset_domain(self, name: str, domain: str):
        '''Mark particular reset as requiring shadow'''

        reset = self.get_reset_by_name(name)

        # Other reset types of hardwired domains
        if reset.rst_type == 'top':
            if domain not in reset.domains:
                reset.domains.append(domain)

    def has_shadowed_reset(self) -> bool:
        '''Do any generated resets have a shadow version?'''

        for reset in self.nodes.values():
            if reset.shadowed:
                return True

        return False


class UnmanagedReset:
    '''An unmanaged reset (input to the top-level).'''

    def __init__(self, raw: Dict[str, object]):
        if 'name' not in raw:
            raise ValueError('Missing field "name" for unmanaged reset')
        self.name = str(raw['name'])
        self.signal_name = f'rst_{self.name}_i'
        self.rst_en_signal_name = f'rst_en_{self.name}_i'

    def _asdict(self) -> Dict[str, object]:
        return {
            'name': self.name,
            'signal_name': self.signal_name,
            'rst_en_signal_name': self.rst_en_signal_name
        }


class UnmanagedResets:
    '''Unmanaged reset connections for the chip.'''

    def __init__(self, raw: List[object]):
        self.resets = {reset['name']: UnmanagedReset(reset) for reset in raw}

    def _asdict(self) -> Dict[str, object]:
        return self.resets

    def get(self, name: str) -> object:
        try:
            return self.resets[name]
        except KeyError:
            raise ValueError(f"No reset defined with name {name}") from None

    def __contains__(self, k: str) -> bool:
        return k in self.resets
