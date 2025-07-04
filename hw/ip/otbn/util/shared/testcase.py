# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from dataclasses import dataclass
import hjson  # type: ignore
import re
from typing import Any, Dict


def _get_symbol(symbols: Dict[str, int], label: str) -> int:
    value = symbols.get(label)
    if value is None:
        raise KeyError(f'Symbol {label} does not exist in the elf')
    return value


@dataclass
class StateExpectations:
    dmem: Dict[str, bytes]  # dmem variable label -> data bytes
    regs: Dict[str, int]  # register label (e.g. x1) -> value

    @staticmethod
    def _dmem_from_dict(dmem_dict: Dict[str, Any],
                        symbols: Dict[str, int]) -> Dict[str, bytes]:
        dmem: Dict[str, bytes] = {}
        for label, value in dmem_dict.items():
            assert isinstance(value, str), "Dmem value must be a label or a hex string."
            value = value.strip()
            if _is_numeric_str(value):
                value = value.removeprefix("0x")
                data_bytes = bytes.fromhex(value)[::-1]  # big-endian -> little-endian
            else:
                value = _get_symbol(symbols, value)
                data_bytes = value.to_bytes(4, 'little')
            dmem[label] = data_bytes
        return dmem

    @staticmethod
    def _regs_from_dict(regs_dict: Dict[str, Any],
                        symbols: Dict[str, int]) -> Dict[str, int]:
        regs: Dict[str, int] = {}
        for label, value in regs_dict.items():
            if isinstance(value, int):
                regs[label] = value
            elif isinstance(value, str):
                value = value.strip()
                if _is_numeric_str(value):
                    regs[label] = int(value, 0)
                else:
                    regs[label] = _get_symbol(symbols, value)
            else:
                raise ValueError(f"Unexpected type for register value: {type(value)}")
        return regs

    @staticmethod
    def _from_dict(data: Dict[str, Any],
                   symbols: Dict[str, int]) -> 'StateExpectations':
        unknown_keys = set(data.keys()) - {'dmem', 'regs'}
        if len(unknown_keys):
            raise ValueError(f'Got unknown keys in testcase input/output: {unknown_keys}')

        dmem_dict = data.get('dmem', {})
        regs_dict = data.get('regs', {})
        return StateExpectations(
            dmem=StateExpectations._dmem_from_dict(dmem_dict, symbols),
            regs=StateExpectations._regs_from_dict(regs_dict, symbols)
        )


@dataclass
class OtbnTestCase:
    entrypoint: int
    input: StateExpectations
    output: StateExpectations

    @staticmethod
    def from_hjson(hjson_str: str,
                   symbols: Dict[str, int]) -> 'OtbnTestCase':
        """
        Parse a testcase HJSON string into a OtbnTestCase object.

        The HJSON schema is defined as follows:
        ```
            {
                entrypoint: str = "0"  // Address or symbol of entrypoint
                input: StateExpectations
                output: StateExpectations
            }
        ```

        The StateExpectations schema is defined as follows:
        ```
            {
                dmem: {
                    // Value is hex string (e.g. "0xdeadbeef") or symbol (e.g. "symbol").
                    //
                    // The variable length is inferred from the value's length or
                    // is 4 bytes if the value is a symbol.
                    <label>: <value>
                },
                regs: {
                    // Value is int, hex string (e.g. "0xdeadbeef"), or symbol (e.g. "symbol").
                    <reg_name>: <value>
                }
            }
        ```

        Args:
            hjson_str: The HJSON string to parse.
            symbols: A dict from symbol name (str) to value (int). This should contain
                     all symbols from the program being tested.

        Returns:
            A OtbnTestCase object representing the parsed testcase.
        """
        data: Dict[str, Any] = hjson.loads(hjson_str)

        unknown_keys = set(data.keys()) - {'entrypoint', 'input', 'output'}
        if len(unknown_keys):
            raise ValueError(f'Got unknown keys in testcase: {unknown_keys}')

        entrypoint = data.get('entrypoint', 0)
        if isinstance(entrypoint, int):
            entrypoint_addr = entrypoint
        elif _is_numeric_str(entrypoint):
            entrypoint_addr = int(entrypoint, 0)
        else:
            entrypoint_addr = _get_symbol(symbols, entrypoint)

        input_data = data.get('input', {})
        output_data = data.get('output', {})

        return OtbnTestCase(
            entrypoint=entrypoint_addr,
            input=StateExpectations._from_dict(input_data, symbols),
            output=StateExpectations._from_dict(output_data, symbols),
        )


def _is_numeric_str(value: str) -> bool:
    return bool(re.match(r'(0x)?[0-9a-fA-F\s]+$', value))
