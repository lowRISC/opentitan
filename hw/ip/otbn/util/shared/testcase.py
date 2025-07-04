# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from dataclasses import dataclass
import hjson  # type: ignore
import re
from typing import Dict


def _get_symbol(symbols: Dict[str, int], label: str) -> int:
    try:
        return symbols[label]
    except KeyError:
        raise KeyError(f'Symbol {label} does not exist in the elf')


def _is_numeric_str(value: str) -> bool:
    return bool(re.match(r'(0x)?[0-9a-fA-F\s]+$', value))


def _get_str_keyed_dict(data: Dict[str, object], key: str) -> Dict[str, object]:
    res = data.get(key, {})
    assert isinstance(res, dict), f'Value of {key} must be a str-keyed dictionary'
    for label in res.keys():
        assert isinstance(label, str), f'{label} must be a string, got {type(label)}'
    return res


def _to_bytes_dict(input_dict: Dict[str, object],
                   symbols: Dict[str, int]) -> Dict[str, bytes]:
    dmem: Dict[str, bytes] = {}
    for label, value in input_dict.items():
        assert isinstance(value, str), f"{label} value must be an ELF symbol or a BE hex string"
        value = value.strip()
        if _is_numeric_str(value):
            value = re.sub(r'\s', '', value)
            if not value.startswith('0x'):
                # Raise an error to avoid confusion with decimal values.
                raise ValueError('Numeric hex string must start with "0x"')
            value = value.removeprefix("0x")
            value = '0' * (len(value) % 2) + value
            data_bytes = bytes.fromhex(value)[::-1]  # big-endian -> little-endian
        else:
            value_int = _get_symbol(symbols, value)
            data_bytes = value_int.to_bytes(4, 'little')
        dmem[label] = data_bytes
    return dmem


def _to_int_dict(input_dict: Dict[str, object],
                 symbols: Dict[str, int]) -> Dict[str, int]:
    bytes_dict = _to_bytes_dict(input_dict, symbols)
    return {k: int.from_bytes(v, 'little') for k, v in bytes_dict.items()}


@dataclass
class StateExpectations:
    dmem: Dict[str, bytes]  # dmem variable label -> little-endian data bytes
    regs: Dict[str, int]  # register label (e.g. x1) -> value

    @staticmethod
    def _from_dict(data: Dict[str, object],
                   symbols: Dict[str, int]) -> 'StateExpectations':
        unknown_keys = set(data.keys()) - {'dmem', 'regs'}
        if len(unknown_keys):
            raise ValueError(f'Got unknown keys in testcase input/output: {unknown_keys}')

        return StateExpectations(
            dmem=_to_bytes_dict(_get_str_keyed_dict(data, 'dmem'), symbols),
            regs=_to_int_dict(_get_str_keyed_dict(data, 'regs'), symbols)
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
                    // Label can be address hex (e.g. "0xbeef") or symbol in ELF (e.g. "symbol").
                    //
                    // Value can be hex string (e.g. "0xdeadbeef") or symbol in ELF (e.g. "symbol").
                    // The number of bytes to be written/compared is inferred from the hex string's
                    // length or is 4 bytes if the value is a symbol.
                    //
                    // In the case of a hex string, its length must be a multiple of 2.
                    <label>: <value>
                },
                regs: {
                    // Register name can be `x0-x31`, `w0-w31`, or those ext_regs like `ERR_BITS`.
                    //
                    // Value is hex string (e.g. "0xdeadbeef") or symbol in ELF (e.g. "symbol").
                    // The size of the register is determined by the hardware spec.
                    //
                    // In the case of a hex string, its length must be a multiple of 2.
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
        data: Dict[str, object] = hjson.loads(hjson_str)

        unknown_keys = set(data.keys()) - {'entrypoint', 'input', 'output'}
        if len(unknown_keys):
            raise ValueError(f'Got unknown keys in testcase: {unknown_keys}')

        entrypoint = data.get('entrypoint', 0)
        if isinstance(entrypoint, int):
            entrypoint_addr = entrypoint
        elif isinstance(entrypoint, str):
            if _is_numeric_str(entrypoint):
                entrypoint_addr = int(entrypoint, 0)
            else:
                entrypoint_addr = _get_symbol(symbols, entrypoint)
        else:
            raise ValueError(f'Entrypoint must be int or str, got {type(entrypoint)}')

        return OtbnTestCase(
            entrypoint=entrypoint_addr,
            input=StateExpectations._from_dict(_get_str_keyed_dict(data, 'input'), symbols),
            output=StateExpectations._from_dict(_get_str_keyed_dict(data, 'output'), symbols),
        )
