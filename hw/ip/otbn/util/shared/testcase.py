# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import hjson  # type: ignore
import re
from typing import Any, Dict


def _is_numeric_str(value: str) -> bool:
    return bool(re.match(r'(0x)?[0-9a-fA-F\s]+$', value))


def parse_testcase(hjson_str: str, symbols: Dict[str, int] = {}) -> Dict[str, Any]:
    '''Parse a testcase HJSON string.

    Schema:
    ```
        {
            entrypoint: str = "0" // Address or symbol of entrypoint
            input: {
                dmem: {
                    <label>: <value>
                },
                regs: {
                    <reg_name>: <value>
                }
            },
            output: {
                dmem: {
                    <label>: <value>
                },
                regs: {
                    <reg_name>: <value>
                }
            }
        }
    ```

    Values may be integers, symbol strings, or numeric strings.

    Args:
        hjson_str: The HJSON string to parse.
        symbols: A dict from symbol name (str) to value (int). This should contain
                all symbols from the program being tested.

    Returns:
        A dict representing the parsed testcase.
    '''
    data: Dict[str, Any] = hjson.loads(hjson_str)

    entrypoint = data.get('entrypoint', 0)
    if isinstance(entrypoint, int):
        pass
    elif _is_numeric_str(entrypoint):
        data['entrypoint'] = int(entrypoint, 0)
    else:
        data['entrypoint'] = symbols[entrypoint]

    for key in ['input', 'output']:
        data.setdefault(key, {})
        data[key].setdefault('dmem', {})
        data[key].setdefault('regs', {})

        for label, value in data[key]['dmem'].items():
            value = value.strip()
            if not _is_numeric_str(value):
                value = symbols[value]
                data[key]['dmem'][label] = value.to_bytes(4, 'little')
            else:
                value = value.removeprefix("0x")
                # big-endian int -> little-endian byte array
                data[key]['dmem'][label] = bytes.fromhex(value)[::-1]

        for label, value in data[key]['regs'].items():
            if isinstance(value, int):
                continue
            value = value.strip()
            if not _is_numeric_str(value):
                data[key]['regs'][label] = symbols[value]
            else:
                data[key]['regs'][label] = int(value, 0)

    return data
