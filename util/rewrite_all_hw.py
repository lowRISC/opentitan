#!/usr/bin/env python3
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from pathlib import Path
import subprocess

default_params = {
    'tops': ["hw/top_earlgrey"],
    'no_regs': False,
    'hjson': '<DEFAULT>',
    'keep_all_files': False,
}

ips = {
    "hw/ip/adc_ctrl": {},
    "hw/ip/aes": {},
    "hw/ip/aon_timer": {},
    "hw/ip/csrng": {},
    "hw/ip/edn": {},
    "hw/ip/entropy_src": {},
    "hw/ip/gpio": {},
    "hw/ip/hmac": {},
    "hw/ip/i2c": {},
    "hw/ip/keymgr": {},
    "hw/ip/kmac": {},
    "hw/ip/lc_ctrl": {},
    "hw/ip/otbn": {'keep_all_files': True},
    "hw/ip/otp_ctrl": {},
    "hw/ip/pattgen": {},
    "hw/ip/prim": {'no_regs': True, 'hjson': None},
    "hw/ip/pwm": {},
    "hw/ip/rom_ctrl": {},
    "hw/ip/rv_core_ibex": {},
    "hw/ip/rv_dm": {},
    "hw/ip/rv_timer": {},
    "hw/ip/spi_device": {},
    "hw/ip/spi_host": {},
    "hw/ip/sram_ctrl": {},
    "hw/ip/sysrst_ctrl": {},
    "hw/ip/tlul": {'no_regs': True, 'hjson': None},
    "hw/ip/uart": {},
    "hw/ip/usbdev": {},
    # top_earlgrey
    'hw/top_earlgrey/ip/ast': {},
    'hw/top_earlgrey/ip/sensor_ctrl': {},
    "hw/top_earlgrey/ip/xbar": {'no_regs': True, 'hjson': None},
    "hw/top_earlgrey/ip/xbar_main": {'no_regs': True, 'hjson': None},
    "hw/top_earlgrey/ip/xbar_peri": {'no_regs': True, 'hjson': None},
}

project_root = Path(__file__).parents[1].resolve()

for (ip_dir, params) in ips.items():
    ip_dir = Path(ip_dir)
    params = default_params | params
    options = []

    if params["no_regs"]:
        options.append("--no-regs")
    if params["hjson"] is not None:
        hjson = params["hjson"]
        if hjson == '<DEFAULT>':
            hjson = ip_dir / 'data' / '{}.hjson'.format(ip_dir.name)
        options.extend(["--hjson", hjson])
    for top in params["tops"]:
        options.extend(["--top", top])
    if params['keep_all_files']:
        options.append('--keep-all-files')
    subprocess.run(
        [project_root / "util" / "rewrite_hw.py", "-v", "-g", "--root", project_root] +
        options + [ip_dir],
        check=True,
    )
