#!/usr/bin/env python3
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import argparse
from pathlib import Path
import subprocess
import os

all_tops = ["darjeeling", "earlgrey"]

all_ips = {
    "hw/ip/adc_ctrl": {},
    "hw/ip/aes": {},
    "hw/ip/aon_timer": {},
    "hw/ip/csrng": {},
    "hw/ip/dma": {},
    "hw/ip/edn": {},
    "hw/ip/entropy_src": {},
    "hw/ip/gpio": {},
    "hw/ip/hmac": {},
    "hw/ip/i2c": {},
    "hw/ip/keymgr": {},
    "hw/ip/keymgr_dpe": {},
    "hw/ip/kmac": {},
    "hw/ip/lc_ctrl": {},
    "hw/ip/otbn": {},
    "hw/ip/otp_ctrl": {},
    "hw/ip/mbx": {},
    "hw/ip/pattgen": {},
    "hw/ip/pwm": {},
    "hw/ip/rom_ctrl": {},
    "hw/ip/rv_core_ibex": {},
    "hw/ip/rv_dm": {},
    "hw/ip/rv_timer": {},
    "hw/ip/spi_device": {},
    "hw/ip/spi_host": {},
    "hw/ip/sram_ctrl": {},
    "hw/ip/sysrst_ctrl": {},
    "hw/ip/uart": {},
    "hw/ip/usbdev": {},
    # templates
    "hw/ip_templates/alert_handler": {"is_template": True, "tops": all_tops},
    "hw/ip_templates/clkmgr": {"is_template": True, "tops": all_tops},
    "hw/ip_templates/rstmgr": {"is_template": True, "tops": all_tops},
    "hw/ip_templates/pwrmgr": {"is_template": True, "tops": all_tops},
    "hw/ip_templates/rv_plic": {"is_template": True, "tops": all_tops},
    "hw/ip_templates/flash_ctrl": {"is_template": True, "tops": ["earlgrey"]},
    "hw/ip_templates/pinmux": {"is_template": True, "tops": all_tops},
    # top_earlgrey
    'hw/top_earlgrey/ip/ast': {},
    'hw/top_earlgrey/ip/sensor_ctrl': {},
    # top_darjeeling
    'hw/top_darjeeling/ip/ast': {},
    'hw/top_darjeeling/ip/sensor_ctrl': {},
    'hw/top_darjeeling/ip/soc_proxy': {},
}

project_root = Path(__file__).parents[1].resolve()


def find_all_files(project_root, search):
    # Use ripgrep to find all matching files
    res = subprocess.run(
        ["rg", "-l", search],
        capture_output = True,
        cwd = project_root,
    )
    # ripgrep returns 1 if there are no matches, 2 on error
    if res.returncode == 1:
        return []
    assert res.returncode == 0, "ripgrep command failed"

    return [Path(os.fsdecode(path)) for path in res.stdout.splitlines()]


def global_replace(project_root, search, replace, verbose):
    print(f'global replace "{search}" by "{replace}"')
    for path in find_all_files(project_root, search):
        path = project_root / path
        if verbose:
            print(f"Patching {path}")
        # Read, patch, write
        f = path.read_text()
        f = f.replace(search, replace)
        path.write_text(f)


def run_buildifier(project_root):
    subprocess.run(
        ["./bazelisk.sh", "run", "//quality:buildifier_fix"],
        check=True,
        cwd = project_root
    )


def run_topgen(project_root):
    for top in all_tops:
        subprocess.run(
            ["./util/topgen.py", "-t", f"hw/top_{top}/data/top_{top}.hjson"],
            check=True,
            cwd = project_root,
        )

    subprocess.run(
        ["make", "-C", "hw", "cmdgen"],
        check=False,
        cwd = project_root,
    )


def delete_rule(lines, rule_name, target_name, file_name):
    try:
        start_idx = 0
        while start_idx < len(lines):
            start_idx = lines.index(f'{rule_name}(\n', start_idx)
            if target_name is None or lines[start_idx + 1] == f'    {target_name},\n':  # noqa: E231
                break
            start_idx = start_idx + 1
    except ValueError:
        assert False, \
            f"did not find beginning of rule {rule_name} (target name {target_name}) in {file_name}"
    try:
        end_idx = lines.index(')\n', start_idx + 1)
    except ValueError:
        assert False, \
            f"did not find end of rule {rule_name} (target name {target_name}) in {file_name}"
    return lines[:start_idx] + lines[end_idx + 1:], start_idx, lines[start_idx:end_idx + 1]


def delete_all_rules(lines, rule_name, target_name, file_name):
    while True:
        try:
            lines, _, _ = delete_rule(lines, rule_name, target_name, file_name)
        except:
            break
    return lines

def step1(project_root, commit):
    new_files = []
    for (_ippath, info) in all_ips.items():
        ippath = project_root / Path(_ippath)
        ip_name = ippath.name
        is_template = info.get("is_template", False)

        def_file_path = ippath / ("defs.bzl.tpl" if is_template else "defs.bzl")
        # build_file_path = ippath / ("BUILD.tpl" if is_template else "BUILD")
        # If file does not exist, create one.
        if def_file_path.exists():
            print(f"File {def_file_path} already exists, will overwrite")
        new_files.append(def_file_path)
        if is_template:
            for top in info["tops"]:
                new_files.append(project_root / "hw" / f"top_{top}" / "ip_autogen" / ip_name / "defs.bzl")

        if is_template:
            hjson_bazel_target = f"//hw/top_${{topname}}/ip_autogen/{ip_name}:data/{ip_name}.hjson"
        else:
            hjson_bazel_target = f"//{_ippath}/data:{ip_name}.hjson"
        print(hjson_bazel_target)

        def_file = [
            '# Copyright lowRISC contributors (OpenTitan project).\n',
            '# Licensed under the Apache License, Version 2.0, see LICENSE for details.\n',
            '# SPDX-License-Identifier: Apache-2.0\n',
            'load("//rules/opentitan:hw.bzl", "opentitan_ip")\n',
            '\n',
            '{} = opentitan_ip(\n'.format(ip_name.upper()),
            '    name = "{}",\n'.format(ip_name),
            '    hjson = "{}",\n'.format(hjson_bazel_target),
            ')\n',
        ]

        def_file_path.write_text(''.join(def_file))

    # Run buildifier.
    run_buildifier(project_root)
    run_topgen(project_root)

    if commit:
        subprocess.run(
            ["git", "add"] + new_files,
            check = True,
            cwd = project_root,
        )
        subprocess.run(
            ["git", "commit", "-vas", "-m",
             "[bazel] Use new rules to describe IPs",  # noqa: E231
             "-m", "This commit was generated by ./util/rewrite_all_hw.py --step=1",
            ],
            check=True,
            cwd = project_root
        )


def step2(project_root, commit):
    for (_ippath, info) in all_ips.items():
        ippath = project_root / Path(_ippath)
        ip_name = ippath.name
        is_template = info.get("is_template", False)

        replacements = {}
        for typ in ["c", "rust"]:
            new_target = f"//hw/top:{ip_name}_{typ}_regs"
            if is_template:
                for top in info["tops"]:
                    # Some exceptions
                    if ip_name in ["rv_plic", "alert_handler"]:
                        replacements[f"//hw/top_{top}:{ip_name}_{typ}_regs"] = new_target
                    else:
                        replacements[f"//hw/top_{top}/ip_autogen/{ip_name}:{ip_name}_{typ}_regs"] = new_target
            else:
                replacements[f"//{_ippath}/data:{ip_name}_{typ}_regs"] = new_target

        for (old, new) in replacements.items():
            global_replace(project_root, old, new, verbose=False)

    # Run buildifier.
    run_buildifier(project_root)
    run_topgen(project_root)

    if commit:
        subprocess.run(
            ["git", "commit", "-vas", "-m",
             "Replace old header targets by new ones",  # noqa: E231
             "-m", "This commit was generated by ./util/rewrite_all_hw.py --step=2",
            ],
            check=True,
            cwd = project_root
        )


def step3(project_root, commit):
    files = list(set(
        find_all_files(project_root, "autogen_hjson_c_header\\(") +
        find_all_files(project_root, "autogen_hjson_rust_header\\(")
    ))
    print(files)
    for path in files:
        build_file_path = project_root / path
        build_file = build_file_path.read_text().splitlines(keepends=True)
        # Remove load to //rules:autogen.bzl
        build_file, _, _ = delete_rule(
            build_file,
            'load',
            '"//rules:autogen.bzl"',
            build_file_path
        )
        # Remove autogen_hjson_c_header and autogen_hjson_rust_header
        build_file = delete_all_rules(
            build_file,
            'autogen_hjson_c_header',
            None,
            build_file_path
        )
        build_file = delete_all_rules(
            build_file,
            'autogen_hjson_rust_header',
            None,
            build_file_path
        )
        build_file_path.write_text(''.join(build_file))

    # Run buildifier.
    run_buildifier(project_root)
    run_topgen(project_root)

    if commit:
        subprocess.run(
            ["git", "commit", "-vas", "-m",
             "Remove old header targets",  # noqa: E231
             "-m", "This commit was generated by ./util/rewrite_all_hw.py --step=3",
            ],
            check=True,
            cwd = project_root
        )


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('-v', '--verbose', action='store_true')
    parser.add_argument('--root', help='Path to the project root (if not specified, assume CWD)')
    parser.add_argument('--step', help='Which step to run')
    parser.add_argument('--commit', action="store_true", help='Which step to run')

    args = parser.parse_args()
    project_root = Path(args.root if args.root is not None else Path.cwd()).resolve()

    if args.step == "1":
        step1(project_root, args.commit)
    elif args.step == "2":
        step2(project_root, args.commit)
    elif args.step == "3":
        step3(project_root, args.commit)
    else:
        assert False, "unknown step"

main()