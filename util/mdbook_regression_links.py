#!/usr/bin/env python3
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
import argparse
from bs4 import BeautifulSoup
import datetime
import hjson
import os
from pathlib import Path
import requests
import tempfile

from ipgen import IpConfig, IpTemplate, IpBlockRenderer

# This script adds a small header to each IP README listed in IP_BLOCKS_HJSON_PATHS with the
# latest regression results. It also adds links to the taped-out regressions results of
# Earl Grey 1.0.0 if applicable. The text is placed inside the defined markers below.

START_MARKER = f"<!-- BEGIN AUTOGEN from util/{os.path.basename(__file__)} -->"
END_MARKER = "<!-- END AUTOGEN -->"

REPO_TOP = Path(__file__).resolve().parents[1]

# A list of all touched READMEs. This should probably be generated using topgen. The README is
# expected to be at ""../ip.hjson/../README.md" or README.md.tpl
#
# Templates will receive the regression results of Earl Grey. Note that this must be manually
# adapted if another top is generated.
top_name = "earlgrey"
IP_BLOCKS_HJSON_PATHS = [
    # IP blocks which use the earlgrey regression
    (REPO_TOP / "hw/ip/aes/data/aes.hjson", top_name),
    (REPO_TOP / "hw/ip/aon_timer/data/aon_timer.hjson", top_name),
    (REPO_TOP / "hw/ip/entropy_src/data/entropy_src.hjson", top_name),
    (REPO_TOP / "hw/ip/csrng/data/csrng.hjson", top_name),
    (REPO_TOP / "hw/ip/adc_ctrl/data/adc_ctrl.hjson", top_name),
    (REPO_TOP / "hw/ip/edn/data/edn.hjson", top_name),
    (REPO_TOP / "hw/ip/hmac/data/hmac.hjson", top_name),
    (REPO_TOP / "hw/ip/i2c/data/i2c.hjson", top_name),
    (REPO_TOP / "hw/ip/keymgr/data/keymgr.hjson", top_name),
    (REPO_TOP / "hw/ip/kmac/data/kmac.hjson", top_name),
    (REPO_TOP / "hw/ip/lc_ctrl/data/lc_ctrl.hjson", top_name),
    (REPO_TOP / "hw/ip/otbn/data/otbn.hjson", top_name),
    (REPO_TOP / "hw/ip/pattgen/data/pattgen.hjson", top_name),
    (REPO_TOP / "hw/ip/rom_ctrl/data/rom_ctrl.hjson", top_name),
    (REPO_TOP / "hw/ip/rv_dm/data/rv_dm.hjson", top_name),
    (REPO_TOP / "hw/ip/rv_timer/data/rv_timer.hjson", top_name),
    (REPO_TOP / "hw/ip/spi_host/data/spi_host.hjson", top_name),
    (REPO_TOP / "hw/ip/spi_device/data/spi_device.hjson", top_name),
    (REPO_TOP / "hw/ip/sram_ctrl/data/sram_ctrl.hjson", top_name),
    (REPO_TOP / "hw/ip/sysrst_ctrl/data/sysrst_ctrl.hjson", top_name),
    (REPO_TOP / "hw/ip/uart/data/uart.hjson", top_name),
    (REPO_TOP / "hw/ip/usbdev/data/usbdev.hjson", top_name),

    # IP blocks with a readme template
    (REPO_TOP / "hw/ip_templates/flash_ctrl/data/flash_ctrl.hjson.tpl", top_name),
    (REPO_TOP / "hw/ip_templates/gpio/data/gpio.hjson.tpl", top_name),
    # TODO: otp_ctrl template cannot be rendered
    # (REPO_TOP / "hw/ip_templates/otp_ctrl/data/otp_ctrl.hjson.tpl", top_name),
    (REPO_TOP / "hw/ip_templates/pwm/data/pwm.hjson.tpl", top_name),
    # TODO: pwrmgr template cannot be rendered
    # (REPO_TOP / "hw/ip_templates/pwrmgr/data/pwrmgr.hjson.tpl", top_name),
    # TODO: rstmgr template cannot be rendered
    # (REPO_TOP / "hw/ip_templates/rstmgr/data/rstmgr.hjson.tpl", top_name),
]

# IPs which were taped out as part of Earl Grey 1.0.0.
# Extracted from branch earlgrey_1.0.0
EG100_TAPED_OUT_IPS = [
    "adc_ctrl",
    "aes",
    "aon_timer",
    "csrng",
    "edn",
    "entropy_src",
    "gpio",
    "hmac",
    "i2c",
    "keymgr",
    "kmac",
    "lc_ctrl",
    "otbn",
    "otp_ctrl",
    "pattgen",
    "pwm",
    "rom_ctrl",
    "rv_core_ibex",
    "rv_dm",
    "rv_timer",
    "spi_device",
    "spi_host",
    "sram_ctrl",
    "sysrst_ctrl",
    "uart",
    "usbdev",
]

# For some IPs there are multiple regressions with different naming. Any IP not listed here has one
# regression named after its name.
REGRESSIONS_PER_IP = {
    "aes": ["masked", "unmasked"],
    "kmac": ["masked", "unmasked"],
    "sram_ctrl": ["main", "ret"],
    "entropy_src": ["rng_4bits"],
    "edn": ["edn0", "edn1"],
    "lc_ctrl": ["volatile_unlock_enabled", "volatile_unlock_disabled"],
    "rom_ctrl": ["32kb", "64kb"],
    "rv_dm": ["use_jtag_interface"],
    "spi_device": ["1r1w", "2p"],
}


def get_previous_sunday():
    """Calculates the date of the most recent Sunday formatted as YYYY_MM_DD."""
    today = datetime.date.today()
    days_to_subtract = today.weekday() + 1
    return (today - datetime.timedelta(days=days_to_subtract)).strftime("%Y_%m_%d")


def parse_version_tuple(rev):
    """Parse version strings into tuples for proper semantic sorting.
    Example: '1.10' -> (1, 10), which correctly ranks higher than '1.2' -> (1, 2).
    """
    v = str(rev.get("version", "0"))

    parts = []
    for part in v.split('.'):
        # Extract just the digits to safely handle things like "1.0-rc1"
        digits = "".join(filter(str.isdigit, part))
        parts.append(int(digits) if digits else -1)

    return tuple(parts)


# Returns the color for the badge based on the percentage value. Expects a string like "85.6%".
# For non % values it returns a greyish color
def get_badge_color_from_percentage(value_str):
    try:
        pct_val = float(value_str.replace('%', ''))
        if pct_val >= 90:
            color = 'brightgreen'
        elif pct_val >= 80:
            color = 'green'
        elif pct_val >= 70:
            color = 'yellowgreen'
        elif pct_val >= 60:
            color = 'yellow'
        elif pct_val >= 50:
            color = 'orange'
        else:
            color = 'red'
    except ValueError:
        color = 'lightgrey'  # Fallback for non-numeric values
    return color


# Generates badges for the test results by parsing the IP report. It uses shields.io badges. Each
# coverage metric as well as number of tests and test passing percentage is returned in a
# dictonary.
def generate_badges(url):
    # No trailing / as otherwise the badge name will have a /
    badge_base_url = "https://img.shields.io/badge"

    # Try to get the IP regression report
    try:
        response = requests.get(url)
        response.raise_for_status()
        html_content = response.text
    except requests.exceptions.RequestException as e:
        print(f"Error fetching the URL: {e}")
        return {}

    soup = BeautifulSoup(html_content, 'html.parser')
    badges = {}

    # Extract Coverage Statistics
    cov_header = soup.find('div', string=lambda text: text and 'Coverage statistics' in text)
    if cov_header:
        cov_container = cov_header.find_next_sibling('div', class_='container small')
        if cov_container:
            cols = cov_container.find_all('div', class_='col')
            for col in cols:
                items = col.find_all('li')
                if len(items) == 2:
                    name = items[0].text.strip()
                    value_str = items[1].text.strip().replace(' ', '')
                    if not name or not value_str:
                        continue

                    color = get_badge_color_from_percentage(value_str)

                    # Replace coverage metric names with proper names.
                    badge_name = name
                    if badge_name == "func":
                        badge_name = "Functional Coverage"
                    elif badge_name == "code":
                        badge_name = "Code Coverage"

                    # Adapt text to match shield.io rules and encode the % sign.
                    safe_value = value_str.replace('%', '%25')
                    badge_name = badge_name.replace('-', '--').replace('_', '__').replace(' ', '_')

                    badge_url = f"{badge_base_url}/{badge_name}-{safe_value}-{color}"
                    badges[f"{badge_name}"] = f'<img src="{badge_url}">'

    # Extract details from validation stages to compute test passed % total number of tests running
    accordion = soup.find('div', id='accordionStages')
    unique_tests = {}

    if accordion:
        # Find all table rows in the accordion
        rows = accordion.find_all('tr')
        for row in rows:
            tds = row.find_all('td')
            # A valid test row has 7 columns. We avoid the testpoint sub-headers.
            if len(tds) >= 7:
                test_name = tds[1].text.strip()
                pass_text = tds[4].text.strip()
                total_text = tds[5].text.strip()

                # Ensure the data is numeric
                if test_name and pass_text.isdigit() and total_text.isdigit():
                    pass_count = int(pass_text)
                    total_count = int(total_text)

                    # Store data for unique tests. A test can be used in multiple testpoints but
                    # has always the same results.
                    if test_name not in unique_tests:
                        unique_tests[test_name] = {'pass': pass_count, 'total': total_count}

    total_unique_passes = sum(t['pass'] for t in unique_tests.values())
    total_unique_tests = sum(t['total'] for t in unique_tests.values())

    if total_unique_tests > 0:
        # Calculate True Total Passing Percentage
        total_passing_pct = (total_unique_passes / total_unique_tests) * 100
        total_passing_pct_str = f"{total_passing_pct:.2f}%"

        # Total Passing badge
        color = get_badge_color_from_percentage(total_passing_pct_str)
        badge_name = "Tests_Passing"
        # Encode the % sign
        safe_value = total_passing_pct_str.replace('%', '%25')
        badge_url = f"https://img.shields.io/badge/{badge_name}-{safe_value}-{color}"
        badges[badge_name] = f'<img src="{badge_url}">'

        # Tests running badge
        badge_name = "Tests_Running"
        badge_url = f"https://img.shields.io/badge/{badge_name}-{total_unique_tests}-blue"
        badges[badge_name] = f'<img src="{badge_url}">'

    return badges


def get_latest_revision(ip_data):
    # Not all IPs have a revision
    latest_revision = None
    if ip_data.get("revisions") is not None:
        revisions = []
        for rev in ip_data.get("revisions"):
            revisions.append({
                "version": rev.get("version", "N/A"),
                "design_stage": rev.get("design_stage", "N/A"),
                "verification_stage": rev.get("verification_stage", "N/A"),
                "life_stage": rev.get("life_stage", "N/A"),
            })

        # Take the latest revision (highest version) for the regression link
        revisions.sort(key=parse_version_tuple, reverse=True)
        latest_revision = revisions[0]
    else:
        latest_revision = {
            "version": ip_data.get("version", "N/A"),
            "design_stage": ip_data.get("design_stage", "N/A"),
            "verification_stage": ip_data.get("verification_stage", "N/A"),
            "life_stage": ip_data.get("life_stage", "N/A"),
        }

    return latest_revision


def generate_links_for_regs_and_badges(ipname, topname, date_str):
    reg_top_base_url = f"https://nightly.reports.lowrisc.org/opentitan_weekly_{topname}"
    latest_reg_base_url = (f"{reg_top_base_url}/{date_str}/")
    latest_reg_all_url = (f"{reg_top_base_url}/{date_str}/index.html")
    latest_reg_ip_url = (f"{reg_top_base_url}/{date_str}/{ipname}.html")

    # TODO: Linking regression_links directly to the IP is currently not possible as the CSS is
    # only loaded when visiting index.html. If this is possible, the two lists badge_links and
    # regression_links can be merged / optimized.
    regression_links = []
    badge_links = []
    if ipname in REGRESSIONS_PER_IP:
        for regression in REGRESSIONS_PER_IP[ipname]:
            regression_links += [f"[`{ipname}_{regression}`]({latest_reg_all_url})"]
            badge_links += [latest_reg_base_url + f"{ipname}_{regression}.html"]
    else:
        regression_links += [f"[`{ipname}`]({latest_reg_all_url})"]
        badge_links += [latest_reg_ip_url]

    return regression_links, badge_links


def generate_regression_info(ip_data, topname):
    ipname = ip_data.get("name")
    print(f"Processing IP {ipname}..")

    date_str = get_previous_sunday()

    regression_links, badge_links = generate_links_for_regs_and_badges(ipname, topname, date_str)

    # Build the header
    block_lines = []
    block_lines += [f"{START_MARKER}"]

    latest_revision = get_latest_revision(ip_data)
    dev_stage_url = "https://opentitan.org/book/doc/project_governance/development_stages.html"
    dev_stages = (f"{latest_revision.get('design_stage')}, "
                  f"{latest_revision.get('verification_stage')}")

    block_lines += [
        f"| Regression | Version | [Stages]({dev_stage_url}) | Results |",
        "|-|-|-|-|",
    ]

    for badge_link, reg_link in zip(badge_links, regression_links):
        badge_html = generate_badges(badge_link)
        block_lines += [
            f" {reg_link} | {latest_revision.get('version')} | {dev_stages} | "
            f"{badge_html['Tests_Running']} {badge_html['Tests_Passing']} "
            f"{badge_html['Functional_Coverage']} {badge_html['Code_Coverage']} |",
        ]

    if ipname in EG100_TAPED_OUT_IPS:
        egv100_doc_url = f"https://opentitan.org/earlgrey_1.0.0/book/hw/ip/{ipname}/index.html"
        block_lines += [
            "",
            "This IP has been taped out in Earl Grey 1.0.0. The corresponding documentation and "
            f"regression results can be found [here]({egv100_doc_url})."
        ]

    block_lines.append(f"{END_MARKER}")
    new_block = "\n".join(block_lines)
    return new_block


def render_template_ip_and_get_data(hjson_path):
    ip_template = IpTemplate.from_template_path(hjson_path.parent.parent)
    ip_config = IpConfig(ip_template.params, "tmp_ip")
    renderer = IpBlockRenderer(ip_template, ip_config)
    # Render template in a temporary directory and read the resulting hjson. The rendered hjson
    # will be automatically deleted after reading.
    with tempfile.TemporaryDirectory() as tmpdir:
        renderer.render(Path(tmpdir), True)
        # Find the ip hjson file without knowing the ip name.
        hjson_file = os.path.join(tmpdir, "data",
                                  os.path.basename(hjson_path).removesuffix(".tpl"))
        with open(hjson_file, "r") as f:
            ip_data = hjson.load(f)

    return ip_data


def update_readmes(add_markers=False):
    hjson_paths = IP_BLOCKS_HJSON_PATHS

    processed_ips = set()
    skipped_ips = set()

    for hjson_path, topname in hjson_paths:
        if not hjson_path.is_file():
            continue

        # If we operate on a template, we first need to render it with the default parameters.
        print(hjson_path)
        if hjson_path.name.endswith(".tpl"):
            ip_data = render_template_ip_and_get_data(hjson_path)
        else:
            with open(hjson_path, "r") as f:
                ip_data = hjson.load(f)

        ipname = ip_data.get("name")

        # readme is at
        # - hjson_path/../README.md
        # - hjson_path/../README.md.tpl (for some template ip but not all)
        readme_path = hjson_path.parent.parent / "README.md"
        readme_template = hjson_path.parent.parent / "README.md.tpl"
        if not os.path.isfile(readme_path):
            if not os.path.isfile(readme_template):
                print(f"README {readme_path} and {readme_template} do not exist for IP "
                      f"{ipname}. Skipping it.")
                skipped_ips.add(ipname)
                continue
            else:
                readme_path = readme_template

        with open(readme_path, "r") as f:
            content = f.read()

        # Search for the tags in the README. If they do not exist, optionally add them.
        start_pos = content.find(START_MARKER)
        end_pos = content.find(END_MARKER)

        if start_pos == -1 and end_pos == -1 and add_markers:
            # Markers were not found. We want to add them on the 2nd line.
            first_newline = content.find('\n')
            if first_newline != -1:
                content = (content[:first_newline + 1] + f"{START_MARKER}\n{END_MARKER}\n" +
                           content[first_newline + 1:])
            # Re-find the markers.
            start_pos = content.find(START_MARKER)
            end_pos = content.find(END_MARKER)

        # Only update readme if markers exist
        if start_pos != -1 and end_pos != -1:
            assert end_pos > start_pos, "End marker is before the start marker."
            content_before = content[:start_pos]
            content_after = content[end_pos + len(END_MARKER):]

            # Ensure clean line spacing around the replaced block
            if content_before and not content_before.endswith('\n'):
                content_before += '\n'
            if content_after and not content_after.startswith('\n'):
                content_after = '\n' + content_after.lstrip('\r\n')

            reg_info = generate_regression_info(ip_data, topname)
            new_content = content_before + reg_info + content_after

            with open(readme_path, "w") as f:
                f.write(new_content)
        else:
            print(f"Markers do not exist for IP {ipname}. Skipping it.")
            skipped_ips.add(ipname)
            continue

        processed_ips.add(ipname)
        print(f"Updated existing readme for IP {ipname} at {readme_path}")

    print("Finished updating readmes.")
    print("Processed IPs:")
    if len(processed_ips) == 0:
        print('- None')
    else:
        for ip in processed_ips:
            print(f"- {ip}")
    print("Skipped IPs:")
    if len(skipped_ips) == 0:
        print('- None')
    else:
        for ip in skipped_ips:
            print(f"- {ip}")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(
        description="Update IP README files with latest regression results."
    )
    parser.add_argument("--add-markers", action="store_true", default=False,
                        help="Add autogen markers to README files if they don't exist.")

    args = parser.parse_args()
    update_readmes(add_markers=args.add_markers)
