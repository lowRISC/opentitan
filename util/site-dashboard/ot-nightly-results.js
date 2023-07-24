// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

const all_report_urls = [
  ["adc_ctrl", ["https://reports.opentitan.org/integrated/hw/ip/adc_ctrl/dv/latest/"]],
  ["aes", ["https://reports.opentitan.org/integrated/hw/ip/aes_masked/dv/latest/", "https://reports.opentitan.org/integrated/hw/ip/aes_unmasked/dv/latest/"]],
  ["alert_handler", ["https://reports.opentitan.org/integrated/hw/top_earlgrey/ip_autogen/alert_handler/dv/latest/"]],
  ["aon_timer", ["https://reports.opentitan.org/integrated/hw/ip/aon_timer/dv/latest/"]],
  ["clkmgr", ["https://reports.opentitan.org/integrated/hw/ip/clkmgr/dv/latest/"]],
  ["csrng", ["https://reports.opentitan.org/integrated/hw/ip/csrng/dv/latest/"]],
  ["edn", ["https://reports.opentitan.org/integrated/hw/ip/edn/dv/latest/"]],
  ["entropy_src", ["https://reports.opentitan.org/integrated/hw/ip/entropy_src/dv/latest/"]],
  ["flash_ctrl", ["https://reports.opentitan.org/integrated/hw/ip/flash_ctrl/dv/latest/"]],
  ["gpio", ["https://reports.opentitan.org/integrated/hw/ip/gpio/dv/latest/"]],
  ["hmac", ["https://reports.opentitan.org/integrated/hw/ip/hmac/dv/latest/"]],
  ["i2c", ["https://reports.opentitan.org/integrated/hw/ip/i2c/dv/latest/"]],
  ["keymgr", ["https://reports.opentitan.org/integrated/hw/ip/keymgr/dv/latest/"]],
  ["kmac", ["https://reports.opentitan.org/integrated/hw/ip/kmac_masked/dv/latest/", "https://reports.opentitan.org/integrated/hw/ip/kmac_unmasked/dv/latest/"]],
  ["lc_ctrl", ["https://reports.opentitan.org/integrated/hw/ip/lc_ctrl/dv/latest/"]],
  ["otbn", ["https://reports.opentitan.org/integrated/hw/ip/otbn/dv/uvm/latest/"]],
  ["otp_ctrl", ["https://reports.opentitan.org/integrated/hw/ip/otp_ctrl/dv/latest/"]],
  ["pattgen", ["https://reports.opentitan.org/integrated/hw/ip/pattgen/dv/latest/"]],
  ["prim_alert", ["https://reports.opentitan.org/integrated/hw/ip/prim/dv/prim_alert/latest/"]],
  ["prim_esc", ["https://reports.opentitan.org/integrated/hw/ip/prim/dv/prim_esc/latest/"]],
  ["prim_lfsr", ["https://reports.opentitan.org/integrated/hw/ip/prim/dv/prim_lfsr/latest/"]],
  ["prim_present", ["https://reports.opentitan.org/integrated/hw/ip/prim/dv/prim_present/latest/"]],
  ["prim_prince", ["https://reports.opentitan.org/integrated/hw/ip/prim/dv/prim_prince/latest/"]],
  ["pwm", ["https://reports.opentitan.org/integrated/hw/ip/pwm/dv/latest/"]],
  ["pwrmgr", ["https://reports.opentitan.org/integrated/hw/ip/pwrmgr/dv/latest/"]],
  ["rom_ctrl", ["https://reports.opentitan.org/integrated/hw/ip/rom_ctrl/dv/latest/"]],
  ["rstmgr", ["https://reports.opentitan.org/integrated/hw/ip/rstmgr/dv/latest/"]],
  ["rstmgr_cnsty_chk", ["https://reports.opentitan.org/integrated/hw/ip/rstmgr/dv/rstmgr_cnsty_chk/latest/"]],
  ["rv_dm", ["https://reports.opentitan.org/integrated/hw/ip/rv_dm/dv/latest/"]],
  ["rv_timer", ["https://reports.opentitan.org/integrated/hw/ip/rv_timer/dv/latest/"]],
  ["spi_device", ["https://reports.opentitan.org/integrated/hw/ip/spi_device/dv/latest/"]],
  ["spi_host", ["https://reports.opentitan.org/integrated/hw/ip/spi_host/dv/latest/"]],
  ["sram_ctrl", ["https://reports.opentitan.org/integrated/hw/ip/sram_ctrl_main/dv/latest/", "https://reports.opentitan.org/integrated/hw/ip/sram_ctrl_ret/dv/latest/"]],
  ["sysrst_ctrl", ["https://reports.opentitan.org/integrated/hw/ip/sysrst_ctrl/dv/latest/"]],
  ["tl_agent", ["https://reports.opentitan.org/integrated/hw/dv/sv/tl_agent/dv/latest/"]],
  ["uart", ["https://reports.opentitan.org/integrated/hw/ip/uart/dv/latest/"]],
  ["usbdev", ["https://reports.opentitan.org/integrated/hw/ip/usbdev/dv/latest/"]],
  ["xbar", ["https://reports.opentitan.org/integrated/hw/top_earlgrey/ip/xbar_main/dv/autogen/latest/", "https://reports.opentitan.org/integrated/hw/top_earlgrey/ip/xbar_peri/dv/autogen/latest/"]],
  ["chip", ["https://reports.opentitan.org/integrated/hw/top_earlgrey/dv/latest/"]],
  ["rv_core_ibex", ["https://ibex.reports.lowrisc.org/opentitan/latest/"]]
];

async function fetch_block_report(block_report_url) {
  try {
    let fetch_response = await fetch(block_report_url + "report.json");
    let block_info = await fetch_response.json();
    let block_results = new BlockLevelResults(block_info, block_report_url);

    return block_results;
  } catch (error) {
    console.error(`Saw error whilst processing block URL ${block_report_url}`);
    console.error(error);
  }

  return null;
}

async function fetch_results(block_report_urls) {
  let report_promises = block_report_urls.map((url) => fetch_block_report(url));

  let report_results = await Promise.allSettled(report_promises);

  return report_results
    .filter((report_result) =>
      report_result.status == "fulfilled" && report_result.value != null)
    .map((report_result) => report_result.value);
}

async function fetch_block_results(block_name) {
  let block_report_urls = all_report_urls.find((block_info) => block_info[0] == block_name);

  return fetch_results(block_report_urls[1]);
}

async function fetch_all_results() {
  block_report_urls = all_report_urls.flatMap((url_info) => url_info[1]);

  return fetch_results(block_report_urls);
}
