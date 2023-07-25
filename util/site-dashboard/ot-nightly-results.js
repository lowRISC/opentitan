// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

const block_level_urls = {
  "adc_ctrl": ["https://reports.opentitan.org/hw/ip/adc_ctrl/dv/latest/"],
  "aes": ["https://reports.opentitan.org/hw/ip/aes_masked/dv/latest/", "https://reports.opentitan.org/hw/ip/aes_unmasked/dv/latest/"],
  "alert_handler": ["https://reports.opentitan.org/hw/top_earlgrey/ip_autogen/alert_handler/dv/latest/"],
  "aon_timer": ["https://reports.opentitan.org/hw/ip/aon_timer/dv/latest/"],
  "clkmgr": ["https://reports.opentitan.org/hw/ip/clkmgr/dv/latest/"],
  "csrng": ["https://reports.opentitan.org/hw/ip/csrng/dv/latest/"],
  "edn": ["https://reports.opentitan.org/hw/ip/edn/dv/latest/"],
  "entropy_src": ["https://reports.opentitan.org/hw/ip/entropy_src/dv/latest/"],
  "flash_ctrl": ["https://reports.opentitan.org/hw/ip/flash_ctrl/dv/latest/"],
  "gpio": ["https://reports.opentitan.org/hw/ip/gpio/dv/latest/"],
  "hmac": ["https://reports.opentitan.org/hw/ip/hmac/dv/latest/"],
  "i2c": ["https://reports.opentitan.org/hw/ip/i2c/dv/latest/"],
  "keymgr": ["https://reports.opentitan.org/hw/ip/keymgr/dv/latest/"],
  "kmac": ["https://reports.opentitan.org/hw/ip/kmac_masked/dv/latest/", "https://reports.opentitan.org/hw/ip/kmac_unmasked/dv/latest/"],
  "lc_ctrl": ["https://reports.opentitan.org/hw/ip/lc_ctrl/dv/latest/"],
  "otbn": ["https://reports.opentitan.org/hw/ip/otbn/dv/uvm/latest/"],
  "otp_ctrl": ["https://reports.opentitan.org/hw/ip/otp_ctrl/dv/latest/"],
  "pattgen": ["https://reports.opentitan.org/hw/ip/pattgen/dv/latest/"],
  "prim_alert": ["https://reports.opentitan.org/hw/ip/prim/dv/prim_alert/latest/"],
  "prim_esc": ["https://reports.opentitan.org/hw/ip/prim/dv/prim_esc/latest/"],
  "prim_lfsr": ["https://reports.opentitan.org/hw/ip/prim/dv/prim_lfsr/latest/"],
  "prim_present": ["https://reports.opentitan.org/hw/ip/prim/dv/prim_present/latest/"],
  "prim_prince": ["https://reports.opentitan.org/hw/ip/prim/dv/prim_prince/latest/"],
  "pwm": ["https://reports.opentitan.org/hw/ip/pwm/dv/latest/"],
  "pwrmgr": ["https://reports.opentitan.org/hw/ip/pwrmgr/dv/latest/"],
  "rom_ctrl": ["https://reports.opentitan.org/hw/ip/rom_ctrl/dv/latest/"],
  "rstmgr": ["https://reports.opentitan.org/hw/ip/rstmgr/dv/latest/"],
  "rstmgr_cnsty_chk": ["https://reports.opentitan.org/hw/ip/rstmgr/dv/rstmgr_cnsty_chk/latest/"],
  "rv_dm": ["https://reports.opentitan.org/hw/ip/rv_dm/dv/latest/"],
  "rv_timer": ["https://reports.opentitan.org/hw/ip/rv_timer/dv/latest/"],
  "spi_device": ["https://reports.opentitan.org/hw/ip/spi_device/dv/latest/"],
  "spi_host": ["https://reports.opentitan.org/hw/ip/spi_host/dv/latest/"],
  "sram_ctrl": ["https://reports.opentitan.org/hw/ip/sram_ctrl_main/dv/latest/", "https://reports.opentitan.org/hw/ip/sram_ctrl_ret/dv/latest/"],
  "sysrst_ctrl": ["https://reports.opentitan.org/hw/ip/sysrst_ctrl/dv/latest/"],
  "tl_agent": ["https://reports.opentitan.org/hw/dv/sv/tl_agent/dv/latest/"],
  "uart": ["https://reports.opentitan.org/hw/ip/uart/dv/latest/"],
  "usbdev": ["https://reports.opentitan.org/hw/ip/usbdev/dv/latest/"],
  "xbar": ["https://reports.opentitan.org/hw/top_earlgrey/ip/xbar_main/dv/autogen/latest/", "https://reports.opentitan.org/hw/top_earlgrey/ip/xbar_peri/dv/autogen/latest/"],
  "rv_core_ibex": ["https://ibex.reports.lowrisc.org/opentitan/latest/"],
};

const chip_level_urls = {
  "chip_earlgrey": ["https://reports.opentitan.org/hw/top_earlgrey/dv/latest/"],
};

/**
 * @param {string} name - Optional name to override the block name pulled from the report.
 * @param {string} report_url - Url of the report to be fetched.
 * @returns {BlockLevelResults} Object containing report data after some processing.
 */
async function fetch_and_process_report(name, report_url) {
  try {
    let fetch_response = await fetch(report_url + "report.json");
    let block_info = await fetch_response.json();
    let block_results = new BlockLevelResults(name, block_info, report_url);
    return block_results;
  } catch (error) {
    console.error(`Saw error whilst processing report URL ${report_url}`);
    console.error(error);
  }

  return null;
}

/**
 * @param {Object} report_urls - An object mapping names to report urls
 * @param {boolean} override_names - Takes the name from the 'report_urls' key rather than the report
 * @returns {Array[BlockLevelResults]}
 */
async function fetch_results(report_urls, override_names = false) {
  const name_url_pairs = [];
  for (const [key, value] of Object.entries(report_urls)) {
    // Each value may be an array, one item for each 'variant' of a block
    for (const variant of value) {
      name_url_pairs.push([key, variant]);
    }
  }
  let report_promises = name_url_pairs.map(pair => fetch_and_process_report(
    (override_names ? pair[0] : undefined), // name
    pair[1]));                              // url
  let report_results = await Promise.allSettled(report_promises);

  return report_results
    .filter((report_result) =>
      report_result.status == "fulfilled" && report_result.value != null)
    .map((report_result) => report_result.value);
}


/**
 * This function is used for the block-dashboard on the homepage of each HWIP block.
 *
 * @param {string} block_name - The name of the block to generate the dashboard for.
 * @returns {Array[BlockLevelResults]} A array with the processed block report(s) for all variants.
 */
async function fetch_block_results(block_name) {
  // Filter-out all the blocks that don't match the 'block_name' argument
  const block_report_urls = Object.fromEntries(
    Object.entries(block_level_urls).filter(
      ([key, val]) => key.includes(block_name)
    )
  );
  return fetch_results(block_report_urls);
}
