// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

const block_level_urls = {
  "adc_ctrl": ["https://reports.opentitan.org/hw/ip/adc_ctrl/dv/2024.01.22_10.44.44/"],
  "aes": ["https://reports.opentitan.org/hw/ip/aes_masked/dv/2024.01.22_10.46.01/","https://reports.opentitan.org/hw/ip/aes_unmasked/dv/2024.01.22_10.45.27/"],
  "alert_handler": ["https://reports.opentitan.org/hw/top_earlgrey/ip_autogen/alert_handler/dv/2024.01.22_11.16.07/"],
  "aon_timer": ["https://reports.opentitan.org/hw/ip/aon_timer/dv/2024.01.22_10.46.17/"],
  "clkmgr": ["https://reports.opentitan.org/hw/ip/clkmgr/dv/2024.01.22_10.47.21/"],
  "csrng": ["https://reports.opentitan.org/hw/ip/csrng/dv/2024.01.22_10.48.06/"],
  "edn": ["https://reports.opentitan.org/hw/ip/edn/dv/2024.01.22_10.48.55/"],
  "entropy_src": ["https://reports.opentitan.org/hw/ip/entropy_src/dv/2024.01.22_10.49.35/"],
  "flash_ctrl": ["https://reports.opentitan.org/hw/ip/flash_ctrl/dv/2024.01.22_10.51.11/"],
  "gpio": ["https://reports.opentitan.org/hw/ip/gpio/dv/2024.01.22_10.52.52/"],
  "hmac": ["https://reports.opentitan.org/hw/ip/hmac/dv/2024.01.22_10.53.53/"],
  "i2c": ["https://reports.opentitan.org/hw/ip/i2c/dv/2024.01.22_10.54.47/"],
  "keymgr": ["https://reports.opentitan.org/hw/ip/keymgr/dv/2024.01.22_10.56.00/"],
  "kmac": ["https://reports.opentitan.org/hw/ip/kmac_masked/dv/2024.01.22_10.57.17/","https://reports.opentitan.org/hw/ip/kmac_unmasked/dv/2024.01.22_10.58.30/"],
  "lc_ctrl": ["https://reports.opentitan.org/hw/ip/lc_ctrl/dv/2024.01.22_10.59.35/"],
  "otbn": ["https://reports.opentitan.org/hw/ip/otbn/dv/uvm/2024.01.22_11.00.27/"],
  "otp_ctrl": ["https://reports.opentitan.org/hw/ip/otp_ctrl/dv/2024.01.22_11.01.45/"],
  "pattgen": ["https://reports.opentitan.org/hw/ip/pattgen/dv/2024.01.22_11.02.37/"],
  "prim_alert": ["https://reports.opentitan.org/hw/ip/prim/dv/prim_alert/2024.01.22_11.02.52/"],
  "prim_esc": ["https://reports.opentitan.org/hw/ip/prim/dv/prim_esc/2024.01.22_11.03.04/"],
  "prim_lfsr": ["https://reports.opentitan.org/hw/ip/prim/dv/prim_lfsr/2024.01.22_11.03.27/"],
  "prim_present": ["https://reports.opentitan.org/hw/ip/prim/dv/prim_present/2024.01.22_11.03.39/"],
  "prim_prince": ["https://reports.opentitan.org/hw/ip/prim/dv/prim_prince/2024.01.22_11.04.05/"],
  "pwm": ["https://reports.opentitan.org/hw/ip/pwm/dv/2024.01.22_11.04.36/"],
  "pwrmgr": ["https://reports.opentitan.org/hw/top_earlgrey/ip_autogen/pwrmgr/dv/2024.01.22_11.16.53/"],
  "rom_ctrl": ["https://reports.opentitan.org/hw/ip/rom_ctrl/dv/2024.01.22_11.05.21/"],
  "rstmgr": ["https://reports.opentitan.org/hw/ip/rstmgr/dv/2024.01.22_11.05.56/"],
  "rstmgr_cnsty_chk": ["https://reports.opentitan.org/hw/ip/rstmgr/dv/rstmgr_cnsty_chk/2024.01.22_11.05.43/"],
  "rv_dm": ["https://reports.opentitan.org/hw/ip/rv_dm/dv/2024.01.22_11.06.19/"],
  "rv_timer": ["https://reports.opentitan.org/hw/ip/rv_timer/dv/2024.01.22_11.07.05/"],
  "spi_device": ["https://reports.opentitan.org/hw/ip/spi_device/dv/2024.01.22_11.09.05/"],
  "spi_host": ["https://reports.opentitan.org/hw/ip/spi_host/dv/2024.01.22_11.07.40/"],
  "sram_ctrl": ["https://reports.opentitan.org/hw/ip/sram_ctrl_main/dv/2024.01.22_11.10.19/","https://reports.opentitan.org/hw/ip/sram_ctrl_ret/dv/2024.01.22_11.11.17/"],
  "sysrst_ctrl": ["https://reports.opentitan.org/hw/ip/sysrst_ctrl/dv/2024.01.22_11.12.25/"],
  "tl_agent": ["https://reports.opentitan.org/hw/dv/sv/tl_agent/dv/2024.01.22_10.43.55/"],
  "uart": ["https://reports.opentitan.org/hw/ip/uart/dv/2024.01.22_11.13.24/"],
  "usbdev": ["https://reports.opentitan.org/hw/ip/usbdev/dv/2024.01.22_11.14.22/"],
  "xbar": ["https://reports.opentitan.org/hw/top_earlgrey/ip/xbar_main/dv/autogen/2024.01.22_11.18.04/","https://reports.opentitan.org/hw/top_earlgrey/ip/xbar_peri/dv/autogen/2024.01.22_11.19.10/"],
  "rv_core_ibex": ["https://ibex.reports.lowrisc.org/opentitan/latest/"],
};

const chip_level_urls = {
  "chip_earlgrey": ["https://reports.opentitan.org/hw/top_earlgrey/dv/2024.01.22_11.25.03/"],
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
