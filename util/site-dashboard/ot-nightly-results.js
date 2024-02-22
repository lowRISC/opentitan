// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

const block_level_urls = {
  "adc_ctrl": ["https://reports.opentitan.org/hw/ip/adc_ctrl/dv/2024.02.19_06.03.32/"],
  "aes": ["https://reports.opentitan.org/hw/ip/aes_masked/dv/2024.02.19_06.04.36/","https://reports.opentitan.org/hw/ip/aes_unmasked/dv/2024.02.19_06.04.09/"],
  "alert_handler": ["https://reports.opentitan.org/hw/top_earlgrey/ip_autogen/alert_handler/dv/2024.02.19_06.17.59/"],
  "aon_timer": ["https://reports.opentitan.org/hw/ip/aon_timer/dv/2024.02.19_06.04.50/"],
  "clkmgr": ["https://reports.opentitan.org/hw/ip/clkmgr/dv/2024.02.19_06.05.08/"],
  "csrng": ["https://reports.opentitan.org/hw/ip/csrng/dv/2024.02.19_06.05.46/"],
  "edn": ["https://reports.opentitan.org/hw/ip/edn/dv/2024.02.19_06.06.01/"],
  "entropy_src": ["https://reports.opentitan.org/hw/ip/entropy_src/dv/2024.02.08_09.00.50/"],
  "flash_ctrl": ["https://reports.opentitan.org/hw/ip/flash_ctrl/dv/2024.02.19_06.06.48/"],
  "gpio": ["https://reports.opentitan.org/hw/ip/gpio/dv/2024.02.19_06.07.30/"],
  "hmac": ["https://reports.opentitan.org/hw/ip/hmac/dv/2024.02.19_06.08.01/"],
  "i2c": ["https://reports.opentitan.org/hw/ip/i2c/dv/2024.02.19_06.08.19/"],
  "keymgr": ["https://reports.opentitan.org/hw/ip/keymgr/dv/2024.02.19_06.08.41/"],
  "kmac": ["https://reports.opentitan.org/hw/ip/kmac_masked/dv/2024.02.19_06.09.08/","https://reports.opentitan.org/hw/ip/kmac_unmasked/dv/2024.02.19_06.09.33/"],
  "lc_ctrl": ["https://reports.opentitan.org/hw/ip/lc_ctrl/dv/2024.02.19_06.09.58/"],
  "otbn": ["https://reports.opentitan.org/hw/ip/otbn/dv/uvm/2024.02.19_06.11.34/"],
  "otp_ctrl": ["https://reports.opentitan.org/hw/ip/otp_ctrl/dv/2024.02.19_06.11.52/"],
  "pattgen": ["https://reports.opentitan.org/hw/ip/pattgen/dv/2024.02.19_06.12.37/"],
  "prim_alert": ["https://reports.opentitan.org/hw/ip/prim/dv/prim_alert/2024.02.19_06.12.50/"],
  "prim_esc": ["https://reports.opentitan.org/hw/ip/prim/dv/prim_esc/2024.02.19_06.13.02/"],
  "prim_lfsr": ["https://reports.opentitan.org/hw/ip/prim/dv/prim_lfsr/2024.02.19_06.13.13/"],
  "prim_present": ["https://reports.opentitan.org/hw/ip/prim/dv/prim_present/2024.02.19_06.13.24/"],
  "prim_prince": ["https://reports.opentitan.org/hw/ip/prim/dv/prim_prince/2024.02.19_06.13.36/"],
  "pwm": ["https://reports.opentitan.org/hw/ip/pwm/dv/2024.02.19_06.14.01/"],
  "pwrmgr": ["https://reports.opentitan.org/hw/top_earlgrey/ip_autogen/pwrmgr/dv/2024.02.19_06.18.39/"],
  "rom_ctrl": ["https://reports.opentitan.org/hw/ip/rom_ctrl/dv/2024.02.19_06.14.14/"],
  "rstmgr": ["https://reports.opentitan.org/hw/top_earlgrey/ip_autogen/rstmgr/dv/2024.02.19_06.19.12/"],
  "rstmgr_cnsty_chk": ["https://reports.opentitan.org/hw/top_earlgrey/ip_autogen/rstmgr/dv/rstmgr_cnsty_chk/2024.02.19_06.19.00/"],
  "rv_dm": ["https://reports.opentitan.org/hw/ip/rv_dm/dv/2024.02.19_06.14.33/"],
  "rv_timer": ["https://reports.opentitan.org/hw/ip/rv_timer/dv/2024.02.19_06.14.53/"],
  "spi_device": ["https://reports.opentitan.org/hw/ip/spi_device/dv/2024.02.19_06.15.36/"],
  "spi_host": ["https://reports.opentitan.org/hw/ip/spi_host/dv/2024.02.19_06.15.22/"],
  "sram_ctrl": ["https://reports.opentitan.org/hw/ip/sram_ctrl_main/dv/2024.02.19_06.16.11/","https://reports.opentitan.org/hw/ip/sram_ctrl_ret/dv/2024.02.19_06.16.32/"],
  "sysrst_ctrl": ["https://reports.opentitan.org/hw/ip/sysrst_ctrl/dv/2024.02.19_06.16.53/"],
  "tl_agent": ["https://reports.opentitan.org/hw/dv/sv/tl_agent/dv/2024.02.19_06.03.22/"],
  "uart": ["https://reports.opentitan.org/hw/ip/uart/dv/2024.02.19_06.17.18/"],
  "usbdev": ["https://reports.opentitan.org/hw/ip/usbdev/dv/2024.02.19_06.17.38/"],
  "xbar": ["https://reports.opentitan.org/hw/top_earlgrey/ip/xbar_main/dv/autogen/2024.02.19_06.19.32/","https://reports.opentitan.org/hw/top_earlgrey/ip/xbar_peri/dv/autogen/2024.02.19_06.19.57/"],
  "rv_core_ibex": ["https://ibex.reports.lowrisc.org/opentitan/latest/"],
};

const chip_level_urls = {
  "chip_earlgrey": ["https://reports.opentitan.org/hw/top_earlgrey/dv/2024.02.19_06.20.20/"],
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
