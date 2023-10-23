// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

const block_level_urls = {
  "adc_ctrl": ["https://reports.opentitan.org/hw/ip/adc_ctrl/dv/2023.10.16_18.03.35/"],
  "aes": ["https://reports.opentitan.org/hw/ip/aes_masked/dv/2023.10.16_18.04.57/", "https://reports.opentitan.org/hw/ip/aes_unmasked/dv/2023.10.16_18.04.21/"],
  "alert_handler": ["https://reports.opentitan.org/hw/top_earlgrey/ip_autogen/alert_handler/dv/2023.10.16_18.37.53/"],
  "aon_timer": ["https://reports.opentitan.org/hw/ip/aon_timer/dv/2023.10.16_18.05.42/"],
  "clkmgr": ["https://reports.opentitan.org/hw/ip/clkmgr/dv/2023.10.16_18.06.50/"],
  "csrng": ["https://reports.opentitan.org/hw/ip/csrng/dv/2023.10.16_18.07.39/"],
  "edn": ["https://reports.opentitan.org/hw/ip/edn/dv/2023.10.16_18.08.30/"],
  "entropy_src": ["https://reports.opentitan.org/hw/ip/entropy_src/dv/2023.10.16_18.09.15/"],
  "flash_ctrl": ["https://reports.opentitan.org/hw/ip/flash_ctrl/dv/2023.10.16_18.10.58/"],
  "gpio": ["https://reports.opentitan.org/hw/ip/gpio/dv/2023.10.16_18.12.48/"],
  "hmac": ["https://reports.opentitan.org/hw/ip/hmac/dv/2023.10.16_18.13.24/"],
  "i2c": ["https://reports.opentitan.org/hw/ip/i2c/dv/2023.10.16_18.14.22/"],
  "keymgr": ["https://reports.opentitan.org/hw/ip/keymgr/dv/2023.10.16_18.15.42/"],
  "kmac": ["https://reports.opentitan.org/hw/ip/kmac_masked/dv/2023.10.16_18.17.06/", "https://reports.opentitan.org/hw/ip/kmac_unmasked/dv/2023.10.16_18.17.38/"],
  "lc_ctrl": ["https://reports.opentitan.org/hw/ip/lc_ctrl/dv/2023.10.16_18.18.27/"],
  "otbn": ["https://reports.opentitan.org/hw/ip/otbn/dv/uvm/2023.10.16_18.19.22/"],
  "otp_ctrl": ["https://reports.opentitan.org/hw/ip/otp_ctrl/dv/2023.10.16_18.20.46/"],
  "pattgen": ["https://reports.opentitan.org/hw/ip/pattgen/dv/2023.10.16_18.21.41/"],
  "prim_alert": ["https://reports.opentitan.org/hw/ip/prim/dv/prim_alert/2023.10.16_18.22.07/"],
  "prim_esc": ["https://reports.opentitan.org/hw/ip/prim/dv/prim_esc/2023.10.16_18.22.31/"],
  "prim_lfsr": ["https://reports.opentitan.org/hw/ip/prim/dv/prim_lfsr/2023.10.16_18.22.54/"],
  "prim_present": ["https://reports.opentitan.org/hw/ip/prim/dv/prim_present/2023.10.16_18.23.17/"],
  "prim_prince": ["https://reports.opentitan.org/hw/ip/prim/dv/prim_prince/2023.10.16_18.23.44/"],
  "pwm": ["https://reports.opentitan.org/hw/ip/pwm/dv/2023.10.16_18.24.16/"],
  "pwrmgr": ["https://reports.opentitan.org/ip_autogen/pwrmgr/dv/2023.10.16_18.39.21/"],
  "rom_ctrl": ["https://reports.opentitan.org/hw/ip/rom_ctrl/dv/2023.10.16_18.25.05/"],
  "rstmgr": ["https://reports.opentitan.org/hw/ip/rstmgr/dv/2023.10.16_18.26.28/"],
  "rstmgr_cnsty_chk": ["https://reports.opentitan.org/hw/ip/rstmgr/dv/rstmgr_cnsty_chk/2023.10.16_18.25.40/"],
  "rv_dm": ["https://reports.opentitan.org/hw/ip/rv_dm/dv/2023.10.16_18.27.26/"],
  "rv_timer": ["https://reports.opentitan.org/hw/ip/rv_timer/dv/2023.10.16_18.28.14/"],
  "spi_device": ["https://reports.opentitan.org/hw/ip/spi_device/dv/2023.10.16_18.30.21/"],
  "spi_host": ["https://reports.opentitan.org/hw/ip/spi_host/dv/2023.10.16_18.28.52/"],
  "sram_ctrl": ["https://reports.opentitan.org/hw/ip/sram_ctrl_main/dv/2023.10.16_18.31.42/", "https://reports.opentitan.org/hw/ip/sram_ctrl_ret/dv/2023.10.16_18.32.44/"],
  "sysrst_ctrl": ["https://reports.opentitan.org/hw/ip/sysrst_ctrl/dv/2023.10.16_18.33.56/"],
  "tl_agent": ["https://reports.opentitan.org/hw/dv/sv/tl_agent/dv/2023.10.16_18.02.43/"],
  "uart": ["https://reports.opentitan.org/hw/ip/uart/dv/2023.10.16_18.34.58/"],
  "usbdev": ["https://reports.opentitan.org/hw/ip/usbdev/dv/2023.10.16_18.36.00/"],
  "xbar": ["https://reports.opentitan.org/hw/top_earlgrey/ip/xbar_main/dv/autogen/2023.10.16_18.40.38/", "https://reports.opentitan.org/hw/top_earlgrey/ip/xbar_peri/dv/autogen/2023.10.16_18.41.48/"],
  "rv_core_ibex": ["https://ibex.reports.lowrisc.org/opentitan/latest/"],
};

const chip_level_urls = {
  "chip_earlgrey": ["https://reports.opentitan.org/hw/top_earlgrey/dv/2023.10.16_18.48.05/"],
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
