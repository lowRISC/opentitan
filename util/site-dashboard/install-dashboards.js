// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

const dashboards = document.getElementsByClassName("dv-dashboard");

for (let i = 0;i < dashboards.length; i++) {
  block_name = dashboards[i].getAttribute("data-block-name");
  if (block_name != null) {
    fetch_block_results(block_name)
      .then(function (block_result_list) {
        let dashboard_toplevel = dashboards[i];
        block_result_list
          .map(block_result =>
            block_result.make_block_summary_dashboard().render(dashboard_toplevel));
      });
  }
}
