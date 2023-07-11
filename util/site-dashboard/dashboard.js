// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

const DashValueKindPlain = 0;
const DashValueKindPctColoured = 1;
const DashValueKindLink = 2;

function render_dashboard_value(value, kind, node) {
  if (value == null) {
    node.textContent = "--";
    return;
  }

  let value_text = "BAD KIND";

  switch (kind) {
    case DashValueKindPlain:
      node.textContent = value.toString();
      break;
    case DashValueKindPctColoured:
      value = value.toPrecision(3);
      node.textContent = value.toString() + " %";

      let r_colour = 0;
      let g_colour = 0;

      if (value >= 50) {
        // Transition from green to yellow
        r_colour = Math.round(255 * ((100 - value) / 50));
        g_colour = 255;
      } else {
        // Transition from yellow to red
        r_colour = 255;
        g_colour = Math.round(255 * (value / 50));
      }

      let color_str = "rgb(" + r_colour.toString() + "," +
        g_colour.toString() + ",0)";

      node.style.backgroundColor = color_str;
      node.style.color = "#3D1067";

      break;
    case DashValueKindLink:
      value_link = document.createElement("a");
      value_link.setAttribute("href", value[1]);
      value_link.textContent = value[0];

      node.appendChild(value_link);
      break;
    default:
      node.textContent = "BAD KIND";
  }
}

class DashboardSingleEntry {
  constructor(label, value, kind) {
    this.label = label;
    this.value = value;
    this.kind = kind;
  }

  render(node) {
    let label_div = document.createElement("div");
    label_div.setAttribute("class", "dashboard-label");
    label_div.textContent = this.label;

    let value_div = document.createElement("div");
    value_div.setAttribute("class", "dashboard-value");

    render_dashboard_value(this.value, this.kind, value_div);

    node.appendChild(label_div);
    node.appendChild(value_div);
  }
}

class DashboardSingleEntryCollection {
  constructor(entries, title = null, report_url = null) {
    this.entries = entries;
    this.report_url = report_url
    this.title = title;
  }

  render(node) {
    if (this.title != null) {
      let title_node = document.createElement("div");
      title_node.setAttribute("class", "dashboard-title");

      if (this.report_url != null) {
        let title_link = document.createElement("a");
        title_link.setAttribute("href", this.report_url + "report.html");
        title_link.textContent = this.title;
        title_node.appendChild(title_link);
      } else {
        title_node.textContent = this.title;
      }

      node.appendChild(title_node);
    }

    this.entries.map(entry => entry.render(node));
  }
}

class DashboardTable {
  constructor(headings, values, kinds) {
    this.headings = headings;
    this.values = values;
    this.kinds = kinds;
  }

  render(node) {
    let table = document.createElement("table");

    this.render_header(table);

    for (let i = 0;i < this.values.length; i++) {
      this.render_value_row(table, this.values[i]);
    }

    node.appendChild(table);
  }

  render_header(node) {
    let header_row = document.createElement("tr");
    for (let i = 0;i < this.headings.length; i++) {
      let header_element = document.createElement("th");
      header_element.textContent = this.headings[i];
      header_row.appendChild(header_element);
    }

    node.appendChild(header_row);
  }

  render_value_row(node, values) {
    let value_row = document.createElement("tr");
    for (let i = 0;i < values.length; i++) {
      let value_element = document.createElement("td");
      render_dashboard_value(values[i], this.kinds[i], value_element);
      value_row.appendChild(value_element);
    }

    node.appendChild(value_row);
  }
}

class BlockLevelResults {
  constructor(json, report_url) {
    this.process_report(json);
    this.report_url = report_url;
  }

  process_report(report) {
    this.block_name = report.block_name;
    if ("block_variant" in report && report.block_variant != null) {
      this.block_name += '/' + report.block_variant;
    }

    this.coverage = report.results.coverage
    this.calculate_summary_coverage(report.tool);

    this.tests = 0;
    this.passing_tests = 0;

    // The report is given in terms of testpoints. Each testpoint may be mapped to
    // multiple tests at a given test may be mapped to multiple testpoints.
    // There may be an additional lists of unmapped tests as well (i.e. those
    // without testpoits). We want a list of unique tests.
    const tests_info = report.results.testpoints
      .flatMap(t => t.tests)
      .concat(report.results.unmapped_tests)
      .filter((t, i, a) => a.findIndex(o => o.name === t.name) === i);

    this.process_tests(tests_info);

    this.passing_tests_pct = (this.passing_tests / this.tests) * 100;
  }

  process_tests(tests_info) {
    this.tests = tests_info
      .map(t => t.total_runs)
      .reduce((acc, x) => acc + x, 0);

    this.passing_tests = tests_info
      .map(t => t.passing_runs)
      .reduce((acc, x) => acc + x, 0);
  }

  calculate_summary_coverage(tool) {
    this.summary_coverage = {
      "functional": null,
      "assertion": null,
      "toggle": null,
      "code": null
    };

    let code_coverage_vals = [];

    // VCS and Xcelium have different category names for coverage. For code
    // coverage there are a number of values to produce an average from for the
    // other summary coverage categories we just need to extract the correct
    // number.
    if (tool == 'vcs') {
        code_coverage_vals =
          [this.coverage["line"],
           this.coverage["cond"],
           this.coverage["fsm"],
           this.coverage["branch"]];

        this.summary_coverage["functional"] = this.coverage["group"];
        this.summary_coverage["assertion"] = this.coverage["assert"];
        this.summary_coverage["toggle"] = this.coverage["toggle"];

    } else if (tool == 'xcelium') {
      code_coverage_vals =
        [this.coverage["block"],
         this.coverage["branch"],
         this.coverage["statement"],
         this.coverage["expression"],
         this.coverage["fsm"]];

      this.summary_coverage["functional"] = this.coverage["covergroup"];
      this.summary_coverage["assertion"] = this.coverage["assertion"];
      this.summary_coverage["toggle"] = this.coverage["toggle"];
    }

    let code_coverage_valid_vals = code_coverage_vals
      .reduce((acc, x) => x != null ? acc + 1 : acc, 0);

    if (code_coverage_valid_vals > 0) {
      let avg_code_coverage = code_coverage_vals
        .reduce((acc, x) => x != null ? acc + x : acc, 0);
      avg_code_coverage /= code_coverage_valid_vals;

      this.summary_coverage["code"] = avg_code_coverage;
    }
  }

  make_block_summary_dashboard() {
    return new DashboardSingleEntryCollection(
      [new DashboardSingleEntry("Tests Running", this.tests, DashValueKindPlain),
       new DashboardSingleEntry("Test Passing", this.passing_tests_pct, DashValueKindPctColoured),
       new DashboardSingleEntry("Functional Coverage", this.summary_coverage["functional"], DashValueKindPctColoured),
       new DashboardSingleEntry("Code Coverage", this.summary_coverage["code"], DashValueKindPctColoured)],
      this.block_name,
      this.report_url,
    );
  }
}

class BlockLevelResultsCollection {
  constructor() {
    this.results_collection = [];
  }

  add_results(results) {
    this.results_collection.push(results);
  }

  make_results_table() {
    let headings = [
      "Block",
      "Tests",
      "Passing",
      "Code Coverage",
      "Toggle Coverage",
      "Assert Coverage",
      "Functional Coverage"
    ]

    let kinds = [
      DashValueKindLink,
      DashValueKindPlain,
      DashValueKindPctColoured,
      DashValueKindPctColoured,
      DashValueKindPctColoured,
      DashValueKindPctColoured,
      DashValueKindPctColoured,
      DashValueKindPctColoured,
    ];

    let values = [];

    for (let i = 0; i < this.results_collection.length; i++) {
      values.push(this.generate_table_values(this.results_collection[i]));
    }

    return new DashboardTable(headings, values, kinds);
  }

  generate_table_values(results) {
    return [
      [results.block_name, results.report_url + "report.html"],
      results.tests,
      results.passing_tests_pct,
      results.summary_coverage["code"],
      results.summary_coverage["toggle"],
      results.summary_coverage["assertion"],
      results.summary_coverage["functional"]
    ];
  }
}
