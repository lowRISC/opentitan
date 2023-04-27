# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from textwrap import dedent
import svg
from functools import reduce
from .util import css_red_green_gradient
from typing import List, TextIO, Dict

SVG_DASHBOARD_HEIGHT = 20
SVG_DASHBOARD_GAP = 5
SVG_DASHBOARD_STYLE = dedent("""
    .text { font: 12px sans-serif;
            text-anchor: middle;
            dominant-baseline: middle;}
    .name { fill: white; }
    .value { fill: black; }
""")
SVG_DASHBOARD_VALUE_WIDTH = 60
SVG_DASHBOARD_NAME_BG_COLOUR = "#666"
SVG_DASHBOARD_PLAIN_VALUE_BG_COLOUR = "#6cf"

class DashboardElement:
    '''A name and value pair SVG dashboard element.'''
    def __init__(self, name: str, value: str, name_width: int,
            value_colour: str = SVG_DASHBOARD_PLAIN_VALUE_BG_COLOUR,
            value_width: int = SVG_DASHBOARD_VALUE_WIDTH,
            height: int = SVG_DASHBOARD_HEIGHT):
        self.name = name
        self.name_width = name_width
        self.value = value
        self.value_width = value_width
        self.height = height
        self.value_colour = value_colour

    def create_svg_elements(self) -> List[svg.Element]:
        return [
                svg.G(
                    elements = self._create_label_elements()),
                svg.G(
                    transform=[svg.Translate(self.name_width, 0)],
                    elements = self._create_value_elements())
                ]

    def _create_label_elements(self) -> List[svg.Element]:
        return [
            svg.Rect(
                x = 0, y = 0,
                width = self.name_width, height = self.height,
                fill = SVG_DASHBOARD_NAME_BG_COLOUR,
                stroke_width = 0),
            svg.Text(
                x = self.name_width / 2, y = self.height / 2,
                class_ = ["text", "name"],
                text = self.name)
        ]

    def _create_value_elements(self) -> List[svg.Element]:
        return [
            svg.Rect(
                x = 0, y = 0,
                width = self.value_width, height = self.height,
                fill = self.value_colour,
                stroke_width = 0),
            svg.Text(
                x = self.value_width / 2, y = self.height / 2,
                class_ = ["text", "value"],
                text = self.value)
        ]

    def calc_total_width(self) -> int:
        return self.name_width + self.value_width

class Dashboard:
    '''A collection of dashboard elements.

    Produces SVG arranging the elements side by side with a defined gap between
    them.
    '''
    def __init__(self, dashboard_elements: List[DashboardElement],
            element_gap: int):
        self.dashboard_elements = dashboard_elements
        self.element_gap = element_gap

    def create_svg_elements(self) -> List[svg.Element]:
        svg_elements = []
        cur_x = 0

        for dashboard_element in self.dashboard_elements:
            new_element = svg.G(
                    elements = dashboard_element.create_svg_elements(),
                    transform = [svg.Translate(cur_x, 0)])
            svg_elements.append(new_element)
            cur_x += dashboard_element.calc_total_width()
            cur_x += self.element_gap

        return svg_elements

    def calc_total_width(self) -> int:
        return reduce(lambda acc, de: (acc + de.calc_total_width() +
                                       self.element_gap),
                      self.dashboard_elements,
                      0) - self.element_gap

def output_results_svg(test_summary_dict: Dict[str, Dict[str, int]],
                       cov_summary_dict: Dict[str, float],
                       dest: TextIO) -> None:
    '''Write an SVG summary dashboard for the given test and coverage results'''

    passing_tests = reduce(lambda acc, test_info: acc +
            test_info[1]['passing'], test_summary_dict.items(), 0)

    failing_tests = reduce(lambda acc, test_info: acc +
            test_info[1]['failing'], test_summary_dict.items(), 0)

    total_tests = passing_tests + failing_tests

    passing_pct = passing_tests / total_tests

    dashboard_elements = [
        DashboardElement("Total Tests", str(total_tests), 120),
        DashboardElement("Tests Passing", f"{passing_pct * 100:.1f}%", 120,
            value_colour = css_red_green_gradient(passing_pct))
    ]


    if cov_summary_dict:
        code_coverage = sum([cov_summary_dict['block'],
                cov_summary_dict['branch'],
                cov_summary_dict['statement'],
                cov_summary_dict['expression'],
                cov_summary_dict['fsm']]) / 5


        dashboard_elements.append(
                DashboardElement("Functional Coverage",
                    f"{cov_summary_dict['covergroup'] * 100:.1f}%", 150,
                    value_colour = css_red_green_gradient(
                        cov_summary_dict['covergroup'])))

        dashboard_elements.append(
                DashboardElement("Code Coverage", f"{code_coverage * 100:.1f}%",
                    120, value_colour = css_red_green_gradient(code_coverage)))


    regression_dashboard = Dashboard(dashboard_elements, SVG_DASHBOARD_GAP)
    summary_svg = svg.SVG(
            width = regression_dashboard.calc_total_width(),
            height = SVG_DASHBOARD_HEIGHT,
            elements = [svg.Style(text=SVG_DASHBOARD_STYLE)] +
                       regression_dashboard.create_svg_elements()
    )

    dest.write(str(summary_svg))
