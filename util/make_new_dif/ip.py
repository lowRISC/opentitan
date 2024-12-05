# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from collections import OrderedDict
from pathlib import Path
from typing import List

import hjson

# This file is $REPO_TOP/util/make_new_dif/ip.py, so it takes three parent()
# calls to get back to the top.
REPO_TOP = Path(__file__).resolve().parent.parent.parent


class Alert:
    """Holds alert information for populating DIF code templates.

    Attributes:
        name_snake (str): Alert short name in lower snake case.
        name_upper (str): Alert short name in upper snake case.
        name_camel (str): Alert short name in camel case.
        description (str): Full description of the alert.

    """

    def __init__(self, alert: OrderedDict) -> None:
        self.name_snake = alert["name"]
        self.name_upper = self.name_snake.upper()
        self.name_camel = "".join(
            [word.capitalize() for word in self.name_snake.split("_")])
        _multiline_description = alert["desc"][0].upper() + alert["desc"][1:]
        self.description = _multiline_description.replace("\n", " ")


class Irq:
    """Holds IRQ information for populating DIF code templates.

    Attributes:
        name_snake (str): IRQ short name in lower snake case.
        name_upper (str): IRQ short name in upper snake case.
        name_camel (str): IRQ short name in camel case.
        description (str): full description of the IRQ.

    """

    def __init__(self, irq: OrderedDict) -> None:
        self.name_snake = irq["name"]
        self.name_upper = self.name_snake.upper()
        self.name_camel = "".join(
            [word.capitalize() for word in self.name_snake.split("_")])
        _multiline_description = irq["desc"][0].upper() + irq["desc"][1:]
        self.description = _multiline_description.replace("\n", " ")
        self.width = irq["width"] if "width" in irq else 1
        self.type = irq["type"] if "type" in irq else "event"
        assert self.type == "event" or self.type == "status"


class Parameter:
    """Holds IP Parameter information for populating DIF code templates.

    Attributes:
        name (str): Parameter name.
        description (str): Parameter description.
        default (int): Default parameter value.

    """

    def __init__(self, parameter: OrderedDict) -> None:
        self.name = parameter["name"]
        self.description = parameter["desc"]
        self.default = None
        if "default" in parameter:
            self.default = parameter["default"]


class Ip:
    """Holds all IP metadata mined from an IP's name and HJSON file.

    Attributes:
        name_snake (str): IP short name in lower snake case.
        name_upper (str): IP short name in upper snake case.
        name_camel (str): IP short name in camel case.
        name_long_lower (str): IP full name in lower case.
        name_long_upper (str): IP full name with first letter capitalized.
        alerts (List[alerts]): List of Alert objs constructed from HSJON data.
        irqs (List[Irq]): List of Irq objs constructed from HJSON data.

    """

    def __init__(self, name_snake: str, name_long_lower: str,
                 ipgen_modules: List[str], reggen_top_modules: List[str]) -> None:
        """Mines metadata to populate this Ip object.

        Args:
            name_snake: IP short name in lower snake case (e.g., pwrmgr).
            name_long_lower: IP full name in lower case (e.g., power manager).
            ipgen_modules: Ipgen modules where hjson is under ip_autogen
            reggen_top_modules: Top Reggen modules where hjson is under top_*
        """
        # Generate various IP name formats.
        self.name_snake = name_snake
        self.name_upper = self.name_snake.upper()
        self.name_camel = "".join(
            [word.capitalize() for word in self.name_snake.split("_")])
        self.name_long_lower = name_long_lower
        # We just want to set the first character to title case. In particular,
        # .capitalize() does not do the right thing, since it would convert
        # UART to Uart.
        self.name_long_upper = (self.name_long_lower[0].upper() +
                                self.name_long_lower[1:])
        # Load HJSON data.
        if self.name_snake in ipgen_modules:
            data_dir = REPO_TOP / "hw/top_earlgrey/ip_autogen/{0}/data".format(
                self.name_snake)
        elif self.name_snake in reggen_top_modules:
            data_dir = REPO_TOP / "hw/top_earlgrey/ip/{0}/data/".format(
                self.name_snake)
        else:
            data_dir = REPO_TOP / "hw/ip/{0}/data".format(self.name_snake)
        _hjson_file = data_dir / "{0}.hjson".format(self.name_snake)
        with _hjson_file.open("r") as f:
            _hjson_str = f.read()
        self._hjson_data = hjson.loads(_hjson_str)
        # Load Alert data from HJSON.
        self.alerts = self._load_alerts()
        # Load IRQ data from HJSON.
        self.irqs = self._load_irqs()
        # Load Parameters from HJSON
        self.parameters = self._load_parameters()

    def _load_alerts(self):
        assert (self._hjson_data and
                "ERROR: must load IP HJSON before loading Alerts")
        alerts = []
        if "alert_list" in self._hjson_data:
            for alert in self._hjson_data["alert_list"]:
                alerts.append(Alert(alert))
        return alerts

    def _load_irqs(self):
        assert (self._hjson_data and
                "ERROR: must load IP HJSON before loading IRQs")
        irqs = []
        if "interrupt_list" in self._hjson_data:
            for irq in self._hjson_data["interrupt_list"]:
                irqs.append(Irq(irq))
        return irqs

    def _load_parameters(self):
        assert (self._hjson_data and
                "ERROR: must load IP HJSON before loarding Parameters")
        parameters = {}
        if "param_list" in self._hjson_data:
            for parameter in self._hjson_data["param_list"]:
                p = Parameter(parameter)
                parameters[p.name] = p
        return parameters

    def has_status_type_irqs(self):
        for irq in self.irqs:
            if irq.type == "status":
                return True
        else:
            return False
