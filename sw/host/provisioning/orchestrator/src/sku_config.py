# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""Module for loading and validating OpenTitan SKU configuration."""

from collections import OrderedDict
from dataclasses import dataclass

import hjson

from ca_config import CaConfig

_PRODUCT_IDS_HJSON = "sw/host/provisioning/orchestrator/data/products.hjson"
_PACKAGE_IDS_HJSON = "sw/host/provisioning/orchestrator/data/packages/earlgrey_a1.hjson"


@dataclass
class SkuConfig:
    """Class for storing an OpenTitan SKU configuration."""
    name: str  # valid: lower snake case only
    product: str  # valid: any product that exists in product database
    si_creator: str  # valid: any SiliconCreator that exists in product database
    package: str  # valid: any package that exists in package database
    target_lc_state: str  # valid: must be in ["dev", "prod", "prod_end"]
    dice_ca: OrderedDict  # valid: see CaConfig
    ext_ca: OrderedDict  # valid: see CaConfig

    def __post_init__(self):
        # Load CA configs.
        self.dice_ca = CaConfig(name="dice_ca", **self.dice_ca)
        self.ext_ca = CaConfig(name="ext_ca", **self.ext_ca)

        # Load product IDs database.
        self._product_ids = None
        with open(_PRODUCT_IDS_HJSON, "r") as fp:
            self._product_ids = hjson.load(fp)

        # Load package IDs database.
        self._package_ids = None
        with open(_PACKAGE_IDS_HJSON, "r") as fp:
            self._package_ids = hjson.load(fp)

        # Validate inputs.
        self.validate()

        # Set product, SiliconCreator, and package IDs.
        self.si_creator_id = int(
            self._product_ids["si_creator_ids"][self.si_creator], 16)
        self.product_id = int(self._product_ids["product_ids"][self.product],
                              16)
        self.package_id = int(self._package_ids[self.package], 16)

    def validate(self) -> None:
        """Validates this object's attributes."""
        # Validate name.
        # TODO: validate SKU name against available binaries to run.
        # Validate product name.
        if self.product not in self._product_ids["product_ids"]:
            raise ValueError("Product ({}) must be product database.".format(
                self.product))
        # Validate SiliconCreator name.
        if self.si_creator not in self._product_ids["si_creator_ids"]:
            raise ValueError(
                "SiliconCreator ({}) must be product database.".format(
                    self.si_creator))
        # Validate package name.
        if self.package not in self._package_ids:
            raise ValueError("Package ({}) must be package database.".format(
                self.package))
        # Validate target_lc_state.
        if self.target_lc_state not in {"dev", "prod", "prod_end"}:
            raise ValueError(
                "Target LC state ({}) must be in [\"dev\", \"prod\", \"prod_end\"]"
                .format(self.target_lc_state))
