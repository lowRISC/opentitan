# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""Module for loading and validating OpenTitan SKU configuration."""

from collections import OrderedDict
from dataclasses import dataclass
from typing import Optional

import hjson

from ca_config import CaConfig
from util import resolve_runfile

_PRODUCT_IDS_HJSON = "sw/host/provisioning/orchestrator/data/products.hjson"
_PACKAGE_IDS_HJSON = "sw/host/provisioning/orchestrator/data/packages/earlgrey_a1.hjson"


@dataclass
class SkuConfig:
    """Class for storing an OpenTitan SKU configuration."""
    name: str  # valid: lower snake case only
    product: Optional[str]  # valid: any product that exists in product database
    si_creator: Optional[str]  # valid: any SiliconCreator that exists in product database
    package: Optional[str]  # valid: any package that exists in package database
    target_lc_state: str  # valid: must be in ["dev", "prod", "prod_end"]
    otp: str  # valid: any string
    perso_bin: str  # valid: any string
    token_encrypt_key: str
    dice_ca: Optional[OrderedDict]  # valid: see CaConfig
    ext_ca: Optional[OrderedDict] = None  # valid: see CaConfig
    owner_fw_boot_str: str = None  # valid: any string

    def __post_init__(self):
        # Load CA configs.
        if self.dice_ca:
            self.dice_ca = CaConfig(name="dice_ca", **self.dice_ca)
        if self.ext_ca:
            self.ext_ca = CaConfig(name="ext_ca", **self.ext_ca)

        # Load product IDs database.
        product_ids_hjson = resolve_runfile(_PRODUCT_IDS_HJSON)
        self._product_ids = None
        with open(product_ids_hjson, "r") as fp:
            self._product_ids = hjson.load(fp)

        # Load package IDs database.
        package_ids_hjson = resolve_runfile(_PACKAGE_IDS_HJSON)
        self._package_ids = None
        with open(package_ids_hjson, "r") as fp:
            self._package_ids = hjson.load(fp)

        # Validate inputs.
        self.validate()

        # Load HW IDs.
        self.load_hw_ids()

        # Resolve LC token encryption key path.
        if self.token_encrypt_key:
            self.token_encrypt_key = resolve_runfile(self.token_encrypt_key)

    @staticmethod
    def from_ids(product_id: int, si_creator_id: int,
                 package_id: int) -> "SkuConfig":
        """Creates a SKU configuration object from product, SiliconCreator, and package IDs."""
        # Load product IDs database.
        product_ids_hjson = resolve_runfile(_PRODUCT_IDS_HJSON)
        product_ids = None
        with open(product_ids_hjson, "r") as fp:
            product_ids = hjson.load(fp)

        # Load package IDs database.
        package_ids_hjson = resolve_runfile(_PACKAGE_IDS_HJSON)
        package_ids = None
        with open(package_ids_hjson, "r") as fp:
            package_ids = hjson.load(fp)

        # Create SKU configuration object.
        product = None
        si_creator = None
        package = None
        for key, value in product_ids["product_ids"].items():
            if int(value, 16) == product_id:
                product = key
                break
        for key, value in product_ids["si_creator_ids"].items():
            if int(value, 16) == si_creator_id:
                si_creator = key
                break
        for key, value in package_ids.items():
            if int(value, 16) == package_id:
                package = key
                break
        sku_config = SkuConfig(name="cp_device_id",
                               product=product,
                               si_creator=si_creator,
                               package=package,
                               target_lc_state="dev",
                               otp="",
                               perso_bin="",
                               dice_ca=OrderedDict(),
                               ext_ca=OrderedDict(),
                               token_encrypt_key="")
        return sku_config

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
        if self.package and self.package not in self._package_ids:
            raise ValueError("Package ({}) must be package database.".format(
                self.package))
        # Validate target_lc_state.
        if self.target_lc_state not in {"dev", "prod", "prod_end"}:
            raise ValueError(
                "Target LC state ({}) must be in [\"dev\", \"prod\", \"prod_end\"]"
                .format(self.target_lc_state))

    def load_hw_ids(self) -> None:
        """Sets product, SiliconCreator, and package IDs."""
        self.si_creator_id = int(
            self._product_ids["si_creator_ids"][self.si_creator], 16)
        self.product_id = int(self._product_ids["product_ids"][self.product],
                              16)
        self.package_id = int(self._package_ids[self.package], 16)
