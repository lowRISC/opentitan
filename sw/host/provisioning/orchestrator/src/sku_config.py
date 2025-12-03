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
    otp: str  # valid: any 4 char string whose first char is alphabetic and last two are numeric
    ast_cfg_version: int  # valid: any positive integer < 256 (to fit in one byte)
    perso_bin: str  # valid: any string
    token_encrypt_key: str  # valid: any file path that exists
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
    def from_ids(product_id: int, si_creator_id: int, package_id: int,
                 otp: str, ast_cfg_version: int) -> "SkuConfig":
        """Creates a SKU configuration object from various subcomponent IDs."""
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
                               otp=otp,
                               ast_cfg_version=ast_cfg_version,
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
        # Validate AST configuration version.
        if self.ast_cfg_version < 0 or self.ast_cfg_version > 255:
            raise ValueError("AST config version should be in range [0, 256).")
        # Validate OTP string.
        if len(self.otp) != 4:
            raise ValueError("OTP must be a non-empty 4 character string.")
        # Validate OTP ID string.
        if not self.otp[0].isalpha() or not self.otp[1].isalpha():
            raise ValueError(
                "First two chars of OTP string must be alphabetic.")
        # Validate OTP version.
        try:
            _ = int(self.otp[2:], 16)
        except ValueError:
            raise ValueError("OTP version should two digit hexstring.")

    def load_hw_ids(self) -> None:
        """Sets product, SiliconCreator, and package IDs."""
        self.si_creator_id = int(
            self._product_ids["si_creator_ids"][self.si_creator], 16)
        self.product_id = int(self._product_ids["product_ids"][self.product],
                              16)
        self.package_id = int(self._package_ids[self.package], 16)
        # We process the OTP str into a two character ID and version number.
        self.otp_id = self.otp[:2]
        self.otp_version = int(self.otp[2:], 16)
