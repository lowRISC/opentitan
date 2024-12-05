# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""Module for loading and validating OpenTitan SKU configuration."""

from dataclasses import dataclass
from pathlib import Path

from util import resolve_runfile


@dataclass
class CaConfig:
    """Class for Certificate Authority configuration."""
    name: str  # valid: must be in ["dice_ca", "ext_ca"]
    certificate: str  # valid: any valid path to a CA PEM file
    key_type: str  # valid: must be in ["Raw", "Token"]
    key_id: str  # valid: 160-bit serial number of CA certificate
    key: str  # valid: valid path to DER CA private key file or key token ID

    def __post_init__(self):
        # Update certificate and key members to Path objs if necessary.
        self.certificate = Path(resolve_runfile(self.certificate))
        if self.key_type == "Raw":
            self.key = Path(resolve_runfile(self.key))
        self.validate()

    def validate(self) -> None:
        """Validates this object's attributes."""
        # Validate name.
        if self.name not in {"dice_ca", "ext_ca"}:
            raise ValueError("CA name must be in [\"dice_ca\", \"ext_ca\"]")
        # Validate certificate path.
        if not self.certificate.exists():
            raise ValueError("CA certificate file ({}) does not exist.".format(
                self.certificate))
        if self.certificate.suffix != ".pem":
            raise ValueError(
                "CA certificate file ({}) must be a PEM file.".format(
                    self.certificate))
        # Validate key_type.
        if self.key_type not in {"Raw", "Token"}:
            raise ValueError("CA key type must be in [\"Raw\", \"Token\"]")
        # TODO: validate key_id
        # Validate key.
        if self.key_type == "Raw":
            if not self.key.exists():
                raise ValueError("CA private file does not exist.")
            if self.key.suffix != ".der":
                raise ValueError(
                    "CA private file ({}) must be a DER file.".format(
                        self.key))
        elif self.key_type == "Token":
            # TODO: check if Cloud KMS / Nitokey token ID exists.
            pass

    def to_dict_entry(self) -> dict:
        return {
            "certificate": str(self.certificate),
            "key": str(self.key),
            "key_type": self.key_type,
            "key_id": self.key_id,
        }
