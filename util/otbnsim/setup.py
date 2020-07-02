# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Install this one as package

from setuptools import setup, find_packages

setup(name="otbnsim",
      packages=find_packages(),
      install_requires=["riscv-model>=0.4.1"],
      entry_points={
          "console_scripts": [
              "otbn-python-model = otbnsim.main:main",
          ],
      })
