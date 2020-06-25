from setuptools import setup, find_packages

setup(
  name = "otbnsim",
  packages=find_packages(),
  install_requires=["riscv-model>=0.4.1"],
  entry_points={
    "console_scripts": [
        "otbn-python-model = otbnsim.main:main",
    ],
  }
)
