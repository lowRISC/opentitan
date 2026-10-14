# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
{
  description = "OpenTitan Earl Grey 1.0.0 EDA development environment";

  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/nixos-26.05";
    # Python 3.9 matches the Bazel toolchain (MODULE.bazel); nixos-24.05 was the
    # stable release when this branch was cut and is the last to package it.
    nixpkgs-python.url = "github:nixos/nixpkgs/nixos-24.05";
    flake-utils.url = "github:numtide/flake-utils";

    pyproject-nix = {
      url = "github:nix-community/pyproject.nix";
      inputs.nixpkgs.follows = "nixpkgs";
    };

    uv2nix = {
      url = "github:pyproject-nix/uv2nix";
      inputs = {
        pyproject-nix.follows = "pyproject-nix";
        nixpkgs.follows = "nixpkgs";
      };
    };

    # Later revisions make setuptools-scm build-depend on vcs-versioning, which
    # needs Python 3.10+.
    pyproject-build-systems = {
      url = "github:pyproject-nix/build-system-pkgs/bc25212cdd84a796f77743b8cf2856c1a16e5282";
      inputs = {
        pyproject-nix.follows = "pyproject-nix";
        uv2nix.follows = "uv2nix";
        nixpkgs.follows = "nixpkgs";
      };
    };

    # Provides mkEdaShell (the EDA devshell builder)
    lowrisc-nix.url = "github:lowRISC/lowrisc-nix/ded9720f4960e3da2ffcb7d88dfa5fd51cbe4021";

    # Makes the standalone dvsim available, however this branch still contains
    # the in-tree version of DVSim and which was used for development at the
    # time.
    dvsim.url = "github:lowRISC/dvsim/v1.52.0";
  };

  nixConfig = {
    extra-substituters = ["https://nix-cache.lowrisc.org/public/"];
    extra-trusted-public-keys = ["nix-cache.lowrisc.org-public-1:O6JLD0yXzaJDPiQW1meVu32JIDViuaPtGDfjlOopU7o="];
  };

  outputs = {
    nixpkgs,
    nixpkgs-python,
    flake-utils,
    pyproject-nix,
    uv2nix,
    pyproject-build-systems,
    lowrisc-nix,
    dvsim,
    ...
  }:
    flake-utils.lib.eachDefaultSystem (system: let
      inherit (nixpkgs) lib;
      pkgs = nixpkgs.legacyPackages.${system};
      # The pyproject.nix build hooks need a uv with `uv build`.
      pkgsPython = nixpkgs-python.legacyPackages.${system}.extend (_: _: {inherit (pkgs) uv;});
      python = pkgsPython.python39;

      workspace = uv2nix.lib.workspace.loadWorkspace {workspaceRoot = ./.;};
      overlay = workspace.mkPyprojectOverlay {sourcePreference = "wheel";};
      pythonSet = (pkgsPython.callPackage pyproject-nix.build.packages {inherit python;})
        .overrideScope (
        lib.composeManyExtensions [
          pyproject-build-systems.overlays.default
          overlay
          (lowrisc-nix.lib.pyprojectOverrides {pkgs = pkgsPython;})
        ]
      );
      pythonEnv = pythonSet.mkVirtualEnv "opentitan-env" workspace.deps.default;

      # DVSim's dependencies conflict with this branch's Python pins, so expose
      # only its entry point (which runs under DVSim's own interpreter).
      dvsimBin = pkgs.runCommand "dvsim-bin" {} ''
        mkdir -p $out/bin
        ln -s ${dvsim.packages.${system}.default}/bin/dvsim $out/bin/dvsim
      '';

      # Bazel is not provided: ./bazelisk.sh fetches the .bazelversion release.
      eda = lowrisc-nix.lib.mkEdaShell {
        inherit pkgs;
        name = "opentitan-eda";
        tools = builtins.fromJSON (builtins.readFile ./tool_data.json);
        extraDeps = [pythonEnv dvsimBin];
        extraPkgs = [
          lowrisc-nix.packages.${system}.verilator_ot # 4.210
          lowrisc-nix.packages.${system}.verible_ot # v0.0-3622-g07b310a3
          pkgs.openssl # AES DPI model
          pkgs.srecord # SW image conversion
          pkgs.unixtools.xxd # SW image build
          pkgs.lcov
          pkgs.libftdi1
          pkgs.libusb1
          pkgs.pcsclite
          pkgs.lrzsz
        ];
      };
    in {
      packages.pythonEnv = pythonEnv;

      devShells = {
        inherit eda;
        default = eda;
      };

      # `nix run .#eda -- <cmd>` runs a command inside the shell.
      apps = {
        eda = eda.app;
        default = eda.app;
      };

      formatter = pkgs.alejandra;
    });
}
