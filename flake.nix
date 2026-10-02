# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
{
  description = "OpenTitan Earl Grey 1.0.0 (B) EDA development environment";

  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/nixos-26.05";
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

    pyproject-build-systems = {
      url = "github:pyproject-nix/build-system-pkgs";
      inputs = {
        pyproject-nix.follows = "pyproject-nix";
        uv2nix.follows = "uv2nix";
        nixpkgs.follows = "nixpkgs";
      };
    };

    lowrisc-nix.url = "github:lowRISC/lowrisc-nix";

    dvsim.url = "github:lowRISC/dvsim/v1.52.0";
  };

  nixConfig = {
    extra-substituters = ["https://nix-cache.lowrisc.org/public/"];
    extra-trusted-public-keys = ["nix-cache.lowrisc.org-public-1:O6JLD0yXzaJDPiQW1meVu32JIDViuaPtGDfjlOopU7o="];
  };

  outputs = {
    nixpkgs,
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
      # Oldest Python in nixpkgs. Bazel and CI use 3.10, which nixpkgs dropped.
      python = pkgs.python311;

      workspace = uv2nix.lib.workspace.loadWorkspace {workspaceRoot = ./.;};
      overlay = workspace.mkPyprojectOverlay {sourcePreference = "wheel";};
      pythonSet = (pkgs.callPackage pyproject-nix.build.packages {inherit python;})
        .overrideScope (
        lib.composeManyExtensions [
          pyproject-build-systems.overlays.default
          overlay
          (lowrisc-nix.lib.pyprojectOverrides {inherit pkgs;})
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
