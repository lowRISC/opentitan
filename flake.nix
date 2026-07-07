# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
{
  description = "OpenTitan EDA development environment";

  inputs = {
    # Pinned to nixos-26.05 to match lowrisc-nix and because that channel ships
    # Verilator 5.048.
    nixpkgs.url = "github:nixos/nixpkgs/nixos-26.05";
    flake-utils.url = "github:numtide/flake-utils";

    # uv2nix builds the Python environment straight from this repo's
    # pyproject.toml + uv.lock
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

    # Provides mkEdaShell (the EDA devshell builder)
    lowrisc-nix.url = "github:lowRISC/lowrisc-nix";
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
    ...
  }:
    flake-utils.lib.eachDefaultSystem (system: let
      inherit (nixpkgs) lib;
      pkgs = nixpkgs.legacyPackages.${system};
      python = pkgs.python312;

      # OpenTitan's Python environment, built from this repo's own pyproject.toml
      # + uv.lock. It bundles fusesoc and dvsim along with every other OpenTitan
      # Python dependency these are available on PATH inside the shell.
      workspace = uv2nix.lib.workspace.loadWorkspace {workspaceRoot = ./.;};
      # Prefer prebuilt wheels: they need no per-package build-system overrides
      # and are auto-patchelfed by pyproject.nix, which avoids building native
      # deps (rpds-py/libcst's Rust, libclang, ...) from source.
      overlay = workspace.mkPyprojectOverlay {sourcePreference = "wheel";};
      pythonSet = (pkgs.callPackage pyproject-nix.build.packages {inherit python;})
        .overrideScope (
        lib.composeManyExtensions [
          pyproject-build-systems.overlays.default
          overlay
          # Declares build systems for the sdist-only stragglers (crcmod, ...).
          # Inert for deps that resolve to a prebuilt wheel above.
          (lowrisc-nix.lib.pyprojectOverrides {inherit pkgs;})
        ]
      );
      pythonEnv = pythonSet.mkVirtualEnv "opentitan-env" workspace.deps.default;

      # Commercial EDA tool shell, built on lowrisc-nix's generic mkEdaShell.
      # Enter with `nix develop .`. It execs into a hermetic FHS sandbox, so
      # it is not direnv-loadable and must be entered explicitly.
      #
      # Tool install paths and license servers are supplied at *runtime* from the
      # JSON file named by $LOWRISC_EDA_CONFIG (the flake only declares which
      # vendor tools + versions are wanted); without that config the shell still
      # works and just warns. See lowrisc-nix lib/README-eda.md.
      eda = lowrisc-nix.lib.mkEdaShell {
        inherit pkgs;
        name = "opentitan-eda";
        tools = builtins.fromJSON (builtins.readFile ./tool_data.json);
        # OpenTitan Python env (fusesoc, dvsim, ...) plus the open-source tools
        # that ship in nixpkgs.
        extraDeps = [pythonEnv];
        extraPkgs = [
          # Pinned via lowrisc-nix rather than nixpkgs directly, so a future
          # nixpkgs bump can't silently drift the devshell's tool versions.
          lowrisc-nix.packages.${system}.verilator_5_048
          lowrisc-nix.packages.${system}.verible_0_0_4080
        ];
      };
    in {
      packages.pythonEnv = pythonEnv;

      devShells = {
        inherit eda;
        default = eda;
      };

      formatter = pkgs.alejandra;
    });
}
