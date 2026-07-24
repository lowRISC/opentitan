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

      lrPkgs = lowrisc-nix.packages.${system};

      # A single FHS devshell for all local OpenTitan workflows, built on
      # lowrisc-nix's mkEdaShell. It serves two entry points off the *same*
      # environment:
      #   - interactive: `nix develop .` (execs into the hermetic FHS sandbox)
      #   - non-interactive: `nix run .#eda -- <cmd>` / `nix run .#lint -- <cat>`
      #     via mkEdaShell's `.app` (its runScript execs argv inside the sandbox).
      #
      # Commercial EDA tool install paths and license servers are supplied at
      # *runtime* from the JSON named by $LOWRISC_EDA_CONFIG (the flake only
      # declares which vendor tools + versions are wanted); without that config
      # the shell still works and just warns. See lowrisc-nix lib/README-eda.md.
      #
      # edaFhsPackages (mkEdaShell's base) already provides the common libraries
      # and build helpers (glibc/gcc, zlib, systemd->libudev, pkg-config, git,
      # make, autotools, curl, ncurses, ...). extraPkgs adds the OpenTitan tools
      # on top, including everything the lint `bazel` category needs to build
      # host tools such as opentitantool from source.
      eda = lowrisc-nix.lib.mkEdaShell {
        inherit pkgs;
        name = "opentitan-eda";
        tools = builtins.fromJSON (builtins.readFile ./tool_data.json);
        # OpenTitan Python env: fusesoc, dvsim, topgen, reggen, ruff, mypy, ...
        extraDeps = [pythonEnv];
        extraPkgs = with pkgs; [
          # Pinned via lowrisc-nix rather than nixpkgs directly, so a future
          # nixpkgs bump can't silently drift the devshell's tool versions.
          lowrisc-nix.packages.${system}.verilator_5_048
          lowrisc-nix.packages.${system}.verible_0_0_4080
          # Bazel pinned to match .bazelversion (8.7.0). With this on PATH,
          # ./bazelisk.sh uses it directly instead of downloading Bazel over the
          # network, so the build is hermetic and reproducible. Keep this version
          # in sync with .bazelversion (bazelisk falls back to downloading if
          # they ever diverge).
          lowrisc-nix.packages.${system}.bazel_8_7_0
          # OpenSSL headers + libcrypto for the AES DPI model (hw/ip/aes/model:
          # crypto.c includes <openssl/*.h> and links -lcrypto).
          pkgs.openssl
          # srec_cat, invoked by rules/opentitan/transform.bzl to convert build
          # artifacts (e.g. SW images -> SREC/VMEM).
          pkgs.srecord
          # xxd, invoked by rules/opentitan/cc.bzl (`... | xxd -r -p`) during the
          # SW image build.
          pkgs.unixtools.xxd
          # lcov/genhtml, used by util/coverage to collect and render SW (C/C++)
          # coverage.
          pkgs.lcov
          # Hardware-interaction libs/tools used by opentitantool and
          # FPGA/chip bring-up (JTAG, USB, smartcard, serial xmodem/zmodem).
          pkgs.libftdi1
          pkgs.libusb1
          pkgs.pcsclite
          pkgs.dfu-util
          pkgs.lrzsz
          # check-lock-files regenerates python-requirements.txt via `uv pip compile`.
          uv
        ];
        # Point the Bazel bindgen toolchain at a nixpkgs libclang (see
        # third_party/rust/extensions.bzl): the LLVM release Bazel would download
        # cannot be dlopen'd under the Nix loader. Set in the FHS profile so
        # Bazel sees it whether launched from `nix develop` or the lint app.
        profile = ''
          export OT_BINDGEN_LLVM=${lrPkgs.libclang_21}
        '';
      };
    in {
      packages.pythonEnv = pythonEnv;

      devShells = {
        inherit eda;
        default = eda;
      };

      # `nix run .#eda` (or `nix run .`) drops into the EDA sandbox in your
      # $SHELL; with args, `nix run .#eda -- <cmd> <args>` execs them inside the
      # sandbox (argv passed through directly, so use e.g. `-- bash -c '...'` for
      # a shell snippet). mkEdaShell exposes the flake-app payload as `eda.app`.
      apps = {
        eda = eda.app;
        default = eda.app;

        # Lint: run the categorized lint flow (ci/lint/run.sh) in the *same*
        # devshell, preserving `nix run .#lint -- <category>`. Thin wrapper that
        # prefixes run.sh onto the devshell app's argv, so CI and local runs
        # share this one environment.
        lint = {
          type = "app";
          program = "${pkgs.writeShellScript "opentitan-lint" ''
            repo="$(${pkgs.git}/bin/git rev-parse --show-toplevel)"
            exec ${eda.app.program} "$repo/ci/lint/run.sh" "$@"
          ''}";
        };
      };

      formatter = pkgs.alejandra;
    });
}
