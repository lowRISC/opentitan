# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

"""CLI for the OpenTitan DV Tool."""

import click


@click.group()
def cli() -> None:
    """OpenTitan DV tool.

    Note: this is an experimental tool and the interface may change.
    """


@cli.command()
def run() -> None:
    """Execute a DV plan."""
    click.echo(
        "Not yet implemented: please use the utils/dvsim/dvsim.py script "
        "instead for the moment.",
    )


@cli.group()
def registry() -> None:
    """Remote centeralised results registry.

    Results registries contain DV results that can be sourced from multiple DV
    runs in a centerlised location.
    """


@registry.command()
def publish() -> None:
    """Publish dv run result artefacts to the registry."""
    # TODO: Collect the run results, package and publish to google bucket


@registry.command()
def pull() -> None:
    """Pull dv run result artefacts from the registry."""
    # TODO: download a subset of the run results from a google bucket


@cli.command()
def report() -> None:
    """Generate reports."""
    # TODO: Parse the dv run artefacts and generate a report from them
    # TODO: Generate a summary


if __name__ == "__main__":
    cli()
