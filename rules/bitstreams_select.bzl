# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

"""Functions to aid filtering references to non-existent targets in the
@bitstreams repo.
"""

load("@bitstreams//:defs.bzl", "BITSTREAM_CACHE_DESIGNS")

def bitstream_cache_or(design, cached, alternate):
    """Mux selection between the `cached` object or an `alternate` object,
    based on whether `design` is in the bitstreams cache.

    Args:
        design: The name of the design. A string.
        cached: The object to select if `design` is in the cache.
        alternate: The object to select if `design` is NOT in the cache.
    Returns:
        Either the `cached` or `alternate` object.
    """
    if design in BITSTREAM_CACHE_DESIGNS:
        return cached
    return alternate

def bitstream_cache_filter(designs):
    """Return a filtered list of the designs that are in the bitstreams cache.
    Args:
        designs: A list of the designs desired to check.
    Returns:
        A list of all designs from `designs` that are in the bitstreams cache.
    """
    filtered = []
    for design in designs:
        if design in BITSTREAM_CACHE_DESIGNS:
            filtered.append(design)
    return filtered
