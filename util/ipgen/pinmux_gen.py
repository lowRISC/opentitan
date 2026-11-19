# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""Provides support functions for the pinmux ipgen template."""

from typing import Dict, List, Tuple

# Maps pad attribute names to their pad_attr_t member name and width. This is required because the
# CSR field names and the SV code mismatch.
PAD_ATTR_FIELDS = {
    "invert": ("invert", 1),
    "virtual_od_en": ("virt_od_en", 1),
    "pull_en": ("pull_en", 1),
    "pull_select": ("pull_select", 1),
    "keeper_en": ("keep_en", 1),
    "schmitt_en": ("schmitt_en", 1),
    "od_en": ("od_en", 1),
    "input_disable": ("input_disable", 1),
    "slew_rate": ("slew_rate", 2),
    "drive_strength": ("drive_strength", 4),
}

# Number of constant selection options preceding the pads/peripheral outputs:
# INSEL has 0 and 1.
# OUTSEL has 0, 1, and high-Z.
INSEL_NUM_CONST = 2
OUTSEL_NUM_CONST = 3


def check_params(n_mio_pads: int, n_dio_pads: int, n_mio_periph_in: int, n_mio_periph_out: int,
                 mio_periph_ins: List[Dict], mio_periph_outs: List[Dict],
                 mio_pad_attr_resvals: List[Tuple[str, Dict]],
                 dio_pad_attr_resvals: List[Tuple[str, Dict]]) -> None:
    """Check the parameters passed to the pinmux template."""
    errors: List[str] = []
    _check_pad_attrs(errors, "mio_pad_attr_resvals", n_mio_pads, mio_pad_attr_resvals)
    _check_pad_attrs(errors, "dio_pad_attr_resvals", n_dio_pads, dio_pad_attr_resvals)
    # The MIO pad attrs list has one entry per MIO pad, take the pad names from there.
    mio_pad_names = [name for name, _ in mio_pad_attr_resvals]
    _check_mio_periph_list(errors, "input", n_mio_pads, mio_pad_names, n_mio_periph_in,
                           mio_periph_ins)
    _check_mio_periph_list(errors, "output", n_mio_pads, mio_pad_names, n_mio_periph_out,
                           mio_periph_outs)
    assert not errors, "\n".join(errors)


def _check_pad_attrs(errors: List[str], param: str, n_pads: int,
                     pad_attrs: List[Tuple[str, Dict]]) -> None:
    """Validate that the pad attribute parameter specifies each pad correctly."""
    if len(pad_attrs) != n_pads:
        errors.append(f"{param} needs {n_pads} entries, got {len(pad_attrs)}")
    for name, attrs in pad_attrs:
        if not isinstance(attrs, dict):
            errors.append(f"pad attrs of {name} must be a dict, got {attrs!r}")
            continue
        for field, value in attrs.items():
            if field not in PAD_ATTR_FIELDS:
                errors.append(f"pad attrs of {name} has unknown field {field}. "
                              f"Valid fields are {list(PAD_ATTR_FIELDS)}")
                continue
            max_value = (1 << PAD_ATTR_FIELDS[field][1]) - 1
            if type(value) is not int or not 0 <= value <= max_value:
                errors.append(f"pad attrs of {name} has {field}: {value!r}. Expected an int in "
                              f"[0, {max_value}]")


def _pad_name(mio_pad_names: List[str], pad: object) -> str:
    return mio_pad_names[pad] if type(pad) is int and 0 <= pad < len(mio_pad_names) else repr(pad)


def _pad_indices(periph: Dict, n_mio_pads: int) -> List[int]:
    """Get the pad indices of all pads a peripheral is muxable to.

    An empty pads entry expands to all MIO pads.
    """
    return periph["pads"] or list(range(n_mio_pads))


def _check_mio_periph_list(errors: List[str], kind: str, n_mio_pads: int,
                           mio_pad_names: List[str], n_periphs: int, periphs: List[Dict]) -> None:
    """Check a list of dicts defining the muxing.

    Each list item is for one MIO peripheral input or output.
    """
    if len(periphs) != n_periphs:
        errors.append(f"Expected {n_periphs} MIO {kind}s, got {len(periphs)}")
    for periph in periphs:
        if not {"name", "pads"} <= set(periph):
            errors.append(f"MIO {kind} {periph} needs a name and pads")
            continue
        name, pads = periph["name"], periph["pads"]
        unknown = set(periph) - {"name", "pads"}
        if unknown:
            errors.append(f"MIO {kind} {name} has unknown keys {sorted(unknown)}")
        for pad in pads:
            if type(pad) is not int or not 0 <= pad < n_mio_pads:
                errors.append(f"MIO {kind} {name} has pad {pad!r}. Expected an int in "
                              f"[0, {n_mio_pads - 1}]")
        dups = sorted({_pad_name(mio_pad_names, pad) for pad in pads if pads.count(pad) > 1})
        if dups:
            errors.append(f"MIO {kind} {name} lists the pads {dups} more than once")


def _sel_mask(idxs: List[int], num_const: int) -> int:
    """Generate the bitmask of legal select values including the constants options."""
    mask = (1 << num_const) - 1
    for idx in idxs:
        mask |= 1 << (idx + num_const)
    return mask


def mio_insel_legal(n_mio_pads: int, mio_periph_ins: List[Dict]) -> List[Tuple[str, int]]:
    """Legal MIO_PERIPH_INSEL values as (name, bitmask), one per peripheral input.

    A 1 in the bitmask allows muxing the pad with that index to the peripheral input.
    """
    return [(periph["name"], _sel_mask(_pad_indices(periph, n_mio_pads), INSEL_NUM_CONST))
            for periph in mio_periph_ins]


def mio_outsel_legal(mio_pad_names: List[str],
                     mio_periph_outs: List[Dict]) -> List[Tuple[str, int]]:
    """Legal MIO_OUTSEL values as (pad name, bitmask), one per MIO pad.

    A 1 in the bitmask allows muxing the peripheral output with that index to the pad.
    """
    out_pads = [_pad_indices(periph, len(mio_pad_names)) for periph in mio_periph_outs]
    return [(name, _sel_mask([idx for idx, pads in enumerate(out_pads) if pad in pads],
                             OUTSEL_NUM_CONST))
            for pad, name in enumerate(mio_pad_names)]


def gen_index_label(items: List[Tuple], offset: int = 0) -> List[Tuple]:
    """Replace the name of each (name, ...) tuple by a label with the right aligned index of the
    item, starting at offset."""
    width = len(str(max(len(items) + offset - 1, 0)))
    return [(f"{idx + offset:>{width}}: {name}", *rest) for idx, (name, *rest) in enumerate(items)]


def pad_attr_sv(attrs: Dict[str, int]) -> str:
    """Render the attrs of a pad as pad_attr_t constant."""
    members = [f"{PAD_ATTR_FIELDS[field][0]}: {PAD_ATTR_FIELDS[field][1]}'h{value:x}"
               for field, value in attrs.items()]
    return "pad_attr_t'{" + ", ".join(members + ["default: '0"]) + "}"


def sv_hex(value: int, width: int) -> str:
    """Render value as sized SV hex literal."""
    return f"{width}'h{value:0{(width + 3) // 4}x}"


def render_attr_resval(pad_attrs: List[Tuple[str, Dict]], field: str) -> object:
    """Render the reset value of a pad attribute field, indexed per pad if the pads differ."""
    vals = [attrs.get(field, 0) for _, attrs in pad_attrs]
    return vals[0] if len(set(vals)) == 1 else f'"{vals}[multireg_idx]"'
