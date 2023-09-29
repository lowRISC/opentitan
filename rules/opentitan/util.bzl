# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

def get_override(obj, item, overrides):
    """Get an item from obj unless it exists in overrides.

    Args:
      obj: The object holding the item.
      item: An object path to the desired item (ie: `attr.srcs`).
      overrides: A dict that may contain an override named by the last
                 component of the item path (ie: `srcs`).
    """
    items = item.split(".")
    item = items[-1]
    if item in overrides:
        return overrides.get(item)
    for i in items:
        obj = getattr(obj, i)
    return obj

_unbound = struct(unbound = True)

def get_fallback(obj, item, fallback):
    """Get an item from obj and fall back to `fallback` if falsy.

    Args:
      obj: The object holding the item.
      item: An object path to the desired item (ie: `attr.srcs`).
      fallback: An object that contains a fallback value named by the last
                component of the item path (ie: `srcs`).
    """
    items = item.split(".")
    item = items[-1]
    for i in items:
        obj = getattr(obj, i, _unbound)
    if obj and obj != _unbound:
        return obj
    return getattr(fallback, item)

def get_files(attrs):
    """Get the list of files associated with a list of labels.

    Args:
      attrs: a list of labels with DefaultInfo providers.
    Returns:
      List[File]: the files associated with the labels.
    """
    files = []
    for attr in attrs:
        if DefaultInfo in attr:
            files.extend(attr[DefaultInfo].files.to_list())
        else:
            print("No DefaultInfo in ", attr)
    return files
