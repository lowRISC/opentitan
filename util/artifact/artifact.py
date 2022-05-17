#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import argparse
import json
import os
import subprocess
import sys

flags = argparse.ArgumentParser(
    description='Query bazel action graph for artifacts')
flags.add_argument('--format',
                   '-f',
                   default='text',
                   choices=['text', 'json', 'filesonly'],
                   help='Output format')
flags.add_argument('--diag',
                   default=False,
                   action='store_true',
                   help='Enable bazel stderr')
flags.add_argument('label',
                   metavar='LABEL',
                   type=str,
                   nargs='+',
                   help='Labels to query')


class QueryError(Exception):
    pass


class ObjectDict(dict):
    """ObjectDict is a `dict` with attribute access to the dictionary contents."""

    def __getattr__(self, name):
        if name in self:
            return self[name]
        else:
            raise AttributeError('No such attribute: ' + name)

    def __setattr__(self, name, value):
        self[name] = value

    def __delattr__(self, name):
        if name in self:
            del self[name]
        else:
            raise AttributeError('No such attribute: ' + name)

    def _get(self, objpath, default=Exception):
        try:
            obj = self
            for k in objpath.split('.'):
                if isinstance(obj, list):
                    obj = obj[int(k)]
                else:
                    obj = obj[k]
            return obj
        except (KeyError, IndexError) as ex:
            if default is Exception:
                raise ex
            return default

    def get(self, objpath, default=None):
        """Get an item by object path.

        Args:
          objpath: str; An object path like 'foo.bar.10.quux'.
          default: object; What to return if the path doesn't exist.
        Returns:
          object
        """
        return self._get(objpath, default)

    def select(self, objpath, **kwargs):
        """Find all items at the given path with matching conditions.

        Args:
          objpath: str; An object path like 'foo.bar.10.quux'.
          kwargs: The match conditions:
            A key=value selects the item at the path where item[key]==value.
            A key=callable selects the item at the path where
                callable(item[key]) returns a truthy value.
        """

        obj = self._get(objpath)
        if not isinstance(obj, list):
            raise QueryError("Object {} is not a list".format(objpath))
        if not kwargs:
            return obj

        result = []
        for o in obj:
            if all(
                    v(o._get(k)) if callable(v) else v == o._get(k)
                    for (k, v) in kwargs.items()):
                result.append(o)
        return result

    def select_one(self, objpath, **kwargs):
        """Find a single item at the given path with matching conditions.
        If no items or more than one item is found, QueryError is raised.
    
        Args:
          objpath: str; An object path like 'foo.bar.10.quux'.
          kwargs: The match conditions:
            A key=value selects the item at the path where item[key]==value.
            A key=callable selects the item at the path where
                callable(item[key]) returns a truthy value.
        """
        result = self.select(objpath, **kwargs)
        if len(result) != 1:
            raise QueryError("Expected exactly 1 of {}, found {}".format(
                objpath, len(result)))
        return result[0]

    @classmethod
    def from_json(cls, text):
        """Create an ObjectDict from the json-encoded `text`."""
        return json.loads(text, object_hook=cls)

    def to_json(self):
        """Serialize this ObjectDict to json."""
        return json.dumps(self, indent=4)


def GetPath(graph, output_id):
    """Reconstruct a path from path fragment IDs."""
    output = graph.select_one('artifacts', id=output_id)
    pf = output.pathFragmentId
    path = []
    while pf:
        fragment = graph.select_one('pathFragments', id=pf)
        path.append(fragment.label)
        pf = fragment.get('parentId')
    return '/'.join(reversed(path))


def Query(label, diag=False):
    """Query the bazel action graph for output filenames associated with a label."""
    bwd = os.environ.get('BUILD_WORKSPACE_DIRECTORY')
    action_graph = subprocess.check_output(
        ['./bazelisk.sh', 'aquery', '--output=jsonproto', label],
        cwd=bwd,
        stderr=None if diag else subprocess.DEVNULL,
        universal_newlines=True)
    graph = ObjectDict.from_json(action_graph)
    target = graph.select_one('targets', label=label)
    action = graph.select_one('actions', targetId=target.id)
    return [GetPath(graph, out) for out in action.outputIds]


def main(argv):
    args = flags.parse_args(argv[1:])
    result = {}
    for target in args.label:
        result[target] = Query(target, args.diag)

    if args.format == 'json':
        print(json.dumps(result, indent=4))
    elif args.format == 'text':
        for target, files in result.items():
            print("{}: {}".format(target, ', '.join(files)))
    elif args.format == 'filesonly':
        for _, files in result.items():
            print(' '.join(files))
    return 0


if __name__ == '__main__':
    sys.exit(main(sys.argv))
