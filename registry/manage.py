#!/usr/bin/env python3
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""Management script for the custom Bazel registry."""

import argparse
import logging
import json
from pathlib import Path
import requests
import sys
from collections import OrderedDict
import hashlib
import base64
import re
import tempfile
import mimetypes
import tarfile

REGISTRY_PATH = Path(__file__).parent
BCR_URL = "https://bcr.bazel.build/"


def download_text_file(url, err_msg):
    logging.debug(f"Downloading {url}")
    req = requests.get(url)
    logging.debug(f"Result: {req}")
    if req.status_code != 200:
        logging.error(err_msg)
        sys.exit(1)
    return req.text


def download_to_file(url, err_msg):
    logging.debug(f"Downloading {url}")
    req = requests.get(url, stream=True)
    logging.debug(f"Result: {req}")
    if req.status_code != 200:
        logging.error(err_msg)
        sys.exit(1)
    f = tempfile.TemporaryFile()
    for chunk in req.iter_content(chunk_size=10_000_000):
        f.write(chunk)
    logging.debug("Done")
    f.seek(0)
    return f


def extract_from_archive(fileobj, url, strip_prefix, filename):
    strip_prefix = Path(strip_prefix)
    filename = Path(filename)
    # Guess the type of the archive from the url
    (archive_type, _) = mimetypes.guess_type(url)
    if archive_type is None:
        logging.error(f"Cannot determine archive format from URL {url}")
        return None
    if archive_type == "application/x-tar":
        # The tarfile constructor assumes that the file object is at the beginning.
        fileobj.seek(0)
        tar = tarfile.open(fileobj = fileobj)
        matched_tarinfo = None
        for tarinfo in tar:
            logging.debug(f"Archive contains file {tarinfo.name}")
            name = Path(tarinfo.name)
            # Try to strip the prefix, otherwise keep as-is
            try:
                name = name.relative_to(strip_prefix)
            except ValueError:
                pass
            # Is that a match?
            if name == filename:
                if matched_tarinfo:
                    logging.error(f"There are more than one matches for {filename} in {url} \
                                  [strip prefix {strip_prefix}")
                    return None
                matched_tarinfo = tarinfo
        # Did we find it ?
        if not matched_tarinfo:
            logging.error(f"File {filename} not found in {url} [strip prefix {strip_prefix}")
            return None
        logging.debug(f"Matched {filename} to {matched_tarinfo.name} in archive")
        subfileobj = tar.extractfile(matched_tarinfo)
        return subfileobj.read()
    else:
        logging.error(f"Unsupported archive type {archive_type}")
        return None


def parse_json(json_text):
    # Make sure to preserve the order.
    return json.loads(json_text, object_pairs_hook=OrderedDict)


def dump_json(obj):
    return json.dumps(obj, indent = 4) + "\n"


def create_empty_metadata(metadata_json_path):
    logging.debug("Creating the {} directory...".format(metadata_json_path.parent))
    metadata_json_path.parent.mkdir(parents = True, exist_ok = True)
    # Empty metadata
    metadata_json = {
        'versions': [],
        'yanked_versions': {},
    }
    metadata_json_path.write_text(dump_json(metadata_json))


def do_add_module(mod_name, mod_ver, source_json, module_bazel):
    # Create module metadata if necessary
    metadata_json_path = REGISTRY_PATH / "modules" / mod_name / "metadata.json"
    if not metadata_json_path.exists():
        logging.info(f"Module {mod_name} does not exist yet in the registry, creating an empty entry...")  # noqa:E501
        create_empty_metadata(metadata_json_path)

    # Load the metadata
    logging.info(f"Loading module {mod_name} metadata")
    metadata_json = parse_json(metadata_json_path.read_text())

    # Make sure that this version does not already exists
    if mod_ver in metadata_json["versions"]:
        logging.error(f"Registry already contains module {mod_name} version {mod_ver}")
        sys.exit(1)

    # Create directory if necessary
    mod_dir = REGISTRY_PATH / "modules" / mod_name / mod_ver
    mod_dir.mkdir(exist_ok = True)

    # Create source.json file
    source_json_path = mod_dir / "source.json"
    if source_json_path.exists():
        logging.error(f"Registry already contains file {source_json_path}, will not overwrite")
        sys.exit(1)
    source_json_path.write_text(dump_json(source_json))

    # Create MODULE.bazel file
    module_bazel_path = mod_dir / "MODULE.bazel"
    if module_bazel_path.exists():
        logging.error(f"Registry already contains file {module_bazel_path}, will not overwrite")
        sys.exit(1)
    module_bazel_path.write_text(module_bazel)

    # Download patches if necessary
    patches = source_json.get('patches', {})
    if patches:
        (mod_dir / "patches").mkdir(exist_ok = True)
    for patch_name in patches:
        # FIXME: might be a good idea to validate patch_name to avoid attacks from ill-formed names
        patch_text = download_text_file(
            f"{BCR_URL}/modules/{mod_name}/{mod_ver}/patches/{patch_name}",
            f"Could not download patch {patch_name} for {mod_name}/{mod_ver}"
        )
        patch_path = mod_dir / "patches" / patch_name
        if patch_path.exists():
            logging.error(f"Registry already contains patch {patch_path}, will not overwrite")
            sys.exit(1)
        patch_path.write_text(patch_text)

    # Edit metadata
    metadata_json["versions"].append(mod_ver)
    metadata_json_path.write_text(dump_json(metadata_json))


def add_module(args):
    # Sanioty check
    if args.strip_prefix and not args.url:
        logging.error("--strip-prefix is only valid when used with --url")
        sys.exit(1)

    mod_name = args.module_name
    mod_ver = args.module_version
    # Create the URL and see if we can find the metadata.json file
    logging.info(f"Getting module {mod_name} metadata...")

    # If no URL is provided, look up the module on the BCR:
    if not args.url:
        metadata_json = download_text_file(
            f"{BCR_URL}/modules/{mod_name}/metadata.json",
            f"Module {mod_name} not found on the BCR")
        # TODO capture errors
        metadata_json = parse_json(metadata_json)

        # Check if the requested version exists
        if args.module_version not in metadata_json["versions"]:
            logging.info("Module {} has versions: {}".format(mod_name, metadata_json["versions"]))
            logging.error(f"Module {mod_name} has no version {mod_ver} in the BCR")
            sys.exit(1)
        # Warn about yanked versions
        if args.module_version in metadata_json["yanked_versions"]:
            logging.warning("Module {} version {} is yanked due to the following reason: {}".format(
                mod_name, mod_ver, metadata_json["yanked_versions"][args.module_version]))

        # Download source.json
        logging.info(f"Getting module {mod_name}/{mod_ver} information...")
        source_json = download_text_file(
            f"{BCR_URL}/modules/{mod_name}/{mod_ver}/source.json",
            f"Could not download information for {mod_name}/{mod_ver}"
        )
        # TODO capture errors
        source_json = parse_json(source_json)

        # Download MODULE.bazel
        logging.info(f"Getting module {mod_name}/{mod_ver} module file...")
        module_bazel = download_text_file(
            f"{BCR_URL}/modules/{mod_name}/{mod_ver}/MODULE.bazel",
            f"Could not download module file for {mod_name}/{mod_ver}"
        )
    else:
        strip_prefix = args.strip_prefix or ""
        # Download the archive, this is necessary so that we can compute the integrity hash and
        # extract the MODULE.bazel file
        archive = download_to_file(args.url, "URL {args.url} is not valid")

        # Compute archive integrity
        archive.seek(0)
        h = hashlib.file_digest(archive, "sha256")
        archive_integrity = "sha256-{}".format(base64.b64encode(h.digest()).decode('utf-8'))
        logging.info(f"Archive integrity is {archive_integrity}")

        module_bazel = extract_from_archive(archive, args.url, strip_prefix, "MODULE.bazel")
        if module_bazel is None:
            logging.error("Failed to extract MODULE.bazel from archive")
            sys.exit(1)
        module_bazel = module_bazel.decode('utf-8')

        # Create a minimal source.json file
        source_json = {
            "integrity": archive_integrity,
            "strip_prefix": strip_prefix,
            "url": args.url,
        }

    do_add_module(mod_name, mod_ver, source_json, module_bazel)


def remove_module(args):
    mod_name = args.module_name
    mod_ver = args.module_version
    # Load metadata.json
    metadata_json_path = REGISTRY_PATH / "modules" / mod_name / "metadata.json"
    if not metadata_json_path.exists():
        logging.error(f"Module {mod_name} does not exist in the registry")
        sys.exit(1)

    # Load the metadata
    logging.info(f"Loading module {mod_name} metadata")
    metadata_json = parse_json(metadata_json_path.read_text())

    # Make sure that this version already exists.
    if mod_ver not in metadata_json["versions"]:
        logging.error(f"Registry does not contains module {mod_name} version {mod_ver}")
        sys.exit(1)

    # Remove version and write back.
    metadata_json["versions"].remove(mod_ver)
    metadata_json_path.write_text(dump_json(metadata_json))

    print("You can now remove the directory {}".format(
        REGISTRY_PATH / "modules" / mod_name / mod_ver
    ))


def change_strip_level(patch_content, strip_delta):
    # Assume patch is encoded using UTF-8.
    patch_content = patch_content.decode()

    # Edit all paths. Note that this regex does not work if any of the paths
    # contains a space.
    def fix_path(match):
        parts = Path(match.group(2)).parts
        print(f"old parts: {parts}")
        if strip_delta < 0:
            parts = parts[-strip_delta:]
        else:
            parts = tuple(["ignored"] * strip_delta) + parts
        print(f"new parts: {parts}")
        return "{} {}".format(match.group(1), Path(*parts))

    patch_content = re.sub(
        r'^(\+\+\+|---) ([\S]+)',
        fix_path,
        patch_content,
        flags = re.MULTILINE,
    )
    return patch_content.encode()


def do_add_module_patch(mod_name, mod_ver, patch_path, patch_strip):
    if not patch_path.exists():
        logging.error(f"Could not find patch file at {patch_path}")
        sys.exit(1)
    # Load source.json
    source_json_path = REGISTRY_PATH / "modules" / mod_name / mod_ver / "source.json"
    if not source_json_path.exists():
        logging.error(f"Registry does not contains module {mod_name} version {mod_ver}")
        sys.exit(1)
    source_json = parse_json(source_json_path.read_text())

    # Extract patch strip if specified. If it is not specified, the simplest
    # solution is to directly write the requested level to avoid changing the patch.
    if 'patch_strip' not in source_json:
        logging.debug("Registry does not specified strip patch level, " +
                      f"using the one from the specified patch ({patch_strip})")
        source_json['patch_strip'] = str(patch_strip)
    target_patch_strip = int(source_json.get('patch_strip'))

    mod_dir = REGISTRY_PATH / "modules" / mod_name / mod_ver
    # Copy file to patches directory
    (mod_dir / "patches").mkdir(exist_ok = True)
    patch_name = patch_path.name
    patch_content = patch_path.read_bytes()
    if target_patch_strip != patch_strip:
        patch_content = change_strip_level(patch_content, target_patch_strip - patch_strip)
    (mod_dir / "patches" / patch_name).write_bytes(patch_content)

    # Compute digest
    h = hashlib.sha256()
    h.update(patch_content)
    patch_integrity = "sha256-{}".format(base64.b64encode(h.digest()).decode('utf-8'))

    # Add entry to the json information
    source_json['patches'] = source_json.get('patches', {}) \
        | OrderedDict([(patch_name, patch_integrity)])
    source_json_path.write_text(dump_json(source_json))


def add_module_patch(args):
    do_add_module_patch(args.module_name, args.module_version, Path(args.patch), args.strip)


def nothing_to_do(args):
    print("nothing to do!")


def main():
    parser = argparse.ArgumentParser(prog="manage_registry")
    parser.add_argument('-v', '--verbose', action="count", default=0)
    subparsers = parser.add_subparsers()
    parser.set_defaults(func=nothing_to_do)
    # "add-module" subparser
    module_add_parser = subparsers.add_parser(
        'add-module',
        help='add module from the BCR or an archive'
    )
    module_add_parser.add_argument('module_name', help='module name')
    module_add_parser.add_argument('module_version', help='module version')
    module_add_parser.add_argument(
        '--url',
        help='use the provided URL instead of looking in the BCR'
    )
    module_add_parser.add_argument(
        '--strip-prefix',
        help='Prefix to strip from the archive. Only valid when a URL is provided using --url'
    )
    module_add_parser.set_defaults(func=add_module)
    # "remove-module" subparser
    module_add_parser = subparsers.add_parser('remove-module', help='remove module from the BCR')
    module_add_parser.add_argument('module_name', help='module name')
    module_add_parser.add_argument('module_version', help='module version')
    module_add_parser.set_defaults(func=remove_module)
    # "add-module-patch" subparser
    module_add_parser = subparsers.add_parser('add-module-patch', help='add a patch to a module')
    module_add_parser.add_argument('module_name', help='module name')
    module_add_parser.add_argument('module_version', help='module version')
    module_add_parser.add_argument('patch', help='patch file')
    module_add_parser.add_argument(
        '--strip', type=int, default=0,
        help='how many path levels to strip from the patch (default is 0)'
    )
    module_add_parser.set_defaults(func=add_module_patch)

    args = parser.parse_args()
    if args.verbose >= 2:
        log_level = logging.DEBUG
    elif args.verbose >= 1:
        log_level = logging.INFO
    else:
        log_level = logging.WARNING
    logging.basicConfig(format="%(filename)s:%(lineno)d: %(levelname)s: %(message)s",
                        level=log_level)

    args.func(args)


if __name__ == "__main__":
    main()
