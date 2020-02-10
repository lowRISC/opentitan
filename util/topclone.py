#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
r"""Creates a new toplevel target by duplicating hw/top_earlgrey
"""


import argparse
import re,os,sys
import subprocess
import logging as log

from pathlib import Path


def toplevel(astring):
    """argparse validation method for top level name.
    """
    if re.match('top_earlgrey', astring):
        raise argparse.ArgumentTypeError("you must specify a new toplevel name; you gave '-t %s'" % astring)
    
    if not re.match('top_[a-zA-Z0-9_]+', astring):
        raise argparse.ArgumentTypeError("expecting a top level name of the format 'top_{name}'")
    else:
        return astring


def search_and_replace_file(path,top_name,dryrun):
    """parses a file and does a line by line search/replace of any string containing 'earlgrey'.
    """
    log.debug("search_and_replace_file called on path=%s top_name=%s" % (path,top_name))

    # Create a temporary file to capture the search/replace output.
    tmp = path.with_name(path.name + '.tmp')
    
    with path.open() as src:
        with tmp.open(mode='w') as dst:
            for line in src:                
                dst.write(line.replace('earlgrey', top_name))

    if not dryrun:
        tmp.rename(path)


def rename_file_or_dir(path,top):
    """renames a path from top_earlgrey to top_{name}
    """
    new = path.with_name(path.name.replace('top_earlgrey', top))
    log.debug("renaming: old=%s new=%s"%(path,new))
    path.rename(new)
    return new


def rename_files(path,top,dryrun):
    """recursively parses a directory tree and renames all files that contain 'top_earlgrey' to 
    the new toplevel name.  If the Path is a file, also search/replace all instances of 
    'top_earlgrey' within the file.
    """
    log.debug('rename_files called on path=%s' % path)

    for p in path.iterdir():
        if p.is_dir():
            if p.match('*top_earlgrey*'):
                p = rename_file_or_dir(p,top)

            # Recurse...
            rename_files(p,top,dryrun)
        else:
            # Ignore any .tmp files created previously by topclone.py
            if p.suffix != '.tmp':
                # Rename the file if needed
                if p.match('*top_earlgrey*'):
                    p = rename_file_or_dir(p,top)
                    
                # Don't try and open non-text files
                if p.suffix not in ['.svg', '.png']:
                    try:
                        # s/earlgrey/{name}/g
                        top_name = top.split('_')[1]
                        search_and_replace_file(p,top_name,dryrun)
                    except UnicodeDecodeError as e:
                        print("error while trying to parse '%s': %s" % (p,e))
                        sys.exit()
            
    
def main():
    
    parser = argparse.ArgumentParser(description="A tool for creating a new top_level")
    parser.add_argument('-t', '--top', required=True, help="specify the new toplevel name", type = toplevel)
    parser.add_argument('-d', '--dryrun', action='store_true', help="don't actually run the flow; show what will happen")
    parser.add_argument('-v', '--verbose', action='store_true', help="enable verbose logging")
    args = parser.parse_args()

    if args.verbose:
        log.basicConfig(format="%(levelname)s: %(message)s", level=log.DEBUG)
    else:
        log.basicConfig(format="%(levelname)s: %(message)s")

    if args.dryrun:
        log.info("dryrun only, .tmp files will be created but not renamed to the original")

    # Generate the source and destination paths.  The assumption here is that all toplevels
    # reside under the same level of hierarchy $PRJ_DIR/hw/top_<name>
    out_path = Path(__file__).parents[1] / 'hw' / args.top
    src_path = Path(__file__).parents[1] / 'hw/top_earlgrey'

    log.debug("out_path=%s" % out_path)
    log.debug("src_path=%s" % src_path)

    # Create a copy of hw/top_earlgrey by using the git archive command. This means we
    # don't have to keep a running list of the files needed for each new toplevel.
    tar_cmd = "cd %s; git archive master | tar -xf - -C %s"%(src_path,out_path)
    log.debug("tar_cmd=%s" % tar_cmd)
    subprocess.run(tar_cmd,shell=True)

    # Iterate over the new toplevel directory and rename all instances of top_earlgrey to args.top
    rename_files(out_path, args.top, args.dryrun)

    log.info("SUCCESS: created new toplevel; you might want to 'git add %s'"%out_path)
    
main()
