#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
from fusesoc.capi2.generator import Generator
import os
import subprocess

class LowriscRomGenerator(Generator):
    def run(self):
        rominit = self.config.get('rominit')
        flashinit = self.config.get('flashinit')
        files = []
        cmd = ['make']
        if self.config.get('sim'):
            cmd.append('SIM=1')

        if rominit:
            outfile = os.path.join(rominit, 'rom.vmem')
            cwd = os.path.dirname(__file__)
            build_dir = os.path.abspath(rominit)
            rc = subprocess.call(cmd + ['SW_DIR='+rominit, 'SW_BUILD_DIR='+build_dir, 'clean', 'all'], cwd=cwd)
            if rc:
                exit(1)
            files.append({outfile : {'file_type' : 'user'}})
            self.add_parameter('rominit',
                               {'datatype' : 'file',
                                'default' : os.path.join(build_dir, 'rom.vmem'),
                                'paramtype' : 'cmdlinearg'})
        if flashinit:
            outfile = os.path.join(flashinit, 'sw.vmem')
            cwd = os.path.dirname(__file__)
            build_dir = os.path.abspath(flashinit)
            rc = subprocess.call(cmd + ['SW_DIR='+flashinit, 'SW_BUILD_DIR='+build_dir, 'clean', 'all'], cwd=cwd)
            if rc:
                exit(1)
            files.append({outfile : {'file_type' : 'user'}})
            self.add_parameter('flashinit',
                               {'datatype' : 'file',
                                'default' : os.path.join(build_dir, 'sw.vmem'),
                                'paramtype' : 'cmdlinearg'})

        if not 'default' in self.targets:
            self.targets['default'] = {}
        if not 'filesets' in self.targets['default']:
            self.targets['default']['filesets'] = []
        self.add_files(files)

g = LowriscRomGenerator()
g.run()
g.write()
