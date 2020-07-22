# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""Generate SystemVerilog UVM agent extended freom our DV lib
"""

import os

from mako import exceptions
from mako.template import Template
from pkg_resources import resource_filename


def gen_agent(name, has_separate_host_device_driver, root_dir, vendor):
    # set sub name
    agent_dir = root_dir + "/" + name + "_agent"

    # yapf: disable
    # 4-tuple - path, ip name, class name, file ext
    agent_srcs = [(agent_dir,               name + '_', 'if',            '.sv'),
                  (agent_dir,               name + '_', 'item',          '.sv'),
                  (agent_dir,               name + '_', 'agent_cfg',     '.sv'),
                  (agent_dir,               name + '_', 'agent_cov',     '.sv'),
                  (agent_dir,               name + '_', 'monitor',       '.sv'),
                  (agent_dir,               name + '_', 'driver',        '.sv'),
                  (agent_dir,               name + '_', 'host_driver',   '.sv'),
                  (agent_dir,               name + '_', 'device_driver', '.sv'),
                  (agent_dir,               name + '_', 'agent_pkg',     '.sv'),
                  (agent_dir,               name + '_', 'agent',         '.sv'),
                  (agent_dir,               name + '_', 'agent',         '.core'),
                  (agent_dir,               "",         'README',        '.md'),
                  (agent_dir + "/seq_lib",  name + '_', 'seq_list',      '.sv'),
                  (agent_dir + "/seq_lib",  name + '_', 'base_seq',      '.sv')]
    # yapf: enable

    for tup in agent_srcs:
        path_dir = tup[0]
        src_prefix = tup[1]
        src = tup[2]
        src_suffix = tup[3]

        if has_separate_host_device_driver:
            if src == "driver": continue
        else:
            if src == "host_driver": continue
            if src == "device_driver": continue

        ftpl = src + src_suffix + '.tpl'
        fname = src_prefix + src + src_suffix

        # read template
        tpl = Template(filename=resource_filename('uvmdvgen', ftpl))

        if not os.path.exists(path_dir): os.system("mkdir -p " + path_dir)
        with open(path_dir + "/" + fname, 'w') as fout:
            try:
                fout.write(
                    tpl.render(name=name,
                               has_separate_host_device_driver=
                               has_separate_host_device_driver,
                               vendor=vendor))
            except:
                log.error(exceptions.text_error_template().render())
