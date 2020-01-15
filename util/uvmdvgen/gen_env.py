# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""Generate SystemVerilog UVM agent extended freom our DV lib
"""

import os

from mako.template import Template
from pkg_resources import resource_filename


def gen_env(name, is_cip, has_interrupts, has_alerts, env_agents, root_dir,
            add_makefile):
    # yapf: disable
    # 4-tuple - sub-path, ip name, class name, file ext
    env_srcs = [('dv/env',          name + '_', 'env_cfg',            '.sv'),
                ('dv/env',          name + '_', 'env_cov',            '.sv'),
                ('dv/env',          name + '_', 'env_pkg',            '.sv'),
                ('dv/env',          name + '_', 'scoreboard',         '.sv'),
                ('dv/env',          name + '_', 'virtual_sequencer',  '.sv'),
                ('dv/env',          name + '_', 'env',                '.sv'),
                ('dv/env',          name + '_', 'env',                '.core'),
                ('dv/env/seq_lib',  name + '_', 'base_vseq',          '.sv'),
                ('dv/env/seq_lib',  name + '_', 'sanity_vseq',        '.sv'),
                ('dv/env/seq_lib',  name + '_', 'common_vseq',        '.sv'),
                ('dv/env/seq_lib',  name + '_', 'vseq_list',          '.sv'),
                ('dv/tb',           '',         'tb',                 '.sv'),
                ('dv/tb',           name + '_', 'bind',               '.sv'),
                ('dv/tests',        name + '_', 'base_test',          '.sv'),
                ('dv/tests',        name + '_', 'test_pkg',           '.sv'),
                ('dv/tests',        name + '_', 'test',               '.core'),
                ('dv/cov',          '',         '',                   ''),
                ('dv',              '',         'Makefile',           ''),
                ('dv',              name + '_', 'sim_cfg',            '.hjson'),
                ('doc',             name + '_', 'dv_plan',            '.md'),
                ('data',            name + '_', 'testplan',           '.hjson'),
                ('dv',              name + '_', 'sim',                '.core')]
    # yapf: enable

    for tup in env_srcs:
        path_dir = root_dir + '/' + tup[0]
        src_prefix = tup[1]
        src = tup[2]
        src_suffix = tup[3]

        # Skip Makefile
        if src == 'Makefile' and not add_makefile: continue

        ftpl = src + src_suffix + '.tpl'
        fname = src_prefix + src + src_suffix

        if not os.path.exists(path_dir): os.system("mkdir -p " + path_dir)
        if fname == "": continue

        # read template
        tpl = Template(filename=resource_filename('uvmdvgen', ftpl))

        # create rendered file
        with open(path_dir + "/" + fname, 'w') as fout:
            try:
                fout.write(
                    tpl.render(name=name,
                               is_cip=is_cip,
                               has_interrupts=has_interrupts,
                               has_alerts=has_alerts,
                               env_agents=env_agents))
            except:
                log.error(exceptions.text_error_template().render())
