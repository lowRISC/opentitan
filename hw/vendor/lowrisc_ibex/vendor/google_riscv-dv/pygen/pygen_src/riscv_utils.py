"""
Copyright 2020 Google LLC
Copyright 2020 PerfectVIPs Inc.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at
http://www.apache.org/licenses/LICENSE-2.0
Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.

"""
import sys
import logging
import pandas as pd
from tabulate import tabulate
from pygen_src.riscv_instr_gen_config import cfg
from pygen_src.riscv_directed_instr_lib import (riscv_directed_instr_stream,
                                                riscv_int_numeric_corner_stream,
                                                riscv_jal_instr, riscv_mem_access_stream)
from pygen_src.riscv_amo_instr_lib import (riscv_lr_sc_instr_stream, riscv_amo_instr_stream)
from pygen_src.riscv_load_store_instr_lib import (riscv_load_store_rand_instr_stream,
                                                  riscv_load_store_hazard_instr_stream,
                                                  riscv_load_store_stress_instr_stream,
                                                  riscv_single_load_store_instr_stream)


def factory(obj_of):
    objs = {
        "riscv_directed_instr_stream": riscv_directed_instr_stream,
        "riscv_int_numeric_corner_stream": riscv_int_numeric_corner_stream,
        "riscv_jal_instr": riscv_jal_instr,
        "riscv_mem_access_stream": riscv_mem_access_stream,
        "riscv_lr_sc_instr_stream": riscv_lr_sc_instr_stream,
        "riscv_amo_instr_stream": riscv_amo_instr_stream,
        "riscv_load_store_rand_instr_stream": riscv_load_store_rand_instr_stream,
        "riscv_load_store_hazard_instr_stream": riscv_load_store_hazard_instr_stream,
        "riscv_load_store_stress_instr_stream": riscv_load_store_stress_instr_stream,
        "riscv_single_load_store_instr_stream": riscv_single_load_store_instr_stream
    }

    try:
        return objs[obj_of]()
    except KeyError:
        logging.critical("Cannot Create object of %s", obj_of)
        sys.exit(1)


def gen_config_table():
    data = []
    for key, value in cfg.__dict__.items():
        # Ignoring the unneccesary attributes
        if key in ["_ro_int", "_int_field_info", "argv", "mem_region",
                   "amo_region", "s_mem_region", "args_dict"]:
            continue
        else:
            try:  # Fields values for the pyvsc data types
                data.append([key, type(key), sys.getsizeof(key), value.get_val()])
            except Exception:
                data.append([key, type(key), sys.getsizeof(key), value])
    df = pd.DataFrame(data, columns=['Name', 'Type', 'Size', 'Value'])
    df['Value'] = df['Value'].apply(str)
    logging.info('\n' + tabulate(df, headers='keys', tablefmt='psql'))
