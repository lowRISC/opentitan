"""
Copyright 2019 Google LLC

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

Regression script for RISC-V random instruction generator
"""

import argparse
import os
import re
import sys
import logging

from scripts.lib import *
from scripts.spike_log_to_trace_csv import *
from scripts.ovpsim_log_to_trace_csv import *
from scripts.sail_log_to_trace_csv import *
from types import SimpleNamespace

LOGGER = logging.getLogger()


def build_cov(out, cfg, cwd, opts_vec, opts_cov):
    """Building the coverage collection framework

    Args:
      out                 : Output directory
      cfg                 : Loaded configuration dictionary.
      cwd                 : Filesystem path to RISCV-DV repo
      opts_vec            : Vector options
      opts_cov            : Coverage options
    """
    # Convert key dictionary to argv variable
    argv = SimpleNamespace(**cfg)
    logging.info("Building the coverage collection framework")
    build_cmd = ("python3 {}/run.py --simulator {} --simulator_yaml {} "
                 " --co -o {} --cov -tl {} {} --cmp_opts \"{} {}\" --noclean".format(
        cwd, argv.simulator, argv.simulator_yaml, out,
        argv.testlist, argv.opts, opts_vec, opts_cov))
    if argv.target:
        build_cmd += (" --target {}".format(argv.target))
    if argv.custom_target:
        build_cmd += (" --custom_target {}".format(argv.custom_target))
    if argv.stop_on_first_error:
        build_cmd += " --stop_on_first_error"
    if argv.lsf_cmd != "":
        build_cmd += (" --lsf_cmd \"{}\"".format(argv.lsf_cmd))
        run_parallel_cmd([build_cmd], argv.timeout, debug_cmd=argv.debug)
    else:
        run_cmd(build_cmd, debug_cmd=argv.debug)


def sim_cov(out, cfg, cwd, opts_vec, opts_cov, csv_list):
    """Simulation the coverage collection

    Args:
      out                 : Output directory
      cfg                 : Loaded configuration dictionary.
      cwd                 : Filesystem path to RISCV-DV repo
      opts_vec            : Vector options
      opts_cov            : Coverage options
      csv_list            : The list of trace csv
    """
    # Convert key dictionary to argv variable
    argv = SimpleNamespace(**cfg)
    logging.info(
        "Collecting functional coverage from {} trace CSV".format(len(csv_list)))
    test_name = "riscv_instr_cov_test"
    base_sim_cmd = (
        "python3 {}/run.py --simulator {} --simulator_yaml {} --noclean "
        "--so -o {} --cov -tl {} {} "
        "-tn {} --steps gen --sim_opts \"<trace_csv_opts> {} {} <visualization>\" "
            .format(cwd, argv.simulator, argv.simulator_yaml, out,
                    argv.testlist,
                    argv.opts, test_name, opts_vec, opts_cov))
    if argv.simulator == "pyflow" and argv.enable_visualization:
        base_sim_cmd = re.sub("<visualization>", "--enable_visualization",
                              base_sim_cmd)
    else:
        base_sim_cmd = re.sub("<visualization>", "", base_sim_cmd)
    if argv.target:
        base_sim_cmd += (" --target {}".format(argv.target))
    if argv.custom_target:
        base_sim_cmd += (" --custom_target {}".format(argv.custom_target))
    if argv.stop_on_first_error:
        base_sim_cmd += " --stop_on_first_error"
    trace_csv_opts = ""
    batch_cnt = 1
    sim_cmd_list = []
    if argv.batch_size > 0:
        batch_cnt = (len(csv_list) + argv.batch_size - 1) / argv.batch_size
        logging.info(
            "Batch size: {}, Batch cnt: {}".format(argv.batch_size, batch_cnt))
    for i in range(len(csv_list)):
        file_idx = 0
        trace_idx = i
        if argv.batch_size > 0:
            file_idx = i / argv.batch_size
            trace_idx = i % argv.batch_size
        if argv.simulator == "pyflow":
            if i == 0:
                trace_csv_opts += (" --trace_csv={}".format(csv_list[i]))
            else:
                trace_csv_opts += (",{}".format(csv_list[i]))
        else:
            trace_csv_opts += (" +trace_csv_{}={}".format(trace_idx, csv_list[i]))
        if (i == len(csv_list) - 1) or (
                (argv.batch_size > 0) and (trace_idx == argv.batch_size - 1)):
            sim_cmd = base_sim_cmd.replace("<trace_csv_opts>", trace_csv_opts)
            sim_cmd += ("  --log_suffix _{}".format(file_idx))
            if argv.lsf_cmd == "":
                logging.info(
                    "Processing batch {}/{}".format(file_idx + 1, batch_cnt))
                run_cmd(sim_cmd, debug_cmd=argv.debug)
            else:
                sim_cmd += (" --lsf_cmd \"{}\"".format(argv.lsf_cmd))
                sim_cmd_list.append(sim_cmd)
            trace_csv_opts = ""
    if argv.lsf_cmd != "":
        run_parallel_cmd(sim_cmd_list, argv.timeout)
    logging.info(
        "Collecting functional coverage from {} trace CSV...done".format(len(
            csv_list)))


def collect_cov(out, cfg, cwd):
    """Collect functional coverage from the instruction trace

    Args:
      out              : Output directory
      cfg              : Loaded configuration dictionary.
      cwd              : Filesystem path to RISCV-DV repo
    """
    # Convert key dictionary to argv variable
    argv = SimpleNamespace(**cfg)
    log_list = []
    csv_list = []
    if not argv.dir:
        logging.error("Missing directory of trace log files")
        sys.exit(RET_FAIL)
    logging.info("Processing trace log under {}".format(argv.dir))
    if not os.path.isdir(argv.dir) or not os.listdir(argv.dir):
        if not argv.debug:
            logging.error("Cannot find {} directory, or it is empty".format(argv.dir))
            sys.exit(RET_FAIL)
    if argv.core:
        """If functional coverage is being collected from an RTL core 
        implementation, the flow assumes that the core's trace logs have 
        already been converted to CSV files by the post_compare step of the 
        flow. """
        trace_log = ("{}/{}_trace_log".format(out, argv.core))
        run_cmd("find {} -name \"*.csv\" | sort > {}".format(argv.dir, trace_log))
    else:
        trace_log = ("{}/{}_trace_log".format(out, argv.iss))
        run_cmd("find {} -name \"*.log\" | sort > {}".format(argv.dir, trace_log))
    with open(trace_log) as f:
        for line in f:
            line = line.rstrip()
            log_list.append(line)
            csv = line[0:-4] + ".csv"
            csv_list.append(csv)
    if argv.steps == "all" or re.match("csv", argv.steps):
        for i in range(len(log_list)):
            log = log_list[i]
            csv = csv_list[i]
            # If a core target is defined, prioritize over ISS
            if argv.core:
                logging.info("Process {} log[{}/{}] : {}".format(
                    argv.core, i + 1, len(log_list), log))
            else:
                logging.info("Process {} log[{}/{}] : {}".format(
                    argv.iss, i + 1, len(log_list), log))
                if argv.iss == "spike":
                    process_spike_sim_log(log, csv, 1)
                elif argv.iss == "ovpsim":
                    process_ovpsim_sim_log(log, csv, argv.stop_on_first_error,
                                           argv.dont_truncate_after_first_ecall,
                                           1)
                else:
                    logging.error(
                        "Full trace for {} is not supported yet".format(argv.iss))
                    sys.exit(RET_FAIL)
    if argv.steps == "all" or re.match("cov", argv.steps):
        opts_vec = ""
        opts_cov = ""
        if argv.vector_options:
            opts_vec = ("{}".format(argv.vector_options))
        if argv.coverage_options:
            opts_cov = ("{}".format(argv.coverage_options))
        if argv.compliance_mode:
            opts_cov += " +define+COMPLIANCE_MODE"
        # Building the coverage collection framework
        if argv.simulator != "pyflow":
            build_cov(out, cfg, cwd, opts_vec, opts_cov)
        # Simulation the coverage collection
        sim_cov(out, cfg, cwd, opts_vec, opts_cov, csv_list)


def setup_parser():
    """Create a command line parser.

    Returns: The created parser.
    """
    # Parse input arguments
    parser = argparse.ArgumentParser()
    parser.add_argument("-o", "--output", type=str,
                        help="Output directory name", dest="o")
    parser.add_argument("-v", "--verbose", dest="verbose", action="store_true",
                        default=False,
                        help="Verbose logging")
    parser.add_argument("--dir", type=str,
                        help="Directory of trace log files")
    parser.add_argument("-bz", "--batch_size", dest="batch_size", type=int,
                        default=0,
                        help="Number of CSV to process per run")
    parser.add_argument("--compliance_mode", action="store_true", default=False,
                        help="Run the coverage model in compliance test mode")
    parser.add_argument("-i", "--instr_cnt", dest="instr_cnt", type=int,
                        default=0,
                        help="Random instruction count for debug mode")
    parser.add_argument("-to", "--timeout", dest="timeout", type=int,
                        default=1000,
                        help="Number of CSV to process per run")
    parser.add_argument("-s", "--steps", type=str, default="all",
                        help="Run steps: csv,cov", dest="steps")
    parser.add_argument("--core", type=str, default="",
                        help="Name of target core")
    parser.add_argument("--isa", type=str, default="",
                        help="RISC-V ISA variant")
    parser.add_argument("--iss", type=str, default="spike",
                        help="RISC-V instruction set simulator: spike,ovpsim,sail")
    parser.add_argument("-tl", "--testlist", type=str, default="",
                        help="Regression testlist", dest="testlist")
    parser.add_argument("--opts", type=str, default="",
                        help="Additional options for the instruction generator")
    parser.add_argument("--lsf_cmd", type=str, default="",
                        help="LSF command. Run in local sequentially if lsf \
                            command is not specified")
    parser.add_argument("--target", type=str, default="rv32imc",
                        help="Run the generator with pre-defined targets: \
                            rv32imc, rv32i, rv64imc, rv64gc")
    parser.add_argument("-si", "--simulator", type=str, default="vcs",
                        help="Simulator used to run the generator, \
                            default VCS", dest="simulator")
    parser.add_argument("--simulator_yaml", type=str, default="",
                        help="RTL simulator setting YAML")
    parser.add_argument("-ct", "--custom_target", type=str, default="",
                        help="Directory name of the custom target")
    parser.add_argument("-cs", "--core_setting_dir", type=str, default="",
                        help="Path for the riscv_core_setting.sv")
    parser.add_argument("--stop_on_first_error", dest="stop_on_first_error",
                        action="store_true", default=False,
                        help="Stop on detecting first error")
    parser.add_argument("--dont_truncate_after_first_ecall",
                        dest="dont_truncate_after_first_ecall",
                        action="store_true", default=False,
                        help="Do not truncate log and csv file on first ecall")
    parser.add_argument("--noclean", action="store_true", default=False,
                        help="Do not clean the output of the previous runs")
    parser.add_argument("--vector_options", type=str, default="",
                        help="Enable Vectors and set options")
    parser.add_argument("--coverage_options", type=str, default="",
                        help="Controlling coverage coverpoints")
    parser.add_argument("--exp", action="store_true", default=False,
                        help="Run generator with experimental features")
    parser.add_argument("-d", "--debug", type=str, default="",
                        help="Generate debug command log file")
    parser.add_argument("--enable_visualization", action="store_true",
                        default=False,
                        help="Enabling coverage report visualization for pyflow")
    return parser


def load_config(args, cwd):
    """
    Load configuration from the command line and the configuration file.

    Args:
        args:   Parsed command-line configuration
    Returns:
        Loaded configuration dictionary.
    """
    if args.debug:
        args.debug = open(args.debug, "w")
    if args.verbose:
        args.opts += "-v"

    if not args.simulator_yaml:
        args.simulator_yaml = cwd + "/yaml/simulator.yaml"

    # Disable ISS coverage if a core is passed in
    if args.core:
        args.iss = ""

    # Keep the core_setting_dir option to be backward compatible, suggest to use
    # --custom_target
    if args.core_setting_dir:
        if not args.custom_target:
            args.custom_target = args.core_setting_dir
    else:
        args.core_setting_dir = args.custom_target

    if not args.custom_target:
        args.core_setting_dir = cwd + "/target/" + args.target

    args.testlist = cwd + "/yaml/cov_testlist.yaml"  ## needed if need to force
    # Create loaded configuration dictionary.
    cfg = vars(args)
    return cfg


def main():
    """This is the main entry point."""
    try:
        parser = setup_parser()
        args = parser.parse_args()
        cwd = os.path.dirname(os.path.realpath(__file__))
        setup_logging(args.verbose)
        # Load configuration from the command line and the configuration file.
        cfg = load_config(args, cwd)
        # Create output directory
        output_dir = create_output(args.o, args.noclean, "cov_out_")
        # Collect coverage for the trace CSV
        collect_cov(output_dir, cfg, cwd)
        logging.info("Coverage results are saved to {}".format(output_dir))
        sys.exit(RET_SUCCESS)
    except KeyboardInterrupt:
        logging.info("\nExited Ctrl-C from user request.")
        sys.exit(130)


if __name__ == "__main__":
    main()
