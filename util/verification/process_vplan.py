#!/usr/bin/env python3
import os
import argparse
import subprocess
from argparse import RawTextHelpFormatter

error_cnt = 0

def run_subprocess(cmd):
    global error_cnt
    result = subprocess.run(cmd)
    if result.returncode != 0:
        error_cnt += 1

def process_hjson(root_dir, hjson_file, demote_error):
    run_subprocess(["./rules_check.py", hjson_file])
    run_subprocess(["./create_tag.py", hjson_file])
    trace_req_cmd = ["./trace_req.py", root_dir, hjson_file]
    if demote_error:
        trace_req_cmd.append("--demote_error")
    run_subprocess(trace_req_cmd)
    run_subprocess(["./hjson2csv.py", hjson_file])


def run_commands(root_dir, vplan_file, demote_error):
    file_ext = os.path.splitext(vplan_file)[1]

    # Check if the vPlan passed as argument is CSV or HJSON
    if file_ext == ".csv":
        hjson_file = vplan_file.replace(".csv", ".hjson")
        run_subprocess(["./csv2hjson.py", vplan_file])
        run_subprocess(["./csv2hjson.py", vplan_file])
        process_hjson(root_dir, hjson_file, demote_error)
    elif file_ext == ".hjson":
        process_hjson(root_dir, vplan_file, demote_error)
    else:
        print("Unsupported file type. Please provide either a .csv or .hjson file.")

def print_subprocess_help(script):
    try:
        result = subprocess.run([script, "--help"], capture_output=True, text=True)
        print(f"----- Help for {script} -----")
        print(result.stdout)
    except FileNotFoundError:
        print(f"Error: {script} not found.")

if __name__ == "__main__":
    parser = argparse.ArgumentParser(
        description='''
                    Run a set of scripts to:
                      - Convert vPlan CSV to HJSON format if the file passed in argument is CSV. Using: csv2hjson.py
                      - Perform checks on the vPlan HJSON format. Execute: rules_check.py, create_tag.py and trace_req.py
                      - Finally, convert the modified HJSON file into CSV format via hjson2csv.py script''',
        formatter_class=RawTextHelpFormatter
    )

    # Required arguments
    parser.add_argument(
        'root_dir',
        type=str,
        help='The path to the root directory of the block/IP. '
             'The sub-directories will be automatically explored except the "dv" folder. '
             'Eg.: hw/ip/block_name'
    )
    parser.add_argument(
        "vplan_file",
        help="Path to the CSV or HJSON file."
    )

    # Optional argument
    parser.add_argument(
        '--demote_error',
        action='store_true',
        help='Print a warning instead of raising an error for missing requirement tags.'
    )
    parser.add_argument(
       "-sh", "--sub_helps",
       action="store_true",
       help='Print help information from all sub-scripts.'
    )

    args = parser.parse_args()

    if args.sub_helps:
        # Print the help of the sub-scripts and exit
        parser.print_help()
        print("\nSub-scripts Help:\n")
        print_subprocess_help("./csv2hjson.py")
        print_subprocess_help("./hjson2csv.py")
        print_subprocess_help("./rules_check.py")
        print_subprocess_help("./create_tag.py")
        print_subprocess_help("./trace_req.py")
    else:
        run_commands(args.root_dir, args.vplan_file, args.demote_error)
        if error_cnt == 0:
            print("\nVerification Plan processed successfully!\n")
        else:
            print("\nFailed to process Verification Plan\n")
