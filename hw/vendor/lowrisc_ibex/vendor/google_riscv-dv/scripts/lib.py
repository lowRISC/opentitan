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

Parse the regression testlist in YAML format
"""

import os
import random
import sys
import subprocess
import time
import yaml
import logging

def setup_logging(verbose):
  """Setup the root logger.

  Args:
    verbose: Verbose logging
  """
  if verbose:
    logging.basicConfig(format="%(asctime)s %(filename)s:%(lineno)-5s %(levelname)-8s %(message)s",
                        datefmt='%a, %d %b %Y %H:%M:%S',
                        level=logging.DEBUG)
  else:
    logging.basicConfig(format="%(asctime)s %(levelname)-8s %(message)s",
                        datefmt='%a, %d %b %Y %H:%M:%S',
                        level=logging.INFO)


def read_yaml(yaml_file):
  """ Read YAML file to a dictionary

  Args:
    yaml_file : YAML file

  Returns:
    yaml_data : data read from YAML in dictionary format
  """
  with open(yaml_file, "r") as f:
    try:
      yaml_data = yaml.safe_load(f)
    except yaml.YAMLError as exc:
      logging.error(exc)
      sys.exit(1)
  return yaml_data


def get_env_var(var):
  """Get the value of environment variable

  Args:
    var : Name of the environment variable

  Returns:
    val : Value of the environment variable
  """
  try:
    val = os.environ[var]
  except KeyError:
    logging.warning("Please set the environment variable %0s" % var)
    sys.exit(1)
  return val


def check_riscv_dv_setting():
  """Check the RISCV-DV directory setting, default "."
  """
  try:
    val = os.environ["RISCV_DV_ROOT"]
  except KeyError:
    os.environ["RISCV_DV_ROOT"] = "."


def get_seed(seed):
  """Get the seed to run the generator

  Args:
    seed : input seed

  Returns:
    seed to run instruction generator
  """
  if seed >= 0:
    return seed
  else:
    return random.getrandbits(32)


def run_cmd(cmd, timeout_s = 999):
  """Run a command and return output

  Args:
    cmd : shell command to run

  Returns:
    command output
  """
  logging.debug(cmd)
  try:
    ps = subprocess.Popen(cmd,
                          shell=True,
                          universal_newlines=True,
                          stdout=subprocess.PIPE,
                          stderr=subprocess.STDOUT)
  except subprocess.CalledProcessError as exc:
    logging.error(ps.communicate()[0])
    sys.exit(1)
  try:
    output = ps.communicate(timeout = timeout_s)[0]
  except subprocess.TimeoutExpired:
    logging.error("Timeout[%ds]: %s" % (timeout_s, cmd))
    output = ""
    ps.kill()
  logging.debug(output)
  return output


def run_parallel_cmd(cmd_list, timeout_s = 999):
  """Run a list of commands in parallel

  Args:
    cmd_list: command list

  Returns:
    command output
  """
  children = []
  for cmd in cmd_list:
    ps = subprocess.Popen(cmd,
                          shell=True,
                          universal_newlines=True,
                          stdout=subprocess.PIPE,
                          stderr=subprocess.STDOUT)
    children.append(ps)
  for i in range(len(children)):
    logging.info("Command progress: %d/%d" % (i, len(children)))
    logging.debug("Waiting for command: %s" % cmd_list[i])
    try:
      output = children[i].communicate(timeout = timeout_s)[0]
    except subprocess.TimeoutExpired:
      logging.error("Timeout[%ds]: %s" % (timeout_s, cmd))
      children[i].kill()
    # Restore stty setting otherwise the terminal may go crazy
    os.system("stty sane")
    logging.debug(output)


def process_regression_list(testlist, test, iterations, matched_list):
  """ Get the matched tests from the regression test list

  Args:
    testlist     : Regression test list
    test         : Test to run, "all" means all tests in the list
    iterations   : Number of iterations for each test

  Returns:
    matched_list : A list of matched tests
  """
  logging.info("Processing regression test list : %s, test: %s" % (testlist, test))
  yaml_data = read_yaml(testlist)
  for entry in yaml_data:
    if (entry['test'] == test) or (test == "all"):
      if (iterations > 0 and  entry['iterations'] > 0):
        entry['iterations'] = iterations
      if entry['iterations'] > 0:
        logging.info("Found matched tests: %s, iterations:%0d" %
                    (entry['test'], entry['iterations']))
        matched_list.append(entry)
