import logging
import os
import sys

_THIS_DIR = os.path.normpath(os.path.join(os.path.dirname(__file__)))
_IBEX_ROOT = os.path.normpath(os.path.join(_THIS_DIR, '../../../..'))
_RISCV_DV_ROOT = os.path.join(_IBEX_ROOT, 'vendor/google_riscv-dv')
_OLD_SYS_PATH = sys.path

# Import lib from _DV_SCRIPTS before putting sys.path back as it started.
try:
    sys.path = [os.path.join(_RISCV_DV_ROOT, 'scripts')] + sys.path
    from lib import read_yaml
finally:
    sys.path = _OLD_SYS_PATH


def subst_opt(string, name, enable, replacement):
    '''Substitute the <name> option in string

    If enable is False, <name> is replaced by '' in string. If it is True,
    <name> is replaced by replacement, which should be a string or None. If
    replacement is None and <name> occurs in string, we throw an error.

    '''
    needle = '<{}>'.format(name)
    if not enable:
        return string.replace(needle, '')

    if replacement is None:
        if needle in string:
            raise RuntimeError('No replacement defined for {} '
                               '(used in string: {!r}).'
                               .format(needle, string))
        return string

    return string.replace(needle, replacement)


def subst_env_vars(string, env_vars):
    '''Substitute environment variables in string

    env_vars should be a string with a comma-separated list of environment
    variables to substitute. For each environment variable, V, in the list, any
    occurrence of <V> in string will be replaced by the value of the
    environment variable with that name. If <V> occurs in the string but $V is
    not set in the environment, an error is raised.

    '''
    env_vars = env_vars.strip()
    if not env_vars:
        return string

    for env_var in env_vars.split(','):
        env_var = env_var.strip()
        needle = '<{}>'.format(env_var)
        if needle in string:
            value = os.environ.get(env_var)
            if value is None:
                raise RuntimeError('Cannot substitute {} in command because '
                                   'the environment variable ${} is not set.'
                                   .format(needle, env_var))
            string = string.replace(needle, value)

    return string


def subst_cmd(cmd, enable_dict, opts_dict, env_vars):
    '''Substitute options and environment variables in cmd

    enable_dict should be a dict mapping names to bools. For each key, N, in
    enable_dict, if enable_dict[N] is False, then all occurrences of <N> in cmd
    will be replaced with ''. If enable_dict[N] is True, all occurrences of <N>
    in cmd will be replaced with opts_dict[N].

    If N is not a key in opts_dict, this is no problem unless cmd contains
    <N>, in which case we throw a RuntimeError.

    Finally, the environment variables are substituted as described in
    subst_env_vars and any newlines are stripped out.

    '''
    for name, enable in enable_dict.items():
        cmd = subst_opt(cmd, name, enable, opts_dict.get(name))

    return subst_env_vars(cmd, env_vars).replace('\n', ' ')


def get_yaml_for_simulator(simulator):
    '''Get the entry for the simulator in RTL simulation yaml'''
    yaml_dir = os.path.normpath(os.path.join(_THIS_DIR, '../yaml'))
    yaml_path = os.path.join(yaml_dir, 'rtl_simulation.yaml')

    logging.info("Processing simulator setup file : %s" % yaml_path)
    for entry in read_yaml(yaml_path):
        if entry.get('tool') == simulator:
            return entry

    raise RuntimeError("Cannot find RTL simulator {}".format(simulator))


def get_simulator_cmd(simulator, enables):
    '''Get compile and run commands for the testbench

    simulator is the name of the simulator to use. enables is a dictionary
    keyed by option names with boolean values: true if the option is enabled.

    Returns (compile_cmds, sim_cmd), which are the simulator commands to
    compile and run the testbench, respectively. compile_cmd is a list of
    strings (multiple commands); sim_cmd is a single string.

    '''
    entry = get_yaml_for_simulator(simulator)
    env_vars = entry.get('env_var', '')

    return ([subst_cmd(arg, enables, entry['compile'], env_vars)
             for arg in entry['compile']['cmd']],
            subst_cmd(entry['sim']['cmd'], enables, entry['sim'], env_vars))
