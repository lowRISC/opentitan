# Synopsys VC Z01X Fault Injection Simulation

This tool, which is integrated into OpenTitan, enables users to conduct a pre-silicon fault injection analysis.
During simulation, Z01X injects faults based on user contraints, and compares the golden vs. the faulty model.

## Usage

Z01X proprietary configuration files are available in the [opentitan_fi_z01x](https://github.com/lowRISC/opentitan_fi_z01x) repository.
Please contact [info@lowrisc.org](mailto:info@lowrisc.org?subject=VC-ZOIX%20access) with the email subject: "VC-ZOIX access" to request access to this repository.

Once you have access, follow these steps:
```bash
$ git clone git@github.com:lowRISC/opentitan_fi_z01x.git
$ git clone git@github.com:lowRISC/opentitan.git
$ export Z01X_DIR=<path to the opentitan_fi_z01x directory>
$ export OT_DIR=<path to the opentitan directory>
$ cd opentitan/
$ ./util/prepare_dvsim_z01x.sh
$ ./util/dvsim/dvsim.py hw/top_earlgrey/ip_autogen/flash_ctrl/dv/flash_ctrl_fi_sim_cfg.hjson \
    -i flash_ctrl_basic_rw -t z01x --reseed-multiplier 0.0001 --fixed-seed 1
```
