# OTBN Mask Accelerator Interface (MAI) Synthesis Flow

This directory also contains a synthesis flow for the OTBN MAI (mask accelerator and related secure gadgets).
It reuses the same Yosys/sv2v infrastructure described in the main [README](README.md) in this directory.

## Requirements

See the main [README](README.md) for tool requirements (Python 3, sv2v, Yosys, and a standard-cell library in `.lib` format).

## Setup

Copy `syn_setup_mai.example.sh` to `syn_setup_sec_add.sh` and set `LR_SYNTH_CELL_LIBRARY_PATH` to the absolute path of your `.lib` file:

```sh
cp syn_setup_mai.example.sh syn_setup_sec_add.sh
```

`syn_setup_sec_add.sh` is read automatically by `syn_yosys_mai.sh` at runtime and is intentionally excluded from version control (add secrets / local paths there freely).

## Running

```sh
cd hw/ip/otbn/pre_syn
./syn_yosys_mai.sh [TARGET_TYPE]
```

`TARGET_TYPE` selects the top-level module to synthesise (defaults to `mask_accelerator` if omitted):

| `TARGET_TYPE`              | Top module synthesised                             | Notes                                    |
|----------------------------|----------------------------------------------------|------------------------------------------|
| *(default)*                | `otbn_mask_accelerator_sca_wrapper`                | Coco Alma SCA verification wrapper       |
| `mask_accelerator_prolead` | `otbn_mask_accelerator`                            | Direct DUT, no wrapper, use with ProLEAD |
| `sec_add`                  | `otbn_sec_add_sca_wrapper`                         |                                          |
| `sec_add_mod`              | `otbn_sec_add_mod_sca_wrapper`                     |                                          |
| `hpc2` / `hpc2o`           | `prim_hpc2_sca_wrapper` / `prim_hpc2o_sca_wrapper` |                                          |
| `hpc3` / `hpc3o`           | `prim_hpc3_sca_wrapper` / `prim_hpc3o_sca_wrapper` |                                          |

Output lands under `syn_out/<top_module>_<timestamp>/` with the standard directory structure (`generated/`, `reports/`, `log/`).
A `syn_out/latest` symlink is updated to point at the most recent run.

## SCA Tool Integration

The synthesised netlist feeds into two formal SCA verification flows.
See the respective guides for details:

* **Alma** — `pre_sca/alma/README.md`
* **ProLEAD** — `pre_sca/prolead/README.md`
