### dv_base_reg_block
This class extends from uvm_reg_block and is used as the base class of all
auto-generated UVM RAL models for all IPs. This class provides a virtualized
`build(base_addr)` method that is used by the actual derived RAL models to build
the entire RAL structure. An instance of the RAL model is created in `cip_base_cfg`.
The model is however, locked by calling `uvm_reg_block::lock_model()` during
`cip_base_env::end_of_elaboration_phase()` to allow any customizations to
the RAL structures if needed during the`build_phase`.

There are a few enhancement planned in future to this base ral model, that will
automatically be available in the extended IP specific RAL models through
inheritance:
* CSR exclusion automation:
  We will add cip_base_reg and cip_base_field extensions to add attributes that
  can be automated during the IP ral model auto-generation, which can be used to
  exclude certain CSRs and fields from the CSR suite of tests.
* Support parameterized RAL model generation:
  In future, we may have parameterized IPs that will have parameterized number of
  CSRs / fields. Having this base class provides a path to support this.

TODO add description for the other classes

