/*
 * Copyright 2018 Google LLC
 * Copyright 2022 Coverify Systems Technology
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

//-----------------------------------------------------------------------------
// RISC-V assembly program generator configuration class
//-----------------------------------------------------------------------------
module riscv.gen.riscv_instr_registry;

import riscv.gen.riscv_instr_gen_config: riscv_instr_gen_config;
import riscv.gen.isa.riscv_instr: riscv_instr;
import riscv.gen.riscv_instr_pkg: riscv_instr_name_t, riscv_instr_group_t,
  riscv_instr_category_t, privileged_reg_t, riscv_reg_t, privileged_mode_t;
import riscv.gen.target: unsupported_instr, supported_isa,
  implemented_csr, XLEN;

import std.format: format;
import std.algorithm: canFind, remove;
import std.traits: EnumMembers;

import esdl.base.rand: urandom;

import uvm;

class riscv_instr_registry: uvm_object
{
  mixin uvm_object_utils;

  // All derived instructions
  string[riscv_instr_name_t]                    instr_registry;

  // Instruction list
  riscv_instr_name_t[]                          instr_names;

  // Categorized instruction list
  riscv_instr_name_t[][riscv_instr_group_t]     instr_group;
  riscv_instr_name_t[][riscv_instr_category_t]  instr_category;
  riscv_instr_name_t[]                          basic_instr;
  riscv_instr[riscv_instr_name_t]               instr_template;

  // Privileged CSR filter
  privileged_reg_t[]                            exclude_reg;
  privileged_reg_t[]                            include_reg;

  riscv_instr_gen_config                        cfg;

  this (string name="") {
    super(name);
  }

  void set_cfg(riscv_instr_gen_config cfg) {
    this.cfg = cfg;
  }

  bool register(riscv_instr_name_t instr_name, string qualified_name) {
    uvm_info("riscv_instr", format("Registering %0s", instr_name), UVM_LOW);
    instr_registry[instr_name] = qualified_name;
    return true;
  }

  // Create the list of instructions based on the supported ISA extensions and configuration of the
  // generator.
  void create_instr_list(riscv_instr_gen_config cfg) {
    assert (cfg !is null);
    instr_names.length = 0;
    // instr_group.clear();
    foreach (group; [EnumMembers!riscv_instr_group_t]) instr_group[group] = [];
    // instr_category.clear();
    foreach (category; [EnumMembers!riscv_instr_category_t]) instr_category[category] = [];
    foreach (instr_name, instr_class_name; instr_registry) {
      riscv_instr instr_inst;
      if (canFind(unsupported_instr, instr_name)) continue;
      instr_inst = create_instr(instr_name, instr_class_name);
      instr_inst.m_cfg = cfg;
      instr_template[instr_name] = instr_inst;
      if (!instr_inst.is_supported(cfg)) continue;
      // C_JAL is RV32C only instruction
      if ((XLEN != 32) && (instr_name == riscv_instr_name_t.C_JAL)) continue;
      if (canFind(cfg.reserved_regs, riscv_reg_t.SP ) &&
	  (instr_name == riscv_instr_name_t.C_ADDI16SP)) {
        continue;
      }
      if (!cfg.enable_sfence && instr_name == riscv_instr_name_t.SFENCE_VMA) continue;
      if (cfg.no_fence && (instr_name.inside(riscv_instr_name_t.FENCE,
					     riscv_instr_name_t.FENCE_I,
					     riscv_instr_name_t.SFENCE_VMA))) continue;
      if (canFind(supported_isa, instr_inst.group) &&
          !(cfg.disable_compressed_instr &&
            (instr_inst.group.inside(riscv_instr_group_t.RV32C, riscv_instr_group_t.RV64C,
				     riscv_instr_group_t.RV32DC, riscv_instr_group_t.RV32FC,
				     riscv_instr_group_t.RV128C))) &&
          !(!cfg.enable_floating_point &&
            (instr_inst.group.inside(riscv_instr_group_t.RV32F, riscv_instr_group_t.RV64F,
				     riscv_instr_group_t.RV32D, riscv_instr_group_t.RV64D))) &&
          !(!cfg.enable_vector_extension &&
            (instr_inst.group == riscv_instr_group_t.RVV)) &&
          !(cfg.vector_instr_only &&
            (instr_inst.group != riscv_instr_group_t.RVV))) {
	instr_category[instr_inst.category] ~= instr_name;
	instr_group[instr_inst.group] ~= instr_name;
	instr_names ~= instr_name;
      }
    }
    build_basic_instruction_list(cfg);
    create_csr_filter(cfg);
  }

  void create_csr_filter(riscv_instr_gen_config cfg) {
    include_reg.length = 0;
    exclude_reg.length = 0;
    if (cfg.enable_illegal_csr_instruction) {
      exclude_reg = implemented_csr;
    }
    else if (cfg.enable_access_invalid_csr_level) {
      include_reg = cfg.invalid_priv_mode_csrs;
    }
    else {
      // Use scratch register to avoid the side effect of modifying other privileged mode CSR.
      if (cfg.init_privileged_mode == privileged_mode_t.MACHINE_MODE) {
	include_reg = [privileged_reg_t.MSCRATCH];
      }
      else if (cfg.init_privileged_mode == privileged_mode_t.SUPERVISOR_MODE) {
	include_reg = [privileged_reg_t.SSCRATCH];
      }
      else {
	include_reg = [privileged_reg_t.USCRATCH];
      }
    }
  }

  riscv_instr create_instr(riscv_instr_name_t instr_name, string instr_class_name) {
    import std.conv: to;
    uvm_coreservice_t coreservice = uvm_coreservice_t.get();
    uvm_factory factory = coreservice.get_factory();
    uvm_object obj =
      factory.create_object_by_name(instr_class_name, "riscv_instr", instr_class_name);
    if (obj is null) {
      uvm_fatal("riscv_instr", format("Failed to create instr: %0s", instr_class_name));
    }
    riscv_instr instr = cast(riscv_instr) obj;
    if (instr is null) {
      uvm_fatal("riscv_instr", format("Failed to cast instr: %0s", instr_class_name));
    }
    return instr;
  }

  void build_basic_instruction_list(riscv_instr_gen_config cfg) {
    basic_instr =
      instr_category[riscv_instr_category_t.SHIFT] ~
      instr_category[riscv_instr_category_t.ARITHMETIC] ~
      instr_category[riscv_instr_category_t.LOGICAL] ~
      instr_category[riscv_instr_category_t.COMPARE];
    if (!cfg.no_ebreak) {
      basic_instr ~= riscv_instr_name_t.EBREAK;
      foreach (sup_isa; supported_isa) {
	if ((sup_isa == riscv_instr_group_t.RV32C) &&
	    !(cfg.disable_compressed_instr)) {
	  basic_instr ~= riscv_instr_name_t.C_EBREAK;
	  break;
	}
      }
    }
    if (cfg.no_dret == 0) {
      basic_instr ~= riscv_instr_name_t.DRET;
    }
    if (cfg.no_fence == 0) {
      basic_instr ~= instr_category[riscv_instr_category_t.SYNCH];
    }
    if ((cfg.no_csr_instr == 0) && (cfg.init_privileged_mode == privileged_mode_t.MACHINE_MODE)) {
      basic_instr ~= instr_category[riscv_instr_category_t.CSR];
    }
    if (cfg.no_wfi == 0) {
      basic_instr ~= riscv_instr_name_t.WFI;
    }
  }

  riscv_instr get_rand_instr(riscv_instr_name_t[] exclude_instr,
			     riscv_instr_category_t[] include_category) {
    return get_rand_instr(null, exclude_instr, include_category, null, null, null);
  }


  riscv_instr get_rand_instr(riscv_instr_category_t[] include_category,
			     riscv_instr_group_t[] exclude_group) {
    return get_rand_instr(null, null, include_category, null, null, exclude_group);
  }

  riscv_instr get_rand_instr(riscv_instr_category_t[] include_category) {
    return get_rand_instr(null, null, include_category, null, null, null);
  }


  riscv_instr get_rand_instr(riscv_instr_name_t[] include_instr) {
    return get_rand_instr(include_instr, null, null, null, null, null);
  }

  riscv_instr get_rand_instr(riscv_instr_name_t[] include_instr,
			     riscv_instr_name_t[] exclude_instr,
			     riscv_instr_group_t[] exclude_group) {
    return get_rand_instr(include_instr, exclude_instr, null, null, null, exclude_group);
  }

  riscv_instr get_rand_instr(riscv_instr_name_t[] include_instr = null,
			     riscv_instr_name_t[] exclude_instr = null,
			     riscv_instr_category_t[] include_category = null,
			     riscv_instr_category_t[] exclude_category = null,
			     riscv_instr_group_t[] include_group = null,
			     riscv_instr_group_t[] exclude_group = null) {
    ulong  idx;
    riscv_instr_name_t name;
    // riscv_instr_name_t name;
    riscv_instr_name_t[] allowed_instr;
    riscv_instr_name_t[] disallowed_instr;
    riscv_instr_category_t[] allowed_categories;
    foreach (icatg; include_category) {
      allowed_instr ~= instr_category[icatg];
    }
    foreach (ecatg; exclude_category) {
      disallowed_instr ~= instr_category[ecatg];
    }
    foreach (igrp; include_group) {
      allowed_instr ~= instr_group[igrp];
    }
    foreach (egrp; exclude_group) {
      if (egrp in instr_group) {
	disallowed_instr ~= instr_group[egrp];
      }
    }
    disallowed_instr ~= exclude_instr;
    if (disallowed_instr.length == 0) {
      if (include_instr.length > 0) {
	idx = urandom(0, include_instr.length);
	name = include_instr[idx];
      }
      else if (allowed_instr.length > 0) {
	idx = urandom(0, allowed_instr.length);
	name = allowed_instr[idx];
      }
      else {
	idx = urandom(0, instr_names.length);
	name = instr_names[idx];
      }
    }
    else {
      import std.algorithm.sorting: sort;
      import std.algorithm.setops: setIntersection, setDifference;
      import std.array: array;

      riscv_instr_name_t[] instr_set = instr_names.dup;
      instr_set.sort();

      riscv_instr_name_t[] include_set = instr_set;
      riscv_instr_name_t[] allowed_set = instr_set;

      if (include_instr.length > 0) {
	include_set = include_instr;
	include_set.sort();
      }

      if (allowed_instr.length > 0) {
	allowed_set = allowed_instr;
	allowed_set.sort();
      }

      riscv_instr_name_t[] inter_set =
	setDifference(setIntersection(instr_set, include_set, allowed_set),
		      disallowed_instr.sort()).array();

      idx = urandom(0, inter_set.length);

      name = inter_set[idx];
    }
    // Shallow copy for all relevant fields, avoid using create() to improve performance
    auto instr = instr_template[name].dup;
    instr.m_cfg = cfg;
    return instr;
  }

  riscv_instr get_load_store_instr(riscv_instr_name_t[] load_store_instr = null) {
    if (load_store_instr.length == 0) {
      load_store_instr = instr_category[riscv_instr_category_t.LOAD] ~
	instr_category[riscv_instr_category_t.STORE];
    }
    // Filter out unsupported load/store instruction
    if (unsupported_instr.length > 0) {
      uint i = 0;
      while (i < load_store_instr.length) {
	if (canFind(unsupported_instr, load_store_instr[i])) {
	  remove(load_store_instr, load_store_instr[i]);
	}
	else {
	  i += 1;
	}
      }
    }
    if (load_store_instr.length == 0) {
      assert (false, "Cannot generate random instruction");
    }
    ulong idx = urandom( 0, load_store_instr.length);
    riscv_instr_name_t name = load_store_instr[idx];
    // Shallow copy for all relevant fields, avoid using create() to improve performance
    auto instr = instr_template[name].dup;
    instr.m_cfg = cfg;
    return instr;
  }

  riscv_instr get_instr(riscv_instr_name_t name) {
    if (name !in instr_template) {
      uvm_fatal("riscv_instr", format("Cannot get instr %0s", name));
    }
    // Shallow copy for all relevant fields, avoid using create() to improve performance
    auto instr = instr_template[name].dup;
    instr.m_cfg = cfg;
    return instr;
  }

}
