// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
<%!
  from reggen import gen_dv
  from reggen.access import HwAccess, SwRdAccess, SwWrAccess
  from reggen.multi_register import MultiRegister
  from reggen.register import Register
  from typing import Dict

  # Get a list reg and its instance name
  # For single reg, return Dict[reg_inst:reg]
  # For multireg, if it's dv_compact, return Dict[mr.name[idx]:mr.reg],
  # if not, return all the items of mr.cregs with their names.
  def get_inst_to_reg_dict(r) -> Dict:
    inst_regs = {} # type: Dict[inst_name:Register]
    if isinstance(r, MultiRegister):
      if r.dv_compact:
        inst_base = r.pregs[0].name.lower()
        for idx, reg in enumerate(r.cregs):
          inst_name = f'{inst_base}[{idx}]'
          inst_regs[inst_name] = reg
      else:
        for r0 in r.cregs:
          inst_regs[r0.name] = r0
    else:
      inst_regs[r.name.lower()] = r
    return inst_regs
%>\
##
##
## make_ral_pkg
## ============
##
## Generate the RAL package for a device interface.
##
##    dv_base_names     a DvBaseNames object that contains register base class names
##
##    reg_width         an integer giving the width of registers in bits
##
##    reg_block_path    the hierarchical path to the relevant register block in the
##                      design
##
##    rb                a RegBlock object
##
##    esc_if_name       a string giving the full, escaped, interface name. For
##                      a device interface called FOO on block BAR,
##                      this will be bar__foo. For an unnamed interface
##                      on block BAR, this will be just bar.
##
<%def name="make_ral_pkg(dv_base_names, reg_width, reg_block_path, rb, esc_if_name)">\
package ${esc_if_name}_ral_pkg;
${make_ral_pkg_hdr(dv_base_names.pkg, [])}

${make_ral_pkg_fwd_decls(esc_if_name, rb.type_regs, rb.windows)}
% for r in rb.all_regs:
<%
    mr = None
    if isinstance(r, MultiRegister):
      mr = r
      if r.dv_compact:
        regs = [r.pregs[0]]
      else:
        regs = r.cregs
    else:
      regs = [r]
%>\
  % for idx, reg in enumerate(regs):

${make_ral_pkg_reg_class(dv_base_names.reg, dv_base_names.field, reg_width, esc_if_name,
reg_block_path, reg, mr, idx)}
  % endfor
% endfor
% for window in rb.windows:

${make_ral_pkg_window_class(dv_base_names.mem, esc_if_name, window)}
% endfor

<%
  reg_block_name = gen_dv.bcname(esc_if_name)
%>\
  class ${reg_block_name} extends ${dv_base_names.block};
% if rb.flat_regs:
    // registers
  % for r in rb.all_regs:
<%
      # If it's dv_compact, then create it as an array even when it only contains one item
      count = 0
      if isinstance(r, MultiRegister):
        if r.dv_compact:
          regs = [r.pregs[0]]
          count = len(r.cregs)
        else:
          regs = r.cregs
      else:
        regs = [r]
%>\
    % for r0 in regs:
<%
      reg_type = gen_dv.rcname(esc_if_name, r0)
      inst_name = r0.name.lower()
      inst_decl = f'{inst_name}[{count}]' if count > 0 else inst_name
%>\
    rand ${reg_type} ${inst_decl};
      % if r0.alias_target is not None:
<%
        alias_inst_name = r0.alias_target.lower()
        alias_inst_decl = f'{alias_inst_name}[{count}]' if count > 0 else alias_inst_name
%>\
    rand ${reg_type} ${alias_inst_decl}; // aliases to ${inst_decl}
      % endif
    % endfor
  % endfor
% endif
% if rb.windows:
    // memories
% for window in rb.windows:
    rand ${gen_dv.mcname(esc_if_name, window)} ${gen_dv.miname(window)};
% endfor
% endif

    `uvm_object_utils(${reg_block_name})

    function new(string name = "",
                 int    has_coverage = UVM_NO_COVERAGE);
      super.new(name, has_coverage);
    endfunction : new

    virtual function void build(uvm_reg_addr_t base_addr,
                                csr_excl_item csr_excl = null);
      // create default map
      this.default_map = create_map(.name("default_map"),
                                    .base_addr(base_addr),
                                    .n_bytes(${reg_width//8}),
                                    .endian(UVM_LITTLE_ENDIAN));
      if (csr_excl == null) begin
        csr_excl = csr_excl_item::type_id::create("csr_excl");
        this.csr_excl = csr_excl;
      end
% if rb.flat_regs:
      set_hdl_path_root("tb.dut", "BkdrRegPathRtl");
      set_hdl_path_root("tb.dut", "BkdrRegPathRtlShadow");
      // create registers
  % for r in rb.all_regs:
<%
    r0 = r.pregs[0] if isinstance(r, MultiRegister) else r
    reg_type = gen_dv.rcname(esc_if_name, r0)
%>\
    % if isinstance(r, MultiRegister):
      % for idx, reg in enumerate(r.cregs):
<%
        if r.dv_compact:
          inst_base = r0.name.lower()
          inst_name = f'{inst_base}[{idx}]'
          if r0.alias_target is not None:
            alias_inst_base = r0.alias_target.lower()
            alias_inst_name = f'{alias_inst_base}[{idx}]'
        else:
          inst_name = reg.name.lower()
          reg_type = gen_dv.rcname(esc_if_name, reg)
          if r0.alias_target is not None:
            alias_inst_name = reg.alias_target.lower()
%>\
${instantiate_register(reg_width, reg_block_path, reg, reg_type, inst_name)}\
        % if reg.alias_target is not None:
      // Assign alias register to generic handle.
      ${alias_inst_name} = ${inst_name};
        % endif
      % endfor
    % else:
${instantiate_register(reg_width, reg_block_path, r, reg_type, r.name.lower())}\
    % endif
    % if r0.alias_target is not None:
<%
    inst_name = r0.name.lower()
    alias_inst_name = r0.alias_target.lower()
%>\
      // Assign alias register to generic handle.
      ${alias_inst_name} = ${inst_name};
    % endif
  % endfor
<%
  any_regwen = False
  for r in rb.flat_regs:
    if r.regwen:
      any_regwen = True
      break
%>\
  % if any_regwen:
      // assign locked reg to its regwen reg
    % for r in rb.all_regs:
      % for inst, reg in get_inst_to_reg_dict(r).items():
${apply_regwen(rb, reg, inst)}\
      % endfor
    % endfor
  % endif
% endif
${make_ral_pkg_window_instances(reg_width, esc_if_name, rb)}

      // Create functional coverage for comportable IP-specific specialized registers.
      // This function can only be called if it is a root block to get the correct gating condition
      // and avoid creating duplicated cov.
      if (this.get_parent() == null && en_dv_reg_cov) create_cov();
    endfunction : build
  endclass : ${reg_block_name}

endpackage
</%def>\
##
##
## make_ral_pkg_hdr
## ================
##
## Generate the header for a RAL package
##
##    dv_base_reg_pkg_name   a string name for the base reg_pkg type
##
##    deps                   a list of names for packages that should be explicitly
##                           imported
##
<%def name="make_ral_pkg_hdr(dv_base_reg_pkg_name, deps)">\
  // dep packages
  import uvm_pkg::*;
  import dv_base_reg_pkg::*;
% if dv_base_reg_pkg_name != "dv_base_reg_pkg":
  import ${dv_base_reg_pkg_name}::*;
% endif
% for dep in deps:
  import ${dep}::*;
% endfor

  // macro includes
  `include "uvm_macros.svh"\
</%def>\
##
##
## make_ral_pkg_fwd_decls
## ======================
##
## Generate the forward declarations for a RAL package
##
##    esc_if_name      as for make_ral_pkg
##
##    type_regs        a list of Register objects, one for each type that
##                     should be defined. Each MultiRegister will contribute
##                     just one register to the list.
##
##    windows          a list of Window objects
##
<%def name="make_ral_pkg_fwd_decls(esc_if_name, type_regs, windows)">\
  // Forward declare all register/memory/block classes
% for r in type_regs:
  typedef class ${gen_dv.rcname(esc_if_name, r)};
% endfor
% for w in windows:
  typedef class ${gen_dv.mcname(esc_if_name, w)};
% endfor
  typedef class ${gen_dv.bcname(esc_if_name)};\
</%def>\
##
##
## make_ral_pkg_reg_class
## ======================
##
## Generate the classes for a register inside a RAL package
##
##    dv_base_reg_name     a string name for the base register type
##
##    dv_base_field_name   a string name for the base reg_field type
##
##    reg_width            as for make_ral_pkg
##
##    esc_if_name          as for make_ral_pkg
##
##    reg_block_path       as for make_ral_pkg
##
##    reg                  a Register object
##
##    mr                   a MultiRegister object if this reg is from a MultiRegister
##
##    reg_idx              the index location of this reg if this reg is from a MultiRegister,
##                         or zero if not
<%def name="make_ral_pkg_reg_class(dv_base_reg_name, dv_base_field_name, reg_width, esc_if_name,
reg_block_path, reg, mr, reg_idx)">\
<%
  reg_name = reg.name.lower()

  is_ext = reg.hwext
  for field in reg.fields:
    if (field.hwaccess.value[1] == HwAccess.NONE and
        field.swaccess.swrd() == SwRdAccess.RD and
        not field.swaccess.allows_write()):
      is_ext = 1

  class_name = gen_dv.rcname(esc_if_name, reg)
  alias_class_name = gen_dv.alias_rcname(esc_if_name, reg)
%>\
  class ${class_name} extends ${dv_base_reg_name};
    // fields
<%
  suffix = ""
  start_idx = 0
  add_style_waive = False
  compact_field_inst_name = ""
  compact_alias_field_inst_name = ""

  if mr is None:
      fields = reg.fields
  else:
    if not mr.compact:
      fields = mr.pregs[0].fields
    else:
      fields = mr.cregs[reg_idx].fields
      compact_field_inst_name = mr.pregs[0].fields[0].name.lower()
      compact_alias_field_inst_name = mr.pregs[0].fields[0].alias_target
      if mr.dv_compact:
        # The dv_compact flag means that the fields of the multi-reg divide equally into registers.
        # In this case, there's an array of registers and make_ral_pkg_reg_class() gets called once
        # to define that array's type, using the fields of the first register in the replication.
        assert reg_idx == 0
        if len(fields) > 1:
          suffix = f'[{len(fields)}]'
      else:
        # In this case, the multi-register is "compact", so there might be multiple copies of its
        # single field in each generated register. But dv_compact is false, which probably means
        # that the fields didn't divide equally into a whole number of registers. In this case, we
        # are generating a different class for each output register and should spit out fields
        # accordingly. Note that we generate an array, even if len(fields) = 1. If that happens, we
        # know we're on the last generated register, so want to keep everything uniform.
        num_fields_per_reg = 32 // fields[0].bits.width()
        start_idx = num_fields_per_reg * reg_idx
        end_idx = start_idx + len(fields) - 1
        suffix = f'[{start_idx}:{end_idx}]'
        if start_idx == 0:
          add_style_waive = True
%>\
% if add_style_waive:
    // verilog_lint: waive unpacked-dimensions-range-ordering
% endif
% if compact_field_inst_name:
    rand ${dv_base_field_name} ${compact_field_inst_name}${suffix};
%     if compact_alias_field_inst_name:
    rand ${dv_base_field_name} ${compact_alias_field_inst_name.lower()}${suffix};
%     endif
% else:
%   for f in fields:
    rand ${dv_base_field_name} ${f.name.lower()};
%     if f.alias_target is not None:
    rand ${dv_base_field_name} ${f.alias_target.lower()}; // aliases to ${f.name.lower()}
%     endif
%   endfor
% endif

    `uvm_object_utils(${class_name})

    function new(string       name = "",
                 int unsigned n_bits = ${reg_width},
                 int          has_coverage = UVM_NO_COVERAGE);
      super.new(name, n_bits, has_coverage);
% if reg.writes_ignore_errors:
      writes_ignore_errors = 1'b1;
% endif
    endfunction : new

    virtual function void build(csr_excl_item csr_excl = null);
% if alias_class_name is not None:
      set_alias_name("${alias_class_name}");
% endif\
      // create fields
% for idx, field in enumerate(fields):
<%
    alias_reg_field_name = ""
    if compact_field_inst_name:
      reg_field_name = compact_field_inst_name
      if compact_alias_field_inst_name:
        alias_reg_field_name = compact_alias_field_inst_name
      # If len(fields) > 1, we define generated reg fields as an array and we need an index to
      # refer to the field object
      # If start_idx > 0, the fields cross more than one register, we define an array for the
      # fields even when the last register only contains one field.
      if len(fields) > 1 or start_idx > 0:
        reg_field_name = reg_field_name + f'[{idx + start_idx}]'
        if compact_alias_field_inst_name:
          alias_reg_field_name = alias_reg_field_name + f'[{idx + start_idx}]'
    else:
      reg_field_name = field.name.lower()
      if field.alias_target is not None:
        alias_reg_field_name = field.alias_target.lower()
%>\
${_create_reg_field(dv_base_field_name, reg_width, reg_block_path, reg.shadowed, reg.hwext,
reg_field_name, field)}\
  % if field.alias_target is not None:
      ${alias_reg_field_name} = ${reg_field_name}; // assign to generic handle
  % endif
% endfor
% if is_ext:
      set_is_ext_reg(1);
% endif
    endfunction : build
  endclass : ${class_name}\
</%def>\
##
##
## _create_reg_field
## =================
##
## Generate the code that creates a uvm_reg_field object for a field
## in a register.
##
##    dv_base_reg_field_name   as for make_ral_pkg_reg_class
##
##    reg_width                as for make_ral_pkg
##
##    reg_block_path           as for make_ral_pkg
##
##    shadowed                 true if the field's register is shadowed
##
##    hwext                    true if the field's register is hwext
##
##    reg_field_name           a string with the name to give the field in the HDL
##
##    field                    a Field object
<%def name="_create_reg_field(dv_base_reg_field_name, reg_width, reg_block_path, shadowed, hwext,
reg_field_name, field)">\
<%
  field_size = field.bits.width()
  field_access = field.swaccess.dv_rights()
  field_mubi_access = field.swaccess.dv_mubi_rights()

  if not field.hwaccess.allows_write():
    field_volatile = 0
  else:
    field_volatile = 1
  field_tags = field.tags

  fname = reg_field_name
%>\
      ${fname} =
          (${dv_base_reg_field_name}::
           type_id::create("${field.name.lower()}"));
      ${fname}.configure(
        .parent(this),
        .size(${field_size}),
        .lsb_pos(${field.bits.lsb}),
        .access("${field_access}"),
        .mubi_access("${field_mubi_access}"),
        .volatile(${field_volatile}),
        .reset(${reg_width}'h${format(field.resval or 0, 'x')}),
        .has_reset(1),
        .is_rand(1),
        .individually_accessible(1));

% if field.alias_target is not None:
      ${fname}.set_alias_name("${field.alias_target.lower()}");
% endif
      ${fname}.set_original_access("${field_access}");
% if field.mubi:
      ${fname}.set_mubi_width(${field_size});
% endif
% if field_tags:
      // create field tags
%     for field_tag in field_tags:
<%
  tag = field_tag.split(":")
%>\
%       if tag[0] == "excl":
      csr_excl.add_excl(${fname}.get_full_name(), ${tag[2]}, ${tag[1]});
%       endif
%     endfor
%   endif
</%def>\
##
##
## make_ral_pkg_window_class
## =========================
##
## Generate the classes for a window inside a RAL package
##
##    dv_base_window_name   a string name for the base windoe type
##
##    esc_if_name           as for make_ral_pkg
##
##    window                a Window object
<%def name="make_ral_pkg_window_class(dv_base_window_name, esc_if_name, window)">\
<%
  mem_name = window.name.lower()
  mem_right = window.swaccess.dv_rights()
  mem_n_bits = window.validbits
  mem_size = window.items

  class_name = gen_dv.mcname(esc_if_name, window)
%>\
  class ${class_name} extends ${dv_base_window_name};

    `uvm_object_utils(${class_name})

    function new(string           name = "",
                 longint unsigned size = ${mem_size},
                 int unsigned     n_bits = ${mem_n_bits},
                 string           access = "${mem_right}",
                 int              has_coverage = UVM_NO_COVERAGE);
      super.new(name, size, n_bits, access, has_coverage);
%     if window.byte_write:
      set_mem_partial_write_support(1);
%     endif
%     if window.data_intg_passthru:
      set_data_intg_passthru(1);
%     endif
    endfunction : new

  endclass : ${class_name}
</%def>\
##
##
## make_ral_pkg_window_instances
## =============================
##
## Generate the classes for a window inside a RAL package
##
##    reg_width        as for make_ral_pkg
##
##    esc_if_name      as for make_ral_pkg
##
##    rb               a RegBlock object
##
<%def name="make_ral_pkg_window_instances(reg_width, esc_if_name, rb)">\
% if rb.windows:

      // create memories
%  for w in rb.windows:
<%
      mem_name = w.name.lower()
      mem_right = w.swaccess.dv_rights()
      mem_offset = "{}'h{:x}".format(reg_width, w.offset)
      mem_n_bits = w.validbits
      mem_size = w.items
%>\
      ${mem_name} =
          ${gen_dv.mcname(esc_if_name, w)}::type_id::create("${mem_name}");
      ${mem_name}.configure(.parent(this));
      default_map.add_mem(.mem(${mem_name}),
                          .offset(${mem_offset}),
                          .rights("${mem_right}"));
%   endfor
% endif
</%def>\
##
##
## instantiate_register
## ====================
##
## Actually instantiate a register in a register block
##
##    reg_width        an integer giving the width of registers in bits
##
##    reg_block_path   as for make_ral_pkg
##
##    reg              the Register to instantiate
##
##    reg_type         a string giving the type name (a subclass of
##                     uvm_register) to instantiate.
##
##    reg_inst         a string giving the field of the uvm_reg_block that
##                     should be set to this new register. For single
##                     registers, this will just be the register name. For
##                     elements of multi-registers, it will be the name of an
##                     array item.
##
<%def name="instantiate_register(reg_width, reg_block_path, reg, reg_type, reg_inst)">\
<%
      reg_name = reg.name.lower()
      reg_offset = "{}'h{:x}".format(reg_width, reg.offset)
%>\
      ${reg_inst} =
          (${reg_type}::
           type_id::create("${reg_name}"));
      ${reg_inst}.configure(.blk_parent(this));
      ${reg_inst}.build(csr_excl);
      default_map.add_reg(.rg(${reg_inst}),
                          .offset(${reg_offset}));
% if reg.shadowed:
      % if reg.update_err_alert:
      ${reg_inst}.add_update_err_alert("${reg.update_err_alert}");
      % endif

      % if reg.storage_err_alert:
      ${reg_inst}.add_storage_err_alert("${reg.storage_err_alert}");
      % endif

  % if reg.hwext:
    % for field in reg.fields:
<%
      shadowed_reg_path = ''
      for tag in field.tags:
        parts = tag.split(':')
        if parts[0] == 'shadowed_reg_path':
          shadowed_reg_path = parts[1]

      if not shadowed_reg_path:
        print("ERROR: ext shadow_reg does not have tags for shadowed_reg_path for each field!")
        assert 0
%>\
      ${reg_inst}.add_hdl_path_slice(
          "${shadowed_reg_path}.committed_reg.q", // verilog_lint: waive line-length
          ${field.bits.lsb}, ${field.bits.width()}, 0, "BkdrRegPathRtl");
      ${reg_inst}.add_hdl_path_slice(
          "${shadowed_reg_path}.shadow_reg.q", // verilog_lint: waive line-length
          ${field.bits.lsb}, ${field.bits.width()}, 0, "BkdrRegPathRtlShadow");
    % endfor
  % endif
% endif
% for field in reg.fields:
<%
    field_size = field.bits.width()
    if len(reg.fields) == 1:
      reg_field_name = reg_name
    else:
      reg_field_name = reg_name + "_" + field.name.lower()

    ##if reg.async_name and not reg.hwext:
    ##  reg_field_name += ".u_subreg"
%>\
%   if ((field.hwaccess.value[1] == HwAccess.NONE and\
       field.swaccess.swrd() == SwRdAccess.RD and\
       not field.swaccess.allows_write())):
      // constant reg
      ${reg_inst}.add_hdl_path_slice(
          "${reg_block_path}.${reg_field_name}_qs",
          ${field.bits.lsb}, ${field_size}, 0, "BkdrRegPathRtl");
%   elif not reg.shadowed:
      ${reg_inst}.add_hdl_path_slice(
          "${reg_block_path}.u_${reg_field_name}.q${"s" if reg.hwext else ""}",
          ${field.bits.lsb}, ${field_size}, 0, "BkdrRegPathRtl");
%   endif
%   if reg.shadowed and not reg.hwext:
      ${reg_inst}.add_hdl_path_slice(
          "${reg_block_path}.u_${reg_field_name}.committed_reg.q",
          ${field.bits.lsb}, ${field_size}, 0, "BkdrRegPathRtl");
      ${reg_inst}.add_hdl_path_slice(
          "${reg_block_path}.u_${reg_field_name}.shadow_reg.q",
          ${field.bits.lsb}, ${field_size}, 0, "BkdrRegPathRtlShadow");
%   endif
% endfor

%     if reg.shadowed:
      ${reg_inst}.set_is_shadowed();
%     endif
%     if reg.tags:
      // create register tags
%       for reg_tag in reg.tags:
<%
        tag = reg_tag.split(":")
%>\
%         if tag[0] == "excl":
      csr_excl.add_excl(${reg_inst}.get_full_name(),
                        ${tag[2]}, ${tag[1]});
%         endif
%       endfor
%     endif
</%def>\
##
##
## apply_regwen
## ============
##
## Apply a regwen to a register
##
##    rb               the register block
##
##    reg              the Register that needs apply regwens
##
##    reg_inst         a string giving the field of the uvm_reg_block that
##                     should be updated. For single registers, this will just
##                     be the register name. For elements of multi-registers,
##                     it will be the name of an array item.
##
<%def name="apply_regwen(rb, reg, reg_inst)">\
% if reg.regwen is None:
<% return "" %>\
% endif
% for wen in rb.all_regs:
%   for wen_inst, wen_reg in get_inst_to_reg_dict(wen).items():
%     if reg.regwen.lower() == wen_reg.name.lower():
      ${wen_inst}.add_lockable_reg_or_fld(${reg_inst});
<% return "" %>\
%     elif wen_reg.name.lower() in reg.regwen.lower():
%       for field in wen_reg.get_field_list():
%         if reg.regwen.lower() == (wen_reg.name.lower() + "_" + field.name.lower()):
      ${wen_inst}.${field.name.lower()}.add_lockable_reg_or_fld(${reg_inst});
<% return "" %>\
%         endif
%       endfor
%     endif
%   endfor
% endfor
</%def>\
