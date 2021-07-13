// Copyright lowRISC contributors.
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
  # if not, return all the mr.regs with their name
  def get_inst_to_reg_dict(r) -> Dict:
    inst_regs = {} # type: Dict[inst_name:Register]
    if isinstance(r, MultiRegister):
      if r.dv_compact:
        inst_base = r.reg.name.lower()
        for idx, reg in enumerate(r.regs):
          inst_name = f'{inst_base}[{idx}]' if len(r.regs) > 1 else inst_base
          inst_regs[inst_name] = reg
      else:
        for r0 in r.regs:
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
##    dv_base_prefix   a string naming the base register type. If it is FOO,
##                     then we will inherit from FOO_reg (assumed to
##                     be a subclass of uvm_reg).
##
##    reg_width        an integer giving the width of registers in bits
##
##    reg_block_path   the hierarchical path to the relevant register block in the
##                     design
##
##    rb               a RegBlock object
##
##    esc_if_name      a string giving the full, escaped, interface name. For
##                     a device interface called FOO on block BAR,
##                     this will be bar__foo. For an unnamed interface
##                     on block BAR, this will be just bar.
##
<%def name="make_ral_pkg(dv_base_prefix, reg_width, reg_block_path, rb, esc_if_name)">\
package ${esc_if_name}_ral_pkg;
${make_ral_pkg_hdr(dv_base_prefix, [])}

${make_ral_pkg_fwd_decls(esc_if_name, rb.type_regs, rb.windows)}
% for r in rb.all_regs:
<%
    if isinstance(r, MultiRegister):
      reg = r.reg
      if r.dv_compact:
        reg.fields = r.regs[0].fields
        regs = [reg]
      else:
        regs = r.regs
    else:
      regs = [r]
%>\
  % for reg in regs:

${make_ral_pkg_reg_class(dv_base_prefix, reg_width, esc_if_name, reg_block_path, reg)}
  % endfor
% endfor
% for window in rb.windows:

${make_ral_pkg_window_class(dv_base_prefix, esc_if_name, window)}
% endfor

<%
  reg_block_name = gen_dv.bcname(esc_if_name)
%>\
  class ${reg_block_name} extends ${dv_base_prefix}_reg_block;
% if rb.flat_regs:
    // registers
  % for r in rb.all_regs:
<%
      if isinstance(r, MultiRegister):
        if r.dv_compact:
          regs = [r.reg]
          count = len(r.regs)
        else:
          regs = r.regs
          count = 1
      else:
        regs = [r]
        count = 1
%>\
    % for r0 in regs:
<%
      reg_type = gen_dv.rcname(esc_if_name, r0)
      inst_name = r0.name.lower()
      inst_decl = f'{inst_name}[{count}]' if count > 1 else inst_name
%>\
    rand ${reg_type} ${inst_decl};
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

    function new(string name = "${reg_block_name}",
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
      set_hdl_path_root("tb.dut", "BkdrRegPathRtlCommitted");
      set_hdl_path_root("tb.dut", "BkdrRegPathRtlShadow");
      // create registers
  % for r in rb.all_regs:
<%
    r0 = r.reg if isinstance(r, MultiRegister) else r
    reg_type = gen_dv.rcname(esc_if_name, r0)
%>\
    % if isinstance(r, MultiRegister):
      % for idx, reg in enumerate(r.regs):
<%
        if r.dv_compact:
          inst_base = r0.name.lower()
          inst_name = f'{inst_base}[{idx}]' if len(r.regs) > 1 else inst_base
        else:
          inst_name = reg.name.lower()
          reg_type = gen_dv.rcname(esc_if_name, reg)
%>\
${instantiate_register(reg_width, reg_block_path, reg, reg_type, inst_name)}\
      % endfor
    % else:
${instantiate_register(reg_width, reg_block_path, r, reg_type, r.name.lower())}\
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
##    dv_base_prefix   as for make_ral_pkg
##
##    deps             a list of names for packages that should be explicitly
##                     imported
##
<%def name="make_ral_pkg_hdr(dv_base_prefix, deps)">\
  // dep packages
  import uvm_pkg::*;
  import dv_base_reg_pkg::*;
% if dv_base_prefix != "dv_base":
  import ${dv_base_prefix}_reg_pkg::*;
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
##    dv_base_prefix   as for make_ral_pkg
##
##    reg_width        as for make_ral_pkg
##
##    esc_if_name      as for make_ral_pkg
##
##    reg_block_path   as for make_ral_pkg
##
##    reg              a Register or MultiRegister object
<%def name="make_ral_pkg_reg_class(dv_base_prefix, reg_width, esc_if_name, reg_block_path, reg)">\
<%
  reg_name = reg.name.lower()

  is_ext = reg.hwext
  for field in reg.fields:
    if (field.hwaccess.value[1] == HwAccess.NONE and
        field.swaccess.swrd() == SwRdAccess.RD and
        not field.swaccess.allows_write()):
      is_ext = 1

  class_name = gen_dv.rcname(esc_if_name, reg)
%>\
  class ${class_name} extends ${dv_base_prefix}_reg;
    // fields
% for f in reg.fields:
    rand ${dv_base_prefix}_reg_field ${f.name.lower()};
% endfor

    `uvm_object_utils(${class_name})

    function new(string       name = "${class_name}",
                 int unsigned n_bits = ${reg_width},
                 int          has_coverage = UVM_NO_COVERAGE);
      super.new(name, n_bits, has_coverage);
    endfunction : new

    virtual function void build(csr_excl_item csr_excl = null);
      // create fields
% for field in reg.fields:
<%
    if len(reg.fields) == 1:
      reg_field_name = reg_name
    else:
      reg_field_name = reg_name + "_" + field.name.lower()
%>\
${_create_reg_field(dv_base_prefix, reg_width, reg_block_path, reg.shadowed, reg.hwext, reg_field_name, field)}
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
##    dv_base_prefix   as for make_ral_pkg
##
##    reg_width        as for make_ral_pkg
##
##    reg_block_path   as for make_ral_pkg
##
##    shadowed         true if the field's register is shadowed
##
##    hwext            true if the field's register is hwext
##
##    reg_field_name   a string with the name to give the field in the HDL
##
##    field            a Field object
<%def name="_create_reg_field(dv_base_prefix, reg_width, reg_block_path, shadowed, hwext, reg_field_name, field)">\
<%
  field_size = field.bits.width()
  field_access = field.swaccess.dv_rights()

  if not field.hwaccess.allows_write():
    field_volatile = 0
  else:
    field_volatile = 1
  field_tags = field.tags

  fname = field.name.lower()
  type_id_indent = ' ' * (len(fname) + 4)
%>\
      ${fname} = (${dv_base_prefix}_reg_field::
      ${type_id_indent}type_id::create("${fname}"));
      ${fname}.configure(
        .parent(this),
        .size(${field_size}),
        .lsb_pos(${field.bits.lsb}),
        .access("${field_access}"),
        .volatile(${field_volatile}),
        .reset(${reg_width}'h${format(field.resval or 0, 'x')}),
        .has_reset(1),
        .is_rand(1),
        .individually_accessible(1));

      ${fname}.set_original_access("${field_access}");
% if field_tags:
      // create field tags
%     for field_tag in field_tags:
<%
  tag = field_tag.split(":")
%>\
%       if tag[0] == "excl":
      csr_excl.add_excl(${field.name.lower()}.get_full_name(), ${tag[2]}, ${tag[1]});
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
##    dv_base_prefix   as for make_ral_pkg
##
##    esc_if_name      as for make_ral_pkg
##
##    window           a Window object
<%def name="make_ral_pkg_window_class(dv_base_prefix, esc_if_name, window)">\
<%
  mem_name = window.name.lower()
  mem_right = window.swaccess.dv_rights()
  mem_n_bits = window.validbits
  mem_size = window.items

  class_name = gen_dv.mcname(esc_if_name, window)
%>\
  class ${class_name} extends ${dv_base_prefix}_mem;

    `uvm_object_utils(${class_name})

    function new(string           name = "${class_name}",
                 longint unsigned size = ${mem_size},
                 int unsigned     n_bits = ${mem_n_bits},
                 string           access = "${mem_right}",
                 int              has_coverage = UVM_NO_COVERAGE);
      super.new(name, size, n_bits, access, has_coverage);
%     if window.byte_write:
      set_mem_partial_write_support(1);
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
      ${mem_name} = ${gen_dv.mcname(esc_if_name, w)}::type_id::create("${mem_name}");
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

      inst_id_indent = ' ' * (len(reg_inst) + 4)
%>\
      ${reg_inst} = (${reg_type}::
      ${inst_id_indent}type_id::create("${reg_name}"));
      ${reg_inst}.configure(.blk_parent(this));
      ${reg_inst}.build(csr_excl);
      default_map.add_reg(.rg(${reg_inst}),
                          .offset(${reg_offset}));
% if reg.shadowed and reg.hwext:
<%
    shadowed_reg_path = ''
    for tag in reg.tags:
      parts = tag.split(':')
      if parts[0] == 'shadowed_reg_path':
        shadowed_reg_path = parts[1]

    if not shadowed_reg_path:
      print("ERROR: ext shadow_reg does not have tags for shadowed_reg_path!")
      assert 0

    bit_idx = reg.fields[-1].bits.msb + 1

%>\
      ${reg_inst}.add_update_err_alert("${reg.update_err_alert}");
      ${reg_inst}.add_storage_err_alert("${reg.storage_err_alert}");
      ${reg_inst}.add_hdl_path_slice(
          "${shadowed_reg_path}.committed_reg.q",
          0, ${bit_idx}, 0, "BkdrRegPathRtlCommitted");
      ${reg_inst}.add_hdl_path_slice(
          "${shadowed_reg_path}.shadow_reg.q",
          0, ${bit_idx}, 0, "BkdrRegPathRtlShadow");
% endif
% for field in reg.fields:
<%
    field_size = field.bits.width()
    if len(reg.fields) == 1:
      reg_field_name = reg_name
    else:
      reg_field_name = reg_name + "_" + field.name.lower()
%>\
%   if ((field.hwaccess.value[1] == HwAccess.NONE and\
       field.swaccess.swrd() == SwRdAccess.RD and\
       not field.swaccess.allows_write())):
      // constant reg
      ${reg_inst}.add_hdl_path_slice(
          "${reg_block_path}.${reg_field_name}_qs",
          ${field.bits.lsb}, ${field_size}, 0, "BkdrRegPathRtl");
%   else:
      ${reg_inst}.add_hdl_path_slice(
          "${reg_block_path}.u_${reg_field_name}.q${"s" if reg.hwext else ""}",
          ${field.bits.lsb}, ${field_size}, 0, "BkdrRegPathRtl");
%   endif
%   if shadowed and not hwext:
      ${reg_inst}.add_hdl_path_slice(
          "${reg_block_path}.u_${reg_field_name}.committed_reg.q",
          ${field.bits.lsb}, ${field_size}, 0, "BkdrRegPathRtlCommitted");
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
      csr_excl.add_excl(${reg_inst}.get_full_name(), ${tag[2]}, ${tag[1]});
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
