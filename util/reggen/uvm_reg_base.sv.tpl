// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
<%!
  from reggen import gen_dv
  from reggen.access import HwAccess, SwRdAccess, SwWrAccess
%>
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

${make_ral_pkg_fwd_decls(esc_if_name, rb.flat_regs, rb.windows)}
% for reg in rb.flat_regs:

${make_ral_pkg_reg_class(dv_base_prefix, reg_width, esc_if_name, reg_block_path, reg)}
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
%   for r in rb.flat_regs:
    rand ${gen_dv.rcname(esc_if_name, r)} ${r.name.lower()};
%   endfor
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
%   for r in rb.flat_regs:
<%
      reg_name = r.name.lower()
      reg_right = r.dv_rights()
      reg_offset = "{}'h{:x}".format(reg_width, r.offset)
      reg_tags = r.tags
      reg_shadowed = r.shadowed

      type_id_indent = ' ' * (len(reg_name) + 4)
%>\
      ${reg_name} = (${gen_dv.rcname(esc_if_name, r)}::
      ${type_id_indent}type_id::create("${reg_name}"));
      ${reg_name}.configure(.blk_parent(this));
      ${reg_name}.build(csr_excl);
      default_map.add_reg(.rg(${reg_name}),
                          .offset(${reg_offset}),
                          .rights("${reg_right}"));
%     if reg_shadowed:
      ${reg_name}.set_is_shadowed();
%     endif
%     if reg_tags:
      // create register tags
%       for reg_tag in reg_tags:
<%
        tag = reg_tag.split(":")
%>\
%         if tag[0] == "excl":
      csr_excl.add_excl(${reg_name}.get_full_name(), ${tag[2]}, ${tag[1]});
%         endif
%       endfor
%     endif
%   endfor
<%
  any_regwen = False
  for r in rb.flat_regs:
    if r.regwen:
      any_regwen = True
      break
%>\
% if any_regwen:
      // assign locked reg to its regwen reg
%     for r in rb.flat_regs:
%       if r.regwen:
%         for reg in rb.flat_regs:
%           if r.regwen.lower() == reg.name.lower():
      ${r.regwen.lower()}.add_lockable_reg_or_fld(${r.name.lower()});
<% break %>\
%           elif reg.name.lower() in r.regwen.lower():
%             for field in reg.get_field_list():
%               if r.regwen.lower() == (reg.name.lower() + "_" + field.name.lower()):
      ${r.regwen.lower()}.${field.name.lower()}.add_lockable_reg_or_fld(${r.name.lower()});
<% break %>\
%               endif
%             endfor
%           endif
%         endfor
%       endif
%     endfor
%   endif
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
##    flat_regs        a list of Register objects (expanding multiregs)
##
##    windows          a list of Window objects
##
<%def name="make_ral_pkg_fwd_decls(esc_if_name, flat_regs, windows)">\
  // Forward declare all register/memory/block classes
% for r in flat_regs:
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
##    reg              a Register object
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
      add_update_err_alert("${reg.update_err_alert}");
      add_storage_err_alert("${reg.storage_err_alert}");
      add_hdl_path_slice("${shadowed_reg_path}.committed_reg.q",
                         0, ${bit_idx}, 0, "BkdrRegPathRtlCommitted");
      add_hdl_path_slice("${shadowed_reg_path}.shadow_reg.q",
                         0, ${bit_idx}, 0, "BkdrRegPathRtlShadow");
% endif
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
  if field.swaccess.key == "r0w1c":
    field_access = "W1C"
  else:
    field_access = field.swaccess.value[1].name

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
% if ((field.hwaccess.value[1] == HwAccess.NONE and\
       field.swaccess.swrd() == SwRdAccess.RD and\
       not field.swaccess.allows_write())):
      // constant reg
      add_hdl_path_slice("${reg_block_path}.${reg_field_name}_qs",
                         ${field.bits.lsb}, ${field_size}, 0, "BkdrRegPathRtl");
% else:
      add_hdl_path_slice("${reg_block_path}.u_${reg_field_name}.q${"s" if hwext else ""}",
                         ${field.bits.lsb}, ${field_size}, 0, "BkdrRegPathRtl");
% endif
% if shadowed and not hwext:
      add_hdl_path_slice("${reg_block_path}.u_${reg_field_name}.committed_reg.q",
                         ${field.bits.lsb}, ${field_size}, 0, "BkdrRegPathRtlCommitted");
      add_hdl_path_slice("${reg_block_path}.u_${reg_field_name}.shadow_reg.q",
                         ${field.bits.lsb}, ${field_size}, 0, "BkdrRegPathRtlShadow");
% endif
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
