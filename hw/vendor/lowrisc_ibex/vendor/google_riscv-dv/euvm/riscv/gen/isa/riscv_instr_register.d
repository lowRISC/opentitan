/*
 * Copyright 2019 Google LLC
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

module riscv.gen.isa.riscv_instr_register;

import riscv.gen.riscv_instr_registry: riscv_instr_registry;
import riscv.gen.isa.riscv_instr: riscv_instr;

import std.traits: fullyQualifiedName;


void register(alias MOD, INSTRS...)(riscv_instr_registry registry) {
  static if (INSTRS.length == 0) return;
  else {
    alias INSTR=__traits(getMember, MOD, INSTRS[0]);
    static if (is (INSTR == class) && is (INSTR: riscv_instr)) {
      // pragma(msg, "register ", fullyQualifiedName!INSTR);
      registry.register(INSTR.RISCV_INSTR_NAME_T, fullyQualifiedName!INSTR);
    }
    register!(MOD, INSTRS[1..$])(registry);
    return;
  }
}

void register_module(alias MOD)(riscv_instr_registry registry) {
  register!(MOD, __traits(allMembers, MOD))(registry);
}

void register_isa(riscv_instr_registry registry) {
  import riscv.gen.isa.rv128c_instr;
  import riscv.gen.isa.rv32a_instr;
  import riscv.gen.isa.rv32b_instr;
  import riscv.gen.isa.rv32c_instr;
  import riscv.gen.isa.rv32dc_instr;
  import riscv.gen.isa.rv32d_instr;
  import riscv.gen.isa.rv32fc_instr;
  import riscv.gen.isa.rv32f_instr;
  import riscv.gen.isa.rv32i_instr;
  import riscv.gen.isa.rv32m_instr;
  import riscv.gen.isa.rv32v_instr;
  import riscv.gen.isa.rv64a_instr;
  import riscv.gen.isa.rv64b_instr;
  import riscv.gen.isa.rv64c_instr;
  import riscv.gen.isa.rv64d_instr;
  import riscv.gen.isa.rv64f_instr;
  import riscv.gen.isa.rv64i_instr;
  import riscv.gen.isa.rv64m_instr;
  import riscv.gen.isa.rv64zba_instr;
  import riscv.gen.isa.rv64zbb_instr;
  import riscv.gen.isa.rv32zba_instr;
  import riscv.gen.isa.rv32zbb_instr;
  import riscv.gen.isa.rv32zbc_instr;
  import riscv.gen.isa.rv32zbs_instr;

  register_module!(riscv.gen.isa.rv128c_instr)(registry);
  register_module!(riscv.gen.isa.rv32a_instr)(registry);
  register_module!(riscv.gen.isa.rv32b_instr)(registry);
  register_module!(riscv.gen.isa.rv32c_instr)(registry);
  register_module!(riscv.gen.isa.rv32dc_instr)(registry);
  register_module!(riscv.gen.isa.rv32d_instr)(registry);
  register_module!(riscv.gen.isa.rv32fc_instr)(registry);
  register_module!(riscv.gen.isa.rv32f_instr)(registry);
  register_module!(riscv.gen.isa.rv32i_instr)(registry);
  register_module!(riscv.gen.isa.rv32m_instr)(registry);
  register_module!(riscv.gen.isa.rv32v_instr)(registry);
  register_module!(riscv.gen.isa.rv64a_instr)(registry);
  register_module!(riscv.gen.isa.rv64b_instr)(registry);
  register_module!(riscv.gen.isa.rv64c_instr)(registry);
  register_module!(riscv.gen.isa.rv64d_instr)(registry);
  register_module!(riscv.gen.isa.rv64f_instr)(registry);
  register_module!(riscv.gen.isa.rv64i_instr)(registry);
  register_module!(riscv.gen.isa.rv64m_instr)(registry);
}
