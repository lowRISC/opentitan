module riscv.gen.target;

version(RV32IMCB) {
  pragma (msg, "Using target: RV32IMCB");
  public import riscv.gen.target.rv32imcb.riscv_core_setting;
 }
 else version(RV64GCV) {
   pragma (msg, "Using target: RV64GCV");
   public import riscv.gen.target.rv64gcv.riscv_core_setting;
 }
 else version(RV64GC) {
   pragma (msg, "Using target: RV64GC");
   public import riscv.gen.target.rv64gc.riscv_core_setting;
 }
 else version(RV64IMCB) {
   pragma (msg, "Using target: RV64IMCB");
   public import riscv.gen.target.rv64imcb.riscv_core_setting;
 }
 else version(RV32IMAFDC) {
   pragma (msg, "Using target: RV32IMAFDC");
   public import riscv.gen.target.rv32imafdc.riscv_core_setting;
 }
 else version(ML) {
   pragma (msg, "Using target: ML");
   public import riscv.gen.target.ml.riscv_core_setting;
 }
 else version(MULTI_HARTS) {
   pragma (msg, "Using target: MULTI_HARTS");
   public import riscv.gen.target.multi_harts.riscv_core_setting;
 }
 else version(RV32IMC_SV32) {
   pragma (msg, "Using target: RV32IMC_SV32");
   public import riscv.gen.target.rv32imc_sv32.riscv_core_setting;
 }
 else version(RV32I) {
   pragma (msg, "Using target: RV32I");
   public import riscv.gen.target.rv32i.riscv_core_setting;
 }
 else version(RV64IMC) {
   pragma (msg, "Using target: RV64IMC");
   public import riscv.gen.target.rv64imc.riscv_core_setting;
 }
 else version(RV32IMC) {
   pragma (msg, "Using target: RV32IMC");
   public import riscv.gen.target.rv32imc.riscv_core_setting;
 }
 else {
   pragma (msg, "Using Default target: RV64IMC");
   public import riscv.gen.target.rv64imc.riscv_core_setting;
 }
