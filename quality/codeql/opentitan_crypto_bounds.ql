// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * @name OpenTitan Crypto Buffer and Keyblob Overflow
 * @description Identifies static buffer overflows across OpenTitan crypto buffer/key structs, constructors, and memory/DMEM primitives.
 * @kind problem
 * @problem.severity error
 * @id cpp/opentitan-crypto-buffer-overflow
 */

import cpp

predicate isInCryptoScope(Element e) {
  e.getFile().getAbsolutePath().matches("%/sw/device/lib/crypto/%") or
  e.getFile().getAbsolutePath().matches("%/sw/device/tests/crypto/%")
}

predicate isIntentionalNegativeTestVar(Variable v) {
  v.getFile().getAbsolutePath().matches("%/sw/device/tests/crypto/%") and
  v.getName().regexpMatch("(^|.*_)(bad|invalid|wrong|fake|small|short)(_.*|$)")
}

predicate isIntentionalNegativeTestCall(FunctionCall fc) {
  fc.getFile().getAbsolutePath().matches("%/sw/device/tests/crypto/%") and
  (
    fc.getEnclosingFunction().getName().matches("%negative%")
    or
    exists(MacroInvocation mi |
      mi.getMacroName() = "OTCRYPTO_BAD_ARGS" and
      mi.getExpr().getEnclosingStmt() = fc.getEnclosingStmt()
    )
  )
}

/**
 * Holds if `va` accesses a standalone variable or a struct field (excluding
 * array-of-struct indexing like `(*tbl)[0].data` and contiguous `share0`+`share1`
 * copies on masked structs).
 */
predicate checkableVarAccess(VariableAccess va, Variable v) {
  v = va.getTarget() and
  not isIntentionalNegativeTestVar(v) and
  (
    not va instanceof FieldAccess
    or
    exists(FieldAccess fa, Struct s |
      fa = va and
      s = fa.getTarget().getDeclaringType() and
      not fa.getQualifier() instanceof ArrayExpr and
      not fa.getQualifier() instanceof PointerDereferenceExpr and
      not (
        fa.getTarget().getName() = "share0" and
        exists(Field f1 |
          f1 = s.getAField() and
          f1.getName() = "share1" and
          f1.getType() = fa.getTarget().getType()
        )
      )
    )
  )
}

/**
 * Resolves pointer expression `e` (stripping casts) to a statically sized array,
 * struct, or scalar variable `v` and its remaining capacity `availBytes` starting
 * from any constant offset in `e`.
 */
predicate resolveStaticMemoryRegion(Expr e, Variable v, int availBytes) {
  exists(Expr stripped | stripped = e.getUnconverted() |
    exists(VariableAccess va, ArrayType arr |
      stripped = va and
      checkableVarAccess(va, v) and
      arr = v.getUnspecifiedType() and
      availBytes = arr.getByteSize()
    )
    or
    exists(AddressOfExpr aoe, VariableAccess va, ArrayType arr |
      aoe = stripped and
      va = aoe.getOperand().getUnconverted() and
      checkableVarAccess(va, v) and
      arr = v.getUnspecifiedType() and
      availBytes = arr.getByteSize()
    )
    or
    exists(AddressOfExpr aoe, ArrayExpr ae, VariableAccess va, ArrayType arr, int idx |
      aoe = stripped and
      ae = aoe.getOperand().getUnconverted() and
      va = ae.getArrayBase().getUnconverted() and
      checkableVarAccess(va, v) and
      arr = v.getUnspecifiedType() and
      idx = ae.getArrayOffset().getValue().toInt() and
      idx >= 0 and
      availBytes = arr.getByteSize() - idx * arr.getBaseType().getSize()
    )
    or
    exists(PointerAddExpr pae, VariableAccess va, ArrayType arr, int idx |
      pae = stripped and
      va = pae.getLeftOperand().getUnconverted() and
      checkableVarAccess(va, v) and
      arr = v.getUnspecifiedType() and
      idx = pae.getRightOperand().getValue().toInt() and
      idx >= 0 and
      availBytes = arr.getByteSize() - idx * arr.getBaseType().getSize()
    )
    or
    exists(AddressOfExpr aoe, VariableAccess va, Type t |
      aoe = stripped and
      va = aoe.getOperand().getUnconverted() and
      checkableVarAccess(va, v) and
      t = v.getUnspecifiedType() and
      not t instanceof ArrayType and
      not t instanceof PointerType and
      availBytes = t.getSize() and
      availBytes > 0
    )
  )
}

/**
 * Public `otcrypto` buffer, digest, and key structs with a pointer field and a length field.
 */
predicate structPtrLenSpec(
  string structName, string ptrFieldName, string lenFieldName, int elemBytes
) {
  structName in [
      "otcrypto_byte_buf", "otcrypto_const_byte_buf", "otcrypto_byte_buf_t",
      "otcrypto_const_byte_buf_t", "otcrypto_generic_buf", "otcrypto_generic_buf_t"
    ] and
  ptrFieldName = "data" and
  lenFieldName = "len" and
  elemBytes = 1
  or
  structName in [
      "otcrypto_word32_buf", "otcrypto_const_word32_buf", "otcrypto_word32_buf_t",
      "otcrypto_const_word32_buf_t", "otcrypto_hash_digest", "otcrypto_hash_digest_t"
    ] and
  ptrFieldName = "data" and
  lenFieldName = "len" and
  elemBytes = 4
  or
  structName in ["otcrypto_blinded_key", "otcrypto_blinded_key_t"] and
  ptrFieldName = "keyblob" and
  lenFieldName = "keyblob_length" and
  elemBytes = 1
  or
  structName in ["otcrypto_unblinded_key", "otcrypto_unblinded_key_t"] and
  ptrFieldName = "key" and
  lenFieldName = "key_length" and
  elemBytes = 1
}

/**
 * Foundational `(ptr, len)` memory and OTBN DMEM primitives.
 *
 * Any function declared in `sw/device/lib/base/hardened_memory.h` or
 * `sw/device/lib/base/memory.h` that takes one `size_t` length parameter and
 * one or more pointer parameters (`uint32_t *` -> 4 bytes/unit, `void *` or
 * `uint8_t *` -> 1 byte/unit) is discovered automatically, so newly added
 * `memcpy`/`memeq`/`memshred`-style helpers in those headers are checked
 * without modifying this query.
 */
predicate baseMemSpec(Function fn, int ptrArgIdx, int lenArgIdx, int unitBytes) {
  // Automatically discover all `(ptr, ..., size_t len)` functions in `hardened_memory.h` / `memory.h`
  exists(Parameter pPtr, Parameter pLen, PointerType pt |
    fn.getADeclarationEntry().getFile().getBaseName() in [
        "hardened_memory.h", "hardened_memory.c", "memory.h", "memory.c"
      ] and
    count(int i | fn.getParameter(i).getType().getName() = "size_t") = 1 and
    pLen = fn.getParameter(lenArgIdx) and
    pLen.getType().getName() = "size_t" and
    pPtr = fn.getParameter(ptrArgIdx) and
    pt = pPtr.getType().stripTopLevelSpecifiers() and
    if pt.getBaseType().getSize() = 4 then unitBytes = 4 else unitBytes = 1
  )
  or
  // Compiler builtins and libc aliases when not resolved through `memory.h`
  fn.getName() in ["memcpy", "ot_memcpy", "__builtin_memcpy", "memcmp", "ot_memcmp", "__builtin_memcmp"] and
  ptrArgIdx in [0, 1] and
  lenArgIdx = 2 and
  unitBytes = 1
  or
  fn.getName() in ["memset", "ot_memset", "__builtin_memset"] and
  ptrArgIdx = 0 and
  lenArgIdx = 2 and
  unitBytes = 1
  or
  // OTBN DMEM transfers (`sw/device/lib/crypto/drivers/otbn.h`)
  fn.getName() = "otbn_dmem_write" and ptrArgIdx = 1 and lenArgIdx = 0 and unitBytes = 4
  or
  fn.getName() = "otbn_dmem_read" and ptrArgIdx = 2 and lenArgIdx = 0 and unitBytes = 4
}

/**
 * Holds if `fn` is a constructor helper returning a struct in `structPtrLenSpec` by
 * assigning its parameters `(ptrParamIdx, lenParamIdx)` to `(ptrFieldName, lenFieldName)`.
 */
predicate constructorFnSpec(Function fn, int ptrParamIdx, int lenParamIdx, int elemBytes) {
  exists(
    string structName, string ptrFieldName, string lenFieldName, Parameter pPtr, Parameter pLen
  |
    structPtrLenSpec(structName, ptrFieldName, lenFieldName, elemBytes) and
    fn.getType().getName() = structName and
    pPtr = fn.getParameter(ptrParamIdx) and
    pLen = fn.getParameter(lenParamIdx) and
    (
      exists(ClassAggregateLiteral cal, Field ptrF, Field lenF |
        cal.getEnclosingFunction() = fn and
        ptrF.getName() = ptrFieldName and
        lenF.getName() = lenFieldName and
        cal.getAFieldExpr(ptrF).getUnconverted().(VariableAccess).getTarget() = pPtr and
        cal.getAFieldExpr(lenF).getUnconverted().(VariableAccess).getTarget() = pLen
      )
      or
      exists(AssignExpr aPtr, AssignExpr aLen |
        aPtr.getEnclosingFunction() = fn and
        aLen.getEnclosingFunction() = fn and
        aPtr.getLValue().(FieldAccess).getTarget().getName() = ptrFieldName and
        aLen.getLValue().(FieldAccess).getTarget().getName() = lenFieldName and
        aPtr.getRValue().getUnconverted().(VariableAccess).getTarget() = pPtr and
        aLen.getRValue().getUnconverted().(VariableAccess).getTarget() = pLen
      )
    )
  )
}

/**
 * Holds if `fn` splits `otcrypto_blinded_key_t *` parameter `paramIdx` into two
 * share pointers `(s0, s1)` via `keyblob_to_shares` and copies static array buffers
 * of sizes `bytes0` and `bytes1` into `s0` and `s1` (`reqBytes = bytes0 + bytes1`).
 */
predicate fnCopiesTwoStaticSharesToKeyblob(Function fn, int paramIdx, int reqBytes) {
  exists(
    Parameter p, LocalScopeVariable s0, LocalScopeVariable s1, FunctionCall toShares,
    FunctionCall copy0, FunctionCall copy1, int bytes0, int bytes1
  |
    toShares.getEnclosingFunction() = fn and
    toShares.getTarget().getName() = "keyblob_to_shares" and
    p = fn.getParameter(paramIdx) and
    toShares.getArgument(0).getUnconverted().(VariableAccess).getTarget() = p and
    toShares.getArgument(1).getUnconverted().(AddressOfExpr).getOperand().(VariableAccess).getTarget() = s0 and
    toShares.getArgument(2).getUnconverted().(AddressOfExpr).getOperand().(VariableAccess).getTarget() = s1 and
    copy0.getEnclosingFunction() = fn and
    copy1.getEnclosingFunction() = fn and
    baseMemSpec(copy0.getTarget(), 0, _, _) and
    baseMemSpec(copy1.getTarget(), 0, _, _) and
    copy0.getArgument(0).getUnconverted().(VariableAccess).getTarget() = s0 and
    copy1.getArgument(0).getUnconverted().(VariableAccess).getTarget() = s1 and
    bytes0 = copy0.getArgument(1).getUnconverted().getUnspecifiedType().(ArrayType).getByteSize() and
    bytes1 = copy1.getArgument(1).getUnconverted().getUnspecifiedType().(ArrayType).getByteSize() and
    reqBytes = bytes0 + bytes1
  )
}

/**
 * 1. Struct initializers (including `OTCRYPTO_MAKE_BUF`) where declared length exceeds capacity.
 */
predicate structPtrLenInitOverflow(ClassAggregateLiteral cal, string msg) {
  exists(
    string ptrFieldName, string lenFieldName, Field ptrField, Field lenField, Expr ptrExpr,
    Expr lenExpr, Variable v, int elemSize, int declLen, int declBytes, int capBytes
  |
    isInCryptoScope(cal) and
    structPtrLenSpec(cal.getType().getName(), ptrFieldName, lenFieldName, elemSize) and
    ptrField.getName() = ptrFieldName and
    lenField.getName() = lenFieldName and
    ptrExpr = cal.getAFieldExpr(ptrField) and
    lenExpr = cal.getAFieldExpr(lenField) and
    not exists(Variable lhs |
      lhs.getInitializer().getExpr() = cal and isIntentionalNegativeTestVar(lhs)
    ) and
    resolveStaticMemoryRegion(ptrExpr, v, capBytes) and
    declLen = lenExpr.getValue().toInt() and
    declBytes = declLen * elemSize and
    declBytes > capBytes and
    msg =
      "Buffer overflow in " + cal.getType().getName() + ": '" + v.getName() +
        "' has remaining capacity " + capBytes + " bytes, but '" + lenFieldName + "' declares " +
        declBytes + " bytes."
  )
}

/**
 * 2. Statement-level field assignments (`s.ptr = arr; s.len = N;`) where length exceeds capacity.
 */
predicate structFieldAssignOverflow(AssignExpr lenAssign, string msg) {
  exists(
    LocalScopeVariable sVar, string ptrFieldName, string lenFieldName, int elemSize,
    AssignExpr ptrAssign, FieldAccess ptrFa, FieldAccess lenFa, Variable v, int declLen,
    int declBytes, int capBytes
  |
    isInCryptoScope(lenAssign) and
    not isIntentionalNegativeTestVar(sVar) and
    structPtrLenSpec(sVar.getType().getName(), ptrFieldName, lenFieldName, elemSize) and
    ptrFa = ptrAssign.getLValue() and
    ptrFa.getQualifier().(VariableAccess).getTarget() = sVar and
    ptrFa.getTarget().getName() = ptrFieldName and
    lenFa = lenAssign.getLValue() and
    lenFa.getQualifier().(VariableAccess).getTarget() = sVar and
    lenFa.getTarget().getName() = lenFieldName and
    ptrAssign.getEnclosingFunction() = lenAssign.getEnclosingFunction() and
    count(AssignExpr other |
      other.getLValue().(FieldAccess).getQualifier().(VariableAccess).getTarget() = sVar and
      other.getLValue().(FieldAccess).getTarget().getName() = ptrFieldName
    ) = 1 and
    resolveStaticMemoryRegion(ptrAssign.getRValue(), v, capBytes) and
    declLen = lenAssign.getRValue().getValue().toInt() and
    declBytes = declLen * elemSize and
    declBytes > capBytes and
    msg =
      "Buffer overflow on " + sVar.getName() + "." + lenFieldName + ": '" + v.getName() +
        "' has remaining capacity " + capBytes + " bytes, but assigned length is " + declBytes +
        " bytes."
  )
}

/**
 * 3. Calls to any struct constructor helper where the length argument exceeds buffer capacity.
 */
predicate constructorHelperOverflow(FunctionCall fc, string msg) {
  exists(
    int ptrArgIdx, int lenArgIdx, int elemSize, Variable v, int declLen, int declBytes, int capBytes
  |
    isInCryptoScope(fc) and
    not isIntentionalNegativeTestCall(fc) and
    constructorFnSpec(fc.getTarget(), ptrArgIdx, lenArgIdx, elemSize) and
    resolveStaticMemoryRegion(fc.getArgument(ptrArgIdx), v, capBytes) and
    declLen = fc.getArgument(lenArgIdx).getValue().toInt() and
    declBytes = declLen * elemSize and
    declBytes > capBytes and
    msg =
      "Buffer overflow in " + fc.getTarget().getName() + ": '" + v.getName() +
        "' has remaining capacity " + capBytes + " bytes, but declared length is " + declBytes +
        " bytes."
  )
}

/**
 * 4. Calls to any `(ptr, len)` memory or DMEM primitive where a static memory region is
 *    smaller than the constant length passed.
 */
predicate memHelperOverflow(FunctionCall fc, string msg) {
  exists(
    Function fn, int ptrArgIdx, int lenArgIdx, int unitBytes, Variable v, int lenUnits,
    int reqBytes, int capBytes
  |
    isInCryptoScope(fc) and
    not isIntentionalNegativeTestCall(fc) and
    fn = fc.getTarget() and
    baseMemSpec(fn, ptrArgIdx, lenArgIdx, unitBytes) and
    resolveStaticMemoryRegion(fc.getArgument(ptrArgIdx), v, capBytes) and
    lenUnits = fc.getArgument(lenArgIdx).getValue().toInt() and
    reqBytes = lenUnits * unitBytes and
    reqBytes > capBytes and
    msg =
      "Buffer overflow in " + fn.getName() + ": '" + v.getName() + "' has remaining capacity " +
        capBytes + " bytes, but call accesses " + reqBytes + " bytes."
  )
}

/**
 * 5. Calls to a function that populates two shares of an `otcrypto_blinded_key_t` from
 *    statically sized buffers whose combined size exceeds the caller's `.keyblob` capacity.
 */
predicate keyblobShareCopyOverflow(FunctionCall fc, string msg) {
  exists(
    Function fn, int paramIdx, Variable keyVar, ClassAggregateLiteral cal, Field ptrField,
    Variable backingVar, int capBytes, int reqBytes
  |
    isInCryptoScope(fc) and
    not isIntentionalNegativeTestCall(fc) and
    fn = fc.getTarget() and
    fnCopiesTwoStaticSharesToKeyblob(fn, paramIdx, reqBytes) and
    fc.getArgument(paramIdx).getAChild*().(VariableAccess).getTarget() = keyVar and
    not isIntentionalNegativeTestVar(keyVar) and
    cal = keyVar.getInitializer().getExpr() and
    ptrField.getName() = "keyblob" and
    resolveStaticMemoryRegion(cal.getAFieldExpr(ptrField), backingVar, capBytes) and
    capBytes < reqBytes and
    msg =
      "Buffer overflow in " + fn.getName() + ": '" + backingVar.getName() + "' has capacity " +
        capBytes + " bytes, but " + fn.getName() + " copies " + reqBytes +
        " bytes into keyblob shares."
  )
}

from Element loc, string msg
where
  structPtrLenInitOverflow(loc, msg) or
  structFieldAssignOverflow(loc, msg) or
  constructorHelperOverflow(loc, msg) or
  memHelperOverflow(loc, msg) or
  keyblobShareCopyOverflow(loc, msg)
select loc, msg
