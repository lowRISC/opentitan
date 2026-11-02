// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * @name OpenTitan Crypto Incomplete Key Share Wipe
 * @description Identifies functions that shred one secret share field of a multi-share struct without wiping the paired share field.
 * @kind problem
 * @problem.severity error
 * @id cpp/opentitan-crypto-incomplete-share-wipe
 */

import cpp

/**
 * Holds if `fA` and `fB` are paired `<prefix>0` / `<prefix>1` fields of the
 * same type on struct `s`.
 */
predicate pairedShareFields(Struct s, Field fA, Field fB) {
  exists(string prefix |
    fA = s.getAField() and
    fB = s.getAField() and
    fA.getType() = fB.getType() and
    (
      fA.getName() = prefix + "0" and fB.getName() = prefix + "1"
      or
      fA.getName() = prefix + "1" and fB.getName() = prefix + "0"
    )
  )
}

/**
 * Holds if `fc` wipes field `f` of struct variable or pointer `v` (including
 * nested `.data` arrays like `v->state0.data` or `v.d0.data`).
 */
predicate wipesStructField(FunctionCall fc, Variable v, Field f) {
  fc.getTarget().getName() in ["hardened_memshred", "memset", "ot_memset", "__builtin_memset"] and
  exists(FieldAccess fa |
    fa = fc.getArgument(0).getAChild*() and
    fa.getQualifier().(VariableAccess).getTarget() = v and
    fa.getTarget() = f
  )
}

/**
 * Holds if `fc` wipes the entire struct `v` (e.g. `hardened_memshred((uint32_t *)&v, ...)`
 * or `hardened_memshred((uint32_t *)v, ...)`).
 */
predicate wipesWholeStruct(FunctionCall fc, Variable v) {
  fc.getTarget().getName() in ["hardened_memshred", "memset", "ot_memset", "__builtin_memset"] and
  (
    fc.getArgument(0).getUnconverted().(AddressOfExpr).getOperand().(VariableAccess).getTarget() = v
    or
    fc.getArgument(0).getUnconverted().(VariableAccess).getTarget() = v
  )
}

from Function fn, FunctionCall fc0, Variable v, Struct s, Field wipedField, Field missingField
where
  fn.getFile().getAbsolutePath().matches("%/sw/device/lib/crypto/%") and
  fc0.getEnclosingFunction() = fn and
  fc0.getTarget().getName() = "hardened_memshred" and
  pairedShareFields(s, wipedField, missingField) and
  wipesStructField(fc0, v, wipedField) and
  not exists(FunctionCall fc1 |
    fc1.getEnclosingFunction() = fn and
    (
      wipesStructField(fc1, v, missingField) or
      wipesWholeStruct(fc1, v)
    )
  )
select fc0,
  "Function '" + fn.getName() + "' shreds '" + v.getName() + "." + wipedField.getName() +
    "', but never wipes '" + v.getName() + "." + missingField.getName() + "'."
