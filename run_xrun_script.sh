#!/usr/bin/env bash
# HMAC UVM TB Compile Check Script
# Usage: ./compile_check.sh [--purge]
#
# Runs a compile-only (--build-only) flow using dvsim.py with Xcelium
# to verify syntactic correctness of the HMAC DV testbench.
#
# Pass/Fail is determined by:
#   - dvsim exit code (0 = pass, non-zero = fail)
#   - Absence of "*E" (error) lines in build.log
#
# Build log: $OPENTITAN_ROOT/scratch/master/hmac-sim-xcelium/default/build.log

set -uo pipefail

OPENTITAN_ROOT="./"
SIM_CFG="./hw/ip/hmac/dv/hmac_sim_cfg.hjson"
BUILD_LOG="${OPENTITAN_ROOT}scratch/master/hmac-sim-xcelium/default/build.log"

# Optional --purge flag to force a clean rebuild
PURGE_FLAG=""
if [[ "${1:-}" == "--purge" ]]; then
  PURGE_FLAG="--purge"
  echo "[INFO] Running with --purge: scratch directory will be cleaned before build."
fi

echo "========================================================"
echo " HMAC UVM TB Compile Check (Xcelium via dvsim)"
echo " Timestamp: $(date -u)"
echo "========================================================"

cd "${OPENTITAN_ROOT}"

python3 util/dvsim/dvsim.py "${SIM_CFG}" \
  -t xcelium \
  --build-only \
  -i hmac_smoke \
  --local \
  ${PURGE_FLAG}

BUILD_EXIT=$?

echo ""
echo "========================================================"
echo " Build Log Summary"
echo "========================================================"

if [[ -f "${BUILD_LOG}" ]]; then
  echo "[Xcelium Summary]"
  grep -E "errors:|warnings:|Exiting on" "${BUILD_LOG}" | tail -5 || true

  echo ""
  echo "[Errors (non-suppressed *E)]"
  ERRORS=$(grep -E "^\*E" "${BUILD_LOG}" 2>/dev/null || true)
  if [[ -n "${ERRORS}" ]]; then
    echo "${ERRORS}" | head -20
    ERROR_COUNT=$(echo "${ERRORS}" | wc -l | tr -d ' ')
    echo ""
    echo "RESULT: FAIL  (${ERROR_COUNT} error(s) found)"
  else
    echo "  None"
    echo ""
    echo "RESULT: PASS  (0 errors)"
  fi
else
  echo "[WARN] Build log not found at: ${BUILD_LOG}"
fi

echo "========================================================"

exit ${BUILD_EXIT}