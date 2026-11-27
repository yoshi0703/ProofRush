#!/usr/bin/env bash
set -euo pipefail

export PATH="$HOME/.elan/bin:$PATH"

if [[ $# -lt 3 ]]; then
  echo "Usage: $0 <wt_name> <prob_id> <theorem_name>" >&2
  exit 1
fi

WT_NAME="$1"
PROB_ID="$2"
THEOREM_NAME="$3"   # 例: main_conjecture

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
WT_FORMAL="${ROOT_DIR}/worktrees/${WT_NAME}/Formal"
PROB_DIR="${WT_FORMAL}/Problems/${PROB_ID}"
LOCK_FILE="${ROOT_DIR}/state/locks/${PROB_ID}.sha256"

if [[ ! -f "${LOCK_FILE}" ]]; then
  echo "[REJECT] Lock file not found: ${LOCK_FILE}" >&2
  exit 1
fi

if [[ ! -f "${PROB_DIR}/Statement.lean" || ! -f "${PROB_DIR}/Solution.lean" ]]; then
  echo "[REJECT] Statement.lean or Solution.lean missing in ${PROB_DIR}" >&2
  exit 1
fi

# 1. Statement.lean の完全一致検証（1バイトの改変も許さない）
EXPECTED_HASH="$(cat "${LOCK_FILE}")"
if command -v sha256sum >/dev/null 2>&1; then
  ACTUAL_HASH="$(sha256sum "${PROB_DIR}/Statement.lean" | awk '{print $1}')"
else
  ACTUAL_HASH="$(shasum -a 256 "${PROB_DIR}/Statement.lean" | awk '{print $1}')"
fi

if [[ "${EXPECTED_HASH}" != "${ACTUAL_HASH}" ]]; then
  echo "[REJECT] Statement.lean hash mismatch! Tampering detected." >&2
  echo "  Expected: ${EXPECTED_HASH}" >&2
  echo "  Actual:   ${ACTUAL_HASH}" >&2
  exit 1
fi

# 2. カーネル回避プリミティブの静的スキャン
if grep -rnE '@\[implemented_by|@\[extern|unsafe |native_decide' "${PROB_DIR}/"; then
  echo "[REJECT] Banned compiler bypass attribute detected." >&2
  exit 1
fi

# 3. 対象モジュールをビルドし、Leanカーネルレベルで #print axioms を強制検証
(cd "${WT_FORMAL}" && lake build "Problems.${PROB_ID}.Statement" "Problems.${PROB_ID}.Solution")

AUDIT_FILE="${WT_FORMAL}/AuditKernel_${PROB_ID}.lean"
trap 'rm -f "${AUDIT_FILE}"' EXIT

cat > "${AUDIT_FILE}" <<EOF
import Problems.${PROB_ID}.Statement
import Problems.${PROB_ID}.Solution

#print axioms ${THEOREM_NAME}
EOF

AXIOM_OUT="$(cd "${WT_FORMAL}" && lake env lean "${AUDIT_FILE}" 2>&1)"
echo "${AXIOM_OUT}"

# sorryAx や独自公理が含まれていないか厳密判定（標準3公理または公理なしのみ許可）
python3 - "${AXIOM_OUT}" "${THEOREM_NAME}" <<'PY'
import re, sys
out, thm = sys.argv[1], sys.argv[2]
allowed = {"propext", "Classical.choice", "Quot.sound"}

if f"'{thm}' does not depend on any axioms" in out:
    print(f"[PASS] Verified cleanly with no axioms: {thm}")
    sys.exit(0)

m = re.search(rf"'{re.escape(thm)}' depends on axioms: \[(.*?)\]", out)
if not m:
    print("[REJECT] Failed to parse #print axioms output.", file=sys.stderr)
    sys.exit(1)

used = {x.strip() for x in m.group(1).split(",") if x.strip()}
illegal = used - allowed
if illegal:
    print(f"[REJECT] Illegal axioms detected (including sorryAx or custom): {illegal}", file=sys.stderr)
    sys.exit(1)

print(f"[PASS] Verified cleanly with standard axioms: {sorted(used)}")
PY
