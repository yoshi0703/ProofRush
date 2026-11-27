#!/usr/bin/env bash
set -euo pipefail

export PATH="$HOME/.elan/bin:$PATH"

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
CMD="${1:-}"
WT_NAME="${2:-}"      # 例: prob-042-prover
PROB_ID="${3:-}"      # 例: Prob042

# macOS / Linux 両対応のSHA-256関数
calc_sha256() {
  if command -v sha256sum >/dev/null 2>&1; then
    sha256sum "$1" | awk '{print $1}'
  else
    shasum -a 256 "$1" | awk '{print $1}'
  fi
}

case "$CMD" in
  init-base)
    echo "[Init] Fetching precompiled Mathlib cache in main..."
    mkdir -p "${ROOT_DIR}/state/locks" "${ROOT_DIR}/worktrees"
    (cd "${ROOT_DIR}/Formal" && lake exe cache get && lake build)
    echo "[Init] Base Lean 4 + Mathlib cache ready."
    ;;

  create)
    if [[ -z "${WT_NAME}" || -z "${PROB_ID}" ]]; then
      echo "Usage: $0 create <wt_name> <prob_id>" >&2
      exit 1
    fi
    WT_PATH="${ROOT_DIR}/worktrees/${WT_NAME}"
    BRANCH="attack/${WT_NAME}"
    STMT_REL="Formal/Problems/${PROB_ID}/Statement.lean"

    # 1. Statement.lean の基準ハッシュをワーカー圏外（state/locks/）に固定保存
    if [[ ! -f "${ROOT_DIR}/${STMT_REL}" ]]; then
      echo "Error: ${STMT_REL} does not exist on main." >&2
      exit 1
    fi
    mkdir -p "${ROOT_DIR}/state/locks" "${ROOT_DIR}/worktrees"
    calc_sha256 "${ROOT_DIR}/${STMT_REL}" > "${ROOT_DIR}/state/locks/${PROB_ID}.sha256"

    # 2. 独立ブランチで git worktree を作成
    git -C "${ROOT_DIR}" worktree add "${WT_PATH}" -b "${BRANCH}" HEAD

    # 3. Mathlib パッケージキャッシュを共有し、ローカルビルド出力先のみ独立作成
    mkdir -p "${WT_PATH}/Formal/.lake/build"
    if [[ -d "${ROOT_DIR}/Formal/.lake/packages" ]]; then
      ln -s "${ROOT_DIR}/Formal/.lake/packages" "${WT_PATH}/Formal/.lake/packages"
    else
      echo "[Warn] ${ROOT_DIR}/Formal/.lake/packages not found. Run '$0 init-base' first." >&2
    fi

    echo "[Ready] Worktree ${WT_PATH} initialized with shared Mathlib cache and locked Statement hash."
    ;;

  create-env)
    if [[ -z "${WT_NAME}" ]]; then
      echo "Usage: $0 create-env <wt_name>" >&2
      exit 1
    fi
    WT_PATH="${ROOT_DIR}/worktrees/${WT_NAME}"
    BRANCH="env/${WT_NAME}"
    mkdir -p "${ROOT_DIR}/worktrees"
    git -C "${ROOT_DIR}" worktree add "${WT_PATH}" -b "${BRANCH}" HEAD
    echo "[Ready] Environmental track worktree ${WT_PATH} initialized (branch ${BRANCH})."
    ;;

  remove)
    if [[ -z "${WT_NAME}" ]]; then
      echo "Usage: $0 remove <wt_name>" >&2
      exit 1
    fi
    WT_PATH="${ROOT_DIR}/worktrees/${WT_NAME}"
    # シンボリックリンクを先に解除してから worktree を安全に削除
    rm -f "${WT_PATH}/Formal/.lake/packages"
    git -C "${ROOT_DIR}" worktree remove --force "${WT_PATH}"
    echo "[Cleaned] Removed worktree ${WT_NAME} (branch preserved for audit)."
    ;;

  list)
    git -C "${ROOT_DIR}" worktree list
    ;;

  *)
    echo "Usage: $0 {init-base | create <wt_name> <prob_id> | create-env <wt_name> | remove <wt_name> | list}" >&2
    exit 1
    ;;
esac
