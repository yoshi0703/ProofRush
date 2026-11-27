#!/usr/bin/env bash
set -euo pipefail

export PATH="$HOME/.elan/bin:/opt/homebrew/bin:$HOME/.local/bin:$PATH"

# 使い方: ./scripts/dispatch_worker.sh <claude|codex> <wt_name> <prob_id> <prover|counterex|env>
if [[ $# -lt 4 ]]; then
  echo "Usage: $0 <claude|codex> <wt_name> <prob_id> <prover|counterex|env>" >&2
  exit 1
fi

ENGINE="$1"
WT_NAME="$2"
PROB_ID="$3"
ROLE="$4"

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
WT_PATH="${ROOT_DIR}/worktrees/${WT_NAME}"
LOG_FILE="${WT_PATH}/worker_stdout.log"

if [[ ! -d "${WT_PATH}" ]]; then
  echo "Error: Worktree ${WT_PATH} does not exist. Create it with scripts/worktree_ctl.sh first." >&2
  exit 1
fi

if [[ "$ROLE" == "env" ]]; then
  TARGET_DIR="EnvTrack/${PROB_ID}/"
  RULES="1. 公開実データを用いた再現可能な数値実験コード、既存ベースラインとの定量ベンチマーク比較、感度分析・統計的検定を実施せよ。
  2. 終了時は必ず \`worker_report.json\` に \`{\"status\": \"solved|partial_progress|stalled\", \"new_lemmas\": [...], \"metrics\": {...}, \"dead_ends\": [...]}\` を出力せよ。"
else
  TARGET_DIR="Formal/Problems/${PROB_ID}/"
  RULES="1. \`Statement.lean\` および \`lakefile.toml\` は一切編集してはならない。\`Solution.lean\`（または補助スクリプト）のみを編集せよ。
  2. \`sorry\`, \`axiom\`, \`unsafe\`, \`@[implemented_by]\`, \`@[extern]\`, \`native_decide\` は使用禁止。
  3. 終了時は必ず \`worker_report.json\` に \`{\"status\": \"solved|counterexample_found|partial_lemma|stalled\", \"new_lemmas\": [...], \"dead_ends\": [...]}\` を出力せよ。"
fi

# ワーカー専用の局所タスク指示書を生成（不要な全体コンテキストを遮断）
cat > "${WT_PATH}/WORKER_TASK.md" <<EOF
# Assigned Task: ${PROB_ID} (Role: ${ROLE})
- 対象問題ディレクトリ: \`${TARGET_DIR}\`
- 参照すべき失敗履歴（読取専用）: \`${ROOT_DIR}/state/dead_ends.md\`
- **厳守事項**:
  ${RULES}
EOF

PROMPT="WORKER_TASK.md を読み、割り当てられた ${ROLE} ロールを完遂して worker_report.json を出力せよ。"

# OSレベルのタイムアウト関数（45分で強制Stop-Loss）
run_with_timeout() {
  python3 -c 'import subprocess, sys; sys.exit(subprocess.call(sys.argv[2:], timeout=int(sys.argv[1])))' 2700 "$@"
}

CLAUDE_MODEL="${CLAUDE_MODEL:-opus}"
CODEX_MODEL="${CODEX_MODEL:-}"

if [[ "$ENGINE" == "claude" ]]; then
  if ! command -v claude >/dev/null 2>&1; then
    echo "Error: 'claude' CLI not found in PATH." >&2
    exit 1
  fi
  (
    cd "${WT_PATH}"
    run_with_timeout claude -p "${PROMPT}" \
      --model "${CLAUDE_MODEL}" \
      --max-turns 25 \
      --allowedTools "Bash,Read,Edit,Write,Grep,Glob" \
      --output-format json > "${LOG_FILE}" 2>&1
  ) &
elif [[ "$ENGINE" == "codex" ]]; then
  if ! command -v codex >/dev/null 2>&1; then
    echo "Error: 'codex' CLI not found in PATH." >&2
    exit 1
  fi
  CODEX_MODEL_ARGS=()
  if [[ -n "${CODEX_MODEL}" ]]; then
    CODEX_MODEL_ARGS=(-m "${CODEX_MODEL}")
  fi
  (
    run_with_timeout codex exec \
      --cd "${WT_PATH}" \
      --sandbox workspace-write \
      "${CODEX_MODEL_ARGS[@]}" \
      -c model_reasoning_effort='"high"' \
      "${PROMPT}" > "${LOG_FILE}" 2>&1
  ) &
else
  echo "Error: Unsupported engine '${ENGINE}'. Use 'claude' or 'codex'." >&2
  exit 1
fi

echo $! > "${WT_PATH}/worker.pid"
echo "[Dispatched] PID $(cat "${WT_PATH}/worker.pid") running ${ENGINE} (${ROLE}) in ${WT_PATH}"
