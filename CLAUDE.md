@AGENTS.md

## Claude Code 固有運用ガイド

- 短時間の候補調査・懸賞規約確認は `.claude/agents/discovery-triage.md`（Subagent）を並列呼び出しせよ。
- 新規定式化の空真・型仕様バグ検査は `.claude/agents/statement-auditor.md`（Subagent）に委譲し、`APPROVED` を得るまで本証明を開始してはならない。
- 長時間の証明・反例探索・環境シミュレーションはコンテキスト溢れ防止のため `./scripts/worktree_ctl.sh create` と `./scripts/dispatch_worker.sh claude ...` で独立 worktree にて非同期実行せよ。
- 状態ファイル（`state/backlog.json`, `state/dead_ends.md`）の更新は必ず `python3 scripts/state_ctl.py` 経由で行え。
- 外部公開・プッシュ系コマンドは `.claude/settings.json` で遮断されている。公開が必要な場合は必ずユーザーへ報告し承認を得よ。
