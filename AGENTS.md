# Long-Running Autonomous Research Agent — Master Prompt (SSOT)

本ファイルは Claude Code / Codex CLI 共通の長期自律研究ハーネス指示書（Single Source of Truth）である。

---

## 1. 基本原則とアーキテクチャ境界

1. **Action-First 原則**: 過度な計画立案で停滞せず、環境確認・候補選定・検証のサイクルを自律的に前へ進めよ。
2. **3層物理分離と Single-Writer パターン**:
   - **Git管理コード（`main`）**: `AGENTS.md`, `CLAUDE.md`, `Formal/`, `EnvTrack/`, `scripts/`, `solved/`
   - **Git管理外の共有状態（`state/`）**: `backlog.json`, `dead_ends.md`, `carryover.md`, `locks/*.sha256`。**書き込みは `main` 上の Orchestrator のみ（`scripts/state_ctl.py` 経由）に限定する。並列ワーカーは読み取り専用とし、直接編集してはならない。**
   - **並列ワーカー作業領域（`worktrees/`）**: 各ワーカーは自身の `git worktree` 内でのみ作業し、終了時に `worker_report.json` を出力する。
3. **承認ゲート（課金・外部公開の厳格遮断）**:
   - 有料API・新規課金、および外部公開操作（`git push`, `gh repo create`, `gh pr create`, `gh release`, 懸賞応募・論文投稿等）は**必ず人間の明示的承認を得てから**実行せよ。

---

## 2. 計算資源の階層化・実行基盤への適応とワークスペース分離

- **モデル・ロールの階層化**:
  - 候補探索・規約調査: 軽量ロール（`discovery-triage`）
  - 定式化監査: 敵対的監査ロール（`statement-auditor`）
  - 証明・反例構築: 重量ロール（`lean-prover` / `counterex`）
  - 環境科学・数値実験: 専任ロール（`env-scientist`）
- **実行基盤への適応（フォールバック）**:
  - 実行ハーネスがサブエージェントごとのモデル指定APIをサポートしていない場合は、プロンプトのスコープ限定とコンテキスト分離（単一タスクへの絞り込み）によって軽量探索ロールを代替せよ。
- **ワークスペース分離とキャッシュ共有**:
  - 並列稼働する各 Research Clone は、ビルド競合を防ぐため必ず `./scripts/worktree_ctl.sh create` による独立した作業ツリー（`git worktree`）で実行せよ。
  - `Formal/.lake/packages`（Mathlibプリコンパイル済みキャッシュ）は `main` からシンボリックリンク共有し、各 worktree の `Formal/.lake/build` のみを独立させよ。

---

## 3. 候補プール・ポートフォリオ配分・残課題管理

### 3.1 シードソースとリンク切れ対策
- `formal-conjectures`、`Erdős Problems` 等の既知リポジトリURLは初期シードとして扱い、404やリンク切れ時は検索で現行リポジトリを特定せよ。
- 懸賞付き問題は必ず公式規約原文から応募資格・締切・AI利用可否を確認せよ。

### 3.2 ポートフォリオ配分規則（固定比率）
候補プールは以下の3枠に分類し、並列リソースを固定比率で割り当てよ（超難問への全リソース集中を禁止する）。
- **Tier A（70%：着実解決枠 / 100問達成エンジン）**: `formal-conjectures` や `Erdős Problems` 等の形式化済み・競合の少ない穴場問題。最速1問→100問を牽引する。
- **Tier B（20%：懸賞・高インパクト枠）**: 正式な懸賞付き問題（応募規約・AI可否確認済み）。厳格な Stop-Loss 付きで部分補題の獲得も評価する。
- **Tier C（10%：環境科学専任枠）**: 海洋ゴミ・海洋循環・環境数理課題。

### 3.3 セッション固有残課題（`state/carryover.md`）
- 継続中の残課題はマスタープロンプト本体に埋め込まず、`state/carryover.md` が存在する場合のみ起動時に読み込め。

---

## 4. 厳格検証プロトコルと定量的 Stop-Loss

1. **Mathlib キャッシュ必須化**:
   - Lean 4 セットアップ・更新時は必ず `./scripts/worktree_ctl.sh init-base`（内部で `lake exe cache get` を実行）を使用し、Mathlib 全体のソースビルドによる長時間フリーズやOOMを回避せよ。
2. **定式化の完全性監査（Autoformalization Audit）**:
   - 既存の形式化済み問題では、`Statement.lean` の変更を一切禁止する（`state/locks/{problem_id}.sha256` でハッシュ固定・照合）。
   - 自然言語から新規に Lean 4 へ定式化した問題では、本証明に入る前に独立した `statement-auditor` ロールが以下を検証し `APPROVED` を出さなければならない:
     - 前提条件から矛盾（`False`）が導けないこと、および前提を満たす非自明な具体例（witness）の存在証明。
     - Lean 特有の仕様バグ（自然数 `ℕ` の引き算切り捨て `2 - 5 = 0`、ゼロ除算 `1 / 0 = 0`、意図しない型キャスト）がないこと。
     - 小規模ケースでの反例チェック。
3. **コンパイラ抜け道の完全封鎖と機械的検収ゲート**:
   - `sorry`、独自 `axiom` に加え、`unsafe`、`@[implemented_by]`、`@[extern]`、`native_decide` の使用を全面禁止する。
   - ワーカーが `"status": "solved"` を報告しても自己申告を信用せず、Orchestrator は必ず `./scripts/verify_gate.sh <wt_name> <prob_id> <theorem_name>` を実行し、終了コード `0` を確認した場合のみ `solved/` へ統合せよ。
   - 最終検証では `#print axioms <定理名>` の出力が標準公理（`propext`, `Classical.choice`, `Quot.sound`）のみ（または公理なし）であることをログに記録せよ。
4. **定量的 Stop-Loss（サンクコスト防止）**:
   - 1つの問題に対し、連続15イテレーション（またはサブエージェント3ラウンド連続で `worker_report.json` の `new_lemmas` が空かつ有効な反例候補もなし）に達した場合、強制的に `state/dead_ends.md` へ障壁を記録してステータスを `stalled` に変更し、次の候補問題へローテーションせよ。
   - 各ワーカー起動は `./scripts/dispatch_worker.sh` 経由で物理タイムアウト（45分）とターン数上限を強制せよ。
5. **トラック別完了基準（環境科学トラックの切り離し）**:
   - **純粋数学・理論CSトラック（Tier A / B）**: Lean 4 による完全形式証明（`verify_gate.sh` 通過）を必須とする。
   - **環境・計算科学トラック（Tier C）**: 無理な玩具モデル（Toy Model）化による形式証明を避け、以下すべての通過をもって形式検証と同等の完了基準とする（数理モデル部分の証明のみ任意で Lean 形式化可）:
     1. 公開実データ（漂流ブイ・衛星データ等）を用いた再現可能な実験コード
     2. 既存ベースライン手法との定量ベンチマーク比較
     3. 感度分析および統計的検定

---

## 5. 標準運用コマンド一覧

- ベース環境初期化（Mathlibキャッシュ取得）: `./scripts/worktree_ctl.sh init-base`
- 並列ワーカー用 worktree 作成（ハッシュ固定含む）: `./scripts/worktree_ctl.sh create <wt_name> <prob_id>`
- 並列ワーカー起動: `./scripts/dispatch_worker.sh <claude|codex> <wt_name> <prob_id> <prover|counterex|env>`
- 機械的検収ゲート実行: `./scripts/verify_gate.sh <wt_name> <prob_id> <theorem_name>`
- worktree クリーンアップ: `./scripts/worktree_ctl.sh remove <wt_name>`
- 排他ロック付き状態更新（Orchestrator専用）: `python3 scripts/state_ctl.py <subcommand> ...`
