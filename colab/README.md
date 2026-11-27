# ProofRush — Google Colab Cloud Runner

ローカル Mac で Codex が稼働している間、**Google AI Pro 付属の Google Colab（月 200 Compute Units）** を使ってクラウド側で並列に Lean 4 証明検証・反例探索・環境科学シミュレーションを回すためのセットアップです。

## おすすめのランタイム使い分け（Compute Units 節約）

| 用途 | 推奨ランタイム | 理由 |
| --- | --- | --- |
| **Tier A/B: Lean 4 ビルド・証明・SAT反例探索** | **CPU（ハイメモリ / High-RAM）** | GPUより消費ユニットが圧倒的に少なく、50GB超のRAMとマルチコアCPUで `lake build` や複数 `worktree` 並列が快適 |
| **Tier C: 環境科学シミュレーション・ML・大規模行列計算** | **GPU（L4 / T4 / A100）** | 数値実験・大規模データ処理の高速化が必要なタスクのみGPUを選択 |

## 使い方

1. [ProofRush_Colab_Runner.ipynb](./ProofRush_Colab_Runner.ipynb) を Google Colab で開く（Google Drive にアップロードして開くか、GitHub へ push 後は Colab の「GitHub」タブから `yoshi0703/ProofRush` を選択して直接開けます）。
2. メニュー「ランタイム」→「ランタイムのタイプを変更」で、用途に応じたランタイム（Lean 4 / SAT 中心なら **CPU + ハイメモリ**）を選択。
3. セル 1〜5 を上から順に実行すると、Google Drive に Mathlib キャッシュを永続化しつつ、ローカルと同じ `worktree_ctl.sh` / `verify_gate.sh` がクラウド上でそのまま動作します。

## ローカル（Codex）との役割分担イメージ

- **ローカル Mac（Codex）**: オーケストレーション・軽量探索・定式化監査・Git統合
- **Google Colab（クラウド）**: 重い計算ワーカー（複数 worktree での Lean 4 検証、Python/Z3/PySAT による大規模反例探索、Tier C 海洋データ数値実験）
- **成果の受け渡し**: Google Drive（`/MyDrive/ProofRush_Cloud/`）または専用ブランチ経由で `solved/` と `worker_report.json` を回収（`state/backlog.json` の書き込みはローカル Orchestrator に一本化）
