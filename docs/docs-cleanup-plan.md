# Stage 1 完了後の docs cleanup と mdBook 導入計画

状態: 計画。Stage 1 完了後に実施する。現時点では docs の再編、mdBook の導入、サイト公開は未実施。

作成日: 2026-10-27（JST）。現状の基準はコミット `6622e6f` の
[README](../README.md)、[実装ロードマップ](stage1-roadmap.md)、テストである。
本書は整理作業の計画であり、Stage 1 の実装完了や形式検証の範囲を拡張するものではない。

## 1. 開始条件と整理の目的

現在の実装は Stage 1b と path package / call-only module import の基盤までであり、
歴史的な Stage 1 全体の完了ではない。
[v0.3 の Stage 1](design/roadmap-acceptance.md#14-initial-implementation-sequence) は、
独立ラムダや有限ディスパッチに加え、関数の編集権限、宣言的差分の合成、影響範囲、
義務の移譲と修復、ストレージ所有権、基本線形代数などを含む。

整理開始時に、実装ロードマップへ次を記録する。

- Stage 1 の完了対象と受入条件、対応する実装・テスト・証明・CI の証拠。
- 完了したコミットまたはタグ、および残る制限・未解決事項。
- 原設計から範囲を変更した場合、その理由と移した項目。未実装項目を黙って完了扱いにしない。

この基準を確定してから、利用者が「使える機能」「使い方」「保証の範囲」「将来設計」を
区別して読めるように整理する。Stage 1 完了までの正確性修正は通常の開発とともに続ける。
cleanup のために言語仕様や証明の意味を変更せず、不整合が見つかった場合は根拠を確認して修正する。

## 2. 文書の役割と正本

| 文書群 | 整理後の役割 | 方針 |
| --- | --- | --- |
| ルート `README.md` | リポジトリの入口 | 概要、現在の到達点、最短のビルド例、book と詳細仕様へのリンクに絞る |
| `docs/README.md`（新規） | book の入口 | 読者別の案内と実装状況表を置く。README の手順全文を複製しない |
| `docs/guide/`（新規） | 利用手順 | 導入、CLI、実行例、ライブラリ利用、診断をまとめる |
| `docs/stage0.md`、`stage1a.md`、`stage1b.md`、`packages.md` | 実装仕様 | 既存パスを保ち、Stage 1 完了時点の契約と制限を照合する。後続 increment の仕様も接続する |
| `docs/protocol.md` | フロントエンド／kernel 間の契約 | public wire protocol と内部 core を区別し、互換性・独立検査の境界を明記する |
| `docs/verification.md` | 証明範囲の正本 | 定理、対象となる実装定義、仮定、未証明部分、回帰テストを区別する |
| `docs/development/`（新規） | 開発者向け手順 | アーキテクチャ、検証コマンド、docs 更新手順を集約する |
| `docs/stage1-roadmap.md`、本書 | 開発計画・履歴 | 完了記録と今後の計画を区別し、現在の仕様は個別仕様書へ案内する |
| `docs/design.md`、`docs/design/` | 歴史的設計と研究上の背景 | v0.3 保存本文を維持し、現行仕様との違いは索引や別文書に書く |
| `stdlib/README.md`、`AGENTS.md` | 各ディレクトリの入口／貢献規約 | 標準ライブラリの詳細は book 内の正本へ集約し、入口を残す。貢献規約はコピーせず参照する |

実装状況表は「機能／仕様書／実装と回帰テスト／証明と仮定／制限・後続課題」を列にする。
実装済み、試験済み、証明済み、仮定、提案、延期を同一の状態として扱わない。
README の短い状況説明はこの表と同期し、証明の説明は `verification.md` を参照する。
現行仕様は既存の英語を基本に、案内・計画の日本語は残す。一括翻訳や二言語版の常時同期は別作業とする。

棚卸しでは特に次を確認する。

- `docs/design.md` の Stage 0 中心の実装案内を、原文保存部分とは分けて更新する。
- `stdlib/README.md` の import に関する説明を、明示的な `--lib` と package mode の違いに合わせる。
- 仕様書の「後続」「未実装」とロードマップの時制を、完了時点の実装に合わせる。
- protocol 2 / 3、`--lib` / `--manifest-path`、所有モジュールと呼出権限の説明を横断確認する。
- Rust acceptance と Lean semantic acceptance、通常コンパイラと proof oracle の依存境界を維持する。

## 3. mdBook の構成

リポジトリルートに `book.toml`、`docs/` に `SUMMARY.md` を追加し、既存 Markdown を
直接 book の入力にする。別の book 用本文コピーは作らず、目次の並べ方で読者別に整理する。
既存仕様書の一括移動・改名は避け、移動が必要な箇所は移動表、旧リンクの扱い、参照元修正を同じ変更に含める。

予定する目次は次のとおり。新規ページは各段階で内容を用意してから目次へ登録する。

```text
入口・実装状況                    docs/README.md
利用ガイド                        docs/guide/{getting-started,cli,stdlib}.md
言語仕様                          docs/{stage0,stage1a,stage1b,packages}.md
                                  + Stage 1 完了までに追加された仕様書
実装と検証                        docs/development/{architecture,validation}.md
                                  docs/{protocol,verification}.md
設計草稿 v0.3                     docs/design.md と docs/design/ 内の全8文書
開発計画と文書保守                docs/{stage1-roadmap,docs-cleanup-plan}.md
                                  docs/development/documentation.md
```

設定の初期案は以下。これは導入時に検証する設定例であり、現在のビルド手順ではない。
[設定仕様](https://rust-lang.github.io/mdBook/format/configuration/general.html) と
[目次形式](https://rust-lang.github.io/mdBook/format/summary.html) に従う。

```toml
[book]
title = "Vastitas"
language = "en"
src = "docs"

[build]
build-dir = "target/book"
create-missing = false

[output.html]
mathjax-support = true

[output.html.playground]
runnable = false
```

生成物は既存の ignore 対象である `target/` に置き、コミットしない。
`create-missing = false` で目次の誤記による空ページ生成を防ぐ。
mdBook はドキュメント用の開発ツールとして固定バージョンを導入し、コンパイラの Cargo / Lake
依存には追加しない。導入時に互換性を確認した版を選び、ローカルと CI で共通のバージョン指定を使う。
インストールは `cargo install mdbook --version '=選定した版' --locked` を基本とする。
[公式 CI ガイド](https://rust-lang.github.io/mdBook/continuous-integration.html) を参照し、
使用する Actions も既存 CI と同様にコミット SHA で固定する。

### 数式・コード・リンクの互換性

- v0.3 は `$...$` / `$$...$$` を含むため、`mathjax-support = true` だけで表示できるとは見なさない。
  [公式の MathJax 説明](https://rust-lang.github.io/mdBook/format/mathjax.html) にも区切り記号の制約がある。
  導入する版で数式、複数行の式、表中の式を試し、必要なら描画時だけ変換する最小限の仕組みを追加する。
  保存本文の数式やエスケープを直接書き換えて解決しない。
- 原文の `draft-v0.3:*` 区間、節番号、仮定、注意事項、参考文献と
  [source-record.json](design/source-record.json) を維持する。
  原目次リンクの置換を逆変換して、各節と再構成した全体のバイト数・SHA-256 を検査する。
  不一致に合わせて記録済みハッシュを更新してはならない。
- 実行できる例には `vast`、シェルには `sh`、設計疑似コードにはその旨を明記する。
  Vastitas 用の強調表示は後続改善とし、Rust として実行する UI は付けない。
- `README.md`、`AGENTS.md`、`examples/`、ソースコードなど `docs/` 外へのリンクは、
  HTML で存在しない相対パスにならないよう整理する。book 内の説明へ参照先を移すか、
  対応するリポジトリ上のファイルへリンクする。保存本文に調整が必要なら描画側で処理する。
- GitHub 上の Markdown と生成 HTML の両方で、相互参照、見出しアンカー、画像、
  `source-record.json` などの添付資料が開けることを確認する。

## 4. 実施順序と成果物

| 段階 | 作業 | 完了条件 |
| --- | --- | --- |
| 1. 棚卸し | Stage 1 完了の基準を固定し、全ページ・重複・古い記述・参照元を一覧化する | 各文書の正本、移動先、保存対象、修正根拠が決まっている |
| 2. 内容整理 | 実装状況表、利用ガイド、開発手順を整え、仕様・証明範囲・README の説明を同期する | 現行仕様と歴史的提案を区別でき、例と根拠をたどれる |
| 3. mdBook 導入 | 固定版、`book.toml`、`SUMMARY.md`、必要最小限の描画対応を追加する | ローカルで build / serve が動き、数式・コード・全章の表示を確認できる |
| 4. CI と保守 | docs build、リンク・原文保存チェック、検証手順、HTML artifact を追加する | PR から出力を確認でき、壊れた章・リンク・保存本文の改変を検出する |
| 5. 公開 | ローカルと CI の完成後、公開先・対象ブランチ・URL を確定して配信を設定する | 公開 URL と更新手順が記録され、サブパスを含む実サイトの導線を確認できる |

各段階をレビュー可能な変更として進める。mdBook 導入とサイト公開は別の成果物とし、
公開先が未確定でも段階 1–4 を完成できるようにする。
公開先の第一候補は GitHub Pages。採用時はプロジェクトの URL に合わせて `site-url` を設定し、
PR は検証・artifact 作成まで、公開は選定したブランチまたはタグの検証成功後に限定する。
公開用の権限は配信ジョブに限定する。現在の計画追加では配信設定を変更しない。

## 5. 検証と保守

docs 用 CI はコンパイラ／oracle のジョブから独立させる。Markdown と設定・描画用資材だけで
book を生成できる構成にし、通常コンパイラの no-mathlib CI を維持する。

| 確認対象 | 導入時に行う検証 |
| --- | --- |
| 章構成と生成 | 固定版の `mdbook build`、目次に載る全ファイルの存在、意図しない空章・未掲載ページの確認 |
| リンク | Markdown のローカル参照と生成 HTML のファイル・アンカーを検査。外部リンクの疎通はネットワーク依存の検査として分ける |
| 原文保存 | `source-record.json` に基づく全節と全文の再構成検証。描画処理が入力ファイルを変更しないことも確認 |
| 表示 | `mdbook serve` で目次、検索、日本語、数式、表、コード、狭い画面、公開サブパスでの導線を確認 |
| 実装例 | kernel を先にビルドし、実行例に `vastitas check` と `vastitas build` を実行、生成物の出力を照合 |
| 拒否例と互換性 | 対応する既存テストで拒否理由、protocol 2 / 3、`--lib` / package mode を確認。追加の例には意味のある回帰ケースを追加 |
| 証明の説明 | 実装定義・定理名・仮定・CI の証拠と照合。証明や kernel に変更が必要なら、その変更に対応する既定の全検証を行う |

[`mdbook test`](https://rust-lang.github.io/mdBook/cli/test.html) は Rust のコード例向けであり、
`.vast` の検証の代わりにはしない。実行例の正本は可能な限り `examples/` や既存の回帰ケースに置き、
docs 側の例と対応を記録する。歴史的設計の疑似コードを現行コンパイラの成功例に含めない。

`docs/development/documentation.md` には固定版の導入、`mdbook build` / `mdbook serve`、
章の追加、リンク検査、実行例の更新、原文保存検査、公開手順を記載する。
CLI・仕様・protocol・証明範囲が変わる PR では、対応する正本と実装状況表も更新する。

## 6. 完了チェックリスト

- [ ] Stage 1 の完了基準・コミット・証拠・残る制限を記録した。
- [ ] 利用ガイド、現行仕様、実装・証明境界、歴史的設計を別々にたどれる。
- [ ] 重複する説明の正本を決め、README と既存入口から詳細へ到達できる。
- [ ] v0.3 の全18節と序文を保持し、保存ハッシュが一致する。
- [ ] 固定した mdBook でローカルと CI のビルドが通り、内部リンクと添付資料が開ける。
- [ ] 数式・表・コード・目次・検索を表示確認し、問題や検索の制限を記録した。
- [ ] 実装例の check / build / 実行結果と拒否例を確認し、実行コマンドと結果を記録した。
- [ ] 通常コンパイラと生成実行ファイルに mdBook・mathlib の依存を追加していない。
- [ ] 文書更新手順と CI artifact の確認方法を記載した。
- [ ] 公開を実施した場合は、URL・配信条件・実サイトの確認結果を記録した。
