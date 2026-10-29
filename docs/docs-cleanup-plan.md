# Stage 1 完了後の docs cleanup と mdBook 導入計画

状態: 計画。Stage 1 完了後に実施する。現時点では docs の再編、mdBook の導入、サイト公開は未実施。

作成日: 2026-10-27（JST）、更新日: 2026-10-29（JST）。今回の棚卸し基準は
PR #215のマージ `5e98abc` と本改訂の文書群である。実装状況の正本は
[README](../README.md)、[Stage 1完了台帳](stage1-completion.md)、テストと検証記録とする。
移行開始時にもう一度棚卸しし、完了時点のコミットを固定する。
本書は整理作業の計画であり、Stage 1 の実装完了や形式検証の範囲を拡張するものではない。

## 1. 開始条件と整理の目的

現在の公開実装は Stage 1b、path package / call-only module import、有限abstract
selector/contract、編集assemblyとprotocol 6の再借用・権限移転を含むが、
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

**Fast like Cを最上位の性能・アーキテクチャ目標とする。**
[改訂7章](storage-ownership.md)のレイアウト・エイリアシング・残差保持・費用契約と
C比較の受入条件を、実装済みという誤解なくbookに掲載する。文書の章立てでも
所有権・ストレージをdispatchと同じ深さで読めるようにする。
現在行うのは棚卸し・計画・必要な設計改訂であり、mdBookのインストール、
設定追加、本文の一括移動、サイト公開はStage 1完了記録後に行う。

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
| `docs/stage1-completion.md`、`stage1-roadmap.md`、`stage1-delivery.md`、本書 | 完了台帳・開発計画・履歴 | 現行台帳と過去のsnapshotを分け、現在の仕様は個別仕様書へ案内する |
| `docs/design.md`、`docs/design/` | 歴史的設計と研究上の背景 | v0.3 保存本文を維持し、現行仕様との違いは索引や別文書に書く |
| `docs/storage-ownership.md`、`docs/adr/` | 採用した設計・方針 | 仕様として採用した契約と実装・証明・性能測定の状態を別に表示する |
| `stdlib/README.md`、`AGENTS.md` | 各ディレクトリの入口／貢献規約 | 標準ライブラリの詳細は book 内の正本へ集約し、入口を残す。貢献規約はコピーせず参照する |

実装状況表は「機能／仕様書／実装と回帰テスト／証明と仮定／制限・後続課題」を列にする。
実装済み、試験済み、証明済み、仮定、提案、延期を同一の状態として扱わない。
README の短い状況説明はこの表と同期し、証明の説明は `verification.md` を参照する。
現行仕様は既存の英語を基本に、案内・計画の日本語は残す。一括翻訳や二言語版の常時同期は別作業とする。

棚卸しでは特に次を確認する。

- `docs/design.md` の Stage 0 中心の実装案内を、原文保存部分とは分けて更新する。
- `stdlib/README.md` の import に関する説明を、明示的な `--lib` と package mode の違いに合わせる。
- 仕様書の「後続」「未実装」とロードマップの時制を、完了時点の実装に合わせる。
- 完了時点で公開されている全protocol、`--lib` / `--manifest-path`、所有モジュールと呼出権限の説明を横断確認する。現在の公開2–6と予定7–8を混同しない。
- Rust acceptance と Lean semantic acceptance、通常コンパイラと proof oracle の依存境界を維持する。

### 2.1 現在の全資料の配置先

ファイル名の古さでobsoleteと判定しない。現在サポートしている互換機能の仕様、
過去の検証証拠、未実装の採用設計は、それぞれ異なる扱いにする。
以下は本改訂時点の`docs/`全Markdownと添付データの棚卸しである。

| 現在のパス（`docs/`からの相対） | 分類・bookでの配置 | 移行時の処置 |
| --- | --- | --- |
| `stage0.md` | 現行の互換言語仕様 | 旧幾何構文・`--lib`のサポート範囲を明示。丸ごとobsoleteにはしない |
| `stage1a.md`、`stage1b.md` | 現行言語仕様 | dispatchと独立関数の正本。新仕様との参照を更新 |
| `packages.md`、`abstract-types.md`、`promotion.md` | 現行言語・stdlib仕様 | パッケージ、abstract selector、値のpromotion方針を維持 |
| `edit-borrowing.md`、`edit-authority.md` | 現行編集権限仕様 | protocol 5と6、定義IDと編集権限、貸出と移転を区別 |
| `indexed-declarations.md`、`indexed-source.md` | 公開indexed構文・内部実装仕様・移行状況 | 公開7と内部checker、互換adapterと未移行stdlibを区別。未完了証明を残す |
| `storage-ownership.md` | 採用設計・改訂7章 | レイアウト、alias、残差保持、費用、性能受入条件の正本。実装証拠は台帳へ接続 |
| `protocol.md`、`verification.md` | 公開境界・検証の正本 | 対応version、実checker、定理、仮定と未証明事項を照合 |
| `adr/0001-mathematics-first-stdlib.md` | 採用方針・ADR | マージ済み方針のstatusを確認し、後続ADRと実装状態を区別 |
| `graph-crossings.md` | 内部実装・後続機能 | 有限crossing checkerの範囲を表示。Stage 1ネットワーク完成と同一視しない |
| `graph-proof-obligations.md` | 未解決設計・証明義務 | 後続の研究・計画節に置く。証明済みの章へ移さない |
| `stage1-completion.md` | 現行完了台帳 | 完了コミット、受入条件、性能測定、制限の入口 |
| `stage1-roadmap.md` | 過去の工程・到達記録 | 履歴節へ。古い「next」等は当時の記述と表示し、現行台帳へ誘導 |
| `stage1-delivery.md` | protocol 5時点の履歴 | 当時のIssue snapshotとして保持。現在の未解決一覧として扱わない |
| `stage1b-indexing.md` | 実装・性能調査の証拠 | 測定commitと条件を保持。現在の実行性能比較とは分ける |
| `benchmarks/stage1b-{original,main}-comparison.csv` | 測定添付データ2件 | 元データのまま配布し、調査文書からリンク |
| `docs-cleanup-plan.md` | 移行・保守計画 | 各段階の実施commitと未完了項目を追記 |
| `design.md` | 現行の設計索引 | 採用設計と保存草稿への入口。古い実装案内は原文外で修正 |
| `design/vision-status.md`、`geometry.md`、`tensor-resources-units.md`、`functions-dispatch.md` | 保存草稿v0.3（序文・1–8章） | 原文区間は不変。現行仕様への案内は区間外に追加 |
| `design/differentiation-spectral.md`、`physics-compiler-verification.md`、`roadmap-acceptance.md`、`history-references.md` | 保存草稿v0.3（9–18章） | 同上。採用設計、将来提案、obsolete部分を章単位で説明 |
| `design/source-record.json` | 原文保存の証拠 | 移動先・逆置換・バイト数・ハッシュを保持して再構成検査に使う |

ルートREADME、`stdlib/README.md`、`AGENTS.md`、実例、検証scriptはbook外の
参照元として別途追跡する。開始時の差分で増えた仕様・ADR・添付データにも行を追加する。

### 2.2 obsolete文書と検索の扱い

各ページに「現行仕様」「採用設計／実装待ち」「内部実装」「履歴」「保存草稿」
の状態、基準commitまたは日付、後継の正本を示す。完全に置換済みの内容だけを
obsoleteとし、後継リンクと置換理由を付ける。古いテスト結果を削除して現行の
結果に書き換えることや、将来提案をobsoleteという理由で消すことはしない。

たとえば旧7章は改訂7章へ、旧8.3の公開実装に対応する部分は`stage1a.md`、
`edit-borrowing.md`、`edit-authority.md`へ案内する。原草稿全体を現行仕様とみなさない。
bookの通常導線では現行文書を先に置き、履歴・保存草稿は独立した付録にまとめる。
検索結果にも状態が分かるタイトル／案内を表示する。固定版で章単位の検索除外が
可能か検証し、できなければ表示ラベルで区別する。未確認の設定を前提にしない。

旧Markdownパスと見出しアンカーは原則維持する。移動が不可欠な場合は
旧パス・旧アンカー・後継パス・後継アンカー・参照元を対応表に記録し、旧ページに
案内を残す。HTMLのredirectだけではGitHub上のMarkdownリンクを救えないため、
両方を検査する。意味が違う新章へ黙って同じアンカーを向けない。

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
ストレージと性能                  docs/storage-ownership.md と測定記録
実装と検証                        docs/development/{architecture,validation}.md
                                  docs/{protocol,verification}.md
設計方針・未解決設計              docs/adr/ と後続機能の設計文書
現在の完了台帳                    docs/stage1-completion.md
履歴・保存草稿                    docs/design.md と docs/design/ 内の全8文書
                                  docs/{stage1-roadmap,stage1-delivery,stage1b-indexing}.md
移行計画と文書保守                docs/docs-cleanup-plan.md
                                  docs/development/documentation.md
```

設定の初期案は以下。これは導入時に検証する設定例であり、現在のビルド手順ではない。
[設定仕様](https://rust-lang.github.io/mdBook/format/configuration/general.html) と
[目次形式](https://rust-lang.github.io/mdBook/format/summary.html) に従う。

```toml
[book]
title = "Vastitas Programming Language"
authors = ["Vastitas Project Contributors"]
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

book のタイトルは `Vastitas Programming Language`、著者名は
`Vastitas Project Contributors` に統一する。book の入口に
`Copyright 2026 Vastitas Project Contributors` と Apache License, Version 2.0 の
案内を表示し、リポジトリの `README.md` と `LICENSE` に表記を合わせる。

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
| 1. 棚卸し | Stage 1 完了の基準を固定し、本書の一覧を全ページ・重複・古い記述・参照元に照合する | 未分類ファイルがなく、各文書の正本、状態、移動先、保存対象、修正根拠が決まっている |
| 2. 内容整理 | 実装状況表、利用ガイド、開発手順を整え、仕様・証明範囲・README の説明を同期する | 現行仕様と歴史的提案を区別でき、例と根拠をたどれる |
| 3. mdBook 導入 | 固定版、`book.toml`、`SUMMARY.md`、必要最小限の描画対応を追加する | ローカルで build / serve が動き、数式・コード・全章の表示を確認できる |
| 4. CI と保守 | docs build、リンク・原文保存チェック、検証手順、HTML artifact を追加する | PR から出力を確認でき、壊れた章・リンク・保存本文の改変を検出する |
| 5. 公開 | ローカルと CI の完成後、公開先・対象ブランチ・URL を確定して配信を設定する | 公開 URL と更新手順が記録され、サブパスを含む実サイトの導線を確認できる |

実装PRは段階1–2の内容整理、段階3のbook構成、段階4の検査と保守、
段階5の公開を分ける。各PRに対象文書一覧と表示／リンク検査結果を残す。
導入で問題が出ても既存Markdownを読める状態を維持し、HTML生成物にしか
情報がない構成を作らない。Stage 1実装PRへmdBook依存を混在させない。

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
| 拒否例と互換性 | 対応する既存テストで拒否理由、完了時点の公開全protocol、`--lib` / package mode を確認。追加の例には意味のある回帰ケースを追加 |
| 状態・性能説明 | obsoleteの後継リンク、改訂7章の実装状態、C比較の条件・元データ・未達事項を確認。コンパイル時間の測定を生成物の実行速度と取り違えない |
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
- [ ] 全資料に分類と正本があり、obsoleteページには後継と置換理由がある。互換仕様と履歴証拠を誤って廃止していない。
- [ ] 改訂7章の費用・性能契約を掲載し、Fast like Cの測定済み範囲と未達を実装状態からたどれる。
- [ ] 重複する説明の正本を決め、README と既存入口から詳細へ到達できる。
- [ ] v0.3 の全18節と序文を保持し、保存ハッシュが一致する。
- [ ] 固定した mdBook でローカルと CI のビルドが通り、内部リンクと添付資料が開ける。
- [ ] 旧Markdownパス・見出しとHTMLの参照を確認し、移動箇所には対応表と互換導線がある。
- [ ] 数式・表・コード・目次・検索を表示確認し、問題や検索の制限を記録した。
- [ ] 実装例の check / build / 実行結果と拒否例を確認し、実行コマンドと結果を記録した。
- [ ] 通常コンパイラと生成実行ファイルに mdBook・mathlib の依存を追加していない。
- [ ] 文書更新手順と CI artifact の確認方法を記載した。
- [ ] 公開を実施した場合は、URL・配信条件・実サイトの確認結果を記録した。
