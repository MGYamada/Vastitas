# Vastitas 言語設計

**現行の規範的な stdlib 境界:** [ADR 0001 — Mathematics-first standard-library admission and trust boundary](adr/0001-mathematics-first-stdlib.md)。本頁以下の v0.3 設計草稿は歴史的提案として保存し、規範と実装状況は区別する。実装の追跡は [#160](https://github.com/MGYamada/Vastitas/issues/160) を参照。

**最上位の性能・アーキテクチャ目標は Fast like C。** 現行の
[改訂7章 — ストレージ・所有権・残差保持](storage-ownership.md) は、レイアウト、
エイリアシング、資源遷移、確保とコピーの費用、C比較による受入条件を定める。
旧7章の保存本文を置換せず、今後の実装判断には改訂版を使う。設計の採用は、実装・証明・性能達成の記録とは別である。

Vastitasは、数学的対象を第一級の値として扱い、数学的意味・実行表現・物理的な証拠を区別する言語を目指す。通常の`Scheme`と滑らかな`CInfScheme`を並行した幾何設定とし、明示的な基底、対象の同一性、射の始終域を保持する。

この索引は、2026年10月26日の設計草稿v0.3をテーマ別に整理したものである。原文の全18節、数式、仮定、注意事項、受入例、参考文献を各文書に保持した。節番号は原文と同じであり、文書中の「Section 8.3」などもその番号を指す。変更したのは、分割に伴う元の目次のリンク先と、索引・案内の追加である。

## 読み方

| テーマ | 原文の節 | 内容 |
| --- | --- | --- |
| [目的と設計の成熟度](design/vision-status.md) | 序文・1 | Math 2.0／Physics 2.0、確定した方向性・提案・未決定事項の区別 |
| [幾何設定・対象・族・層](design/geometry.md) | 2–5 | 通常／滑らかなスキーム、一般化点、存在パッケージ、基底変換、Grassmannianと線値Plückerデータ |
| [テンソル・次元・資源](design/tensor-resources-units.md) | 6–7 | 共通の`⊗`、モノイダル構造、単位と次元、ストレージと線形ポートの所有権 |
| [純粋関数と静的ディスパッチ](design/functions-dispatch.md) | 8 | 暗黙キャプチャの禁止、関数全体の編集権限、宣言的差分、有限検査核、許可された影響範囲 |
| [逆微分とスペクトル幾何](design/differentiation-spectral.md) | 9–11 | 基点付き余接空間、計量付き`grad`、固有値の重複と作用、Hermitian cluster、接続写像を保持するSVD |
| [物理モデル・コンパイラ・検証](design/physics-compiler-verification.md) | 12–13 | 意味と表現の分離、数値的実現、物理モデルの仮定、IR、信頼境界、証拠の依存関係と失効 |
| [実装段階・受入条件・未決定事項](design/roadmap-acceptance.md) | 14–16 | 段階別の完成条件、正常系と拒否例、今後の研究・実装上の問い |
| [設計の来歴と参考文献](design/history-references.md) | 17–18 | v0.1からv0.3への決定事項、先行草稿、数学・言語研究の出典 |

## 実装との関係

草稿中のコードは疑似コードであり、すべてが実装済みという意味ではない。幾何の構成に関する数学的議論、条件付きのディスパッチ補題、数値的性質、形式証明の完了状況も区別する。実装済みの文法・ビルド手順・検証結果は[README](../README.md)と個別の開発文書を参照する。RustとLeanの通信形式は[コンパイラプロトコル](protocol.md)で定める。

現在の公開実装はStage 1b、path package、有限abstract selector/contract、編集assemblyとprotocol 6の再借用・権限移転を含む。宣言ベースのindexed Core、関数・dispatch・権限の内部checkerも接続されているが、公開protocol 7、ストレージ所有権、線形代数と有限ネットワークの完成は[Stage 1完了台帳](stage1-completion.md)で追跡する。Rustフロントエンドを`src/`、mathlibを含まないLeanバックエンドを`lean-kernel/`、その実定義をimportして証明するmathlib付きオラクルを`lean/`に分離する。通常のコンパイルは証明オラクルを呼び出さない。

Stage 0の幾何構文は互換機能として残るため、その仕様書を古いという理由だけでobsoleteにはしない。一般の多項式射、AD、数値ソルバ、物理モデルと証拠管理は後続であり、この索引や草稿の存在をもって実装・証明済みとは扱わない。文書の分類と移行手順は[mdBook移行計画](docs-cleanup-plan.md)を参照する。

## 原文の保存確認

原文の序文と全18節を分割先から再構成し、目次リンクの移動だけを戻した結果が元のUTF-8バイト列と完全一致することを確認した。元文書名、全体と各節のSHA-256、移動先、リンク置換記録は[source-record.json](design/source-record.json)に記録している。原文の数学的内容を要約で置き換えてはいない。
