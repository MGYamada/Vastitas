# 実行・検証状況

記録日: 2026-10-29 JST。照合した基点:
`b3f8ff79a364858f6500d5905ab284dd77679784`。
初回実行の Python は `3.12.14`。PR #193 の再検証では Python `3.15.2`、
ピン留めされた Lean `4.35.0`（`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`）を使用した。
以下はこの限定実験の結果である。

## 実行したもの

| コマンド | 観測した結果 |
| --- | --- |
| `python3 -m unittest discover -s experiments/iterator_prefix -p 'test_*.py' -v` | 18テスト成功。うち1テストで有限列 oracle と1,200構成を比較し、別の1テストで36個の打切り位置を検査 |
| `python3 experiments/iterator_prefix/demo.py` | 3例を実行。take(0) は上流0回で Done、false filter の take(1) は32 Skip・出力0・残要求1の BudgetExhausted、平方列は `[0, 1, 4]` 後に Done |
| `bash experiments/iterator_prefix/check_lean.sh` | Lean 4.35.0 で全補題を elaboration。382モデル宣言の推移的公理監査成功。許可公理は `propext` / `Classical.choice` / `Quot.sound` のみ |
| `python3 scripts/check_boundaries.py` | `compiler/oracle dependency boundaries verified` |
| `git diff --cached --check` | 今回追加したファイルの whitespace 検査成功 |

所有権の検査は Yield / Skip / Done / 明示的 dispose と、消費後のさらに長い
prefix を対象にする。旧状態・同じフィールドの複製・foreign handle の拒否、
拒否時の台帳不変、走査間の資源 ID 分離、各 frame の破棄回数を検査した。
上限到達時の継続と明示的打切りは別々に検査した。

1,200構成は3種類の有限元列それぞれに、7種類の map / filter / take 変換を
0〜3段合成した `3 × (1 + 7 + 49 + 343)` ケース。期待値は有限 Python list に
よる独立の eager oracle から作り、モデルの cursor / pulse 関数を使用しない。
有限の試験範囲を超える全称的な正しさの証明ではない。

初版の Lean 草案には予約語 `initialize`、複数行 record 更新、`List.range` の
一意性補題の未指定によるエラーがあった。再検証で修正し、上記の独立した
検査スクリプトを追加した。Python のモデル・テスト・観測結果は変更していない。

## 未検証・対象外

| 対象 | 状態 |
| --- | --- |
| Python と Lean の simulation / refinement | 未証明 |
| 実際の Vastitas public checker の iterator 受理 | 未実装・未試験 |
| 実返却 Core と独立 store / allocation / borrow の意味論 | 未接続・未証明 |
| Rust / kernel / proof oracle のビルド・回帰 suite | 今回は未実行。これらの本体は変更していない |
| ネイティブ実行・FFI・OOM・例外時 cleanup・並行実行 | 対象外、未検証 |
| #191 全体のメモリ安全性定理 | 未証明、この実験では完了しない |

`check_lean.sh` は一時ディレクトリにモデルの `.olean` を作り、その実体を
`Audit.lean` から読み込む。通常ビルドや既存 oracle への import は追加しない。
独立モデルが elaboration・公理監査に成功しても、実際の checker・Core・
ストレージへの接続義務が自動的に解決することはない。

歴史的 Stage 1 の完了条件、既存の checker taxonomy、production の build / CI
条件は変更していない。Hosted CI の成功もこの記録からは主張しない。
