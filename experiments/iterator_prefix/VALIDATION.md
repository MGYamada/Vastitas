# 実行・検証状況

記録日: 2026-10-29 JST。照合した基点:
`b3f8ff79a364858f6500d5905ab284dd77679784`。
実行環境の Python は `3.12.14`。以下はこの限定実験の結果である。

## 実行したもの

| コマンド | 観測した結果 |
| --- | --- |
| `python3 -m unittest discover -s experiments/iterator_prefix -p 'test_*.py' -v` | 18テスト成功。うち1テストで有限列 oracle と1,200構成を比較し、別の1テストで36個の打切り位置を検査 |
| `python3 experiments/iterator_prefix/demo.py` | 3例を実行。take(0) は上流0回で Done、false filter の take(1) は32 Skip・出力0・残要求1の BudgetExhausted、平方列は `[0, 1, 4]` 後に Done |
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

## 未検証・対象外

| 対象 | 状態 |
| --- | --- |
| `FinitePrefixDraft.lean` の構文・型・証明候補 | 未検証。`lean --version` は exit 127 (`lean: command not found`)。Lean 4.35.0 での elaboration と transitive axiom audit は未実行 |
| Python と Lean の simulation / refinement | 未証明 |
| 実際の Vastitas public checker の iterator 受理 | 未実装・未試験 |
| 実返却 Core と独立 store / allocation / borrow の意味論 | 未接続・未証明 |
| Rust / kernel / proof oracle のビルド・回帰 suite | 今回は未実行。これらの本体は変更していない |
| ネイティブ実行・FFI・OOM・例外時 cleanup・並行実行 | 対象外、未検証 |
| #191 全体のメモリ安全性定理 | 未証明、この実験では完了しない |

将来、ピン留めされたツールチェーンのある環境で草案を点検する入口は
`lean experiments/iterator_prefix/FinitePrefixDraft.lean`。
これは今回成功したコマンドの一覧には含まれない。
草案が elaboration に成功しても、実際の checker・Core・ストレージへの
接続義務が自動的に解決することはない。

歴史的 Stage 1 の完了条件、既存の checker taxonomy、production の build / CI
条件は変更していない。Hosted CI の成功もこの記録からは主張しない。
