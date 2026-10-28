# 有限ステップ iterator 参照実験（#190 / #191）

**Python の限定参照モデルと回帰テスト、および Lean で検査した独立抽象モデル。**
Lean 4.35.0 で有限 prefix の補題と公理監査を通したが、Vastitas の実装・実行や
実メモリ安全性の検証ではない。Python との対応も未証明である。
この実験は #191 全体の完了条件を満たさず、歴史的 Stage 1 の追加完了条件にも
新しい checker にもならない。

照合基点は `b3f8ff79a364858f6500d5905ab284dd77679784`。
[Core.Term](https://github.com/MGYamada/Vastitas/blob/b3f8ff79a364858f6500d5905ab284dd77679784/lean-kernel/VastitasKernel/Core.lean)
に loop / iterator 項はない。
[ProgramSafety.module_total_and_typed](https://github.com/MGYamada/Vastitas/blob/b3f8ff79a364858f6500d5905ab284dd77679784/lean/VastitasOracle/ProgramSafety.lean)
は `ModuleWellTyped` と検査済みの `Dependency.ModuleOrdered` から現在の Core の
停止・型保存を導く。新しい発散可能な実行への適用はできない。
[有限 protocol-5 受理定理](https://github.com/MGYamada/Vastitas/blob/b3f8ff79a364858f6500d5905ab284dd77679784/lean/VastitasOracle/EditAcceptance.lean)
も実在するが、ストレージ所有権や iterator の安全性はその結論に含まれない。

## 再実行

Python 3.10 以降、標準ライブラリのみ。リポジトリのルートから実行する。

```sh
python3 -m unittest discover -s experiments/iterator_prefix -p 'test_*.py' -v
python3 experiments/iterator_prefix/demo.py
bash experiments/iterator_prefix/check_lean.sh
```

Lean 検査はリポジトリでピン留めされた 4.35.0 を使い、mathlib を必要としない。

- [model.py](model.py): 純粋な記述、残余 cursor、使用権台帳、有限観測器。
- [test_model.py](test_model.py): 意味・所有権・破棄の回帰例。
- [demo.py](demo.py): 元の3例と破棄前後の台帳を JSON 出力。
- [FinitePrefixDraft.lean](FinitePrefixDraft.lean): 具体的な `State` / `Step` /
  `Invariant` と有限 prefix 保存の補題。Lean 4.35.0 で elaboration・公理監査済み。
- [check_lean.sh](check_lean.sh) / [Audit.lean](Audit.lean): 独立した再検査と全モデル宣言の推移的公理監査。
- [VALIDATION.md](VALIDATION.md): 今回実行した試験と実行していない検証。

通常の compiler / oracle ビルドにこの実験を import しない。CI や Stage 1 の
ゲートも変更しない。回帰コマンドは上記の独立した実験用コマンドである。

## 対象と1ステップの意味

値は Nat、演算子は `CountFrom`・`Map`・`Filter`・`Take` のみ。
`MapOp` は identity / square / add、`Predicate` は false / true / even /
at-least の閉じたタグで、必要な environment は明示的な Nat 値とする。
任意の Python 関数・捕捉・iterator handle は記述として受理しない。
これは実験内の入力制約であり、Vastitas checker の受理ではない。

`CountFrom`, `Map`, `Filter`, `Take` は immutable な再利用可能な **記述**。
`Machine.start(plan)` ごとに新しい残余 cursor・走査 ID・資源 ID・使用権を作る。
記述の共有や再走査で使用権を共有しない。Python では
`Take(source, limit)` の順で呼ぶ。これは提案中の Vastitas 構文ではない。

1回の `step(handle)` は有限の cursor 木をたどる1回の **pulse** であり、
各 wrapper は上流を最大1回だけ進める。`filter` 内で次の出力まで探索する
ループは置かない。有限の記述に対する構造的な処理でも、整数演算や再帰の
実時間・メモリを定数で抑えるという主張にはならない。

| 結果 | 状態の変化 | `Take` の残要求数 |
| --- | --- | --- |
| `Yield(value, next)` | 旧使用権を消費し、新使用権を発行 | 上流の Yield に対してのみ1減る |
| `Skip(next)` | 出力なしでも旧使用権を消費し、新使用権を発行 | 変わらない |
| `Done` | 旧使用権を消費、全 frame を一度ずつ破棄、継続なし | 0 または上流が終了 |
| `dispose(handle)` | 途中打切りとして消費・破棄、継続なし | 関係なし |

`Take(0, source)` の pulse は上流の pulse より先に終了する。
`start` は有限の cursor 木を作るので、「上流を進めない」は「frame の初期化も
しない」という意味ではない。最後の Yield の直後は残要求数0の状態を保持する。
その状態は次の pulse で Done になるか、呼出側が明示的に dispose する。

所有権は **cursor 木全体に対する1つの affine lease** として近似する。
内部 cursor は純粋な値であり、個々の子 cursor に独立した公開使用権はない。
資源は各演算子 frame に1個の模擬 ID を割り当て、全体の Done / dispose まで
保持する。未訪問の上流を含む全 frame の破棄回数を実際に加算する。
カウンタを単に1へ上書きして二重破棄を隠すことはしない。
これは heap free・要素の destructor・borrow の意味論ではない。

`step` / `dispose` は、同じ走査の現在の **発行済み handle オブジェクト**だけを
受け付ける。旧 handle、別走査・別 Machine の handle、同じフィールドで作った
コピーを拒否する。失敗した呼出しは台帳を変更しない。信頼された逐次 Python
呼出しを前提とし、reflection・private field 改変・並行実行への防御ではない。

## 観測予算と破棄

`observe(handle, budget)` の予算は **Yield・Skip・Done の各 pulse**を数える。
`BudgetExhausted` は観測器の返却理由であり、iterator の Done イベントではない。
予算0では何も進めず、同じ使用権を返す。予算到達時に自動で終了・破棄せず、
返された唯一の使用権で再開または dispose する。`demo.py` は観測後に明示的に
dispose し、その前後を別々に記録する。

| 観測例 | pulse | 出力 | 観測結果 |
| --- | --- | --- | --- |
| `take(0, filter(false, countfrom(0)))` | Done 1回、上流0回 | `[]` | 終了、各 frame の破棄1回 |
| `take(1, filter(false, countfrom(0)))` | Skip 32回 | `[]` | 予算到達、要求数1、継続は生存 |
| `take(3, map(square, countfrom(0)))` | Yield 3回 + Done 1回 | `[0, 1, 4]` | 終了、各 frame の破棄1回 |

32回の観測だけでは発散の証明にも終端の証明にもならない。
この特定の false filter の継続は模式規則からも記述できるが、一般の filter の
生産性は得られない。純粋で再走査可能な記述と productive な `InfiniteList` は
同義ではない。任意の filter を Infinite と認定する規則は設けない。

記述を捨てても走査は破棄されない。走査の呼出側が所有権を返却する責任を持つ。
生存中の有限 prefix を認めるので、一般の leak freedom は主張しない。
記録した trace・出力・監査履歴もメモリを消費する。メモリ有界性、OOM の安全性、
host 例外・割込み時の unwinding はこの実験の対象外である。

## Lean 抽象モデルとの対応

`Plan` と `Cursor` を別の帰納型として定義し、`pulse` を有限 cursor への
構造的再帰で具体化した。`State` は走査 ID、世代、optional cursor、frame ID 列、
release event 列、dispose 回数を保持する。

`Invariant` は frame ID の一意性に加え、生存時は release なし・dispose 0回・
cursor と同数の frame、終了時は全 frame と一致する release 列・dispose 1回を
要求する。`Step` の規則はこの Invariant を前提にせず、実際の pulse 結果と現在の
ticket から `advance` / `finish` を決める。したがって保存を定義に埋め込んではいない。

モデルの `pulse_keeps_size` → `step_preserves` → `finite_prefix_preserves` は、
初期不変条件から**任意の有限 prefix の終状態と全中間状態**の不変条件を導く形。
`consumed_never_owned` は、Skip を含む消費後にさらに有限 prefix を進めても旧
ticket が復活しないことを述べる。`closed_cannot_step` と
`closed_released_exactly_once` が終了後の再実行・再破棄を扱う。

これらは **独立抽象モデルの検査済み補題**であり、実際の Vastitas checker や
ストレージに対する定理ではない。Python との対応もまだ証明していない。
Lean は単一走査の ticket を
`(run, generation)` で表し、Python の object identity 検査を抽象化している。
Python の frame 別 drop counter は Lean の重複を許す release event 列に対応する。
複数走査の ID 分離は Python で試験しただけで、Lean の大域合成補題は未作成。

## 実際の受理・返却 Core・ストレージへの未証明義務

以下は必要な接続の記録であり、仮定を充足した証明や新しい受理 API ではない。
`Accept(P,E,Q)` は #184/#191 の将来の模式表記で、現在の関数名ではない。

| ID | 必要な接続・証明 | この実験の境界 |
| --- | --- | --- |
| O1 | ピン留めした Lean でモデルを elaboration し、有限 prefix 補題と依存 axiom を監査する。Python の Plan / cursor / 各台帳更新が Lean の Step を模倣することを示す | 前半は Lean 4.35.0・382宣言の監査を通過。Python simulation/refinement は未証明 |
| O2 | 実際の `Core.Term`・typing・effects に有限の loop / step machine を追加し、その独立操作意味論を定義する。`take(n)` の実行時 n と有限 IR 構造を分離する | Core に追加していない。閉じた演算タグは実際の canonical callable identity の代用ではない |
| O3 | 実際の public checker の成功等式から **その返却値 C** の型・所有権・partiality policy と source-plan 対応を導く。既存 `Surface.StaticCallsValid` と実際の lowering を拡張し、生存 environment、全 body、静的 target を照合する | `safe=true`、Rust 成功、再構築した別 Core、annotation-only `CertifiedModule` では代替できない |
| O4 | #180/#183 の独立 store を定義し、allocation ID / provenance、region、owner、loan、初期化、bounds、live aliases の不変条件を実 checker から導く | frame ID と drop 回数は実 allocation・borrow・メモリ解放ではない |
| O5 | 全ての実際の store 小ステップについて不変条件保存と fault 不在を示し、有限 prefix に持ち上げる。map / predicate / cleanup 内部の小ステップも含め、OOM・部分初期化・安全な失敗を規定する | 参照モデルの pulse は抽象的に atomic。pulse 境界の保存だけでは内部の unsafe access を排除できない |
| O6 | #184 の同一 `P,E,Q,C` と同一 snapshot / assembly に、適用される Core Safety と domain obligation ledger を合成する。変換後も同じ契約を保持し stale evidence を拒否する | 既存 `checkEditProgram_finite_acceptance` の `certified.val` との同一性規律を継承する必要がある。現在の `total` は非循環な既存 fragment の結果 |
| O7 | one-shot state、resource-bearing 要素、borrowed environment、early return / branch join / destruction、動的 nominal identity の導入・escape を型と store の両側で扱う | この実験は Nat のみ。未対応資源をこのモデルから安全と認定しない |
| O8 | source → plan → **実返却 Core** → 最適化 → backend の refinement を示す。静的 target、environment、所有権台帳を保存し、raw IR / forged Core / native の拒否・実行試験を行う | Python 実行は Vastitas native 実行ではなく、Lean/C/FFI/allocator/OS の正しさも確立しない |

O4/O5 では例えば次を独立に定義して証明する必要がある。ここに現れる Store、
RealStep、SafeEvent、ValidStore は未実装の義務を示す記号であり、Lean の既存定義や
充足済みの仮定ではない。

```text
ActualAccept(P,E,Q) = Accepted(C,evidence)
  => OwnershipBorrowSafe(C,E,Q) ∧ SourceCoreCorresponds(P,E,C)

ValidStore(C,E,σ) ∧ RealStep(C,E,σ,event,σ')
  => SafeEvent(event) ∧ ValidStore(C,E,σ')

ActualAccept(P,E,Q) = Accepted(C,evidence)
  ∧ ValidInitialStore(C,E,σ0) ∧ FiniteRealPrefix(C,E,σ0,trace)
  => every intermediate store is valid ∧ every event is memory-safe
```

初期 store は任意の外部メモリを無条件で安全とするものではなく、必要な初期化・
所有権・環境の前提を満たす store に限定する。fault クラスには use-after-move/free、
double free/use、競合 alias、lifetime escape、範囲外・未初期化 access、所有権複製を
含める。不変条件だけを述べて不正アクセスイベントの排除を省略してはいけない。
停止性、生産性、メモリ有界性はこの有限 prefix 安全性とは別に扱う。

参照: [#190](https://github.com/MGYamada/Vastitas/issues/190)、
[#191](https://github.com/MGYamada/Vastitas/issues/191)、
[#180](https://github.com/MGYamada/Vastitas/issues/180)、
[#183](https://github.com/MGYamada/Vastitas/issues/183)、
[#184](https://github.com/MGYamada/Vastitas/issues/184)、
[現在の検証境界](../../docs/verification.md)。
