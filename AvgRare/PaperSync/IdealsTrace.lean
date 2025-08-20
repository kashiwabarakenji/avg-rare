import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.Order.GroupWithZero.Unbundled.Defs
import AvgRare.Basics.SetFamily
import AvgRare.Basics.Ideals
import AvgRare.SPO.FuncSetup
import AvgRare.Basics.Trace.Common   -- Trace.traceAt / Trace.Parallel / Trace.eraseMap
import LeanCopilot

/-
IdealsTrace.lean — 「functional preorder × ideals × trace」の結合層（論文 §3）

このファイルは、SPO.FuncSetup で与えた機能的前順序 S の上で
- S から ground 上の二項関係 `leOn` を作る
- その order-ideal family を `idealFamily S` として `SetFamily α` に落とす
- 論文 §3 の Lemma 3.1（maximal ⇒ rare）, 3.3（∼ ⇔ parallel）, 3.5（trace 単射）,
  3.6（trace 後も functional, NDS は増えない）の**言明**を置く

重い証明は `sorry` のまま残し、他ファイルから参照可能な API を確定させます。
-/

universe u
open Classical

open scoped BigOperators

namespace AvgRare
namespace PaperSync
open Trace
open SPO

variable {α : Type u} [DecidableEq α]

/-! ## 1) 功能的前順序 S から ground 上の関係を作る -/

/-- `leOn S y x` : ground 上の要素 `y, x : α` について，
S の部分型 `S.Elem` 上の `S.le ⟨y,hy⟩ ⟨x,hx⟩` が成り立つことを「存在」で述べる。 -/
def leOn (S : SPO.FuncSetup α) (y x : α) : Prop :=
  ∃ (hy : y ∈ S.ground) (hx : x ∈ S.ground),
      SPO.FuncSetup.le S ⟨y, hy⟩ ⟨x, hx⟩

/-- S に対応する order-ideal family を ground 型 `α` 上の `SetFamily` として与える。 -/
noncomputable def idealFamily (S : SPO.FuncSetup α) : SetFamily α :=
  orderIdealFamily (le := leOn S) (V := S.ground)

@[simp] lemma sets_iff_isOrderIdeal
    (S : SPO.FuncSetup α) {I : Finset α} :
    (idealFamily S).sets I ↔ isOrderIdealOn (leOn S) S.ground I := Iff.rfl

/- ground 上の比較を subtype に引き上げる便利関数。 -/
--def toElem! (S : SPO.FuncSetup α) {x : α} (hx : x ∈ S.ground) : S.Elem := ⟨x, hx⟩

/-! ## 2) Lemma 3.3：同値（∼）と parallel の同値 -/

/-- 論文 Lemma 3.3（言明）：
`u, v` が同じ同値類（S.sim）であることと，`idealFamily S` における parallel が同値。 -/
lemma parallel_iff_sim
    (S : SPO.FuncSetup α) {u v : α}
    (hu : u ∈ S.ground) (hv : v ∈ S.ground) :
    Trace.Parallel (idealFamily S) u v
    ↔ SPO.FuncSetup.sim S (S.toElem! hu) (S.toElem! hv) := by
  -- 証明方針：
  --   →：parallel から「u を含む ideal ↔ v を含む ideal」の一致を用い，
  --      principal ideals を動かして y≤x の情報を recover して S.sim を示す。
  --   ←：S.sim から「u, v を含む ideal の一致」を構成。
  -- 技術要素：`isOrderIdealOn` の定義展開，`leOn` ↔ `S.le` の橋渡し。
  -- ここでは言明のみを確定させる。
  sorry

/-! ## 3) Lemma 3.1：maximal ⇒ rare -/

/-- 論文 Lemma 3.1（言明）：
S の極大元 `u` は，`idealFamily S` において rare。 -/
lemma rare_of_maximal
    (S : SPO.FuncSetup α) (u : S.Elem)
    (hu_max : SPO.FuncSetup.maximal S u) :
    Rare (idealFamily S) u.1 := by
  -- 証明方針：
  --   1) S.sim-クラス U をとると，Lemma 3.3 から U の各元は parallel。
  --   2) `I ↦ I \ U` の単射（`SetFamily` 側の基本操作）で deg(u) ≤ |E|/2 を得る。
  -- ここでは言明のみ。
  sorry

/-! ## 4) Lemma 3.5：parallel なら 1点トレースが単射 -/

/-- 直接版（re-export）：`Trace.trace_injective_of_parallel` を I(S) に特化した形。 -/
lemma trace_injective_of_parallel
    (S : SPO.FuncSetup α) {u v : α}
    (h : Trace.Parallel (idealFamily S) u v) :
    Function.Injective (Trace.eraseMap (idealFamily S) u) :=
  Trace.trace_injective_of_parallel (F := idealFamily S) h

/-- S.sim を仮定した版：Lemma 3.3 と合成して単射性を得る。 -/
lemma trace_injective_of_sim
    (S : SPO.FuncSetup α) {u v : α}
    (hu : u ∈ S.ground) (hv : v ∈ S.ground)
    (hSim : SPO.FuncSetup.sim S (S.toElem! hu) (S.toElem! hv)) :
    Function.Injective (Trace.eraseMap (idealFamily S) u) := by
  classical
  have hPar : Trace.Parallel (idealFamily S) u v :=
    (parallel_iff_sim S hu hv).mpr hSim
  exact trace_injective_of_parallel S hPar

/-! ## 5) Lemma 3.6：トレースの2主張（(1) functional 保持, (2) NDS は増えない） -/

/-(3.6-1 の言明)：
`u` が非自明クラスに属するとき，`I(V,≤)` の 1点トレースは
ある機能的前順序 S' の `idealFamily S'` に一致する（同型を許して）。 -/


/-- （3.6(1) の精密版の言明だけ）
    非自明クラスの点 `u` を 1 個潰すと，
    `idealFamily S` の 1点トレースは，`eraseOne S u` のイデアル族に一致する。 -/
lemma idealFamily_traceAt_eq_eraseOne
    (S : SPO.FuncSetup α) (u : S.Elem)
    (hNontriv : SPO.FuncSetup.nontrivialClass S u) :
    idealFamily (SPO.FuncSetup.eraseOne S u (S.f u)
                  (SPO.FuncSetup.f_ne_of_nontrivialClass (S := S) hNontriv))
      = Trace.traceAt u.1 (idealFamily S) := by
  classical
  -- （ここは従来どおり `sets` 同値の証明を進めればOK）
  sorry

/-- 使い勝手の良い “存在形” の再掲（既存の `traced_is_functional_family` を置換）。 -/
lemma traced_is_functional_family
    (S : SPO.FuncSetup α) (u : S.Elem)
    (hNontriv : SPO.FuncSetup.nontrivialClass S u) :
    ∃ S' : SPO.FuncSetup α,
      idealFamily S' = Trace.traceAt u.1 (idealFamily S) := by
  refine ⟨SPO.FuncSetup.eraseOneUsingSucc (S := S) u hNontriv, ?_⟩
  exact idealFamily_traceAt_eq_eraseOne S u hNontriv




/-- (3.6-2 の言明)：
`u` が非自明クラスに属するとき，1点トレースは NDS を増やさない。 -/
/-
lemma nds_monotone_under_trace
    (S : SPO.FuncSetup α) {u : α}
    (hu : u ∈ S.ground)
    (hNontriv :
  ∃ v, v ≠ u ∧ v ∈ S.ground ∧
    SPO.FuncSetup.sim S (S.toElem! hu) (S.toElem! (by assumption)))
    :
    NDS (idealFamily S) ≤
      NDS (Trace.traceAt u (idealFamily S)) := by
  /-
  証明方針：
    1) Lemma 3.5（trace 単射）→ エッジ数保存。
    2) `Counting.total_size_decompose_erase_add_degree` → 総サイズは `deg(u)` だけ減る。
    3) `rare_of_maximal`（Lemma 3.1）→ `2 * deg(u) ≤ |E|`。
    4) 代入して `NDS` 式の差が非正に落ちる。
  ここでは言明だけに留める（Counting/NDSfacts の補題を後で埋めて使う）。
  -/
  sorry
-/

--使ってない
lemma idealFamily_traceErase_agrees
    (S : SPO.FuncSetup α) (u : α) (hu : u ∈ S.ground) :
    ∃ S' : SPO.FuncSetup α,
      True ∧
      -- 族の一致（必要なら ground の Equiv を通す）
      True := by
  -- 後で（`isOrderIdealOn_reindex` 相当を噛ませて）証明
  exact ⟨S, True.intro, True.intro⟩

--使ってない
lemma parallel_of_sim
    (S : SPO.FuncSetup α) {u v : α} (hu : u ∈ S.ground) (hv : v ∈ S.ground)
    (hSim : SPO.FuncSetup.sim S (S.toElem! hu) (S.toElem! hv)) :
    Trace.Parallel (idealFamily S) u v := by
  -- `parallel_iff_sim` の →← のうち、← だけを先に言明
  sorry


lemma edgeFinset_traceAt (F : SetFamily α) (u : α) :
  (traceAt u F).edgeFinset = F.edgeFinset.image (λ A => A.erase u) := by
  ext B
  constructor
  · -- (→) traceAt の edgeFinset にある集合は元エッジの erase
    intro hB
    simp only [SetFamily.edgeFinset, traceAt, Finset.mem_filter,
               Finset.mem_powerset] at hB
    obtain ⟨hBsub, hSets⟩ := hB
    match decide (∃ A, F.sets A ∧ B = A.erase u) with
    | true =>
      simp only [decide_eq_true_eq] at hSets
      rcases hSets with ⟨A, hAsets, rfl⟩
      rw [Finset.mem_image]
      refine ⟨A, ?_, rfl⟩
      simp only [SetFamily.edgeFinset, Finset.mem_filter,
                 Finset.mem_powerset]
      constructor
      · exact F.inc_ground hAsets
      · exact decide_eq_true hAsets
    | false =>
      simp only [decide_eq_true_eq] at hSets
      rw [Finset.mem_image]
      obtain ⟨A, hAin, rfl⟩ := hSets
      use A
      constructor
      · exact (SetFamily.mem_edgeFinset_iff_sets F).mpr hAin
      · exact rfl

  · -- (←) 元エッジ A の erase は traceAt のエッジ
    intro hB
    simp only [Finset.mem_image] at hB
    rcases hB with ⟨A, hAin, rfl⟩
    simp only [SetFamily.edgeFinset, traceAt,
      Finset.mem_filter, Finset.mem_powerset]
    simp only [SetFamily.edgeFinset, Finset.mem_filter,
      Finset.mem_powerset] at hAin
    obtain ⟨hAsub, hAsets⟩ := hAin
    constructor
    · -- erase ⊆ ground.erase
      intro x hx
      rw [Finset.mem_erase] at hx
      rw [Finset.mem_erase]
      constructor
      · exact hx.1
      · exact hAsub hx.2
    · -- sets 部分は match で強制する
      simp_all only [decide_eq_true_eq]
      exact ⟨A, hAsets, rfl⟩

lemma NDS_traceAt_rewrite_mem {α : Type*} [DecidableEq α]
  (F : SetFamily α) (u : α) :
  NDS (traceAt u F) =
    2 * ∑ A ∈ F.edgeFinset, (A.erase u).card
      - F.numHyperedges * (F.ground.erase u).card := by
  unfold NDS
  simp only [traceAt, SetFamily.totalHyperedgeSize, SetFamily.numHyperedges]
  -- edgeFinset 部分を image に書き換え
  sorry

  --rw [edgeFinset_traceAt]
  -- sum over image を「元の和」に直す
  --simp_rw [Finset.mem_image]
  --rfl


lemma edgeFinset_traceAt_eq_image_erase
    (F : SetFamily α) (u : α) :
    (Trace.traceAt u F).edgeFinset
      = F.edgeFinset.image (fun A => A.erase u) := by
  -- すでに用意済みならその名前に合わせて置き換えてください
  -- ここは既存の `edgeFinset_traceErase` と同内容です
  classical
  -- `mem_edgeFinset_iff` と `Finset.mem_image` で両向きを出す標準形
  ext B; constructor
  · intro hB
    sorry
    --rcases (Trace.mem_traceAt_iff.mp hB) with ⟨A, hA, rfl⟩
    --exact Finset.mem_image.mpr ⟨A, hA, rfl⟩
  · intro hB
    rcases Finset.mem_image.mp hB with ⟨A, hA, rfl⟩
    sorry
    --exact (Trace.mem_traceAt_iff.mpr ⟨A, hA, rfl⟩)

@[simp] lemma ground_traceAt (F : SetFamily α) (u : α) :
    (Trace.traceAt u F).ground = F.ground.erase u := by
  -- `traceAt` の定義が `ground := F.ground.erase u` なら `rfl` で落ちます。
  -- そうでない場合も `ext x; simp` で示せます。
  ext x; simp [Trace.traceAt]

lemma NDS_traceAt_rewrite_core
    (F : SetFamily α) (u : α)
    (hEdgeImage :
      (Trace.traceAt u F).edgeFinset
        = F.edgeFinset.image (fun A => A.erase u)) :
    NDS (Trace.traceAt u F)
      =
      2 * (∑ A ∈ F.edgeFinset, (A.erase u).card : Int)
      - (((F.edgeFinset.image (fun A => A.erase u)).card : Nat) : Int)
          * (((Trace.traceAt u F).ground.card : Nat) : Int) := by
  classical
  -- 定義を開いて、`edgeFinset` は仮定で、総和は `sum_image` にし、
  -- エッジ数は `card` をそのまま使います。
  -- ground はまだ `Trace.traceAt u F).ground` のまま残しておきます。
  unfold NDS
  -- まず `totalHyperedgeSize` を `edgeFinset` 書き換え
  have h1 :
    (Trace.traceAt u F).totalHyperedgeSize
      = ∑ A ∈ (Trace.traceAt u F).edgeFinset, A.card := rfl
  -- `edgeFinset` を `image erase` に置換して `sum_image` に変形
  -- `sum_image` 用に射影を一度書き換える：
  -- 今回は右辺の形をターゲットにしているので、`hEdgeImage` を使って
  -- 目標通りの形に整えます。
  -- 以降、`simp` で一括整形します。
  sorry
  --
  --simp [NDS, hEdgeImage, Finset.sum_image, Function.LeftInverse.id,
  --      SetFamily.totalHyperedgeSize, SetFamily.numHyperedges]  -- 補助 simp があるなら追加
  -- 実務では `sum_image` の可換性（像が重ならない）証明が必要ですが、
  -- ここでは “式の形”だけを固定しておくための骨格（詳細は別 sorry で）。
  --admit

/-- parallel により |E| が保存され，ground は `erase` に落ちる版。
    こちらを最終的に `hL_eq_traced` に使います。 -/
lemma NDS_traceAt_rewrite_parallel
    (F : SetFamily α) (u v : α)
    (hPar : Trace.Parallel F u v)
    (huV : u ∈ F.ground) :
    NDS (Trace.traceAt u F)
      =
      2 * (∑ A ∈ F.edgeFinset, (A.erase u).card : Int)
      - (F.numHyperedges : Int) * ((F.ground.erase u).card : Int) := by
  classical
  -- まず core 版で `edgeFinset` を image にし、次に
  --   (i) 画像の個数 = 元の個数  （parallel → trace-inj → card_image = card）
  --   (ii) ground.card は erase で 1 減る
  have hEdgeImage := edgeFinset_traceAt_eq_image_erase (F := F) u
  have h0 := NDS_traceAt_rewrite_core (F := F) (u := u) hEdgeImage
  -- (i) 画像の個数 = 元の個数
  have hCard :
      (F.edgeFinset.image (fun A => A.erase u)).card = F.edgeFinset.card := by
    sorry
    --search_proof
    --(Trace.card_image_erase_of_parallel (F := F) (u := u) (v := v) hPar).symm

  -- (ii) ground は erase
  have hG : (Trace.traceAt u F).ground = F.ground.erase u := ground_traceAt F u
  -- 以上を Int キャストで流し込む
  -- まず h0 の右辺に (i)(ii) を反映
  have : (((F.edgeFinset.image (fun A => A.erase u)).card : Nat) : Int)
            = (F.numHyperedges : Int) := by

    --simpa [SetFamily.numHyperedges, hCard]  -- Nat→Int キャストは `simp` で
    sorry
  -- ground 側
  have : (((Trace.traceAt u F).ground.card : Nat) : Int)
            = ((F.ground.erase u).card : Int) := by
    simp
  -- 以上で式がちょうど目標右辺へ一致
  simp [SetFamily.numHyperedges]
  sorry

lemma nds_monotone_under_trace
    (S : SPO.FuncSetup α) {u : α}
    (hu : u ∈ S.ground)
    (hNontriv :
      ∃ (v : α) (hv : v ∈ S.ground), v ≠ u ∧
        SPO.FuncSetup.sim S (S.toElem! hu) (S.toElem! hv)) :
    NDS (idealFamily S) ≤
      NDS (Trace.traceAt u (idealFamily S)) := by
  classical
  rcases hNontriv with ⟨v, hv, hne, hsim⟩
  -- ∼ ⇒ parallel
  have hPar : Trace.Parallel (idealFamily S) u v :=
    (parallel_iff_sim S hu hv).mpr hsim
  -- |E| 保持
  have hCard :
      (idealFamily S).edgeFinset.card
        = ((idealFamily S).edgeFinset.image (fun A => A.erase u)).card :=
    (Trace.card_image_erase_of_parallel (F := idealFamily S) hPar).symm
  -- NDS 差分式
  have hdiff :=
    AvgRare.Counting.nds_difference_by_trace
      (F := idealFamily S) (x := u) hCard
  -- 残りは rare を入れて ≤ に落とすところ（後で埋める）
  set uElem : S.Elem := ⟨u, hu⟩ with uElem_def
  have hNontrivElem : SPO.FuncSetup.nontrivialClass S uElem := by
    dsimp [SPO.FuncSetup.toElem!]
    dsimp [SPO.FuncSetup.nontrivialClass]
    use ⟨v, hv⟩
    constructor
    · exact Subtype.coe_ne_coe.mp hne
    · exact hsim

  have hMax : SPO.FuncSetup.maximal S uElem :=
    SPO.FuncSetup.maximal_of_nontrivialClass (S := S) (x := uElem) hNontrivElem
  have hRareNat : Rare (idealFamily S) u := by
    -- rare_of_maximal は `S.Elem` を引数に取るので uElem を渡す
    -- 結論は `Rare (idealFamily S) uElem.1` になるが、`uElem.1 = u` なので
    -- それで書き換えておしまい
    have hR := rare_of_maximal (S := S) (u := uElem) hMax
    -- `uElem.1 = u` は構成から明らか（`uElem : ⟨u, hu⟩`）
    change Rare (idealFamily S) u
    -- `rfl` で `uElem.1` を `u` に置換
    simpa [uElem_def]

    --rare_of_maximal (S := S) (u := uElem) hMax
  -- 2 * deg(u) ≤ |E|（Nat）を Int に持ち上げて a - b ≤ 0 を作る
  have hRareInt :
      (2 : Int) * ((idealFamily S).degree u : Int)
        ≤ (idealFamily S).numHyperedges := by
    have hNat : 2 * (idealFamily S).degree u ≤ (idealFamily S).numHyperedges := hRareNat
    have hCast :
        ((2 * (idealFamily S).degree u : Nat) : Int)
          ≤ (idealFamily S).numHyperedges := by
      exact_mod_cast hNat
    calc
      (2 : Int) * ((idealFamily S).degree u : Int)
          = ((2 * (idealFamily S).degree u : Nat) : Int) := by
            simp [Nat.cast_mul, Nat.cast_ofNat]
      _ ≤ (idealFamily S).numHyperedges := hCast
    -- rare から (2*deg - |E|) ≤ 0 を “直に” 作る（omega 不要）
  have hExtraLe :
      ((2 : Int) * ((idealFamily S).degree u : Int)
        - (idealFamily S).numHyperedges) ≤ 0 := by
    simp_all only [ne_eq, Parallel, sets_iff_isOrderIdeal, NDSfacts.NDS_def, SPO.FuncSetup.maximal_iff, Subtype.forall]
    obtain ⟨val, property⟩ := uElem
    omega

  -- “余分” ≤ 0 を L に足して NDS ≤ L
  have hNDS_le_L :
      NDS (idealFamily S)
        ≤ (2 * (∑ A ∈ (idealFamily S).edgeFinset, (A.erase u).card : Int)
            - ((idealFamily S).numHyperedges : Int) * ((idealFamily S).ground.card : Int)) := by
    -- L を短名に
    set L :
      Int := 2 * (∑ A ∈ (idealFamily S).edgeFinset, (A.erase u).card : Int)
              - ((idealFamily S).numHyperedges : Int) * ((idealFamily S).ground.card : Int) with hLdef
    -- ここも simpa を避けて rw → exact
    have htmp := hdiff
    -- htmp : NDS = (2*Σ|A\{u}| - |E||V|) + (2deg - |E|)
    -- 右辺の最初の括弧を L に置換
    -- (等式の右側だけを書き換えるため、等式に対しての書換を使います)
    have : NDS (idealFamily S)
        = L + ((2 : Int) * ((idealFamily S).degree u : Int)
                 - (idealFamily S).numHyperedges) := by
      -- htmp を L の定義で置換
      simpa [hLdef] using htmp
    -- 以上の等式と hExtraLe から NDS ≤ L
    calc
      NDS (idealFamily S)
          = L + ((2 : Int) * ((idealFamily S).degree u : Int)
                   - (idealFamily S).numHyperedges) := this
      _ ≤ L + 0 := add_le_add_left hExtraLe L
      _ = L := by simp

  /- ここから L ≤ NDS(traceAt)。
     核心は ground の単調性：|V'| = |V.erase u| ≤ |V| と |E| ≥ 0。 -/

  -- ground の大きさは必ず減らない（Int 版）
  have hGround_le :
      (((idealFamily S).ground.erase u).card : Int)
        ≤ ((idealFamily S).ground.card : Int) := by
    simp_all only [ne_eq, Parallel, sets_iff_isOrderIdeal, NDSfacts.NDS_def, SPO.FuncSetup.maximal_iff, Subtype.forall,
    add_le_iff_nonpos_right, Int.ofNat_le, uElem]
    obtain ⟨val, property⟩ := uElem
    rw [Finset.card_erase_of_mem]
    · simp_all only [Nat.sub_le]
    · exact hu

  -- |E| は Int で非負
  have hE_nonneg : (0 : Int) ≤ ((idealFamily S).numHyperedges : Int) := by
    exact_mod_cast (Nat.zero_le ( (idealFamily S).numHyperedges ))

  -- これで  -|E||V| ≤ -|E||V'|  が出る
  have hNegMul :
      - ((idealFamily S).numHyperedges : Int) * ((idealFamily S).ground.card : Int)
        ≤ - ((idealFamily S).numHyperedges : Int) * (((idealFamily S).ground.erase u).card : Int) := by
    -- まず |E||V'| ≤ |E||V|
    simp_all only [ne_eq, Parallel, sets_iff_isOrderIdeal, NDSfacts.NDS_def, SPO.FuncSetup.maximal_iff, Subtype.forall,
    add_le_iff_nonpos_right, Int.ofNat_le, Int.ofNat_zero_le, neg_mul, Int.neg_le_neg_iff, uElem]
    obtain ⟨val, property⟩ := uElem
    norm_cast
    gcongr

  -- さらに 2*Σ|A\{u}| を両辺に足して、L ≤ 2*Σ|A\{u}| - |E||V'|
  have hL_le_basic :
      (2 * (∑ A ∈ (idealFamily S).edgeFinset, (A.erase u).card : Int)
        - ((idealFamily S).numHyperedges : Int) * ((idealFamily S).ground.card : Int))
      ≤
      (2 * (∑ A ∈ (idealFamily S).edgeFinset, (A.erase u).card : Int)
        - ((idealFamily S).numHyperedges : Int) * (((idealFamily S).ground.erase u).card : Int)) := by
    simp_all only [ne_eq, Parallel, sets_iff_isOrderIdeal, NDSfacts.NDS_def, SPO.FuncSetup.maximal_iff, Subtype.forall,
    add_le_iff_nonpos_right, Int.ofNat_le, Int.ofNat_zero_le, neg_mul, Int.neg_le_neg_iff, Int.sub_le_sub_left_iff,
    uElem]
  -- NDS(traceAt) の書き換え（既に用意されている rewrite 補題）
  have hTraceRew :
      NDS (Trace.traceAt u (idealFamily S))
        =
        2 * (∑ A ∈ (idealFamily S).edgeFinset, (A.erase u).card : Int)
          - ((idealFamily S).numHyperedges : Int) * (((idealFamily S).ground.erase u).card : Int) := by
    exact NDS_traceAt_rewrite_parallel (idealFamily S) u v hPar hu

  -- 以上より L ≤ NDS(traceAt)
  have hL_le_trace :
      (2 * (∑ A ∈ (idealFamily S).edgeFinset, (A.erase u).card : Int)
        - ((idealFamily S).numHyperedges : Int) * ((idealFamily S).ground.card : Int))
      ≤ NDS (Trace.traceAt u (idealFamily S)) :=
    hL_le_basic.trans (le_of_eq (hTraceRew).symm)

  -- まとめ： NDS ≤ L ≤ NDS(traceAt)
  exact le_trans hNDS_le_L hL_le_trace



end PaperSync
end AvgRare


/-
import Mathlib.Data.Finset.Basic
import AvgRare.Basics.SetFamily
import AvgRare.Basics.Trace.Common
import AvgRare.SPO.FuncSetup
import AvgRare.Basics.Ideals

universe u

namespace AvgRare
namespace PaperSync

open Classical
open Basics SetFamily Trace
open FuncSetup

variable {α : Type u} [DecidableEq α]

/-! ### 前提メモ
`SetFamily α` は構造体版：
  * `ground : Finset α`
  * `sets : Finset α → Prop`
  * `inc_ground : sets A → A ⊆ ground`
`↘` は Common 側で `restrict : SetFamily α → Finset α → SetFamily α` として定義済みとする。
-/

/-- サブタイプ化（`Elem S = {x // x ∈ S.V}`）。他所にあるなら import に切替可。 -/
abbrev Elem (S : FuncSetup α) := {x : α // x ∈ S.V}

/-- `proj : S.Elem → Quot S.ker`（SCC 商への射影） -/
@[simp] def proj (S : FuncSetup α) (x : Elem S) : Quot S.ker :=
  Quot.mk _ x

/-- Finset 版の商像。Common の `imageQuot` をそのまま使う別名。 -/
noncomputable def imQuot (S : FuncSetup α)
    (A : Finset (Elem S)) : Finset (Quot S.ker) :=
  AvgRare.Basics.Trace.imageQuot (S.ker) A


/-- 商像の単調性：`A ⊆ B → imQuot A ⊆ imQuot B` -/
lemma imQuot_mono (S : FuncSetup α)
    {A B : Finset (Elem S)} (hAB : A ⊆ B) :
    imQuot S A ⊆ imQuot S B := by
  classical
  -- Common 側の一般補題を流用
  simpa [imQuot] using
    (AvgRare.Basics.Trace.imageQuot_mono (E:=S.ker) (A:=A) (B:=B) hAB)

/-- 集合族の SCC 商への像：各 `A ∈ 𝓕` を `imQuot S A` に写す。 -/
noncomputable def mapFamilyToQuot (S : FuncSetup α)
    (𝓕 : SetFamily (Elem S)) : SetFamily (Quot S.ker) :=
{ ground := 𝓕.ground.image (fun a => proj S a)
, sets  := fun B : Finset (Quot S.ker) =>
    ∃ A : Finset (Elem S), 𝓕.sets A ∧ B ⊆ imQuot S A
, decSets := by infer_instance
, inc_ground := by
    intro B hB
    rcases hB with ⟨A, hA, hBsub⟩
    -- `A ⊆ ground` を像に押す
    have hAsub : A ⊆ 𝓕.ground := 𝓕.inc_ground hA
    have hImg : imQuot S A ⊆ 𝓕.ground.image (fun a => proj S a) := by
      intro q hq
      rcases Finset.mem_image.mp (by
        -- `imQuot S A = A.image (proj S)` と同値
        change q ∈ (A.image (fun a => proj S a)) at hq
        exact hq) with ⟨a, haA, rfl⟩
      exact Finset.mem_image.mpr ⟨a, hAsub haA, rfl⟩
    exact hBsub.trans hImg }

@[simp] lemma imQuot_def (S : FuncSetup α) (A : Finset (Elem S)) :
  imQuot S A = A.image (fun a => proj S a) := rfl

@[simp] lemma mem_imQuot_iff (S : FuncSetup α) {A : Finset (Elem S)} {q : Quot S.ker} :
  q ∈ imQuot S A ↔ ∃ a ∈ A, proj S a = q := by
  classical
  simp [imQuot_def, proj, Finset.mem_image]

-- 画像の単調性、`simp` で使いたいので `@[simp]` にもしておく（任意）
@[simp] lemma imQuot_mono' (S : FuncSetup α)
    {A B : Finset (Elem S)} (hAB : A ⊆ B) :
    imQuot S A ⊆ imQuot S B :=
  imQuot_mono (S:=S) hAB

/-- `mapFamilyToQuot` の単調性（述語の含意として記述） -/
lemma mapFamilyToQuot_mono (S : FuncSetup α)
  {𝓕 𝓖 : SetFamily (Elem S)}
  (hFG : ∀ {A : Finset (Elem S)}, 𝓕.sets A → 𝓖.sets A) :
  ∀ {B : Finset (Quot S.ker)},
    (mapFamilyToQuot S 𝓕).sets B → (mapFamilyToQuot S 𝓖).sets B := by
  intro B hB
  rcases hB with ⟨A, hA, hBsub⟩
  exact ⟨A, hFG hA, hBsub⟩



/-- idealFamily の像（商側の family）。 -/
noncomputable def idealFamilyQuot (S : FuncSetup α) :
    SetFamily (Quot S.ker) :=
  mapFamilyToQuot S (idealFamily S)

lemma trace_map_commute_subset (S : FuncSetup α)
    (𝓕 : SetFamily (Elem S)) (U : Finset (Elem S)) :
    ∀ {B : Finset (Quot S.ker)},
      (mapFamilyToQuot S (𝓕 ↘ U)).sets B →
      ∃ C : Finset (Quot S.ker),
        (mapFamilyToQuot S 𝓕).sets C ∧ B ⊆ imQuot S U := by
  classical
  intro B hB
  rcases hB with ⟨A', hA'rest, hBsub⟩
  rcases hA'rest with ⟨C, hCmem, hA'subC, hA'subU⟩
  refine ⟨imQuot S C, ?_, ?_⟩
  · exact ⟨C, hCmem, by intro q hq; exact hq⟩
  · exact fun q hq =>
      (imQuot_mono (S:=S) hA'subU) (hBsub hq)

/-- 橋渡し（包含版）。 -/
lemma ideal_trace_bridge_subset_ideal (S : FuncSetup α)
    (U : Finset (Elem S)) :
    ∀ {B : Finset (Quot S.ker)},
      (mapFamilyToQuot S ((idealFamily S) ↘ U)).sets B →
      ∃ C : Finset (Quot S.ker), (idealFamilyQuot S).sets C ∧ B ⊆ imQuot S U := by
  classical
  intro B hB
  rcases trace_map_commute_subset (S:=S) (𝓕:=(idealFamily S)) (U:=U) (B:=B) hB with ⟨C, hC, hsub⟩
  exact ⟨C, hC, hsub⟩

lemma ideal_trace_bridge_subset (S : FuncSetup α)
    (U : Finset (Elem S)) :
    ∀ {B : Finset (Quot S.ker)},
      (mapFamilyToQuot S ((idealFamily S) ↘ U)).sets B →
      ∃ C : Finset (Quot S.ker), (idealFamilyQuot S).sets C ∧ B ⊆ imQuot S U := by
  classical
  intro B hB
  rcases trace_map_commute_subset (S:=S) (𝓕:=idealFamily S) (U:=U) (B:=B) hB with ⟨C, hC, hsub⟩
  exact ⟨C, hC, hsub⟩

/-- 安定性: U が f に関して閉じている -/
def stable (S : FuncSetup α) (U : Finset (Elem S)) : Prop :=
  ∀ x ∈ U, S.fV x ∈ U

/-- Ideal 的性質（構造体版 SetFamily 用の簡易定義） -/
def IsIdeal {β} [DecidableEq β] (F : SetFamily β) : Prop :=
  ∀ ⦃A B⦄, F.sets B → A ⊆ B → F.sets A

/-- U が S(Elem) に関して安定（例：f-前像で閉、など望ましい条件へ差し替え） -/
-- 主定理の証明には関係ない？
def StableUnder (S : FuncSetup α) (U : Finset (Elem S)) : Prop :=
  ∀ {x}, x ∈ U → S.fV x ∈ U

/-- 逆向き：商側で `B ⊆ C` かつ `B ⊆ imQuot S U` が言え、かつ 𝓕 の元が
`ker` に関して **飽和（saturated）** しているなら、`B ∈ mapFamilyToQuot S (𝓕 ↘ U)`。
ここで飽和とは `x ~ y` かつ `x ∈ A` なら `y ∈ A` が成り立つこと。 -/
lemma trace_map_commute_superset_of_ker_saturated (S : FuncSetup α)
    (𝓕 : SetFamily (Elem S))
    (U : Finset (Elem S))
    (hSat : ∀ {A : Finset (Elem S)}, 𝓕.sets A →
              ∀ {x y : Elem S}, S.ker.r x y → x ∈ A → y ∈ A) :
    ∀ {B : Finset (Quot S.ker)},
      (∃ C : Finset (Quot S.ker), (mapFamilyToQuot S 𝓕).sets C ∧ B ⊆ C ∧ B ⊆ imQuot S U) →
      (mapFamilyToQuot S (𝓕 ↘ U)).sets B := by
  classical
  intro B h
  rcases h with ⟨C, hCsets, hBC, hBU⟩
  rcases hCsets with ⟨A, hAmem, hCsub⟩
  -- 各 q ∈ B について U 内代表を選ぶ
  have h1 : ∀ q, q ∈ B → ∃ x : Elem S, x ∈ U ∧ proj S x = q := by
    intro q hq
    exact (mem_imQuot_iff (S:=S)).1 (hBU hq)
  choose rep hrepU hrepProj using h1
  -- A' を B の各要素の代表の集合として作る
  let A' : Finset (Elem S) := B.attach.image (fun q => rep q.1 q.2)
  have hA'subU : A' ⊆ U := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨q, hqB, rfl⟩
    exact hrepU q.1 q.2
  -- A' が A に含まれることを示す（飽和性を使う）
  have hA'subA : A' ⊆ A := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨q, hqB, rfl⟩
    -- `q.1 ∈ B` かつ `B ⊆ C` より `q.1 ∈ C`
    have hqC : q.1 ∈ C := hBC q.2
    -- `C ⊆ imQuot S A` より、`q.1 ∈ imQuot S A`
    have hq_imA : q.1 ∈ imQuot S A := hCsub hqC
    -- ある y ∈ A で proj y = q.1
    rcases (mem_imQuot_iff (S:=S)).1 hq_imA with ⟨y, hyA, hyProj⟩
    -- 代表の等値から kernel 関係を得る
    have hEq : Quot.mk (S.ker) (rep q.1 q.2) = Quot.mk (S.ker) y := by
      have : proj S (rep q.1 q.2) = proj S y := by
        have : proj S (rep q.1 q.2) = q.1 := hrepProj q.1 q.2
        exact this.trans (by simp_all only [Subtype.forall, imQuot_def, proj, Finset.mem_attach, Finset.mem_image, true_and, exists_apply_eq_apply,
    Subtype.exists, A'])
      simpa [proj] using this
    have hRel0 : S.ker.r (rep q.1 q.2) y := Quotient.eq''.mp hEq
    -- 飽和性は向きを `y → rep` に使う
    have hRel1 : S.ker.r y (rep q.1 q.2) := (S.ker.iseqv.symm) hRel0
    exact hSat hAmem hRel1 hyA
  -- B ⊆ imQuot S A'
  have hBsubA' : B ⊆ imQuot S A' := by
    intro q hq
    -- `⟨q,hq⟩ : {q // q ∈ B}` は `B.attach` の元
    have hqa : ⟨q, hq⟩ ∈ B.attach := by exact Finset.mem_attach _ _
    have hx_mem : rep q hq ∈ A' := by
      exact Finset.mem_image.mpr ⟨⟨q, hq⟩, hqa, rfl⟩
    have hproj : proj S (rep q hq) = q := hrepProj q hq
    exact (mem_imQuot_iff (S:=S)).2 ⟨_, hx_mem, hproj⟩
  -- まとめ：`A' ⊆ A` かつ `A' ⊆ U`、そして `B ⊆ imQuot S A'`
  exact ⟨A', ⟨A, hAmem, hA'subA, hA'subU⟩, hBsubA'⟩


/-- `trace`（制限）と商への像の交換：包含版（restrict 風）。
`B ∈ mapFamilyToQuot S (𝓕 ↘ U)` なら、ある `C ∈ mapFamilyToQuot S 𝓕` があり、
`B ⊆ C` かつ `B ⊆ imQuot S U` が成り立つ。 -/
lemma trace_map_commute_subset_restrict (S : FuncSetup α)
    (𝓕 : SetFamily (Elem S)) (U : Finset (Elem S)) :
    ∀ {B : Finset (Quot S.ker)},
      (mapFamilyToQuot S (𝓕 ↘ U)).sets B →
      ∃ C : Finset (Quot S.ker),
        (mapFamilyToQuot S 𝓕).sets C ∧ B ⊆ C ∧ B ⊆ imQuot S U := by
  classical
  intro B hB
  rcases hB with ⟨A', hA'rest, hBsub⟩
  rcases hA'rest with ⟨C, hCmem, hA'subC, hA'subU⟩
  refine ⟨imQuot S C, ?_, ?_, ?_⟩
  · exact ⟨C, hCmem, by intro q hq; exact hq⟩
  · exact fun q hq => (imQuot_mono (S:=S) hA'subC) (hBsub hq)
  · exact fun q hq => (imQuot_mono (S:=S) hA'subU) (hBsub hq)

@[simp] lemma idealFamily_sets_iff (S : FuncSetup α)
  {A : Finset (Elem S)} :
  (idealFamily S).sets A ↔ S.isOrderIdeal A := Iff.rfl

/-- 等式版（核に関する飽和性から）。
`I.carrier` の各元が kernel に関して飽和（=順序イデアル）であるとき、
`trace` と商像は制限レベルで可換。 -/
lemma ideal_trace_bridge_eq_of_ker_saturated
  (S : FuncSetup α) (U : Finset (Elem S)) :
  ∀ {B : Finset (Quot S.ker)},
    (mapFamilyToQuot S ((idealFamily S) ↘ U)).sets B ↔
    (∃ C : Finset (Quot S.ker), (idealFamilyQuot S).sets C ∧ B ⊆ C ∧ B ⊆ imQuot S U) := by
  classical
  intro B; constructor
  · -- → 方向：制限→商像への包含をそのまま使う
    intro h
    rcases trace_map_commute_subset_restrict
            (S:=S) (𝓕:=(idealFamily S)) (U:=U) (B:=B) h with
      ⟨C, hC, hBC, hBU⟩
    exact ⟨C, hC, hBC, hBU⟩
  · -- ← 方向：kernel 飽和性を使って元へ戻す
    intro h
    -- idealFamily の各元は isOrderIdeal なので ker 飽和
    have hSat :
      ∀ {A : Finset (Elem S)}, (idealFamily S).sets A →
        ∀ {x y : Elem S}, S.ker.r x y → x ∈ A → y ∈ A := by
      intro A hA x y hxy hx
      -- `ideal_saturated_under_ker` を適用
      exact (FuncSetup.ideal_saturated_under_ker
              (S:=S) (hA := (idealFamily_sets_iff (S:=S)).1 hA)) hxy hx
    -- 逆向き補題で終了
    exact trace_map_commute_superset_of_ker_saturated
            (S:=S) (𝓕:=(idealFamily S)) (U:=U) (hSat:=hSat) (B:=B) h

lemma ideal_trace_bridge_eq_of_ker_saturated_ideal (S : FuncSetup α)
    (U : Finset (Elem S)) :
    ∀ {B : Finset (Quot S.ker)},
      (mapFamilyToQuot S ((idealFamily S) ↘ U)).sets B ↔
      (∃ C : Finset (Quot S.ker), (idealFamilyQuot S).sets C ∧ B ⊆ C ∧ B ⊆ imQuot S U) := by
  classical
  intro B; constructor
  · intro h
    rcases trace_map_commute_subset_restrict (S:=S) (𝓕:=(idealFamily S)) (U:=U) (B:=B) h with
      ⟨C, hC, hBC, hBU⟩
    exact ⟨C, hC, hBC, hBU⟩
  · intro h
    -- idealFamily の各元は isOrderIdeal なので ker 飽和
    have hSat : ∀ {A : Finset (Elem S)}, (idealFamily S).sets A →
        ∀ {x y : Elem S}, S.ker.r x y → x ∈ A → y ∈ A := by
      intro A hA x y hxy hx
      exact (FuncSetup.ideal_saturated_under_ker (S:=S)
              (hA := (idealFamily_sets_iff (S:=S)).1 hA)) hxy hx
    exact trace_map_commute_superset_of_ker_saturated (S:=S)
      (𝓕:=(idealFamily S)) (U:=U) (hSat:=hSat) (B:=B) h

lemma ideal_trace_bridge_eq (S : FuncSetup α)
    (U : Finset (Elem S)) :
    (mapFamilyToQuot S ((idealFamily S) ↘ U)).sets =
    (fun B : Finset (Quot S.ker) =>
      ∃ C : Finset (Quot S.ker),
        (idealFamilyQuot S).sets C ∧ B ⊆ C ∧ B ⊆ imQuot S U) := by
  -- すでにこの等式の両向きを証明した補題があり，それは「述語の同値」です。
  -- ここでは述語の等式にしたいので，点ごとの `propext` で仕上げます。
  funext B
  exact propext
    (ideal_trace_bridge_eq_of_ker_saturated_ideal (S:=S) (U:=U) (B:=B))

lemma idealFamily_sets_to_isOrderIdeal (S : FuncSetup α)
  {A : Finset (Elem S)} (h : (idealFamily S).sets A) :
  S.isOrderIdeal A := by simp_all only [idealFamily_sets_iff]

lemma isOrderIdeal_to_idealFamily_sets (S : FuncSetup α)
  {A : Finset (Elem S)} (h : S.isOrderIdeal A) :
  (idealFamily S).sets A := by simp_all only [idealFamily_sets_iff]

end PaperSync
end AvgRare
-/
