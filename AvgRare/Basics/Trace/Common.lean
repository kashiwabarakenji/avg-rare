import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import AvgRare.Basics.SetFamily
import AvgRare.Basics.Ideals
import LeanCopilot

/-
Common.lean — Trace と汎用補助

このファイルでは
* 1点トレース `Trace.traceAt`
* 並行性 `Trace.Parallel`
* その場で使える小補助

を提供します。証明が重い主張（単射性など）は「言明だけ」を先に置き、
後で `IdealsTrace.lean` 等で埋める方針です。
-/

universe u
open Classical
open scoped BigOperators

namespace AvgRare
namespace Trace
open SetFamily

variable {α : Type u} [DecidableEq α]

/-- 1点トレース：各ハイパーエッジから要素 `x` を取り除いた族。
`ground` は `F.ground.erase x` に落とす。 -/
--idealだけでなく、集合族一般にTraceを定義している。
noncomputable def traceAt (x : α) (F : SetFamily α) : SetFamily α := by
  classical
  refine
  { ground := F.ground.erase x
    , sets   := fun B =>
        ∃ A : Finset α, F.sets A ∧ B = A.erase x
    , decSets := Classical.decPred _
    , inc_ground := ?_ }
  intro B hB
  rcases hB with ⟨A, hA, hBsub, hBsubU⟩
  intro y
  simp only [Finset.mem_erase]
  intro h
  constructor
  · exact h.1
  · exact F.inc_ground hA (by
      -- `y ∈ A.erase x` なら `y ∈ A` なので、`A ⊆ F.ground` を使う
      simp_all only [ne_eq])

@[simp] lemma traceAt_ground (x : α) (F : SetFamily α) :
    (traceAt x F).ground = F.ground.erase x := rfl


--ここからは使わないかも。
/-- `Subtype` のエッジを `erase u` に写す自然な射。 -/
def eraseMap (F : SetFamily α) (u : α) :
    {A // F.sets A} → Finset α := fun A => (Subtype.val A).erase u

@[simp] lemma eraseMap_apply (F : SetFamily α) (u : α) (A : {A // F.sets A}) :
    eraseMap F u A = (A.val).erase u := rfl

-- 以下の部分は、idealsTraceと融合する必要があり。多分、全部コメントアウト
/-
--FuncSetupを使わない部分
/-- （言明のみ）Lemma 3.5 に対応：
`u` と `v` が Parallel なら，`A ↦ A.erase u` はエッジ集合上で単射。 -/
lemma trace_injective_of_parallel
    (F : SetFamily α) {u v : α} (h : F.Parallel u v) :
    Function.Injective (eraseMap F u) := by
  -- 詳細証明は IdealsTrace で（`mem_edgeFinset_iff` などと併用）
  intro A1 A2 hEq
  -- 将来の証明埋め込みで `simp_all` を活かせるように温存
  sorry

/-- Parallel なら `image (erase u)` に重複が出ない。 -/
--uとvが一致しないという条件がない。Nontrivの条件に統一する方向。
lemma card_image_erase_of_parallel
    (F : SetFamily α) {u v : α} (h : F.Parallel u v) :
    (F.edgeFinset.image (fun A => A.erase u)).card = F.edgeFinset.card := by
  classical
  -- `trace_injective_of_parallel` と `Finset.card_image_iff` で
  sorry

lemma NDS_traceAt_rewrite
    (F : SetFamily α) (u : α)
    (hEdgeImage : (Trace.traceAt u F).edgeFinset = F.edgeFinset.image (fun A => A.erase u))
    (hCardPres : (Trace.traceAt u F).numHyperedges = F.numHyperedges)
    (hGround   : (Trace.traceAt u F).ground = F.ground) :
    (Trace.traceAt u F).NDS
      = 2 * (∑ A ∈ F.edgeFinset, (A.erase u).card : Int)
        - (F.numHyperedges : Int) * (F.ground.card : Int) := by
  -- unfold NDS; rewrite 3つの仮定; `sum_image` の書き換えで完成（詳細は後で）
  sorry
-/

--------

@[simp] lemma ground_card_trace_of_mem
    (F : SetFamily α) {u : α} (hu : u ∈ F.ground) :
    (traceAt u F).ground.card = F.ground.card - 1 := by
  classical
  -- `traceAt` の ground 定義が `F.ground.erase u` であることを使用
  simp [traceAt, hu]

/-ChatGPTの3番-/
lemma erase_on_edges_injective_of_parallel
    (F : SetFamily α) {u v : α}
    (huv : F.Parallel u v) (hne : u ≠ v) :
    Function.Injective
      (fun (A : {A // A ∈ F.edgeFinset}) => (A.1).erase u) := by
  classical
  intro A B h
  -- 目標は A = B（Subype.ext で値の一致を示せば十分）
  apply Subtype.ext
  -- Finset extensionality で要素ごとに同値を示す
  apply Finset.ext
  intro x
  by_cases hx : x = u
  · -- ケース1: x = u のとき，u の所属を比較したい

    -- A,B がエッジであることから sets 証拠を回収
    have hAsets : F.sets A.1 := by
      simp_all only [SetFamily.Parallel, ne_eq]
      obtain ⟨val, property⟩ := A
      obtain ⟨val_1, property_1⟩ := B
      simp_all only
      simp_all only [SetFamily.mem_edgeFinset]

    have hBsets : F.sets B.1 := by
      simp_all only [SetFamily.Parallel, ne_eq]
      obtain ⟨val, property⟩ := A
      obtain ⟨val_1, property_1⟩ := B
      simp_all only
      simp_all only [SetFamily.mem_edgeFinset, and_true]

    -- `A.erase u = B.erase u` から v の所属は一致
    have hv_on_erases :
        (v ∈ A.1.erase u) ↔ (v ∈ B.1.erase u) := by
      constructor <;> intro hv' <;> simpa [h] using hv'
    -- v ≠ u なので，`erase u` で v の所属は不変
    have hvAB : (v ∈ A.1) ↔ (v ∈ B.1) := by
      have hvne : v ≠ u := (ne_comm).1 hne
      simpa [Finset.mem_erase, hvne] using hv_on_erases
    -- Parallel: (u ∈ X) ↔ (v ∈ X) を A,B それぞれで使用し合成
    rw [hx]
    calc
      u ∈ A.1 ↔ v ∈ A.1 := by
        dsimp [SetFamily.Parallel] at huv
        constructor
        · intro hu
          have : A.1 ∈ {A : Finset α | F.sets A ∧ u ∈ A} := by
            exact Set.mem_sep hAsets hu
          subst hx
          simp_all only [ne_eq, Finset.mem_erase, Set.mem_setOf_eq, true_and]
        · intro hv
          have : A.1 ∈ {A : Finset α | F.sets A ∧ v ∈ A} := by
            exact Set.mem_sep hAsets hv
          --subst hx
          have : A.1 ∈ {A : Finset α | F.sets A ∧ u ∈ A} := by
            rw [←huv] at this
            exact this
          rw [Set.mem_setOf_eq] at this
          exact this.2
      _       ↔ v ∈ B.1 := hvAB
      _       ↔ u ∈ B.1 := by
        dsimp [SetFamily.Parallel] at huv
        constructor
        · intro hu
          have : B.1 ∈ {A : Finset α | F.sets A ∧ v ∈ A} := by
            exact Set.mem_sep hBsets hu
          have : B.1 ∈ {A : Finset α | F.sets A ∧ u ∈ A} := by
            rw [←huv] at this
            exact this
          rw [Set.mem_setOf_eq] at this
          exact this.2
        · intro hv
          have : B.1 ∈ {A : Finset α | F.sets A ∧ u ∈ A} := by
            exact Set.mem_sep hBsets hv
          --subst hx
          have : B.1 ∈ {A : Finset α | F.sets A ∧ v ∈ A} := by
            rw [huv] at this
            exact this
          rw [Set.mem_setOf_eq] at this
          exact this.2
  · -- ケース2: x ≠ u のとき，erase の等式からそのまま同値
    have hx_on_erases :
        (x ∈ A.1.erase u) ↔ (x ∈ B.1.erase u) := by
      constructor <;> intro hx' <;> simpa [h] using hx'
    -- x ≠ u なので，`erase u` で x の所属はそのまま
    simpa [Finset.mem_erase, hx] using hx_on_erases

--4番
@[simp] lemma sets_traceAt_iff (F : SetFamily α) (u : α) {B : Finset α} : (traceAt u F).sets B ↔ ∃ A, F.sets A ∧ B = A.erase u := by
  rfl

/-- トレース後のエッジ集合は，元のエッジ集合に `erase u` を施した像と一致。
`parallel` はここでは不要（像集合の同一性）。 -/
lemma edgeFinset_trace_eq_image_erase_of_parallel
    (F : SetFamily α) {u v : α}
    (huv : F.Parallel u v) (hne : u ≠ v) :
    (traceAt u F).edgeFinset = F.edgeFinset.image (fun A => A.erase u) := by
  classical
  -- メンバーシップ同値で両包含を示す
  apply Finset.ext
  intro B
  constructor
  · -- 「→」: B がトレース側のエッジなら，元の何か A の erase になっている
    intro hB
    have hBsets : (traceAt u F).sets B :=
      (mem_edgeFinset_iff_sets (F := traceAt u F) (A := B)).1 hB
    -- トレースの特徴付け：B = A.erase u
    rcases (sets_traceAt_iff (F := F) (u := u) (B := B)).1 hBsets with ⟨A, hA, rfl⟩
    -- 画像の元として書き換え
    exact Finset.mem_image.mpr
      ⟨A, (mem_edgeFinset_iff_sets (F := F) (A := A)).2 hA, rfl⟩
  · -- 「←」: 右辺の像の元なら，トレース側のエッジ
    intro hB
    rcases Finset.mem_image.mp hB with ⟨A, hAedge, hBdef⟩
    have hAsets : F.sets A :=
      (mem_edgeFinset_iff_sets (F := F) (A := A)).1 hAedge
    -- A ∈ F.sets なら (A.erase u) はトレース側のエッジ
    have : (traceAt u F).sets (A.erase u) :=
      (sets_traceAt_iff (F := F) (u := u) (B := A.erase u)).2 ⟨A, hAsets, rfl⟩
    -- edgeFinset への持ち上げ
    simpa [hBdef] using
      (mem_edgeFinset_iff_sets (F := traceAt u F) (A := A.erase u)).2 this

--ChatGPTの5番 どうも証明には必要なかった。
/- 上の二つから，全単射（存在）を明示しておく版。 -/
/-
lemma edges_bijection_exists_of_parallel
    (F : SetFamily α) {u v : α}
    (huv : F.Parallel u v) (hne : u ≠ v) :
    ∃ e : {A // A ∈ F.edgeFinset} ≃ {B // B ∈ (traceAt u F).edgeFinset},
      ∀ A, (e A).1 = (A.1.erase u) := by
  sorry
-/

--ChatGPTの6番
lemma numHyperedges_preserved_of_parallel
    (F : SetFamily α) {u v : α}
    (huv : F.Parallel u v) (hne : u ≠ v) :
    (traceAt u F).numHyperedges = F.numHyperedges := by
  classical
  -- ④: トレース後のエッジは `erase u` の像
  have himg :
      (traceAt u F).edgeFinset
        = F.edgeFinset.image (fun A => A.erase u) :=
    edgeFinset_trace_eq_image_erase_of_parallel (F := F) (u := u) (v := v) huv hne

  -- ③: `A ↦ A.erase u` は `F.edgeFinset` 上で単射
  have hinj_on :
      ∀ A ∈ F.edgeFinset, ∀ B ∈ F.edgeFinset,
        (A.erase u) = (B.erase u) → A = B := by
    intro A hA B hB hEq
    -- サブタイプ版の単射から引き戻す
    have hsub_inj :=
      @erase_on_edges_injective_of_parallel α _ F u v huv hne
    unfold Function.Injective at hsub_inj
    simp_all only [Parallel, ne_eq, mem_edgeFinset, Subtype.forall, Subtype.mk.injEq, and_imp, subset_refl]
    apply hsub_inj
    · simp_all only [subset_refl]
    · simp_all only [subset_refl]
    · simp_all only [subset_refl]
    · simp_all only [subset_refl]
    · simp_all only [subset_refl]

  -- `image` のカードは InjOn なら元と等しい
  have hcard_image :
      (F.edgeFinset.image (fun A => A.erase u)).card
        = F.edgeFinset.card := by
    -- お手元の補題名に応じて差し替えてください：
    -- 例: `Finset.card_image_iff.mpr hinj_on`
    --     または `Finset.card_image_eq_iff.mpr hinj_on`
    --     あるいは `by
    --        refine Finset.card_image_of_injOn ?_;
    --        exact hinj_on`
    -- ここでは `card_image_iff` 風の名前を仮定します。
    simpa using Finset.card_image_iff.mpr hinj_on

  -- 仕上げ：カード等式に書き換え
  simp [numHyperedges, himg, hcard_image]

lemma sum_edge_sizes_split_by_u
    (F : SetFamily α) (u : α) :
    (∑ A ∈ F.edgeFinset, A.card)
      = (∑ A ∈ F.edgeFinset, (A.erase u).card) + F.degree u := by
  classical
  have hpt :
      ∀ A : Finset α,
        A.card = (A.erase u).card + (if u ∈ A then 1 else 0) := by
    intro A; by_cases huA : u ∈ A
    · -- u を含むとき
      -- (A.erase u).card = A.card - 1 を使えば OK
      have : (A.erase u).card = A.card - 1 := by
        simp [huA]

      -- 自然数なので `A.card - 1 + 1 = A.card`
      have hpos : 0 < A.card := by
        exact Finset.card_pos.mpr ⟨u, huA⟩
      -- `Nat.succ_pred_eq_of_pos` を使う形に整える
      -- ここは `simp` で流せることが多いです
      simpa [this, huA] using by
        have := this
        -- 同値変形：A.card = (A.card - 1) + 1
        exact (by
          have := Nat.succ_pred_eq_of_pos hpos
          -- `A.card = Nat.succ (A.card - 1)`
          -- よって `(A.card - 1) + 1 = A.card`
          simpa [Nat.succ_eq_add_one, Nat.add_comm] using this.symm)
    · -- u を含まないとき
      -- (A.erase u).card = A.card, indicator は 0
      simp [huA]
  -- 点ごとの恒等式を和に移す
  have hsum :
      (∑ A ∈ F.edgeFinset, A.card)
        = ∑ A ∈ F.edgeFinset, ((A.erase u).card + (if u ∈ A then 1 else 0)) := by
    refine Finset.sum_congr rfl ?_
    intro A hA; simp [hpt A]
  -- 右辺を分配
  rw [hsum]

  simp [Finset.sum_add_distrib]
  exact Eq.symm (SetFamily.degree_eq_card_filter F u)

/-- 上をトレースのエッジ集合で書き直した版（parallel を使って像に置換）。 -/
lemma sum_edge_sizes_trace_version_of_parallel
    (F : SetFamily α) {u v : α}
    (huv : F.Parallel u v) (hne : u ≠ v) :
    (∑ A ∈ F.edgeFinset, A.card)
      = (∑ B ∈ (traceAt u F).edgeFinset, B.card) + F.degree u := by
  classical
  -- まず、parallel 不要の分解補題
  have hsplit := sum_edge_sizes_split_by_u (F := F) u
  -- ④: トレース後のエッジは `erase u` の像
  have himg :
      (traceAt u F).edgeFinset
        = F.edgeFinset.image (fun A => A.erase u) :=
    edgeFinset_trace_eq_image_erase_of_parallel (F := F) (u := u) (v := v) huv hne
  -- ③ から：`A ↦ A.erase u` が `F.edgeFinset` 上で InjOn
  have hinj_on :
      ∀ A ∈ F.edgeFinset, ∀ B ∈ F.edgeFinset,
        (A.erase u) = (B.erase u) → A = B := by
    intro A hA B hB hEq
    have hsub_inj :=
      @erase_on_edges_injective_of_parallel α _ F u v huv hne
    unfold Function.Injective at hsub_inj
    simp_all only [Parallel, ne_eq, mem_edgeFinset, Subtype.forall, Subtype.mk.injEq, and_imp, subset_refl]
    apply hsub_inj
    · simp_all only [subset_refl]
    · simp_all only [subset_refl]
    · simp_all only [subset_refl]
    · simp_all only [subset_refl]
    · simp_all only [subset_refl]

  -- `sum_image` で `∑ (A.erase u).card` を像側の和へ
  have hsum_image :
      (∑ A ∈ F.edgeFinset, (A.erase u).card)
        = (∑ B ∈ (F.edgeFinset.image (fun A => A.erase u)), B.card) := by
    -- `sum_image` は像側=元側 の向きなので `symm` を付けない形で書く
    -- sum_image : (InjOn f s) → ∑ x in s.image f, g x = ∑ x in s, g (f x)
    -- ここでは g := Finset.card
    exact Eq.symm (Finset.sum_image hinj_on)

  -- 仕上げ：置換して等式完成
  calc
    (∑ A ∈ F.edgeFinset, A.card)
        = (∑ A ∈ F.edgeFinset, (A.erase u).card) + F.degree u := hsplit
    _   = (∑ B ∈ (F.edgeFinset.image (fun A => A.erase u)), B.card) + F.degree u := by
            simp [hsum_image]
    _   = (∑ B ∈ (traceAt u F).edgeFinset, B.card) + F.degree u := by
            simp [himg]


/-- 目標：NDS の等式（版B）。
  `NDS(F) = 2 * Σ|A| - |E(F)| * |ground|` を使う。
  仮定：`u` は ground に属し，`v` は `u` の parallel パートナー。 -/
lemma NDS_eq_of_parallel
    (F : SetFamily α) {u v : α}
    (huv : F.Parallel u v) (hne : u ≠ v) (hu : u ∈ F.ground)
    (hNDSDef :
      F.NDS
        = 2 * (∑ A ∈ F.edgeFinset, (A.card : Int))
          - (F.numHyperedges : Int) * (F.ground.card : Int))
    (hNDSDefTrace :
      (traceAt u F).NDS
        = 2 * (∑ B ∈ (traceAt u F).edgeFinset, (B.card : Int))
          - ((traceAt u F).numHyperedges : Int) * ((traceAt u F).ground.card : Int)) :
    F.NDS = (traceAt u F).NDS + 2 * (F.degree u : Int) - (F.numHyperedges : Int) := by
classical
  -- ⑧（Nat）を Int に持ち上げる：
  have hsum_nat :
      (∑ A ∈ F.edgeFinset, A.card)
        = (∑ B ∈ (traceAt u F).edgeFinset, B.card) + F.degree u :=
    sum_edge_sizes_trace_version_of_parallel (F := F) (u := u) (v := v) huv hne
  have hsum_int :
      (∑ A ∈ F.edgeFinset, (A.card : Int))
        = (∑ B ∈ (traceAt u F).edgeFinset, (B.card : Int))
          + (F.degree u : Int) := by
    -- Nat 等式を Int にキャスト
    have := congrArg (fun n : ℕ => (n : Int)) hsum_nat
    -- 和・加法の `Nat.cast` を展開
    simpa [Nat.cast_sum, Nat.cast_add] using this

  -- ⑥：辺数保存（Nat → Int）
  have hE_nat :
      (traceAt u F).numHyperedges = F.numHyperedges :=
    numHyperedges_preserved_of_parallel (F := F) (u := u) (v := v) huv hne
  have hE_int :
      ((traceAt u F).numHyperedges : Int) = (F.numHyperedges : Int) := by
    simpa using congrArg (fun n : ℕ => (n : Int)) hE_nat

  -- ground のサイズ：`u ∈ ground` より `|V(trace)| = |V| - 1`
  have hV_nat :
      (traceAt u F).ground.card = F.ground.card - 1 :=
    ground_card_trace_of_mem (F := F) hu
  -- そこから `|V| - |V(trace)| = 1` の Int 版を作る
  have hV_pos : 0 < F.ground.card := Finset.card_pos.mpr ⟨u, hu⟩
  have hsucc :
      (traceAt u F).ground.card + 1 = F.ground.card := by
    -- `Nat.succ (F.ground.card - 1) = F.ground.card`
    -- と `hV_nat` からの置換
    simp
    let nc := (Nat.succ_pred_eq_of_pos hV_pos)
    simp_all only [Parallel, ne_eq, NDS_def, sub_left_inj, mul_eq_mul_left_iff, OfNat.ofNat_ne_zero, or_false,
    traceAt_ground, Finset.card_erase_of_mem, Nat.cast_pred]
    exact nc


  have hV_int_eq :
      (F.ground.card : Int) = ((traceAt u F).ground.card : Int) + 1 := by
    have := congrArg (fun n : ℕ => (n : Int)) hsucc
    simp
    exact id (Eq.symm this)


  -- 本体計算
  -- 版Bの定義で `NDS(F)` と `NDS(trace)` を展開してから整理
  calc
    F.NDS
        = 2 * (∑ A ∈ F.edgeFinset, (A.card : Int))
            - (F.numHyperedges : Int) * (F.ground.card : Int) := hNDSDef
    _   = 2 * ( (∑ B ∈ (traceAt u F).edgeFinset, (B.card : Int))
                + (F.degree u : Int))
            - ((traceAt u F).numHyperedges : Int) * (((traceAt u F).ground.card : Int) + 1) := by
            -- sums を ⑧ で置換、|E| と |V| を ⑥ と hV_int_eq で置換
            simp [hsum_int, hE_int, hV_int_eq]

    _   = (2 * (∑ B ∈ (traceAt u F).edgeFinset, (B.card : Int))
            - ((traceAt u F).numHyperedges : Int) * ((traceAt u F).ground.card : Int))
          + (2 * (F.degree u : Int) - ((traceAt u F).numHyperedges : Int)) := by
            -- 分配して `(a+b) - (c*(d+1)) = (2a - c*d) + (2b - c)`
            -- 詳細：`2*(X+D) = 2X + 2D`、`E*(G+1) = E*G + E`
            -- その後 `(x + y) - (p + q) = (x - p) + (y - q)`
            have : 2 * ((∑ B ∈ (traceAt u F).edgeFinset, (B.card : Int))
                        + (F.degree u : Int))
                    = 2 * (∑ B ∈ (traceAt u F).edgeFinset, (B.card : Int))
                      + 2 * (F.degree u : Int) := by
              simp [two_mul, mul_add, add_comm, add_assoc]
            have : ((traceAt u F).numHyperedges : Int)
                      * (((traceAt u F).ground.card : Int) + 1)
                    = ((traceAt u F).numHyperedges : Int)
                        * ((traceAt u F).ground.card : Int)
                      + ((traceAt u F).numHyperedges : Int) := by
              simp [mul_add, add_comm]
            -- まとめて変形
            -- `simp` で `sub_eq_add_neg` を使って並べ替える
            simp [two_mul, mul_add, add_comm, add_left_comm, add_assoc,
                   sub_eq_add_neg]
    _   = (traceAt u F).NDS + (2 * (F.degree u : Int) - (F.numHyperedges : Int)) := by
            -- 版Bの `trace` 定義へ戻す＋辺数は ⑥ で置換
            simp [ hE_int]
            dsimp [SetFamily.totalHyperedgeSize]
            exact Eq.symm (Nat.cast_sum (traceAt u F).edgeFinset Finset.card)
  exact add_sub_assoc' (traceAt u F).NDS (2 * ↑(F.degree u)) ↑F.numHyperedges

end Trace

end AvgRare

/- トレース後の「`B` がトレース族のメンバである」ことの便利な再表現。 -/
--lemma mem_traceAt_iff {x : α} {F : SetFamily α} {B : Finset α} :
--    (traceAt x F).sets B ↔ ∃ A, F.sets A ∧ B ⊆ A.erase x ∧ B ⊆ F.ground.erase x := by

/- 1点トレースの ground 包含（再掲）。 -/
/-
lemma subset_ground_of_mem_trace {x : α} {F : SetFamily α} {B : Finset α}
    (hB : (traceAt x F).sets B) :
    B ⊆ (traceAt x F).ground := by
  classical
  rcases (mem_traceAt_iff).1 hB with ⟨A, hA, hBsub, hBsubU⟩
  -- 定義どおり
  simpa using hBsubU
-/

/- 小補助：`A ⊆ F.ground` なら `A.erase x ⊆ F.ground.erase x`。 -/
/-
lemma erase_subset_erase_of_subset {x : α} {F : SetFamily α} {A : Finset α}
    (hA : A ⊆ F.ground) :
    A.erase x ⊆ F.ground.erase x := by
  intro a ha
  have : a ∈ A ∧ a ≠ x := by
    -- `Finset.mem_erase` の逆向き
    simp_all only [Finset.mem_erase, ne_eq, not_false_eq_true, and_self]
  have haA : a ∈ A := this.1
  have hne : a ≠ x := this.2
  have haU : a ∈ F.ground := hA haA
  -- `mem_erase` の順向き
  exact by
    -- a ∈ ground ∧ a ≠ x から a ∈ ground.erase x
    have : a ∈ F.ground.erase x := by
      -- `Finset.mem_erase` ⇔ (a ≠ x ∧ a ∈ ground)
      have := (show a ≠ x ∧ a ∈ F.ground from And.intro hne haU)
      -- 書き換え
      simpa [Finset.mem_erase, And.comm] using this
    exact this
-/

/-
noncomputable def traceErase (x : α) (F : SetFamily α) : SetFamily α := by
  classical
  refine
  { ground := F.ground.erase x
    , sets := fun B => ∃ A, F.sets A ∧ B = A.erase x
    , decSets := Classical.decPred _
    , inc_ground := ?_ }
  intro B hB
  rcases hB with ⟨A, hA, rfl⟩
  -- A ⊆ ground → A.erase x ⊆ ground.erase x
  exact (erase_subset_erase_of_subset (F := F) (A := A) (F.inc_ground hA))
-/

/- 像だけ版の edge 列挙：`edgeFinset = image (erase x)`。 -/
/-
lemma edgeFinset_traceErase (x : α) (F : SetFamily α) :
    (traceErase x F).edgeFinset
      = F.edgeFinset.image (fun A => A.erase x) := by
  classical
  -- ここは後で埋める（`mem_edgeFinset_iff` と `Finset.image` の往復）
  sorry
-/


/-
必要になったときに拡張しやすいよう、Trace とは独立の小道具をここに置いておけます
（例えば Equiv による ground の付け替え等）。現状は最小限に留めています。
-/


/-
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import AvgRare.Basics.SetFamily
import AvgRare.SPO.FuncSetup

universe u

namespace AvgRare
namespace Basics
namespace Trace
open scoped BigOperators

variable {α : Type u} [DecidableEq α]

/-- `A : Finset α` を同値関係 `E` の商に写した像。 -/
noncomputable def imageQuot (E : Setoid α) (A : Finset α) : Finset (Quot E) := by
  classical
  exact A.image (fun a => Quot.mk _ a)

@[simp]
lemma mem_imageQuot {E : Setoid α} {A : Finset α} {q : Quot E} :
    q ∈ imageQuot E A ↔ ∃ a ∈ A, Quot.mk _ a = q := by
  classical
  simp [imageQuot]

lemma imageQuot_mono {E : Setoid α} {A B : Finset α} (h : A ⊆ B) :
    imageQuot E A ⊆ imageQuot E B := by
  classical
  intro q hq
  rcases (mem_imageQuot (E:=E) (A:=A)).1 hq with ⟨a, haA, rfl⟩
  exact (mem_imageQuot (E:=E) (A:=B)).2 ⟨a, h haA, rfl⟩

--section
variable (E : Setoid α)
-- ★ ここで型レベルにインスタンスを用意しておく
noncomputable local instance : DecidableEq (Quot E) := Classical.decEq _

/-- `trace E F`：各超辺の商像を取り、その **下閉包** で得た集合族。 -/
noncomputable def trace (E : Setoid α) (F : SetFamily α) : SetFamily (Quot E) := by
  classical
  refine
  { ground := imageQuot E F.ground
    sets   := fun B => ∃ A : Finset α, F.sets A ∧ B ⊆ imageQuot E A
    decSets := Classical.decPred _
    inc_ground := ?_ }

  intro B hB
  rcases hB with ⟨A, hA, hsub⟩
  have hAg : A ⊆ F.ground := F.inc_ground hA
  have him : imageQuot E A ⊆ imageQuot E F.ground :=
    imageQuot_mono (E:=E) hAg
  exact hsub.trans him

/-- E ≤ E' ：E が E' より細かい（E の同値は E' の同値でもある） -/
def refines (E E' : Setoid α) : Prop :=
  ∀ ⦃a b : α⦄, E.r a b → E'.r a b

/-- refinement から商への写像 `Quot E → Quot E'` -/
noncomputable def liftQuot {E E' : Setoid α} (h : refines E E') :
  Quot E → Quot E' :=
  Quot.map (fun x => x) (by intro a b hab; exact h hab)

@[simp] lemma liftQuot_mk {E E' : Setoid α} (h : refines E E') (a : α) :
  liftQuot (E:=E) (E':=E') h (Quot.mk _ a) = Quot.mk _ a := rfl

/-- `imageQuot` を粗い同値に取り直すと、持ち上げ写像で包含が成り立つ。 -/
lemma imageQuot_mono_under_refines
  {E E' : Setoid α} (h : refines E E') (A : Finset α) :
  (A.image (fun a => Quot.mk E a)).image (liftQuot (E:=E) (E':=E') h)
    ⊆ A.image (fun a => Quot.mk E' a) := by
  classical
  intro q hq
  rcases Finset.mem_image.1 hq with ⟨q0, hq0, rfl⟩
  rcases Finset.mem_image.1 hq0 with ⟨a, haA, rfl⟩
  -- 右辺に同じ代表 a で入る
  exact Finset.mem_image.2 ⟨a, haA, rfl⟩

/-- **trace の単調性（Setoid を粗くすると大きくなる）**
`E ≤ E'`（E が細かい）なら、`trace E F` の各超辺像を `Quot E → Quot E'` に移せば `trace E' F` の超辺に含まれる。 -/
lemma trace_mono_in_setoid
  (E E' : Setoid α) (F : SetFamily α) (h : refines E E') :
  ∀ {B : Finset (Quot E)},
    (trace E F).sets B →
    ∃ B' : Finset (Quot E'),
      (trace E' F).sets B' ∧
      B.image (liftQuot (E:=E) (E':=E') h) ⊆ B' := by
  classical
  intro B hB
  -- 定義展開：B ⊆ imageQuot E A
  rcases hB with ⟨A, hAsets, hBsub⟩
  refine ⟨A.image (fun a => Quot.mk E' a), ?_, ?_⟩
  · -- `trace E' F` のメンバー
    refine ⟨A, hAsets, ?_⟩
    -- `imageQuot E' A` に対しては自明な包含
    intro q hq
    exact hq
  · -- B を `liftQuot` で写すと、`imageQuot E' A` に入る
    -- すなわち B.image (liftQuot h) ⊆ (imageQuot E' A)
    -- まず B ⊆ imageQuot E A を使って、像に押し出す
    intro q hq
    rcases Finset.mem_image.1 hq with ⟨q0, hq0, rfl⟩
    have : q0 ∈ A.image (fun a => Quot.mk E a) := hBsub hq0
    -- ここで `imageQuot_mono_under_refines` で E→E' に移す
    have step :=
      imageQuot_mono_under_refines (E:=E) (E':=E') h (A := A)
    -- step : (imageQuot E A).image (liftQuot h) ⊆ imageQuot E' A
    exact step (by
      -- q0 を像に入れてから lift して得る要素は右辺に含まれる
      exact Finset.mem_image.2 ⟨q0, this, rfl⟩)


noncomputable def restrict {α} [DecidableEq α]
    (F : SetFamily α) (U : Finset α) : SetFamily α := by
  classical
  refine
  { ground := U
    , sets := fun B => ∃ A : Finset α, F.sets A ∧ B ⊆ A ∧ B ⊆ U
    , decSets := Classical.decPred _
    , inc_ground := ?_ }
  intro B hB
  rcases hB with ⟨A, hA, hBsubA, hBsubU⟩
  exact hBsubU

@[simp] lemma mem_restrict_iff {α} [DecidableEq α]
    {F : SetFamily α} {U B : Finset α} :
    (restrict F U).sets B ↔ ∃ A, F.sets A ∧ B ⊆ A ∧ B ⊆ U := Iff.rfl

lemma isOrderIdeal_erase_on_restrict
  {α} [DecidableEq α] (S : FuncSetup α)
  (A : Finset S.Elem) (hA : S.isOrderIdeal A) (u : S.Elem) :
  (S.restrict (S.V.erase u)).isOrderIdeal (A.erase u) := by
  intro x y hy hx
  -- `x y : (S.restrict ...).Elem` だと思って使えるように、必要なら `Subtype` の `val` 展開
  -- `hy : y ≤ x` は制限順序の比較。基の順序の比較に戻してから `hA` に投げる。
  rcases Finset.mem_erase.mp hx with ⟨hx_ne, hxA⟩
  have hyA : (y : S.Elem) ∈ A := hA (by simpa using hy) hxA
  -- 結論は `x ∈ A.erase u`：
  apply Finset.mem_erase.mpr
  constructor
  · -- x ≠ u
    -- x = u なら u ≤ y だが y は `A` に居るので、`A.erase u` の仮定と矛盾、の形で弾く
    intro hxu; subst hxu
    -- `u ≤ y` だが `y ∈ A` なので `u ∈ A`（下方閉）。しかし `hx` は x≠u を言っていた…という整理。
    -- ここは環境の順序補題（反射・推移）に合わせて書き分け。
    have : (u : S.Elem) ∈ A := hA (by simpa using hy) hxA
    exact hx_ne this.symm
  · -- x ∈ A
    exact hA (by simpa using hy) hxA


/-- 記法：`𝓕 ↘ U` を `restrict 𝓕 U` の糖衣として定義。 -/
notation:90 F "↘" U => AvgRare.Basics.Trace.restrict F U

@[simp] lemma imageQuot_eq_image {E : Setoid α} (A : Finset α) :
  imageQuot E A = A.image (fun a => Quot.mk _ a) := rfl

@[simp] lemma mem_imageQuot_iff {E : Setoid α} {A : Finset α} {q : Quot E} :
  q ∈ imageQuot E A ↔ ∃ a ∈ A, Quot.mk _ a = q :=
by classical simp [imageQuot]

/-- 画像の画像：`imageQuot E A` の各要素を恒等的に lift する形の `image` は `imageQuot` の交換で吸収できる -/
lemma image_imageQuot_lift {E E' : Setoid α} (h : refines E E') (A : Finset α) :
  (imageQuot E A).image (liftQuot (E:=E) (E':=E') h)
    ⊆ imageQuot E' A := by
  classical
  -- 既存の `imageQuot_mono_under_refines` の言い換え
  have := imageQuot_mono_under_refines (E:=E) (E':=E') h (A:=A)
  -- 使っている定義の向きを合わせるだけ
  simpa [imageQuot_eq_image] using this

end Trace
end Basics
end AvgRare


-/
