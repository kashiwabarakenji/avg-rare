import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import LeanCopilot

universe u

open scoped BigOperators

namespace AvgRare

/-- 有限台集合 `ground` と，その部分集合族 `sets`（判定述語＋可判定性） -/
@[ext]
structure SetFamily (α : Type u) [DecidableEq α] where
  ground    : Finset α
  sets      : Finset α → Prop
  decSets   : DecidablePred sets
  inc_ground :
    ∀ {s : Finset α}, sets s → s ⊆ ground

attribute [instance] SetFamily.decSets

namespace SetFamily

variable {α : Type u} [DecidableEq α]

noncomputable def reindexEmbedding {α β} [DecidableEq α] [DecidableEq β]
  (ι : β ↪ α) (F : SetFamily β) : SetFamily α :=
{ ground := F.ground.map ι,
  sets   := fun B => ∃ A, F.sets A ∧ B = A.image ι,
  decSets := Classical.decPred _,     -- classical で ok
  inc_ground := by
    classical
    intro B hB b hb
    rcases hB with ⟨A, hA, rfl⟩
    rcases Finset.mem_image.1 hb with ⟨a, haA, rfl⟩
    have : a ∈ F.ground := F.inc_ground hA haA
    exact Finset.mem_map.2 ⟨a, this, rfl⟩ }

/-- 族の全メンバー（有限集合の有限集合） -/
noncomputable def hyperedges (F : SetFamily α) : Finset (Finset α) :=
  F.ground.powerset.filter F.sets

/-- 超辺の個数（Nat） -/
noncomputable def number_of_hyperedgesNat (F : SetFamily α) : Nat :=
  F.hyperedges.card

/-- 頂点の次数（Nat）：その頂点を含む超辺数 -/
noncomputable def degreeNat (F : SetFamily α) (v : α) : Nat :=
  (F.hyperedges.filter (fun s => v ∈ s)).card

/-- 超辺サイズ総和（Nat）：`∑_{A∈F} |A|` -/
noncomputable def total_size_of_hyperedgesNat (F : SetFamily α) : Nat :=
  F.hyperedges.sum Finset.card

/-- 論文で使う整数スケール版：`2*deg(v) - |I|` -/
noncomputable def normalized_degree (F : SetFamily α) (v : α) : Int :=
  (2 : Int) * (F.degreeNat v : Int) - (F.number_of_hyperedgesNat : Int)

/-- 論文で使う整数スケール版：`2*Σ|A| - |I|*|ground|` -/
noncomputable def normalized_degree_sum (F : SetFamily α) : Int :=
  (2 : Int) * (F.total_size_of_hyperedgesNat : Int)
  - (F.number_of_hyperedgesNat : Int) * (F.ground.card : Int)

/-- 頂点 v が rare か（`normalized_degree ≤ 0`） -/
def is_rare (F : SetFamily α) (v : α) : Prop :=
  F.normalized_degree v ≤ 0

/-- 二重計数：`ground` 上の次数総和 = 超辺サイズ総和（Nat 版） -/
lemma degree_sum_eq_total_size_of_hyperedgesNat (F : SetFamily α) :
    (∑ v ∈ F.ground, F.degreeNat v) = F.total_size_of_hyperedgesNat := by
  classical
  -- 記号短縮
  set V := F.ground
  set H := F.hyperedges
  -- LHS を「if で数える形」に展開

  have hdeg :
      ∀ v ∈ V,
        (F.degreeNat v)
          = ∑ A ∈ H, (if v ∈ A then (1 : Nat) else 0) := by
    intro v hv
    -- `degreeNat v = card (H.filter (· ∋ v))` を if-和へ
    have := by
      -- `card_filter` を ∑ if に置換する定番形
      -- (H.filter p).card = ∑ A∈H, if p A then 1 else 0
      simpa using (Finset.card_filter (s := H) (p := fun A => v ∈ A))
    -- 上の `this : (H.filter (fun A => v ∈ A)).card = ...`
    -- を そのまま使えば OK
    simp [SetFamily.degreeNat, H]


  -- RHS（Σ|A|）を「if で数える形」に展開
  have hcard :
      ∀ {A}, A ∈ H → A.card = ∑ v ∈ V, (if v ∈ A then 1 else 0) := by
    intro A hA
    -- A ⊆ V を得る（H は V の powerset の filter なので）
    have hA_subV : A ⊆ V := by
      have : A ∈ V.powerset := (Finset.mem_filter.mp hA).1
      simpa [Finset.mem_powerset] using this
    -- `A.card` を V 上のインジケータ和に持ち上げる
    -- `card = ∑_{v∈A} 1` を，`A ⊆ V` を使って `∑_{v∈V} if v∈A then 1 else 0` に等しいへ
    calc
      A.card = (Finset.filter (fun v => v ∈ A) V).card := by
        -- A⊆V なので V を A で filter するとちょうど A
        -- （要素同値を示してから card を取る）
        have : V.filter (fun v => v ∈ A) = A := by
          ext v
          constructor
          · intro hv
            exact (Finset.mem_filter.mp hv).2
          · intro hv
            exact Finset.mem_filter.mpr ⟨hA_subV hv, hv⟩
        simp [this]
      _ = ∑ v ∈ V, (if v ∈ A then 1 else 0) := by
        -- `card_filter` の Nat 版（定番）
        simpa using (Finset.card_filter (s := V) (p := fun v => v ∈ A))

  -- 以上を使って Fubini（和の交換）
  calc
    (∑ v ∈ V, F.degreeNat v)
        = ∑ v ∈ V, ∑ A ∈ H, (if v ∈ A then 1 else 0) := by
          refine Finset.sum_congr rfl ?_
          intro v hv; simpa using hdeg v hv
    _   = ∑ A ∈ H, ∑ v ∈ V, (if v ∈ A then 1 else 0) := by
          exact Finset.sum_comm
    _   = ∑ A ∈ H, A.card := by
          refine Finset.sum_congr rfl ?_
          intro A hA;
          simp [hcard hA]
    _   = F.total_size_of_hyperedgesNat := rfl

/-- 各頂点の整数版 normalized_degree の総和 = 整数版 NDS -/
lemma sum_normalized_degree_eq_nds (F : SetFamily α) :
    (∑ v ∈ F.ground, F.normalized_degree v) = F.normalized_degree_sum := by
  classical
  -- Nat → Int：∑deg = ∑|A|
  have hNat : (∑ v ∈ F.ground, F.degreeNat v)
                = F.total_size_of_hyperedgesNat :=
    degree_sum_eq_total_size_of_hyperedgesNat (F := F)
  have hDC :
      (∑ v ∈ F.ground, (F.degreeNat v : Int))
        = (F.total_size_of_hyperedgesNat : Int) := by
    -- cast(∑ Nat) → ∑ cast(Nat)
    have := congrArg (fun n : Nat => (n : Int)) hNat
    -- 左辺 cast を ∑ に配る
    simpa [Nat.cast_sum] using this

  -- 以降は代数整理だけ
  unfold normalized_degree normalized_degree_sum
  have h1 :
      (∑ v ∈ F.ground, (2 : Int) * (F.degreeNat v : Int))
        = (2 : Int) * (∑ v ∈ F.ground, (F.degreeNat v : Int)) := by
    simp [Finset.mul_sum]
  have h2 :
      (∑ v ∈ F.ground, (F.number_of_hyperedgesNat : Int))
        = (F.ground.card : Int) * (F.number_of_hyperedgesNat : Int) := by
    simp [Finset.sum_const]

  calc
    (∑ v ∈ F.ground, ((2 : Int) * (F.degreeNat v : Int) - (F.number_of_hyperedgesNat : Int)))
        = (∑ v ∈ F.ground, (2 : Int) * (F.degreeNat v : Int))
          - (∑ v ∈ F.ground, (F.number_of_hyperedgesNat : Int)) := by
            simp [Finset.sum_sub_distrib]
    _   = (2 : Int) * (∑ v ∈ F.ground, (F.degreeNat v : Int))
          - (F.ground.card : Int) * (F.number_of_hyperedgesNat : Int) := by
            simp [h1, h2]
    _   = (2 : Int) * (F.total_size_of_hyperedgesNat : Int)
          - (F.number_of_hyperedgesNat : Int) * (F.ground.card : Int) := by
            -- 二重計数を適用
            simp [hDC, mul_comm]

/-- `F` による parallel（集合族の同値）：
  すべての超辺 `A` について `x ∈ A ↔ y ∈ A` が成り立つ。 -/
noncomputable def parallelSetoid (F : SetFamily α) : Setoid α :=
{ r := fun x y => ∀ {A : Finset α}, F.sets A → (x ∈ A ↔ y ∈ A),
  iseqv :=
  ⟨
    -- refl
    by
      intro x
      intro A hA
      exact Iff.rfl,
    -- symm
    by
      intro x y hxy
      intro A hA
      exact (hxy (A := A) hA).symm,
    -- trans
    by
      intro x y z hxy hyz
      intro A hA
      exact Iff.trans (hxy (A := A) hA) (hyz (A := A) hA)
  ⟩
}

@[simp] lemma parallelSetoid_r_iff
    {F : SetFamily α} {x y : α} :
    (parallelSetoid F).r x y
      ↔ (∀ {A : Finset α}, F.sets A → (x ∈ A ↔ y ∈ A)) :=
Iff.rfl


--variable {α : Type u} [DecidableEq α]

/-- 並行（parallel）：同じ超辺にちょうど同じ仕方で現れる。 -/
def parallel (F : SetFamily α) (x y : α) : Prop :=
  ∀ {A : Finset α}, F.sets A → (x ∈ A ↔ y ∈ A)

lemma parallel_refl (F : SetFamily α) (x : α) : F.parallel x x := by
  intro A hA; constructor <;> intro hx <;> exact hx

lemma parallel_symm {F : SetFamily α} {x y : α} :
    F.parallel x y → F.parallel y x := by
  intro h A hA; have := h (A := A) hA; exact Iff.symm this

lemma parallel_trans {F : SetFamily α} {x y z : α} :
    F.parallel x y → F.parallel y z → F.parallel x z := by
  intro hxy hyz A hA
  have hx := hxy (A := A) hA
  have hz := hyz (A := A) hA
  exact Iff.trans hx hz

/-- 並行なら次数は等しい（Nat 版）。 -/
lemma parallel_degreeNat_eq {F : SetFamily α} {x y : α}
    (h : F.parallel x y) :
    F.degreeNat x = F.degreeNat y := by
  classical
  -- degreeNat は「hyperedges 上で x∈A を満たす A の個数」
  unfold SetFamily.degreeNat
  -- H の要素なら sets が成り立つ（parallel の適用に使う）
  have hsets_of_mem : ∀ {A : Finset α}, A ∈ F.hyperedges → F.sets A := by
    intro A hA
    exact (Finset.mem_filter.mp hA).2

  -- フィルタされた Finset が一致することを示す
  have hfilter :
      F.hyperedges.filter (fun A => x ∈ A)
        = F.hyperedges.filter (fun A => y ∈ A) := by
    ext A
    constructor
    · intro hAx
      rcases Finset.mem_filter.mp hAx with ⟨hAH, hxA⟩
      -- parallel：x∈A ↔ y∈A （A が hyperedge なので sets A）
      have hxy : (x ∈ A ↔ y ∈ A) := h (A := A) (hsets_of_mem hAH)
      exact Finset.mem_filter.mpr ⟨hAH, (Iff.mp hxy) hxA⟩
    · intro hAy
      rcases Finset.mem_filter.mp hAy with ⟨hAH, hyA⟩
      have hxy : (x ∈ A ↔ y ∈ A) := h (A := A) (hsets_of_mem hAH)
      exact Finset.mem_filter.mpr ⟨hAH, (Iff.mpr hxy) hyA⟩

  -- 同じ Finset なので card が等しい
  simp [hfilter]

/-- 1 点トレース（u を消す）：`A` を `A.erase u` に写す像を取った集合族。 -/
noncomputable def traceErase (F : SetFamily α) (u : α) : SetFamily α := by
  classical
  refine
  { ground := F.ground.erase u
    , sets := fun B => ∃ A : Finset α, F.sets A ∧ B = A.erase u
    , decSets := Classical.decPred _
    , inc_ground := ?_ }
  -- `B = A.erase u` かつ `A ⊆ F.ground` から `B ⊆ F.ground.erase u`
  intro B hB
  rcases hB with ⟨A, hAsets, rfl⟩
  intro x hx
  -- x ∈ A.erase u ⇒ x ≠ u ∧ x ∈ A
  have hx_ne : x ≠ u := (Finset.mem_erase.mp hx).1
  have hxA  : x ∈ A := (Finset.mem_erase.mp hx).2
  -- A ⊆ ground
  have hAg : A ⊆ F.ground := F.inc_ground hAsets
  have hxg : x ∈ F.ground := hAg hxA
  -- よって x ∈ ground.erase u
  exact Finset.mem_erase.mpr ⟨hx_ne, hxg⟩

@[simp] lemma mem_traceErase_sets_iff
    {F : SetFamily α} {u : α} {B : Finset α} :
    (traceErase F u).sets B ↔ ∃ A, F.sets A ∧ B = A.erase u := Iff.rfl

/-- `traceErase` の超辺は，元の超辺を `erase u` したものの像と一致。 -/
lemma hyperedges_traceErase_eq_image_erase
    (F : SetFamily α) (u : α) :
    (traceErase F u).hyperedges
      = F.hyperedges.image (fun A : Finset α => A.erase u) := by
  classical
  -- 等号を示すために両包含を出す
  apply (Finset.Subset.antisymm_iff).mpr
  constructor
  · -- ⊆ 方向
    intro B hB
    -- B は trace 側の hyperedge：B ⊆ ground.erase u ∧ ∃ A, sets A ∧ B = A.erase u
    have hPowAndSet :
        B ∈ (F.ground.erase u).powerset ∧ (∃ A, F.sets A ∧ B = A.erase u) :=
      Finset.mem_filter.mp hB
    rcases hPowAndSet.2 with ⟨A, hAsets, hBE⟩
    -- A は元の hyperedge
    have hAin : A ∈ F.hyperedges := by
      have hAg : A ⊆ F.ground := F.inc_ground hAsets
      have hPow : A ∈ F.ground.powerset := (Finset.mem_powerset.mpr hAg)
      exact Finset.mem_filter.mpr ⟨hPow, hAsets⟩
    -- B = A.erase u は像に入る
    subst hBE
    simp_all only [Finset.mem_powerset, Finset.mem_image]
    obtain ⟨left, right⟩ := hPowAndSet
    obtain ⟨w, h⟩ := right
    obtain ⟨left_1, right⟩ := h
    simp_all only
    use A
  · -- ⊇ 方向
    intro B hB
    -- B = A.erase u で A は元の hyperedge
    rcases Finset.mem_image.mp hB with ⟨A, hAin, rfl⟩
    have hAsets : F.sets A := (Finset.mem_filter.mp hAin).2
    have hAg    : A ⊆ F.ground := by
      have hPowA := (Finset.mem_filter.mp hAin).1
      exact (Finset.mem_powerset.mp hPowA)
    -- A.erase u ⊆ ground.erase u
    have hsub : A.erase u ⊆ F.ground.erase u := by
      intro x hx
      have hx_ne : x ≠ u := (Finset.mem_erase.mp hx).1
      have hxA  : x ∈ A := (Finset.mem_erase.mp hx).2
      have hxg  : x ∈ F.ground := hAg hxA
      exact Finset.mem_erase.mpr ⟨hx_ne, hxg⟩
    -- よって trace 側の hyperedge
    have hPow : A.erase u ∈ (F.ground.erase u).powerset :=
      Finset.mem_powerset.mpr hsub
    have hSet : (traceErase F u).sets (A.erase u) := ⟨A, hAsets, rfl⟩
    exact Finset.mem_filter.mpr ⟨hPow, hSet⟩

/-- `erase u` は，parallel な相棒 `v (≠ u)` があるとき，
    元 hyperedges 上で単射。 -/
lemma erase_inj_on_hyperedges_of_parallel
    {F : SetFamily α} {u v : α} (hpar : F.parallel u v) (hvne : v ≠ u) :
    Set.InjOn (fun A : Finset α => A.erase u) (↑F.hyperedges : Set (Finset α)) := by
  classical
  intro A hA B hB hEq
  -- Finset 側の membership に直す
  have hA' : A ∈ F.hyperedges := Finset.mem_coe.mp hA
  have hB' : B ∈ F.hyperedges := Finset.mem_coe.mp hB
  have hAsets : F.sets A := (Finset.mem_filter.mp hA').2
  have hBsets : F.sets B := (Finset.mem_filter.mp hB').2

  -- （補助）x ≠ u なら A→B/B→A への包含が成り立つ（erase の等式から）
  have AtoB_ne : ∀ x, x ≠ u → x ∈ A → x ∈ B := by
    intro x hxne hxA
    have hxAerase : x ∈ A.erase u := Finset.mem_erase.mpr ⟨hxne, hxA⟩
    have hxBerase : x ∈ B.erase u := by
      -- erase の等号から右辺へ
      exact (Eq.mp (congrArg (fun (S : Finset α) => x ∈ S) hEq) hxAerase)
    -- 消去して x∈B を得る
    exact (Finset.mem_erase.mp hxBerase).2

  have BtoA_ne : ∀ x, x ≠ u → x ∈ B → x ∈ A := by
    intro x hxne hxB
    have hxBerase : x ∈ B.erase u := Finset.mem_erase.mpr ⟨hxne, hxB⟩
    have hxAerase : x ∈ A.erase u := by
      -- 反対向き
      exact (Eq.mpr (congrArg (fun (S : Finset α) => x ∈ S) hEq) hxBerase)
    exact (Finset.mem_erase.mp hxAerase).2

  -- v ≠ u なので v の会員は A ↔ B
  have hvAtoB : v ∈ A → v ∈ B := AtoB_ne v hvne
  have hvBtoA : v ∈ B → v ∈ A := BtoA_ne v hvne
  have hviff : v ∈ A ↔ v ∈ B := ⟨hvAtoB, hvBtoA⟩

  -- parallel で u の会員を v に移して同値化：u∈A ↔ u∈B
  have huAtoB : u ∈ A → u ∈ B := by
    intro huA
    -- u∈A ⇒（parallel on A）⇒ v∈A ⇒（erase 等式＋v≠u）⇒ v∈B ⇒（parallel on B）⇒ u∈B
    have hvA : v ∈ A := (hpar (A := A) hAsets).mp huA
    have hvB : v ∈ B := hvAtoB hvA
    exact (hpar (A := B) hBsets).mpr hvB

  have huBtoA : u ∈ B → u ∈ A := by
    intro huB
    have hvB : v ∈ B := (hpar (A := B) hBsets).mp huB
    have hvA : v ∈ A := hvBtoA hvB
    exact (hpar (A := A) hAsets).mpr hvA

  have huiff : u ∈ A ↔ u ∈ B := ⟨huAtoB, huBtoA⟩

  -- 仕上げ：要素同値で ext
  apply Finset.ext
  intro x
  by_cases hx : x = u
  · -- x = u の場合は上で作った huiff を使う
    subst hx
    exact huiff
  · -- x ≠ u は erase 等式から直ちに同値
    exact ⟨AtoB_ne x hx, BtoA_ne x hx⟩



end SetFamily
end AvgRare

--attribute [simp] Finset.mem_attach
--attribute [simp] Quot.eq -- 代表の単純化に使う場合は危険でない範囲で

--@[simp] lemma imageQuot_ground (E : Setoid α) (F : SetFamily α) :
--  imageQuot E F.ground = (trace E F).ground := rfl
