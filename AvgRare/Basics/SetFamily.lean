import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import LeanCopilot

universe u

open scoped BigOperators

namespace AvgRare

/-
SetFamily.lean  —  基本集合族と計数まわり（NDSの土台）

このファイルは「有限台集合上の集合族」を述語 `sets : Finset α → Prop` で表し、
列挙・計数のための `edgeFinset` を（powerset からの filter で）構成します。
NDS 自体の定義は Ideals 側に置く想定ですが、基礎量
  * numHyperedges : ハイパーエッジ数
  * totalHyperedgeSize : サイズ総和
  * degree : 要素の出現回数
をここで定義しておきます。

注意:
- ここでは poset/ideal など順序に依存する概念は扱いません（Ideals 側へ）。
- トレースやリインデックスは Common/Trace 側へ。（必要ならここに移してOK）
-/

variable {α : Type u} [DecidableEq α]

/-- 有限台集合 `ground` 上の集合族。`sets A` は `A` が族のメンバである述語。
    計数・列挙のため、`edgeFinset` を powerset からの filter で構成できるように、
    `decSets`（可判別性）と `inc_ground`（台集合に含まれること）を仮定する。 -/
structure SetFamily (α : Type u) [DecidableEq α] where
  ground     : Finset α
  sets       : Finset α → Prop
  decSets    : DecidablePred sets
  inc_ground : ∀ {A : Finset α}, sets A → A ⊆ ground

namespace SetFamily

variable (F : SetFamily α)

attribute [simp] SetFamily.ground

instance instDecidablePred_sets (F : SetFamily α) : DecidablePred F.sets :=
  F.decSets


/-- 列挙用：族のメンバ全体を `powerset` から述語で filter して得る Finset。 -/
def edgeFinset : Finset (Finset α) :=
  F.ground.powerset.filter (fun A => decide (F.sets A))

/-- `edgeFinset` の要素は台集合に含まれる。 -/
lemma subset_ground_of_mem_edge {A : Finset α}
    (hA : A ∈ F.edgeFinset) : A ⊆ F.ground := by
  classical
  rcases Finset.mem_filter.mp hA with ⟨hPow, _⟩
  exact Finset.mem_powerset.mp hPow

/-- `edgeFinset` と述語 `sets` の一致。以後の計数で便利。 -/
lemma mem_edgeFinset_iff {A : Finset α} :
    A ∈ F.edgeFinset ↔ F.sets A := by
  classical
  constructor
  · intro h
    rcases Finset.mem_filter.mp h with ⟨hPow, hDec⟩
    -- decide (F.sets A) = true から F.sets A を回収
    simp_all only [Finset.mem_powerset, decide_eq_true_eq]
  · intro hA
    have hSub : A ⊆ F.ground := F.inc_ground hA
    have hPow : A ∈ F.ground.powerset := Finset.mem_powerset.mpr hSub
    have hDec : decide (F.sets A) = true := by simp_all only [Finset.mem_powerset, decide_true]

    exact Finset.mem_filter.mpr ⟨hPow, hDec⟩

/-- ハイパーエッジ数。 -/
def numHyperedges : Nat :=
  F.edgeFinset.card

/-- サイズ総和。 -/
def totalHyperedgeSize : Nat :=
  ∑ A ∈ F.edgeFinset, A.card

/-- 要素 `x` の次数（その要素を含むエッジの個数）。 -/
def degree (x : α) : Nat :=
  ∑ A ∈ F.edgeFinset, (if x ∈ A then (1 : Nat) else 0)

/-- `degree` を「含むエッジの個数」として書き直した版。 -/
lemma degree_eq_card_filter (x : α) :
    F.degree x = (F.edgeFinset.filter (fun A => x ∈ A)).card := by
  classical
  unfold degree
  -- `∑ (if p then 1 else 0)` を `∑ over s.filter p 1` に移す
  have h :
      (∑ A ∈ F.edgeFinset, (if x ∈ A then (1 : Nat) else 0))
        = (∑ A ∈ F.edgeFinset.filter (fun A => x ∈ A), (1 : Nat)) := by
    -- `sum_filter`：左辺 ↔ 右辺
    -- `simp` の向きの都合で `symm` を使う
    simp_all only [Finset.sum_boole, Nat.cast_id, Finset.sum_const, smul_eq_mul, mul_one]
  -- 右辺は定数 1 の総和＝個数
  simp_all only [Finset.sum_boole, Nat.cast_id, Finset.sum_const, smul_eq_mul, mul_one]

/-- `edgeFinset` は powerset の部分集合。 -/
lemma edgeFinset_subset_powerset :
    F.edgeFinset ⊆ F.ground.powerset := by
  classical
  intro A hA
  exact (Finset.mem_filter.mp hA).1

/-- `edgeFinset` 上のメンバは台集合に含まれる（便利な再掲）。 -/
lemma mem_edgeFinset_subset_ground {A : Finset α}
    (hA : A ∈ F.edgeFinset) : A ⊆ F.ground :=
  F.subset_ground_of_mem_edge hA

/-- 台集合の制限。ハイパーエッジは元のエッジの部分集合で、かつ `U` に含まれるもの。 -/
noncomputable def restrict (U : Finset α) : SetFamily α := by
  classical
  refine
  { ground := U
    , sets   := fun B => ∃ A : Finset α, F.sets A ∧ B ⊆ A ∧ B ⊆ U
    , decSets := Classical.decPred _
    , inc_ground := ?_ }
  intro B hB
  rcases hB with ⟨A, hA, hBsubA, hBsubU⟩
  exact hBsubU

@[simp] lemma mem_edgeFinset :
  A ∈ F.edgeFinset ↔ A ⊆ F.ground ∧ F.sets A := by
  classical
  constructor
  · intro h
    rcases Finset.mem_filter.mp h with ⟨hPow, hDec⟩
    have hSub : A ⊆ F.ground := Finset.mem_powerset.mp hPow
    have hSets : F.sets A := by
      -- ここは decide ↔ 命題の橋渡しを simp に任せる
      simpa using (show decide (F.sets A) = true from hDec)
    exact ⟨hSub, hSets⟩
  · intro h
    rcases h with ⟨hSub, hSets⟩
    have hPow : A ∈ F.ground.powerset := Finset.mem_powerset.mpr hSub
    have hDec : decide (F.sets A) = true := by simpa using hSets
    exact Finset.mem_filter.mpr ⟨hPow, hDec⟩

@[simp] lemma mem_edgeFinset_iff_sets : (A ∈ F.edgeFinset) ↔ F.sets A := by
  classical
  constructor
  · intro h; have := (F.mem_edgeFinset (A := A)).1 h; exact this.2
  · intro h; have : A ⊆ F.ground := F.inc_ground h
    exact (F.mem_edgeFinset (A := A)).2 ⟨this, h⟩

/-
-- （必要なら）リインデックス：`e : α ≃ β` で要素を書き換える。
-- poset 側の理想再インデックスで使いたい時に、コメントアウトを外してください。

def reindex {β : Type*} [DecidableEq β] (e : α ≃ β) : SetFamily β := by
  classical
  refine
  { ground := F.ground.image e
    , sets   := fun B => ∃ A : Finset α, F.sets A ∧ B = A.image e
    , decSets := Classical.decPred _
    , inc_ground := ?_ }
  intro B hB
  rcases hB with ⟨A, hA, rfl⟩
  intro b hb
  rcases Finset.mem_image.mp hb with ⟨a, haA, rfl⟩
  exact Finset.mem_image.mpr ⟨a, F.inc_ground hA haA, rfl⟩
-/

/-


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

section
universe v
variable {α : Type u} {β : Type v}
variable [DecidableEq α] [DecidableEq β]
/-- 要素型の同型 `e : α ≃ β` による集合族 `F` のリインデックス。
    ground は `image e`、メンバー述語は「元のメンバーの `image e` と等しいものの存在」で与える。 -/
noncomputable def reindex (e : α ≃ β) (F : SetFamily α) [DecidableEq  β]: SetFamily β := by
  classical
  refine
  { ground := F.ground.image (fun a => e a)
    , sets := fun B : Finset β => ∃ A : Finset α, F.sets A ∧ B = A.image (fun a => e a)
    , decSets := Classical.decPred _
    , inc_ground := ?_ }
  -- inc_ground：B = image e A かつ A ⊆ F.ground から B ⊆ image e ground
  intro B hB
  rcases hB with ⟨A, hAsets, rfl⟩
  intro b hb
  -- hb : b ∈ (A.image e)
  rcases Finset.mem_image.mp hb with ⟨a, haA, hb⟩
  -- F.inc_ground: A ⊆ F.ground
  have hAg : A ⊆ F.ground := F.inc_ground hAsets
  have haG : a ∈ F.ground := hAg haA
  -- よって b = e a は image e F.ground に入る
  exact Finset.mem_image.mpr ⟨a, haG, hb⟩

/-- ground の簡約。 -/
@[simp] lemma reindex_ground (e : α ≃ β) (F : SetFamily α) :
  (reindex e F).ground = F.ground.image (fun a => e a) := rfl

/-- メンバー述語の展開（`↔` ではなく「定義に等しい」）。 -/
@[simp] lemma mem_reindex_sets_iff (e : α ≃ β) (F : SetFamily α)
  {B : Finset β} :
  (reindex e F).sets B ↔ ∃ A : Finset α, F.sets A ∧ B = A.image (fun a => e a) :=
Iff.rfl

/-- リインデックスの単調性：`A ⊆ ground` の像は `reindex` 側の ground に入る。 -/
lemma subset_ground_image (e : α ≃ β) (F : SetFamily α)
  {A : Finset α} (hA : F.sets A) :
  A.image (fun a => e a) ⊆ (reindex e F).ground := by
  classical
  -- inc_ground をそのまま使うだけ
  have : (reindex e F).sets (A.image (fun a => e a)) := by
    exact ⟨A, hA, rfl⟩
  -- （定義より）inc_ground は B∈sets → B⊆ground
  exact (reindex e F).inc_ground this

/-- 述語レベルの単調性：`F.sets A` なら `reindex e F` にもその像が入る。 -/
lemma image_mem_reindex (e : α ≃ β) (F : SetFamily α)
  {A : Finset α} (hA : F.sets A) :
  (reindex e F).sets (A.image (fun a => e a)) := by
  exact ⟨A, hA, rfl⟩

end

end SetFamily
end AvgRare

--attribute [simp] Finset.mem_attach
--attribute [simp] Quot.eq -- 代表の単純化に使う場合は危険でない範囲で

--@[simp] lemma imageQuot_ground (E : Setoid α) (F : SetFamily α) :
--  imageQuot E F.ground = (trace E F).ground := rfl

-/
