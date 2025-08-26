import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import AvgRare.Basics.General
import LeanCopilot

universe u

open scoped BigOperators

namespace AvgRare

/-
SetFamily.lean  —  基本集合族とNDS。

集合族に関する基本的な定義と計数を行う。
- ここでは poset/ideal など順序に依存する概念は扱いません（Ideals 側へ）。
- トレースは Commonへ。
- FuncSetup が出てくるものは、FuncSetupへ。
-/

variable {α : Type u} [DecidableEq α]

/-- 有限台集合 `ground` 上の集合族。`sets A` は `A` が族のメンバである述語。
    計数・列挙のため、`edgeFinset` を powerset からの filter で構成できるように、
    `decSets`（可判別性）と `inc_ground`（台集合に含まれること）を仮定する。 -/
@[ext]
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

/-- NDS（正規化された次数和）：
`2 * (サイズ総和) - (エッジ数) * (台集合の大きさ)` を `Int` で定義。 -/
def NDS (F : SetFamily α) : Int :=
  2 * (F.totalHyperedgeSize : Int) - (F.numHyperedges : Int) * (F.ground.card : Int)

/-- Rare（稀）要素：`deg(x) ≤ |E|/2` を（両辺 2 倍して）自然数の不等式で表現。 -/
def Rare (F : SetFamily α) (x : α) : Prop :=
  2 * F.degree x ≤ F.numHyperedges

variable (F : SetFamily α)

@[simp] lemma NDS_def :
    NDS F = 2 * (F.totalHyperedgeSize : Int)
             - (F.numHyperedges : Int) * (F.ground.card : Int) := rfl

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
--どこで必要なのか考える。
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

/- `F.sets A` は `A ∈ F.edgeFinset` と同値。
    `edgeFinset = ground.powerset.filter (decide ∘ F.sets)` なので自動化できます。 -/
/-
@[simp] --上と同じだった。
lemma sets_iff_mem_edge (F : SetFamily α) {A : Finset α} :
  F.sets A ↔ A ∈ F.edgeFinset := by
  -- A が ground に含まれることと `filter (decide ∘ F.sets)` の会員判定を往復
  have : A ⊆ F.ground ↔ A ∈ F.ground.powerset := by
    exact Iff.symm Finset.mem_powerset
  constructor
  · intro hA
    have hAsub : A ⊆ F.ground := F.inc_ground hA
    -- powerset ∧ filter
    simp [edgeFinset, this.mp hAsub, hA]

  · intro hA
    -- filter に入っているなら `F.sets A` が真
    have : A ∈ F.ground.powerset ∧ decide (F.sets A) := by
      simpa [edgeFinset] using (Finset.mem_filter.mp hA)
    have hsets : F.sets A := by
     simp_all only [iff_true, mem_edgeFinset, true_and, Finset.mem_powerset, decide_true, and_self]

    exact hsets
-/

/-- 並行性：族 `F` において「`u` を含むエッジの集合」と
「`v` を含むエッジの集合」が一致する。 -/
--uやvが、F.ground外のときにはパラレルになってしまう。
--1. u、vをサブタイプにする。
--2. u in F.ground,v in F.groundという条件をつける。
--3. SetFamilyに全体集合をもつことを要求する。
@[simp] def Parallel (F : SetFamily α) (u v : α) : Prop :=
  {A : Finset α | F.sets A ∧ u ∈ A} = {A : Finset α | F.sets A ∧ v ∈ A}

lemma parallel_refl (F : SetFamily α) (u : α) : Parallel F u u := rfl

lemma parallel_symm {F : SetFamily α} {u v : α} :
    Parallel F u v → Parallel F v u := fun h => h.symm

--lemma parallel_symm' {F : SetFamily α} {a b : α}
--  (hab : Parallel F a b) : Parallel F b a :=
--  Eq.symm hab

/-- `Parallel` は同値関係：推移律（集合等式の推移） -/
lemma parallel_trans {F : SetFamily α} {a b c : α}
  (hab : Parallel F a b) (hbc : Parallel F b c) :
  Parallel F a c := by
  exact hab.trans hbc

/-- （計算しやすい）parallel の定義：`edgeFinset` を `u∈` で filter した Finset が一致。 -/
def Parallel_edge (F : SetFamily α) (u v : α) : Prop :=
  F.edgeFinset.filter (fun A => u ∈ A) =
  F.edgeFinset.filter (fun A => v ∈ A)

/-- あなたの `Parallel`（集合内包での等式）と `Parallel_edge` は同値。 -/
lemma Parallel_edge_iff_Parallel (F : SetFamily α) (u v : α) :
  Parallel_edge F u v ↔ Parallel F u v := by
  -- どちらも「`F.sets A` かつ `u∈A`（/`v∈A`）」という同じ性質を
  -- Finset の filter か Set の内包かの違いで述べているだけ。
  -- `sets_iff_mem_edge` で橋渡しして、`Finset.ext`/`Set.ext` で決着します。
  constructor
  · intro h
    -- filter の等式→ 内包集合の等式
    ext A
    constructor <;> intro hA <;>
    · rcases hA with ⟨hsets, hx⟩

      --have : A ∈ F.edgeFinset := (sets_iff_mem_edge F).mp hsets
      -- filter の等式で左右へ移すだけ
      all_goals
        have := congrArg (fun (s : Finset (Finset α)) => A ∈ s) h
        rw [@Set.mem_setOf_eq]
        constructor
        · exact hsets
        · simp at this
          have incg:A ⊆ F.ground := F.inc_ground hsets
          specialize this incg hsets
          simp_all only [iff_true]

  · intro h
    -- 内包集合の等式→ filter の等式
    -- `Finset.ext` で会員判定を `sets_iff_mem_edge` に落として一致
    apply Finset.ext
    intro A
    have h' := congrArg (fun (S : Set (Finset α)) => A ∈ S) h
    -- 2つの filter の会員判定と内包の会員判定を対応付ける
    constructor
    · intro hu
      rw [@Finset.mem_filter]
      rw [@Finset.mem_filter] at hu
      simp at h'
      simp_all only [Parallel, mem_edgeFinset, true_iff, forall_const, and_self]
    · intro hv
      rw [@Finset.mem_filter]
      rw [@Finset.mem_filter] at hv
      simp at h'
      simp_all only [Parallel, mem_edgeFinset, forall_const, and_self]

noncomputable def ParallelClass (F : SetFamily α) (a : α) : Finset α :=
  -- ground 上の同値類（decidable は classical で供給）
  by
    classical
    exact F.ground.filter (fun b => Parallel F a b)

noncomputable def classSet (F : SetFamily α) : Finset (Finset α) :=
  -- 「同値類の集合」を代表元写像の像で実装
  by
    classical
    exact F.ground.image (fun a => ParallelClass F a)

lemma ParallelClass_subset_ground (F : SetFamily α) {a : α} :
  ParallelClass F a ⊆ F.ground := by
  classical
  intro x hx
  have hx' := Finset.mem_filter.mp hx
  exact hx'.1

lemma ParallelClass_nonempty (F : SetFamily α) {a : α} (ha : a ∈ F.ground) :
  (ParallelClass F a).Nonempty := by
  classical
  refine ⟨a, ?_⟩
  -- a ∈ ground ∧ Parallel F a a
  exact Finset.mem_filter.mpr (And.intro ha (by rfl))

lemma mem_classSet_iff (F : SetFamily α) {C : Finset α} :
  C ∈ classSet F ↔ ∃ a ∈ F.ground, C = ParallelClass F a := by
  classical
  unfold classSet
  constructor
  · intro h
    -- h : C ∈ F.ground.image (λ a, ParallelClass F a)
    rcases Finset.mem_image.mp h with ⟨a, ha, hC⟩
    exact ⟨a,ha,hC.symm⟩
  · intro h
    rcases h with ⟨a, ha, hC⟩
    -- C = imageの値 なので像に入る
    have : ParallelClass F a ∈ F.ground.image (fun a => ParallelClass F a) :=
      Finset.mem_image.mpr ⟨a, ha, rfl⟩
    -- 書き換え
    rw [Finset.mem_image]
    rw [Finset.mem_image] at this
    obtain ⟨a,ha⟩  := this
    use a
    subst hC
    simp_all only [and_self]

--lemma pairwiseDisjoint_classSet (F : SetFamily α) :
--  (classSet F).PairwiseDisjoint id :=
--  sorry


noncomputable def numClasses (F : SetFamily α) : ℕ :=
  (classSet F).card

--方針を変えたが新方針でも使う。
/-- `ParallelClass` の代表を取り替えても同一。 -/
lemma parallelClass_eq_of_parallel
  (F : SetFamily α) {a b : α}
  (hab : Parallel F a b) :
  ParallelClass F a = ParallelClass F b := by
  classical
  -- いずれも `ground.filter` の形なので，会員判定を同値に落とす
  apply Finset.ext
  intro x
  constructor
  · intro hx
    -- x ∈ ground ∧ Parallel F a x から Parallel F b x へ
    rcases (Finset.mem_filter.mp hx) with ⟨hxg, hax⟩
    have hbx : Parallel F b x := by
      -- hab : S(a)=S(b) なので S(a)=S(x) ↔ S(b)=S(x)
      -- hax : Parallel F a x すなわち S(a)=S(x)
      -- よって S(b)=S(x)
      have hba : Parallel F b a := (parallel_symm (F := F) hab)
      exact parallel_trans (F := F) hba hax
    exact Finset.mem_filter.mpr ⟨hxg, hbx⟩
  · intro hx
    rcases (Finset.mem_filter.mp hx) with ⟨hxg, hbx⟩
    have hax : Parallel F a x := by
      have hab' : Parallel F b a := (parallel_symm (F := F) hab)
      exact parallel_trans hab hbx
    exact Finset.mem_filter.mpr ⟨hxg, hax⟩


--方針を変えたので、使わない方向と思ったが使うかも.
lemma classSet_disjoint_of_ne
  (F : SetFamily α) {C D : Finset α}
  (hC : C ∈ classSet F) (hD : D ∈ classSet F) (hne : C ≠ D) :
  Disjoint C D := by
  classical
  -- 代表元へ戻す
  unfold classSet at hC hD
  rcases Finset.mem_image.mp hC with ⟨a, ha, hCa⟩
  rcases Finset.mem_image.mp hD with ⟨b, hb, hDb⟩
  -- 交わると仮定して矛盾を作る
  refine Finset.disjoint_left.mpr ?_
  intro x hxC hxD
  -- `x ∈ ParallelClass a` と `x ∈ ParallelClass b` から `Parallel a b`
  have hxC' : x ∈ ParallelClass F a := by
    -- `C = ParallelClass F a`
    have := hxC; exact by
      -- `rw [hCa] at this` して使えばよい（using は使わない）
      -- 実運用では次の 2 行：
      --   have hxC'' := this; rw [hCa] at hxC''; exact hxC''
      -- ここでは直接：
      exact (by
        -- 書換を明示したい場合は `have hxC'' := hxC; rw [hCa] at hxC''; exact hxC''`
        -- としてください
        subst hCa hDb
        simp_all only [Finset.mem_image, ne_eq]

        )
  have hxD' : x ∈ ParallelClass F b := by
    exact (by
      -- 同様に `rw [hDb]` で置換して使う
      subst hCa hDb
      simp_all only [Finset.mem_image, ne_eq]
      )
  have hax : Parallel F a x := (Finset.mem_filter.mp hxC').2
  have hbx : Parallel F b x := (Finset.mem_filter.mp hxD').2
  -- `Parallel a b`
  have hba : Parallel F b a := parallel_trans hbx (parallel_symm hax)
  have hab : Parallel F a b := parallel_symm hba
  -- クラス等号へ
  have hEq : ParallelClass F a = ParallelClass F b := by

    exact parallelClass_eq_of_parallel F hab
  -- では C = D、`hne` に反する
  have : C = D := by
    -- `C = class a = class b = D`
    subst hCa hDb
    simp_all only [Parallel]
  exact (hne this).elim

--方針を変えたので、使わない方向。と思ったが使う。
/-- ground はクラスの不交和（被覆）。 -/
lemma ground_eq_biUnion_classSet (F : SetFamily α) :
  F.ground = Finset.biUnion (classSet F) (fun C => C) := by
classical
  -- ⊆ と ⊇ の両向き
  -- (⊆) 任意の a ∈ ground は自分のクラスに入るので和集合に入る
  apply Finset.Subset.antisymm_iff.mpr
  constructor
  · intro a ha
    -- a は `ParallelClass F a` の要素（反射律）
    have hmem : a ∈ ParallelClass F a := by
      exact Finset.mem_filter.mpr (And.intro ha (parallel_refl F a))
    -- そのクラスは `classSet F` の元
    have hC : ParallelClass F a ∈ classSet F := by
      unfold classSet
      exact Finset.mem_image.mpr ⟨a, ha, rfl⟩
    -- biUnion のメンバー判定
    -- `a ∈ ⋃_{C ∈ classSet} C` は、ある C で `C∈classSet` かつ `a∈C`
    exact Finset.mem_biUnion.mpr ⟨ParallelClass F a, hC, hmem⟩
  · -- (⊇) 和集合に入るなら、そのクラスは ground の部分集合なので ground に入る
    intro a ha
    -- メンバー判定をほどく
    rcases Finset.mem_biUnion.mp ha with ⟨C, hC, haC⟩
    -- そのクラスは ground の部分集合（1)）
    have hsub : C ⊆ F.ground := by
      -- C = ParallelClass F x という表示に直す
      unfold classSet at hC
      rcases Finset.mem_image.mp hC with ⟨x, hx, hCx⟩
      have : ParallelClass F x ⊆ F.ground :=
        by
          intro y hy
          exact (Finset.mem_filter.mp hy).1
      -- 書き換えで `C ⊆ ground`
      -- `C = ParallelClass F x`
      -- avoid `simpa using`：`rw [hCx]` で置換
      -- 最後に `exact` で出す
      -- 実装：
      --   `rw [hCx]; exact this`
      -- ここでは最終行だけ：
      exact
        (by
          -- 1 行版：`convert this using 1; exact hCx`
          -- 簡潔に：
          --   直接 `rw [hCx]` して `exact this`
          -- エディタでは：
          -- rw [hCx]; exact this
          subst hCx
          simp_all only [Finset.mem_biUnion, Finset.mem_image]

          )
    -- したがって a ∈ ground
    exact hsub haC


--方針を変えたので、使わないが、外から使っている。
lemma card_ground_eq_sum_card_classes (F : SetFamily α) :
  F.ground.card = ∑ C ∈ classSet F, C.card := by
  classical
  -- `ground = ⋃ C∈classSet, C`
  have hcover := ground_eq_biUnion_classSet (F := F)
  -- biUnion の濃度＝和（互いに素）
  have hdisj :
    ∀ C ∈ classSet F, ∀ D ∈ classSet F, C ≠ D → Disjoint C D := by
    intro C hC D hD hne
    exact classSet_disjoint_of_ne (F := F) hC hD hne
  -- `Finset.card_biUnion` でカード計算
  -- まず右辺（被覆）の濃度を和で表す
  have hcard :
      (Finset.biUnion (classSet F) (fun C => C)).card
        = ∑ C ∈ classSet F, C.card := by
    -- `card_biUnion` はインデックスを Finset で走る biUnion に使える
    -- （環境により表記が `∑ C in classSet F, (C.card)` でも同値）
    exact Finset.card_biUnion hdisj
  -- ground 側へ書換
  -- `rw [hcover]` で OK
  have := hcard
  -- 仕上げ
  -- 実運用では `rw [← hcover]` or `rw [hcover]` を 1 行
  -- ここでは最終行だけ出します：
  simp_all only [ne_eq]

--方針を変えたので使わない方向
lemma sum_card_sub_one_add_card
  (s : Finset (Finset α)) :
  (∑ C ∈ s, ((C.card:Int) - 1)) + s.card = ∑ C ∈ s, C.card := by
  classical
  refine Finset.induction_on s ?h0 ?hstep
  · -- 空集合
    simp
  · -- 挿入ステップ
    intro C s hC ih
    -- `sum_insert`, `card_insert` を展開
    -- `Nat.succ_eq_add_one` を使って整形
    have h1 :
        (∑ D ∈ insert C s, ((D.card:Int) - 1))
          = ((C.card:Int) - 1) + ∑ D ∈ s, ((D.card:Int) - 1) := by

      exact Finset.sum_insert (by exact hC)
    have h2 :
        (∑ D ∈ insert C s, D.card)
          = C.card + ∑ D ∈ s, D.card := by
      exact Finset.sum_insert (by exact hC)
    have h3 : (insert C s).card = s.card + 1 := by
      -- `Finset.card_insert` と `Nat.succ_eq_add_one`
      simp_all only [not_false_eq_true, Finset.sum_insert, Finset.card_insert_of_notMem]

    -- 目標を両辺とも `h1, h2, h3` で書換えてから整理
    -- LHS
    --   = ((C.card - 1) + ∑(…)) + (s.card + 1)
    --   = (C.card + ∑(…)) + s.card
    -- RHS
    --   = C.card + ∑(…)
    -- となるので、結局 `ih` を使って一致
    -- 実装は `simp` と結合法則で十分
    -- 展開

    calc
      (∑ D ∈ insert C s, ((D.card:Int) - 1)) + (insert C s).card
          = (((C.card:Int) - 1) + ∑ D ∈ s, ((D.card:Int) - 1)) + (s.card + 1) := by
            rw [h1, h3]
            exact rfl
      _   = (C.card + ∑ D ∈ s, ((D.card:Int) - 1)) + s.card := by
            -- `(C.card - 1) + (s.card + 1) = C.card + s.card`
            -- を使って整理
            -- ℕ なので可換群の道具は使わず、書換＋結合法則で
            -- `(a - 1) + (b + 1) = a + b`
            -- ここは `Nat.add_comm` 系で整理
            have : ((C.card:Int) - 1) + (s.card + 1) = C.card + s.card := by
              -- `Nat` では `a - 1 + 1 = a`、さらに `+ s.card` を付ける
              -- 形式的整形を `Nat.add_comm`/`Nat.add_assoc` で行う
              -- ここは計算補題として扱い、最終形だけ置きます
              -- 実務的には `cases C.card` で場合分けでも可

              simp_all only [Finset.sum_sub_distrib, Finset.sum_const, Int.nsmul_eq_mul, mul_one, sub_add_cancel, Nat.cast_sum,
                not_false_eq_true, Finset.sum_insert, Nat.cast_add, Nat.cast_one,
                Finset.card_insert_of_notMem, sub_add_add_cancel]

            -- 置換してから結合法則
            -- （実務では `simp [Nat.add_assoc, Nat.add_comm, this]` で十分）
            simp_all only [not_false_eq_true, Finset.sum_insert, Finset.card_insert_of_notMem]
            simp_all only [Finset.sum_sub_distrib, Finset.sum_const, Int.nsmul_eq_mul, mul_one, sub_add_cancel, Nat.cast_sum,
               sub_add_add_cancel]
            omega
      _   = C.card + (∑ D ∈ s, ((D.card:Int) - 1) + s.card) := by
            -- 結合法則
            exact Int.add_assoc (↑C.card) (∑ D ∈ s, (↑D.card - 1)) ↑s.card
      _   = C.card + (∑ D ∈ s, D.card) := by
            -- 帰納法の仮定
            -- `ih : (∑ (… - 1)) + s.card = ∑ (…)`
            -- を使用
            -- 実務では `rw [← ih]` 等
            simp_all only [Finset.sum_sub_distrib, Finset.sum_const, Int.nsmul_eq_mul, mul_one, sub_add_cancel, Nat.cast_sum,
              not_false_eq_true, Finset.sum_insert, Nat.cast_add, Nat.cast_one, Finset.card_insert_of_notMem]
      _   = (∑ D ∈ insert C s, D.card) := by
            -- `h2` で戻す
            rw [h2]
            exact rfl

--方針を変えたので、使わない方向
/-- 「∑1 = 個数」の基本補題。 -/
lemma sum_one_eq_card (s : Finset (Finset α)) :
  ∑ C ∈ s, (1 : Nat) = s.card := by
  classical
  refine Finset.induction_on s ?h0 ?hstep
  · simp
  · intro C s hC ih
    -- `sum_insert` と `card_insert`
    have h1 := Finset.sum_insert (by exact hC) (f := fun _ => (1 : Nat))
    simp_all only [Finset.sum_const, smul_eq_mul, mul_one, not_false_eq_true, Finset.card_insert_of_notMem]

--方針を変えたので、使わない方向
/-- 各クラスは非空なので、∑ card ≥ 個数。 -/
lemma classes_card_le_sum_cards (F : SetFamily α) :
  (classSet F).card ≤ ∑ C ∈ classSet F, C.card := by
  classical
  -- 各クラス `C` について `1 ≤ C.card`
  have h1 : ∀ C ∈ classSet F, 1 ≤ C.card := by
    intro C hC
    -- 代表元 a を取って `C = ParallelClass F a` に直す
    unfold classSet at hC
    rcases Finset.mem_image.mp hC with ⟨a, ha, hCa⟩
    -- クラスは非空
    have hne : (ParallelClass F a).Nonempty :=
      ParallelClass_nonempty (F := F) ha
    have : 0 < (ParallelClass F a).card :=
      Finset.card_pos.mpr hne
    -- `Nat.succ_le_of_lt`
    have : 1 ≤ (ParallelClass F a).card := Nat.succ_le_of_lt this
    -- `C = ParallelClass F a` で置換
    -- 実務では `rw [hCa]` の 1 行
    (expose_names; exact le_of_le_of_eq this_1 (congrArg Finset.card hCa))
  -- ∑1 ≤ ∑card
  have hsumle :
      ∑ C ∈ classSet F, (1 : Nat) ≤ ∑ C ∈ classSet F, C.card := by
    refine Finset.sum_le_sum ?hpoint
    intro C hC
    exact h1 C hC
  -- ∑1 = 個数
  have hleft : ∑ C ∈ classSet F, (1 : Nat) = (classSet F).card :=
    sum_one_eq_card (s := classSet F)
  -- 仕上げ
  -- `≤` に左辺を書換
  -- 実運用では `rw [hleft] at hsumle; exact hsumle`
  exact by
    -- 書換後にそのまま出す
    -- ここでは最終形だけ：
    -- `have := hsumle; rw [hleft] at this; exact this`
    exact le_of_eq_of_le (id (Eq.symm hleft)) hsumle


/- 上ですでに証明ずみ
/-- `Parallel a b` ならクラス等号。 -/
lemma parallelClass_eq_of_parallel
  (F : SetFamily α) {a b : α} (h : Parallel F a b) :
  ParallelClass F a = ParallelClass F b := by
  classical
  apply Finset.ext
  intro x; constructor
  · intro hx
    have hxg := (Finset.mem_filter.mp hx).1
    have hax := (Finset.mem_filter.mp hx).2
    have hba : Parallel F b a := parallel_symm h
    have hbx : Parallel F b x := parallel_trans hba hax
    exact Finset.mem_filter.mpr (And.intro hxg hbx)
  · intro hx
    have hxg := (Finset.mem_filter.mp hx).1
    have hbx := (Finset.mem_filter.mp hx).2
    have hax : Parallel F a x := parallel_trans h hbx
    exact Finset.mem_filter.mpr (And.intro hxg hax)
-/

/-- `classSet` の任意の要素は非空。 -/
lemma classSet_nonempty (F : SetFamily α) :
  ∀ C ∈ classSet F, C.Nonempty := by
  classical
  intro C hC
  unfold classSet at hC
  rcases Finset.mem_image.mp hC with ⟨a, ha, hCa⟩
  -- 代表 a は自分のクラスに入る
  have : a ∈ ParallelClass F a :=
    Finset.mem_filter.mpr (And.intro ha (parallel_refl F a))
  exact ⟨a, by
    -- `C = ParallelClass F a`
    -- 実ファイルでは `rw [hCa]` で置換
    subst hCa
    simp_all only [Finset.mem_image]
    ⟩

/- 画像は元集合以下：`numClasses ≤ |ground|`。 -/
lemma numClasses_le_ground_card (F : SetFamily α) :
  numClasses F ≤ F.ground.card := by
  classical
  unfold numClasses classSet
  -- (`(ground.image f).card ≤ ground.card`)
  exact Finset.card_image_le


/-
--上ですでに証明済みだがこちらのほうが短い？でも通ってないのでコメントアウト。
/-- `classSet` の異なる 2 クラスは互いに素。 -/
lemma classSet_disjoint_of_ne
  (F : SetFamily α) {C D : Finset α}
  (hC : C ∈ classSet F) (hD : D ∈ classSet F) (hne : C ≠ D) :
  Disjoint C D := by
  classical
  unfold classSet at hC hD
  rcases Finset.mem_image.mp hC with ⟨a, ha, hCa⟩
  rcases Finset.mem_image.mp hD with ⟨b, hb, hDb⟩
  refine Finset.disjoint_left.mpr ?_
  intro x hxC hxD
  have hxC' : x ∈ ParallelClass F a := by
    -- 実ファイルでは `rw [hCa] at hxC; exact hxC`
    exact hxC
  have hxD' : x ∈ ParallelClass F b := by
    exact hxD
  have hax : Parallel F a x := (Finset.mem_filter.mp hxC').2
  have hbx : Parallel F b x := (Finset.mem_filter.mp hxD').2
  have hba : Parallel F b a := parallel_trans hbx (parallel_symm hax)
  have hab : Parallel F a b := parallel_symm hba
  have hEq : ParallelClass F a = ParallelClass F b :=
    parallelClass_eq_of_parallel (F := F) hab
  have : C = D := Eq.trans hCa (Eq.trans hEq (Eq.symm hDb))
  exact (hne this).elim
-/
--ここから新方針
--すでに証明だった。
/-- `ground` はクラスの被覆。 -/
/-
lemma ground_eq_biUnion_classSet (F : SetFamily α) :
  F.ground = Finset.biUnion (classSet F) (fun C => C) := by
  classical
  apply Finset.Subset.antisymm_iff.mp
  constructor
  · intro a ha
    have hmem : a ∈ ParallelClass F a :=
      Finset.mem_filter.mpr (And.intro ha (parallel_refl F a))
    have hC : ParallelClass F a ∈ classSet F := by
      unfold classSet; exact Finset.mem_image.mpr ⟨a, ha, rfl⟩
    exact Finset.mem_biUnion.mpr ⟨ParallelClass F a, hC, hmem⟩
  · intro a ha
    rcases Finset.mem_biUnion.mp ha with ⟨C, hC, haC⟩
    unfold classSet at hC
    rcases Finset.mem_image.mp hC with ⟨x, hx, hCx⟩
    have : ParallelClass F x ⊆ F.ground := by
      intro y hy; exact (Finset.mem_filter.mp hy).1
    -- a ∈ C = ParallelClass F x ⊆ ground
    exact this (by
      -- 実ファイルでは `rw [hCx] at haC; exact haC`
      exact haC)
-/
------

-- 「w を含むエッジの集合」を Finset で：
def withElem (E : Finset (Finset α)) (w : α) : Finset (Finset α) :=
  E.filter (fun A => w ∈ A)

lemma Parallel_iff_filter_edge (F : SetFamily α) (w z : α) :
  Parallel F w z
  ↔ withElem F.edgeFinset w = withElem F.edgeFinset z := by
  -- sets での定義と edgeFinset = ground.powerset.filter(sets) をつなぐだけ
  -- `Finset.ext` と `mem_filter` の往復で出せます
  dsimp [Parallel]
  dsimp [withElem]
  rw [Finset.ext_iff]
  simp
  constructor
  · intro h
    rw [Set.ext_iff] at h
    intro a a_1 a_2
    simp_all only [Set.mem_setOf_eq, and_congr_right_iff]
  · intro h
    rw [Set.ext_iff]
    intro A
    simp_all
    intro hA
    specialize h A
    specialize h (F.inc_ground hA)
    exact h hA

  /-- 会員判定の基本形：`x ∈ ParallelClass F a` を「台集合所属＋平行」へ展開。 -/
@[simp] lemma mem_ParallelClass_iff
  (F : SetFamily α) (a x : α) :
  x ∈ ParallelClass F a ↔ (x ∈ F.ground ∧ Parallel F a x) := by
  classical
  unfold ParallelClass
  -- ground.filter _
  have : x ∈ F.ground.filter (fun b => Parallel F a b)
       ↔ (x ∈ F.ground ∧ Parallel F a x) :=
    by
      constructor
      · intro hx
        exact Finset.mem_filter.mp hx
      · intro hx
        exact Finset.mem_filter.mpr hx
  exact this

/-- `u‖v` なら、任意のクラス `C` で `u ∈ C ↔ v ∈ C`。 -/
--全体集合を持たないと証明がうまくいかない。
lemma mem_u_iff_mem_v_of_class
  (F : SetFamily α) (hasU: F.sets F.ground){u v : α} (hp : Parallel F u v)
  {C : Finset α} (hC : C ∈ classSet F) :
  (u ∈ C ↔ v ∈ C) := by
  classical
  -- `C = ParallelClass F a` を取り出す
  obtain ⟨a, ha, hCdef⟩ :
      ∃ a, a ∈ F.ground ∧ C = ParallelClass F a := by
    -- classSet F = ground.image (ParallelClass F)
    -- より、像の元はその形
    -- hC : C ∈ classSet F
    -- Finset.mem_image の型に合わせて取り出す
    have h := (Finset.mem_image.mp hC)
    -- h : ∃ a, a ∈ F.ground ∧ C = ParallelClass F a
    simp_all only [Parallel]
    obtain ⟨w, h⟩ := h
    obtain ⟨left, right⟩ := h
    subst right
    exact ⟨w, left, rfl⟩
  -- 以後、`C = ParallelClass F a` に書き換える
  -- 会員判定を補題で展開して、平行の推移で往復を作る
  have h1 : (u ∈ ParallelClass F a) → (v ∈ ParallelClass F a) := by
    intro huC
    have huC' : (u ∈ F.ground ∧ Parallel F a u) :=
      (mem_ParallelClass_iff F a u).1 huC
    have hav : Parallel F a v :=
      parallel_trans (F := F) huC'.2 hp
    have hvC' : (v ∈ F.ground ∧ Parallel F a v) := by
      constructor
      · dsimp [SetFamily.Parallel] at hp
        have : F.ground ∈ {A | F.sets A ∧ u ∈ A}:= by
          rw [@Set.mem_setOf_eq]
          subst hCdef
          simp_all only [mem_ParallelClass_iff, Parallel, true_and, and_true, and_self]
        subst hCdef
        simp_all only [mem_ParallelClass_iff, Parallel, true_and, and_true, Set.mem_setOf_eq]
      · exact hav

    exact (mem_ParallelClass_iff F a v).2 hvC'
  have h2 : (v ∈ ParallelClass F a) → (u ∈ ParallelClass F a) := by
    intro hvC
    have hvC' : (v ∈ F.ground ∧ Parallel F a v) :=
      (mem_ParallelClass_iff F a v).1 hvC
    have hpu : Parallel F v u := parallel_symm (F := F) hp
    have hau : Parallel F a u :=
      parallel_trans (F := F) hvC'.2 hpu
    have huC' : (u ∈ F.ground ∧ Parallel F a u) := by
      constructor
      · dsimp [SetFamily.Parallel] at hp
        have : F.ground ∈ {A | F.sets A ∧ v ∈ A}:= by
          rw [@Set.mem_setOf_eq]
          subst hCdef
          simp_all only [mem_ParallelClass_iff, Parallel, true_and, and_true, and_self]
        rw [←hp] at this
        simp at this
        exact this.2
      · exact hau
    exact (mem_ParallelClass_iff F a u).2 huC'
  -- 最後に `C = class a` に戻して両向きの同値を組む
  constructor
  · intro huC
    have : u ∈ ParallelClass F a := by
      -- 置換を「書き換え」で行う
      -- `hCdef : C = ParallelClass F a`
      -- huC : u ∈ C
      -- 書き換え：u ∈ C ↔ u ∈ ParallelClass F a
      have := huC
      have : u ∈ ParallelClass F a := by
        -- rw [hCdef] at huC は tactic だが、明示書換を使わずに等式置換
        exact cast (by rw [hCdef]) huC
      exact this
    have : v ∈ ParallelClass F a := h1 this
    -- 逆方向への置換
    apply cast
    exact rfl
    subst hCdef
    simp_all only [Parallel, imp_self, mem_ParallelClass_iff, and_true, and_self]
  · intro hvC
    have : v ∈ ParallelClass F a := cast (by rw [hCdef]) hvC
    have : u ∈ ParallelClass F a := h2 this
    subst hCdef
    simp_all only [Parallel, imp_self, mem_ParallelClass_iff, and_true, and_self]

section CountLemmas

variable {β : Type*}
/- 使ってないみたい。
/- 和 `∑ a∈s, (if p a then 1 else 0)` は `s.filter p` の個数に一致。 -/
lemma sum_indicator_card_filter (s : Finset β) (p : β → Prop) [DecidablePred p] :
    ∑ a ∈ s, (if p a then (1 : Nat) else 0) = (s.filter p).card := by
  classical
  refine Finset.induction_on s ?h0 ?hstep
  · -- 空集合
    simp
  · intro a s ha_notmem ih
    by_cases hpa : p a
    · -- p a = true
      have : (s.filter p).card.succ
            = (insert a s |>.filter p).card := by
        -- filter_insert（p a=true）→ a が 1 個増える（a∉sなので重複なし）
        have hfi : (insert a s).filter p = insert a ((s.filter p)) := by
          -- `Finset.filter_insert` と `hpa`、`ha_notmem`
          -- `simp` を避け、等式で書換え
          -- 既知：`filter p (insert a s) = if p a then insert a (filter p s) else filter p s`
          -- ここでは `p a = true`
          have := Finset.filter_insert (s := s) (p := p) a
          -- 書き換え
          have : (insert a s).filter p
              = (if p a then insert a (s.filter p) else s.filter p) := this
          -- true ケースに潰す
          have : (insert a s).filter p = insert a (s.filter p) := by
            simpa [hpa]
          exact this
        -- いまの等式から card をとる
        -- `a ∉ s.filter p`（a∉s なので当然）
        have hnot : a ∉ s.filter p := by
          intro ha'
          have : a ∈ s := (Finset.mem_of_subset (Finset.filter_subset _ _) ha')
          exact ha_notmem this
        -- `card (insert a t) = card t + 1` （a∉t）
        have hcard := Finset.card_insert_of_notMem hnot
        -- 目的の向きに整形
        -- `card (insert a (s.filter p)) = (s.filter p).card + 1`
        -- 逆向きに書いておく
        have : (insert a ((s.filter p))).card = (s.filter p).card + 1 := hcard
        -- succ = +1
        -- `Nat.succ n = n + 1`
        have : (s.filter p).card.succ = (insert a (s.filter p)).card := by
          -- `Nat.succ` の定義で置換
          -- `Nat.succ n = n + 1`
          -- ここでは `rw [Nat.succ_eq_add_one]`
          -- ただし simpa 禁止のため段階的に
          simp_all only [Finset.sum_boole, Nat.cast_id, Finset.mem_filter, and_true, not_false_eq_true, Finset.card_insert_of_notMem, Nat.succ_eq_add_one]
        simp_all only [Finset.sum_boole, Nat.cast_id, Finset.mem_filter, and_true, not_false_eq_true, Finset.card_insert_of_notMem, Nat.succ_eq_add_one]
        -- これで完了

      -- 和の側：挿入で 1 足し
      -- sum over insert = sum over s + (if p a then 1 else 0) = ih + 1
      have hs : ∑ x ∈ insert a s, (if p x then (1:Nat) else 0)
              = (if p a then 1 else 0) + ∑ x ∈ s, (if p x then 1 else 0) := by
        -- `sum_insert`（a∉s）
        have := Finset.sum_insert (by exact ha_notmem) (f := fun x => if p x then (1:Nat) else 0)
        -- `sum_insert` は `f a + sum_s` の形。型を合わせて使う
        exact this
      -- まとめ
      -- 左辺：hs、右辺：ih と上の card 等式
      -- （`Nat.succ` を `+1` に戻す）
      -- `Nat.succ_eq_add_one`
      have : ∑ x ∈ insert a s, (if p x then (1:Nat) else 0)
             = (s.filter p).card + 1 := by
        -- 書き換え
        -- hs と ih、hpa を使う
        -- 先に hs を適用
        calc
          _ = (if p a then 1 else 0) + ∑ x ∈ s, (if p x then (1:Nat) else 0) := hs
          _ = 1 + (∑ x ∈ s, (if p x then (1:Nat) else 0)) := by
                -- p a = true
                have : (if p a then 1 else 0) = (1:Nat) := by exact by simp_all only [Finset.sum_boole, Nat.cast_id, Nat.succ_eq_add_one, ↓reduceIte]
                rw [this]
          _ = 1 + (s.filter p).card := by rw [ih]
          _ = (s.filter p).card + 1 := Nat.add_comm 1 _
      -- 右辺：filter のカード
      -- 先に `Nat.succ_eq_add_one` と上で得た `succ = card(insert ...)`
      have hcard_ins :
        (insert a s |>.filter p).card = (s.filter p).card + 1 := by
        -- すでに上の `this` が `succ = card(insert ...)` の対称形
        -- 直上で作った等式 `this` は sum 側、紛らわしいので別名に
        -- ここは `Nat.succ` の等式を使った `this` (hfi/hcard 組) から
        -- `card (filter (insert ...)) = (s.filter p).card + 1` が出ています
        -- 上で `this` として `∑ = ...` を付けたので名称が被るため書き直し:
        -- 再構築は冗長なので、簡潔にもう一度：
        have hfi : (insert a s).filter p = insert a (s.filter p) := by
          have := Finset.filter_insert (s := s) (p := p) a
          have : (insert a s).filter p
              = (if p a then insert a (s.filter p) else s.filter p) := this
          -- true ケース
          exact by simpa [hpa] using this
        -- すると `card(filter insert) = card(insert ...) = ... + 1`
        have hnot : a ∉ s.filter p := by
          intro ha'
          have : a ∈ s := (Finset.mem_of_subset (Finset.filter_subset _ _) ha')
          exact ha_notmem this
        have : (insert a (s.filter p)).card = (s.filter p).card + 1 :=
          Finset.card_insert_of_notMem hnot
        -- 置換
        simpa [hfi]
      -- 以上で両辺一致
      -- まとめる：
      -- 目標：sum(insert) = card(filter(insert))
      -- 左辺は上の `this`、右辺は `hcard_ins`
      -- （記号衝突を避け、ここでは `hs_sum` と `hs_card` に分けて再利用）
      -- 既に左辺 `this` を作ったので、置換して終了
      -- 実際にはこのブロックで十分
      -- 目標を書き換えて終了
      -- （`exact` で置ける）
      -- ここでは、先ほどの `this` は sum 側だったので、再度命名してから `exact` します。
      exact by
        -- sum(insert) = (s.filter p).card + 1 かつ
        -- card(filter(insert)) = (s.filter p).card + 1
        -- よって等しい
        have hsum : ∑ x ∈ insert a s, (if p x then (1:Nat) else 0)
                  = (s.filter p).card + 1 := by
          -- 直上で作った sum 等式
          -- 再掲
          -- （すでに `this` 名が使われているので再作成）
          -- 同内容をもう一度書くのは冗長ですが、明示で安全にします。
          calc
            _ = (if p a then 1 else 0) + ∑ x ∈ s, (if p x then (1:Nat) else 0) := by
                  exact hs
            _ = 1 + (∑ x ∈ s, (if p x then (1:Nat) else 0)) := by
                  have : (if p a then 1 else 0) = (1:Nat) := by
                    simp_all only [Finset.sum_boole, Nat.cast_id, Nat.succ_eq_add_one, ↓reduceIte, Nat.cast_add, Nat.cast_one]
                  rw [this]
            _ = 1 + (s.filter p).card := by rw [ih]
            _ = (s.filter p).card + 1 := Nat.add_comm 1 _
        -- これと hcard_ins を合わせて
        exact by
          -- 目標：sum(insert) = card(filter(insert))
          -- 置換
          rw [hsum, hcard_ins]
    · -- p a = false
      -- 挿入後の和は ih のまま
      have hs : ∑ x ∈ insert a s, (if p x then (1:Nat) else 0)
              = ∑ x ∈ s, (if p x then (1:Nat) else 0) := by
        have := Finset.sum_insert (by exact ha_notmem) (f := fun x => if p x then (1:Nat) else 0)
        -- 左辺の先頭項は 0
        -- `if p a then 1 else 0 = 0`
        have hz : (if p a then (1:Nat) else 0) = 0 := by simp_all only [Finset.sum_boole, Nat.cast_id, ↓reduceIte, zero_add]
        -- 上の sum_insert: `f a + sum_s`
        -- ゆえに `0 + sum_s = sum_s`
        -- 置換
        have := by
          calc
            (if p a then (1:Nat) else 0) + ∑ x ∈ s, (if p x then (1:Nat) else 0)
                = 0 + ∑ x ∈ s, (if p x then (1:Nat) else 0) := by rw [hz]
            _ = ∑ x ∈ s, (if p x then (1:Nat) else 0) := by exact Nat.zero_add _
        -- まとめ
        exact by
          -- `sum_insert` から始めて置換
          have := Finset.sum_insert (by exact ha_notmem)
              (f := fun x => if p x then (1:Nat) else 0)
          -- その等式を `rw` で使い、次に上の 0 消去を使う
          -- ここは直接 `rw` が煩雑なので、別経路の等式として使う
          -- 簡潔に：`bycases` で `p a = false` を使えば上と同じ結果に到達
          -- 最後は直接目標を `exact` で閉じます
          -- 既に `hs` に等式を収束させています
          simp_all only [Finset.sum_boole, Nat.cast_id, ↓reduceIte, zero_add]

      -- filter 側：¬p の方が 1 増える
      have hfi_false : (insert a s).filter (fun x => ¬ p x) = insert a (s.filter (fun x => ¬ p x)) := by
        -- `filter_insert` に p := (fun x => ¬ p x)
        have := Finset.filter_insert (s := s) (p := fun x => ¬ p x) a
        -- 今は `¬ p a = true` なので true ケース
        have : (insert a s).filter (fun x => ¬ p x)
            = (if (¬ p a) then insert a (s.filter (fun x => ¬ p x))
               else s.filter (fun x => ¬ p x)) := this
        have : (insert a s).filter (fun x => ¬ p x)
            = insert a (s.filter (fun x => ¬ p x)) := by
          -- ここで `¬ p a` は true
          have : (¬ p a) := by
            have : p a = False := by simp_all only [Finset.sum_boole, Nat.cast_id, not_false_eq_true, ↓reduceIte]
            -- `p a = false` から `¬ p a`
            exact by
              -- 反転
              simp_all only [Finset.sum_boole, Nat.cast_id, not_false_eq_true, ↓reduceIte, eq_iff_iff, iff_false]

          simp_all only [Finset.sum_boole, Nat.cast_id, not_false_eq_true, ↓reduceIte]
        exact this
      -- `a ∉ s.filter (¬p)`
      have hnot : a ∉ s.filter (fun x => ¬ p x) := by
        intro ha'
        have : a ∈ s := (Finset.mem_of_subset (Finset.filter_subset _ _) ha')
        exact ha_notmem this
      have hcard_ins :
          (insert a s |>.filter (fun x => ¬ p x)).card
          = (s.filter (fun x => ¬ p x)).card + 1 := by
        -- 上の等式から card_insert_of_not_mem
        have := Finset.card_insert_of_notMem hnot
        -- 置換
        simpa [hfi_false] using this
      -- また、`(insert a s).filter p = s.filter p`（p a=false）
      have hfi_true :
          (insert a s |>.filter p) = s.filter p := by
        -- 先ほどの p 版の filter_insert の false ケース
        have := Finset.filter_insert (s := s) (p := p) a
        have : (insert a s).filter p
            = (if p a then insert a (s.filter p) else s.filter p) := this
        -- p a = false
        have : (insert a s).filter p = s.filter p := by simpa [hpa] using this
        exact this
      -- 目標：sum = card(filter p)
      -- `hs` と `ih`、`hfi_true` を合わせれば OK
      calc
        ∑ x ∈ insert a s, (if p x then (1:Nat) else 0)
            = ∑ x ∈ s, (if p x then (1:Nat) else 0) := hs
        _ = (s.filter p).card := ih
        _ = ((insert a s).filter p).card := by rw [hfi_true]
-/
/-- `card (s.filter p) + card (s.filter (¬p)) = card s`。 -/
lemma card_filter_add_card_filter_not (s : Finset β) (p : β → Prop) [DecidablePred p] :
    (s.filter p).card + (s.filter (fun b => ¬ p b)).card = s.card := by
  classical
  refine Finset.induction_on s ?h0 ?hstep
  · simp
  · intro a s ha ih
    by_cases hpa : p a
    · -- p a
      -- 左辺： (insert a (filter p s)).card + (filter ¬p s).card
      have hfi_p :
          (insert a s).filter p = insert a (s.filter p) := by
        have := Finset.filter_insert (s := s) (p := p) a
        simpa [hpa] using this
      have hfi_np :
          (insert a s).filter (fun b => ¬ p b) = (s.filter (fun b => ¬ p b)) := by
        have := Finset.filter_insert (s := s) (p := fun b => ¬ p b) a
        -- ここでは `¬ p a = false`
        have : ¬ p a = False := by simp_all only [not_true_eq_false, ↓reduceIte, eq_iff_iff, iff_false, not_false_eq_true]
        -- false ケース
        simp_all only [not_true_eq_false, ↓reduceIte, eq_iff_iff, iff_false, not_false_eq_true]
      have hnot : a ∉ s.filter p := by
        intro ha'
        have : a ∈ s := (Finset.mem_of_subset (Finset.filter_subset _ _) ha')
        exact ha this
      have hcard_insert :
          (insert a (s.filter p)).card = (s.filter p).card + 1 :=
        Finset.card_insert_of_notMem hnot
      calc
        ((insert a s).filter p).card + ((insert a s).filter (fun b => ¬ p b)).card
            = (insert a (s.filter p)).card + (s.filter (fun b => ¬ p b)).card := by
                rw [hfi_p, hfi_np]
        _ = (s.filter p).card + 1 + (s.filter (fun b => ¬ p b)).card := by
                rw [hcard_insert]
        _ = (s.filter p).card + (s.filter (fun b => ¬ p b)).card + 1 := by
                exact Nat.add_right_comm (Finset.filter p s).card 1 {b ∈ s | ¬p b}.card
        _ = s.card + 1 := by
                rw [ih]
        _ = (insert a s).card := by
                -- `card_insert_of_not_mem`
                have := Finset.card_insert_of_notMem ha
                -- `card (insert a s) = card s + 1`
                exact this.symm
    · -- p a = false
      -- 対称な議論
      have hfi_p :
          (insert a s).filter p = (s.filter p) := by
        have := Finset.filter_insert (s := s) (p := p) a
        simpa [hpa] using this
      have hfi_np :
          (insert a s).filter (fun b => ¬ p b) = insert a (s.filter (fun b => ¬ p b)) := by
        have := Finset.filter_insert (s := s) (p := fun b => ¬ p b) a
        -- ここでは `¬ p a = true`
        have : (¬ p a) = True := by simp_all only [not_false_eq_true, ↓reduceIte]
        -- true ケース
        simp_all only [↓reduceIte, eq_iff_iff, iff_true]
      have hnot : a ∉ s.filter (fun b => ¬ p b) := by
        intro ha'
        have : a ∈ s := (Finset.mem_of_subset (Finset.filter_subset _ _) ha')
        exact ha this
      have hcard_insert :
          (insert a (s.filter (fun b => ¬ p b))).card
          = (s.filter (fun b => ¬ p b)).card + 1 :=
        Finset.card_insert_of_notMem hnot
      calc
        ((insert a s).filter p).card + ((insert a s).filter (fun b => ¬ p b)).card
            = (s.filter p).card + (insert a (s.filter (fun b => ¬ p b))).card := by
                rw [hfi_p, hfi_np]
        _ = (s.filter p).card + (s.filter (fun b => ¬ p b)).card + 1 := by
                rw [hcard_insert]
                exact rfl
        _ = s.card + 1 := by
                rw [ih]
        _ = (insert a s).card := by
                have := Finset.card_insert_of_notMem ha
                exact this.symm

end CountLemmas
end SetFamily



/-

/-- 有限台集合 `ground` と，その部分集合族 `sets`（判定述語＋可判定性） 古い定義-/
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

/-- 二重計数：`ground` 上の次数総和 = 超辺サイズ総和（Nat 版）平均次数の議論をするには復活させてもいいかも。 -/
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


end SetFamily
end AvgRare

--attribute [simp] Finset.mem_attach
--attribute [simp] Quot.eq -- 代表の単純化に使う場合は危険でない範囲で

--@[simp] lemma imageQuot_ground (E : Setoid α) (F : SetFamily α) :
--  imageQuot E F.ground = (trace E F).ground := rfl

-/
