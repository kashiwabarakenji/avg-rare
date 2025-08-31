import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Basic
import Mathlib.Logic.Function.Iterate
import AvgRare.Basics.SetFamily
import LeanCopilot

/-
FuncSetup.lean — Setup for (functional preorder) (Paper §2)
FuncSetup is a hypothetical definition and basic lemma.
-/

universe u

open scoped BigOperators
open Classical

namespace AvgRare

variable {α : Type u} [DecidableEq α]

structure FuncSetup (α : Type u)  [DecidableEq α] where
  ground : Finset α
  nonempty : Nonempty ground  --ground.Nonempty is better?
  f      : {x // x ∈ ground} → {y // y ∈ ground}

namespace FuncSetup

variable (S : FuncSetup α)

abbrev Elem := {x : α // x ∈ S.ground}

def cover (x y : S.Elem) : Prop := S.f x = y

def le (x y : S.Elem) : Prop := Relation.ReflTransGen S.cover x y

/- 記法：`x ≤ₛ y` / `x ⋖ₛ y` -/
/-
scoped infix:50 " ≤ₛ " => FuncSetup.le
scoped infix:50 " ⋖ₛ " => FuncSetup.cover
-/

lemma le_refl (x : S.Elem) : S.le x x := by
  exact Relation.ReflTransGen.refl

lemma le_trans {x y z : S.Elem} (hxy : S.le x y) (hyz : S.le y z) : S.le x z := by
  exact Relation.ReflTransGen.trans hxy hyz

--以下の2つは、FuncPosetに移動。
def has_le_antisymm  : Prop :=
∀ {x y : S.Elem}, (S.le x y) → (S.le y x) → x = y



lemma cover_to_le {x y : S.Elem} (h : S.cover x y) : S.le x y := by
  exact Relation.ReflTransGen.single h

/-- 同じ元からの `cover` の像は一意 -/
--下で使われている。
lemma cover_out_unique (S : FuncSetup α){u y z : S.Elem} :
  S.cover u y → S.cover u z → y = z := by
  intro hy hz

  dsimp [FuncSetup.cover] at hy hz
  have h' := hz
  rw [hy] at h'
  exact h'

--------------------
--SubType---------
----------------------

/-- ground の元 `x : α` とその証明から `S.Elem` を作るユーティリティ。 -/
def toElem! {x : α} (hx : x ∈ S.ground) : S.Elem := ⟨x, hx⟩

@[simp] lemma toElem!_val {x : α} (hx : x ∈ S.ground) :
    (S.toElem! hx).1 = x := rfl
@[simp] lemma toElem!_mem {x : α} (hx : x ∈ S.ground) :
    (S.toElem! hx).2 = hx := rfl

-- toElem! の往復（既存なら @[simp] を付けると後の書き換えが楽）。
--使っている。
@[simp] lemma toElem!_coe (S : FuncSetup α) (x : S.Elem) :
    S.toElem! x.property = x := by
  cases x with
  | mk x hx => rfl

-- S.Elem の不等号から underlying へ
--一箇所使っている。
lemma coe_ne_of_ne {S : FuncSetup α} {x y : S.Elem} (h : x ≠ y) :
    (x : α) ≠ (y : α) := by
  intro hxy
  apply h
  apply Subtype.ext
  exact hxy

/-- `leOn S y x` : ground 上の要素 `y, x : α` について，
S の部分型 `S.Elem` 上の `S.le ⟨y,hy⟩ ⟨x,hx⟩` が成り立つことを「存在」で述べる。 -/
def leOn (S : FuncSetup α) (y x : α) : Prop :=
  ∃ (hy : y ∈ S.ground) (hx : x ∈ S.ground),
      FuncSetup.le S ⟨y, hy⟩ ⟨x, hx⟩

--結構使っている
lemma leOn_iff_subtype (S : FuncSetup α) {a b : α}
  (ha : a ∈ S.ground) (hb : b ∈ S.ground) :
  S.leOn a b ↔ S.le ⟨a, ha⟩ ⟨b, hb⟩ := by
  constructor
  · rintro ⟨ha', hb', h⟩
    have ea : (⟨a, ha'⟩ : S.Elem) = ⟨a, ha⟩ := Subtype.ext (rfl)
    have eb : (⟨b, hb'⟩ : S.Elem) = ⟨b, hb⟩ := Subtype.ext (rfl)
    cases ea; cases eb; exact h
  · intro h; exact ⟨ha, hb, h⟩

lemma leOn_refl (S : FuncSetup α) {x : α} (hx : x ∈ S.ground) :
  S.leOn x x :=
by
  exact ⟨hx, hx, Relation.ReflTransGen.refl⟩

lemma leOn_trans (S : FuncSetup α) {y x z : α}
  (h₁ : S.leOn y x) (h₂ : S.leOn x z) :
  S.leOn y z :=
by
  rcases h₁ with ⟨hy, hx, h_yx⟩
  rcases h₂ with ⟨hx', hz, h_xz⟩
  have h_yx' : S.le ⟨y, hy⟩ ⟨x, hx'⟩ := by
    have e : (⟨x, hx⟩ : S.Elem) = ⟨x, hx'⟩ := Subtype.ext (by rfl)
    cases e
    exact h_yx
  have h_yz : S.le ⟨y, hy⟩ ⟨z, hz⟩ :=
    Relation.ReflTransGen.trans h_yx' h_xz
  exact ⟨hy, hz, h_yz⟩

--leOn_iff_subtypeと同じ
lemma leOn_iff (S : FuncSetup α)
  {a b : α} (hb : b ∈ S.ground) (ha : a ∈ S.ground) :
  S.leOn b a ↔ S.le ⟨b, hb⟩ ⟨a, ha⟩ := by
  unfold FuncSetup.leOn
  simp_all only [exists_true_left]

-- サブタイプ上の比較と ground 上の比較の橋渡し
-- （S.le が「S.leOn をサブタイプへ持ち上げたもの」になっていれば定義等号で証明できます）
@[simp] lemma le_iff_leOn_val
    (S : FuncSetup α) (x y : S.Elem) :
    S.le x y ↔ S.leOn (x : α) (y : α) := by
    obtain ⟨val, property⟩ := x
    obtain ⟨val_1, property_1⟩ := y
    simp_all only
    apply Iff.intro
    · intro a
      dsimp [FuncSetup.leOn]
      simp_all only [exists_const]
    · intro a
      induction a
      simp_all only [exists_true_left]

--------------------------------
--------------------hyperedge関連
-----------------------------------

noncomputable def coeFinset (S : FuncSetup α) (I : Finset S.Elem) : Finset α :=
  I.image (fun x => (x.1 : α))

noncomputable def liftFinset
  (S : FuncSetup α) (J : Finset α) (hJ : J ⊆ S.ground) : Finset S.Elem :=
  J.attach.map
    ⟨(fun t => (⟨t.1, hJ t.2⟩ : S.Elem)),
     by
       intro u v h; cases u; cases v; cases h; rfl⟩

@[simp] lemma mem_coeFinset (S : FuncSetup α) (I : Finset S.Elem) {x : α} :
  x ∈ S.coeFinset I ↔ ∃ y ∈ I, (y : α) = x := by
  classical
  constructor
  · intro hx
    rcases Finset.mem_image.mp hx with ⟨y, hyI, rfl⟩
    exact ⟨y, hyI, rfl⟩
  · rintro ⟨y, hyI, rfl⟩
    exact Finset.mem_image.mpr ⟨y, hyI, rfl⟩

@[simp] lemma mem_coeFinset_val_iff
    (S : FuncSetup α) {I : Finset S.Elem} {a : α} :
    a ∈ S.coeFinset I ↔ ∃ z : S.Elem, z ∈ I ∧ (z : α) = a := by
  constructor
  · intro ha
    rcases Finset.mem_image.mp ha with ⟨z, hzI, rfl⟩
    exact ⟨z, hzI, rfl⟩
  · rintro ⟨z, hzI, rfl⟩
    exact Finset.mem_image.mpr ⟨z, hzI, rfl⟩

@[simp] lemma mem_coeFinset_iff
    (S : FuncSetup α) {I : Finset S.Elem} {a : α} (ha : a ∈ S.ground) :
    a ∈ S.coeFinset I ↔ ⟨a, ha⟩ ∈ I := by
  constructor
  · intro haI
    rcases (mem_coeFinset_val_iff (S:=S)).mp haI with ⟨z, hzI, hz⟩
    -- `z : S.Elem` と `z.1 = a` から `z = ⟨a,ha⟩` を得る
    have : z = ⟨a, ha⟩ := Subtype.ext (by simpa [Subtype.ext] using congrArg id hz)
    subst this
    simp_all only [FuncSetup.mem_coeFinset, Subtype.exists, exists_and_right, exists_eq_right, exists_const]
  · intro hz
    -- 逆向きは像の定義そのもの
    exact Finset.mem_image.mpr ⟨⟨a, ha⟩, hz, rfl⟩

@[simp] lemma mem_liftFinset_iff
  (S : FuncSetup α) {J : Finset α} {hJ : J ⊆ S.ground} {z : S.Elem} :
  z ∈ S.liftFinset J hJ ↔ (z : α) ∈ J := by
  classical
  unfold FuncSetup.liftFinset
  constructor
  · intro hz
    rcases Finset.mem_map.mp hz with ⟨t, ht, hmap⟩
    -- t : {a // a ∈ J}, ht : t ∈ J.attach, hmap : ⟨t.1, hJ t.2⟩ = z
    -- よって (z : α) = t.1 ∈ J
    have : (z : α) = t.1 := by cases z; cases t; cases hmap; rfl
    exact this ▸ t.2
  · intro hz
    refine Finset.mem_map.mpr ?_
    refine ⟨⟨z.1, hz⟩, ?_, ?_⟩
    · exact Finset.mem_attach _ _
    · cases z; rfl

/-- 目的の補題：`coeFinset ∘ liftFinset = id` （`J ⊆ ground` が前提） -/
@[simp] lemma coeFinset_liftFinset
  (S : FuncSetup α) (J : Finset α) (hJ : J ⊆ S.ground) :
  S.coeFinset (S.liftFinset J hJ) = J := by
  classical
  apply Finset.ext
  intro a
  constructor
  · intro ha
    -- a ∈ coeFinset (lift J) → ∃ z ∈ lift J, z.1 = a → a ∈ J
    rcases (mem_coeFinset_val_iff S).1 ha with ⟨z, hzLift, hz⟩
    -- z ∈ lift ↔ z.1 ∈ J
    have : (z : α) ∈ J := (mem_liftFinset_iff S).1 hzLift
    -- z.1 = a で書き換え
    subst hz
    simp_all only [mem_liftFinset_iff, FuncSetup.mem_coeFinset, Subtype.exists, exists_and_left, exists_prop,
    exists_eq_right_right]

  · intro haJ
    -- a ∈ J → ある z=⟨a, hJ haJ⟩ が lift に入り、その像に a が入る
    have hz : (⟨a, hJ haJ⟩ : S.Elem) ∈ S.liftFinset J hJ :=
      (mem_liftFinset_iff S).2 haJ
    exact (mem_coeFinset_val_iff S).2 ⟨⟨a, hJ haJ⟩, hz, rfl⟩
--同値類関係

/-- 同値関係：`x ∼ y` iff `x ≤ y ∧ y ≤ x`。 -/
def sim (x y : S.Elem) : Prop := S.le x y ∧ S.le y x

/-- `sim` は同値関係。 -/
lemma sim_refl (x : S.Elem) : S.sim x x := by
  constructor <;> exact S.le_refl x

lemma sim_symm {x y : S.Elem} (h : S.sim x y) : S.sim y x := by
  constructor
  · exact h.2
  · exact h.1

lemma sim_trans {x y z : S.Elem} (hxy : S.sim x y) (hyz : S.sim y z) : S.sim x z := by
  constructor
  · exact S.le_trans hxy.1 hyz.1
  · exact S.le_trans hyz.2 hxy.2

/-- `sim` を `Setoid` に。 -/
--現状使ってない
def simSetoid : Setoid S.Elem where
  r := S.sim
  iseqv := ⟨S.sim_refl, S.sim_symm, S.sim_trans⟩



/-- 「同値類が非自明（別の点がある）」の実用形。 -/
def nontrivialClass {α : Type u} [DecidableEq α] (S : FuncSetup α) (x : S.Elem) : Prop :=
  ∃ y : S.Elem, y ≠ x ∧ S.sim x y



lemma fixed_point_unique {α : Type u} [DecidableEq α] (S : FuncSetup α) (u : S.Elem)
    (h_fixed : S.f u = u) {v : S.Elem} (h_le : S.le u v) : u = v := by
  induction h_le with
  | refl => rfl
  | tail hb h_cover ih =>
    rename_i b c
    have : S.f b = c:= by exact h_cover
    rw [ih] at h_fixed
    rw [h_fixed] at this
    rw [←ih] at this
    exact this

/-- 非自明同値類に属する `u` は自己固定点ではない（`f u ≠ u`）。 -/
--2箇所で使っている。
lemma f_ne_of_nontrivialClass (S : FuncSetup α) {u : S.Elem}
    (h : S.nontrivialClass u) : S.f u ≠ u := by
  rcases h with ⟨y, hy_ne, hy_sim⟩
  intro hfix -- 仮に等しいとすると
  -- u ≤ y から `fixed_point_unique` で u = y
  have : u = y := S.fixed_point_unique u hfix hy_sim.1
  exact hy_ne this.symm

/-! ## 2) 「機能性」：出次数高々 1 -/

-- 極大関係

/-- 極大：`x` の上は全部 `x` に戻る（前順序版）。 -/
def maximal (x : S.Elem) : Prop :=
  ∀ ⦃y⦄, S.le x y → S.le y x

@[simp] lemma maximal_iff (x : S.Elem) :
    S.maximal x ↔ (∀ ⦃y⦄, S.le x y → S.le y x) := Iff.rfl

/-- `f u = u` なら `u` は極大（反対称性不要） -/
--使われている。
lemma maximal_of_fixpoint  (S : FuncSetup α){u : S.Elem} (huu : S.cover u u) :
  S.maximal u := by
  intro v huv
  -- 「u から到達できるのは u のみ」を反復閉包で帰納
  have reach_eq : ∀ w, S.le u w → w = u := by
    intro w hw
    induction hw with
    | @refl =>
        rfl
    | @tail w x hw ih hwx =>
        -- `hw : u ≤ w`, `hwx : cover w x`, 帰納法の仮定 `ih : w = u`
        have hux : S.cover u x := by
          cases ih
          exact congrArg S.f (id (Eq.symm hwx))
        have hx : x = u := by
          exact cover_out_unique S hux huu
        exact hx
  have hveq : v = u := reach_eq v huv
  cases hveq
  exact Relation.ReflTransGen.refl

--上と内容が同じなので廃止
/-
lemma fixpoint_is_maximal
  (S : FuncSetup α) {p : S.Elem} (hfix : S.cover p p) :
  S.maximal p := by

  have h_fixed : S.f p = p := hfix

  intro y hy

  have : p = y :=
    fixed_point_unique (S := S) (u := p) (h_fixed := h_fixed) (v := y) (h_le := hy)

  cases this
  exact Relation.ReflTransGen.refl
-/

/-! ## 3) Lemma 3.1：maximal ⇒ rare -/

--Rare.leanで利用。
lemma sim_of_maximal_above_class
    (S : FuncSetup α) {u x y : S.Elem}
    (hmax : S.maximal u)
    (hyU : S.sim y u) (hyx : S.le y x) :
    S.sim x u := by
  -- `u ≤ x` と `x ≤ u` の両方を示せば良い
  constructor
  · -- まず `u ≤ x`
    have hux : S.le u x := S.le_trans hyU.2 hyx
    -- 最大性：`u ≤ x → x ≤ u`
    exact hmax hux
  · -- つぎに `u ≤ x` は上で得た `hux`
    exact S.le_trans hyU.2 hyx

--------sim (idealもParallelも関係ないもの)

/-- ground 上の要素型 `S.Elem` における `u` の同値類（Finset 版）。 -/
noncomputable def simClassElem (S : FuncSetup α) (u : S.Elem) : Finset S.Elem :=
  S.ground.attach.filter (fun v => S.sim v u)

/-- `α` 側へ戻した同値類（`idealFamily : SetFamily α` が扱うのはこちら）。 -/
noncomputable def simClass (S : FuncSetup α) (u : S.Elem) : Finset α :=
  (S.simClassElem u).image (Subtype.val)

/-- `v ∈ simClassElem u` の判定は「ちょうど `S.sim v u`」。 -/
@[simp] lemma mem_simClassElem
    (S : FuncSetup α) (u : S.Elem) (v : S.Elem) :
    v ∈ S.simClassElem u ↔ S.sim v u := by
  classical
  unfold simClassElem
  constructor
  · intro hv
    have hv' := Finset.mem_filter.mp hv
    exact hv'.2
  · intro hsim
    have hvattach : v ∈ S.ground.attach := by
      -- `attach` の要素は（証明部分はどうであれ）常に自分自身が所属します
      -- `simp` だけで出ます
      simp_all only [Finset.mem_attach]
    exact Finset.mem_filter.mpr ⟨hvattach, hsim⟩

/-- `a ∈ simClass u` の判定。 -/
lemma mem_simClass_iff
    (S : FuncSetup α) (u : S.Elem) {a : α} :
    a ∈ S.simClass u ↔ ∃ (ha : a ∈ S.ground), S.sim ⟨a, ha⟩ u := by
  classical
  unfold simClass
  constructor
  · intro haimg
    rcases Finset.mem_image.mp haimg with ⟨v, hv, rfl⟩

    have hsim : S.sim v u := (S.mem_simClassElem u v).1 hv
    exact ⟨v.property, hsim⟩
  · intro h
    rcases h with ⟨ha, hsim⟩
    let v : S.Elem := ⟨a, ha⟩
    have hv : v ∈ S.simClassElem u := (S.mem_simClassElem u v).2 hsim
    exact Finset.mem_image.mpr ⟨v, hv, rfl⟩

-------------------------------
----ここからIdeal関連

/-- S に対応する order-ideal family を ground 型 `α` 上の `SetFamily` として与える。 -/
--FuncSetupからidealFaimilyが定理できると便利なので定義だけ与える。
--と思ったが、FuncSetupでIdealを使ったものを集めたファイルがないので、分離するとよいかも。
noncomputable def idealFamily (S : FuncSetup α) : SetFamily α :=
  SetFamily.orderIdealFamily (le := leOn S) (V := S.ground)

@[simp] lemma sets_iff_isOrderIdeal
    (S : FuncSetup α) {I : Finset α} :
    (S.idealFamily).sets I ↔ SetFamily.isOrderIdealOn (S.leOn) S.ground I := Iff.rfl

/-- `S.ground` は `idealFamily` の edge（＝理想）である。 -/
lemma ground_mem_ideal_edge (S : FuncSetup α) :
  S.ground ∈ (S.idealFamily).edgeFinset := by
  classical
  -- `S.ground` が order ideal であることを直展開で示す
  have hIdeal : SetFamily.isOrderIdealOn (S.leOn) S.ground S.ground := by
    dsimp [SetFamily.isOrderIdealOn]
    constructor
    · intro x hx; exact hx
    · intro x hx y hy _; exact hy
  -- sets ↔ isOrderIdealOn で写してから、edgeFinset へ
  have hSets : (S.idealFamily).sets S.ground :=
    (S.sets_iff_isOrderIdeal).2 hIdeal
  exact (SetFamily.mem_edgeFinset_iff_sets (F := S.idealFamily) (A := S.ground)).2 hSets

/-- `∅` も `idealFamily` の edge である。 -/
lemma empty_mem_ideal_edge (S : FuncSetup α) :
  (∅ : Finset α) ∈ (S.idealFamily).edgeFinset := by
  classical
  -- 空集合は自明に order ideal
  have hIdeal : SetFamily.isOrderIdealOn (S.leOn) S.ground (∅ : Finset α) := by
    dsimp [SetFamily.isOrderIdealOn]
    constructor
    · intro x hx; cases hx
    · intro x hx; cases hx
  have hSets : (S.idealFamily).sets (∅ : Finset α) :=
    (S.sets_iff_isOrderIdeal).2 hIdeal
  exact (SetFamily.mem_edgeFinset_iff_sets (F := S.idealFamily) (A := ∅)).2 hSets

/-- `idealFamily` の `edgeFinset` は空でない。 -/
lemma ideal_edge_nonempty (S : FuncSetup α) :
  (S.idealFamily).edgeFinset.Nonempty := by
  classical
  exact ⟨S.ground, ground_mem_ideal_edge S⟩

/-- よって `numHyperedges ≥ 1`。 -/
lemma numHyperedges_ge_one (S : FuncSetup α) :
  1 ≤ (S.idealFamily).numHyperedges := by
  classical
  -- `numHyperedges = card edgeFinset`
  have hpos : 0 < (S.idealFamily).edgeFinset.card :=
    Finset.card_pos.mpr (ideal_edge_nonempty S)
  -- `0 < n` から `1 ≤ n`
  exact Nat.succ_le_of_lt hpos

/-- `ground ≠ ∅` なら、`∅` と `ground` がどちらも edge でしかも異なるので card ≥ 2。 -/
lemma numHyperedges_ge_two
  (S : FuncSetup α) (hne : S.ground.Nonempty) :
  2 ≤ (S.idealFamily).numHyperedges := by
  classical
  let P : Finset (Finset α) := insert S.ground ({∅} : Finset (Finset α))
  have hPsub : P ⊆ (S.idealFamily).edgeFinset := by
    intro A hA
    rcases Finset.mem_insert.mp hA with rfl | hA0
    · exact ground_mem_ideal_edge S
    · have : A = (∅ : Finset α) := Finset.mem_singleton.mp hA0; subst this
      exact empty_mem_ideal_edge S
  have hg_ne : S.ground ≠ (∅ : Finset α) :=
    Finset.nonempty_iff_ne_empty.mp hne
  have hPcard : 2 = P.card := by
    have : S.ground ∉ ({∅} : Finset (Finset α)) := by
      intro h; exact hg_ne (Finset.mem_singleton.mp h)
    simp_all only [ne_eq, Finset.mem_singleton, not_false_eq_true, Finset.card_insert_of_notMem, Finset.card_singleton,
    Nat.reduceAdd, P]
  -- `card_le_card` で押す
  have := Finset.card_le_card hPsub
  simpa [SetFamily.numHyperedges, hPcard] using this

lemma simClass_subset_of_contains
    (S : FuncSetup α) {u : S.Elem} {I : Finset α}
    (hI : (S.idealFamily).sets I) (huI : u.1 ∈ I) :
    S.simClass u ⊆ I := by
  classical
  -- isOrderIdealOn に展開
  have hIdeal : SetFamily.isOrderIdealOn (S.leOn) S.ground I := by
    -- `[simp] lemma sets_iff_isOrderIdeal` が `Iff.rfl` なので書換えだけで OK
    -- `rw` で潰す（`simpa using` は使わない）
    change SetFamily.isOrderIdealOn (S.leOn) S.ground I
    exact (S.sets_iff_isOrderIdeal).1 hI
  -- 以降：U の元 a を任意に取り、I に属することを示す
  intro a haU
  rcases (S.mem_simClass_iff u).1 haU with ⟨ha, hsim⟩
  -- `a ≤ u` を取り出す
  have h_le : S.le ⟨a, ha⟩ u := hsim.1
  -- `leOn a u.1` に持ち上げ
  have h_leOn : S.leOn a u.1 := by
    -- `leOn_iff_subtype` を使う
    have : S.leOn a u.1 ↔ S.le ⟨a, ha⟩ u :=
      S.leOn_iff_subtype (a := a) (b := u.1) ha u.property
    exact this.mpr h_le
  -- isOrderIdealOn の下方閉により `a ∈ I`
  have hI_sub : I ⊆ S.ground := hIdeal.1
  have hxI : u.1 ∈ I := huI
  --have hxV : u.1 ∈ S.ground := hI_sub hxI
  -- 下方閉：`x∈I, y∈V, leOn y x → y∈I`
  have := hIdeal.2 (x := u.1) hxI (y := a) (by exact ha) h_leOn
  exact this

--下で使っている。単なるidealが下に閉じているという性質のleOn版か。今はそとから参照されてないので、private。
private lemma mem_of_le_of_mem_inIdeal
  (S : FuncSetup α) {I : Finset S.Elem}
  (hIdeal : SetFamily.isOrderIdealOn S.leOn S.ground (S.coeFinset I))
  {x y : S.Elem}
  (hleOn : S.leOn (x : α) (y : α)) (hy : y ∈ I) :
  x ∈ I := by
  have hyGround : (y : α) ∈ S.ground := y.property
  -- y∈I → (y:α)∈coeFinset I
  have hyIn : (y : α) ∈ S.coeFinset I :=
    (S.mem_coeFinset_iff (I := I) (a := y) hyGround).2 hy
  -- downward closed で (x:α)∈coeFinset I
  have hxIn : (x : α) ∈ S.coeFinset I :=
    hIdeal.2 (x := (y : α)) hyIn (y := (x : α)) (by exact x.property) hleOn
  -- 逆向きで x∈I に戻す
  have : ∃ z ∈ I, (z : α) = (x : α) := (S.mem_coeFinset_val_iff).1 hxIn
  rcases this with ⟨z, hzI, hz⟩
  cases z with
  | mk z hzground =>
    cases x with
    | mk x hxground =>
      cases hz
      simpa using hzI


noncomputable def Iy (S : FuncSetup α) (y : S.Elem) : Finset S.Elem :=
  S.ground.attach.filter (fun z : S.Elem => S.le z y)

-- 目標： hb : b ∈ S.ground, hleOn : S.leOn b a, haGround : a ∈ S.coeFinset Iy
--       から b ∈ S.coeFinset Iy を出す
--xとyに大小関係があれば、yを含むidealは、xも含む。重要補題。
--基礎補題を集めたファイルを作って分離してもよい。

lemma le_iff_forall_ideal_mem
  (S : FuncSetup α) (x y : S.Elem) :
  S.le x y ↔
    (∀ I : Finset S.Elem,
      (S.idealFamily).sets (S.coeFinset I) → y ∈ I → x ∈ I) := by
  constructor
  · -- (→) : `x ≤ y` なら、任意のイデアル I で `y ∈ I → x ∈ I`
    intro hxy I hI hyI
    have hIdeal :
        SetFamily.isOrderIdealOn (S.leOn) S.ground (S.coeFinset I) :=
      (S.sets_iff_isOrderIdeal).1 hI
    have hy' : (y.1 : α) ∈ S.coeFinset I := by

      exact (mem_coeFinset_iff S (I:=I) (a:=y.1) (ha:=y.2)).2 hyI
    have hx' : (x.1 : α) ∈ S.coeFinset I := by
      have hleOn : S.leOn x.1 y.1 := by exact (S.le_iff_leOn_val x y).mp hxy--S.le_to_leOn hxy
      simp_all only [ FuncSetup.mem_coeFinset, Subtype.exists, exists_and_right,
         exists_eq_right, Subtype.coe_eta, Finset.coe_mem, exists_const]
      exact S.mem_of_le_of_mem_inIdeal hIdeal hleOn  hyI

    simp_all only [FuncSetup.mem_coeFinset, Subtype.exists, exists_and_right,
    exists_eq_right, Subtype.coe_eta, Finset.coe_mem, exists_const]

  ·
    intro hAll

    let Iy : Finset S.Elem :=
      S.ground.attach.filter (fun z => S.le z y)
    have hyIy : y ∈ Iy := by

      have hy₀ : y ∈ S.ground.attach := by
        exact Finset.mem_attach S.ground y
      have : S.le y y := S.le_refl y
      simpa [Iy] using Finset.mem_filter.mpr ⟨hy₀, this⟩

    have hIy_sets : (S.idealFamily).sets (S.coeFinset Iy) := by

      have : SetFamily.isOrderIdealOn (S.leOn) S.ground (S.coeFinset Iy) := by

        refine And.intro ?dc ?subset
        ·
          simp_all only [Finset.mem_filter, Finset.mem_attach, true_and, Iy]
          intro z hz
          simp_all only [FuncSetup.mem_coeFinset, Finset.mem_filter, Finset.mem_attach, true_and, Subtype.exists,
            ]
          simp_all only [FuncSetup.le_iff_leOn_val, FuncSetup.sets_iff_isOrderIdeal, exists_and_left, exists_prop,
            exists_eq_right_right]
        ·
          intro a haIn

          rcases (S.mem_coeFinset_val_iff).1 haIn with ⟨z, hzIy, hz⟩

          have hzInAttach : z ∈ S.ground.attach :=
            (Finset.mem_filter).1 hzIy |>.left

          have hzGround : z.1 ∈ S.ground := by
            subst hz
            simp_all only [ Finset.mem_filter, Finset.mem_attach, true_and,
              FuncSetup.mem_coeFinset, Subtype.exists, Finset.coe_mem, Iy]


          have : a ∈ S.ground := by

            exact Eq.ndrec hzGround hz

          intro y_1 a_1 a_2
          subst hz
          simp_all only [Finset.mem_attach, FuncSetup.mem_coeFinset, Subtype.exists, Finset.coe_mem,Iy]
          simp_all
          apply S.leOn_trans
          exact a_2
          exact hzIy

      simp_all only [Finset.mem_filter, Finset.mem_attach, true_and, Iy]
      exact this

    have hxIy : x ∈ Iy := hAll Iy hIy_sets hyIy
    have hxLe : S.le x y := (Finset.mem_filter.mp hxIy).2
    exact hxLe


----Something that comes with ideal and parallel at the same time.

/-- 論文 Lemma 3.3：
`u, v` が同じ同値類（S.sim）であることと，`idealFamily S` における parallel が同値。 -/
--この関係はfunctionalでなくても成り立つはずであるがここではfunctionalなものに対して証明している。
theorem parallel_iff_sim
  (S : FuncSetup α) (u v : S.Elem) :
  (S.idealFamily).Parallel u v ↔ FuncSetup.sim S u v := by
  constructor
  · intro hPar

    have hUV :
      ∀ I : Finset S.Elem,
        (S.idealFamily).sets (S.coeFinset I) →
        (u ∈ I ↔ v ∈ I) := by
      dsimp [SetFamily.Parallel, FuncSetup.coeFinset] at *
      intro I hI
      constructor
      · intro hu
        have : (Finset.image (fun x => ↑x) I) ∈ {A | S.idealFamily.sets A ∧ ↑u ∈ A} :=
        by
          rw [@Set.mem_setOf_eq]
          constructor
          · exact hI
          · simp_all only [ Finset.mem_image, Subtype.exists, exists_and_right, exists_eq_right,
            Subtype.coe_eta, Finset.coe_mem, exists_const]
        simp_all only [ Set.mem_setOf_eq, Finset.mem_image, Subtype.exists, exists_and_right,
          exists_eq_right, Subtype.coe_eta, Finset.coe_mem, exists_const, true_and]
      · intro hv
        have : (Finset.image (fun x => ↑x) I) ∈ {A | S.idealFamily.sets A ∧ ↑v ∈ A} :=
        by
          rw [@Set.mem_setOf_eq]
          constructor
          · exact hI
          · simp_all only [Finset.mem_image, Subtype.exists, exists_and_right, exists_eq_right,
            Subtype.coe_eta, Finset.coe_mem, exists_const]
        rw [←hPar] at this
        rw [Set.mem_setOf_eq] at this
        simp_all only [Finset.mem_image, Subtype.exists, exists_and_right, exists_eq_right,
          Subtype.coe_eta, Finset.coe_mem, exists_const]

    have huv : S.le u v := by
      let lifim := (le_iff_forall_ideal_mem S u v).mpr
      apply lifim
      intro I a a_1
      simp_all only [SetFamily.Parallel]

    have hvu : S.le v u := by
      let lifim := (le_iff_forall_ideal_mem S v u).mpr
      apply lifim
      intro I a a_1
      simp_all only [SetFamily.Parallel]
    dsimp [FuncSetup.sim]
    exact ⟨huv, hvu⟩

  · intro hSim
    rcases hSim with ⟨huv, hvu⟩
    dsimp [SetFamily.Parallel] at *
    ext J

    constructor
    swap
    · intro hu

      rw [@Set.mem_setOf_eq]
      rw [@Set.mem_setOf_eq] at hu
      constructor
      · exact hu.1
      · have : J ⊆ S.ground := by
          exact S.idealFamily.inc_ground hu.1

        let lifim := (le_iff_forall_ideal_mem S u v).mp huv (S.liftFinset J this)
        rw [S.coeFinset_liftFinset] at lifim
        specialize lifim hu.1
        simp_all only [FuncSetup.le_iff_leOn_val, FuncSetup.sets_iff_isOrderIdeal, FuncSetup.mem_liftFinset_iff, forall_const]

    · intro hv
      rw [@Set.mem_setOf_eq]
      rw [@Set.mem_setOf_eq] at hv
      constructor
      · exact hv.1
      · have : J ⊆ S.ground := by
          exact S.idealFamily.inc_ground hv.1

        let lifim := (le_iff_forall_ideal_mem S v u).mp hvu (S.liftFinset J this)
        rw [S.coeFinset_liftFinset] at lifim
        specialize lifim hv.1
        simp_all only [FuncSetup.le_iff_leOn_val, FuncSetup.sets_iff_isOrderIdeal, FuncSetup.mem_liftFinset_iff, forall_const]

-- 既存: parallel_iff_sim (S : FuncSetup α) (u v : S.Elem)
-- をそのまま使い、必要なら underlying へ落とすだけ。
--そとから使っている。Rare.leanでもIdealTraceでも。
@[simp]
lemma parallel_of_sim_coe (S : FuncSetup α) {x y : S.Elem}
    (h : FuncSetup.sim S x y) :
    (S.idealFamily).Parallel (x : α) (y : α) := by
  have hxy : (S.idealFamily).Parallel x y :=
    (parallel_iff_sim S x y).2 h
  exact hxy

--FuncSetupを使っているので、SetFamilyには移せない。
--`simClass u` と `ParallelClass F u` の同値性。
--そとからも使っている。
@[simp]
lemma simClass_eq_parallelClass
  (S : FuncSetup α) (u : S.Elem) :
  S.simClass u = (S.idealFamily).ParallelClass (u : α) := by
  classical
  ext a; constructor
  · intro ha
    rcases (S.mem_simClass_iff u).1 ha with ⟨ha', hsim⟩
    have hpar : (S.idealFamily).Parallel (u : α) a :=
      (S.parallel_iff_sim u ⟨a, ha'⟩).2 (S.sim_symm hsim)
    exact Finset.mem_filter.mpr ⟨ha', hpar⟩
  · intro ha
    rcases Finset.mem_filter.1 ha with ⟨ha', hpar⟩
    have hsim : S.sim u ⟨a, ha'⟩ := (S.parallel_iff_sim u ⟨a, ha'⟩).1 hpar
    exact (S.mem_simClass_iff u).2 ⟨ha', S.sim_symm hsim⟩

--下で使っている。
private lemma mem_simClass_of_sim
  (S : FuncSetup α) {u v : S.Elem} (h : S.sim u v) :
  (v : α) ∈ S.simClass u :=
  (S.mem_simClass_iff u).2 ⟨v.2, S.sim_symm h⟩

--そとからも使っている。
lemma eq_of_sim_of_all_classes_card_one
  (S : FuncSetup α)
  (h1 : ∀ C ∈ (S.idealFamily).classSet , C.card = 1) :
  ∀ {u v : S.Elem}, S.sim u v → u = v := by
  classical
  intro u v hsim
  have hv_mem : (v : α) ∈ S.simClass u := mem_simClass_of_sim S hsim
  have hu_mem : (u : α) ∈ S.simClass u := mem_simClass_of_sim S (S.sim_refl u)
  have hC :
      (S.idealFamily).ParallelClass (u : α) ∈ (S.idealFamily).classSet := by
    unfold SetFamily.classSet
    exact Finset.mem_image.mpr ⟨(u : α), u.2, rfl⟩
  have hEq := simClass_eq_parallelClass S u
  have hcard_one : (S.simClass u).card = 1 := by
    have hc := h1 _ hC
    simp_all only [SetFamily.mem_ParallelClass_iff, Finset.coe_mem, SetFamily.Parallel, sets_iff_isOrderIdeal, true_and,
    and_self]
  rcases Finset.card_eq_one.1 hcard_one with ⟨a, ha⟩
  have hv := by rw [ha] at hv_mem; exact Finset.mem_singleton.1 hv_mem
  have hu := by rw [ha] at hu_mem; exact Finset.mem_singleton.1 hu_mem
  apply Subtype.ext
  exact Eq.trans hu (Eq.symm hv)

--In non-trivial classes, there will always be parallel partners.
--Reduction.lean, used as NDS proof.
lemma exists_parallel_partner_from_nontrivial
    (S : FuncSetup α) {u : S.Elem}
    (hx : S.nontrivialClass u) :
    ∃ v : α, v ≠ u.1 ∧ v ∈ S.ground ∧ (S.idealFamily).Parallel u.1 v := by
  classical
  rcases hx with ⟨y, hneq, hsim⟩
  refine ⟨(y : α), ?hne, y.property, ?hpar⟩
  · -- y ≠ u から値の不等号へ
    intro h
    apply hneq
    apply Subtype.ext
    exact h
  · -- sim ⇒ parallel
    exact S.parallel_of_sim_coe hsim

-----------------------------------------------------------
------fのiterationの話---------------------------------
-----idealよりも前においてもいいかも。

section IterateRTG  --sectionを区切る意味があるのか？
variable {α : Type u} (f : α → α) --Type *だったがType uに変更。

/-- 「反復で到達できる」写像反復。 -/
--traceFunctionalでつかっているみたい。使わずに直接書いているところも多数。
def iter (k : Nat) : S.Elem → S.Elem :=
  Nat.iterate S.f k

--SetFamilyもFuncSetupも出てこない、一般的な補題は、Generalに置くべきかもしれない。
--ただし、fが出てきているので、実質的にFuncSetupの枠組み。stepRelもFuncSetupの枠組みで定義した方がいいかも。
-- 関係 R_f : x R_f y ↔ f x = y
def stepRel : α → α → Prop := fun x y => f x = y

private lemma iterate_commute_right (f : α → α) :
    ∀ n x, Nat.iterate f n (f x) = f (Nat.iterate f n x) := by
  intro n
  induction' n with n ih
  · intro x; rfl
  · intro x
    -- iterate (n+1) (f x) = iterate n (f (f x))
    have h1 : Nat.iterate f (n+1) (f x) = Nat.iterate f n (f (f x)) := by
      -- 定義展開
      simp [Nat.iterate]
    -- 右側を `ih` で一段ほどく
    have h2 : Nat.iterate f n (f (f x)) = f (Nat.iterate f n (f x)) := by
      -- `ih` を `x := f x` に適用
      simpa using ih (f x)
    -- さらに `ih` で `(f^[n]) (f x)` を置換
    have h3 : f (Nat.iterate f n (f x)) = f (f (Nat.iterate f n x)) := by
      -- `ih x : (f^[n]) (f x) = f ((f^[n]) x)` を `f ∘ _` の中で使用
      simpa using congrArg f (ih x)
    -- 仕上げ：定義で `(f^[n+1]) x = (f^[n]) (f x)` に戻す
    calc
      Nat.iterate f (n+1) (f x)
          = Nat.iterate f n (f (f x)) := h1
      _   = f (Nat.iterate f n (f x)) := h2
      _   = f (f (Nat.iterate f n x)) := h3
      _   = f (Nat.iterate f (n+1) x) := by
              -- `Nat.iterate f (n+1) x = Nat.iterate f n (f x)`
              simp [Nat.iterate]
              simp_all only [Function.iterate_succ, Function.comp_apply]

/-- 主要補題：`ReflTransGen (stepRel f) x y ↔ ∃ k, (f^[k]) x = y` -/
--外部ファイルからも多数引用。le_iff_exists_iterと内容が被っている。
theorem reflTransGen_iff_exists_iterate
    (f : α → α) {x y : α} :
    Relation.ReflTransGen (stepRel f) x y ↔ ∃ k : ℕ, Nat.iterate f k x = y := by
  constructor
  ·
    intro h
    induction h with
    | @refl  =>
        exact ⟨0, rfl⟩
    | @tail  b c hxb hbc ih =>
        rcases ih with ⟨k, hk⟩
        refine ⟨k + 1, ?_⟩
        calc
          Nat.iterate f (k+1) x
              = Nat.iterate f k (f x) := by
                  simp [Nat.iterate]
          _   = f (Nat.iterate f k x) := iterate_commute_right f k x
          _   = f b := by exact congrArg f hk
          _   = c := hbc
  ·
    intro h
    rcases h with ⟨k, hk⟩

    have hx_to_iter : Relation.ReflTransGen (stepRel f) x (Nat.iterate f k x) := by
      revert x
      induction' k with k ih
      · intro x;
        intro hk
        subst hk
        simp_all only [Function.iterate_zero, id_eq]
        rfl

      · intro x
        have step : stepRel f (Nat.iterate f k x) (Nat.iterate f (k+1) x) := by
          have h1 : Nat.iterate f (k+1) x = Nat.iterate f k (f x) := by
            simp [Nat.iterate]
          have h2 : Nat.iterate f k (f x) = f (Nat.iterate f k x) :=
            iterate_commute_right f k x
          exact (Eq.trans (Eq.symm h2) (Eq.symm h1))
        exact fun hk => Relation.ReflTransGen.head rfl (ih hk)

    have : Relation.ReflTransGen (stepRel f) x y := by
      show Relation.ReflTransGen (stepRel f) x y
      exact (by
        have hk' : y = Nat.iterate f k x := hk.symm
        simpa [hk'] using hx_to_iter
      )
    exact this

/-- 論文 Lemma 2.2：
`x ≤ y` ↔ ある `k ≥ 0` で `f^[k] x = y`。 -/
--It is duplicated just like reflTransGen_iff_exists_iterate.Maybe it's better to unify it.
--However, since the arguments are different, a simple replacement might not work.
lemma le_iff_exists_iter {α} [DecidableEq α] (S : FuncSetup α) (x y : S.Elem) :
    S.le x y ↔ ∃ k : Nat, S.iter k x = y := by
  dsimp [FuncSetup.le]
  unfold FuncSetup.cover
  exact reflTransGen_iff_exists_iterate (fun xx => S.f xx)

-- まず小補題： g u = u なら g^[n] u = u
private lemma iterate_fixpoint {β} (g : β → β) (u : β) (n : ℕ) (hu : g u = u) :
    Nat.iterate g n u = u := by
  induction' n with n ih
  · simp [Nat.iterate]
  ·
    have : Nat.iterate g (n + 1) u = Nat.iterate g n (g u) := by
      simp [Nat.iterate]
    have : Nat.iterate g n (g u) = u := by
      have : Nat.iterate g n (g u) = Nat.iterate g n u := by
        simp [hu]
      simp_all only
    simp [Nat.iterate, hu, ih]

/-- イテレートは単調：`i ≤ j` なら `(f^[i]) x ≤ (f^[j]) x`。 -/
--le_iff_exists_iterと違って、自然数の大小
lemma le_between_iter {α} [DecidableEq α]  (S : FuncSetup α) (x : S.Elem) :
  ∀ {i j : ℕ}, i ≤ j → S.le ((S.f^[i]) x) ((S.f^[j]) x)
| i, j, hij => by

  rcases Nat.exists_eq_add_of_le hij with ⟨d, rfl⟩
  induction d with
  | zero =>
      exact Relation.ReflTransGen.refl
  | succ d ih =>
      -- 1歩： (f^[i+d]) x ⋖ (f^[i+d+1]) x
      have hstep :
          S.cover ((S.f^[i + d]) x) ((S.f^[i + d + 1]) x) := by
        dsimp [FuncSetup.cover]
        exact (Function.iterate_succ_apply' S.f (i + d) x).symm
      simp at ih
      refine Relation.ReflTransGen.tail ?_ hstep
      convert ih
      dsimp [FuncSetup.cover]
      dsimp [FuncSetup.leOn]
      dsimp [FuncSetup.le]
      simp_all only [le_add_iff_nonneg_right, zero_le, Function.iterate_succ, Function.comp_apply, Subtype.coe_eta,
        Finset.coe_mem, exists_const]


end IterateRTG  --これをどこに置くかで後ろのalphaに影響。

--Parallel関係かつIteration関係
--直接的にはidealも出てこない。
omit [DecidableEq α] in
lemma maximal_of_nontrivialClass_lemma
    (f : α → α) [Fintype α] {u v : α}
    (huv : Relation.ReflTransGen (stepRel f) u v ∧
           Relation.ReflTransGen (stepRel f) v u)
    (hneq : u ≠ v) :
    (∀ x, Relation.ReflTransGen (stepRel f) u x →
          Relation.ReflTransGen (stepRel f) x u) := by
  intro x hux
  rcases (reflTransGen_iff_exists_iterate f).1 huv.1 with ⟨k, hk⟩
  rcases (reflTransGen_iff_exists_iterate f).1 huv.2 with ⟨ℓ, hℓ⟩
  rcases (reflTransGen_iff_exists_iterate f).1 hux   with ⟨m, hm⟩

  have hL' : Nat.iterate f (ℓ + k) u = u := by
    have h1 : Nat.iterate f (ℓ + k) u
                = Nat.iterate f ℓ (Nat.iterate f k u) :=
      Function.iterate_add_apply f ℓ k u
    have h2 : Nat.iterate f ℓ (Nat.iterate f k u)
                = Nat.iterate f ℓ v := by
      rw [hk]
    exact Eq.trans (Eq.trans h1 h2) hℓ

  let L := ℓ + k
  have hL : Nat.iterate f L u = u := by
    change Nat.iterate f (ℓ + k) u = u
    exact hL'

  let t : ℕ := L * (m + 1) - m

  have Lpos : 0 < L := by
    by_contra hLz
    have : L = 0 := le_antisymm (le_of_not_gt hLz) (Nat.zero_le _)

    apply False.elim
    subst hℓ hm
    simp_all only [not_lt, Nat.le_zero_eq, Nat.add_eq_zero, add_zero, Function.iterate_zero, id_eq, and_self, ne_eq,
      not_true_eq_false, L]

  have hmle : m ≤ L * (m + 1) := by
    have h1 : m ≤ m + 1 := Nat.le_succ m
    have h2 : m + 1 ≤ L * (m + 1) := by
      exact Nat.le_mul_of_pos_left (m + 1) Lpos
    exact Nat.le_trans h1 h2

  have ht_add : t + m = L * (m + 1) := by
    change (L * (m + 1) - m) + m = L * (m + 1)
    exact Nat.sub_add_cancel hmle

  have h_iter_eq : Nat.iterate f t x = u := by
    have base := Eq.symm (Function.iterate_add_apply f t m u)
    have base' : Nat.iterate f t x = Nat.iterate f (t + m) u := by
      have tmp := base

      have tmp' := tmp

      clear tmp
      calc
        Nat.iterate f t x
            = Nat.iterate f t (Nat.iterate f m u) := by
                rw [←hm]
        _   = Nat.iterate f (t + m) u := base
    have h_right1 : Nat.iterate f (t + m) u = Nat.iterate f (L * (m + 1)) u := by
      have : t + m = L * (m + 1) := ht_add

      subst hℓ hm
      simp_all only [Nat.sub_add_cancel, ne_eq, L, t]

    have h_mul : Nat.iterate f (L * (m + 1)) u
                  = Nat.iterate (Nat.iterate f L) (m + 1) u := by
      let fi := Function.iterate_mul f L (m + 1)
      exact congrFun fi u

    have h_fix : Nat.iterate (Nat.iterate f L) (m + 1) u = u :=
      iterate_fixpoint (Nat.iterate f L) u (m + 1) hL

    calc
      Nat.iterate f t x
          = Nat.iterate f (t + m) u := base'
      _   = Nat.iterate f (L * (m + 1)) u := by
              have : t + m = L * (m + 1) := ht_add
              exact by
                rw [this]
      _   = Nat.iterate (Nat.iterate f L) (m + 1) u := h_mul
      _   = u := by
              exact h_fix

  exact (reflTransGen_iff_exists_iterate f).2 ⟨t, h_iter_eq⟩

--パラレルな元であれば、uからxにいければxからuにいける。
--極大性は使ってない。parallel_iff_simは使う立場。
--nontrivialClassの仮定を使って書き換えられそう。
--nds_monotone_under_traceで利用されている。
--この言明には、functionalという仮定が必要。
theorem maximal_of_parallel_nontrivial
    (S : FuncSetup α) {u v : α}
    (hu : u ∈ S.ground) (hv : v ∈ S.ground)
    (hpar : (S.idealFamily).Parallel u v)
    (hneq : u ≠ v) :
    ∀ x : S.Elem,
      Relation.ReflTransGen (stepRel S.f) (S.toElem! hu) x →
      Relation.ReflTransGen (stepRel S.f) x (S.toElem! hu) := by
  classical
  -- parallel ⇒ sim
  have hsim : S.sim (S.toElem! hu) (S.toElem! hv) :=
    (S.parallel_iff_sim (S.toElem! hu) (S.toElem! hv)).1 hpar
  -- sim ⇒ 両向きの ReflTransGen(stepRel S.f)
  have huv : Relation.ReflTransGen (stepRel S.f) (S.toElem! hu) (S.toElem! hv) := by
    -- le → ∃k → ReflTransGen
    have hle := hsim.1
    rcases (S.le_iff_exists_iter (S.toElem! hu) (S.toElem! hv)).1 hle with ⟨k, hk⟩
    exact (reflTransGen_iff_exists_iterate S.f).2 ⟨k, hk⟩
  have hvu : Relation.ReflTransGen (stepRel S.f) (S.toElem! hv) (S.toElem! hu) := by
    have hle := hsim.2
    rcases (S.le_iff_exists_iter (S.toElem! hv) (S.toElem! hu)).1 hle with ⟨k, hk⟩
    exact (reflTransGen_iff_exists_iterate S.f).2 ⟨k, hk⟩
  have hneq' : (S.toElem! hu) ≠ (S.toElem! hv) := by
    intro h; exact hneq (congrArg Subtype.val h)
  -- 一般補題を S.Elem, f := S.f に適用
  have hmax :=
    maximal_of_nontrivialClass_lemma
      (α := S.Elem) (f := S.f)
      (u := S.toElem! hu) (v := S.toElem! hv)
      ⟨huv, hvu⟩ hneq'
  -- 仕上げ
  intro x hx; exact hmax x hx


end FuncSetup

end AvgRare

------------------------

/-
/-- 逆に、`v` が `u` のクラスに入るなら `sim u v`。 -/
--つかってないかも。
lemma sim_of_mem_simClass
  (S : FuncSetup α) {u : S.Elem} {a : α}
  (ha : a ∈ S.ground) (hmem : a ∈ S.simClass u) :
  S.sim ⟨a, ha⟩ u := by
  classical
  have := (S.mem_simClass_iff u).mp hmem
  -- this : ∃ ha', S.sim ⟨a, ha'⟩ u
  rcases this with ⟨_, hsim⟩
  -- ground 証明が違っても Subtype.ext で同一視
  -- ⟨a, ha⟩ と ⟨a, _⟩ は値が同じなので transport で書き換え
  -- 実際には値部分が同じなので hsim をそのまま使えます
  exact hsim
-/

/- ground 上の比較を subtype に引き上げる便利関数。 -/
--def toElem! (S : FuncSetup α) {x : α} (hx : x ∈ S.ground) : S.Elem := ⟨x, hx⟩

----使ってないもの。


/-（使い勝手用）非自明同値類のとき，後継 `f u` を
    「u と異なる ground の元」として取り出す形。 -/
-- hvは暗黙につかっている。
--現状使ってない。
/-
lemma exists_succ_partner_of_nontrivial {α : Type u} [DecidableEq α]
    (S : FuncSetup α) {u : α} (hu : u ∈ S.ground)
    (h : S.nontrivialClass (S.toElem! hu)) :
    ∃ (v : α) (_ : v ∈ S.ground), v ≠ u := by
  classical
  let ue : S.Elem := ⟨u, hu⟩
  let ve : S.Elem := S.f ue
  refine ⟨ve.1, ve.2, ?_⟩
  -- `ve ≠ ue` を `Subtype.ext` で基の α に落とす
  have hne : ve ≠ ue := S.f_ne_of_nontrivialClass (u := ue) h
  intro hval
  apply hne
  apply Subtype.ext
  exact hval

-- 部分型の同値 ≠ から基底の ≠ を取り出す補助。現状使ってない。
private lemma ne_val_of_ne {x y : {a // a ∈ S.ground}} (h : x ≠ y) : x.1 ≠ y.1 := by
  intro hval
  apply h
  apply Subtype.ext
  exact hval

-/
