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

-- The following two are moved to FuncPoset.
def has_le_antisymm  : Prop :=
∀ {x y : S.Elem}, (S.le x y) → (S.le y x) → x = y



lemma cover_to_le {x y : S.Elem} (h : S.cover x y) : S.le x y := by
  exact Relation.ReflTransGen.single h

/-- The image of `cover` from the same element is unique -/
-- Used below.
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

/-- Utility to create `S.Elem` from an element `x : α` in ground and its proof. -/
def toElem! {x : α} (hx : x ∈ S.ground) : S.Elem := ⟨x, hx⟩

@[simp] lemma toElem!_val {x : α} (hx : x ∈ S.ground) :
    (S.toElem! hx).1 = x := rfl
@[simp] lemma toElem!_mem {x : α} (hx : x ∈ S.ground) :
    (S.toElem! hx).2 = hx := rfl

-- Round trip of toElem! (adding @[simp] would make later rewrites easier).
-- Used.
@[simp] lemma toElem!_coe (S : FuncSetup α) (x : S.Elem) :
    S.toElem! x.property = x := by
  cases x with
  | mk x hx => rfl

-- From S.Elem inequality to underlying
-- Used in one place.
lemma coe_ne_of_ne {S : FuncSetup α} {x y : S.Elem} (h : x ≠ y) :
    (x : α) ≠ (y : α) := by
  intro hxy
  apply h
  apply Subtype.ext
  exact hxy

/-- `leOn S y x` : For elements `y, x : α` on the ground,
using "existence" to state that `S.le ⟨y,hy⟩ ⟨x,hx⟩` holds on the subtype `S.Elem` of S. -/
def leOn (S : FuncSetup α) (y x : α) : Prop :=
  ∃ (hy : y ∈ S.ground) (hx : x ∈ S.ground),
      FuncSetup.le S ⟨y, hy⟩ ⟨x, hx⟩

--Frequently used
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
⟨hx, hx, S.le_refl ⟨x, hx⟩⟩

lemma leOn_trans (S : FuncSetup α) {y x z : α}
  (h₁ : S.leOn y x) (h₂ : S.leOn x z) :
  S.leOn y z := by
  rcases h₁ with ⟨hy, hx, h_yx⟩
  rcases h₂ with ⟨hx', hz, h_xz⟩
  have h_yx' : S.le ⟨y, hy⟩ ⟨x, hx'⟩ := by
    have e : (⟨x, hx⟩ : S.Elem) = ⟨x, hx'⟩ := Subtype.ext rfl
    rwa [e]
  exact ⟨hy, hz, S.le_trans h_yx' h_xz⟩

--Same as leOn_iff_subtype
lemma leOn_iff (S : FuncSetup α)
  {a b : α} (hb : b ∈ S.ground) (ha : a ∈ S.ground) :
  S.leOn b a ↔ S.le ⟨b, hb⟩ ⟨a, ha⟩ := by
  unfold FuncSetup.leOn
  simp_all only [exists_true_left]

-- Bridge between subtype comparison and ground comparison
-- (If S.le were "S.leOn lifted to subtype", this could be proven by definitional equality)
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
--------------------hyperedge-related
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
    -- From `z : S.Elem` and `z.1 = a`, obtain `z = ⟨a,ha⟩`
    have : z = ⟨a, ha⟩ := Subtype.ext (by simpa [Subtype.ext] using congrArg id hz)
    subst this
    simp_all only [FuncSetup.mem_coeFinset, Subtype.exists, exists_and_right, exists_eq_right, exists_const]
  · intro hz
    -- The reverse direction is just the definition of image
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
    -- Therefore (z : α) = t.1 ∈ J
    have : (z : α) = t.1 := by cases z; cases t; cases hmap; rfl
    exact this ▸ t.2
  · intro hz
    refine Finset.mem_map.mpr ?_
    refine ⟨⟨z.1, hz⟩, ?_, ?_⟩
    · exact Finset.mem_attach _ _
    · cases z; rfl

/-- Target lemma: `coeFinset ∘ liftFinset = id` (assuming `J ⊆ ground`) -/
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
    -- Rewrite with z.1 = a
    subst hz
    simp_all only [mem_liftFinset_iff, FuncSetup.mem_coeFinset, Subtype.exists, exists_and_left, exists_prop,
    exists_eq_right_right]

  · intro haJ
    -- a ∈ J → some z=⟨a, hJ haJ⟩ is in lift and a is in its image
    have hz : (⟨a, hJ haJ⟩ : S.Elem) ∈ S.liftFinset J hJ :=
      (mem_liftFinset_iff S).2 haJ
    exact (mem_coeFinset_val_iff S).2 ⟨⟨a, hJ haJ⟩, hz, rfl⟩
--Equivalence class relation

/-- Equivalence relation: `x ∼ y` iff `x ≤ y ∧ y ≤ x`. -/
def sim (x y : S.Elem) : Prop := S.le x y ∧ S.le y x

/-- `sim` is an equivalence relation. -/
lemma sim_refl (x : S.Elem) : S.sim x x :=
  ⟨S.le_refl x, S.le_refl x⟩

lemma sim_symm {x y : S.Elem} (h : S.sim x y) : S.sim y x :=
  ⟨h.2, h.1⟩

lemma sim_trans {x y z : S.Elem} (hxy : S.sim x y) (hyz : S.sim y z) : S.sim x z :=
  ⟨S.le_trans hxy.1 hyz.1, S.le_trans hyz.2 hxy.2⟩

/-- `sim` as a `Setoid`. -/
--Currently not used
def simSetoid : Setoid S.Elem where
  r := S.sim
  iseqv := ⟨S.sim_refl, S.sim_symm, S.sim_trans⟩



/-- Practical form of "equivalence class is non-trivial (has another point)". -/
def nontrivialClass {α : Type u} [DecidableEq α] (S : FuncSetup α) (x : S.Elem) : Prop :=
  ∃ y : S.Elem, y ≠ x ∧ S.sim x y



lemma fixed_point_unique {α : Type u} [DecidableEq α] (S : FuncSetup α) (u : S.Elem)
    (h_fixed : S.f u = u) {v : S.Elem} (h_le : S.le u v) : u = v := by
  induction h_le with
  | refl => rfl
  | tail hb h_cover ih =>
    rename_i b c
    have : S.f b = c := h_cover
    rw [ih] at h_fixed
    rw [h_fixed] at this
    rw [←ih] at this
    exact this

/-- `u` belonging to a non-trivial equivalence class is not a self-fixed point (`f u ≠ u`). -/
--Used in 2 places.
lemma f_ne_of_nontrivialClass (S : FuncSetup α) {u : S.Elem}
    (h : S.nontrivialClass u) : S.f u ≠ u := by
  rcases h with ⟨y, hy_ne, hy_sim⟩
  intro hfix -- Suppose they are equal
  -- From u ≤ y, get u = y by `fixed_point_unique`
  have : u = y := S.fixed_point_unique u hfix hy_sim.1
  exact hy_ne this.symm

/-! ## 2) 「機能性」：出次数高々 1 -/

-- Maximal relation

/-- Maximal: everything above `x` returns to `x` (preorder version). -/
def maximal (x : S.Elem) : Prop :=
  ∀ ⦃y⦄, S.le x y → S.le y x

@[simp] lemma maximal_iff (x : S.Elem) :
    S.maximal x ↔ (∀ ⦃y⦄, S.le x y → S.le y x) := Iff.rfl

/-- If `f u = u`, then `u` is maximal (antisymmetry not required) -/
--Used.
lemma maximal_of_fixpoint  (S : FuncSetup α){u : S.Elem} (huu : S.cover u u) :
  S.maximal u := by
  intro v huv
  -- "Only u is reachable from u" by induction on reflexive transitive closure
  suffices v = u from this ▸ S.le_refl u
  induction huv with
  | refl => rfl
  | tail _ hwx ih =>
    -- `hwx : cover _ v`, induction hypothesis `ih : _ = u`
    rw [ih] at hwx
    exact S.cover_out_unique hwx huu

--Deprecated as it has the same content as above
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

--Used in Rare.lean.
lemma sim_of_maximal_above_class
    (S : FuncSetup α) {u x y : S.Elem}
    (hmax : S.maximal u)
    (hyU : S.sim y u) (hyx : S.le y x) :
    S.sim x u := by
  -- We need to show both `u ≤ x` and `x ≤ u`
  have hux : S.le u x := S.le_trans hyU.2 hyx
  constructor
  · -- First `u ≤ x` → maximality: `u ≤ x → x ≤ u`
    exact hmax hux
  · -- Next, `u ≤ x` is the `hux` obtained above
    exact hux

--------sim (unrelated to ideal or Parallel)

/-- Equivalence class of `u` in element type `S.Elem` on ground (Finset version). -/
noncomputable def simClassElem (S : FuncSetup α) (u : S.Elem) : Finset S.Elem :=
  S.ground.attach.filter (fun v => S.sim v u)

/-- Equivalence class mapped back to `α` side (this is what `idealFamily : SetFamily α` handles). -/
noncomputable def simClass (S : FuncSetup α) (u : S.Elem) : Finset α :=
  (S.simClassElem u).image (Subtype.val)

/-- Determining `v ∈ simClassElem u` is exactly `S.sim v u`. -/
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
      -- Elements of `attach` always belong to themselves (regardless of proof part)
      -- Can be done with just `simp`
      simp_all only [Finset.mem_attach]
    exact Finset.mem_filter.mpr ⟨hvattach, hsim⟩

/-- Judgment of `a ∈ simClass u`. -/
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
----From here: Ideal-related

/-- Give the order-ideal family corresponding to S as a `SetFamily` on ground type `α`. -/
--It's convenient to be able to derive idealFamily from FuncSetup, so just giving the definition.
--On second thought, there's no file that collects FuncSetup things using Ideal, so it might be good to separate.
noncomputable def idealFamily (S : FuncSetup α) : SetFamily α :=
  SetFamily.orderIdealFamily (le := leOn S) (V := S.ground)

@[simp] lemma sets_iff_isOrderIdeal
    (S : FuncSetup α) {I : Finset α} :
    (S.idealFamily).sets I ↔ SetFamily.isOrderIdealOn (S.leOn) S.ground I := Iff.rfl

/-- `S.ground` is an edge (= ideal) of `idealFamily`. -/
lemma ground_mem_ideal_edge (S : FuncSetup α) :
  S.ground ∈ (S.idealFamily).edgeFinset := by
  classical
  -- Show that `S.ground` is an order ideal by direct expansion
  have hIdeal : SetFamily.isOrderIdealOn (S.leOn) S.ground S.ground := by
    dsimp [SetFamily.isOrderIdealOn]
    constructor
    · intro x hx; exact hx
    · intro x hx y hy _; exact hy
  -- Transfer via sets ↔ isOrderIdealOn, then to edgeFinset
  have hSets : (S.idealFamily).sets S.ground :=
    (S.sets_iff_isOrderIdeal).2 hIdeal
  exact (SetFamily.mem_edgeFinset_iff_sets (F := S.idealFamily) (A := S.ground)).2 hSets

/-- `∅` is also an edge of `idealFamily`. -/
--similar to empty_mem_ideal_edge
lemma empty_mem_ideal_edge (S : FuncSetup α) :
  (∅ : Finset α) ∈ (S.idealFamily).edgeFinset := by
  classical
  -- The empty set is trivially an order ideal
  have hIdeal : SetFamily.isOrderIdealOn (S.leOn) S.ground (∅ : Finset α) := by
    dsimp [SetFamily.isOrderIdealOn]
    constructor
    · intro x hx; cases hx
    · intro x hx; cases hx
  have hSets : (S.idealFamily).sets (∅ : Finset α) :=
    (S.sets_iff_isOrderIdeal).2 hIdeal
  exact (SetFamily.mem_edgeFinset_iff_sets (F := S.idealFamily) (A := ∅)).2 hSets

/-- The `edgeFinset` of `idealFamily` is non-empty. -/
lemma ideal_edge_nonempty (S : FuncSetup α) :
  (S.idealFamily).edgeFinset.Nonempty := by
  classical
  exact ⟨S.ground, ground_mem_ideal_edge S⟩

/-- Therefore `numHyperedges ≥ 1`. -/
lemma numHyperedges_ge_one (S : FuncSetup α) :
  1 ≤ (S.idealFamily).numHyperedges := by
  classical
  -- `numHyperedges = card edgeFinset`
  have hpos : 0 < (S.idealFamily).edgeFinset.card :=
    Finset.card_pos.mpr (ideal_edge_nonempty S)
  -- From `0 < n` to `1 ≤ n`
  exact Nat.succ_le_of_lt hpos

/-- If `ground ≠ ∅`, then both `∅` and `ground` are edges and different, so card ≥ 2. -/
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
  -- Use `card_le_card` to bound
  have := Finset.card_le_card hPsub
  simpa [SetFamily.numHyperedges, hPcard] using this

lemma simClass_subset_of_contains
    (S : FuncSetup α) {u : S.Elem} {I : Finset α}
    (hI : (S.idealFamily).sets I) (huI : u.1 ∈ I) :
    S.simClass u ⊆ I := by
  classical
  -- Expand to isOrderIdealOn
  have hIdeal : SetFamily.isOrderIdealOn (S.leOn) S.ground I := by
    -- Since `[simp] lemma sets_iff_isOrderIdeal` is `Iff.rfl`, rewriting alone is OK
    -- Eliminate with `rw` (don't use `simpa using`)
    change SetFamily.isOrderIdealOn (S.leOn) S.ground I
    exact (S.sets_iff_isOrderIdeal).1 hI
  -- From here: take any element a of U and show it belongs to I
  intro a haU
  rcases (S.mem_simClass_iff u).1 haU with ⟨ha, hsim⟩
  -- Extract `a ≤ u`
  have h_le : S.le ⟨a, ha⟩ u := hsim.1
  -- Lift to `leOn a u.1`
  have h_leOn : S.leOn a u.1 := by
    -- Use `leOn_iff_subtype`
    have : S.leOn a u.1 ↔ S.le ⟨a, ha⟩ u :=
      S.leOn_iff_subtype (a := a) (b := u.1) ha u.property
    exact this.mpr h_le
  -- By downward closure of isOrderIdealOn, `a ∈ I`
  have hI_sub : I ⊆ S.ground := hIdeal.1
  have hxI : u.1 ∈ I := huI
  --have hxV : u.1 ∈ S.ground := hI_sub hxI
  -- Downward closure: `x∈I, y∈V, leOn y x → y∈I`
  have := hIdeal.2 (x := u.1) hxI (y := a) ha h_leOn
  exact this

--Used below. LeOn version of the property that simple ideals are downward closed? Currently not referenced from outside, so private.
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
  -- Downward closed, so (x:α)∈coeFinset I
  have hxIn : (x : α) ∈ S.coeFinset I :=
    hIdeal.2 (x := (y : α)) hyIn (y := (x : α)) x.property hleOn
  -- Convert back to x∈I in reverse direction
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

-- Goal: From hb : b ∈ S.ground, hleOn : S.leOn b a, haGround : a ∈ S.coeFinset Iy
--       derive b ∈ S.coeFinset Iy
--If x and y have an order relation, any ideal containing y also contains x. Important lemma.
--Could create a separate file collecting basic lemmas.

lemma le_iff_forall_ideal_mem
  (S : FuncSetup α) (x y : S.Elem) :
  S.le x y ↔
    (∀ I : Finset S.Elem,
      (S.idealFamily).sets (S.coeFinset I) → y ∈ I → x ∈ I) := by
  constructor
  · -- (→) : If `x ≤ y`, then for any ideal I, `y ∈ I → x ∈ I`
    intro hxy I hI hyI
    have hIdeal :
        SetFamily.isOrderIdealOn (S.leOn) S.ground (S.coeFinset I) :=
      (S.sets_iff_isOrderIdeal).1 hI
    have hy' : (y.1 : α) ∈ S.coeFinset I := by

      exact (mem_coeFinset_iff S (I:=I) (a:=y.1) (ha:=y.2)).2 hyI
    have hx' : (x.1 : α) ∈ S.coeFinset I := by
      have hleOn : S.leOn x.1 y.1 := (S.le_iff_leOn_val x y).mp hxy
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

/-- Paper Lemma 3.3:
`u, v` being in the same equivalence class (S.sim) is equivalent to parallel in `idealFamily S`. -/
--This relation should hold even without being functional, but here we prove it for functional ones.
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

-- Existing: parallel_iff_sim (S : FuncSetup α) (u v : S.Elem)
-- Use it as is, just drop to underlying when necessary.
--Used from outside. In both Rare.lean and IdealTrace.
@[simp]
lemma parallel_of_sim_coe (S : FuncSetup α) {x y : S.Elem}
    (h : FuncSetup.sim S x y) :
    (S.idealFamily).Parallel (x : α) (y : α) := by
  have hxy : (S.idealFamily).Parallel x y :=
    (parallel_iff_sim S x y).2 h
  exact hxy

--Cannot be moved to SetFamily because it uses FuncSetup.
--Equivalence of `simClass u` and `ParallelClass F u`.
--Also used from outside.
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

--Used below.
private lemma mem_simClass_of_sim
  (S : FuncSetup α) {u v : S.Elem} (h : S.sim u v) :
  (v : α) ∈ S.simClass u :=
  (S.mem_simClass_iff u).2 ⟨v.2, S.sim_symm h⟩

--Also used from outside.
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
  · -- From y ≠ u to value inequality
    intro h
    apply hneq
    apply Subtype.ext
    exact h
  · -- sim ⇒ parallel
    exact S.parallel_of_sim_coe hsim

-----------------------------------------------------------
------Discussion of f iteration---------------------------------
-----Could be placed before ideals.

section IterateRTG  --Is there meaning to separating sections?
variable {α : Type u} (f : α → α) --Was Type * but changed to Type u.

/-- "Reachable by iteration" map iteration. -/
--Seems to be used in traceFunctional. Many places also write directly without using it.
def iter (k : Nat) : S.Elem → S.Elem :=
  Nat.iterate S.f k

--General lemmas that don't involve SetFamily or FuncSetup should perhaps be placed in General.
--However, since f appears, it's substantially within the FuncSetup framework. stepRel might also be better defined within the FuncSetup framework.
-- Relation R_f : x R_f y ↔ f x = y
def stepRel : α → α → Prop := fun x y => f x = y

private lemma iterate_commute_right (f : α → α) :
    ∀ n x, Nat.iterate f n (f x) = f (Nat.iterate f n x) := by
  intro n
  induction' n with n ih
  · intro x; rfl
  · intro x
    -- iterate (n+1) (f x) = iterate n (f (f x))
    have h1 : Nat.iterate f (n+1) (f x) = Nat.iterate f n (f (f x)) := by
      -- Definition expansion
      simp [Nat.iterate]
    -- Unpack the right side one step with `ih`
    have h2 : Nat.iterate f n (f (f x)) = f (Nat.iterate f n (f x)) := by
      -- Apply `ih` to `x := f x`
      simpa using ih (f x)
    -- Further substitute `(f^[n]) (f x)` with `ih`
    have h3 : f (Nat.iterate f n (f x)) = f (f (Nat.iterate f n x)) := by
      -- Use `ih x : (f^[n]) (f x) = f ((f^[n]) x)` inside `f ∘ _`
      simpa using congrArg f (ih x)
    -- Finish: by definition `(f^[n+1]) x = (f^[n]) (f x)`
    calc
      Nat.iterate f (n+1) (f x)
          = Nat.iterate f n (f (f x)) := h1
      _   = f (Nat.iterate f n (f x)) := h2
      _   = f (f (Nat.iterate f n x)) := h3
      _   = f (Nat.iterate f (n+1) x) := by
              -- `Nat.iterate f (n+1) x = Nat.iterate f n (f x)`
              simp [Nat.iterate]
              simp_all only [Function.iterate_succ, Function.comp_apply]

/-- Main lemma: `ReflTransGen (stepRel f) x y ↔ ∃ k, (f^[k]) x = y` -/
--Frequently cited from external files. Content overlaps with le_iff_exists_iter.
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
          _   = f b := congrArg f hk
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

/-- Paper Lemma 2.2:
`x ≤ y` ↔ ある `k ≥ 0` で `f^[k] x = y`。 -/
--It is duplicated just like reflTransGen_iff_exists_iterate.Maybe it's better to unify it.
--However, since the arguments are different, a simple replacement might not work.
lemma le_iff_exists_iter {α} [DecidableEq α] (S : FuncSetup α) (x y : S.Elem) :
    S.le x y ↔ ∃ k : Nat, S.iter k x = y := by
  dsimp [FuncSetup.le]
  unfold FuncSetup.cover
  exact reflTransGen_iff_exists_iterate (fun xx => S.f xx)

-- First small lemma: if g u = u then g^[n] u = u
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

/-- Iterate is monotonic: if `i ≤ j` then `(f^[i]) x ≤ (f^[j]) x`. -/
--Unlike le_iff_exists_iter, this involves ordering of natural numbers
lemma le_between_iter {α} [DecidableEq α]  (S : FuncSetup α) (x : S.Elem) :
  ∀ {i j : ℕ}, i ≤ j → S.le ((S.f^[i]) x) ((S.f^[j]) x)
| i, j, hij => by
  rcases Nat.exists_eq_add_of_le hij with ⟨d, rfl⟩
  induction d with
  | zero => exact S.le_refl _
  | succ d ih =>
      -- One step: (f^[i+d]) x ⋖ (f^[i+d+1]) x
      have hstep : S.cover ((S.f^[i + d]) x) ((S.f^[i + d + 1]) x) := by
        exact (Function.iterate_succ_apply' S.f (i + d) x).symm
      have h_prev : S.le ((S.f^[i]) x) ((S.f^[i + d]) x) := ih (Nat.le_add_right i d)
      exact S.le_trans h_prev (S.cover_to_le hstep)


end IterateRTG  --Where to place this affects the alpha scope below.

--Parallel relation and Iteration relation
--Ideals don't appear directly.
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

--If elements are parallel, then if you can go from u to x, you can go from x to u.
--Doesn't use maximality. Uses parallel_iff_sim.
--Could be rewritten using the assumption of nontrivialClass.
--Used in nds_monotone_under_trace.
--This statement requires the functional assumption.
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
  -- sim ⇒ bidirectional ReflTransGen(stepRel S.f)
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
  -- Apply general lemma to S.Elem, f := S.f
  have hmax :=
    maximal_of_nontrivialClass_lemma
      (α := S.Elem) (f := S.f)
      (u := S.toElem! hu) (v := S.toElem! hv)
      ⟨huv, hvu⟩ hneq'
  -- Finish
  intro x hx; exact hmax x hx


end FuncSetup

end AvgRare

------------------------

/-
/-- Conversely, if `v` is in the class of `u`, then `sim u v`. -/
--Maybe not used.
lemma sim_of_mem_simClass
  (S : FuncSetup α) {u : S.Elem} {a : α}
  (ha : a ∈ S.ground) (hmem : a ∈ S.simClass u) :
  S.sim ⟨a, ha⟩ u := by
  classical
  have := (S.mem_simClass_iff u).mp hmem
  -- this : ∃ ha', S.sim ⟨a, ha'⟩ u
  rcases this with ⟨_, hsim⟩
  -- Identify with Subtype.ext even if ground proofs differ
  -- ⟨a, ha⟩ and ⟨a, _⟩ have the same value so rewrite with transport
  -- Actually, since the value parts are the same, we can use hsim directly
  exact hsim
-/

/- Convenient function to lift ground comparison to subtype. -/
--def toElem! (S : FuncSetup α) {x : α} (hx : x ∈ S.ground) : S.Elem := ⟨x, hx⟩

----Unused items.


/-(For convenience) When in a non-trivial equivalence class, extract successor `f u`
    as "a ground element different from u". -/
-- hv is used implicitly.
--Currently not used.
/-
lemma exists_succ_partner_of_nontrivial {α : Type u} [DecidableEq α]
    (S : FuncSetup α) {u : α} (hu : u ∈ S.ground)
    (h : S.nontrivialClass (S.toElem! hu)) :
    ∃ (v : α) (_ : v ∈ S.ground), v ≠ u := by
  classical
  let ue : S.Elem := ⟨u, hu⟩
  let ve : S.Elem := S.f ue
  refine ⟨ve.1, ve.2, ?_⟩
  -- Drop `ve ≠ ue` to the base α with `Subtype.ext`
  have hne : ve ≠ ue := S.f_ne_of_nontrivialClass (u := ue) h
  intro hval
  apply hne
  apply Subtype.ext
  exact hval

-- Helper to extract base ≠ from subtype equivalence ≠. Currently not used.
private lemma ne_val_of_ne {x y : {a // a ∈ S.ground}} (h : x ≠ y) : x.1 ≠ y.1 := by
  intro hval
  apply h
  apply Subtype.ext
  exact hval

-/
