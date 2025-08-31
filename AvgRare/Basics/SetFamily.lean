import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.Order.BigOperators.Group.Finset

import AvgRare.Basics.General
import LeanCopilot

universe u

open scoped BigOperators

namespace AvgRare

/-
SetFamily.lean — Basic Set Family and NDS.
Basic definitions and lemma.
- Here we will also move on to the concepts that depend on order, such as ideal.
-/

variable {α : Type u} [DecidableEq α]

@[ext]
structure SetFamily (α : Type u) [DecidableEq α] where
  ground     : Finset α
  sets       : Finset α → Prop
  decSets    : DecidablePred sets
  inc_ground : ∀ {A : Finset α}, sets A → A ⊆ ground

namespace SetFamily --Align names to enable dot notation.
variable (F : SetFamily α)

instance instDecidablePred_sets (F : SetFamily α) : DecidablePred F.sets :=
  F.decSets

def edgeFinset : Finset (Finset α) :=
  F.ground.powerset.filter (fun A => decide (F.sets A))

/-- The `edgeFinset` element is included in the ground set. -/
-- Used in only one place. That lemma is not used either.
lemma subset_ground_of_mem_edge {A : Finset α}
    (hA : A ∈ F.edgeFinset) : A ⊆ F.ground := by
  classical
  rcases Finset.mem_filter.mp hA with ⟨hPow, _⟩
  exact Finset.mem_powerset.mp hPow

def numHyperedges : Nat :=
  F.edgeFinset.card

def totalHyperedgeSize : Nat :=
  ∑ A ∈ F.edgeFinset, A.card

def degree (x : α) : Nat :=
  ∑ A ∈ F.edgeFinset, (if x ∈ A then (1 : Nat) else 0)

noncomputable def sumProd {α} [DecidableEq α]
  (F₁ F₂ : SetFamily α) : SetFamily α := by
  classical
  refine
  { ground := F₁.ground ∪ F₂.ground
    , sets := fun X =>
        ∃ A B, F₁.sets A ∧ F₂.sets B ∧ X = A ∪ B
    , decSets := Classical.decPred _
    , inc_ground := ?_ }
  intro X hX
  rcases hX with ⟨A, B, hA, hB, rfl⟩
  have hAsub : A ⊆ F₁.ground := F₁.inc_ground hA
  have hBsub : B ⊆ F₂.ground := F₂.inc_ground hB
  exact Finset.union_subset
          (hAsub.trans Finset.subset_union_left)
          (hBsub.trans Finset.subset_union_right)

-- NDS: `2 * (sum of sizes) - (number of edges) * (size of ground set)` defined as `Int`.
def NDS (F : SetFamily α) : Int :=
  2 * (F.totalHyperedgeSize : Int) - (F.numHyperedges : Int) * (F.ground.card : Int)



variable (F : SetFamily α)

@[simp] lemma NDS_def :
    NDS F = 2 * (F.totalHyperedgeSize : Int)
             - (F.numHyperedges : Int) * (F.ground.card : Int) := rfl

/-- Version with `degree` rewritten as "number of edges containing x". -/
-- Used in several places.
lemma degree_eq_card_filter (x : α) :
    F.degree x = (F.edgeFinset.filter (fun A => x ∈ A)).card := by
  classical
  unfold degree
  have h :
      (∑ A ∈ F.edgeFinset, (if x ∈ A then (1 : Nat) else 0))
        = (∑ A ∈ F.edgeFinset.filter (fun A => x ∈ A), (1 : Nat)) := by
    simp_all only [Finset.sum_boole, Nat.cast_id, Finset.sum_const, smul_eq_mul, mul_one]
  simp_all only [Finset.sum_boole, Nat.cast_id, Finset.sum_const, smul_eq_mul, mul_one]

/-- `edgeFinset` is a subset of powerset. -/
/-
lemma edgeFinset_subset_powerset :
    F.edgeFinset ⊆ F.ground.powerset := by
  classical
  intro A hA
  exact (Finset.mem_filter.mp hA).1
-/

--It is used a lot.
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
    have hDec : decide (F.sets A) = true := decide_eq_true_iff.mpr hSets
    exact Finset.mem_filter.mpr ⟨hPow, hDec⟩

@[simp] lemma mem_edgeFinset_iff_sets : (A ∈ F.edgeFinset) ↔ F.sets A := by
  classical
  constructor
  · intro h; have := (F.mem_edgeFinset (A := A)).1 h; exact this.2
  · intro h; have : A ⊆ F.ground := F.inc_ground h
    exact (F.mem_edgeFinset (A := A)).2 ⟨this, h⟩

---------------------------------------------------------
-- Parallel Relationship Definitions and Basic Limitation
---------------------------------------------------------

@[simp] def Parallel (F : SetFamily α) (u v : α) : Prop :=
  {A : Finset α | F.sets A ∧ u ∈ A} = {A : Finset α | F.sets A ∧ v ∈ A}

lemma parallel_refl (F : SetFamily α) (u : α) : Parallel F u u := rfl

lemma parallel_symm {F : SetFamily α} {u v : α} :
    Parallel F u v → Parallel F v u := fun h => h.symm

lemma parallel_trans {F : SetFamily α} {a b c : α}
  (hab : Parallel F a b) (hbc : Parallel F b c) :
  Parallel F a c := by
  exact hab.trans hbc

def Parallel_edge (F : SetFamily α) (u v : α) : Prop :=
  F.edgeFinset.filter (fun A => u ∈ A) =
  F.edgeFinset.filter (fun A => v ∈ A)

/-- `Parallel` (equation in set collection) and `Parallel_edge` are the same value。 -/
lemma Parallel_edge_iff_Parallel (F : SetFamily α) (u v : α) :
  Parallel_edge F u v ↔ Parallel F u v := by
  constructor
  · intro h
    ext A
    constructor <;> intro hA <;>
    · rcases hA with ⟨hsets, hx⟩
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
    apply Finset.ext
    intro A
    have h' := congrArg (fun (S : Set (Finset α)) => A ∈ S) h
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
  by
    classical
    exact F.ground.filter (fun b => Parallel F a b)

/-
-- Currently not used.
lemma ParallelClass_subset_ground (F : SetFamily α) {a : α} :
  ParallelClass F a ⊆ F.ground := by
  classical
  intro x hx
  have hx' := Finset.mem_filter.mp hx
  exact hx'.1

-- Currently not used.
lemma ParallelClass_nonempty (F : SetFamily α) {a : α} (ha : a ∈ F.ground) :
  (ParallelClass F a).Nonempty := by
  classical
  refine ⟨a, ?_⟩
  -- a ∈ ground ∧ Parallel F a a
  exact Finset.mem_filter.mpr (And.intro ha rfl)
-/

/-- Even if you replace the representative of `ParallelClass`, it remains the same. -/
-- Currently used only within this file.
private lemma parallelClass_eq_of_parallel
  (F : SetFamily α) {a b : α}
  (hab : Parallel F a b) :
  ParallelClass F a = ParallelClass F b := by
  classical
  apply Finset.ext
  intro x
  constructor
  · intro hx
    have ⟨hxg, hax⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨hxg, parallel_trans (parallel_symm hab) hax⟩
  · intro hx
    have ⟨hxg, hbx⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨hxg, parallel_trans hab hbx⟩

  /-- Basic form of membership test: `x ∈ ParallelClass F a` expands to "ground membership + parallel". -/
-- Used extensively.
@[simp] lemma mem_ParallelClass_iff
  (F : SetFamily α) (a x : α) :
  x ∈ ParallelClass F a ↔ (x ∈ F.ground ∧ Parallel F a x) := by
  classical
  exact Finset.mem_filter

-- From here on, we'll discuss classSet for a while.

-- "Set of equivalence classes" is implemented as an image of the representative map.
noncomputable def classSet (F : SetFamily α) : Finset (Finset α) :=
  by
    classical
    exact F.ground.image (fun a => ParallelClass F a)

/-
-- Not used in the end.
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
    -- C is an image value, so it belongs to the image
    have : ParallelClass F a ∈ F.ground.image (fun a => ParallelClass F a) :=
      Finset.mem_image.mpr ⟨a, ha, rfl⟩
    rw [Finset.mem_image]
    rw [Finset.mem_image] at this
    obtain ⟨a,ha⟩  := this
    use a
    subst hC
    simp_all only [and_self]
-/

-- Disjointness of equivalence classes
-- Used somewhat.
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
    -- `C = ParallelClass F a`
    have := hxC; exact by
      exact (by
        subst hCa hDb
        simp_all only [Finset.mem_image, ne_eq]

        )
  have hxD' : x ∈ ParallelClass F b := by
    exact (by
      subst hCa hDb
      simp_all only [Finset.mem_image, ne_eq]
      )
  have hax : Parallel F a x := (Finset.mem_filter.mp hxC').2
  have hbx : Parallel F b x := (Finset.mem_filter.mp hxD').2
  -- `Parallel a b`
  have hba : Parallel F b a := parallel_trans hbx (parallel_symm hax)
  have hab : Parallel F a b := parallel_symm hba
  have hEq : ParallelClass F a = ParallelClass F b := by

    exact parallelClass_eq_of_parallel F hab
  have : C = D := by
    -- `C = class a = class b = D`
    subst hCa hDb
    simp_all only [Parallel]
  exact (hne this).elim

-- Used somewhat.
/-- ground is a union of classes. -/
lemma ground_eq_biUnion_classSet (F : SetFamily α) :
  F.ground = Finset.biUnion (classSet F) (fun C => C) := by
  classical
  apply Finset.ext
  intro a
  constructor
  · intro ha
    have hmem : a ∈ ParallelClass F a :=
      Finset.mem_filter.mpr ⟨ha, parallel_refl F a⟩
    have hC : ParallelClass F a ∈ classSet F :=
      Finset.mem_image.mpr ⟨a, ha, rfl⟩
    exact Finset.mem_biUnion.mpr ⟨ParallelClass F a, hC, hmem⟩
  · intro ha
    obtain ⟨C, hC, haC⟩ := Finset.mem_biUnion.mp ha
    obtain ⟨x, hx, hCx⟩ := Finset.mem_image.mp hC
    rw [←hCx] at haC
    exact (Finset.mem_filter.mp haC).1

lemma card_ground_eq_sum_card_classes (F : SetFamily α) :
  F.ground.card = ∑ C ∈ classSet F, C.card := by
  classical
  -- `ground = ⋃ C∈classSet, C`
  have hcover := ground_eq_biUnion_classSet F
  have hdisj : ∀ C ∈ classSet F, ∀ D ∈ classSet F, C ≠ D → Disjoint C D :=
    fun C hC D hD hne => classSet_disjoint_of_ne F hC hD hne
  rw [hcover, Finset.card_biUnion hdisj]


/--Any element in `classSet` is non-empty. -/
lemma classSet_nonempty (F : SetFamily α) :
  ∀ C ∈ classSet F, C.Nonempty := by
  classical
  intro C hC
  obtain ⟨a, ha, hCa⟩ := Finset.mem_image.mp hC
  have : a ∈ ParallelClass F a :=
    Finset.mem_filter.mpr ⟨ha, parallel_refl F a⟩
  exact ⟨a, hCa ▸ this⟩

-- From here on, numClasses related

noncomputable def numClasses (F : SetFamily α) : ℕ :=
  (classSet F).card

/- The number of equivalence classes is at most the size of the original set: `numClasses ≤ |ground|`. -/
lemma numClasses_le_ground_card (F : SetFamily α) :
  numClasses F ≤ F.ground.card := by
  classical
  unfold numClasses classSet
  -- (`(ground.image f).card ≤ ground.card`)
  exact Finset.card_image_le


-- numClasses related ends here

-- "Set of edges containing w" as Finset:
-- Used only immediately below.
def withElem (E : Finset (Finset α)) (w : α) : Finset (Finset α) :=
  E.filter (fun A => w ∈ A)

/-- If `u‖v`, then for any class `C`: `u ∈ C ↔ v ∈ C`. -/
-- Cannot prove without the universal set. Used somewhat.

lemma mem_u_iff_mem_v_of_class
  (F : SetFamily α) (hasU: F.sets F.ground){u v : α} (hp : Parallel F u v)
  {C : Finset α} (hC : C ∈ classSet F) :
  (u ∈ C ↔ v ∈ C) := by
  classical
  obtain ⟨a, ha, hCdef⟩ :
      ∃ a, a ∈ F.ground ∧ C = ParallelClass F a := by
    have h := (Finset.mem_image.mp hC)
    simp_all only [Parallel]
    obtain ⟨w, h⟩ := h
    obtain ⟨left, right⟩ := h
    subst right
    exact ⟨w, left, rfl⟩
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
  constructor
  · intro huC
    have : u ∈ ParallelClass F a := by
      have := huC
      have : u ∈ ParallelClass F a := by
        exact cast (by rw [hCdef]) huC
      exact this
    have : v ∈ ParallelClass F a := h1 this
    apply cast
    exact rfl
    subst hCdef
    simp_all only [Parallel, imp_self, mem_ParallelClass_iff, and_true, and_self]
  · intro hvC
    have : v ∈ ParallelClass F a := cast (by rw [hCdef]) hvC
    have : u ∈ ParallelClass F a := h2 this
    subst hCdef
    simp_all only [Parallel, imp_self, mem_ParallelClass_iff, and_true, and_self]

/-
-- Something not used.

-- The equivalence of being parallel and having equal included edges, but not used anywhere.
lemma Parallel_iff_filter_edge (F : SetFamily α) (w z : α) :
  Parallel F w z
  ↔ withElem F.edgeFinset w = withElem F.edgeFinset z := by
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
-/

-------------------------------------------
-- ideal
-------------------------------------------

def isOrderIdealOn (le : α → α → Prop) (V I : Finset α) : Prop :=
  I ⊆ V ∧ ∀ ⦃x⦄, x ∈ I → ∀ ⦃y⦄, y ∈ V → le y x → y ∈ I

noncomputable def orderIdealFamily (le : α → α → Prop) (V : Finset α) : SetFamily α := by
  classical
  refine
  { ground := V
    , sets := fun I => isOrderIdealOn le V I
    , decSets := Classical.decPred _
    , inc_ground := ?_ }
  intro A a
  exact a.1

-- Used.
@[simp] lemma sets_iff_isOrderIdeal {I : Finset α} :
    (orderIdealFamily le V).sets I ↔ isOrderIdealOn le V I := Iff.rfl


end SetFamily
end AvgRare
