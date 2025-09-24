import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import AvgRare.Basics.SetFamily
--import LeanCopilot

/-
SetTrace.lean — Trace without FuncSetup
It's mainly about indicating that trace reduces one more excess
We also demonstrate the change in NDS when parallel elements are traced.
-/

universe u
open Classical
open scoped BigOperators

namespace AvgRare
namespace SetFamily

variable {α : Type u} [DecidableEq α]

/-- 1 point trace: A family with element `x` removed from each hyperedge.
`ground` is dropped to `F.ground.erase x`.-/
--ideals define Traces as well as collective families in general.
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
      simp_all only [ne_eq])

@[simp] lemma traceAt_ground (x : α) (F : SetFamily α) :
    (traceAt x F).ground = F.ground.erase x := rfl

@[simp] lemma sets_traceAt_iff (F : SetFamily α) (u : α) {B : Finset α} : (traceAt u F).sets B ↔ ∃ A, F.sets A ∧ B = A.erase u := by
  rfl
-- The lemma describing the behavior of trace operation.
private lemma edgeFinset_traceAt_eq_image_erase (F : SetFamily α) (u : α) :
  (traceAt u F).edgeFinset = F.edgeFinset.image (fun A => A.erase u) := by
  classical
  ext B; constructor
  · intro hB
    have hSets : (traceAt u F).sets B :=
      (SetFamily.mem_edgeFinset_iff_sets (F := traceAt u F) (A := B)).1 hB
    rcases (sets_traceAt_iff (F := F) (u := u) (B := B)).1 hSets with ⟨A, hA, rfl⟩
    exact Finset.mem_image.mpr
      ⟨A, (SetFamily.mem_edgeFinset_iff_sets (F := F) (A := A)).2 hA, rfl⟩
  · intro hB
    rcases Finset.mem_image.mp hB with ⟨A, hAedge, rfl⟩
    have hAsets : F.sets A :=
      (SetFamily.mem_edgeFinset_iff_sets (F := F) (A := A)).1 hAedge
    have hTrace : (traceAt u F).sets (A.erase u) :=
      (sets_traceAt_iff (F := F) (u := u) (B := A.erase u)).2 ⟨A, hAsets, rfl⟩
    exact (SetFamily.mem_edgeFinset_iff_sets (F := traceAt u F) (A := A.erase u)).2 hTrace

/-Original proof
lemma edgeFinset_traceAt_eq_image_erase (F : SetFamily α) (u : α) :
  (traceAt u F).edgeFinset = F.edgeFinset.image (λ A => A.erase u) := by
  ext B
  constructor
  · -- (→) Sets in traceAt's edgeFinset are erased from original edges
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

  · -- (←) Erase of original edge A is an edge of traceAt
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
    · -- The sets part is enforced by match
      simp_all only [decide_eq_true_eq]
      exact ⟨A, hAsets, rfl⟩
-/

/- Unused reference.
lemma trace_filter_eq_image_filter_of_ne
  (F : SetFamily α) (u w : α) (hwu : w ≠ u) :
  (traceAt u F).edgeFinset.filter (fun B => w ∈ B)
  =
  (F.edgeFinset.filter (fun A => w ∈ A)).image (fun A => A.erase u) := by
  classical
  -- First apply the fact that the whole thing is an image to filter
  have H := edgeFinset_traceAt_eq_image_erase (F := F) (u := u)
  -- If `w ≠ u` then `w ∈ A.erase u ↔ w ∈ A`
  -- This allows us to say "filtered image = image after filter" directly (injective is not needed).
  apply Finset.ext
  intro B
  constructor
  · intro hB
    rcases Finset.mem_filter.mp hB with ⟨hBmem, hBw⟩
    have : B ∈ (F.edgeFinset.image fun A => A.erase u) := by
      rw [H]; exact hBmem
    rcases Finset.mem_image.mp this with ⟨A, hA, rfl⟩
    -- From `w ∈ A.erase u` to `w ∈ A` (using w ≠ u)
    have : w ∈ A := by
      simp only [Finset.mem_erase, hwu, true_and] at hBw
      exact hBw
    exact Finset.mem_image.mpr ⟨A, (Finset.mem_filter.mpr ⟨hA, this⟩), rfl⟩
  · intro hB
    rcases Finset.mem_image.mp hB with ⟨A, hA, rfl⟩
    rcases Finset.mem_filter.mp hA with ⟨hAedge, hAw⟩
    -- Right to left: A.erase u is an edge on the trace side and contains w
    refine Finset.mem_filter.mpr ?_
    constructor
    · simpa [H]
      using (Finset.mem_image.mpr ⟨A, hAedge, rfl⟩ :
        A.erase u ∈ (F.edgeFinset.image fun A => A.erase u))
    · -- `w ∈ A.erase u` (using w ≠ u)
      -- again: mem_erase ↔ (w ≠ u ∧ w ∈ A)
      simp only [Finset.mem_erase, hwu, true_and]
      exact hAw

-/

-- Trace-related
-- Existence of parallel partner was not necessary.
private lemma parallel_off_u_preserved_by_trace
  {α : Type*}
  [DecidableEq α]
  (F : SetFamily α) (u w z : α)
  (hw : w ≠ u) (hz : z ≠ u) :
  Parallel_edge (traceAt u F) w z ↔ Parallel_edge F w z := by
  -- Known: edge set is the image of erase
  have himg :
      (traceAt u F).edgeFinset
        = F.edgeFinset.image (fun A : Finset α => A.erase u) :=
    edgeFinset_traceAt_eq_image_erase F u

  -- (→) direction
  constructor
  · intro htr
    have h_on_image :
      ∀ B ∈ (F.edgeFinset.image (fun A => A.erase u)),
        (w ∈ B) ↔ (z ∈ B) := by
      have := (filter_eq_iff_on
        (S := (traceAt u F).edgeFinset)
        (p := fun B => w ∈ B) (q := fun B => z ∈ B)).1
        (by simp [himg]
            dsimp [Parallel_edge] at htr
            simp [himg] at htr
            exact htr
        )

      simpa [himg] using this
    have h_on_domain :
      ∀ A ∈ F.edgeFinset, (w ∈ A) ↔ (z ∈ A) := by
      intro A hA
      have : (w ∈ A.erase u) ↔ (z ∈ A.erase u) := by
        exact h_on_image (A.erase u)
          (by exact Finset.mem_image.mpr ⟨A, hA, rfl⟩)
      have hw' : (w ∈ A.erase u) ↔ (w ∈ A) :=
        Finset.mem_erase.trans ⟨fun h => h.2, fun h => ⟨hw, h⟩⟩
      have hz' : (z ∈ A.erase u) ↔ (z ∈ A) :=
        Finset.mem_erase.trans ⟨fun h => h.2, fun h => ⟨hz, h⟩⟩
      simpa [hw', hz'] using this
    exact
      (filter_eq_iff_on (S := F.edgeFinset)
        (p := fun A => w ∈ A) (q := fun A => z ∈ A)).2 h_on_domain

  · intro hdom
    have h_on_domain :
      ∀ A ∈ F.edgeFinset, (w ∈ A) ↔ (z ∈ A) :=
      (filter_eq_iff_on
        (S := F.edgeFinset)
        (p := fun A => w ∈ A) (q := fun A => z ∈ A)).1 hdom
    have h_on_image :
      ∀ B ∈ (F.edgeFinset.image (fun A => A.erase u)),
        (w ∈ B) ↔ (z ∈ B) := by
      intro B hB
      rcases (Finset.mem_image).1 hB with ⟨A, hA, rfl⟩
      have hw' : (w ∈ A.erase u) ↔ (w ∈ A) :=
        Finset.mem_erase.trans ⟨fun h => h.2, fun h => ⟨hw, h⟩⟩
      have hz' : (z ∈ A.erase u) ↔ (z ∈ A) :=
        Finset.mem_erase.trans ⟨fun h => h.2, fun h => ⟨hz, h⟩⟩
      rw [hw', hz']
      exact h_on_domain A hA
    have : (traceAt u F).edgeFinset.filter (fun B => w ∈ B)
           = (traceAt u F).edgeFinset.filter (fun B => z ∈ B) := by
      have := (filter_eq_iff_on
        (S := F.edgeFinset.image (fun A => A.erase u))
        (p := fun B => w ∈ B) (q := fun B => z ∈ B)).2 h_on_image
      simpa [himg] using this
    exact this

omit [DecidableEq α] in
private lemma parallel_off_u_preserved_by_trace2
  [DecidableEq α] (F : SetFamily α) (u w z : α)
  (hw : w ≠ u) (hz : z ≠ u) :
  Parallel (traceAt u F) w z ↔ Parallel F w z := by
  let pe := parallel_off_u_preserved_by_trace F u w z hw hz
  rw [Parallel_edge_iff_Parallel ] at pe
  rw [Parallel_edge_iff_Parallel ] at pe
  exact pe

--Is it easier to calculate if defined with Int?
noncomputable def excess (F : SetFamily α) : ℕ :=
  F.ground.card - numClasses F

private lemma ParallelClass_trace_eq_erase
  (F : SetFamily α) (u a : α)
  (ha : a ∈ F.ground.erase u) :
  ParallelClass (traceAt u F) a = (ParallelClass F a).erase u := by
  classical
  apply Finset.ext
  intro b
  have LtoR : b ∈ ParallelClass (traceAt u F) a →
              b ∈ (ParallelClass F a).erase u := by
    intro hb
    have hb' :
      (b ∈ (traceAt u F).ground ∧ Parallel (traceAt u F) a b) :=
      (mem_ParallelClass_iff (traceAt u F) a b).1 hb
    have hb_ne_u : b ≠ u := (Finset.mem_erase.mp hb'.1).1
    have hiff :=
      parallel_off_u_preserved_by_trace2
        (F := F) (u := u) (w := a) (z := b)
        (hw := (Finset.mem_erase.mp ha).1) (hz := hb_ne_u)
    have hab : Parallel F a b := by
      exact (Iff.mp hiff) hb'.2
    have hbg : b ∈ F.ground := (Finset.mem_erase.mp hb'.1).2
    have hbC : b ∈ ParallelClass F a :=
      (mem_ParallelClass_iff F a b).2 (And.intro hbg hab)
    exact Finset.mem_erase.mpr (And.intro hb_ne_u hbC)
  have RtoL : b ∈ (ParallelClass F a).erase u →
              b ∈ ParallelClass (traceAt u F) a := by
    intro hb
    have hb_ne_u : b ≠ u := (Finset.mem_erase.mp hb).1
    have hbC     : b ∈ ParallelClass F a := (Finset.mem_erase.mp hb).2
    have hbC' :
      (b ∈ F.ground ∧ Parallel F a b) :=
      (mem_ParallelClass_iff F a b).1 hbC
    have hiff :=
      parallel_off_u_preserved_by_trace2
        (F := F) (u := u) (w := a) (z := b)
        (hw := (Finset.mem_erase.mp ha).1) (hz := hb_ne_u)
    have hab_t : Parallel (traceAt u F) a b :=
      hiff.mpr hbC'.2
    have hbg_t : b ∈ (traceAt u F).ground :=
      Finset.mem_erase.mpr ⟨hb_ne_u, hbC'.1⟩
    exact (mem_ParallelClass_iff (traceAt u F) a b).2
           (And.intro hbg_t hab_t)
  constructor
  · intro h; exact LtoR h
  · intro h; exact RtoL h

/-- `classSet (traceAt u F)` is the image of `classSet F` after `erase u`.
    When the representative is `u`, replace it with `v` (using `u‖v`). -/
private lemma classSet_trace_eq_image_erase_of_parallel
  (F : SetFamily α) {u v : α}
  (hu : u ∈ F.ground) (hv : v ∈ F.ground)
  (hne : u ≠ v) (hp : Parallel F u v) :
  classSet (traceAt u F) = (classSet F).image (fun C => C.erase u) := by
  classical
  -- Left ⊆ Right
  apply Finset.ext
  intro D
  constructor
  · intro hD
    -- D = class(trace) a (a ∈ ground.erase u) constructed from
    obtain ⟨a, ha, hDdef⟩ :
        ∃ a, a ∈ F.ground.erase u ∧
              D = ParallelClass (traceAt u F) a := by
      -- classSet(trace) = (ground.erase u).image (class(trace))
      have h := (Finset.mem_image.mp hD)
      -- h : ∃ a, a ∈ ground.erase u ∧ D = class(trace) a
      obtain ⟨a, ha, hDdef⟩ := h
      exact ⟨a, ha, hDdef.symm⟩
    -- D = (ParallelClass F a).erase u
    have hD' :
        D = (ParallelClass F a).erase u :=
      by
        have h := ParallelClass_trace_eq_erase (F := F) (u := u) (a := a) ha
        exact Eq.trans hDdef h
    have hsrc : ParallelClass F a ∈ classSet F := by
      have ha_g : a ∈ F.ground := (Finset.mem_erase.mp ha).2
      exact Finset.mem_image.mpr (Exists.intro a (And.intro ha_g rfl))
    apply Finset.mem_image.mpr (Exists.intro (ParallelClass F a)
           (And.intro hsrc hD'.symm))
  · intro hD
    obtain ⟨C, hC, hDdef⟩ :
        ∃ C, C ∈ classSet F ∧  C.erase u = D :=
      Finset.mem_image.mp hD
    obtain ⟨a, ha, hCdef⟩ :
        ∃ a, a ∈ F.ground ∧ ParallelClass F a = C:=
      Finset.mem_image.mp hC
    by_cases hau : a = u
    ·
      have hCv : C = ParallelClass F v := by
        -- C = class F a = class F u = class F v
        have h1 : C = ParallelClass F u := by
          exact Eq.trans hCdef.symm (by exact congrArg F.ParallelClass hau)  -- Stabilization: just type matching
        have h2 : ParallelClass F u = ParallelClass F v :=
          by

            apply Finset.ext
            intro x
            have L : x ∈ ParallelClass F u ↔ (x ∈ F.ground ∧ Parallel F u x) :=
              (mem_ParallelClass_iff F u x)
            have R : x ∈ ParallelClass F v ↔ (x ∈ F.ground ∧ Parallel F v x) :=
              (mem_ParallelClass_iff F v x)
            constructor
            · intro hx
              have hx' := (Iff.mp L) hx
              have hvx : Parallel F v x := by
                subst h1 hau hDdef
                simp_all only [mem_ParallelClass_iff, Parallel, true_and, ne_eq, true_iff, and_self, and_true, Finset.mem_image]
              exact (Iff.mpr R) (And.intro hx'.1 hvx)
            · intro hx
              have hx' := (Iff.mp R) hx
              have hux : Parallel F u x :=
                parallel_trans (F := F) hp hx'.2
              exact (Iff.mpr L) (And.intro hx'.1 hux)
        exact Eq.trans h1 h2
      have hv' : v ∈ F.ground.erase u :=
        Finset.mem_erase.mpr (And.intro (ne_comm.mp hne) hv)
      have : D = ParallelClass (traceAt u F) v := by
        have h3 : D = (ParallelClass F v).erase u :=
          Eq.trans hDdef.symm (by exact congrArg (fun t => t) (congrFun (congrArg Finset.erase hCv) u))
        have h4 :=
          ParallelClass_trace_eq_erase (F := F) (u := u) (a := v) hv'
        have h4' : (ParallelClass F v).erase u = ParallelClass (traceAt u F) v :=
          Eq.symm h4
        exact Eq.trans h3 h4'
      apply Finset.mem_image.mpr
      apply Exists.intro v
      · constructor
        · exact hv'
        · exact this.symm

    · have : D = ParallelClass (traceAt u F) a := by
        have h := ParallelClass_trace_eq_erase
                   (F := F) (u := u) (a := a)
                   (Finset.mem_erase.mpr (And.intro hau ha))
        have h' : (ParallelClass F a).erase u = ParallelClass (traceAt u F) a :=
          Eq.symm h
        -- D = C.erase u = (class F a).erase u = class(trace) a
        exact Eq.trans hDdef.symm (Eq.trans (by rw [hCdef]) h')
      -- membership
      apply Finset.mem_image.mpr
      apply Exists.intro a
      · constructor
        · subst this hCdef
          simp_all only [ne_eq, Parallel, Finset.mem_image, traceAt_ground, Finset.mem_erase, not_false_eq_true, and_self]
        · exact this.symm

/-- `erase u` is injective on `classSet F` (when `u‖v`). -/
private lemma erase_on_classSet_injective_of_parallel
  (F : SetFamily α) (hasU: F.sets F.ground) {u v : α}
  (hu : u ∈ F.ground) --(hv : v ∈ F.ground)
  (hne : u ≠ v) (hp : Parallel F u v) :
  Function.Injective
    (fun (C : {C // C ∈ classSet F}) => (C.1).erase u) := by
  classical
  intro C D hEq
  -- Name `C.1` and `D.1` as `Cset` and `Dset` respectively for handling
  let Cset := C.1
  let Dset := D.1
  have hCmem : Cset ∈ classSet F := C.2
  have hDmem : Dset ∈ classSet F := D.2
  apply Subtype.ext
  apply Finset.ext
  intro x
  by_cases hx : x = u
  ·
    have hvne : v ≠ u := ne_comm.mp hne

    have hveq : (v ∈ Cset.erase u) ↔ (v ∈ Dset.erase u) := by
      constructor
      · intro hvC
        have : v ∈ Dset.erase u := by
          subst hx
          simp_all only [Finset.coe_mem, ne_eq, Parallel, Finset.mem_erase, not_false_eq_true, true_and, and_self, Cset, Dset]

        exact this
      · intro hvD
        have : v ∈ Cset.erase u := by
          subst hx
          simp_all only [Finset.coe_mem, ne_eq, Parallel, Finset.mem_erase, not_false_eq_true, true_and, and_self, Cset, Dset]

        exact this
    have hvC_iff : (v ∈ Cset.erase u) ↔ (v ∈ Cset) := by
      constructor
      · intro hvC
        exact (Finset.mem_erase.mp hvC).2
      · intro hvC
        exact Finset.mem_erase.mpr (And.intro hvne hvC)
    have hvD_iff : (v ∈ Dset.erase u) ↔ (v ∈ Dset) := by
      constructor
      · intro hvD
        exact (Finset.mem_erase.mp hvD).2
      · intro hvD
        exact Finset.mem_erase.mpr (And.intro hvne hvD)
    have h1 : (u ∈ Cset) ↔ (v ∈ Cset) := by
      apply mem_u_iff_mem_v_of_class F
      subst hx
      simp_all only [Finset.coe_mem, ne_eq, Parallel, Finset.mem_erase, not_false_eq_true, true_and, Cset, Dset]
      exact hp
      exact hCmem
    have h2 : (u ∈ Dset) ↔ (v ∈ Dset) := by
      apply mem_u_iff_mem_v_of_class F hasU hp hDmem
    constructor
    · intro huC
      have hvC : v ∈ Cset := by
        subst hx
        simp_all only [Finset.coe_mem, ne_eq, Parallel, Finset.mem_erase, not_false_eq_true,
          true_and, iff_true, Cset, Dset]

      have hvD : v ∈ Dset := by
        have : v ∈ Cset.erase u := (Iff.mpr hvC_iff) hvC
        have : v ∈ Dset.erase u := (Iff.mp hveq) this
        exact (Iff.mp hvD_iff) this
      subst hx
      simp_all only [Finset.coe_mem, ne_eq, Parallel, Finset.mem_erase, not_false_eq_true, and_self, iff_true, Cset, Dset]

    · intro huD
      have hvD : v ∈ Dset := by
        subst hx
        simp_all only [Finset.coe_mem, ne_eq, Parallel, Finset.mem_erase, not_false_eq_true, true_and, true_iff, Cset, Dset]

      have hvC : v ∈ Cset := by
        have : v ∈ Dset.erase u := (Iff.mpr hvD_iff) hvD
        have : v ∈ Cset.erase u := (Iff.mpr hveq) this
        exact (Iff.mp hvC_iff) this
      subst hx
      simp_all only [Finset.coe_mem, ne_eq, Parallel, Finset.mem_erase, not_false_eq_true, and_self, iff_true, Cset, Dset]

  ·
    have hxC_iff : (x ∈ Cset) ↔ (x ∈ Cset.erase u) := by
      constructor
      · intro hxC; exact Finset.mem_erase.mpr (And.intro hx hxC)
      · intro hxC; exact (Finset.mem_erase.mp hxC).2
    have hxD_iff : (x ∈ Dset) ↔ (x ∈ Dset.erase u) := by
      constructor
      · intro hxD; exact Finset.mem_erase.mpr (And.intro hx hxD)
      · intro hxD; exact (Finset.mem_erase.mp hxD).2
    have heq_x :
        (x ∈ Cset.erase u) ↔ (x ∈ Dset.erase u) := by
      constructor
      · intro hxC
        simp [Dset]
        constructor
        · exact hx
        · simp_all [Cset]
      · intro hxD
        simp_all only [ne_eq, Parallel, Finset.coe_mem, Finset.mem_erase, not_false_eq_true, and_self, Cset, Dset]

    constructor
    · intro hxC
      have : x ∈ Cset.erase u := (Iff.mp hxC_iff) hxC
      have : x ∈ Dset.erase u := (Iff.mp heq_x) this
      exact Finset.mem_of_mem_erase this
    · intro hxD
      have : x ∈ Dset.erase u := (Iff.mp hxD_iff) hxD
      have : x ∈ Cset.erase u := (Iff.mpr heq_x) this
      exact Finset.mem_of_mem_erase this

@[simp] lemma ground_card_trace_of_mem
    (F : SetFamily α) {u : α} (hu : u ∈ F.ground) :
    (traceAt u F).ground.card = F.ground.card - 1 := by
  classical
  simp [traceAt, hu]

/-- ★ Final goal: `excess` decreases by 1. Referenced from Reduction -/
theorem excess_trace
  (F : SetFamily α) (hasU: F.sets F.ground)(Nonemp:F.ground.card ≥ 1) (u v : α)
  (hu : u ∈ F.ground) (hv : v ∈ F.ground)
  (huv : u ≠ v) (hp : Parallel F u v) :
  excess (traceAt u F) = excess F - 1 := by
  classical
  have hground :
      (traceAt u F).ground.card = F.ground.card - 1 := by
    apply ground_card_trace_of_mem (F := F) (hu := hu)
  have hclassSet :
      classSet (traceAt u F) = (classSet F).image (fun C => C.erase u) :=
    classSet_trace_eq_image_erase_of_parallel
      (F := F) (hu := hu) (hv := hv) (hne := huv) (hp := hp)
  have hinj :
      Function.Injective
        (fun (C : {C // C ∈ classSet F}) => (C.1).erase u) := by
    apply erase_on_classSet_injective_of_parallel hasU
      (F := F) (hu := hu) (hne := huv) (hp := hp)
  -- `card (image f S) = card S` を得る
  have hcard_image :
      ((classSet F).image (fun C => C.erase u)).card
      = (classSet F).card := by
    apply Finset.card_image_of_injOn

    exact Set.injOn_iff_injective.mpr hinj
  have hnum :
      numClasses (traceAt u F) = numClasses F := by
    unfold numClasses
    have : (classSet (traceAt u F)).card
           = ((classSet F).image (fun C => C.erase u)).card :=
      congrArg Finset.card hclassSet
    have : (classSet (traceAt u F)).card = (classSet F).card :=
      Eq.trans this hcard_image
    exact this

  unfold excess
  -- Left side - Was it not used?
  have L :
      (traceAt u F).ground.card - numClasses (traceAt u F)
      = (F.ground.card:Int) - (1 + numClasses F) := by
    have : (traceAt u F).ground.card = F.ground.card - 1 := hground
    have : (F.ground.card - 1) - numClasses (traceAt u F)
           = F.ground.card - (1 + numClasses (traceAt u F)) :=
      Nat.sub_sub _ _ _
    have : F.ground.card - (1 + numClasses (traceAt u F))
           = F.ground.card - (1 + numClasses F) := by
      exact congrArg (fun t => F.ground.card - (1 + t)) hnum

    have : (traceAt u F).ground.card - numClasses (traceAt u F)
           = (F.ground.card:Int) - (1 + numClasses (traceAt u F)) := by
      simp
      simp at this
      simp_all
      omega

    rw [this]
    simp_all only [ge_iff_le, Finset.one_le_card, ne_eq, Parallel, traceAt_ground, Finset.card_erase_of_mem, Nat.cast_sub,
    Nat.cast_one]

  have R :
      F.ground.card - numClasses F - 1
      = F.ground.card - (numClasses F + 1) := by
    exact Nat.sub_sub _ _ _
  have : (traceAt u F).ground.card - numClasses (traceAt u F)
          = F.ground.card - (numClasses F + 1) := by
    have : F.ground.card - (1 + numClasses F)
           = F.ground.card - (numClasses F + 1) :=
      by
        exact congrArg (fun t => F.ground.card - t) (Nat.add_comm 1 (numClasses F))
    have L' :
        (traceAt u F).ground.card - numClasses (traceAt u F)
        = F.ground.card - (1 + numClasses F) := by
      rw [←hnum]
      rw [hground]
      omega

    exact Eq.trans L' this
  calc
    excess (traceAt u F)
        = (traceAt u F).ground.card - numClasses (traceAt u F) := rfl
    _   = F.ground.card - (numClasses F + 1) := this
    _   = (F.ground.card - numClasses F) - 1 := by
            exact Eq.symm (Nat.sub_sub _ _ _)
    _   = excess F - 1 := rfl

private lemma erase_on_edges_injective_of_parallel
    (F : SetFamily α) {u v : α}
    (huv : F.Parallel u v) (hne : u ≠ v) :
    Function.Injective
      (fun (A : {A // A ∈ F.edgeFinset}) => (A.1).erase u) := by
  classical
  intro A B h
  apply Subtype.ext
  apply Finset.ext
  intro x
  by_cases hx : x = u
  ·

    have hAsets : F.sets A.1 :=
      (SetFamily.mem_edgeFinset_iff_sets F).mp A.2

    have hBsets : F.sets B.1 :=
      (SetFamily.mem_edgeFinset_iff_sets F).mp B.2

    have hv_on_erases :
        (v ∈ A.1.erase u) ↔ (v ∈ B.1.erase u) := by
      constructor <;> intro hv' <;> simpa [h] using hv'
    have hvAB : (v ∈ A.1) ↔ (v ∈ B.1) := by
      have hvne : v ≠ u := (ne_comm).1 hne
      simpa [Finset.mem_erase, hvne] using hv_on_erases
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
          have : B.1 ∈ {A : Finset α | F.sets A ∧ v ∈ A} := by
            rw [huv] at this
            exact this
          rw [Set.mem_setOf_eq] at this
          exact this.2
  ·
    have hx_on_erases :
        (x ∈ A.1.erase u) ↔ (x ∈ B.1.erase u) := by
      constructor <;> intro hx' <;> simpa [h] using hx'

    simpa [Finset.mem_erase, hx] using hx_on_erases



/-- The edge set after trace matches the image of the original edge set with `erase u` applied.
`parallel` is not needed here (identity of image sets). -/
private lemma edgeFinset_trace_eq_image_erase_of_parallel
    (F : SetFamily α) {u v : α}
    (_ : F.Parallel u v) (_ : u ≠ v) :
    (traceAt u F).edgeFinset = F.edgeFinset.image (fun A => A.erase u) := by
  classical
  apply Finset.ext
  intro B
  constructor
  ·
    intro hB
    have hBsets : (traceAt u F).sets B :=
      (mem_edgeFinset_iff_sets (F := traceAt u F) (A := B)).1 hB

    rcases (sets_traceAt_iff (F := F) (u := u) (B := B)).1 hBsets with ⟨A, hA, rfl⟩

    exact Finset.mem_image.mpr
      ⟨A, (mem_edgeFinset_iff_sets (F := F) (A := A)).2 hA, rfl⟩
  ·
    intro hB
    rcases Finset.mem_image.mp hB with ⟨A, hAedge, hBdef⟩
    have hAsets : F.sets A :=
      (mem_edgeFinset_iff_sets (F := F) (A := A)).1 hAedge
    have : (traceAt u F).sets (A.erase u) :=
      (sets_traceAt_iff (F := F) (u := u) (B := A.erase u)).2 ⟨A, hAsets, rfl⟩
    simpa [hBdef] using
      (mem_edgeFinset_iff_sets (F := traceAt u F) (A := A.erase u)).2 this


private lemma numHyperedges_preserved_of_parallel
    (F : SetFamily α) {u v : α}
    (huv : F.Parallel u v) (hne : u ≠ v) :
    (traceAt u F).numHyperedges = F.numHyperedges := by
  classical
  have himg :
      (traceAt u F).edgeFinset
        = F.edgeFinset.image (fun A => A.erase u) :=
    edgeFinset_trace_eq_image_erase_of_parallel (F := F) (u := u) (v := v) huv hne

  have hinj_on :
      ∀ A ∈ F.edgeFinset, ∀ B ∈ F.edgeFinset,
        (A.erase u) = (B.erase u) → A = B := by
    intro A hA B hB hEq
    have hsub_inj :=
      @erase_on_edges_injective_of_parallel α _ F u v huv hne
    unfold Function.Injective at hsub_inj
    simp_all only [Parallel, ne_eq, mem_edgeFinset, Subtype.forall, Subtype.mk.injEq, and_imp, subset_refl]
    apply hsub_inj
    · exact hA.1
    · exact hA.2
    · exact hB.1
    · exact hB.2
    · exact hEq

  have hcard_image :
      (F.edgeFinset.image (fun A => A.erase u)).card
        = F.edgeFinset.card :=
    Finset.card_image_iff.mpr hinj_on

  simp [numHyperedges, himg, hcard_image]

private lemma sum_edge_sizes_split_by_u
    (F : SetFamily α) (u : α) :
    (∑ A ∈ F.edgeFinset, A.card)
      = (∑ A ∈ F.edgeFinset, (A.erase u).card) + F.degree u := by
  classical
  have hpt :
      ∀ A : Finset α,
        A.card = (A.erase u).card + (if u ∈ A then 1 else 0) := by
    intro A; by_cases huA : u ∈ A
    ·
      have : (A.erase u).card = A.card - 1 := by
        simp [huA]


      have hpos : 0 < A.card := by
        exact Finset.card_pos.mpr ⟨u, huA⟩

      simpa [this, huA] using by
        have := this

        exact (by
          have := Nat.succ_pred_eq_of_pos hpos

          simpa [Nat.succ_eq_add_one, Nat.add_comm] using this.symm)
    ·
      simp [huA]
  have hsum :
      (∑ A ∈ F.edgeFinset, A.card)
        = ∑ A ∈ F.edgeFinset, ((A.erase u).card + (if u ∈ A then 1 else 0)) := by
    refine Finset.sum_congr rfl ?_
    intro A hA; simp [hpt A]
  rw [hsum]

  simp [Finset.sum_add_distrib]
  exact Eq.symm (SetFamily.degree_eq_card_filter F u)

/-- Refined version using trace's edge set (replacing with image using parallel). -/
private lemma sum_edge_sizes_trace_version_of_parallel
    (F : SetFamily α) {u v : α}
    (huv : F.Parallel u v) (hne : u ≠ v) :
    (∑ A ∈ F.edgeFinset, A.card)
      = (∑ B ∈ (traceAt u F).edgeFinset, B.card) + F.degree u := by
  classical
  have hsplit := sum_edge_sizes_split_by_u (F := F) u
  have himg :
      (traceAt u F).edgeFinset
        = F.edgeFinset.image (fun A => A.erase u) :=
    edgeFinset_trace_eq_image_erase_of_parallel (F := F) (u := u) (v := v) huv hne
  have hinj_on :
      ∀ A ∈ F.edgeFinset, ∀ B ∈ F.edgeFinset,
        (A.erase u) = (B.erase u) → A = B := by
    intro A hA B hB hEq
    have hsub_inj :=
      @erase_on_edges_injective_of_parallel α _ F u v huv hne
    unfold Function.Injective at hsub_inj
    simp_all only [Parallel, ne_eq, mem_edgeFinset, Subtype.forall, Subtype.mk.injEq, and_imp, subset_refl]
    apply hsub_inj
    · exact hA.1
    · exact hA.2
    · exact hB.1
    · exact hB.2
    · exact hEq

  have hsum_image :
      (∑ A ∈ F.edgeFinset, (A.erase u).card)
        = (∑ B ∈ (F.edgeFinset.image (fun A => A.erase u)), B.card) :=
    (Finset.sum_image hinj_on).symm

  calc
    (∑ A ∈ F.edgeFinset, A.card)
        = (∑ A ∈ F.edgeFinset, (A.erase u).card) + F.degree u := hsplit
    _   = (∑ B ∈ (F.edgeFinset.image (fun A => A.erase u)), B.card) + F.degree u := by
            simp [hsum_image]
    _   = (∑ B ∈ (traceAt u F).edgeFinset, B.card) + F.degree u := by
            simp [himg]


/-- Goal: NDS equality. Used from Reduction.lean.
  Using `NDS(F) = 2 * Σ|A| - |E(F)| * |ground|`.
  Assumption: `u` belongs to ground and `v` is a parallel partner of `u`. -/
theorem NDS_eq_of_parallel
    (F : SetFamily α) {u v : α}
    (huv : F.Parallel u v) (hne : u ≠ v) (hu : u ∈ F.ground):
    F.NDS = (traceAt u F).NDS + 2 * (F.degree u : Int) - (F.numHyperedges : Int) := by
classical
  -- ⑧ (Nat) lifted to Int:
  have hsum_nat :
      (∑ A ∈ F.edgeFinset, A.card)
        = (∑ B ∈ (traceAt u F).edgeFinset, B.card) + F.degree u :=
    sum_edge_sizes_trace_version_of_parallel (F := F) (u := u) (v := v) huv hne
  have hsum_int :
      (∑ A ∈ F.edgeFinset, (A.card : Int))
        = (∑ B ∈ (traceAt u F).edgeFinset, (B.card : Int))
          + (F.degree u : Int) := by
    have := congrArg (fun n : ℕ => (n : Int)) hsum_nat
    simpa [Nat.cast_sum, Nat.cast_add] using this

  have hE_nat :
      (traceAt u F).numHyperedges = F.numHyperedges :=
    numHyperedges_preserved_of_parallel (F := F) (u := u) (v := v) huv hne
  have hE_int :
      ((traceAt u F).numHyperedges : Int) = (F.numHyperedges : Int) := by
    simpa using congrArg (fun n : ℕ => (n : Int)) hE_nat

  have hV_nat :
      (traceAt u F).ground.card = F.ground.card - 1 :=
    ground_card_trace_of_mem (F := F) hu
  have hV_pos : 0 < F.ground.card := Finset.card_pos.mpr ⟨u, hu⟩
  have hsucc :
      (traceAt u F).ground.card + 1 = F.ground.card := by
    simp
    let nc := (Nat.succ_pred_eq_of_pos hV_pos)
    simp_all only [Parallel, ne_eq, traceAt_ground, Finset.card_erase_of_mem]
    exact nc

  have hV_int_eq :
      (F.ground.card : Int) = ((traceAt u F).ground.card : Int) + 1 := by
    have := congrArg (fun n : ℕ => (n : Int)) hsucc
    simp
    exact id (Eq.symm this)

  calc
    F.NDS
        = 2 * (∑ A ∈ F.edgeFinset, (A.card : Int))
            - (F.numHyperedges : Int) * (F.ground.card : Int) := by
            let nd := NDS_def F
            rw [nd]
            dsimp [SetFamily.totalHyperedgeSize]
            simp_all only [Parallel, ne_eq, traceAt_ground, Finset.card_erase_of_mem, Finset.card_pos, Finset.one_le_card,
               Nat.sub_add_cancel, Nat.cast_sub, Nat.cast_one, sub_add_cancel, Nat.cast_add, Nat.cast_sum]
    _   = 2 * ( (∑ B ∈ (traceAt u F).edgeFinset, (B.card : Int))
                + (F.degree u : Int))
            - ((traceAt u F).numHyperedges : Int) * (((traceAt u F).ground.card : Int) + 1) := by
            simp [hsum_int, hE_int, hV_int_eq]

    _   = (2 * (∑ B ∈ (traceAt u F).edgeFinset, (B.card : Int))
            - ((traceAt u F).numHyperedges : Int) * ((traceAt u F).ground.card : Int))
          + (2 * (F.degree u : Int) - ((traceAt u F).numHyperedges : Int)) := by
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
            simp [two_mul, mul_add, add_comm, add_left_comm, add_assoc,
                   sub_eq_add_neg]
    _   = (traceAt u F).NDS + (2 * (F.degree u : Int) - (F.numHyperedges : Int)) := by
            simp [ hE_int]
            dsimp [SetFamily.totalHyperedgeSize]
            exact Eq.symm (Nat.cast_sum (traceAt u F).edgeFinset Finset.card)
  exact add_sub_assoc' (traceAt u F).NDS (2 * ↑(F.degree u)) ↑F.numHyperedges

end SetFamily

end AvgRare
