import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Logic.Relation
import Mathlib.Algebra.Order.Sub.Basic
import AvgRare.Basics.SetFamily
import AvgRare.Functional.FuncSetup
import AvgRare.Functional.FuncPoset

universe u


namespace AvgRare
namespace UniqueMax
open Classical
variable {α : Type u} [DecidableEq α]
open AvgRare
open FuncSetup

lemma erase_nonempty(A:Finset α) (hA : A.card ≥ 2) (hu : u ∈ A) : (A.erase u).Nonempty := by
  have card_pos : 0 < (A.erase u).card := by
    calc
      0 < A.card - 1 := by omega
      _ = (A.erase u).card := by rw [Finset.card_erase_of_mem hu]
  exact Finset.card_pos.1 card_pos

--PosetTrace, which is limited to the maximum, will later appear.
--Geq2 is assumed to ensure that the one that has been traces is non-empty.
noncomputable def posetTraceCore (S : FuncSetup α) (m : S.Elem) (geq2: S.ground.card ≥ 2): FuncSetup α :=
{ ground := S.ground.erase m.1
  nonempty := by
   let en := erase_nonempty S.ground geq2 m.property
   exact Finset.Nonempty.to_subtype en
, f := by
    refine fun x => by
      classical
      let x₀ : S.Elem := ⟨x.1, (Finset.mem_erase.mp x.2).2⟩
      by_cases hx : S.f x₀ = m
      · exact ⟨x.1, by
          simp_all only [Finset.coe_mem, x₀]⟩
      · exact ⟨(S.f x₀).1, by
          simp_all only [Finset.mem_erase, ne_eq, Finset.coe_mem, and_true, x₀]
          apply Aesop.BuiltinRules.not_intro
          intro a
          apply hx
          simp_all only
          exact hx (Subtype.ext a)
        ⟩
}

/- (From the definition) the platform set of `posetTraceCore` is `erase m`。 -/
@[simp] lemma posetTraceCore_ground
  (S : FuncSetup α) (m : S.Elem) (geq2: S.ground.card ≥ 2):
  (posetTraceCore S m geq2).ground = S.ground.erase m.1 :=
rfl

--m is not assumed to be the maximum.
/-- If `S.cover x y` and `y ≠ m`, then `posetTraceCore` is the same。 -/
private lemma cover_preserved_if_target_ne_m
  (S : FuncSetup α) (m : S.Elem) (geq2: S.ground.card ≥ 2)
  {x y : α}
  (hx : x ∈ S.ground.erase m.1) (hy : y ∈ S.ground.erase m.1)
  (hxy : S.cover ⟨x, (Finset.mem_erase.mp hx).2⟩ ⟨y, (Finset.mem_erase.mp hy).2⟩) :
  (posetTraceCore S m geq2).cover ⟨x, hx⟩ ⟨y, hy⟩ := by
  let xS : S.Elem := ⟨x, (Finset.mem_erase.mp hx).2⟩
  let yS : S.Elem := ⟨y, (Finset.mem_erase.mp hy).2⟩
  have hy_ne : y ≠ m.1 := (Finset.mem_erase.mp hy).1

  have hfy : S.f xS = yS := hxy
  have hfx_ne_m : S.f xS ≠ m := by
    intro hbad
    have : (S.f xS).1 = m.1 := congrArg Subtype.val hbad
    have : y = m.1 := by
      simp_all [xS, yS]
    exact hy_ne this
  change (posetTraceCore S m geq2).f ⟨x, hx⟩ = ⟨y, hy⟩
  dsimp [posetTraceCore]
  by_cases h : S.f xS = m
  · exact (hfx_ne_m h).elim
  apply Subtype.ext
  apply congrArg Subtype.val
  simp_all only [ne_eq, not_false_eq_true, xS, yS]
  simp_all only [↓reduceDIte]

/-- Reverse: If `S.f x ≠ m`, the cover with `posetTraceCore` returns to the original cover. -/
private lemma cover_reflect_if_source_not_to_m
  (S : FuncSetup α) (m : S.Elem) (geq2: S.ground.card ≥ 2)
  {x y : α}
  (hx : x ∈ S.ground.erase m.1) (hy : y ∈ S.ground.erase m.1)
  (hfx_ne_m : S.f ⟨x, (Finset.mem_erase.mp hx).2⟩ ≠ m)
  (h : (posetTraceCore S m geq2 ).cover ⟨x, hx⟩ ⟨y, hy⟩) :
  S.cover ⟨x, (Finset.mem_erase.mp hx).2⟩ ⟨y, (Finset.mem_erase.mp hy).2⟩ := by
  let xS : S.Elem := ⟨x, (Finset.mem_erase.mp hx).2⟩
  let yS : S.Elem := ⟨y, (Finset.mem_erase.mp hy).2⟩
  change S.f xS = yS
  have : (posetTraceCore S m geq2).f ⟨x, hx⟩ = ⟨y, hy⟩ := h
  dsimp [posetTraceCore] at this
  by_cases h' : S.f xS = m
  · exact (hfx_ne_m h').elim
  have hv : (S.f xS).1 = y := by
    have := congrArg Subtype.val this
    subst this
    simp_all only [ne_eq, not_false_eq_true, posetTraceCore_ground, xS]
    simp_all only [↓reduceDIte]

  apply Subtype.ext
  exact hv

/-- Covering with `S' = posetTraceCore S m` is
If the original does not point to `m`, return to the original cover,
If it refers to `m`, it is limited to its own loop to itself. -/
private lemma cover_in_posetTraceCore_elim
  (S : FuncSetup α) (m : S.Elem) (geq2: S.ground.card ≥ 2)
  {x y : (posetTraceCore S m geq2).Elem}
  (hxy : (posetTraceCore S m geq2).cover x y) :
  y = x ∨
    S.cover
      ⟨x.1, (Finset.mem_erase.mp x.2).2⟩
      ⟨y.1, (Finset.mem_erase.mp y.2).2⟩ := by
  let xS : S.Elem := ⟨x.1, (Finset.mem_erase.mp x.2).2⟩
  let yS : S.Elem := ⟨y.1, (Finset.mem_erase.mp y.2).2⟩
  by_cases hfx : S.f xS = m
  ·
    have hv : ((posetTraceCore S m geq2).f x).1 = y.1 := congrArg Subtype.val hxy
    dsimp [posetTraceCore] at hv
    have hv' : x.1 = y.1 := by
      by_cases h' : S.f xS = m
      · simp_all only [posetTraceCore_ground, ↓reduceDIte, Subtype.coe_eta, xS]
      · exact False.elim (h' hfx)
    left
    apply Subtype.ext
    exact hv'.symm
  ·
    have hxmem : x.1 ∈ S.ground.erase m.1 := x.2
    have hymem : y.1 ∈ S.ground.erase m.1 := y.2
    have hc :
      S.cover ⟨x.1, (Finset.mem_erase.mp hxmem).2⟩
              ⟨y.1, (Finset.mem_erase.mp hymem).2⟩ :=
      cover_reflect_if_source_not_to_m
        (S := S) (m := m) (x := x.1) (y := y.1)
        geq2 hxmem hymem hfx hxy
    right
    exact hc

/-- `S' = posetTraceCore S m` reach relationship is
Discarding the loop and returning it to the original cover one hand at a time to make it appear in `S.le`. -/
private lemma le_reflect_to_S_posetTraceCore
  (S : FuncSetup α) (m : S.Elem) (geq2: S.ground.card ≥ 2)
  {x y : (posetTraceCore S m geq2).Elem}
  (hxy : Relation.ReflTransGen (posetTraceCore S m geq2).cover x y) :
  Relation.ReflTransGen S.cover
    ⟨x.1, (Finset.mem_erase.mp x.2).2⟩
    ⟨y.1, (Finset.mem_erase.mp y.2).2⟩ := by

  let S' := posetTraceCore S m
  let toS : (S' geq2).Elem → S.Elem := fun z =>
    ⟨z.1, (Finset.mem_erase.mp z.2).2⟩
  refine Relation.ReflTransGen.rec ?h0 ?hstep hxy
  · -- refl
    exact Relation.ReflTransGen.refl
  · -- tail: x ≤' b → cover b c → x ≤ c
    intro b c hb hbc ih
    have hsplit := cover_in_posetTraceCore_elim (S := S) (m := m) (x := b) (y := c) geq2 hbc
    cases hsplit with
    | inl h_eq =>
        have : toS b = toS c := by
          apply Subtype.ext
          apply congrArg Subtype.val
          exact congrArg toS h_eq.symm
        subst h_eq
        simp_all only [posetTraceCore_ground, toS, S']

    | inr h_cov =>
        exact Relation.ReflTransGen.tail ih h_cov


/-- If `S` is partial order, `posetTraceCore S m` is partial order. -/
-- m is not assumed to be the maximum.
-- this theorem is use in MainStatement
theorem isPoset_posetTraceCore
  (S : FuncSetup α) (hpos : isPoset S) (m : S.Elem) (geq2: S.ground.card ≥ 2) :
  isPoset (posetTraceCore S m geq2)  := by
  have :(posetTraceCore S m geq2).has_le_antisymm  := by
    intro x y hxy hyx
    have H₁ :
      Relation.ReflTransGen S.cover
        ⟨x.1, (Finset.mem_erase.mp x.2).2⟩
        ⟨y.1, (Finset.mem_erase.mp y.2).2⟩ :=
      le_reflect_to_S_posetTraceCore (S := S) (m := m) (x := x) (y := y) geq2 hxy
    have H₂ :
      Relation.ReflTransGen S.cover
        ⟨y.1, (Finset.mem_erase.mp y.2).2⟩
        ⟨x.1, (Finset.mem_erase.mp x.2).2⟩ :=
      le_reflect_to_S_posetTraceCore (S := S) (m := m) (x := y) (y := x) geq2 hyx

    have : (⟨x.1, (Finset.mem_erase.mp x.2).2⟩ : S.Elem)
         = (⟨y.1, (Finset.mem_erase.mp y.2).2⟩ : S.Elem) := by
      exact hpos H₁ H₂

    apply Subtype.ext
    apply congrArg Subtype.val
    simp_all only [le_iff_leOn_val, posetTraceCore_ground, Subtype.mk.injEq]
    obtain ⟨val_1, property_1⟩ := x
    subst this
    simp_all only [posetTraceCore_ground]
    exact rfl

  dsimp [isPoset]
  simp_all

---The number of Ideals must be equal or greater than the set of machines +1.Important, but only quoted in the file.
private theorem ideals_card_ge_ground_card_succ
  (S : FuncSetup α) (hpos : isPoset S) :
  (S.idealFamily).numHyperedges ≥ S.ground.card + 1 := by
  classical
  -- 下界集合 P
  let P : Finset (Finset α) :=
    (S.ground.attach.image (fun x : S.Elem => S.principalIdeal x.1 x.2)) ∪ {∅}
  -- P ⊆ edgeFinset
  have hPsub : P ⊆ (S.idealFamily).edgeFinset := by
    intro A hA
    have h := Finset.mem_union.mp hA
    cases h with
    | inl h1 =>
        rcases Finset.mem_image.mp h1 with ⟨x, hx, rfl⟩
        exact S.principalIdeal_mem_edge x
    | inr h0 =>
        have hA0 : A = (∅ : Finset α) := Finset.mem_singleton.mp h0
        have := S.empty_mem_edge
        exact hA0 ▸ this

  have hEdgeGeP : (S.idealFamily).edgeFinset.card ≥ P.card := by
    simp_all [Finset.union_singleton, ge_iff_le, P]
    exact Finset.card_le_card hPsub

  have hInj :
    ∀ ⦃x⦄, x ∈ S.ground.attach →
    ∀ ⦃y⦄, y ∈ S.ground.attach →
      (S.principalIdeal x.1 x.2 = S.principalIdeal y.1 y.2) → x = y := by
    intro x hx y hy hxy
    exact S.principalOn_inj (hpos := hpos) (x := x) (y := y) (hxy := hxy)

  have hCardImage :
      (S.ground.attach.image (fun x : S.Elem => S.principalIdeal x.1 x.2)).card
        = S.ground.attach.card :=
    Finset.card_image_iff.mpr hInj

  have hCardAttach : S.ground.attach.card = S.ground.card :=
    Finset.card_attach

  have hDisj :
      Disjoint
        (S.ground.attach.image (fun x : S.Elem => S.principalIdeal x.1 x.2))
        ({∅} : Finset (Finset α)) := by
    refine Finset.disjoint_left.mpr ?_
    intro A hA hA0
    rcases Finset.mem_image.mp hA with ⟨x, _, rfl⟩
    have hx_self : x.1 ∈ S.principalIdeal x.1 x.2 := by
      have hxx : S.le x x := Relation.ReflTransGen.refl
      exact (S.mem_principalIdeal_iff (a := x.1) (y := x.1) x.2).2 ⟨x.2, hxx⟩
    simp_all [Finset.union_singleton, ge_iff_le, Finset.card_attach, Finset.mem_attach, Finset.mem_image, true_and,
    exists_apply_eq_apply, Finset.mem_singleton, Finset.notMem_empty, P]

  have hPcard :
      P.card
        = (S.ground.attach.image (fun x : S.Elem => S.principalIdeal x.1 x.2)).card + 1 :=
    Finset.card_union_of_disjoint hDisj

  have hP_eq : P.card = S.ground.card + 1 := by
    calc
      P.card = (S.ground.attach.image (fun x : S.Elem => S.principalIdeal x.1 x.2)).card + 1 := hPcard
      _ = S.ground.attach.card + 1 := by rw [hCardImage]
      _ = S.ground.card + 1 := by rw [hCardAttach]

  exact le_of_eq_of_le hP_eq.symm hEdgeGeP

--使っている
private lemma lift_le_to_traceCore_if_not_m_below
  (S : FuncSetup α) (m : S.Elem) (geq2: S.ground.card ≥ 2)
  (hpos : isPoset S) (hmax : S.maximal m)
  {a b : (posetTraceCore S m geq2).Elem}
  (h : Relation.ReflTransGen S.cover
        ⟨a.1, (Finset.mem_erase.mp a.2).2⟩
        ⟨b.1, (Finset.mem_erase.mp b.2).2⟩) :
  Relation.ReflTransGen (posetTraceCore S m geq2).cover a b := by
  classical
  have hb_ne : b.1 ≠ m.1 := (Finset.mem_erase.mp b.2).1

  refine
    Relation.ReflTransGen.head_induction_on
      (r := S.cover)
      (b := ⟨b.1, (Finset.mem_erase.mp b.2).2⟩)
      (motive := fun z _ => ∀ (hz : z.1 ∈ S.ground.erase m.1),
        Relation.ReflTransGen (posetTraceCore S m geq2).cover ⟨z.1, hz⟩ ⟨b.1, b.2⟩)
      h
      ?base
      ?head
      (a := ⟨a.1, (Finset.mem_erase.mp a.2).2⟩)
      (by exact a.2)
  · intro hb
    have eb : (⟨b.1, hb⟩ : (posetTraceCore S m geq2).Elem) = b := Subtype.ext (by rfl)
    cases eb
    exact Relation.ReflTransGen.refl
  · intro z c hzc hcb ih hz
    have hc_ne_m : c ≠ m := by
      intro hc
      have hmb : S.le m ⟨b.1, (Finset.mem_erase.mp b.2).2⟩ := by
        cases hc
        exact hcb
      have hbm : S.le ⟨b.1, (Finset.mem_erase.mp b.2).2⟩ m := hmax hmb
      have heq : ⟨b.1, (Finset.mem_erase.mp b.2).2⟩ = m := by
        exact hpos (hmax hmb) hmb
      have : b.1 = m.1 := congrArg Subtype.val heq
      exact hb_ne this
    have hc_mem : c.1 ∈ S.ground.erase m.1 := by
      refine Finset.mem_erase.mpr ?_
      refine And.intro ?neq c.property
      have : c.1 ≠ m.1 := by
        intro hv
        apply hc_ne_m
        exact Subtype.ext hv
      exact this
    have hzc' :
        (posetTraceCore S m geq2).cover ⟨z.1, hz⟩ ⟨c.1, hc_mem⟩ := by
      have hL :
          (⟨z.1, (Finset.mem_erase.mp hz).2⟩ : S.Elem) = ⟨z.1, z.property⟩ :=
        Subtype.ext (by rfl)
      have hR :
          (⟨c.1, (Finset.mem_erase.mp hc_mem).2⟩ : S.Elem) = ⟨c.1, c.property⟩ :=
        Subtype.ext (by rfl)
      have hxy :
        S.cover ⟨z.1, (Finset.mem_erase.mp hz).2⟩ ⟨c.1, (Finset.mem_erase.mp hc_mem).2⟩ := by
        cases hL
        cases hR
        exact hzc
      exact cover_preserved_if_target_ne_m (S := S) (m := m) (geq2 := geq2)
        (hx := hz) (hy := hc_mem) (hxy := hxy)
    have hcb' :
        Relation.ReflTransGen (posetTraceCore S m geq2).cover ⟨c.1, hc_mem⟩ ⟨b.1, b.2⟩ :=
      ih hc_mem
    exact Relation.ReflTransGen.head hzc' hcb'

--Called also from Forest.lean.
lemma edgeFinset_trace_eq_filter_not_mem
  (S : FuncSetup α) [Fintype S.Elem]
  (m : S.Elem) (geq2: S.ground.card ≥ 2)
  (hKeep :
    ∀ I : Finset α, SetFamily.isOrderIdealOn (S.leOn) S.ground I →
      m.1 ∉ I →
      ((posetTraceCore S m geq2).idealFamily).sets I)
  (hBack :
    ∀ I : Finset α,
      ((posetTraceCore S m geq2).idealFamily).sets I →
      (S.idealFamily).sets I ∧ m.1 ∉ I) :
  ((posetTraceCore S m geq2).idealFamily).edgeFinset
    = (S.idealFamily).edgeFinset.filter (fun A => m.1 ∉ A) := by
  classical
  set F  := S.idealFamily
  set F' := (posetTraceCore S m geq2).idealFamily

  apply Finset.Subset.antisymm_iff.mpr
  constructor
  ·
    intro A hA

    have hA_sets' : F'.sets A :=
      (SetFamily.mem_edgeFinset_iff_sets (F := F') (A := A)).1 hA

    have hback := hBack A hA_sets'
    have hA_sets : F.sets A := hback.1
    have hm_not : m.1 ∉ A := hback.2

    have hA_edge : A ∈ F.edgeFinset :=
      (SetFamily.mem_edgeFinset_iff_sets (F := F) (A := A)).2 hA_sets

    exact Finset.mem_filter.mpr ⟨hA_edge, hm_not⟩
  ·
    intro A hA

    have hA_edge : A ∈ F.edgeFinset := (Finset.mem_filter.mp hA).1
    have hm_not  : m.1 ∉ A           := (Finset.mem_filter.mp hA).2

    have hA_sets : F.sets A :=
      (SetFamily.mem_edgeFinset_iff_sets (F := F) (A := A)).1 hA_edge

    have hA_ideal : SetFamily.isOrderIdealOn (S.leOn) S.ground A :=
      (S.sets_iff_isOrderIdeal (I := A)).1 hA_sets

    have hA_sets' : F'.sets A := hKeep A hA_ideal hm_not

    exact (SetFamily.mem_edgeFinset_iff_sets (F := F') (A := A)).2 hA_sets'

--proved by edgeFinset_trace_eq_filter_not_mem. Called also from Forest.lean.
lemma edge_card_trace_eq_filter_not_mem
  (S : FuncSetup α) [Fintype S.Elem]
  (m : S.Elem) (geq2: S.ground.card ≥ 2)
  (hKeep :
    ∀ I : Finset α, SetFamily.isOrderIdealOn (S.leOn) S.ground I →
      m.1 ∉ I →
      ((posetTraceCore S m geq2).idealFamily).sets I)
  (hBack :
    ∀ I : Finset α,
      ((posetTraceCore S m geq2 ).idealFamily).sets I →
      (S.idealFamily).sets I ∧ m.1 ∉ I) :
  ((posetTraceCore S m geq2).idealFamily).edgeFinset.card
    = ( (S.idealFamily).edgeFinset.filter (fun A => m.1 ∉ A) ).card := by
  classical

  have h := edgeFinset_trace_eq_filter_not_mem
              (S := S) (m := m) (hKeep := hKeep) (hBack := hBack)

  exact congrArg Finset.card h

noncomputable def posetTraceOfUnique
  (S : FuncSetup α) (geq2: S.ground.card ≥ 2) (hexu : ∃! m : S.Elem, S.maximal m) :
  FuncSetup α :=
  posetTraceCore S (Classical.choose (hexu).exists) geq2

private lemma all_below_unique_maximal
  (S : FuncSetup α) [Fintype S.Elem]
  (hpos : isPoset S) (hexu : ∃! m : S.Elem, S.maximal m) :
  ∀ u : S.Elem, S.le u (Classical.choose hexu.exists) := by
  classical
  set m : S.Elem := Classical.choose hexu.exists
  have hm : S.maximal m := Classical.choose_spec hexu.exists

  have uniq : ∀ {p : S.Elem}, S.maximal p → p = m := by
    intro p a
    simp_all [maximal_iff, le_iff_leOn_val, Subtype.forall, m]
    cases hexu
    simp_all [maximal_iff, le_iff_leOn_val, Finset.coe_mem, implies_true]
  intro u

  obtain ⟨p, hup, hpp⟩ :=
    FuncSetup.eventually_hits_fixpoint (S := S) (hpos := hpos) (x := u)

  have hpmax : S.maximal p := S.maximal_of_fixpoint hpp

  have pm : p = m := uniq hpmax

  cases pm
  exact hup

private lemma hOnlyTop_of_uniqueMax
  (S : FuncSetup α) [Fintype S.Elem]
  (hpos  : isPoset S)
  (hexu  : ∃! m : S.Elem, S.maximal m)
  {I : Finset α}
  (hI   : SetFamily.isOrderIdealOn (S.leOn) S.ground I)
  (hmI  : (Classical.choose hexu.exists).1 ∈ I) :
  I = S.ground := by

  classical

  set m : S.Elem := Classical.choose hexu.exists
  have hm : S.maximal m := Classical.choose_spec hexu.exists

  have hI_sub : I ⊆ S.ground := hI.1

  have hG_sub_I : S.ground ⊆ I := by
    intro y hy
    have hle_m : S.le ⟨y, hy⟩ m :=
      all_below_unique_maximal (S := S) (hpos := hpos) (hexu := hexu) ⟨y, hy⟩
    have hleOn : S.leOn y m.1 :=
      (leOn_iff S hy m.2).mpr hle_m
    exact hI.2 (x := m.1) hmI (y := y) hy hleOn

  exact Finset.Subset.antisymm hI_sub hG_sub_I

private lemma keep_sets_from_trace_at_without_m
  (S : FuncSetup α) (m : S.Elem) (geq2: S.ground.card ≥ 2) {I : Finset α}
  (hI  : SetFamily.isOrderIdealOn (S.leOn) S.ground I)
  (hmI : m.1 ∉ I) :
  ((posetTraceCore S m geq2).idealFamily).sets I := by
  -- `sets` ↔ `isOrderIdealOn`
  change SetFamily.isOrderIdealOn ((posetTraceCore S m geq2).leOn) ((posetTraceCore S m geq2).ground) I
  constructor
  · intro x hx
    have hxV : x ∈ S.ground := hI.1 hx
    have hne : x ≠ m.1 := by
      intro e; apply hmI; cases e; exact hx
    exact (by
      change x ∈ S.ground.erase m.1
      exact (Finset.mem_erase.mpr ⟨hne, hxV⟩))
  · intro x hxI y hyG' hle'   -- `hle' : leOn' y x`
    have hxV : x ∈ S.ground := hI.1 hxI
    have hyV : y ∈ S.ground := (Finset.mem_erase.mp (by
      change y ∈ S.ground.erase m.1 at hyG'
      exact hyG')).2
    have hx' : x ∈ (posetTraceCore S m geq2).ground := by
      have hSub : I ⊆ (posetTraceCore S m geq2).ground := by
        intro z hz
        have hzV : z ∈ S.ground := hI.1 hz
        have hz_ne : z ≠ m.1 := by
          intro e; apply hmI; cases e; exact hz
        change z ∈ S.ground.erase m.1
        exact Finset.mem_erase.mpr ⟨hz_ne, hzV⟩
      exact hSub hxI
    have hRTG' :
        Relation.ReflTransGen (posetTraceCore S m geq2).cover
          ⟨y, hyG'⟩ ⟨x, hx'⟩ :=
      ( (posetTraceCore S m geq2).leOn_iff_subtype (a := y) (b := x) hyG' hx').1 hle'

    have hRTG :
        Relation.ReflTransGen S.cover
          ⟨y, (Finset.mem_erase.mp (by change y ∈ S.ground.erase m.1 at hyG'; exact hyG')).2⟩
          ⟨x, hxV⟩ :=
      le_reflect_to_S_posetTraceCore (S := S) (m := m) (x := ⟨y, hyG'⟩) (y := ⟨x, hx'⟩) geq2 hRTG'

    have hle : S.leOn y x := by
      have hySub : S.leOn y x ↔ S.le ⟨y, hyV⟩ ⟨x, hxV⟩ :=
        S.leOn_iff_subtype (a := y) (b := x) hyV hxV
      exact hySub.mpr hRTG

    exact hI.2 hxI hyV hle

--The maximum trace, and the group tribe after the trace is included in the original group tribe.
--Used to prove --back_sets_from_trace_at_max_sets'.It is used a lot.
--It is also used by Forest.
lemma back_sets_from_trace_at_max_sets
  (S : FuncSetup α) [Fintype S.Elem]
  (hpos : isPoset S) (m : S.Elem) (geq2: S.ground.card ≥ 2)(hm : S.maximal m)
  {I : Finset α}
  (hI : ((posetTraceCore S m geq2).idealFamily).sets I) :
  (S.idealFamily).sets I := by
  classical
  have hI' : SetFamily.isOrderIdealOn ((posetTraceCore S m geq2).leOn) ((posetTraceCore S m geq2).ground) I := by
    change SetFamily.isOrderIdealOn _ _ I
    exact ((posetTraceCore S m geq2).sets_iff_isOrderIdeal (I := I)).1 hI

  have hIsub' : I ⊆ (posetTraceCore S m geq2).ground := hI'.1
  have hIsubS : I ⊆ S.ground := by
    intro x hxI
    have hx' : x ∈ (posetTraceCore S m geq2).ground := hIsub' hxI
    rcases Finset.mem_erase.mp (by change x ∈ S.ground.erase m.1; exact hIsub' hxI) with ⟨_, hxG⟩
    exact hxG

  have hIdealS : SetFamily.isOrderIdealOn (S.leOn) S.ground I := by
    dsimp [SetFamily.isOrderIdealOn]
    constructor
    · exact hIsubS
    · intro x hxI y hyG hleOn
      have hx_ne_m : x ≠ m.1 := by
        have hx' : x ∈ (posetTraceCore S m geq2).ground := hIsub' hxI
        rcases Finset.mem_erase.mp (by change x ∈ S.ground.erase m.1; exact hIsub' hxI) with ⟨hxne, _⟩
        exact hxne
      by_cases hy_eq : y = m.1
      ·
        have hxG : x ∈ S.ground := hIsubS hxI
        have h_yx : S.le ⟨y, hyG⟩ ⟨x, hxG⟩ := (leOn_iff S hyG hxG).mp hleOn
        have hmx : S.le m ⟨x, hxG⟩ := by cases hy_eq; exact h_yx
        have hxm : S.le ⟨x, hxG⟩ m := hm hmx
        have : (⟨x, hxG⟩ : S.Elem) = m := by exact hpos (hm hmx) hmx
        have : x = m.1 := congrArg Subtype.val this
        have : False := hx_ne_m this
        exact this.elim
      ·
        have hyE : y ∈ S.ground.erase m.1 := by
          refine Finset.mem_erase.mpr ?_
          refine And.intro ?neq hyG
          intro h; exact hy_eq h
        have hxG : x ∈ S.ground := hIsubS hxI
        have hxE : x ∈ S.ground.erase m.1 := by
          refine Finset.mem_erase.mpr ?_
          refine And.intro hx_ne_m hxG
        have hSle : S.le ⟨y, hyG⟩ ⟨x, hxG⟩ :=
          (leOn_iff S hyG hxG).mp hleOn
        have hS'le :
            Relation.ReflTransGen (posetTraceCore S m geq2).cover
              ⟨y, hyE⟩ ⟨x, hxE⟩ :=
          lift_le_to_traceCore_if_not_m_below
            (S := S) (m := m) (hpos := hpos) (hmax := hm)
            (a := ⟨y, hyE⟩) (b := ⟨x, hxE⟩) (h := hSle)
        have hy' : y ∈ (posetTraceCore S m geq2).ground := by
          change y ∈ S.ground.erase m.1; exact hyE
        have hx' : x ∈ (posetTraceCore S m geq2).ground := by
          change x ∈ S.ground.erase m.1; exact hxE
        have hleOn' :
            (posetTraceCore S m geq2).leOn y x :=
          (leOn_iff (posetTraceCore S m geq2) hy' hx').mpr hS'le
        exact hI'.2 (x := x) hxI (y := y) hy' hleOn'

  exact (S.sets_iff_isOrderIdeal (I := I)).2 hIdealS

/-- "Back": The ideal on `posetTraceCore` is ideal on the S side, and `m ∉ I`. -/
private lemma back_sets_from_trace_at_max_sets'
  (S : FuncSetup α) [Fintype S.Elem]
  (hpos : isPoset S) {m : S.Elem}(geq2: S.ground.card ≥ 2) (hm : S.maximal m)
  {I : Finset α}
  (hI : ((posetTraceCore S m geq2).idealFamily).sets I) :
  (S.idealFamily).sets I ∧ m.1 ∉ I :=
by
  have hSets :
      (S.idealFamily).sets I :=
    back_sets_from_trace_at_max_sets (S := S) (hpos := hpos) (m := m) (hm := hm) (hI := hI)
  have hI' :
      SetFamily.isOrderIdealOn ((posetTraceCore S m geq2).leOn) ((posetTraceCore S m geq2).ground) I := by
    change SetFamily.isOrderIdealOn _ _ I
    exact ((posetTraceCore S m geq2).sets_iff_isOrderIdeal (I := I)).1 hI
  have hSub' : I ⊆ (posetTraceCore S m geq2).ground := hI'.1
  have hm_not : m.1 ∉ I := by
    intro hmI
    have : m.1 ∈ (posetTraceCore S m geq2).ground := hSub' hmI
    rcases Finset.mem_erase.mp this with ⟨heq, _⟩
    exact heq rfl
  exact ⟨hSets, hm_not⟩

private lemma arith_reduce (V n t : Nat) (hV : 1 ≤ V) :
  ((V : Int)
    + (-(V : Int)
       + ( -((n : Int) * (V : Int))
           + ((t : Int) + (t : Int)) )))
  =
  ( -(n : Int)
    + ( -((n : Int) * (↑(V - 1)))
        + ((t : Int) + (t : Int)) ) ) := by
  classical
  simp [add_assoc, add_comm, add_left_comm]
  have V_decomp : (V : Int) = (↑(V - 1) + 1) := by
    simpa [Nat.cast_add, Nat.cast_one] using
      congrArg (fun x : ℕ => (x : Int)) ((Nat.sub_add_cancel hV).symm)
  have split :
      -((n : Int) * (V : Int))
        = -(n : Int) + -((n : Int) * (↑(V - 1))) := by
    calc
      -((n : Int) * (V : Int))
          = (- (n : Int)) * (V : Int) := by
                exact Int.neg_mul_eq_neg_mul ↑n ↑V
      _ = (- (n : Int)) * (↑(V - 1) + 1) := by
                simp [V_decomp]
      _ = (- (n : Int)) * (↑(V - 1)) + (- (n : Int)) * 1 := by
                simp [mul_add]
      _ = -((n : Int) * (↑(V - 1))) + (-(n : Int)) := by
                simp [neg_mul, mul_one, add_comm]
    exact Int.add_comm (-(↑n * ↑(V - 1))) (-↑n)
  simp_all only [Nat.cast_sub, Nat.cast_one, sub_add_cancel]
  omega

/- Commented out since a shorter alternative proof was found
--This is a general transformation, so it could be moved to General.lean.
lemma arith_reduce (V n t : Nat) (hV : 1 ≤ V) :
  ((V : Int)
    + (-(V : Int)
       + ( -((n : Int) * (V : Int))
           + ((t : Int) + (t : Int)) )))
  =
  ( -(n : Int)
    + ( -((n : Int) * (↑(V - 1)))
        + ((t : Int) + (t : Int)) ) ) := by
  classical
  -- ↑(V-1) を (V:ℤ) - 1 に直す
  have hCast : (↑(V - 1) : Int) = (V : Int) - 1 := (Nat.cast_sub hV)

  -- 左辺を簡約： (V) + (-(V) + X) = X
  have hL :
      (V : Int)
        + (-(V : Int)
            + ( -((n : Int) * (V : Int))
                + ((t : Int) + (t : Int)) ))
      =
      ( -((n : Int) * (V : Int))
        + ((t : Int) + (t : Int)) ) := by
    calc
      (V : Int) + (-(V : Int) + _)
          = ((V : Int) + (-(V : Int))) + _ := by
                rw [add_assoc]
      _   = 0 + _ := by
                -- a + (-a) = 0
                exact Eq.symm (Int.zero_add (↑V + -↑V + (-(↑n * ↑V) + (↑t + ↑t))))
      _   = _ := by
                rw [zero_add]
                simp_all only [Nat.cast_sub, Nat.cast_one, add_neg_cancel, zero_add]

  -- 右辺を簡約： -(n) + (-(n*(V-1)) + (t+t)) を展開して -(n*V) + (t+t) に
  have hR :
      ( -(n : Int)
        + ( -((n : Int) * (↑(V - 1)))
            + ((t : Int) + (t : Int)) ) )
      =
      ( -((n : Int) * (V : Int))
        + ((t : Int) + (t : Int)) ) := by
    -- まず ↑(V-1) を (V:ℤ)-1 に置換
    have := hCast
    -- `rw [this]` を段階的に適用
    calc
      -(n : Int) + ( -((n : Int) * (↑(V - 1)))
                      + ((t : Int) + (t : Int)) )
          = -(n : Int) + ( -((n : Int) * ((V : Int) - 1))
                            + ((t : Int) + (t : Int)) ) := by
                rw [this]
      _   = -(n : Int) + ( -(((n : Int) * (V : Int)) - (n : Int))
                            + ((t : Int) + (t : Int)) ) := by
                -- n*(V-1) = n*V - n
                -- `mul_sub` と `mul_one`
                have hmul :
                    (n : Int) * ((V : Int) - 1)
                      = (n : Int) * (V : Int) - (n : Int) := by
                  calc
                    (n : Int) * ((V : Int) - 1)
                        = (n : Int) * (V : Int) - (n : Int) * (1 : Int) := by
                              exact (mul_sub (n : Int) (V : Int) (1 : Int))
                    _   = (n : Int) * (V : Int) - (n : Int) := by
                              -- (n:ℤ)*1 = n
                              simp_all only [add_neg_cancel_left, Nat.cast_sub, Nat.cast_one, mul_one]

                -- Rewrite the `- (n * ((V:ℤ)-1))` in LHS using the above equation
                -- Give it in `show` form for `rw`
                -- Actually `simp` would work too, but explicitly using `rw`
                have : -((n : Int) * ((V : Int) - 1))
                          = -(((n : Int) * (V : Int)) - (n : Int)) := by
                  -- 直前の hmul を使うだけ
                  exact congrArg Neg.neg hmul
                -- これを使って置換
                simp_all only [add_neg_cancel_left, Nat.cast_sub, Nat.cast_one, neg_sub]
      _   = -(n : Int) + ( (n : Int) - (n : Int) * (V : Int)
                            + ((t : Int) + (t : Int)) ) := by
                -- `-(A - B) = B - A`
                rw [Int.neg_sub ((n : Int) * (V : Int)) (n : Int)]
      _   = ( (-(n : Int) + (n : Int)) - (n : Int) * (V : Int)
              + ((t : Int) + (t : Int)) ) := by
                -- b - a = b + (-a)、結合で並べ替え
                -- まず外の `a + (b + c)` → `(a + b) + c`
                simp_all only [add_neg_cancel_left, Nat.cast_sub, Nat.cast_one, neg_add_cancel, zero_sub]
                omega
                -- ここまでで所望の並びに
      _   = ( -((n : Int) * (V : Int))
              + ((t : Int) + (t : Int)) ) := by
                -- `-(n) + n = 0`
                have : (-(n : Int)) + (n : Int) = 0 := by
                  exact Int.add_left_neg ↑n
                -- 0 + x = x
                calc
                  ( (-(n : Int) + (n : Int)) - (n : Int) * (V : Int)
                    + ((t : Int) + (t : Int)) )
                        = ( 0 - (n : Int) * (V : Int)
                            + ((t : Int) + (t : Int)) ) := by
                              rw [this]
                  _     = ( -((n : Int) * (V : Int))
                            + ((t : Int) + (t : Int)) ) := by
                              -- 0 - a = -a
                              simp [sub_eq_add_neg, add_comm, add_assoc]

  -- 左右を突き合わせて終了
  exact hL.trans hR.symm
-/

private lemma numHyperedges_trace_pred_of_max
  (S : FuncSetup α) [Fintype S.Elem]
  (m : S.Elem)(geq2: S.ground.card ≥ 2)
  (hOnlyTop :
    ∀ I : Finset α, SetFamily.isOrderIdealOn (S.leOn) S.ground I → m.1 ∈ I → I = S.ground)
  (hKeep :
    ∀ I : Finset α, SetFamily.isOrderIdealOn (S.leOn) S.ground I → m.1 ∉ I →
      ((posetTraceCore S m geq2).idealFamily).sets I)
  (hBack :
    ∀ I : Finset α, ((posetTraceCore S m geq2).idealFamily).sets I →
      (S.idealFamily).sets I ∧ m.1 ∉ I) :
  ((posetTraceCore S m geq2).idealFamily).numHyperedges + 1
    = (S.idealFamily).numHyperedges := by
  classical
  set F  := S.idealFamily
  set F' := (posetTraceCore S m geq2).idealFamily

  have hEdgeEq :
      F'.edgeFinset = F.edgeFinset.filter (fun A => m.1 ∉ A) :=
    edgeFinset_trace_eq_filter_not_mem (S := S) (m := m)
      (hKeep := hKeep) (hBack := hBack)

  have h_onlyTop_filter :
      (F.edgeFinset.filter (fun A => m.1 ∈ A)) = {S.ground} := by
    apply Finset.Subset.antisymm_iff.mpr; constructor
    · intro A hA
      have hA_edge : A ∈ F.edgeFinset := (Finset.mem_filter.mp hA).1
      have hmA    : m.1 ∈ A           := (Finset.mem_filter.mp hA).2
      have hA_ideal : SetFamily.isOrderIdealOn (S.leOn) S.ground A :=
        (S.sets_iff_isOrderIdeal (I := A)).1
          ((SetFamily.mem_edgeFinset_iff_sets (F := F) (A := A)).1 hA_edge)
      exact Finset.mem_singleton.mpr (hOnlyTop A hA_ideal hmA)
    · intro A hA
      have hAeq : A = S.ground := Finset.mem_singleton.mp hA
      have hGroundSets : F.sets S.ground :=
        (S.sets_iff_isOrderIdeal (I := S.ground)).2
          (by dsimp [SetFamily.isOrderIdealOn]; exact And.intro (by intro x hx; exact hx)
                (by intro x hx y hy _; exact hy))
      have hGroundEdge : S.ground ∈ F.edgeFinset :=
        (SetFamily.mem_edgeFinset_iff_sets (F := F) (A := S.ground)).2 hGroundSets
      have hmG : m.1 ∈ S.ground := m.2
      have h0 : S.ground ∈ F.edgeFinset.filter (fun A => m.1 ∈ A) :=
        Finset.mem_filter.mpr ⟨hGroundEdge, hmG⟩
      cases hAeq; exact h0

  have hSplit :
      (F.edgeFinset.filter (fun A => m.1 ∉ A)).card
        = F.edgeFinset.card - 1 := by
    have := Finset.filter_card_add_filter_neg_card_eq_card
               (s := F.edgeFinset) (p := fun A : Finset α => m.1 ∈ A)
    have hleft :
        (F.edgeFinset.filter (fun A => m.1 ∈ A)).card = 1 := by
      -- `card {ground} = 1`
      have : (F.edgeFinset.filter (fun A => m.1 ∈ A)) = {S.ground} := h_onlyTop_filter
      exact congrArg Finset.card this ▸ Finset.card_singleton _
    exact by
      have := Nat.eq_sub_of_add_eq' (hleft ▸ this)
      exact this
  have hF' :
      F'.edgeFinset.card
        = (F.edgeFinset.filter (fun A => m.1 ∉ A)).card := by
    exact congrArg Finset.card hEdgeEq
  have : F'.edgeFinset.card = F.edgeFinset.card - 1 := by
    simpa [hF'] using hSplit
  dsimp [SetFamily.numHyperedges]
  simp [this]
  let nhg := FuncSetup.numHyperedges_ge_one S
  dsimp [SetFamily.numHyperedges] at nhg
  dsimp [F]
  exact Nat.sub_add_cancel nhg

/-- Size sum: Just `|V|` decrease -/
private lemma totalHyperedgeSize_trace_sub_card_ground_of_max
  (S : FuncSetup α) [Fintype S.Elem]
  (m : S.Elem)(geq2: S.ground.card ≥ 2)
  (hOnlyTop :
    ∀ I : Finset α, SetFamily.isOrderIdealOn (S.leOn) S.ground I → m.1 ∈ I → I = S.ground)
  (hKeep :
    ∀ I : Finset α, SetFamily.isOrderIdealOn (S.leOn) S.ground I → m.1 ∉ I →
      ((posetTraceCore S m geq2).idealFamily).sets I)
  (hBack :
    ∀ I : Finset α, ((posetTraceCore S m geq2).idealFamily).sets I →
      (S.idealFamily).sets I ∧ m.1 ∉ I) :
  (S.idealFamily).totalHyperedgeSize
    = ((posetTraceCore S m geq2).idealFamily).totalHyperedgeSize
      + S.ground.card := by
  classical
  set F  := S.idealFamily
  set F' := (posetTraceCore S m geq2).idealFamily
  have hEdgeEq :
      F'.edgeFinset = F.edgeFinset.filter (fun A => m.1 ∉ A) :=
    edgeFinset_trace_eq_filter_not_mem
      (S := S) (m := m) (hKeep := hKeep) (hBack := hBack)
  have h_onlyTop_filter :
      (F.edgeFinset.filter (fun A => m.1 ∈ A)) = {S.ground} := by
    -- 同上
    apply Finset.Subset.antisymm_iff.mpr; constructor
    · intro A hA
      have hA_edge : A ∈ F.edgeFinset := (Finset.mem_filter.mp hA).1
      have hmA    : m.1 ∈ A           := (Finset.mem_filter.mp hA).2
      have hA_ideal : SetFamily.isOrderIdealOn (S.leOn) S.ground A :=
        (S.sets_iff_isOrderIdeal (I := A)).1
          ((SetFamily.mem_edgeFinset_iff_sets (F := F) (A := A)).1 hA_edge)
      exact Finset.mem_singleton.mpr (hOnlyTop A hA_ideal hmA)
    · intro A hA
      have hAeq : A = S.ground := Finset.mem_singleton.mp hA
      have hGroundSets : F.sets S.ground :=
        (S.sets_iff_isOrderIdeal (I := S.ground)).2
          (by dsimp [SetFamily.isOrderIdealOn]; exact And.intro (by intro x hx; exact hx)
                (by intro x hx y hy _; exact hy))
      have hGroundEdge : S.ground ∈ F.edgeFinset :=
        (SetFamily.mem_edgeFinset_iff_sets (F := F) (A := S.ground)).2 hGroundSets
      have hmG : m.1 ∈ S.ground := m.2
      have h0 : S.ground ∈ F.edgeFinset.filter (fun A => m.1 ∈ A) :=
        Finset.mem_filter.mpr ⟨hGroundEdge, hmG⟩
      cases hAeq; exact h0

  have hUnion : F'.edgeFinset ∪ {S.ground} = F.edgeFinset := by
    apply Finset.ext; intro A
    constructor
    · intro hA
      cases Finset.mem_union.mp hA with
      | inl h1 =>
          have : A ∈ F.edgeFinset.filter (fun B => m.1 ∉ B) := by
            simp_all only [ sets_iff_isOrderIdeal, posetTraceCore_ground,
              Finset.union_singleton, Finset.mem_insert, Finset.mem_filter, SetFamily.mem_edgeFinset, not_false_eq_true, and_self,
              F', F]
          exact Finset.mem_of_mem_filter A this
      | inr h0 =>
          have hAeq : A = S.ground := Finset.mem_singleton.mp h0
          have hGround : S.ground ∈ F.edgeFinset := by
            have hGroundSets : F.sets S.ground :=
              (S.sets_iff_isOrderIdeal (I := S.ground)).2
                (by dsimp [SetFamily.isOrderIdealOn]; exact And.intro (by intro x hx; exact hx)
                      (by intro x hx y hy _; exact hy))
            exact (SetFamily.mem_edgeFinset_iff_sets (F := F) (A := S.ground)).2 hGroundSets
          cases hAeq; exact hGround
    · intro hA
      by_cases hmA : m.1 ∈ A
      · -- ground 側
        have hA_sets : F.sets A := (SetFamily.mem_edgeFinset_iff_sets (F := F) (A := A)).1 hA
        have hA_ideal : SetFamily.isOrderIdealOn (S.leOn) S.ground A :=
          (S.sets_iff_isOrderIdeal (I := A)).1 hA_sets
        have hAeq : A = S.ground := hOnlyTop A hA_ideal hmA
        exact Finset.mem_union.mpr (Or.inr (by cases hAeq; exact Finset.mem_singleton_self _))
      · -- F' 側
        have hFilt : A ∈ F.edgeFinset.filter (fun B => m.1 ∉ B) :=
          Finset.mem_filter.mpr ⟨hA, hmA⟩
        have : A ∈ F'.edgeFinset := by
          simp_all only [sets_iff_isOrderIdeal, posetTraceCore_ground,
            SetFamily.mem_edgeFinset, Finset.mem_filter, not_false_eq_true, and_self, F', F]
        exact Finset.mem_union.mpr (Or.inl this)

  have hDisj : Disjoint F'.edgeFinset ({S.ground} : Finset (Finset α)) := by
    refine Finset.disjoint_left.mpr ?_
    intro A hA hA0
    have hAeq : A = S.ground := Finset.mem_singleton.mp hA0
    have hAsets' : F'.sets A :=
      (SetFamily.mem_edgeFinset_iff_sets (F := F') (A := A)).1 hA
    have hm_not : m.1 ∉ A := (hBack A hAsets').2
    have hmG : m.1 ∈ S.ground := m.2
    cases hAeq; exact (hm_not hmG).elim

  have hSumSplit :
      (∑ A ∈ F.edgeFinset, A.card)
        = (∑ A ∈ F'.edgeFinset, A.card)
          + (∑ A ∈ ({S.ground} : Finset (Finset α)), A.card) := by
    have : (∑ A ∈ (F'.edgeFinset ∪ ({S.ground} : Finset (Finset α))), A.card)
            = (∑ A ∈ F'.edgeFinset, A.card)
              + (∑ A ∈ ({S.ground} : Finset (Finset α)), A.card) :=
      Finset.sum_union hDisj
    simp_all only [ Finset.coe_mem, sets_iff_isOrderIdeal, posetTraceCore_ground,
      Finset.union_singleton, Finset.disjoint_singleton_right, Finset.mem_filter, SetFamily.mem_edgeFinset,
      not_true_eq_false, and_false, not_false_eq_true, Finset.sum_singleton,  F', F]

  have hSingleton :
      (∑ A ∈ ({S.ground} : Finset (Finset α)), A.card) = S.ground.card :=
    by simp

  dsimp [SetFamily.totalHyperedgeSize]
  calc
    (∑ A ∈ F.edgeFinset, A.card)
        = (∑ A ∈ F'.edgeFinset, A.card)
          + (∑ A ∈ ({S.ground} : Finset (Finset α)), A.card) := hSumSplit
    _   = (∑ A ∈ F'.edgeFinset, A.card) + S.ground.card := by rw [hSingleton]

/-  exactly 1 decrease -/
--Called from MainStatement
lemma ground_card_after_trace_of_max
  (S : FuncSetup α) [Fintype S.Elem]
  (m : S.Elem)(geq2: S.ground.card ≥ 2) :
  ((posetTraceCore S m geq2).ground).card = S.ground.card - 1 := by
  classical
  have : (posetTraceCore S m geq2).ground = S.ground.erase m.1 := rfl
  have hm : m.1 ∈ S.ground := m.2
  have h := Finset.card_erase_add_one hm
  exact Nat.eq_sub_of_add_eq h

/- equation of NDS difference -/
private lemma nds_diff_eq_root_delete_identity_of_max
  (S : FuncSetup α) [Fintype S.Elem]
  (m : S.Elem) (geq2: S.ground.card ≥ 2)
  (hOnlyTop :
    ∀ I : Finset α, SetFamily.isOrderIdealOn (S.leOn) S.ground I → m.1 ∈ I → I = S.ground)
  (hKeep :
    ∀ I : Finset α, SetFamily.isOrderIdealOn (S.leOn) S.ground I → m.1 ∉ I →
      ((posetTraceCore S m geq2).idealFamily).sets I)
  (hBack :
    ∀ I : Finset α, ((posetTraceCore S m geq2).idealFamily).sets I →
      (S.idealFamily).sets I ∧ m.1 ∉ I) :
  let S' := posetTraceCore S m geq2
  (S.idealFamily).NDS
    = (S'.idealFamily).NDS
      + (S.ground.card - (S.idealFamily).numHyperedges + 1 : Int) := by
  classical
  intro S'
  set F  := S.idealFamily
  set F' := S'.idealFamily
  have hNum : F'.numHyperedges + 1 = F.numHyperedges :=
    numHyperedges_trace_pred_of_max (S := S) (m := m)
      (hOnlyTop := hOnlyTop) (hKeep := hKeep) (hBack := hBack)
  have hSize :
    F.totalHyperedgeSize = F'.totalHyperedgeSize + S.ground.card :=
    totalHyperedgeSize_trace_sub_card_ground_of_max
      (S := S) (m := m) (geq2 := geq2) (hOnlyTop := hOnlyTop) (hKeep := hKeep) (hBack := hBack)
  have hV : S'.ground.card = S.ground.card - 1 :=
    ground_card_after_trace_of_max (S := S) (m := m) geq2

  have hNumZ :
      (F.numHyperedges : Int) = ((F'.numHyperedges + 1 : Nat) : Int) :=
    (congrArg (fun n : Nat => (n : Int)) hNum.symm)
  have hSizeZ :
      (F.totalHyperedgeSize : Int)
        = ((F'.totalHyperedgeSize + S.ground.card : Nat) : Int) :=
    (congrArg (fun n : Nat => (n : Int)) hSize)
  have hVZ :
      (F'.ground.card : Int) = ((S.ground.card - 1 : Nat) : Int) :=
    (congrArg (fun n : Nat => (n : Int)) hV)

  have hCalc :
      F.NDS
        = (2 * (F'.totalHyperedgeSize : Int)
              - (F'.numHyperedges : Int) * ((S.ground.card - 1 : Nat) : Int))
          + ((S.ground.card : Int) - (F'.numHyperedges : Int)) := by
    dsimp [SetFamily.NDS]
    rw [hSizeZ, hNumZ]
    have hCastAdd₁ :
        ((F'.totalHyperedgeSize + S.ground.card : Nat) : Int)
          = (F'.totalHyperedgeSize : Int) + (S.ground.card : Int) :=
      (Nat.cast_add _ _)
    have hCastAdd₂ :
        ((F'.numHyperedges + 1 : Nat) : Int)
          = (F'.numHyperedges : Int) + 1 :=
      (Nat.cast_add _ _)
    simp [mul_add, add_mul, two_mul, add_comm, add_left_comm,
          add_assoc, sub_eq_add_neg]
    have hVpos : 1 ≤ S.ground.card :=
      Nat.succ_le_of_lt (Finset.card_pos.mpr ⟨m.1, m.2⟩)
    exact arith_reduce (V := S.ground.card) (n := F'.numHyperedges)
                       (t := F'.totalHyperedgeSize) (hV := hVpos)

  have hRight :
      F'.NDS + (S.ground.card - F.numHyperedges + 1 : Int)
        = (2 * (F'.totalHyperedgeSize : Int)
              - (F'.numHyperedges : Int) * ((S.ground.card - 1 : Nat) : Int))
          + ((S.ground.card : Int) - (F'.numHyperedges : Int)) := by
    dsimp [SetFamily.NDS]
    rw [hVZ]
    have hNatRew :
        (S.ground.card - F.numHyperedges + 1 : Int)
          = (S.ground.card - (F'.numHyperedges + 1) + 1 : Int) := by
      have hNat :
          S.ground.card - F.numHyperedges + 1
            = S.ground.card - (F'.numHyperedges + 1) + 1 :=
        (congrArg (fun n : Nat => S.ground.card - n + 1) hNum.symm)
      norm_cast
      simp_all only [ Finset.coe_mem, sets_iff_isOrderIdeal, posetTraceCore_ground,
        Finset.card_erase_of_mem, Nat.cast_add, Nat.cast_inj, SetFamily.NDS_def, F', S', F]

    have hToZ :
        (S.ground.card - (F'.numHyperedges + 1) + 1 : Int)
          = (S.ground.card : Int) - (F'.numHyperedges : Int) := by
      simp [sub_eq_add_neg, add_comm, add_left_comm]
    rw [hNatRew, hToZ]

  exact hCalc.trans hRight.symm

/--NDS Difference equation-/
private theorem nds_diff_eq_root_delete_identity_uniqueMax
  (S : FuncSetup α) [Fintype S.Elem] (geq2: S.ground.card ≥ 2)
  (hpos : isPoset S) (hexu : ∃! m : S.Elem, S.maximal m) :
  let S' := posetTraceOfUnique S geq2 hexu
  (S.idealFamily).NDS
    = (S'.idealFamily).NDS
      + (S.ground.card - (S.idealFamily).numHyperedges + 1 : Int) := by
  classical
  intro S'
  set m : S.Elem := Classical.choose hexu.exists
  have hm : S.maximal m := Classical.choose_spec hexu.exists

  have hOnlyTop :
    ∀ I : Finset α, SetFamily.isOrderIdealOn (S.leOn) S.ground I → m.1 ∈ I → I = S.ground :=
    fun I hI hmI =>
      hOnlyTop_of_uniqueMax (S := S) (hpos := hpos) (hexu := hexu) (hI := hI) (hmI := hmI)

  have hKeep :
    ∀ I : Finset α, SetFamily.isOrderIdealOn (S.leOn) S.ground I → m.1 ∉ I →
      ((posetTraceCore S m geq2).idealFamily).sets I :=
    fun I hI hnot =>
      keep_sets_from_trace_at_without_m (S := S) (m := m) (geq2 := geq2) (hI := hI) (hmI := hnot)

  have hBack :
    ∀ I : Finset α, ((posetTraceCore S m geq2).idealFamily).sets I →
      (S.idealFamily).sets I ∧ m.1 ∉ I :=
    fun I hI' =>
      back_sets_from_trace_at_max_sets' (S := S) (hpos := hpos) (m := m) (hm := hm) (hI := hI')

  have base :=
    nds_diff_eq_root_delete_identity_of_max
      (S := S) (m := m) (geq2 := geq2)
      (hOnlyTop := hOnlyTop) (hKeep := hKeep) (hBack := hBack)

  -- `posetTraceOfUnique S hexu = posetTraceCore S m` を反映
  dsimp [posetTraceOfUnique, m] at base
  exact base

/-- (Trace at maximum does not reduce NDS) -/
--Called from MainStatement
theorem nds_trace_nondecreasing_uniqueMax
  (S : FuncSetup α) [Fintype S.Elem] (geq2 : S.ground.card ≥ 2)
  (hpos : isPoset S) (hexu : ∃! m : S.Elem, S.maximal m) :
  let S' := posetTraceOfUnique S geq2 hexu
  (S.idealFamily).NDS ≤ (S'.idealFamily).NDS := by
  classical
  intro S'
  -- 記号
  set F  := S.idealFamily
  set F' := S'.idealFamily

  have hEq :
      F.NDS = F'.NDS + (S.ground.card - F.numHyperedges + 1 : Int) :=
    nds_diff_eq_root_delete_identity_uniqueMax
      (S := S) (geq2 := geq2) (hpos := hpos) (hexu := hexu)

  have hLower : F.numHyperedges ≥ S.ground.card + 1 :=
    ideals_card_ge_ground_card_succ (S := S) (hpos := hpos)

  have hNat : S.ground.card + 1 ≤ F.numHyperedges := by exact hLower
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hNat
  have hkZ : (F.numHyperedges : Int) =
             ((S.ground.card + 1 + k : Nat) : Int) :=
    congrArg (fun n : Nat => (n : Int)) hk

  have hTerm_nonpos :
      (S.ground.card : Int) - (F.numHyperedges : Int) + 1 ≤ 0 := by
    calc
      (S.ground.card : Int) - (F.numHyperedges : Int) + 1
          = (S.ground.card : Int)
              - ((S.ground.card + 1 + k : Nat) : Int) + 1 := by
                rw [hkZ]
      _   = (S.ground.card : Int)
              - (((S.ground.card + 1 : Nat) : Int) + (k : Int)) + 1 := by
                exact congrArg (fun t => (S.ground.card : Int) - t + 1)
                               (Nat.cast_add (S.ground.card + 1) k)
      _   = (S.ground.card : Int)
              - ((S.ground.card : Int) + 1 + (k : Int)) + 1 := by
                exact congrArg (fun t => (S.ground.card : Int) - (t + (k : Int)) + 1)
                               (Nat.cast_add (S.ground.card) 1)
      _   = - (k : Int) := by
                simp [sub_eq_add_neg, add_comm, add_left_comm]
    -- −k ≤ 0
    have hk_nonneg : 0 ≤ (k : Int) := Int.natCast_nonneg k
    exact neg_nonpos.mpr hk_nonneg

  have hStep :
      F'.NDS + ((S.ground.card : Int) - (F.numHyperedges : Int) + 1)
        ≤ F'.NDS := by
    have := add_le_add_left hTerm_nonpos (F'.NDS)
    simpa using this

  have : F.NDS ≤ F'.NDS := by
    have h := hEq
    simp_all [SetFamily.NDS_def, ge_iff_le, Nat.cast_add, Nat.cast_one, add_le_iff_nonpos_right, F, F', S']

  exact this


end UniqueMax
end AvgRare
