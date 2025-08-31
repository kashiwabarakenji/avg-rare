import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.Order.GroupWithZero.Unbundled.Defs
import Mathlib.Algebra.Order.Sub.Basic
import AvgRare.Basics.SetFamily
import AvgRare.Basics.SetTrace
import AvgRare.Functional.FuncSetup
import AvgRare.Functional.TraceFunctional
import AvgRare.Reductions.Rare
import AvgRare.Functional.FuncPoset --isPoset_excessのため。


/-
IdealsTrace.lean — 「functional preorder × ideals × trace」

From high-level lemma statements as mentioned in papers, to the return of the quasi-primary theorem to the quasi-primary theorem
It is only quoted from Secondary.lean.
-/

universe u
open Classical

open scoped BigOperators

namespace AvgRare
namespace Reduction
open AvgRare
open Reduction
open SetFamily

variable {α : Type u} [DecidableEq α]

--Lemma 2.4--Non-obvious equivalence class ⇒ Max
--Also, {α} is required.
private theorem maximal_of_nontrivialClass {α : Type u} [DecidableEq α]
    (S : FuncSetup α) {x : S.Elem}
    (hx : S.nontrivialClass x) : S.maximal x := by
  rcases hx with ⟨y, hneq, hsim⟩
  have hpar : (S.idealFamily).Parallel (x : α) (y : α) :=
    S.parallel_of_sim_coe hsim
  have H :=
    S.maximal_of_parallel_nontrivial
      (u := (x : α)) (v := (y : α))
      (hu := x.property) (hv := y.property)
      (hpar := hpar)
      (hneq := Subtype.coe_ne_coe.mpr (id (Ne.symm hneq)))

  have Hx :
      ∀ z : S.Elem,
        Relation.ReflTransGen (FuncSetup.stepRel S.f) x z →
        Relation.ReflTransGen (FuncSetup.stepRel S.f) z x := by
    intro z hz
    have hz' :
        Relation.ReflTransGen (FuncSetup.stepRel S.f) (S.toElem! x.property) z := by
      exact hz
    have hxback :=
      H z hz'
    exact hxback

  intro z hxz

  have hxz_rtg : Relation.ReflTransGen (FuncSetup.stepRel S.f) x z := by exact hxz --rtg_of_le S hxz
  have hzx_rtg : Relation.ReflTransGen (FuncSetup.stepRel S.f) z x :=
    Hx z hxz_rtg
  rcases (FuncSetup.reflTransGen_iff_exists_iterate (S.f)).1 hzx_rtg with ⟨k, hk⟩
  have : S.le z x := by
    exact H z hxz

  exact this

/-- Paper Lemma 3.1 (statement):
The maximum element `u` of S is rare in `idealFamily S`.-/
private theorem rare_of_maximal {α : Type u} [DecidableEq α]
  (S : FuncSetup α) {u : S.Elem} (hmax : S.maximal u) :
  Rare (S.idealFamily) u.1 := by
  classical
  let Φ :=
    AvgRare.Reduction.Phi (u := u) (hmax := hmax)
  have hΦ : Function.Injective Φ :=
    Phi_injective (u := u) S hmax
  exact rare_of_injection_between_filters
          (F := S.idealFamily) (x := u.1) Φ hΦ

/- Article Lemma 3.6(1) Statement:-/
private theorem NDS_le_trace_of_nontrivialClass {α : Type u} [DecidableEq α]
  (S : FuncSetup α) {u : S.Elem}
  (hx : S.nontrivialClass u) :
  (S.idealFamily).NDS ≤ (traceAt u.1 (S.idealFamily)).NDS := by
  classical
  rcases S.exists_parallel_partner_from_nontrivial (u := u) hx with
    ⟨v, hne, hv, hpar⟩
  have hEq :
    (S.idealFamily).NDS
      = (traceAt u.1 (S.idealFamily)).NDS
        + 2 * ((S.idealFamily).degree u.1 : Int)
        - ((S.idealFamily).numHyperedges : Int) :=
    NDS_eq_of_parallel
      (F := S.idealFamily) (u := u.1) (v := v)
      (huv := hpar) (hne := hne.symm) (hu := u.property)

  have hmax : S.maximal u := maximal_of_nontrivialClass S (x := u) hx
  have hRare : Rare (S.idealFamily) u.1 := rare_of_maximal (S := S) (u := u) hmax
  have hnonpos :
      2 * ((S.idealFamily).degree u.1 : Int)
        - ((S.idealFamily).numHyperedges : Int) ≤ 0 :=
    diff_term_nonpos_of_Rare (F := S.idealFamily) (x := u.1) hRare
  have :(traceAt (↑u) S.idealFamily).NDS + 2 * ↑(S.idealFamily.degree ↑u) - ↑S.idealFamily.numHyperedges = (traceAt (↑u) S.idealFamily).NDS + (2 * ↑(S.idealFamily.degree ↑u) - ↑S.idealFamily.numHyperedges):= by
    exact
      Int.add_sub_assoc (traceAt (↑u) S.idealFamily).NDS (2 * ↑(S.idealFamily.degree ↑u))
        ↑S.idealFamily.numHyperedges
  rw [this] at hEq
  exact le_of_eq_add_of_nonpos hEq hnonpos

-- If excess is positive, there are non-trivial equivalence classes.
private lemma exists_nontrivialClass_of_excess_pos {α : Type u} [DecidableEq α]
  (S : FuncSetup α)
  (hpos : 0 < excess (S.idealFamily)) :
  ∃ u : S.Elem, S.nontrivialClass u := by

  classical
  let F := (S.idealFamily)
  have hlt_classes :
      (F.numClasses) < F.ground.card := by
    dsimp [excess] at hpos
    dsimp [F]
    exact Nat.lt_of_sub_pos hpos

  have himg :
      (F.ground.image (fun a : α => F.ParallelClass a)).card < F.ground.card := by
    -- `numClasses = (classSet).card = (ground.image ...).card`
    change (F.classSet).card < F.ground.card at hlt_classes

    simpa [SetFamily.numClasses, SetFamily.classSet]
      using hlt_classes
  obtain ⟨a, ha, b, hb, hneq, hcls⟩ :=
    exists_pair_with_same_image_of_card_image_lt
      (s := F.ground) (f := fun x : α => F.ParallelClass x) himg
  have hpar_ab : F.Parallel a b := by
    have hb_in : b ∈ F.ParallelClass b := by
      have : F.Parallel b b := by
        rfl
      have : b ∈ F.ground ∧ F.Parallel b b := And.intro hb this
      have : b ∈ F.ground.filter (fun x => F.Parallel b x) := by
        have : b ∈ F.ground := hb
        simp [this, Finset.mem_filter]

      simpa [SetFamily.ParallelClass] using this
    have : b ∈ F.ParallelClass a := by
      have hb' := hb_in
      rw [← hcls] at hb'
      exact hb'
    have : b ∈ F.ground ∧ F.Parallel a b := by
      simpa [SetFamily.ParallelClass, Finset.mem_filter] using this
    exact this.right
  let u : S.Elem := ⟨a, ha⟩
  let v : S.Elem := ⟨b, hb⟩
  have hneq_uv : u ≠ v := by
    intro h'
    have : a = b := congrArg (fun (z : S.Elem) => z.1) h'
    exact hneq this
  have hsim : FuncSetup.sim S u v := by
    have : (F).Parallel u v := by
      exact hpar_ab
    exact (FuncSetup.parallel_iff_sim S u v).mp hpar_ab
  have hsim' : FuncSetup.sim S u v :=
    (S.parallel_iff_sim u v).1 hpar_ab
  use u
  dsimp [FuncSetup.nontrivialClass]
  use v
  simp_all [F, u, v]
  intro a_1
  simp_all only [not_true_eq_false]

/-- （論文の前半の結論）準主定理を仮定して主定理を導く：強い帰納法を使う。 このファイルの主定理-/
theorem main_nds_nonpos_of_secondary {α : Type u} [DecidableEq α]
  (secondary_nds_nonpos :
    ∀ (T : FuncSetup α), FuncSetup.isPoset_excess T → (T.idealFamily).NDS ≤ 0)
  (S : FuncSetup α) :
  (S.idealFamily).NDS ≤ 0 := by
  classical
  refine
    (Nat.strongRecOn
      (excess (S.idealFamily))
      (motive := fun k =>
        ∀ (T : FuncSetup α),
          excess (T.idealFamily) = k → (T.idealFamily).NDS ≤ 0)
      ?step) S rfl
  · intro k IH T hk
    cases k with
    | zero =>
      have hposet : FuncSetup.isPoset_excess T := hk
      exact secondary_nds_nonpos T hposet
    | succ k' =>
      have hpos : 0 < excess (T.idealFamily) := by
        rw [hk]; exact Nat.succ_pos _
      obtain ⟨u, hnontriv⟩ :=
        exists_nontrivialClass_of_excess_pos (S := T) hpos
      have hNDS_mono :
          (T.idealFamily).NDS ≤ (SetFamily.traceAt u.1 (T.idealFamily)).NDS :=
        NDS_le_trace_of_nontrivialClass (S := T) (u := u) hnontriv
      obtain ⟨v, hneq_uv, hsim⟩ := hnontriv
      have hpar : (T.idealFamily).Parallel u v :=
        (T.parallel_iff_sim u v).2 hsim
      have h_nonempty : (T.idealFamily).ground.card ≥ 1 := by
        have : 0 < (T.idealFamily).ground.card :=
          Finset.card_pos.mpr ⟨u.1, u.2⟩
        exact Nat.succ_le_of_lt this
      have h_ground_sets :
          (T.idealFamily).sets (T.idealFamily).ground := by
        change isOrderIdealOn (T.leOn) T.ground (T.idealFamily).ground
        simp_all only [SetFamily.NDS_def, Nat.zero_lt_succ, traceAt_ground, Finset.coe_mem, Finset.card_erase_of_mem,
          Nat.cast_sub, Nat.cast_one, ne_eq, SetFamily.Parallel, FuncSetup.sets_iff_isOrderIdeal, ge_iff_le,
          Finset.one_le_card]
        obtain ⟨val, property⟩ := u
        obtain ⟨val_1, property_1⟩ := v
        simp_all only [Subtype.mk.injEq]
        rw [isOrderIdealOn]
        apply And.intro
        · rfl
        · intro x a y a_1 a_2
          exact a_1
      have h_excess :
          excess (SetFamily.traceAt u.1 (T.idealFamily))
            = excess (T.idealFamily) - 1 := by
        have hu : u.1 ∈ (T.idealFamily).ground := u.2
        -- v.1 ∈ ground, u.1 ≠ v.1
        have hv : v.1 ∈ (T.idealFamily).ground := v.2
        have hneqα : u.1 ≠ v.1 := by
          intro h'; have : u = v := Subtype.ext (by exact h'); exact hneq_uv (id (Eq.symm this))
        exact excess_trace
          (F := T.idealFamily) (hasU := h_ground_sets) (Nonemp := h_nonempty)
          (u := u.1) (v := v.1)
          (hu := hu) (hv := hv) (huv := hneqα) (hp := hpar)
      have hNontriv' : FuncSetup.nontrivialClass T u :=
        ⟨v, And.intro hneq_uv hsim⟩  -- 順序を揃える
      let tisf := T.traced_is_functional_family (u := u) hNontriv'
      obtain ⟨T', hTrace⟩ := tisf
      -- `excess (T'.idealFamily) = k'`
      have hex_T' : excess (T'.idealFamily) = k' := by
        calc
          excess (T'.idealFamily)
              = excess (SetFamily.traceAt u.1 (T.idealFamily)) := by
                rw [hTrace]
          _   = excess (T.idealFamily) - 1 := by exact h_excess
          _   = Nat.succ k' - 1 := by rw [hk]
          _   = k' := Nat.succ_sub_one k'
      have hIH_T' : (T'.idealFamily).NDS ≤ 0 :=
        IH k' (Nat.lt_succ_self k') T' hex_T'
      have hNDS_eq :
          (SetFamily.traceAt u.1 (T.idealFamily)).NDS
            = (T'.idealFamily).NDS := by
        rw [← hTrace]
      calc
        (T.idealFamily).NDS
            ≤ (SetFamily.traceAt u.1 (T.idealFamily)).NDS := hNDS_mono
        _   = (T'.idealFamily).NDS := hNDS_eq
        _   ≤ 0 := hIH_T'



end Reduction
end AvgRare
