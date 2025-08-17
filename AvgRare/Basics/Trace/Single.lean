import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import AvgRare.Basics.SetFamily

namespace AvgRare.Basics.Trace.Single

open Classical

universe u
variable {α : Type u} [DecidableEq α]

/- 点 `x` を代表とする「1点 trace」（必要に応じて定義調整） -/
noncomputable def traceAt (x : α) (F : SetFamily α) : SetFamily α :=
{ ground := F.ground.erase x
, sets   := fun B => ∃ A, F.sets A ∧ B ⊆ A.erase x
, decSets := Classical.decPred _
, inc_ground := by
    intro B hB; rcases hB with ⟨A, hA, hsub⟩
    have hAg : A ⊆ F.ground := F.inc_ground hA
    exact fun v hv => by
      have : v ∈ A := by
        have hv' : v ∈ B := hv
        have := hsub hv'
        exact (Finset.mem_erase.mp this).2
      simp_all only [Finset.mem_erase, ne_eq]
      apply And.intro
      · apply Aesop.BuiltinRules.not_intro
        intro a
        subst a
        rw [Finset.subset_iff] at hsub
        simp_all only [Finset.mem_erase, ne_eq]
        specialize hsub hv
        simp_all only [not_true_eq_false, false_and]
      · exact hAg this
}


/- 3.5: parallel（同値類一致）なら traceAt の像対応が単射 -/
lemma traceAt_injective_if_parallel
  (x : α) (F : SetFamily α) : True := by  -- TODO: precise statement
  trivial

/- 3.6(2): 1点 trace で NDS は増えない（不増） -/
lemma traceAt_nds_mono (x : α) (F : SetFamily α) :
  SetFamily.normalized_degree_sum (traceAt x F) ≤
  SetFamily.normalized_degree_sum F := by
  sorry

end AvgRare.Basics.Trace.Single
