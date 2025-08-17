import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import AvgRare.Basics.SetFamily
import AvgRare.SPO.FuncSetup

namespace AvgRare.Basics.Ideals

open Classical

universe u
variable {α : Type u} [DecidableEq α]

/- 4.2: |I(V,≤)| ≥ |V|+1 の型（詳細は後で） -/
lemma card_ideals_ge_cardV_plus_one
  (S : FuncSetup α) : True := by
  trivial

end AvgRare.Basics.Ideals
