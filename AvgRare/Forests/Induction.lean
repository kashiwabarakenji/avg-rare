import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import AvgRare.Basics.SetFamily
import AvgRare.SPO.FuncSetup
import AvgRare.SPO.Forest

universe u
open Classical
variable {V : Type u} [Fintype V] [DecidableEq V]

namespace AvgRare
namespace AvgRare.Forests.Induction

-- S : FuncSetup α, Q := Quot S.ker
def hasSink (S : FuncSetup α) : Prop := ∃ a : Quot S.ker, ¬ ∃ b, FuncSetup.stepQuot S a b

lemma exists_sink_of_forest (S : FuncSetup α)
  (hforest : IsRootedForest S) : hasSink S := by sorry

def isSink (S : FuncSetup α) (a : Quot S.ker) : Prop :=
  ¬ ∃ b : Quot S.ker, b ≠ a ∧ FuncSetup.stepQuot S a b

-- sink を 1 点「剥がす」操作は、ground を erase a した restrict で表現
-- 例：(idealsQuot S) ↘ ((idealsQuot S).ground.erase a)

lemma nds_peel_sink_step (S : FuncSetup α)
  (hforest : IsRootedForest S)
  {a : Quot S.ker}
  (ha_sink : isSink S a)
  (ha_in  : a ∈ (idealsQuot S).ground) :
  SetFamily.normalized_degree_sum (idealsQuot S)
    ≤ SetFamily.normalized_degree_sum ((idealsQuot S) ↘ ((idealsQuot S).ground.erase a)) := by
  -- 証明方針：
  -- 1) NDS = 2*Σ|A| - |I|*|V|
  -- 2) sink a を消すと、(i) ground が1減る、(ii) 各超辺は a を含む分だけサイズが減少、
  --    (iii) ideal 構造と「outdegree ≤ 1」（森林性）から “a を含む増分” が非増加になる
  -- 3) 以上より NDS(original) ≤ NDS(restrict)
  -- ここは後で詳細補題を積み上げて埋めます。
  sorry

lemma nds_rooted_forest_nonpos_via_induction
  (S : FuncSetup α) (hforest : IsRootedForest S) :
  SetFamily.normalized_degree_sum (idealsQuot S) ≤ 0 := by sorry

end AvgRare.Forests.Induction

end AvgRare
