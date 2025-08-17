import AvgRare.SPO.FuncSetup
import AvgRare.Basics.SetFamily
import AvgRare.Basics.Trace.Common
import AvgRare.SPO.Forest
import AvgRare.PaperSync.IdealsTrace

universe u

namespace AvgRare
namespace PaperSync
open Classical

variable {α : Type u} [DecidableEq α]

/-`FuncSetup S`（`V` と `f`）から得られる
    「前順序のイデアル全体」を集合族として束ねたもの。 -/
/- すでにidealsTraceで定義済み。
noncomputable def idealFamily (S : FuncSetup α) : SetFamily S.Elem :=
{ ground := S.V.attach,
  sets := fun A : Finset S.Elem => FuncSetup.isOrderIdeal S A,
  decSets := by infer_instance,   -- `isOrderIdeal` は `Classical.decPred`
  inc_ground := by
    -- 型が `Finset S.Elem` なので，任意の A の要素は自動的に ground（= S.V.attach）に入る
    intro A hA x hx
    cases x with
    | mk x hxV =>
        -- `⟨x, hxV⟩ ∈ S.V.attach`
        exact Finset.mem_attach S.V ⟨x, hxV⟩ }
-/

/-
lemma nds_trace_ker_eq (S : FuncSetup α) :
  SetFamily.normalized_degree_sum (
    AvgRare.trace S.ker (ideals S : SetFamily S.Elem))
  = SetFamily.normalized_degree_sum (ideals S) := by
  -- 7.3 の片向き + 逆向き（`nds_le_of_trace_ker`）から `le_antisymm`。
  sorry
-/


/-- 主定理（言明）：
    `f : V → V` から誘導された前順序のイデアル族の NDS は非正。 -/
theorem main_nds_nonpos (S : FuncSetup α) :
  (idealFamily S).normalized_degree_sum ≤ 0 := by
  -- 橋渡し＋森林性＋帰納の合成だけで閉じるのが理想
  have hforest := condensation_is_forest S
  have hforest_nds := nds_rooted_forest_nonpos S hforest
  have hbridge := nds_ideal_family_eq_on_quot S
  -- 等式を使って目標に移す
  -- (idealFamily S).nds = (idealFamilyQuot S).nds ≤ 0
  -- という形に整える
  -- ここは `rw [hbridge]` で終了予定
  sorry


end PaperSync
end AvgRare
