import AvgRare.SPO.FuncSetup
import AvgRare.Basics.SetFamily
import AvgRare.Basics.Trace.Common
import AvgRare.SPO.Forest
import AvgRare.PaperSync.IdealsTrace

set_option maxHeartbeats 100000000

universe u

namespace AvgRare
namespace PaperSync
open Classical

variable {α : Type u} [DecidableEq α]

/- 主定理（言明）：
    `f : V → V` から誘導された前順序のイデアル族の NDS は非正。 -/
theorem main_nds_nonpos (S : FuncSetup α) :
  (idealFamilyQuot S).normalized_degree_sum ≤ 0 := by
  -- 論文：凝縮 DAG は森 ⇒ 森の NDS は非正
  -- （Forest 側の補題名は既存のものに合わせて調整してください）
  have hforest := condensation_is_forest S
  convert nds_rooted_forest_nonpos S hforest
  --dsimp [idealFamilyQuot]
  --dsimp [idealsQuot]
  sorry



end PaperSync
end AvgRare
