import AvgRare.Basics.SetFamily
import AvgRare.SPO.FuncSetup
import AvgRare.Basics.Trace.Common

namespace AvgRare
open FuncSetup

noncomputable instance quotientDecEq {β : Type _} (E : Setoid β) : DecidableEq (Quotient E) :=
  Classical.decEq _

variable {α : Type _} [DecidableEq α]
variable (S : FuncSetup α)

-- SCC凝縮グラフがDAG（= 反対称）で outdegree ≤ 1 であること
def IsRootedForest : Prop :=
  (∀ a b, S.preQuot.le a b → S.preQuot.le b a → a = b) ∧
  (∀ a, ¬ ∃ b c, b ≠ c ∧ FuncSetup.stepQuot S a b ∧ FuncSetup.stepQuot S a c)

theorem condensation_is_forest : IsRootedForest S := by
  refine ⟨?hAnti, ?hOut⟩
  · -- 反対称性：FuncSetup.antisymm_on_quot を使用
    intro a b h1 h2
    -- after you prove antisymm_on_quot:
    -- exact FuncSetup.antisymm_on_quot (S:=S) h1 h2
    sorry
  · -- 出次数 ≤ 1：FuncSetup.outdeg_le_one_on_quot を使用
    intro a
    -- exact FuncSetup.outdeg_le_one_on_quot (S:=S) a
    sorry
/-
def IsRootedForest (S : FuncSetup α) : Prop := True  -- ← 型だけ（後で定義差し替え）

-- 事実：機能グラフの凝縮は常に森林
theorem condensation_is_forest (S : FuncSetup α) : IsRootedForest S := by
  sorry
-/

-- 使う側（あなたの lemma）も S を渡す
lemma nds_leaf_step (S : FuncSetup α)
    (hforest : IsRootedForest S) :
  True := by
  trivial

noncomputable instance (S : FuncSetup α) : DecidableEq (Quot S.ker) :=
  Classical.decEq _

--noncomputable def imageQuot (E : Setoid α) [DecidableEq (Quotient E)] (A : Finset α) : Finset (Quotient E) := A.image (Quot.mk E)

noncomputable def idealsQuot (S : FuncSetup α) : SetFamily (Quot S.ker) :=
{ ground := imageQuot S.ker S.V.attach,
  sets   := fun B => ∃ A : Finset S.Elem, S.isOrderIdeal A ∧ B ⊆ imageQuot S.ker A,
  decSets := Classical.decPred _,
  inc_ground := by
    intro B hB
    rcases hB with ⟨A, hA, hsub⟩
    have hAg : A ⊆ S.V.attach := by
      -- `isOrderIdeal` の定義が「下に閉じた」だけなら `A ⊆ ground` は自明扱いでもOK
      -- 必要なら別途 `inc_ground` 相当を用意
      intro x hx;
      exact Finset.mem_attach S.V x
    have : imageQuot S.ker A ⊆ imageQuot S.ker S.V.attach := by
      intro q hq; rcases Finset.mem_image.1 hq with ⟨a, haA, rfl⟩
      exact Finset.mem_image.2 ⟨a, hAg haA, rfl⟩
    exact hsub.trans this }

/-- 森に対する二次主定理（非正性、言明）。 -/
lemma nds_rooted_forest_nonpos (S : FuncSetup α)
    (hforest : IsRootedForest S) :
  SetFamily.normalized_degree_sum (idealsQuot S) ≤ 0 := by
  -- `nds_leaf_step` による帰納法で証明
  sorry

end AvgRare
