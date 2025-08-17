-- AvgRare/PaperSync/IdealsTrace.lean
import Mathlib.Data.Finset.Basic
import AvgRare.Basics.SetFamily
import AvgRare.SPO.FuncSetup
-- （trace 系をここで使うなら）import AvgRare.Basics.Trace.Common

universe u

namespace AvgRare
namespace PaperSync
open Classical
open FuncSetup

variable {α : Type u} [DecidableEq α]

/--/ ============================
   1) Elem 版の理想族
   ============================ -/

noncomputable def idealFamily (S : FuncSetup α) : SetFamily S.Elem :=
{ ground    := S.V.attach,
  sets      := fun A : Finset S.Elem => S.isOrderIdeal A,
  decSets   := by infer_instance,  -- FuncSetup 側で DecidablePred を出していれば拾えます
  inc_ground := by
    intro A hA x hx
    -- 任意の x : S.Elem は ground = S.V.attach に属する
    exact Finset.mem_attach S.V x }

/-
noncomputable def idealFamily (S : FuncSetup α) : SetFamily S.Elem :=
{ ground := S.V.attach,
  sets := fun A => S.isOrderIdeal A,
  decSets := Classical.decPred _,
  inc_ground := by
    intro A hA x hx
    -- 任意の x : S.Elem は ground = S.V.attach に入る
    exact Finset.mem_attach S.V x }
-/

/--/ ============================
   2) Quot 版の理想族
      ※ Finset.image を使うので DecidableEq (Quot S.ker) が必要。
         先に用意してから定義します。
   ============================ -/

-- ここで“定義の前”にインスタンスを供給しておくのがコツ
noncomputable local instance (S : FuncSetup α) : DecidableEq (Quot S.ker) := Classical.decEq _

noncomputable def idealFamilyQuot (S : FuncSetup α) : SetFamily (Quot S.ker) := by
  classical
  refine
  { ground := (S.V.attach).image (fun a : S.Elem => Quot.mk (S.ker) a)
    , sets := fun B =>
        ∃ A : Finset S.Elem,
          S.isOrderIdeal A ∧
          B ⊆ A.image (fun a : S.Elem => Quot.mk (S.ker) a)
    , decSets := Classical.decPred _
    , inc_ground := by
        intro B hB
        rcases hB with ⟨A, hAideal, hsub⟩
        -- A ⊆ S.V.attach は型レベルで常に成り立つ
        have hA_sub : A ⊆ S.V.attach := by
          intro a ha; exact Finset.mem_attach S.V a
        -- 画像の包含単調性（像の型は (Quot S.ker)）
        have hmono :
          A.image (fun a : S.Elem => Quot.mk (S.ker) a)
            ⊆ (S.V.attach).image (fun a : S.Elem => Quot.mk (S.ker) a) := by
          intro q hq
          rcases Finset.mem_image.1 hq with ⟨a, haA, rfl⟩
          exact Finset.mem_image.2 ⟨a, hA_sub haA, rfl⟩
        exact hsub.trans hmono }

/- ============================
   3) 橋渡し（言明）
      Elem 版と Quot 版の NDS が一致
   ============================ -/

theorem nds_ideal_family_eq_on_quot (S : FuncSetup α) :
  (idealFamily (α:=α) S).normalized_degree_sum
  = (idealFamilyQuot S).normalized_degree_sum := by
  -- 方針（後で実装）:
  --  • ground の 1–1 対応（attach の要素 ↔ その SCC 商像）
  --  • 頂点次数の一致：1_{q ∈ image(A)} の代表換算
  --  • 二重計数を Nat→Int に持ち上げて合計一致へ
  --  • 同一 SCC 中の重複は “下閉包” で吸収されることを明示
  sorry

lemma ground_card_eq (S : FuncSetup α) :
  (idealFamily S).ground.card
  = (idealFamilyQuot S).ground.card := by
  sorry

/-- 代表で数え直した次数は一致：Elem 版と Quot 版。 -/
lemma degree_bridge (S : FuncSetup α) (q : Quot S.ker) (r : S.Elem) (hr : Quot.mk S.ker r = q) :
  (idealFamilyQuot S).degreeNat q
  = (idealFamily S).degreeNat r := by
  -- 代表を取る補題を別に立ててから使う想定
  sorry

end PaperSync
end AvgRare
/-
-- AvgRare/PaperSync/IdealsTrace.lean
import Mathlib.Data.Finset.Basic
import AvgRare.Basics.SetFamily
import AvgRare.Basics.Trace
import AvgRare.SPO.FuncSetup
import LeanCopilot

universe u

namespace AvgRare
open Classical
open FuncSetup

variable {α : Type u} [DecidableEq α]

/-- `S` の order ideal 全体を集合族として見る（`FuncSetup.isOrderIdeal` 利用）。
    既にどこかで `ideals` を定義済みなら、この定義は削除してください。 -/
noncomputable def ideals (S : FuncSetup α) : SetFamily S.Elem :=
{ ground := S.V.attach
, sets := fun A => S.isOrderIdeal A
, decSets := Classical.decPred _
, inc_ground := by
    intro A hA x hx
    -- 任意の `x : S.Elem` は常に `S.V.attach` に属する：
    simp_all only [Finset.mem_attach]
}

noncomputable def idealsQuot (S : FuncSetup α) : SetFamily (Quot S.ker) :=
{ ground := imageQuot S.ker S.V.attach
, sets   := fun B => ∃ A : Finset S.Elem, S.isOrderIdeal A ∧ B ⊆ imageQuot S.ker A
, decSets := Classical.decPred _
, inc_ground := by
    intro B hB; rcases hB with ⟨A, hA, hsub⟩
    have hAg : A ⊆ S.V.attach := by
      intro x hx
      apply Finset.mem_attach

    have : imageQuot S.ker A ⊆ imageQuot S.ker S.V.attach := by
      intro q hq; rcases Finset.mem_image.1 hq with ⟨a, haA, rfl⟩
      exact Finset.mem_image.2 ⟨a, hAg haA, rfl⟩
    exact hsub.trans this }

-- 必要ならここで `Quot` の DecEq をローカル供給
noncomputable local instance (S : FuncSetup α) : DecidableEq (Quot S.ker) := Classical.decEq _

/-- Quot 版：SCC 商上のイデアル族。Forest には置かずここに集約しておくと循環を避けられる。 -/
noncomputable def idealFamilyQuot (S : FuncSetup α) : SetFamily (Quot S.ker) :=
{ ground := (S.V.attach).image (fun a => Quot.mk _ a),
  sets   := fun B =>
              ∃ A : Finset S.Elem,
                FuncSetup.isOrderIdeal S A ∧
                B ⊆ (A.image (fun a => Quot.mk _ a)),
  decSets := Classical.decPred _,
  inc_ground := by
    intro B hB
    rcases hB with ⟨A, hA, hsub⟩
    have hA_sub : A ⊆ S.V.attach := by
      intro a ha; exact Finset.mem_attach S.V a
    -- 画像の単調性
    have hmono :
      A.image (fun a => Quot.mk _ a)
        ⊆ (S.V.attach).image (fun a => Quot.mk _ a) := by --error
      intro q hq
      rcases Finset.mem_image.1 hq with ⟨a, haA, rfl⟩
      exact Finset.mem_image.2 ⟨a, hA_sub haA, rfl⟩
    exact hsub.trans hmono }

/-- 橋渡し補題：Elem版とQuot版で NDS が一致（あるいは同値に足る形）。 -/
theorem nds_ideal_family_eq_on_quot (S : FuncSetup α) :
  (idealFamily (α:=α) S).normalized_degree_sum --error
  = (idealFamilyQuot S).normalized_degree_sum := by
  -- 方針メモ（後で実装）:
  -- ・ground:  `S.V.attach` と その像の要素数は対応
  -- ・各頂点の次数:  1_{q ∈ image(A)} を代表で数え直し
  -- ・二重計数補題を Nat → Int に持ち上げ、合計で一致させる
  -- ・重複像（同一 SCC の複数元）が下閉包で吸収されることを明示
  sorry

--もしかして使わないかも。
lemma trace_ker_ideals_eq_idealsQuot (S : FuncSetup α) :
  AvgRare.trace S.ker (ideals S : SetFamily S.Elem) = idealsQuot S := by
  -- ground と sets の ext で証明（飽和性レマを使用）
  sorry

/- `ker` の trace と商の理想族の一致（言明）。 -/
--lemma trace_ker_ideals_eq_ideals_preQuot (S : FuncSetup α) :
--  AvgRare.trace S.ker (ideals S : SetFamily S.Elem)
--    = (ideals S.preQuot : SetFamily (Quot S.ker)) := by
--  sorry

/-- 逆向き比較：functional な核での trace は NDS を下からも抑える。 -/
lemma nds_le_of_trace_ker (S : FuncSetup α) :
  SetFamily.normalized_degree_sum (ideals S)
    ≤ SetFamily.normalized_degree_sum (
        AvgRare.trace S.ker (ideals S : SetFamily S.Elem)) := by
  -- `nds` の展開レマ（`degree_sum_eq_total_size_of_hyperedges` 等）と
  -- 同値類ごとの 1–1 対応（次数保存）を使う。
  sorry

/-- NDS の保存性（等式版）。 -/
lemma nds_trace_ker_eq (S : FuncSetup α) :
  SetFamily.normalized_degree_sum (
      AvgRare.trace S.ker (ideals S : SetFamily S.Elem))
  = SetFamily.normalized_degree_sum (ideals S) := by
  apply le_antisymm
  · -- 片向き：trace の単調性
    simpa using AvgRare.trace_nds_mono (α := S.Elem) S.ker (ideals S)
  · -- 逆向き：上の補題
    simpa using nds_le_of_trace_ker (S := S)

end AvgRare
-/
