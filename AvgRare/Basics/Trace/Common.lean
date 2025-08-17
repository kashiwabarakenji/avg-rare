import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import AvgRare.Basics.SetFamily

universe u

namespace AvgRare
open scoped BigOperators

variable {α : Type u} [DecidableEq α]

/-- `A : Finset α` を同値関係 `E` の商に写した像。 -/
noncomputable def imageQuot (E : Setoid α) (A : Finset α) : Finset (Quot E) := by
  classical
  exact A.image (fun a => Quot.mk _ a)

@[simp]
lemma mem_imageQuot {E : Setoid α} {A : Finset α} {q : Quot E} :
    q ∈ imageQuot E A ↔ ∃ a ∈ A, Quot.mk _ a = q := by
  classical
  simp [imageQuot]

lemma imageQuot_mono {E : Setoid α} {A B : Finset α} (h : A ⊆ B) :
    imageQuot E A ⊆ imageQuot E B := by
  classical
  intro q hq
  rcases (mem_imageQuot (E:=E) (A:=A)).1 hq with ⟨a, haA, rfl⟩
  exact (mem_imageQuot (E:=E) (A:=B)).2 ⟨a, h haA, rfl⟩

section
variable (E : Setoid α)
-- ★ ここで型レベルにインスタンスを用意しておく
noncomputable local instance : DecidableEq (Quot E) := Classical.decEq _

/-- `trace E F`：各超辺の商像を取り、その **下閉包** で得た集合族。 -/
noncomputable def trace (E : Setoid α) (F : SetFamily α) : SetFamily (Quot E) := by
  classical
  refine
  { ground := imageQuot E F.ground
    sets   := fun B => ∃ A : Finset α, F.sets A ∧ B ⊆ imageQuot E A
    decSets := Classical.decPred _
    inc_ground := ?_ }

  intro B hB
  rcases hB with ⟨A, hA, hsub⟩
  have hAg : A ⊆ F.ground := F.inc_ground hA
  have him : imageQuot E A ⊆ imageQuot E F.ground :=
    imageQuot_mono (E:=E) hAg
  exact hsub.trans him

/-- E ≤ E' ：E が E' より細かい（E の同値は E' の同値でもある） -/
def refines (E E' : Setoid α) : Prop :=
  ∀ ⦃a b : α⦄, E.r a b → E'.r a b

/-- refinement から商への写像 `Quot E → Quot E'` -/
noncomputable def liftQuot {E E' : Setoid α} (h : refines E E') :
  Quot E → Quot E' :=
  Quot.map (fun x => x) (by intro a b hab; exact h hab)

@[simp] lemma liftQuot_mk {E E' : Setoid α} (h : refines E E') (a : α) :
  liftQuot (E:=E) (E':=E') h (Quot.mk _ a) = Quot.mk _ a := rfl

/-- `imageQuot` を粗い同値に取り直すと、持ち上げ写像で包含が成り立つ。 -/
lemma imageQuot_mono_under_refines
  {E E' : Setoid α} (h : refines E E') (A : Finset α) :
  (A.image (fun a => Quot.mk E a)).image (liftQuot (E:=E) (E':=E') h)
    ⊆ A.image (fun a => Quot.mk E' a) := by
  classical
  intro q hq
  rcases Finset.mem_image.1 hq with ⟨q0, hq0, rfl⟩
  rcases Finset.mem_image.1 hq0 with ⟨a, haA, rfl⟩
  -- 右辺に同じ代表 a で入る
  exact Finset.mem_image.2 ⟨a, haA, rfl⟩

/-- **trace の単調性（Setoid を粗くすると大きくなる）**
`E ≤ E'`（E が細かい）なら、`trace E F` の各超辺像を `Quot E → Quot E'` に移せば `trace E' F` の超辺に含まれる。 -/
lemma trace_mono_in_setoid
  (E E' : Setoid α) (F : SetFamily α) (h : refines E E') :
  ∀ {B : Finset (Quot E)},
    (trace E F).sets B →
    ∃ B' : Finset (Quot E'),
      (trace E' F).sets B' ∧
      B.image (liftQuot (E:=E) (E':=E') h) ⊆ B' := by
  classical
  intro B hB
  -- 定義展開：B ⊆ imageQuot E A
  rcases hB with ⟨A, hAsets, hBsub⟩
  refine ⟨A.image (fun a => Quot.mk E' a), ?_, ?_⟩
  · -- `trace E' F` のメンバー
    refine ⟨A, hAsets, ?_⟩
    -- `imageQuot E' A` に対しては自明な包含
    intro q hq
    exact hq
  · -- B を `liftQuot` で写すと、`imageQuot E' A` に入る
    -- すなわち B.image (liftQuot h) ⊆ (imageQuot E' A)
    -- まず B ⊆ imageQuot E A を使って、像に押し出す
    intro q hq
    rcases Finset.mem_image.1 hq with ⟨q0, hq0, rfl⟩
    have : q0 ∈ A.image (fun a => Quot.mk E a) := hBsub hq0
    -- ここで `imageQuot_mono_under_refines` で E→E' に移す
    have step :=
      imageQuot_mono_under_refines (E:=E) (E':=E') h (A := A)
    -- step : (imageQuot E A).image (liftQuot h) ⊆ imageQuot E' A
    exact step (by
      -- q0 を像に入れてから lift して得る要素は右辺に含まれる
      exact Finset.mem_image.2 ⟨q0, this, rfl⟩)

lemma total_size_of_hyperedges_trace_le
  {α} [DecidableEq α] (E : Setoid α) (F : SetFamily α) :
  (trace E F).total_size_of_hyperedgesNat ≤ F.total_size_of_hyperedgesNat := by
  -- 像でサイズは縮み、下閉包でさらに同じか減る、の二段論法
  sorry
/-
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import AvgRare.Basics.SetFamily


universe u

namespace AvgRare
open scoped BigOperators
open Classical

variable {α : Type u} [DecidableEq α]

/-- `A : Finset α` を同値関係 `E` の商に写した像。 -/
noncomputable def imageQuot (E : Setoid α) (A : Finset α) : Finset (Quot E) :=
  A.image (fun a => Quot.mk _ a)

/-- `trace E F`：各超辺の商像を取り、その**下閉包**で得た集合族。 -/
noncomputable def trace (E : Setoid α) (F : SetFamily α) : SetFamily (Quot E) :=
{ ground := imageQuot E F.ground
, sets := fun B => ∃ A : Finset α, F.sets A ∧ B ⊆ imageQuot E A
, decSets := Classical.decPred _
, inc_ground := by
    intro B hB; rcases hB with ⟨A, hA, hsub⟩
    have hAg : A ⊆ F.ground := F.inc_ground hA
    have him : imageQuot E A ⊆ imageQuot E F.ground := by
      intro x hx
      rcases Finset.mem_image.1 hx with ⟨a, haA, rfl⟩
      exact Finset.mem_image.2 ⟨a, hAg haA, rfl⟩
    exact hsub.trans him }
    -/
