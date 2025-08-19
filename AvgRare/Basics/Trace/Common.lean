import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import AvgRare.Basics.SetFamily
import AvgRare.Basics.Ideals
import LeanCopilot

/-
Common.lean — Trace と汎用補助

このファイルでは
* 1点トレース `Trace.traceAt`
* 並行性 `Trace.Parallel`
* その場で使える小補助

を提供します。証明が重い主張（単射性など）は「言明だけ」を先に置き、
後で `IdealsTrace.lean` 等で埋める方針です。
-/

universe u
open Classical
open scoped BigOperators

namespace AvgRare
namespace Trace

variable {α : Type u} [DecidableEq α]

/-- 1点トレース：各ハイパーエッジから要素 `x` を取り除いた族。
`ground` は `F.ground.erase x` に落とす。 -/
noncomputable def traceAt (x : α) (F : SetFamily α) : SetFamily α := by
  classical
  refine
  { ground := F.ground.erase x
    , sets   := fun B =>
        ∃ A : Finset α, F.sets A ∧ B = A.erase x
    , decSets := Classical.decPred _
    , inc_ground := ?_ }
  intro B hB
  rcases hB with ⟨A, hA, hBsub, hBsubU⟩
  intro y
  simp only [Finset.mem_erase]
  intro h
  constructor
  · exact h.1
  · exact F.inc_ground hA (by
      -- `y ∈ A.erase x` なら `y ∈ A` なので、`A ⊆ F.ground` を使う
      simp_all only [ne_eq])

@[simp] lemma traceAt_ground (x : α) (F : SetFamily α) :
    (traceAt x F).ground = F.ground.erase x := rfl

/-- 並行性：族 `F` において「`u` を含むエッジの集合」と
「`v` を含むエッジの集合」が一致する。 -/
@[simp] def Parallel (F : SetFamily α) (u v : α) : Prop :=
  {A : Finset α | F.sets A ∧ u ∈ A} = {A : Finset α | F.sets A ∧ v ∈ A}

lemma parallel_refl (F : SetFamily α) (u : α) : Parallel F u u := rfl
lemma parallel_symm {F : SetFamily α} {u v : α} :
    Parallel F u v → Parallel F v u := fun h => h.symm

/-- `Subtype` のエッジを `erase u` に写す自然な射。 -/
def eraseMap (F : SetFamily α) (u : α) :
    {A // F.sets A} → Finset α := fun A => (Subtype.val A).erase u

@[simp] lemma eraseMap_apply (F : SetFamily α) (u : α) (A : {A // F.sets A}) :
    eraseMap F u A = (A.val).erase u := rfl

/-- （言明のみ）Lemma 3.5 に対応：
`u` と `v` が Parallel なら，`A ↦ A.erase u` はエッジ集合上で単射。 -/
lemma trace_injective_of_parallel
    (F : SetFamily α) {u v : α} (h : Parallel F u v) :
    Function.Injective (eraseMap F u) := by
  -- 詳細証明は IdealsTrace で（`mem_edgeFinset_iff` などと併用）
  intro A1 A2 hEq
  -- 将来の証明埋め込みで `simp_all` を活かせるように温存
  sorry

/- トレース後の「`B` がトレース族のメンバである」ことの便利な再表現。 -/
--lemma mem_traceAt_iff {x : α} {F : SetFamily α} {B : Finset α} :
--    (traceAt x F).sets B ↔ ∃ A, F.sets A ∧ B ⊆ A.erase x ∧ B ⊆ F.ground.erase x := by

/- 1点トレースの ground 包含（再掲）。 -/
/-
lemma subset_ground_of_mem_trace {x : α} {F : SetFamily α} {B : Finset α}
    (hB : (traceAt x F).sets B) :
    B ⊆ (traceAt x F).ground := by
  classical
  rcases (mem_traceAt_iff).1 hB with ⟨A, hA, hBsub, hBsubU⟩
  -- 定義どおり
  simpa using hBsubU
-/

/- 小補助：`A ⊆ F.ground` なら `A.erase x ⊆ F.ground.erase x`。 -/
/-
lemma erase_subset_erase_of_subset {x : α} {F : SetFamily α} {A : Finset α}
    (hA : A ⊆ F.ground) :
    A.erase x ⊆ F.ground.erase x := by
  intro a ha
  have : a ∈ A ∧ a ≠ x := by
    -- `Finset.mem_erase` の逆向き
    simp_all only [Finset.mem_erase, ne_eq, not_false_eq_true, and_self]
  have haA : a ∈ A := this.1
  have hne : a ≠ x := this.2
  have haU : a ∈ F.ground := hA haA
  -- `mem_erase` の順向き
  exact by
    -- a ∈ ground ∧ a ≠ x から a ∈ ground.erase x
    have : a ∈ F.ground.erase x := by
      -- `Finset.mem_erase` ⇔ (a ≠ x ∧ a ∈ ground)
      have := (show a ≠ x ∧ a ∈ F.ground from And.intro hne haU)
      -- 書き換え
      simpa [Finset.mem_erase, And.comm] using this
    exact this
-/

/-
noncomputable def traceErase (x : α) (F : SetFamily α) : SetFamily α := by
  classical
  refine
  { ground := F.ground.erase x
    , sets := fun B => ∃ A, F.sets A ∧ B = A.erase x
    , decSets := Classical.decPred _
    , inc_ground := ?_ }
  intro B hB
  rcases hB with ⟨A, hA, rfl⟩
  -- A ⊆ ground → A.erase x ⊆ ground.erase x
  exact (erase_subset_erase_of_subset (F := F) (A := A) (F.inc_ground hA))
-/

/- 像だけ版の edge 列挙：`edgeFinset = image (erase x)`。 -/
/-
lemma edgeFinset_traceErase (x : α) (F : SetFamily α) :
    (traceErase x F).edgeFinset
      = F.edgeFinset.image (fun A => A.erase x) := by
  classical
  -- ここは後で埋める（`mem_edgeFinset_iff` と `Finset.image` の往復）
  sorry
-/

/-- Parallel なら `image (erase u)` に重複が出ない。 -/
lemma card_image_erase_of_parallel
    (F : SetFamily α) {u v : α} (h : Parallel F u v) :
    (F.edgeFinset.image (fun A => A.erase u)).card = F.edgeFinset.card := by
  classical
  -- `trace_injective_of_parallel` と `Finset.card_image_iff` で
  sorry

lemma NDS_traceAt_rewrite
    (F : SetFamily α) (u : α)
    (hEdgeImage : (Trace.traceAt u F).edgeFinset = F.edgeFinset.image (fun A => A.erase u))
    (hCardPres : (Trace.traceAt u F).numHyperedges = F.numHyperedges)
    (hGround   : (Trace.traceAt u F).ground = F.ground) :
    NDS (Trace.traceAt u F)
      = 2 * (∑ A ∈ F.edgeFinset, (A.erase u).card : Int)
        - (F.numHyperedges : Int) * (F.ground.card : Int) := by
  -- unfold NDS; rewrite 3つの仮定; `sum_image` の書き換えで完成（詳細は後で）
  sorry



end Trace
/-
必要になったときに拡張しやすいよう、Trace とは独立の小道具をここに置いておけます
（例えば Equiv による ground の付け替え等）。現状は最小限に留めています。
-/

end AvgRare

/-
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import AvgRare.Basics.SetFamily
import AvgRare.SPO.FuncSetup

universe u

namespace AvgRare
namespace Basics
namespace Trace
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

--section
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


noncomputable def restrict {α} [DecidableEq α]
    (F : SetFamily α) (U : Finset α) : SetFamily α := by
  classical
  refine
  { ground := U
    , sets := fun B => ∃ A : Finset α, F.sets A ∧ B ⊆ A ∧ B ⊆ U
    , decSets := Classical.decPred _
    , inc_ground := ?_ }
  intro B hB
  rcases hB with ⟨A, hA, hBsubA, hBsubU⟩
  exact hBsubU

@[simp] lemma mem_restrict_iff {α} [DecidableEq α]
    {F : SetFamily α} {U B : Finset α} :
    (restrict F U).sets B ↔ ∃ A, F.sets A ∧ B ⊆ A ∧ B ⊆ U := Iff.rfl

lemma isOrderIdeal_erase_on_restrict
  {α} [DecidableEq α] (S : FuncSetup α)
  (A : Finset S.Elem) (hA : S.isOrderIdeal A) (u : S.Elem) :
  (S.restrict (S.V.erase u)).isOrderIdeal (A.erase u) := by
  intro x y hy hx
  -- `x y : (S.restrict ...).Elem` だと思って使えるように、必要なら `Subtype` の `val` 展開
  -- `hy : y ≤ x` は制限順序の比較。基の順序の比較に戻してから `hA` に投げる。
  rcases Finset.mem_erase.mp hx with ⟨hx_ne, hxA⟩
  have hyA : (y : S.Elem) ∈ A := hA (by simpa using hy) hxA
  -- 結論は `x ∈ A.erase u`：
  apply Finset.mem_erase.mpr
  constructor
  · -- x ≠ u
    -- x = u なら u ≤ y だが y は `A` に居るので、`A.erase u` の仮定と矛盾、の形で弾く
    intro hxu; subst hxu
    -- `u ≤ y` だが `y ∈ A` なので `u ∈ A`（下方閉）。しかし `hx` は x≠u を言っていた…という整理。
    -- ここは環境の順序補題（反射・推移）に合わせて書き分け。
    have : (u : S.Elem) ∈ A := hA (by simpa using hy) hxA
    exact hx_ne this.symm
  · -- x ∈ A
    exact hA (by simpa using hy) hxA


/-- 記法：`𝓕 ↘ U` を `restrict 𝓕 U` の糖衣として定義。 -/
notation:90 F "↘" U => AvgRare.Basics.Trace.restrict F U

@[simp] lemma imageQuot_eq_image {E : Setoid α} (A : Finset α) :
  imageQuot E A = A.image (fun a => Quot.mk _ a) := rfl

@[simp] lemma mem_imageQuot_iff {E : Setoid α} {A : Finset α} {q : Quot E} :
  q ∈ imageQuot E A ↔ ∃ a ∈ A, Quot.mk _ a = q :=
by classical simp [imageQuot]

/-- 画像の画像：`imageQuot E A` の各要素を恒等的に lift する形の `image` は `imageQuot` の交換で吸収できる -/
lemma image_imageQuot_lift {E E' : Setoid α} (h : refines E E') (A : Finset α) :
  (imageQuot E A).image (liftQuot (E:=E) (E':=E') h)
    ⊆ imageQuot E' A := by
  classical
  -- 既存の `imageQuot_mono_under_refines` の言い換え
  have := imageQuot_mono_under_refines (E:=E) (E':=E') h (A:=A)
  -- 使っている定義の向きを合わせるだけ
  simpa [imageQuot_eq_image] using this

end Trace
end Basics
end AvgRare


-/
