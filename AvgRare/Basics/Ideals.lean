import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import AvgRare.Basics.SetFamily
import AvgRare.SPO.FuncSetup
import LeanCopilot

namespace AvgRare
namespace FuncSetup

open Classical
open FuncSetup
open SetFamily

universe u
variable {α : Type u} [DecidableEq α]

section
variable (S : FuncSetup α)

-- 便利記法：S の台集合上の要素
--abbrev Elem := S.Elem

/-- 空集合はイデアル。 -/
@[simp] lemma isOrderIdeal_empty : S.isOrderIdeal (∅ : Finset S.Elem) := by
  intro x y hy hx
  -- x∈∅ は矛盾
  simp_all only [Finset.notMem_empty]

/-- 和はイデアル。 -/
lemma isOrderIdeal_union {A B : Finset S.Elem}
    (hA : S.isOrderIdeal A) (hB : S.isOrderIdeal B) :
    S.isOrderIdeal (A ∪ B) := by
  intro x y hy hmem
  rcases Finset.mem_union.mp hmem with hx | hx
  · exact Finset.mem_union.mpr (Or.inl (hA hy hx))
  · exact Finset.mem_union.mpr (Or.inr (hB hy hx))

/-- 交叉はイデアル。 -/
lemma isOrderIdeal_inter {A B : Finset S.Elem}
    (hA : S.isOrderIdeal A) (hB : S.isOrderIdeal B) :
    S.isOrderIdeal (A ∩ B) := by
  intro x y hy hmem
  rcases Finset.mem_inter.mp hmem with ⟨hxA, hxB⟩
  exact Finset.mem_inter.mpr ⟨hA hy hxA, hB hy hxB⟩

/-- 主イデアル（\↓x）：`ground` から `≤ x` な要素を集めたもの。 -/
noncomputable def principalIdeal (x : S.Elem) : Finset S.Elem :=
  S.V.attach.filter (fun y => y ≤ x)

@[simp] lemma mem_principalIdeal {x y : S.Elem} :
  y ∈ S.principalIdeal x ↔ y ≤ x := by
  classical
  -- attach にはすべての Elem が入る
  have hy : y ∈ S.V.attach := Finset.mem_attach _ _
  constructor
  · intro h
    -- filter の条件が通っている
    have := (Finset.mem_filter.mp h).2
    simpa using this
  · intro hle
    -- attach にいる y で、かつ ≤ x
    exact Finset.mem_filter.mpr ⟨hy, hle⟩

/-- 主イデアルはイデアル。 -/
lemma isOrderIdeal_principal (x : S.Elem) :
  S.isOrderIdeal (S.principalIdeal x) := by
  intro a b hba ha
  -- a∈↓x かつ b≤a ⇒ b≤x なので b∈↓x
  have : a ≤ x := (mem_principalIdeal (S:=S)).1 ha
  have : b ≤ x := (S.pre).le_trans _ _ _ hba this
  exact (mem_principalIdeal (S:=S)).2 this

/-- 単元から生成される主イデアルは，その点を含む。 -/
@[simp] lemma self_mem_principal (x : S.Elem) :
  x ∈ S.principalIdeal x := by
  simp_all only [mem_principalIdeal, le_refl]

end

/-! # （占位）カウント系の足場

  4.2 の `|I(V,≤)| ≥ |V| + 1` は、前順序の場合は
  「同一の主イデアルになる元がある（同値類内）」ので素朴にはズレます。
  厳密には SCC 商（半順序）側の主イデアルと空集合で `|V/≈| + 1` 本は確保できます。
  ここでは占位の主張は True にしつつ、後で Forrest/Quot 側と接続して仕上げましょう。
-/
lemma card_ideals_ge_cardV_plus_one
  (S : FuncSetup α) : True := by
  trivial

variable (S : FuncSetup α)

lemma parallel_on_ideals_iff_ker
    {x y : S.Elem} :
    (∀ {A : Finset S.Elem}, S.isOrderIdeal A → (x ∈ A ↔ y ∈ A))
      ↔ ((x ≤ y) ∧ (y ≤ x)) := by
  constructor
  · intro h
    -- y ≤ x：A := ↓x をとる
    have hx_in : x ∈ S.principalIdeal x := S.self_mem_principal x
    have h_y_in : y ∈ S.principalIdeal x := by
      have hx_iff_yx := h (A := S.principalIdeal x) (S.isOrderIdeal_principal x)
      -- x∈A → y∈A
      exact (Iff.mp hx_iff_yx) hx_in
    have hy_le_x : y ≤ x :=
      (S.mem_principalIdeal).1 h_y_in

    -- x ≤ y：A := ↓y をとる
    have hy_in : y ∈ S.principalIdeal y := S.self_mem_principal y
    have h_x_in : x ∈ S.principalIdeal y := by
      have hy_iff_xy := h (A := S.principalIdeal y) (S.isOrderIdeal_principal y)
      -- y∈A → x∈A
      simp_all only [mem_principalIdeal, le_refl, iff_true]
    have hx_le_y : x ≤ y :=
      (S.mem_principalIdeal).1 h_x_in

    exact ⟨hx_le_y, hy_le_x⟩
  · intro hle
    -- isOrderIdeal の下閉性で両向きを示す
    intro A hA
    constructor
    · intro hxA
      -- x∈A, かつ y ≤ x から y∈A
      have hy_le_x : y ≤ x := hle.2
      exact hA hy_le_x hxA
    · intro hyA
      -- y∈A, かつ x ≤ y から x∈A
      have hx_le_y : x ≤ y := hle.1
      exact hA hx_le_y hyA

/-- `SetFamily.parallelSetoid` をイデアル族に適用したとき，
  その同値が `ker`（前順序の同値）と同値であること（関係レベル）。 -/
lemma parallelSetoid_rel_eq_ker_of_idealFamily
    (F : SetFamily S.Elem)
    (hSets : ∀ {A : Finset S.Elem}, F.sets A ↔ S.isOrderIdeal A)
    {x y : S.Elem} :
    (AvgRare.SetFamily.parallelSetoid F).r x y
      ↔ S.ker.r x y := by
  constructor
  · intro h
    -- F.sets A → isOrderIdeal A に書き換えてから適用
    have h' :
        (∀ {A : Finset S.Elem}, S.isOrderIdeal A → (x ∈ A ↔ y ∈ A)) := by
      intro A hA
      have hFA : F.sets A := (hSets).mpr hA
      exact h (A := A) hFA
    -- 前補題で ker へ
    -- `S.ker.r x y` は定義上 `(x ≤ y) ∧ (y ≤ x)` と同一
    have : (x ≤ y) ∧ (y ≤ x) :=
      (S.parallel_on_ideals_iff_ker (x := x) (y := y)).1 h'
    exact this
  · intro hker
    -- `F.sets A` から `isOrderIdeal A` に落として、下閉性で両向き
    intro A hFA
    have hA : S.isOrderIdeal A := (hSets).1 hFA
    -- hker : x≤y ∧ y≤x
    constructor
    · intro hxA
      have hy_le_x : y ≤ x := hker.2
      exact hA hy_le_x hxA
    · intro hyA
      have hx_le_y : x ≤ y := hker.1
      exact hA hx_le_y hyA

variable (S : FuncSetup α)

/-- `S` の順序イデアル全体を集合族としてまとめたもの。
    ground は `S.V.attach`、メンバー判定は `S.isOrderIdeal`. -/
noncomputable def idealFamily (S : FuncSetup α) : SetFamily (Elem S) :=
{ ground     := S.V.attach,
  sets       := fun A : Finset (Elem S) => S.isOrderIdeal A,
  decSets    := by infer_instance,           -- 既に `instance : DecidablePred (isOrderIdeal S)`
  inc_ground := by
    intro A hA x hx
    -- `x : S.Elem` は常に `attach` に入る
    exact Finset.mem_attach S.V x }

-- 使い勝手のための最小限の `@[simp]` 群
@[simp] lemma idealFamily_ground :
  (idealFamily S).ground = S.V.attach := rfl

@[simp] lemma idealFamily_sets_iff {A : Finset (Elem S)} :
  (idealFamily S).sets A ↔ S.isOrderIdeal A := Iff.rfl


lemma parallel_iff_ker {x y : S.Elem} :
    (S.idealFamily).parallel x y ↔ S.ker.r x y := by
  classical
  constructor
  · -- (→) parallel ⇒ x≤y ∧ y≤x
    intro hpar
    -- `↓x` はイデアル
    have hIx : S.isOrderIdeal (S.principalIdeal x) := S.isOrderIdeal_principal x
    have hIy : S.isOrderIdeal (S.principalIdeal y) := S.isOrderIdeal_principal y
    have hxiff :
        (x ∈ S.principalIdeal x ↔ y ∈ S.principalIdeal x) :=
      hpar (A := S.principalIdeal x)
           ((idealFamily_sets_iff (S := S)).2 hIx)
    have hyiff :
        (x ∈ S.principalIdeal y ↔ y ∈ S.principalIdeal y) :=
      hpar (A := S.principalIdeal y)
           ((idealFamily_sets_iff (S := S)).2 hIy)

    -- parallel を principalIdeal に適用
    have hx_in : x ∈ S.principalIdeal x := S.self_mem_principal x
    have hy_le_x : y ≤ x := by
      have hy_in : y ∈ S.principalIdeal x := (Iff.mp hxiff) hx_in
      exact (FuncSetup.mem_principalIdeal (S := S)).1 hy_in

    have hy_in' : y ∈ S.principalIdeal y := S.self_mem_principal y
    have hx_le_y : x ≤ y := by
      have hx_in' : x ∈ S.principalIdeal y := (Iff.mpr hyiff) hy_in'
      exact (FuncSetup.mem_principalIdeal (S := S)).1 hx_in'

    exact ⟨hx_le_y, hy_le_x⟩

  · -- (←) x≤y ∧ y≤x ⇒ すべてのイデアルで x∈I ↔ y∈I
    intro hxy
    intro I hI
    constructor
    · intro hxI
      -- y ≤ x かつ x∈I ⇒ y∈I（下方閉性）
      have hyx : y ≤ x := hxy.2
      exact (hI (hyx) hxI)
    · intro hyI
      -- x ≤ y かつ y∈I ⇒ x∈I
      have hxy' : x ≤ y := hxy.1
      exact (hI (hxy') hyI)

end FuncSetup
end AvgRare
