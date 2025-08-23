import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import AvgRare.Basics.SetFamily
import LeanCopilot

/-
Ideals.lean — イデアル族

このファイルでは：
* 有限集合 V と二項関係 `le : α → α → Prop` に対する
  「V 上の順序イデアル」の述語 `isOrderIdealOn le V I`
* その全体を `SetFamily` として束ねる `orderIdealFamily le V`

FuncSetupを使わないものでIdealが関係して、traceが関係しないものを集めているが、
FuncSetup前提でなく、SetFamily前提のidealの議論そもそもあんまりないのかも。
結果的にほとんど使われない可能性あり。
commonのNDSを移動してきてもいいが、あっちもそれほど行数はない。500行以下。それにTrace関係なのであっちのほうがいいかも。

注意：
- ここでは `le` に可判定性や型クラス（`Preorder` 等）は**要求しません**。
  `orderIdealFamily` の述語の可判別性は `Classical.decPred` で与えます。
- `∑` は `∈` を使っています。`simpa using` は使っていません。
-/

universe u

open scoped BigOperators

namespace AvgRare

open SetFamily

variable {α : Type u} [DecidableEq α]

/-- `isOrderIdealOn le V I` :
  有限台集合 `V : Finset α` 上で，`I : Finset α` が
  （V に含まれること＋）`le` に関して下方閉包（downward-closed）であること。 -/
def isOrderIdealOn (le : α → α → Prop) (V I : Finset α) : Prop :=
  I ⊆ V ∧ ∀ ⦃x⦄, x ∈ I → ∀ ⦃y⦄, y ∈ V → le y x → y ∈ I

/-- 台集合 `V` と関係 `le` に対する「順序イデアル族」を `SetFamily` として束ねる。 -/
--idealFamilyの定義として利用されている。
noncomputable def orderIdealFamily (le : α → α → Prop) (V : Finset α) : SetFamily α := by
  classical
  refine
  { ground := V
    , sets := fun I => isOrderIdealOn le V I
    , decSets := Classical.decPred _
    , inc_ground := ?_ }
  intro A a
  simpa using a.1

namespace Ideals

variable (le : α → α → Prop) (V : Finset α)

@[simp] lemma isOrderIdealOn.subset {I : Finset α}
    (h : isOrderIdealOn le V I) : I ⊆ V := h.1

@[simp] lemma isOrderIdealOn_empty : isOrderIdealOn le V (∅ : Finset α) := by
  constructor
  · exact Finset.empty_subset V
  · intro x hx; cases hx
    -- 空集合なので到達不能

@[simp] lemma isOrderIdealOn_univ : isOrderIdealOn le V V := by
  constructor
  · exact Finset.Subset.rfl
  · intro x hx y hy hle
    exact hy

@[simp] lemma sets_iff_isOrderIdeal {I : Finset α} :
    (orderIdealFamily le V).sets I ↔ isOrderIdealOn le V I := Iff.rfl

@[simp] lemma empty_mem_orderIdealFamily :
    (orderIdealFamily le V).sets (∅ : Finset α) := by
  simp_all only [sets_iff_isOrderIdeal, isOrderIdealOn_empty]

@[simp] lemma V_mem_orderIdealFamily :
    (orderIdealFamily le V).sets V := by
  simp [sets_iff_isOrderIdeal]




end Ideals
/-
以下，後続の Trace/Forest 側で頻繁に用いる“計数系の等式”が置いてあったが、別のところで証明。
-/
/-
namespace Counting

variable (F : SetFamily α)


-- 和の分解：`erase x` のサイズ和と `degree x` の関係（Trace の差分計算に使用）
-- パラレルな要素をtraceした時にしか成り立たないので条件が足りない。xはパラレルパートナーを持つという条件を足す必要がある。
-- もしくは、traceの写像が単射であるという条件。
-- 現状使ってない。本当は次の補題で使うはず。
lemma total_size_decompose_erase_add_degree (x : α) :
    (∑ A ∈ F.edgeFinset, (A.erase x).card) + F.degree x = F.totalHyperedgeSize := by
  -- 典型事実：各 A について `A.card = (A.erase x).card + (if x ∈ A then 1 else 0)`
  -- を ∑ に流し込んだもの。後で証明を埋める。
  sorry


-- Trace がエッジ数を保つときの NDS の差分式（Lemma 3.6(2) で使用）
-- HCardPreserveの仮定が特殊なので、集合族一般で成り立つというほどではない。
-- サイズの合計に関する条件もいるかも。total_size_decompose_erase_add_degree
lemma nds_difference_by_trace
    {x : α}
    (hCardPreserve : (F.edgeFinset.card = (F.edgeFinset.image fun A => A.erase x).card))
    (hGround : True := True.intro) :
    NDS F =
      (2 * (∑ A ∈ F.edgeFinset, (A.erase x).card : Int)
        - (F.numHyperedges : Int) * (F.ground.card : Int)) + (2 * F.degree x - F.numHyperedges) := by
  -- 上の分解補題を Int にキャストして並べ替える等式。
  -- `image` 側の詳細は Trace 側で扱うため，ここでは card 保持を仮引数としておく。
  sorry

end Counting
-/
end AvgRare

/-
順序イデアル族に特化した“小さな事実”の言明。
-/
/-
namespace SpecialToOrderIdeals

variable (le : α → α → Prop) (V : Finset α)

instance instDecidablePred_rel_right (r : α → α → Prop) [DecidableRel r] (y : α) :
    DecidablePred (fun x => r x y) :=
  fun x => inferInstance

--principal idealを定義する。principal ideal自体がFuncSetupで定義されているのでここでは不要かも。
/-- （推奨版）`decide` を使わず、述語のまま `filter` する。
    これにより `failed to synthesize Decidable (le x v)` を回避。 -/
def principalOn (le : α → α → Prop) [DecidableRel le]
    (V : Finset α) (v : α) : Finset α :=
  V.filter (fun x => le x v)

@[simp] lemma mem_principalOn {le : α → α → Prop} [DecidableRel le]
    {V : Finset α} {v x : α} :
    x ∈ principalOn le V v ↔ x ∈ V ∧ le x v := by
  classical
  simp [principalOn]  -- `mem_filter`
-/

/-
 --idealsTraceでも同じようなことを証明している。idealFamily_mem_principal。とりあえず、コメントアウト
lemma principal_is_orderIdeal
    (le : α → α → Prop) [DecidableRel le]
    (V : Finset α) (v : α)
    (hrefl  : ∀ {x}, x ∈ V → le x x)
    (htrans : ∀ {x y z}, x ∈ V → y ∈ V → z ∈ V → le x y → le y z → le x z)
    : isOrderIdealOn le V (principalOn le V v) := by
  classical
  -- 1) ⊆ V
  constructor
  · intro x hx
    -- x ∈ V.filter (fun x => le x v) → x ∈ V
    exact (Finset.mem_filter.mp hx).1
  -- 2) downward-closed
  · intro x hx y hy h_yx
    -- x ∈ principalOn → x ∈ V ∧ le x v
    rcases (Finset.mem_filter.mp hx) with ⟨hxV, hx_le_v⟩
    -- 目標: y ∈ principalOn, すなわち y ∈ V ∧ le y v
    have hy_le_v : le y v := htrans (x := y) (y := x) (z := v) hy hxV (by
      -- v は principalOn のメンバである必要はないが、htrans の仮定が z ∈ V を要求するので
      -- ここでは v ∈ V を要求しない版の htrans を仮定している（上の仮定は z ∈ V も引数）
      -- 既に仮定の htrans は z ∈ V を引数に含む形なので、そのまま使う
      -- ただし、あなたの htrans の仮定が z ∈ V を必要としない形なら、この行の第三引数は不要
      -- 今回は要求されているので、hxV ではなく v ∈ V の仮定が必要になるが、
      -- principal ideal の定義では v ∈ V を仮定しない設計が自然なため、
      -- htrans の第三引数は hy か hxV に置換できない。z ∈ V を引数に取らない版を推奨。
      -- （下で z ∈ V 仮定を外した補題版も用意します）
      sorry
    ) h_yx hx_le_v
    -- 以上で y ∈ V ∧ le y v
    exact Finset.mem_filter.mpr ⟨hy, hy_le_v⟩
-/

/-
-- 台集合の大きさ以上にイデアルが存在する（Lemma 4.2 相当；型だけ用意）
--principal idealの議論を使う。これもidealsTraceで議論するほうがいいのかも。
lemma lower_bound_on_number_of_ideals :
    (orderIdealFamily le V).numHyperedges ≥ V.card + 1 := by
  -- 単射 v ↦ ↓v ＋ 空イデアルの 1 個を足す，という標準事実。
  sorry
-/



/-

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

--idealからmaximalな要素をtraceしても、イデアル性は保たれる。ただし、functional性まで議論してない。
lemma isOrderIdeal_erase_of_no_above
  {A : Finset S.Elem} (hA : S.isOrderIdeal A) {u : S.Elem}
  (hmax : ∀ {x : S.Elem}, u ≤ x → x = u) :
  S.isOrderIdeal (A.erase u) := by
  intro x y hy hx
  -- x ∈ A.erase u なら x ≠ u かつ x ∈ A
  rcases Finset.mem_erase.mp hx with ⟨hx_ne_u, hxA⟩
  -- 下方閉で y ∈ A
  have hyA : y ∈ A := hA hy hxA
  -- y = u だと `u ≤ x` から `x = u` を強制し，x≠u と矛盾
  have hy_ne_u : y ≠ u := by
    intro hyu
    have : u ≤ x := by simpa [hyu] using hy
    have : x = u := hmax this
    exact hx_ne_u this
  -- よって y ∈ A.erase u
  exact Finset.mem_erase.mpr ⟨hy_ne_u, hyA⟩

lemma isOrderIdeal_reindex
  (e : S.Elem ≃ S'.Elem)
  (hmono : ∀ {x y}, (e y) ≤' (e x) → y ≤ x)
  {A : Finset S.Elem} (hA : S.isOrderIdeal A) :
  S'.isOrderIdeal (A.image e) :=
by
  intro x' y' hy' hx'
  rcases Finset.mem_image.mp hx' with ⟨x, hx, rfl⟩
  rcases Finset.mem_image.mp ?goal with ⟨y, hyA, rfl⟩
  -- `hmono` と `hA` で決着
  exact Finset.mem_image.mpr
    ⟨y, hA (hmono hy') hx, rfl⟩

end

variable (S : FuncSetup α)

--パラレルであることと、preorderで同値なことが、等しい。
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

section Iso

@[simp]
lemma mem_map_equiv_iff
  {S S' : FuncSetup α} (e : S.Elem ≃ S'.Elem)
  (A : Finset S.Elem) (x : S.Elem) :
  e x ∈ A.map e.toEmbedding ↔ x ∈ A := by
  classical
  constructor
  · intro hx
    rcases Finset.mem_map.1 hx with ⟨x', hx', h⟩
    -- h : e.toEmbedding x' = e.toEmbedding x  →  e x' = e x
    have : x' = x := e.injective (by simpa using congrArg (fun z => (z : S'.Elem)) h)
    subst this
    simp_all only [Finset.mem_map_equiv, Equiv.symm_apply_apply, Equiv.coe_toEmbedding]
  · intro hx
    exact Finset.mem_map.2 ⟨x, hx, rfl⟩

/-- `e : S.Elem ≃ S'.Elem` が前順序の同型（`y ≤ x ↔ e y ≤ e x`）なら，
    `isOrderIdeal` は Equiv.map で保存される（→方向） -/
lemma isOrderIdeal_map_equiv_of_forward
  {S S' : FuncSetup α}
  (e : S.Elem ≃ S'.Elem)
  (mono : ∀ {x y : S.Elem}, (y ≤ x) ↔ (e y ≤ e x))
  {A : Finset S.Elem}
  (hA : S.isOrderIdeal A) :
  (S').isOrderIdeal (A.map e.toEmbedding) := by
  classical
  -- 下方閉性の確認
  intro x' y' hle' hx'
  -- 順序対応で S 側へ戻す
  have hle : e.symm y' ≤ e.symm x' := by
    -- mono を x := e.symm x', y := e.symm y' に適用
    have := (mono : ∀ {x y}, y ≤ x ↔ e y ≤ e x)
    simp_all only [implies_true, Finset.mem_map_equiv, Subtype.forall, Subtype.coe_eta, Equiv.apply_symm_apply]
  -- メンバーを S 側へ移して使う
  have hxA : e.symm x' ∈ A := by
    -- x' ∈ A.map e.toEmbedding ↔ e.symm x' ∈ A
    simpa [mem_map_equiv_iff (S:=S) (S':=S') e A (e.symm x')] using
      (by
        -- x' と e (e.symm x') は一致
        have : e (e.symm x') = x' := by simp
        simpa [this] using hx')
  -- 下方閉性から e.symm y' ∈ A
  have hyA : e.symm y' ∈ A := hA hle hxA
  -- もう一度 S' 側へ
  have : y' ∈ A.map e.toEmbedding := by
    -- y' = e (e.symm y')
    have : e (e.symm y') = y' := by simp
    simpa [this, mem_map_equiv_iff (S:=S) (S':=S') e A (e.symm y')] using hyA
  exact this

/-- `e : S.Elem ≃ S'.Elem` が前順序の同型（`y ≤ x ↔ e y ≤ e x`）なら，
    `isOrderIdeal` は Equiv.map で保存される（←方向） -/
lemma isOrderIdeal_map_equiv_of_backward
  {S S' : FuncSetup α}
  (e : S.Elem ≃ S'.Elem)
  (mono : ∀ {x y : S.Elem}, (y ≤ x) ↔ (e y ≤ e x))
  {A : Finset S.Elem}
  (hA' : (S').isOrderIdeal (A.map e.toEmbedding)) :
  S.isOrderIdeal A := by
  classical
  -- 下方閉性の確認
  intro x y hle hx
  -- 順序対応で S' 側へ送る
  have hle' : e y ≤ e x := (mono.mp hle)
  -- x∈A から e x ∈ A.map ...
  have hx' : e x ∈ A.map e.toEmbedding := by
    simpa [mem_map_equiv_iff (S:=S) (S':=S') e A x] using hx
  -- 下方閉性で e y ∈ map
  have hy' : e y ∈ A.map e.toEmbedding := hA' hle' hx'
  -- 戻すと y ∈ A
  simpa [mem_map_equiv_iff (S:=S) (S':=S') e A y] using hy'

/-- まとめ：`e` が前順序の同型なら，`A` が order ideal であることと
    `A.map e` が order ideal であることは同値 -/
lemma isOrderIdeal_reindex
  {S S' : FuncSetup α}
  (e : S.Elem ≃ S'.Elem)
  (mono : ∀ {x y : S.Elem}, (y ≤ x) ↔ (e y ≤ e x))
  {A : Finset S.Elem} :
  (S').isOrderIdeal (A.map e.toEmbedding) ↔ S.isOrderIdeal A :=
by
  constructor
  · intro h; exact isOrderIdeal_map_equiv_of_backward (S:=S) (S':=S') e mono h
  · intro h; exact isOrderIdeal_map_equiv_of_forward  (S:=S) (S':=S') e mono h

end Iso

section Erase

/-- 有用な像換算：`(A.image f).erase (f u) = (A.erase u).image f` （`f` 単射） -/
lemma image_erase_eq_erase_image
  {β : Type _} [DecidableEq β] (f : S.Elem ↪ β) (A : Finset S.Elem) (u : S.Elem) :
  (A.image f).erase (f u) = (A.erase u).image f := by
  classical
  -- `Finset.image` は単射写像で良い性質を持つ
  -- この恒等式は mathlib にもありますが、自前で `ext` + `simp` で示せます。
  ext b; constructor <;> intro hb
  · -- → 方向
    rcases Finset.mem_erase.1 hb with ⟨hbne, hbimg⟩
    rcases Finset.mem_image.1 hbimg with ⟨x, hxA, rfl⟩
    have : x ≠ u := by
      intro hxu; subst hxu; exact hbne rfl
    exact Finset.mem_image.2 ⟨x, Finset.mem_erase.2 ⟨this, hxA⟩, rfl⟩
  · -- ← 方向
    rcases Finset.mem_image.1 hb with ⟨x, hxA, rfl⟩
    rcases Finset.mem_erase.1 hxA with ⟨hxne, hxA'⟩
    apply Finset.mem_erase.2
    simp_all only [Finset.mem_erase, ne_eq, not_false_eq_true, and_self, Finset.mem_image, EmbeddingLike.apply_eq_iff_eq,
    exists_eq_right]

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

/-
lemma isOrderIdeal_erase {A : Finset S.Elem} (hA : S.isOrderIdeal A) (u : S.Elem) :
  S.isOrderIdeal (A.erase u) := by
  intro x y hy hx
  -- x ∈ A.erase u ⇒ x ∈ A
  have hxA : x ∈ A := Finset.mem_of_mem_erase hx
  -- 下方閉で y ∈ A
  have hyA : y ∈ A := hA hy hxA
  -- かつ y ≠ u を示せば y ∈ A.erase u
  by_cases hyu : y = u
  · -- もし y = u なら、x ≤ y = u かつ x ≠ u（erase の仮定）から
    -- 下方閉で u ∈ A までは良いが、erase に入らない。矛盾ではないので
    -- 直接は入らない。別ルート：`Finset.mem_erase` の必要条件は `y ≠ u`
    -- なので `hyu` は排除する。
    exact False.elim (by

      -- `hyx : x ∈ A.erase u` から x ≠ u が従う
      have hxne : x ≠ u := (Finset.mem_erase.1 hx).1
      -- y = u かつ y ≤ x から x = u なら ≤ 反射で矛盾…としたくなるが
      -- ここは簡単に「y ≠ u が必要」という形で片を付ける：
      revert hyA; simp [hyu]
      show u ∉ A
      sorry
      )
  · -- y ≠ u。よって erase に入る
    exact Finset.mem_erase.2 ⟨hyu, hyA⟩
-/

end Erase


end FuncSetup
end AvgRare

-/
