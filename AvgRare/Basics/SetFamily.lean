import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import LeanCopilot

universe u

open scoped BigOperators

namespace AvgRare

/-- 有限台集合 `ground` と，その部分集合族 `sets`（判定述語＋可判定性） -/
structure SetFamily (α : Type u) [DecidableEq α] where
  ground    : Finset α
  sets      : Finset α → Prop
  decSets   : DecidablePred sets
  inc_ground :
    ∀ {s : Finset α}, sets s → s ⊆ ground

attribute [instance] SetFamily.decSets

namespace SetFamily
variable {α : Type u} [DecidableEq α]

/-- 族の全メンバー（有限集合の有限集合） -/
noncomputable def hyperedges (F : SetFamily α) : Finset (Finset α) :=
  F.ground.powerset.filter F.sets

/-- 超辺の個数（Nat） -/
noncomputable def number_of_hyperedgesNat (F : SetFamily α) : Nat :=
  F.hyperedges.card

/-- 頂点の次数（Nat）：その頂点を含む超辺数 -/
noncomputable def degreeNat (F : SetFamily α) (v : α) : Nat :=
  (F.hyperedges.filter (fun s => v ∈ s)).card

/-- 超辺サイズ総和（Nat）：`∑_{A∈F} |A|` -/
noncomputable def total_size_of_hyperedgesNat (F : SetFamily α) : Nat :=
  F.hyperedges.sum Finset.card

/-- 論文で使う整数スケール版：`2*deg(v) - |I|` -/
noncomputable def normalized_degree (F : SetFamily α) (v : α) : Int :=
  (2 : Int) * (F.degreeNat v : Int) - (F.number_of_hyperedgesNat : Int)

/-- 論文で使う整数スケール版：`2*Σ|A| - |I|*|ground|` -/
noncomputable def normalized_degree_sum (F : SetFamily α) : Int :=
  (2 : Int) * (F.total_size_of_hyperedgesNat : Int)
  - (F.number_of_hyperedgesNat : Int) * (F.ground.card : Int)

/-- 頂点 v が rare か（`normalized_degree ≤ 0`） -/
def is_rare (F : SetFamily α) (v : α) : Prop :=
  F.normalized_degree v ≤ 0

/-- 二重計数：`ground` 上の次数総和 = 超辺サイズ総和（Nat 版） -/
lemma degree_sum_eq_total_size_of_hyperedgesNat (F : SetFamily α) :
    (∑ v ∈ F.ground, F.degreeNat v) = F.total_size_of_hyperedgesNat := by
  classical
  -- 記号短縮
  set V := F.ground
  set H := F.hyperedges
  -- LHS を「if で数える形」に展開

  have hdeg :
      ∀ v ∈ V,
        (F.degreeNat v)
          = ∑ A ∈ H, (if v ∈ A then (1 : Nat) else 0) := by
    intro v hv
    -- `degreeNat v = card (H.filter (· ∋ v))` を if-和へ
    have := by
      -- `card_filter` を ∑ if に置換する定番形
      -- (H.filter p).card = ∑ A∈H, if p A then 1 else 0
      simpa using (Finset.card_filter (s := H) (p := fun A => v ∈ A))
    -- 上の `this : (H.filter (fun A => v ∈ A)).card = ...`
    -- を そのまま使えば OK
    simp [SetFamily.degreeNat, H]


  -- RHS（Σ|A|）を「if で数える形」に展開
  have hcard :
      ∀ {A}, A ∈ H → A.card = ∑ v ∈ V, (if v ∈ A then 1 else 0) := by
    intro A hA
    -- A ⊆ V を得る（H は V の powerset の filter なので）
    have hA_subV : A ⊆ V := by
      have : A ∈ V.powerset := (Finset.mem_filter.mp hA).1
      simpa [Finset.mem_powerset] using this
    -- `A.card` を V 上のインジケータ和に持ち上げる
    -- `card = ∑_{v∈A} 1` を，`A ⊆ V` を使って `∑_{v∈V} if v∈A then 1 else 0` に等しいへ
    calc
      A.card = (Finset.filter (fun v => v ∈ A) V).card := by
        -- A⊆V なので V を A で filter するとちょうど A
        -- （要素同値を示してから card を取る）
        have : V.filter (fun v => v ∈ A) = A := by
          ext v
          constructor
          · intro hv
            exact (Finset.mem_filter.mp hv).2
          · intro hv
            exact Finset.mem_filter.mpr ⟨hA_subV hv, hv⟩
        simp [this]
      _ = ∑ v ∈ V, (if v ∈ A then 1 else 0) := by
        -- `card_filter` の Nat 版（定番）
        simpa using (Finset.card_filter (s := V) (p := fun v => v ∈ A))

  -- 以上を使って Fubini（和の交換）
  calc
    (∑ v ∈ V, F.degreeNat v)
        = ∑ v ∈ V, ∑ A ∈ H, (if v ∈ A then 1 else 0) := by
          refine Finset.sum_congr rfl ?_
          intro v hv; simpa using hdeg v hv
    _   = ∑ A ∈ H, ∑ v ∈ V, (if v ∈ A then 1 else 0) := by
          exact Finset.sum_comm
    _   = ∑ A ∈ H, A.card := by
          refine Finset.sum_congr rfl ?_
          intro A hA;
          simp [hcard hA]
    _   = F.total_size_of_hyperedgesNat := rfl

/-- 各頂点の整数版 normalized_degree の総和 = 整数版 NDS -/
lemma sum_normalized_degree_eq_nds (F : SetFamily α) :
    (∑ v ∈ F.ground, F.normalized_degree v) = F.normalized_degree_sum := by
  classical
  -- Nat → Int：∑deg = ∑|A|
  have hNat : (∑ v ∈ F.ground, F.degreeNat v)
                = F.total_size_of_hyperedgesNat :=
    degree_sum_eq_total_size_of_hyperedgesNat (F := F)
  have hDC :
      (∑ v ∈ F.ground, (F.degreeNat v : Int))
        = (F.total_size_of_hyperedgesNat : Int) := by
    -- cast(∑ Nat) → ∑ cast(Nat)
    have := congrArg (fun n : Nat => (n : Int)) hNat
    -- 左辺 cast を ∑ に配る
    simpa [Nat.cast_sum] using this

  -- 以降は代数整理だけ
  unfold normalized_degree normalized_degree_sum
  have h1 :
      (∑ v ∈ F.ground, (2 : Int) * (F.degreeNat v : Int))
        = (2 : Int) * (∑ v ∈ F.ground, (F.degreeNat v : Int)) := by
    simp [Finset.mul_sum]
  have h2 :
      (∑ v ∈ F.ground, (F.number_of_hyperedgesNat : Int))
        = (F.ground.card : Int) * (F.number_of_hyperedgesNat : Int) := by
    simp [Finset.sum_const]

  calc
    (∑ v ∈ F.ground, ((2 : Int) * (F.degreeNat v : Int) - (F.number_of_hyperedgesNat : Int)))
        = (∑ v ∈ F.ground, (2 : Int) * (F.degreeNat v : Int))
          - (∑ v ∈ F.ground, (F.number_of_hyperedgesNat : Int)) := by
            simp [Finset.sum_sub_distrib]
    _   = (2 : Int) * (∑ v ∈ F.ground, (F.degreeNat v : Int))
          - (F.ground.card : Int) * (F.number_of_hyperedgesNat : Int) := by
            simp [h1, h2]
    _   = (2 : Int) * (F.total_size_of_hyperedgesNat : Int)
          - (F.number_of_hyperedgesNat : Int) * (F.ground.card : Int) := by
            -- 二重計数を適用
            simp [hDC, mul_comm]


end SetFamily
end AvgRare

--attribute [simp] Finset.mem_attach
--attribute [simp] Quot.eq -- 代表の単純化に使う場合は危険でない範囲で

--@[simp] lemma imageQuot_ground (E : Setoid α) (F : SetFamily α) :
--  imageQuot E F.ground = (trace E F).ground := rfl
