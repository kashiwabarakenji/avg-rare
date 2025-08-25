--ファイル切り離し候補import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset--Mathlib.Topology.Instances.ENNReal.Lemmas --おためし
import LeanCopilot

universe u

open scoped BigOperators

namespace AvgRare

/-
SetFamily.lean  —  基本集合族とNDS。

集合族に関する基本的な定義と計数を行う。
- ここでは poset/ideal など順序に依存する概念は扱いません（Ideals 側へ）。
- トレースは Commonへ。
- FuncSetup が出てくるものは、FuncSetupへ。
-/

variable {α : Type u} [DecidableEq α]

--universe u
open Classical

variable {α : Type u} [DecidableEq α]

/- 技術：`∑ f = |s|` かつ `∀ i∈s, 1 ≤ f i` なら各項が 1。 -/

lemma sum_one_eq_card {ι : Type u} [DecidableEq ι]
  (s : Finset ι) : ∑ i ∈ s, (1 : Nat) = s.card := by
  classical
  refine Finset.induction_on s ?h0 ?hstep
  · simp
  · intro a s ha ih
    -- 和は「1 + 次の和」、個数は「カード+1」
    -- `simp` で両辺を同じ形に整えれば閉じる
    simp [ha]

/-- 抽象補題：
`s` 上で各項 `f i` が `1 ≤ f i`、しかも `∑_{i ∈ s} f i = s.card` なら
すべての項が `1`。引き算は使わない。 -/
lemma all_one_of_sum_eq_card
  {ι : Type u} [DecidableEq ι] :
  ∀ (s : Finset ι),                       -- ← まず s をイントロ
    (∀ f : ι → Nat,
      (∀ i ∈ s, 1 ≤ f i) →
      (∑ i ∈ s, f i = s.card) →
      ∀ i ∈ s, f i = 1)                    -- ← これが motive(s)
  := by
  intros s f h_le_one h_sum_eq_card

  -- ステップ1: `∑ i in s, (f i - 1)` が 0 になることを示す
  have h_sum_sub_one_eq_zero : ∑ i ∈ s, (f i - 1) = 0 := by
    -- `s.card + ∑ i in s, (f i - 1) = s.card` を示し、
    -- `Nat.add_left_cancel` で `∑ i in s, (f i - 1) = 0` を導く
    apply Nat.add_left_cancel
    -- `calc` ブロックで等式変形を行う
    calc
      -- まず、card を和の形に書き換える
      s.card + ∑ i ∈ s, (f i - 1) = (∑ i ∈ s, 1) + ∑ i ∈ s, (f i - 1) := by
        rw [Finset.sum_const]
        simp_all only [smul_eq_mul, mul_one]

      -- `sum_add_distrib` で和をまとめる
      _ = ∑ i ∈ s, (1 + (f i - 1)) := by
        rw [Finset.sum_add_distrib]
      -- `1 + (f i - 1)` を `f i` に戻す
      -- `h_le_one` から `1 ≤ f i` なので `(f i - 1) + 1 = f i` が成立する
      _ = ∑ i ∈ s, f i := by
        apply Finset.sum_congr rfl
        intros i hi
        rw [add_comm, Nat.sub_add_cancel (h_le_one i hi)]
      -- 仮説 `h_sum_eq_card` を使って、和を card に戻す
      _ = s.card := h_sum_eq_card

  -- ステップ2: 各 `f i - 1` が 0 であることを示す
  -- 自然数の和が 0 ならば、各項は 0 でなければならない (`Finset.sum_eq_zero_iff`)
  have h_sub_one_eq_zero : ∀ i ∈ s, f i - 1 = 0 :=
    Finset.sum_eq_zero_iff.mp h_sum_sub_one_eq_zero

  -- ステップ3: `f i = 1` を証明する
  intros i hi
  -- `f i - 1 = 0` は `f i ≤ 1` と同値 (`Nat.sub_eq_zero_iff_le`)
  have h_f_le_one : f i ≤ 1 := Nat.sub_eq_zero_iff_le.mp (h_sub_one_eq_zero i hi)
  -- 仮説 `h_le_one` から `1 ≤ f i` も得られている
  -- `f i ≤ 1` と `1 ≤ f i` から、反対称性により `f i = 1` が結論付けられる
  exact le_antisymm h_f_le_one (h_le_one i hi)

lemma card_eq_blocks_iff_all_blocks_card_one
  {α : Type u} [DecidableEq α]
  (s : Finset α) (P : Finset (Finset α))
  (hdisj : ∀ C ∈ P, ∀ D ∈ P, C ≠ D → Disjoint C D)
  (hcover : s = Finset.biUnion P (fun C => C))
  (hnonempty : ∀ C ∈ P, C.Nonempty) :
  s.card = P.card ↔ ∀ C ∈ P, C.card = 1 := by
  classical
  -- 濃度＝サイズ和
  have hsum :
      s.card = ∑ C ∈ P, C.card := by
    -- `card_biUnion` と被覆
    -- 実装： `have := Finset.card_biUnion hdisj; rw [hcover] at this; exact this`
    subst hcover
    simp_all only [ne_eq]
    have :(P.biUnion fun C => C).card = ∑ C ∈ P, C.card := by
      exact Finset.card_biUnion hdisj
    exact this
  -- 各ブロックは非空 ⇒ `1 ≤ C.card`
  have hpos : ∀ C ∈ P, 1 ≤ C.card := by
    intro C hC
    have : 0 < C.card := Finset.card_pos.mpr (hnonempty C hC)
    exact Nat.succ_le_of_lt this
  constructor
  · intro hEq
    -- `∑ card = P.card` に落とす
    have hsum' : ∑ C ∈ P, C.card = P.card := by
      -- `rw [← hsum]; exact hEq`
      subst hcover
      simp_all only [ne_eq, Finset.one_le_card, implies_true]
    -- 抽象補題を適用（`f := card`）
    exact all_one_of_sum_eq_card (s := P) (f := fun C => C.card) hpos hsum'
  · intro h1
    -- 逆向き：和が「全部 1」だから `∑ card = ∑1 = P.card`
    have hx : ∑ C ∈ P, C.card = ∑ C ∈ P, (1 : Nat) := by
      -- `sum_congr` で各項書換
      subst hcover
      simp_all only [ne_eq, le_refl, implies_true, Finset.sum_const, smul_eq_mul, mul_one]
    -- `∑1 = card`
    have hsum1 : ∑ C ∈ P, (1 : Nat) = P.card := by
      -- `simp`（`Finset.card` の事実）
      subst hcover
      simp_all only [ne_eq, le_refl, implies_true, Finset.sum_const, smul_eq_mul, mul_one]

    -- 合成して `s.card = P.card`
    -- `rw [hsum, hx, hsum1]`
    subst hcover
    simp_all only [ne_eq, le_refl, implies_true, Finset.sum_const, smul_eq_mul, mul_one]
