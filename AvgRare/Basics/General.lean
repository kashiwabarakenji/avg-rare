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
  (s : Finset ι) : ∑ _ ∈ s, (1 : Nat) = s.card := by
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

section CountLemmas

variable {β : Type*}

/-- `card (s.filter p) + card (s.filter (¬p)) = card s`。 -/
lemma card_filter_add_card_filter_not (s : Finset β) (p : β → Prop) [DecidablePred p] :
    (s.filter p).card + (s.filter (fun b => ¬ p b)).card = s.card := by
  classical
  refine Finset.induction_on s ?h0 ?hstep
  · simp
  · intro a s ha ih
    by_cases hpa : p a
    · -- p a
      -- 左辺： (insert a (filter p s)).card + (filter ¬p s).card
      have hfi_p :
          (insert a s).filter p = insert a (s.filter p) := by
        have := Finset.filter_insert (s := s) (p := p) a
        simpa [hpa] using this
      have hfi_np :
          (insert a s).filter (fun b => ¬ p b) = (s.filter (fun b => ¬ p b)) := by
        have := Finset.filter_insert (s := s) (p := fun b => ¬ p b) a
        -- ここでは `¬ p a = false`
        have : ¬ p a = False := by simp_all only [not_true_eq_false, ↓reduceIte, eq_iff_iff, iff_false, not_false_eq_true]
        -- false ケース
        simp_all only [not_true_eq_false, ↓reduceIte, eq_iff_iff, iff_false, not_false_eq_true]
      have hnot : a ∉ s.filter p := by
        intro ha'
        have : a ∈ s := (Finset.mem_of_subset (Finset.filter_subset _ _) ha')
        exact ha this
      have hcard_insert :
          (insert a (s.filter p)).card = (s.filter p).card + 1 :=
        Finset.card_insert_of_notMem hnot
      calc
        ((insert a s).filter p).card + ((insert a s).filter (fun b => ¬ p b)).card
            = (insert a (s.filter p)).card + (s.filter (fun b => ¬ p b)).card := by
                rw [hfi_p, hfi_np]
        _ = (s.filter p).card + 1 + (s.filter (fun b => ¬ p b)).card := by
                rw [hcard_insert]
        _ = (s.filter p).card + (s.filter (fun b => ¬ p b)).card + 1 := by
                exact Nat.add_right_comm (Finset.filter p s).card 1 {b ∈ s | ¬p b}.card
        _ = s.card + 1 := by
                rw [ih]
        _ = (insert a s).card := by
                -- `card_insert_of_not_mem`
                have := Finset.card_insert_of_notMem ha
                -- `card (insert a s) = card s + 1`
                exact this.symm
    · -- p a = false
      -- 対称な議論
      have hfi_p :
          (insert a s).filter p = (s.filter p) := by
        have := Finset.filter_insert (s := s) (p := p) a
        simpa [hpa] using this
      have hfi_np :
          (insert a s).filter (fun b => ¬ p b) = insert a (s.filter (fun b => ¬ p b)) := by
        have := Finset.filter_insert (s := s) (p := fun b => ¬ p b) a
        -- ここでは `¬ p a = true`
        have : (¬ p a) = True := by simp_all only [not_false_eq_true, ↓reduceIte]
        -- true ケース
        simp_all only [↓reduceIte, eq_iff_iff, iff_true]
      have hnot : a ∉ s.filter (fun b => ¬ p b) := by
        intro ha'
        have : a ∈ s := (Finset.mem_of_subset (Finset.filter_subset _ _) ha')
        exact ha this
      have hcard_insert :
          (insert a (s.filter (fun b => ¬ p b))).card
          = (s.filter (fun b => ¬ p b)).card + 1 :=
        Finset.card_insert_of_notMem hnot
      calc
        ((insert a s).filter p).card + ((insert a s).filter (fun b => ¬ p b)).card
            = (s.filter p).card + (insert a (s.filter (fun b => ¬ p b))).card := by
                rw [hfi_p, hfi_np]
        _ = (s.filter p).card + (s.filter (fun b => ¬ p b)).card + 1 := by
                rw [hcard_insert]
                exact rfl
        _ = s.card + 1 := by
                rw [ih]
        _ = (insert a s).card := by
                have := Finset.card_insert_of_notMem ha
                exact this.symm

--trace関係ないし、SetFamilyも出てきてないので、generalでもいいかも。
-- 補助：S.filter p = S.filter q ↔ ∀ x∈S, p x ↔ q x
lemma filter_eq_iff_on {β} [DecidableEq β]
  {S : Finset β} {p q : β → Prop}
  [DecidablePred p] [DecidablePred q] :
  S.filter p = S.filter q ↔ (∀ x ∈ S, p x ↔ q x) := by
  constructor
  · intro h x hx
    -- 等式の両辺で x の帰属が同値
    have := congrArg (fun (T : Finset β) => x ∈ T) h
    -- x∈S を仮定して filter の展開
    simpa [Finset.mem_filter, hx] using this
  · intro h
    ext x; constructor <;> intro hx
    · rcases (Finset.mem_filter).1 hx with ⟨hxS, hpx⟩
      have : q x := (h x hxS).1 hpx
      exact (Finset.mem_filter).2 ⟨hxS, this⟩
    · rcases (Finset.mem_filter).1 hx with ⟨hxS, hqx⟩
      have : p x := (h x hxS).2 hqx
      exact (Finset.mem_filter).2 ⟨hxS, this⟩

end CountLemmas

lemma exists_pair_with_same_image_of_card_image_lt
  {α β : Type u} [DecidableEq α] [DecidableEq β]
  (s : Finset α) (f : α → β)
  (h : (s.image f).card < s.card) :
  ∃ x ∈ s, ∃ y ∈ s, x ≠ y ∧ f x = f y := by

  classical
  by_contra hno
  -- hno : ¬ ∃ x ∈ s, ∃ y ∈ s, x ≠ y ∧ f x = f y
  have hinj : ∀ x ∈ s, ∀ y ∈ s, f x = f y → x = y := by
    intro x hx y hy hxy
    by_cases hxy' : x = y
    · exact hxy'
    · have : ∃ x ∈ s, ∃ y ∈ s, x ≠ y ∧ f x = f y :=
        ⟨x, hx, y, hy, hxy', hxy⟩
      exact False.elim (hno this)
  have hcard : (s.image f).card = s.card := by
    -- `card_image_iff` は「像の濃度＝元の濃度 ↔ injOn」。
    -- Finset 版はこの形で使えます。
    exact Finset.card_image_iff.mpr hinj
  -- これで `h : (s.image f).card < s.card` と矛盾
  have : s.card < s.card := by
    -- `rw` で書き換えて矛盾を顕在化
    -- （simpa using は使わない）
    have hh := h
    rw [hcard] at hh
    exact hh
  exact (lt_irrefl _ this).elim

--一般的な補題なので移動してもいい。TraceFunctionalとか。
lemma le_of_eq_add_of_nonpos {a b t : Int}
    (h : a = b + t) (ht : t ≤ 0) : a ≤ b := by
  -- 目標を h で書き換え
  rw [h]
  -- b + t ≤ b + 0
  have h1 : b + t ≤ b + 0 := add_le_add_left ht b
  -- 右の 0 を消す
  -- `rw [add_zero]` で十分
  -- （tactic スタイルを用いて `simpa` は使わない）
  have h2 := h1
  -- 書き換え
  -- ここは tactic ブロックで簡潔に
  have : b + t ≤ b := by
    -- 右辺の `+ 0` を消す
    -- `rw` は許容されている想定（`simpa using` を避けるため）
    -- 直接 h1 を上書きして使う
    -- 以降、この小ブロックでのみ tactic を使います
    -- (Lean では `by` ブロック内で `rw` を使えます)
    -- 変数 h1 を上書きしてもよいのですが、ここではローカルコピー h2 を書換えます
    have h2' := h2
    -- `rw [add_zero] at h2'`
    -- tactic:
    -- (ここで実際のコードでは `rw [add_zero] at h2'` と一行書きます)
    -- 仕上げとして h2' を返す想定です
    -- ただしこの大域ブロックでは term モードのため、最終形を直接返します：
    -- 手短に：`by have h := h1; rwa [add_zero] at h` でもOK
    exact (add_le_iff_nonpos_right b).mpr ht

  exact this
