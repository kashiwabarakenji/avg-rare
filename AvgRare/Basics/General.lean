import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import LeanCopilot

universe u

open scoped BigOperators

namespace AvgRare

/-
General.lean is a general lemma.
We've gathered lemma that neither FuncSetup nor SetFamily assumes.
Do not refer to other files.
-/

variable {α : Type u} [DecidableEq α]

open Classical

variable {α : Type u} [DecidableEq α]

/- If `∑ f = |s|` and `∀ i∈s, 1 ≤ f i`, each term is 1. -/
lemma sum_one_eq_card {ι : Type u} [DecidableEq ι]
  (s : Finset ι) : ∑ _ ∈ s, (1 : Nat) = s.card := by
  classical
  refine Finset.induction_on s ?h0 ?hstep
  · simp
  · intro a s ha ih
    simp [ha]

/-- If `∑ f = |s|` and `∀ i∈s, 1 ≤ f i`, each term is 1. -/
private lemma all_one_of_sum_eq_card
  {ι : Type u} [DecidableEq ι] :
  ∀ (s : Finset ι),
    (∀ f : ι → Nat,
      (∀ i ∈ s, 1 ≤ f i) →
      (∑ i ∈ s, f i = s.card) →
      ∀ i ∈ s, f i = 1)
  := by
  intros s f h_le_one h_sum_eq_card

  have h_sum_sub_one_eq_zero : ∑ i ∈ s, (f i - 1) = 0 := by
    apply Nat.add_left_cancel
    calc
      s.card + ∑ i ∈ s, (f i - 1) = (∑ i ∈ s, 1) + ∑ i ∈ s, (f i - 1) := by
        rw [Finset.sum_const]
        simp_all only [smul_eq_mul, mul_one]

      _ = ∑ i ∈ s, (1 + (f i - 1)) := by
        rw [Finset.sum_add_distrib]
      _ = ∑ i ∈ s, f i := by
        apply Finset.sum_congr rfl
        intros i hi
        rw [add_comm, Nat.sub_add_cancel (h_le_one i hi)]
      _ = s.card := h_sum_eq_card

  have h_sub_one_eq_zero : ∀ i ∈ s, f i - 1 = 0 :=
    Finset.sum_eq_zero_iff.mp h_sum_sub_one_eq_zero

  intros i hi
  have h_f_le_one : f i ≤ 1 := Nat.sub_eq_zero_iff_le.mp (h_sub_one_eq_zero i hi)
  exact le_antisymm h_f_le_one (h_le_one i hi)

lemma card_eq_blocks_iff_all_blocks_card_one
  {α : Type u} [DecidableEq α]
  (s : Finset α) (P : Finset (Finset α))
  (hdisj : ∀ C ∈ P, ∀ D ∈ P, C ≠ D → Disjoint C D)
  (hcover : s = Finset.biUnion P (fun C => C))
  (hnonempty : ∀ C ∈ P, C.Nonempty) :
  s.card = P.card ↔ ∀ C ∈ P, C.card = 1 := by
  classical
  have hsum :
      s.card = ∑ C ∈ P, C.card := by
    subst hcover
    simp_all only [ne_eq]
    have :(P.biUnion fun C => C).card = ∑ C ∈ P, C.card := by
      exact Finset.card_biUnion hdisj
    exact this
  have hpos : ∀ C ∈ P, 1 ≤ C.card := by
    intro C hC
    have : 0 < C.card := Finset.card_pos.mpr (hnonempty C hC)
    exact Nat.succ_le_of_lt this
  constructor
  · intro hEq
    have hsum' : ∑ C ∈ P, C.card = P.card := by
      subst hcover
      simp_all only [ne_eq, Finset.one_le_card, implies_true]
    exact all_one_of_sum_eq_card (s := P) (f := fun C => C.card) hpos hsum'
  · intro h1
    have hx : ∑ C ∈ P, C.card = ∑ C ∈ P, (1 : Nat) := by
      subst hcover
      simp_all only [ne_eq, le_refl, implies_true, Finset.sum_const, smul_eq_mul, mul_one]
    have hsum1 : ∑ C ∈ P, (1 : Nat) = P.card := by
      subst hcover
      simp_all only [ne_eq, le_refl, implies_true, Finset.sum_const, smul_eq_mul, mul_one]

    subst hcover
    simp_all only [ne_eq, le_refl, implies_true, Finset.sum_const, smul_eq_mul, mul_one]

variable {β : Type*}

lemma card_filter_add_card_filter_not (s : Finset β) (p : β → Prop) [DecidablePred p] [DecidableEq β] :
    (s.filter p).card + (s.filter (fun b => ¬ p b)).card = s.card := by
classical
  -- 1) 互いに素
  have hdisj :
      Disjoint (s.filter p) (s.filter (fun b => ¬ p b)) := by
    refine Finset.disjoint_left.mpr ?_
    intro x hx hx'
    have hx_p  : p x     := (Finset.mem_filter.mp hx).2
    have hx_np : ¬ p x   := (Finset.mem_filter.mp hx').2
    exact (hx_np hx_p).elim
  -- 2) 和が元の集合
  have hcup :
      (s.filter p) ∪ (s.filter (fun b => ¬ p b)) = s := by
    ext x
    constructor
    · intro hx
      rcases Finset.mem_union.mp hx with hx | hx
      · exact (Finset.mem_filter.mp hx).1
      · exact (Finset.mem_filter.mp hx).1
    · intro hx
      by_cases hpx : p x
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨hx, hpx⟩))
      · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨hx, hpx⟩))
  -- 3) カード数
  have := Finset.card_union_of_disjoint (s := s.filter p)
                                        (t := s.filter (fun b => ¬ p b))
                                        hdisj
  -- (s ∪ t).card = s.card + t.card なので左右を入れ替えて使う
  simpa [hcup, Nat.add_comm] using this.symm


/- 上で別証明を行ったので、こちらは消す。

/-- `card (s.filter p) + card (s.filter (¬p)) = card s`。 -/
lemma card_filter_add_card_filter_not (s : Finset β) (p : β → Prop) [DecidablePred p] :
    (s.filter p).card + (s.filter (fun b => ¬ p b)).card = s.card := by
  classical
  refine Finset.induction_on s ?h0 ?hstep
  · simp
  · intro a s ha ih
    by_cases hpa : p a
    · -- p a
      have hfi_p :
          (insert a s).filter p = insert a (s.filter p) := by
        have := Finset.filter_insert (s := s) (p := p) a
        simpa [hpa] using this
      have hfi_np :
          (insert a s).filter (fun b => ¬ p b) = (s.filter (fun b => ¬ p b)) := by
        have := Finset.filter_insert (s := s) (p := fun b => ¬ p b) a
        have : ¬ p a = False := by simp_all only [not_true_eq_false, ↓reduceIte, eq_iff_iff, iff_false, not_false_eq_true]
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
      have hfi_p :
          (insert a s).filter p = (s.filter p) := by
        have := Finset.filter_insert (s := s) (p := p) a
        simpa [hpa] using this
      have hfi_np :
          (insert a s).filter (fun b => ¬ p b) = insert a (s.filter (fun b => ¬ p b)) := by
        have := Finset.filter_insert (s := s) (p := fun b => ¬ p b) a
        have : (¬ p a) = True := by simp_all only [not_false_eq_true, ↓reduceIte]
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
-/

-- 補助：S.filter p = S.filter q ↔ ∀ x∈S, p x ↔ q x
lemma filter_eq_iff_on {β} [DecidableEq β]
  {S : Finset β} {p q : β → Prop}
  [DecidablePred p] [DecidablePred q] :
  S.filter p = S.filter q ↔ (∀ x ∈ S, p x ↔ q x) := by
  constructor
  · intro h x hx
    have := congrArg (fun (T : Finset β) => x ∈ T) h
    simpa [Finset.mem_filter, hx] using this
  · intro h
    ext x; constructor <;> intro hx
    · rcases (Finset.mem_filter).1 hx with ⟨hxS, hpx⟩
      have : q x := (h x hxS).1 hpx
      exact (Finset.mem_filter).2 ⟨hxS, this⟩
    · rcases (Finset.mem_filter).1 hx with ⟨hxS, hqx⟩
      have : p x := (h x hxS).2 hqx
      exact (Finset.mem_filter).2 ⟨hxS, this⟩

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
    exact Finset.card_image_iff.mpr hinj
  have : s.card < s.card := by
    have hh := h
    rw [hcard] at hh
    exact hh
  exact (lt_irrefl _ this).elim

lemma le_of_eq_add_of_nonpos {a b t : Int}
    (h : a = b + t) (ht : t ≤ 0) : a ≤ b := by
  rw [h]
  have h1 : b + t ≤ b + 0 := add_le_add_left ht b
  have h2 := h1
  have : b + t ≤ b := by
    have h2' := h2
    exact (add_le_iff_nonpos_right b).mpr ht

  exact this
