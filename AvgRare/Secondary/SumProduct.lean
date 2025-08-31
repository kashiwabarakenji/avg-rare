import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Logic.Relation
import Mathlib.Tactic.Ring
import AvgRare.Basics.SetFamily
import AvgRare.Functional.FuncSetup
import AvgRare.Functional.FuncPoset

universe u
namespace AvgRare
namespace SumProduct
open Classical
variable {α : Type u} [DecidableEq α]
open AvgRare
open FuncSetup

/-- `coIdeal m := ground \ principalIdeal m` -/
noncomputable def coIdeal (S : FuncSetup α)(m : S.Elem) : Finset α :=
  S.ground \ (S.principalIdeal m.1 m.2)

/-- membership of `coIdeal m`  -/
lemma mem_coIdeal_iff (S : FuncSetup α)
  {m : S.Elem} {y : α} :
  y ∈ coIdeal S m ↔ y ∈ S.ground ∧ y ∉ S.principalIdeal m.1 m.2 := by
  classical
  unfold coIdeal
  exact Finset.mem_sdiff

lemma exists_first_step_or_refl (S : FuncSetup α)
  {x m : S.Elem} :
  S.le x m → x = m ∨ ∃ z : S.Elem, S.cover x z ∧ S.le z m := by
  intro hxm
  induction hxm with
  | @refl  =>
      exact Or.inl rfl
  | @tail b c hxb hbc ih =>
      cases ih with
      | inl hxb_eq =>
          cases hxb_eq
          exact Or.inr ⟨c, hbc, Relation.ReflTransGen.refl⟩
      | inr h =>
          rcases h with ⟨z, hxz, hzb⟩
          exact Or.inr ⟨z, hxz, Relation.ReflTransGen.tail hzb hbc⟩

private lemma cover_preserves_principalIdeal_of_maximal (S : FuncSetup α)
  --(hpos : isPoset S)
  {m x y : S.Elem}
  (hm : S.maximal m)
  (hx : x.1 ∈ S.principalIdeal m.1 m.2)
  (hxy : S.cover x y) :
  y.1 ∈ S.principalIdeal m.1 m.2 := by
  classical
  have ⟨hxG, hxm⟩ :=
    (S.mem_principalIdeal_iff (a := m.1) (y := x.1) (ha := m.2)).1 hx
  have := exists_first_step_or_refl S (x := x) (m := m) hxm
  cases this with
  | inl hx_eq =>
      cases hx_eq
      have hmle : S.le m y := Relation.ReflTransGen.single hxy
      have hyle : S.le y m := hm hmle
      exact
        (S.mem_principalIdeal_iff (a := m.1) (y := y.1) (ha := m.2)).2
          ⟨y.2, hyle⟩
  | inr h =>
      rcases h with ⟨z, hxz, hzm⟩
      have : z = y := by
        dsimp [FuncSetup.cover] at hxz hxy
        exact Eq.trans (Eq.symm hxz) hxy
      cases this
      exact
        (S.mem_principalIdeal_iff (a := m.1) (y := y.1) (ha := m.2)).2
          ⟨y.2, hzm⟩

private lemma cover_preserves_coIdeal  (S : FuncSetup α)
  {m x y : S.Elem}
  (hx : x.1 ∈ coIdeal S m) (hxy : S.cover x y) :
  y.1 ∈ coIdeal S m := by
  classical
  have hxy_le : S.le x y := Relation.ReflTransGen.single hxy
  have : y.1 ∉ S.principalIdeal m.1 m.2 := by
    intro hy
    have ⟨hyG, hyle⟩ :=
      (S.mem_principalIdeal_iff (a := m.1) (y := y.1) (ha := m.2)).1 hy
    have : S.le x ⟨m.1, m.2⟩ := hxy_le.trans hyle
    have hx_in :
      x.1 ∈ S.principalIdeal m.1 m.2 :=
      (S.mem_principalIdeal_iff (a := m.1) (y := x.1) (ha := m.2)).2 ⟨x.2, this⟩
    have := (mem_coIdeal_iff S (m := m) (y := x.1)).1 hx
    exact this.2 hx_in
  have hyG : y.1 ∈ S.ground := y.2
  exact (mem_coIdeal_iff S (m := m) (y := y.1)).2 ⟨hyG, this⟩

private lemma le_preserves_coIdeal (S : FuncSetup α)
  {m x y : S.Elem} (hx : x.1 ∈ coIdeal S m) (hxy : S.le x y) :
  y.1 ∈ coIdeal S m := by
  classical
  induction hxy with
  | @refl =>
      exact hx
  | @tail b c hxbc hbc ih =>
      exact cover_preserves_coIdeal S (m := m) (x := b) (y := c) ih hbc

private lemma le_preserves_principalIdeal_of_maximal (S : FuncSetup α)
  {m x y : S.Elem}
  (hm : S.maximal m)
  (hx : x.1 ∈ S.principalIdeal m.1 m.2)
  (hxy : S.le x y) :
  y.1 ∈ S.principalIdeal m.1 m.2 := by
  classical
  induction hxy with
  | @refl =>
    simp_all only [maximal_iff, le_iff_leOn_val, Subtype.forall]
  | @tail z hxz hzy ih =>
    apply cover_preserves_principalIdeal_of_maximal S (m := m) (x := z) hm
    (expose_names; exact a_ih)
    exact ih


noncomputable def upSet (S : FuncSetup α)
 (y : S.Elem) : Finset S.Elem :=
  (S.ground.attach).filter (fun t => S.le y t)

/-- `U := { t | x ≤ t }`  is non-empty for （`x ∈ U`）。 -/
lemma mem_U_of_x (S : FuncSetup α) (x : S.Elem) :
  x ∈ (S.ground.attach).filter (fun t => S.le x t) := by
  refine Finset.mem_filter.mpr ?_
  exact ⟨by simp, Relation.ReflTransGen.refl⟩

/-- existance of maximal element above `x` -/
lemma exists_maximal_above (S : FuncSetup α)
  [Fintype S.Elem] --(hpos : isPoset S)
  (x : S.Elem) :
  ∃ m : S.Elem, S.maximal m ∧ S.le x m := by
  classical
  -- U := {t | x ≤ t}
  let U : Finset S.Elem := (S.ground.attach).filter (fun t => S.le x t)
  have hUne : U.Nonempty := ⟨x, mem_U_of_x S x⟩

  let μ : S.Elem → Nat := fun y => (upSet S y).card

  obtain ⟨m, hmU, hmin⟩ := Finset.exists_min_image U μ hUne
  have hxm : S.le x m := (Finset.mem_filter.mp hmU).2

  have hm : S.maximal m := by
    intro y hmy
    have hyU : y ∈ U := by
      refine Finset.mem_filter.mpr ?_
      exact ⟨by simp, Relation.ReflTransGen.trans hxm hmy⟩

    have hsubset : upSet S y ⊆ upSet S m := by
      intro w hw
      have hyw : S.le y w := (Finset.mem_filter.mp hw).2
      have hmw : S.le m w := Relation.ReflTransGen.trans hmy hyw
      exact Finset.mem_filter.mpr ⟨by simp, hmw⟩

    by_contra hnot
    have hm_in : m ∈ upSet S m :=
      Finset.mem_filter.mpr ⟨by simp, Relation.ReflTransGen.refl⟩
    have hm_notin : m ∉ upSet S y := by
      intro hmem
      exact hnot ((Finset.mem_filter.mp hmem).2)
    have hne : upSet S y ≠ upSet S m := by
      intro hEq
      have : m ∈ upSet S y := by
        have := hm_in
        exact hEq ▸ this
      exact hm_notin this
    have hss : upSet S y ⊂ upSet S m := by
      exact HasSubset.Subset.ssubset_of_not_subset hsubset fun a => hm_notin (a hm_in)

    have hlt : (upSet S y).card < (upSet S m).card := by exact Finset.card_lt_card hss
    have hle : (upSet S m).card ≤ (upSet S y).card := hmin y hyU
    have : (upSet S y).card < (upSet S y).card := Nat.lt_of_lt_of_le hlt hle
    exact (lt_irrefl _ ) this

  exact ⟨m, hm, hxm⟩

private lemma coIdeal_nonempty_of_two_maximal (S : FuncSetup α)
  (hpos : isPoset S)
  {m m' : S.Elem} (hm' : S.maximal m') (hne : m ≠ m') :
  (coIdeal S m).Nonempty := by
  classical
  have hnot :
    m'.1 ∉ S.principalIdeal m.1 m.2 := by
    intro hmem
    have ⟨hmG, hm'le⟩ :=
      (S.mem_principalIdeal_iff (a := m.1) (y := m'.1) (ha := m.2)).1 hmem
    have hmle' : S.le m m' := hm' hm'le
    have : m = m' := by exact hpos (hm' hm'le) hm'le
    exact hne this
  have hm'G : m'.1 ∈ S.ground := m'.2
  have : m'.1 ∈ coIdeal S m :=
    (mem_coIdeal_iff S (m := m) (y := m'.1)).2 ⟨hm'G, hnot⟩
  exact ⟨m'.1, this⟩

private lemma coIdeal_nonempty_of_not_unique_maximal
  (S : FuncSetup α) [Fintype S.Elem]
  (hpos : isPoset S)
  (notuniq : ¬ (∃! mm : S.Elem, S.maximal mm))
  (m : S.Elem) :
  (coIdeal S m).Nonempty := by
  classical
  obtain ⟨m0, hm0, _hx⟩ := exists_maximal_above S m
  have htwo : ∃ m1 : S.Elem, S.maximal m1 ∧ m1 ≠ m0 := by
    by_contra hnone
    have huniq : ∃! mm : S.Elem, S.maximal mm := by
      refine ⟨m0, hm0, ?_⟩
      intro mm hmm
      by_contra hneq
      exact hnone ⟨mm, hmm, hneq⟩
    exact notuniq huniq
  rcases htwo with ⟨m1, hm1, hne10⟩

  let mp : S.Elem := if h : m = m0 then m1 else m0

  have hmp_max : S.maximal mp := by
    by_cases h : m = m0
    · have : mp = m1 := by simp [mp, h]
      simp_all only [maximal_iff, le_iff_leOn_val, Subtype.forall, Finset.coe_mem, ne_eq, dite_eq_ite, ↓reduceIte,
        implies_true, mp]

    · have : mp = m0 := by simp [mp, h]
      simp_all only [maximal_iff, le_iff_leOn_val, Subtype.forall, Finset.coe_mem, ne_eq, dite_eq_ite, ↓reduceIte,
    implies_true, mp]

  have hne_m_mp : m ≠ mp := by
    by_cases h : m = m0
    · have hem : mp = m1 := by simp [mp, h]
      have hneq : m ≠ m1 := by
        intro heq
        have : m0 = m1 := Eq.trans (Eq.symm h) heq
        apply hne10
        exact id (Eq.symm this)
      intro heq
      have : m = m1 := Eq.trans heq hem
      exact hneq this
    · have hem : mp = m0 := by simp [mp, h]
      intro heq
      have : m = m0 := Eq.trans heq hem
      exact h this

  exact coIdeal_nonempty_of_two_maximal S hpos
    (m := m) (m' := mp) hmp_max hne_m_mp

private lemma no_comparable_across_split (S : FuncSetup α)
  {m x y : S.Elem}
  (hm : S.maximal m)
  (hx : x.1 ∈ S.principalIdeal m.1 m.2)
  (hy : y.1 ∈ coIdeal S m) :
  ¬ S.le x y ∧ ¬ S.le y x := by
  classical
  have h₁ : ¬ S.le x y := by
    intro hxy
    have yin : y.1 ∈ S.principalIdeal m.1 m.2 :=
      le_preserves_principalIdeal_of_maximal S  (m := m)
        (x := x) (y := y) hm hx hxy
    have : y.1 ∈ S.ground ∧ y.1 ∉ S.principalIdeal m.1 m.2 :=
      (mem_coIdeal_iff S (m := m) (y := y.1)).1 hy
    exact this.2 yin
  have h₂ : ¬ S.le y x := by
    intro hyx
    have xin : x.1 ∈ coIdeal S m :=
      le_preserves_coIdeal S (m := m) (x := y) (y := x) hy hyx
    have : x.1 ∈ S.ground ∧ x.1 ∉ S.principalIdeal m.1 m.2 :=
      (mem_coIdeal_iff S (m := m) (y := x.1)).1 xin
    exact this.2 hx
  exact ⟨h₁, h₂⟩

noncomputable def restrictToIdeal (S : FuncSetup α)
  (m : S.Elem) (hm : S.maximal m): FuncSetup α := by
  classical
  refine
    { ground := S.principalIdeal m.1 m.2
      nonempty := by
        have : m.1 ∈ S.principalIdeal m.1 m.2 := by
          exact self_mem_principalIdeal S m
        simp_all only [maximal_iff, le_iff_leOn_val, Subtype.forall, nonempty_subtype]
        obtain ⟨val, property⟩ := m
        simp_all only
        exact ⟨_, this⟩
      , f := ?f }
  intro x
  let xg : S.Elem := ⟨x.1, (principalIdeal_subset_ground S ⟨m.1,m.2⟩) x.2⟩
  let y : S.Elem := S.f xg
  have : y.1 ∈ S.principalIdeal m.1 m.2 :=
    cover_preserves_principalIdeal_of_maximal S
      (m := m) (x := xg) (y := y) hm
      (by
        exact x.2)
      rfl
  exact ⟨y.1, this⟩

noncomputable def restrictToCoIdeal (S : FuncSetup α) (m : S.Elem)  (hpos : isPoset S) (notconnected: ¬ (∃! mm: S.Elem, S.maximal mm)): FuncSetup α := by
  classical
  refine
    { ground := coIdeal S m,
      nonempty := by
        let cno := coIdeal_nonempty_of_not_unique_maximal S (hpos := hpos) notconnected m
        simp_all only [nonempty_subtype]
        obtain ⟨val, property⟩ := m
        exact cno
    , f := ?f }
  intro x
  let xg : S.Elem :=
    ⟨x.1, (mem_coIdeal_iff S (m := m) (y := x.1)).1 x.2 |>.1⟩
  let y : S.Elem := S.f xg
  have : y.1 ∈ coIdeal S m :=
    cover_preserves_coIdeal S (m := m) (x := xg) (y := y)
      (by
        -- `x.2 : x.1 ∈ coIdeal m`
        exact x.2)
      rfl
  exact ⟨y.1, this⟩

private lemma ground_union_split
  (S : FuncSetup α) (m : S.Elem) (hm : S.maximal m)
  (hpos : isPoset S) (notconnected : ¬ (∃! mm : S.Elem, S.maximal mm)) :
  (restrictToIdeal S m hm).ground ∪ (restrictToCoIdeal S m hpos notconnected).ground
    = S.ground := by
  classical
  change S.principalIdeal m.1 m.2 ∪ coIdeal S m = S.ground
  unfold coIdeal
  have hsub : S.principalIdeal m.1 m.2 ⊆ S.ground :=
    S.principalIdeal_subset_ground ⟨m.1, m.2⟩
  -- `s ∪ (t \ s) = t`
  exact Finset.union_sdiff_of_subset hsub

private lemma ground_disjoint_split
  (S : FuncSetup α) (m : S.Elem) (hm : S.maximal m)
  (hpos : isPoset S) (notconnected : ¬ (∃! mm : S.Elem, S.maximal mm)) :
  Disjoint (restrictToIdeal S m hm).ground (restrictToCoIdeal S m hpos notconnected).ground := by
  classical
  change Disjoint (S.principalIdeal m.1 m.2) (coIdeal S m)
  unfold coIdeal
  exact Finset.disjoint_sdiff

private lemma card_coIdeal_eq_sub (S : FuncSetup α) (m : S.Elem) :
  (coIdeal S m).card = S.ground.card - (S.principalIdeal m.1 m.2).card := by
  classical
  have hsub : S.principalIdeal m.1 m.2 ⊆ S.ground :=
    S.principalIdeal_subset_ground ⟨m.1, m.2⟩
  unfold coIdeal
  exact Finset.card_sdiff hsub

private lemma card_coIdeal_add_card_principal
  (S : FuncSetup α) (m : S.Elem) :
  (coIdeal S m).card + (S.principalIdeal m.1 m.2).card = S.ground.card := by
  classical
  have hsub : S.principalIdeal m.1 m.2 ⊆ S.ground :=
    S.principalIdeal_subset_ground ⟨m.1, m.2⟩
  have hsdiff :
    (coIdeal S m).card = S.ground.card - (S.principalIdeal m.1 m.2).card :=
    card_coIdeal_eq_sub S m
  -- (A \ B).card + B.card = A.card
  calc
    (coIdeal S m).card + (S.principalIdeal m.1 m.2).card
        = (S.ground.card - (S.principalIdeal m.1 m.2).card)
          + (S.principalIdeal m.1 m.2).card := by
            exact congrArg (fun t => t + (S.principalIdeal m.1 m.2).card) hsdiff
    _ = S.ground.card := by
         apply Nat.sub_add_cancel
         exact Finset.card_le_card hsub

private lemma card_coIdeal_lt_ground (S : FuncSetup α) (m : S.Elem) :
  (coIdeal S m).card < S.ground.card := by
  classical
  have hmem : m.1 ∈ S.principalIdeal m.1 m.2 := S.self_mem_principalIdeal m
  have hpos : 0 < (S.principalIdeal m.1 m.2).card :=
    Finset.card_pos.mpr ⟨m.1, hmem⟩
  have hsum := card_coIdeal_add_card_principal S m
  have hle : (coIdeal S m).card + 1 ≤ S.ground.card := by
    have : 1 ≤ (S.principalIdeal m.1 m.2).card := Nat.succ_le_of_lt hpos
    have : (coIdeal S m).card + 1
            ≤ (coIdeal S m).card + (S.principalIdeal m.1 m.2).card :=
      Nat.add_le_add_left this _
    calc
      (coIdeal S m).card + 1
          ≤ (coIdeal S m).card + (S.principalIdeal m.1 m.2).card := this
      _ = S.ground.card := hsum
  have : (coIdeal S m).card < Nat.succ ((coIdeal S m).card) :=
    Nat.lt_succ_self _
  exact Nat.lt_of_lt_of_le this (by
    have : Nat.succ ((coIdeal S m).card) = (coIdeal S m).card + 1 := rfl
    exact (by
      simpa using hle))

private lemma card_principal_lt_ground_of_not_unique
  (S : FuncSetup α) [Fintype S.Elem]
  (hpos : isPoset S) (notconnected : ¬ (∃! mm : S.Elem, S.maximal mm))
  (m : S.Elem) :
  (S.principalIdeal m.1 m.2).card < S.ground.card := by
  classical
  have hne : (coIdeal S m).Nonempty :=
    coIdeal_nonempty_of_not_unique_maximal S (hpos := hpos) notconnected m
  obtain ⟨y, hy⟩ := hne
  have hposCo : 0 < (coIdeal S m).card := Finset.card_pos.mpr ⟨y, hy⟩
  have hsum := card_coIdeal_add_card_principal S m
  have hle : (S.principalIdeal m.1 m.2).card + 1 ≤ S.ground.card := by
    have : 1 ≤ (coIdeal S m).card := Nat.succ_le_of_lt hposCo
    have : (S.principalIdeal m.1 m.2).card + 1
            ≤ (S.principalIdeal m.1 m.2).card + (coIdeal S m).card :=
      Nat.add_le_add_left this _
    have hcomm :
      (S.principalIdeal m.1 m.2).card + (coIdeal S m).card
        = (coIdeal S m).card + (S.principalIdeal m.1 m.2).card := by
      exact Nat.add_comm _ _
    calc
      (S.principalIdeal m.1 m.2).card + 1
          ≤ (S.principalIdeal m.1 m.2).card + (coIdeal S m).card := this
      _ = (coIdeal S m).card + (S.principalIdeal m.1 m.2).card := hcomm
      _ = S.ground.card := hsum
  have : (S.principalIdeal m.1 m.2).card < Nat.succ ((S.principalIdeal m.1 m.2).card) :=
    Nat.lt_succ_self _
  exact Nat.lt_of_lt_of_le this (by
    -- `succ = +1`
    have : Nat.succ ((S.principalIdeal m.1 m.2).card)
            = (S.principalIdeal m.1 m.2).card + 1 := rfl
    simpa using hle)

--It is called from MainStatement.
lemma restrictToCoIdeal_card_lt
  (S : FuncSetup α) (m : S.Elem)
  (hpos : isPoset S) (notconnected : ¬ (∃! mm : S.Elem, S.maximal mm)) :
  (restrictToCoIdeal S m hpos notconnected).ground.card < S.ground.card := by
  classical
  -- ground = coIdeal
  change (coIdeal S m).card < S.ground.card
  exact card_coIdeal_lt_ground S m

/--The platform set size of `restrictToIdeal` is truly small (if the maximum is not unique). -/
lemma restrictToIdeal_card_lt_of_not_unique
  (S : FuncSetup α) (m : S.Elem) (hm : S.maximal m)
  [Fintype S.Elem] (hpos : isPoset S)
  (notconnected : ¬ (∃! mm : S.Elem, S.maximal mm)) :
  (restrictToIdeal S m hm).ground.card < S.ground.card := by
  classical
  -- ground = principalIdeal
  change (S.principalIdeal m.1 m.2).card < S.ground.card
  exact card_principal_lt_ground_of_not_unique S (hpos := hpos) notconnected m

lemma unique_maximal_above (S : FuncSetup α)
  [Fintype S.Elem] (hpos : isPoset S)
  {x m₁ m₂ : S.Elem}
  (hm₁ : S.maximal m₁) (hm₂ : S.maximal m₂)
  (hx₁ : S.le x m₁) (hx₂ : S.le x m₂) :
  m₁ = m₂ := by
  classical
  rcases (le_iff_exists_iter S x m₁).1 hx₁ with ⟨i, hi⟩
  rcases (le_iff_exists_iter S x m₂).1 hx₂ with ⟨j, hj⟩
  by_cases hij : i ≤ j
  · -- m₁ ≤ m₂
    have hchain := S.le_between_iter x hij
    have h₁ : S.le m₁ ((S.f^[j]) x) := by cases hi; exact hchain
    have h₂ : S.le m₁ m₂ := by cases hj; exact h₁
    have h₃ : S.le m₂ m₁ := hm₁ h₂
    exact hpos (hm₂ (hm₁ h₂)) h₃
  ·
    have hji : j ≤ i := le_of_not_ge hij
    have hchain := le_between_iter S x hji
    have h₁ : S.le m₂ ((S.f^[i]) x) := by cases hj; exact hchain
    have h₂ : S.le m₂ m₁ := by cases hi; exact h₁
    have h₃ : S.le m₁ m₂ := hm₂ h₂
    exact hpos (hm₂ (hm₁ h₃)) h₂

/-
lemma exists_unique_maxAbove (S : FuncSetup α)
  [Fintype S.Elem] (hpos : isPoset S) (x : S.Elem) :
  ∃! m : S.Elem, S.maximal m ∧ S.le x m := by
  classical
  obtain ⟨m, hm, hxm⟩ := exists_maximal_above S x
  refine ⟨m, ⟨hm, hxm⟩, ?uniq⟩
  intro m' hm'
  let uma := unique_maximal_above (S := S) (hpos := hpos) (hm₁ := hm) (hm₂ := hm'.1)  (hx₁ := hxm) (hx₂ := hm'.2)
  exact id (Eq.symm uma)
-/

def liftFromIdeal
  (S : FuncSetup α) (m : S.Elem) (hm : S.maximal m)
  (x : (restrictToIdeal S m hm).Elem) : S.Elem :=
  ⟨ x.1, (S.principalIdeal_subset_ground ⟨m.1, m.2⟩) x.2 ⟩

def liftFromCoIdeal
  (S : FuncSetup α) (m : S.Elem) (hpos : isPoset S) (notuniq : ¬∃! mm, S.maximal mm)
  (x : (restrictToCoIdeal S m hpos notuniq).Elem) : S.Elem :=
  ⟨ x.1, (mem_coIdeal_iff S (m := m) (y := x.1)).1 x.2 |>.1 ⟩

private lemma cover_lift_Ideal
  (S : FuncSetup α) (m : S.Elem) (hm : S.maximal m)
  {x y : (restrictToIdeal S m hm).Elem} :
  (restrictToIdeal S m hm).cover x y →
  S.cover (liftFromIdeal S m hm x) (liftFromIdeal S m hm y) := by
  classical
  intro h
  dsimp [FuncSetup.cover, restrictToIdeal] at h
  let xg : S.Elem := ⟨x.1, (S.principalIdeal_subset_ground ⟨m.1,m.2⟩) x.2⟩
  have hval : (S.f xg).1 = y.1 := congrArg Subtype.val h

  dsimp [liftFromIdeal]
  apply Subtype.ext
  exact hval

private lemma cover_lift_CoIdeal
  (S : FuncSetup α) (m : S.Elem) (hpos : isPoset S) (notuniq : ¬∃! mm, S.maximal mm)
  {x y : (restrictToCoIdeal S m hpos notuniq).Elem} :
  (restrictToCoIdeal S m hpos notuniq).cover x y →
  S.cover (liftFromCoIdeal S m hpos notuniq x) (liftFromCoIdeal S m hpos notuniq y) := by
  classical
  intro h
  dsimp [FuncSetup.cover, restrictToCoIdeal] at h
  let xg : S.Elem := ⟨x.1, (mem_coIdeal_iff S (m := m) (y := x.1)).1 x.2 |>.1⟩
  have hval : (S.f xg).1 = y.1 := congrArg Subtype.val h
  dsimp [liftFromCoIdeal]
  apply Subtype.ext
  exact hval


/-- Lift `≤` of `restrictToIdeal` to `≤` of `S`. -/
lemma le_lift_Ideal
  (S : FuncSetup α) (m : S.Elem) (hm : S.maximal m)
  {x y : (restrictToIdeal S m hm).Elem} :
  (restrictToIdeal S m hm).le x y →
  S.le (liftFromIdeal S m hm x) (liftFromIdeal S m hm y) := by
  classical
  intro hxy
  induction hxy with
  | @refl =>
      exact Relation.ReflTransGen.refl
  | @tail b c hbc hcy ih =>
      have hcov :
          S.cover (liftFromIdeal S m hm b) (liftFromIdeal S m hm c) := by
        apply cover_lift_Ideal S m hm
        exact hcy
      exact Relation.ReflTransGen.tail ih hcov

/-- Lift `≤` of `restrictToCoIdeal` to `≤` of `S`. -/
lemma le_lift_CoIdeal
  (S : FuncSetup α) (m : S.Elem)
  (hpos : isPoset S) (notuniq : ¬ (∃! mm : S.Elem, S.maximal mm))
  {x y : (restrictToCoIdeal S m hpos notuniq).Elem} :
  (restrictToCoIdeal S m hpos notuniq).le x y →
  S.le (liftFromCoIdeal S m hpos notuniq x) (liftFromCoIdeal S m hpos notuniq y) := by
  classical
  intro hxy
  induction hxy with
  | @refl =>
      exact Relation.ReflTransGen.refl
  | @tail b c hbc hcy ih =>
      have hcov :
          S.cover (liftFromCoIdeal S m hpos notuniq b)
                  (liftFromCoIdeal S m hpos notuniq c) := by
        apply cover_lift_CoIdeal S m hpos notuniq
        exact hcy
      exact Relation.ReflTransGen.tail ih hcov

--Called from MainStatement.lean
theorem antisymm_restrictToIdeal_of_isPoset
  (S : FuncSetup α) (hpos : isPoset S) (m : S.Elem) (hm : S.maximal m) :
  ∀ {u v : (restrictToIdeal S m hm).Elem},
    (restrictToIdeal S m hm).le u v →
    (restrictToIdeal S m hm).le v u →
    u = v := by
  classical
  intro u v huv hvu
  have : S.le (liftFromIdeal S m hm u) (liftFromIdeal S m hm v) :=
    le_lift_Ideal S m hm huv
  have : (S.le (liftFromIdeal S m hm u) (liftFromIdeal S m hm v))
       ∧ (S.le (liftFromIdeal S m hm v) (liftFromIdeal S m hm u)) := by
    exact ⟨this, le_lift_Ideal S m hm hvu⟩
  rcases this with ⟨h₁, h₂⟩
  have h_eqS : liftFromIdeal S m hm u = liftFromIdeal S m hm v := by
    exact hpos this h₂
  have : u.1 = v.1 :=by
    simp_all only [le_iff_leOn_val]
    injection h_eqS

  exact Subtype.ext this

--Called from MainStatement.lean
lemma antisymm_restrictToCoIdeal_of_isPoset
  (S : FuncSetup α) (hpos : isPoset S) (m : S.Elem)
  (notuniq : ¬∃! mm, S.maximal mm) :
  ∀ {u v : (restrictToCoIdeal S m hpos notuniq).Elem},
    (restrictToCoIdeal S m hpos notuniq).le u v →
    (restrictToCoIdeal S m hpos notuniq).le v u →
    u = v := by
  classical
  intro u v huv hvu
  have h₁ : S.le (liftFromCoIdeal S m hpos notuniq u) (liftFromCoIdeal S m hpos notuniq v) :=
    le_lift_CoIdeal S m hpos notuniq huv
  have h₂ : S.le (liftFromCoIdeal S m hpos notuniq v) (liftFromCoIdeal S m hpos notuniq u) :=
    le_lift_CoIdeal S m hpos notuniq hvu
  have h_eqS :
      liftFromCoIdeal S m hpos notuniq u
    = liftFromCoIdeal S m hpos notuniq v := by
    exact hpos h₁ h₂
  have : u.1 = v.1 := by
    apply congrArg Subtype.val
    simp_all only [le_iff_leOn_val]
    injection h_eqS
    (expose_names; exact Subtype.eq val_eq)
  exact Subtype.ext this

-----------------------------------sumProd

private lemma mem_edge_sumProd_iff {α} [DecidableEq α]
  (F₁ F₂ : SetFamily α) {X : Finset α} :
  X ∈ (SetFamily.sumProd F₁ F₂).edgeFinset
    ↔ ∃ A ∈ F₁.edgeFinset, ∃ B ∈ F₂.edgeFinset, X = A ∪ B := by
  classical
  constructor
  · intro h
    have hsets :
        (SetFamily.sumProd F₁ F₂).sets X :=
      (SetFamily.mem_edgeFinset_iff_sets (F := SetFamily.sumProd F₁ F₂) (A := X)).1 h
    rcases hsets with ⟨A, B, hA, hB, rfl⟩
    have hAe : A ∈ F₁.edgeFinset :=
      (SetFamily.mem_edgeFinset_iff_sets (F := F₁) (A := A)).2 hA
    have hBe : B ∈ F₂.edgeFinset :=
      (SetFamily.mem_edgeFinset_iff_sets (F := F₂) (A := B)).2 hB
    exact ⟨A, hAe, B, hBe, rfl⟩
  · intro h
    rcases h with ⟨A, hAe, B, hBe, rfl⟩
    have hAset : F₁.sets A :=
      (SetFamily.mem_edgeFinset_iff_sets (F := F₁) (A := A)).1 hAe
    have hBset : F₂.sets B :=
      (SetFamily.mem_edgeFinset_iff_sets (F := F₂) (A := B)).1 hBe
    have hXset :
        (SetFamily.sumProd F₁ F₂).sets (A ∪ B) :=
      ⟨A, B, hAset, hBset, rfl⟩
    exact (SetFamily.mem_edgeFinset_iff_sets
            (F := SetFamily.sumProd F₁ F₂) (A := A ∪ B)).2 hXset

/-- `edgeFinset` 自体の同一視（像としての記述）。 -/
--Called from MainStatement.lean
theorem edgeFinset_sumProd {α} [DecidableEq α]
  (F₁ F₂ : SetFamily α) :
  (SetFamily.sumProd F₁ F₂).edgeFinset
    =
    (F₁.edgeFinset.product F₂.edgeFinset).image
      (fun p : Finset α × Finset α => p.1 ∪ p.2) := by
  classical
  ext X
  constructor
  · intro h
    have := (mem_edge_sumProd_iff F₁ F₂ (X := X)).1 h
    rcases this with ⟨A, hAe, B, hBe, rfl⟩
    refine Finset.mem_image.mpr ?_
    refine ⟨(A, B), ?prod, rfl⟩
    exact Finset.mem_product.mpr ⟨hAe, hBe⟩
  · intro h
    rcases Finset.mem_image.mp h with ⟨p, hp, rfl⟩
    rcases Finset.mem_product.mp hp with ⟨hA, hB⟩
    have : ∃ A ∈ F₁.edgeFinset, ∃ B ∈ F₂.edgeFinset, p.1 ∪ p.2 = A ∪ B :=
      ⟨p.1, hA, p.2, hB, rfl⟩
    have := (mem_edge_sumProd_iff F₁ F₂ (X := p.1 ∪ p.2)).2 this
    exact this

/-- principal ideal 側：`S₁ := restrictToIdeal S m hm` の `leOn` は
    ground 上では `S` の `leOn` を含意する。 -/
private lemma leOn_of_leOn_restrict_I
  (S : FuncSetup α) (m : S.Elem) (hm : S.maximal m)
  {x y : α} (hxI : x ∈ S.principalIdeal m.1 m.2) (hyI : y ∈ S.principalIdeal m.1 m.2)
  (hxy : (restrictToIdeal S m hm).leOn x y) :
  S.leOn x y := by
  classical
  have hxG : x ∈ S.ground := (S.principalIdeal_subset_ground ⟨m.1,m.2⟩) hxI
  have hyG : y ∈ S.ground := (S.principalIdeal_subset_ground ⟨m.1,m.2⟩) hyI
  have : (restrictToIdeal S m hm).le ⟨x, hxI⟩ ⟨y, hyI⟩ := by
    have hiff := (restrictToIdeal S m hm).le_iff_leOn_val (x := ⟨x,hxI⟩) (y := ⟨y,hyI⟩)
    exact (leOn_iff (restrictToIdeal S m hm) hxI hyI).mp hxy
  have : S.le (liftFromIdeal S m hm ⟨x,hxI⟩) (liftFromIdeal S m hm ⟨y,hyI⟩) :=
    le_lift_Ideal S m hm this
  have hiffS := S.le_iff_leOn_val (x := ⟨x,hxG⟩) (y := ⟨y,hyG⟩)
  exact (leOn_iff S hxG hyG).mpr this

/-- co-ideal 側：`S₂ := restrictToCoIdeal S m hpos notuniq` の `leOn` は
    ground 上では `S` の `leOn` を含意する。 -/
private lemma leOn_of_leOn_restrict_C
  (S : FuncSetup α) (m : S.Elem)
  (hpos : isPoset S) (notuniq : ¬ (∃! mm : S.Elem, S.maximal mm))
  {x y : α} (hxC : x ∈ coIdeal S m) (hyC : y ∈ coIdeal S m)
  (hxy : (restrictToCoIdeal S m hpos notuniq).leOn x y) :
  S.leOn x y := by
  classical
  have hxG : x ∈ S.ground := (mem_coIdeal_iff S (m := m) (y := x)).1 hxC |>.1
  have hyG : y ∈ S.ground := (mem_coIdeal_iff S (m := m) (y := y)).1 hyC |>.1
  have : (restrictToCoIdeal S m hpos notuniq).le ⟨x, hxC⟩ ⟨y, hyC⟩ := by
    have hiff := (restrictToCoIdeal S m hpos notuniq).le_iff_leOn_val
                    (x := ⟨x,hxC⟩) (y := ⟨y,hyC⟩)
    exact (leOn_iff (restrictToCoIdeal S m hpos notuniq) hxC hyC).mp hxy
  have : S.le (liftFromCoIdeal S m hpos notuniq ⟨x,hxC⟩)
               (liftFromCoIdeal S m hpos notuniq ⟨y,hyC⟩) :=
    le_lift_CoIdeal S m hpos notuniq this
  have hiffS := S.le_iff_leOn_val (x := ⟨x,hxG⟩) (y := ⟨y,hyG⟩)
  exact (leOn_iff S hxG hyG).mpr this

private lemma mem_I_or_C_of_ground
  (S : FuncSetup α) (m : S.Elem) (hm : S.maximal m)
  (hpos : isPoset S) (notuniq : ¬ (∃! mm : S.Elem, S.maximal mm))
  {x : α} (hxG : x ∈ S.ground) :
  x ∈ S.principalIdeal m.1 m.2 ∨ x ∈ coIdeal S m := by
  classical
  have hsplit :=
    ground_union_split S m hm hpos notuniq
  have : x ∈ (restrictToIdeal S m hm).ground ∪ (restrictToCoIdeal S m hpos notuniq).ground := by
    simp_all only

  have : x ∈ S.principalIdeal m.1 m.2 ∪ coIdeal S m := this
  exact Finset.mem_union.mp this

private lemma build_restrict_le_I
  (S : FuncSetup α) (m : S.Elem) (hm : S.maximal m)
  {y x : α} (hyG : y ∈ S.ground) (hxG : x ∈ S.ground)
  (hyI : y ∈ S.principalIdeal m.1 m.2) (hxI : x ∈ S.principalIdeal m.1 m.2)
  (h : S.le ⟨y,hyG⟩ ⟨x,hxG⟩) :
  (restrictToIdeal S m hm).le ⟨y,hyI⟩ ⟨x,hxI⟩ := by
  classical
  have main :
    ∀ (b : S.Elem), S.le ⟨y,hyG⟩ b → (hb:b.1 ∈ S.principalIdeal m.1 m.2) →
      (restrictToIdeal S m hm).le ⟨y,hyI⟩ ⟨b.1, by exact hb⟩ := by
    intro b hb_le hbI
    induction hb_le with
    | @refl =>
        exact Relation.ReflTransGen.refl
    | @tail p q hpq hpq_to_b ih =>
        have hp_in_I : p.1 ∈ S.principalIdeal m.1 m.2 := by
          have y_le_p : S.le ⟨y,hyG⟩ p := by
            exact hpq --ih.elim (fun _ => Relation.ReflTransGen.refl) (fun h => h)
          exact
            le_preserves_principalIdeal_of_maximal (S := S)
              (m := m) (x := ⟨y,hyG⟩) (y := p) hm
              (by exact hyI) y_le_p
        have hcov_restrict :
            (restrictToIdeal S m hm).cover
              ⟨p.1, hp_in_I⟩
              ⟨q.1,
                by
                  have : S.le p q := by
                    apply Relation.ReflTransGen.single
                    exact hpq_to_b
                  exact
                    le_preserves_principalIdeal_of_maximal (S := S)
                      (m := m) (x := p) (y := q) hm hp_in_I this⟩ := by
          have hf_pq : S.f ⟨p.1, p.2⟩ = q := by
            simp_all only [le_iff_leOn_val, forall_const, Subtype.coe_eta]
            exact hpq_to_b
          have hf_on_input :
              S.f ⟨p.1, (S.principalIdeal_subset_ground ⟨m.1,m.2⟩) hp_in_I⟩
            = q := by
            simp_all only [le_iff_leOn_val, forall_const, Subtype.coe_eta]

          dsimp [FuncSetup.cover, restrictToIdeal]
          apply Subtype.ext
          have := congrArg Subtype.val hf_on_input
          exact this
        apply  Relation.ReflTransGen.tail
        exact ih hp_in_I

        exact hcov_restrict

  have := main ⟨x,hxG⟩ h hxI
  exact this

/--（前方向の証明内で使う）`S.le ⟨y,hyG⟩ ⟨x,hxG⟩` から
  `restrictToCoIdeal` 側の `le ⟨y,hyC⟩ ⟨x,hxC⟩` を構成する。 -/
private lemma build_restrict_le_C
  (S : FuncSetup α) (m : S.Elem)
  (hpos : isPoset S) (notuniq : ¬ (∃! mm : S.Elem, S.maximal mm))
  {y x : α} (hyG : y ∈ S.ground) (hxG : x ∈ S.ground)
  (hyC : y ∈ coIdeal S m) (hxC : x ∈ coIdeal S m)
  (h : S.le ⟨y,hyG⟩ ⟨x,hxG⟩) :
  (restrictToCoIdeal S m hpos notuniq).le ⟨y,hyC⟩ ⟨x,hxC⟩ := by
  classical
  have main :
    ∀ (b : S.Elem), S.le ⟨y,hyG⟩ b →(hb:b.1 ∈ coIdeal S m) →
      (restrictToCoIdeal S m hpos notuniq).le ⟨y,hyC⟩ ⟨b.1, by exact hb⟩ := by
    intro b hb_le hbC
    induction hb_le with
    | @refl =>
        exact Relation.ReflTransGen.refl
    | @tail p q hpq hpq_to_b ih =>

        have hp_in_C : p.1 ∈ coIdeal S m := by
          have y_le_p : S.le ⟨y,hyG⟩ p := by
            exact hpq
          exact
            le_preserves_coIdeal (S := S) (m := m)
              (x := ⟨y,hyG⟩) (y := p) (hx := hyC) (hxy := y_le_p)

        have hp_ground :
          p.1 ∈ S.ground :=
          (mem_coIdeal_iff S (m := m) (y := p.1)).1 hp_in_C |>.1
        let pG : S.Elem := ⟨p.1, hp_ground⟩

        have hf_pq : S.f ⟨p.1, p.2⟩ = q := by
          exact hpq_to_b

        have heq_dom : pG = ⟨p.1, p.2⟩ := by
          apply Subtype.ext; rfl

        have hf_on_input : S.f pG = q := by
          have := congrArg (fun z => S.f z) heq_dom
          exact Eq.trans this hf_pq

        have hq_in_C : q.1 ∈ coIdeal S m :=
          cover_preserves_coIdeal (S := S)
            (m := m) (x := p) (y := q) (hx := hp_in_C) (hxy := hpq_to_b)

        have hcov_restrict :
            (restrictToCoIdeal S m hpos notuniq).cover
              ⟨p.1, hp_in_C⟩ ⟨q.1, hq_in_C⟩ := by

          dsimp [FuncSetup.cover, restrictToCoIdeal]

          apply Subtype.ext

          apply congrArg Subtype.val hf_on_input

        apply Relation.ReflTransGen.tail
        exact ih hp_in_C
        exact hcov_restrict

  exact main ⟨x,hxG⟩ h hxC

private lemma ideal_sets_iff_sumProd
  (S : FuncSetup α) (m : S.Elem) (hm : S.maximal m)
  (hpos : isPoset S) (notuniq : ¬ (∃! mm : S.Elem, S.maximal mm))
  {X : Finset α} :
  (S.idealFamily).sets X ↔
  ∃ A B,
    ((restrictToIdeal S m hm).idealFamily).sets A ∧
    ((restrictToCoIdeal S m hpos notuniq).idealFamily).sets B ∧
    X = A ∪ B := by
  classical
  -- 記号省略
  let I : Finset α := S.principalIdeal m.1 m.2
  let C : Finset α := coIdeal S m
  let F  := S.idealFamily
  let F₁ := (restrictToIdeal S m hm).idealFamily
  let F₂ := (restrictToCoIdeal S m hpos notuniq).idealFamily
  constructor
  ·
    intro hX
    let A : Finset α := X ∩ I
    let B : Finset α := X ∩ C
    have hA : F₁.sets A := by
      dsimp [SetFamily.sets, SetFamily, FuncSetup.idealFamily] at *
      have hAsub : A ⊆ I := by
        intro x hx
        exact (Finset.mem_inter.mp hx).2
      have hdc :
        ∀ ⦃x⦄, x ∈ A → ∀ ⦃y⦄, y ∈ I →
          (restrictToIdeal S m hm).leOn y x → y ∈ A := by
        intro x hxA y hyI hle₁
        have hxX : x ∈ X := (Finset.mem_inter.mp hxA).1
        have hyG : y ∈ S.ground :=
          (S.principalIdeal_subset_ground ⟨m.1,m.2⟩) hyI
        have hleS : S.leOn y x :=
          leOn_of_leOn_restrict_I S m hm (hxI := hyI)
                                   (hyI := (Finset.mem_inter.mp hxA).2) hle₁
        have : y ∈ X := by
          cases hX with
          | intro hsub hdown =>
            exact hdown (by exact hxX) (by exact hyG) (by exact hleS)
        exact Finset.mem_inter.mpr ⟨this, hyI⟩
      exact And.intro hAsub hdc

    have hB : F₂.sets B := by

      dsimp [SetFamily.sets, SetFamily, FuncSetup.idealFamily] at *

      have hBsub : B ⊆ C := by
        intro x hx
        exact (Finset.mem_inter.mp hx).2
      have hdc :
        ∀ ⦃x⦄, x ∈ B → ∀ ⦃y⦄, y ∈ C →
          (restrictToCoIdeal S m hpos notuniq).leOn y x → y ∈ B := by
        intro x hxB y hyC hle₂

        have hxX : x ∈ X := (Finset.mem_inter.mp hxB).1
        -- y ∈ ground
        have hyG : y ∈ S.ground := (mem_coIdeal_iff S (m := m) (y := y)).1 hyC |>.1
        have hleS : S.leOn y x :=
          leOn_of_leOn_restrict_C S m hpos notuniq (hxC := hyC)
                                  (hyC := (Finset.mem_inter.mp hxB).2) hle₂
        have : y ∈ X := by
          cases hX with
          | intro hsub hdown =>
              exact hdown (by exact hxX) (by exact hyG) (by exact hleS)
        exact Finset.mem_inter.mpr ⟨this, hyC⟩
      exact And.intro hBsub hdc

    -- X = A ∪ B
    have hXeq : X = A ∪ B := by
      have : C = S.ground \ I := rfl
      have hsplit :=
        ground_union_split S m hm hpos notuniq
      have : X = X ∩ S.ground := by
        cases hX with
        | intro hsub hdown =>
          simp_all only [sets_iff_isOrderIdeal, F₁, A, I, F₂, B, C]
          ext a : 1
          simp_all only [Finset.mem_inter, iff_self_and]
          intro a_1
          exact hsub a_1

      calc
        X = X ∩ S.ground := this
        _ = X ∩ ((restrictToIdeal S m hm).ground ∪ (restrictToCoIdeal S m hpos notuniq).ground) := by
              have := congrArg (fun (t : Finset α) => X ∩ t)
                               (ground_union_split S m hm hpos notuniq)
              exact id (Eq.symm this)
        _ = (X ∩ I) ∪ (X ∩ C) := by
              exact
                Finset.inter_union_distrib_left X (restrictToIdeal S m hm).ground
                  (restrictToCoIdeal S m hpos notuniq).ground
        _ = A ∪ B := rfl

    exact ⟨A, B, hA, hB, hXeq⟩

  ·
    intro hx
    rcases hx with ⟨A, B, hA, hB, rfl⟩
    dsimp [SetFamily.sets, SetFamily, FuncSetup.idealFamily] at *
    have hAsubI : A ⊆ I := (And.left hA)
    have hBsubC : B ⊆ C := (And.left hB)
    have hIsubG : I ⊆ S.ground :=
      S.principalIdeal_subset_ground ⟨m.1,m.2⟩
    have hCsubG : C ⊆ S.ground := by
      intro x hxC
      exact (mem_coIdeal_iff S (m := m) (y := x)).1 hxC |>.1
    have hXsubG : (A ∪ B) ⊆ S.ground := by
      intro x hx
      have hx' := Finset.mem_union.mp hx
      cases hx' with
      | inl hxA => exact hIsubG (hAsubI hxA)
      | inr hxB => exact hCsubG (hBsubC hxB)

    have hdown :
      ∀ ⦃x⦄, x ∈ A ∪ B → ∀ ⦃y⦄, y ∈ S.ground → S.leOn y x → y ∈ A ∪ B := by
      intro x hxU y hyG hleS
      have hxU' := Finset.mem_union.mp hxU
      cases hxU' with
      | inl hxA =>
          have hyI : y ∈ I := by
            by_contra hyNotI
            have hyC : y ∈ C := by
              have := mem_I_or_C_of_ground S m hm hpos notuniq hyG
              cases this with
              | inl hyI0 => exact False.elim (hyNotI hyI0)
              | inr hyC0 => exact hyC0
            let yE : S.Elem := ⟨y, hyG⟩
            let xE : S.Elem := ⟨x, hIsubG (hAsubI hxA)⟩
            have h_yx : S.le yE xE :=
              (S.le_iff_leOn_val (x := yE) (y := xE)).mpr hleS
            dsimp [C] at hyC
            have hnc := no_comparable_across_split S (m := m) (x := xE) (y:= yE)
                          (hm := hm)
                          (hx := by exact hAsubI hxA)
                          (hy := hyC)

            simp_all only [Finset.mem_union, true_or, le_iff_leOn_val, not_true_eq_false, and_false, C, I, yE, xE]

          have h_yx_Sle : S.le ⟨y, hyG⟩ ⟨x, hIsubG (hAsubI hxA)⟩ :=
            (S.le_iff_leOn_val (x := ⟨y,hyG⟩) (y := ⟨x,hIsubG (hAsubI hxA)⟩)).mpr hleS

          have hyx_restrict_leOn :
              (restrictToIdeal S m hm).leOn y x := by

            have h_restrict_le :
                (restrictToIdeal S m hm).le ⟨y, hyI⟩ ⟨x, hAsubI hxA⟩ :=
              build_restrict_le_I S m hm
                (hyG := hyG)
                (hxG := hIsubG (hAsubI hxA))
                (hyI := hyI)
                (hxI := hAsubI hxA)
                (h := h_yx_Sle)

            have hiff :=
              (restrictToIdeal S m hm).le_iff_leOn_val
                (x := ⟨y, hyI⟩) (y := ⟨x, hAsubI hxA⟩)

            have hyx_restrict_leOn :
                (restrictToIdeal S m hm).leOn y x :=
              by exact (leOn_iff (restrictToIdeal S m hm) hyI (hAsubI hxA)).mpr h_restrict_le

            exact (leOn_iff (restrictToIdeal S m hm) hyI (hAsubI hxA)).mpr h_restrict_le
          have hA_closed := (And.right hA)
          have : y ∈ A := hA_closed hxA hyI hyx_restrict_leOn
          exact Finset.mem_union.mpr (Or.inl this)

      | inr hxB =>
          have hyC : y ∈ C := by
            by_contra hyNotC
            have hyI : y ∈ I := by
              have := mem_I_or_C_of_ground S m hm hpos notuniq hyG
              cases this with
              | inl hyI0 => exact hyI0
              | inr hyC0 => exact False.elim (hyNotC hyC0)
            let yE : S.Elem := ⟨y, hyG⟩
            let xE : S.Elem := ⟨x, hCsubG (hBsubC hxB)⟩
            have h_yx : S.le yE xE :=
              (S.le_iff_leOn_val (x := yE) (y := xE)).mpr hleS
            have hnc := no_comparable_across_split S (m := m) (x := yE) (y := xE)
                          (hm := hm)
                          (hx := by exact hyI)
                          (hy := by
                            -- x∈C
                            exact hBsubC hxB )
            exact (hnc.1) h_yx
          have h_yx_Sle : S.le ⟨y, hyG⟩ ⟨x, hCsubG (hBsubC hxB)⟩ :=
            (S.le_iff_leOn_val (x := ⟨y,hyG⟩) (y := ⟨x,hCsubG (hBsubC hxB)⟩)).mpr hleS
          have hyx_restrict_leOn :
              (restrictToCoIdeal S m hpos notuniq).leOn y x := by
            have hiff := (restrictToCoIdeal S m hpos notuniq).le_iff_leOn_val
                            (x := ⟨y, by exact hyC⟩)
                            (y := ⟨x, by exact hBsubC hxB⟩)
            have h_restrict_le :
                (restrictToCoIdeal S m hpos notuniq).le
                  ⟨y, hyC⟩ ⟨x, hBsubC hxB⟩ :=
              build_restrict_le_C S m hpos notuniq
                (hyG := hyG)
                (hxG := hCsubG (hBsubC hxB))
                (hyC := hyC)
                (hxC := hBsubC hxB)
                (h := h_yx_Sle)

            have hiff :=
              (restrictToCoIdeal S m hpos notuniq).le_iff_leOn_val
                (x := ⟨y, hyC⟩) (y := ⟨x, hBsubC hxB⟩)

            have hyx_restrict_leOn :
                (restrictToCoIdeal S m hpos notuniq).leOn y x := by
              exact
                (leOn_iff (restrictToCoIdeal S m hpos notuniq) hyC (hBsubC hxB)).mpr h_restrict_le

            exact (leOn_iff (restrictToCoIdeal S m hpos notuniq) hyC (hBsubC hxB)).mpr h_restrict_le
          have hB_closed := (And.right hB)
          have : y ∈ B := hB_closed hxB hyC hyx_restrict_leOn
          exact Finset.mem_union.mpr (Or.inr this)

    exact And.intro hXsubG hdown

/-- edgeFinset の一致（これが NDS 等式には十分） -/
private lemma ideal_edgeFinset_eq_sumProd
  (S : FuncSetup α) (m : S.Elem) (hm : S.maximal m)
  (hpos : isPoset S) (notuniq : ¬ (∃! mm : S.Elem, S.maximal mm)) :
  let F  := S.idealFamily
  let F₁ := (restrictToIdeal S m hm).idealFamily
  let F₂ := (restrictToCoIdeal S m hpos notuniq).idealFamily
  F.edgeFinset = (SetFamily.sumProd F₁ F₂).edgeFinset := by
  classical
  intro F F₁ F₂
  ext X
  constructor
  · intro hX
    have hset : F.sets X :=
      (SetFamily.mem_edgeFinset_iff_sets (F := F) (A := X)).1 hX
    have hsum : (SetFamily.sumProd F₁ F₂).sets X :=
      (ideal_sets_iff_sumProd S m hm hpos notuniq).1 hset
    exact (SetFamily.mem_edgeFinset_iff_sets (F := SetFamily.sumProd F₁ F₂) (A := X)).2 hsum
  · intro hX
    have hset : (SetFamily.sumProd F₁ F₂).sets X :=
      (SetFamily.mem_edgeFinset_iff_sets (F := SetFamily.sumProd F₁ F₂) (A := X)).1 hX
    have hset' : F.sets X :=
      (ideal_sets_iff_sumProd S m hm hpos notuniq).2 hset
    exact (SetFamily.mem_edgeFinset_iff_sets (F := F) (A := X)).2 hset'

private lemma ideal_ground_eq_sumProd_ground
  (S : FuncSetup α) (m : S.Elem) (hm : S.maximal m)
  (hpos : isPoset S) (notuniq : ¬ (∃! mm : S.Elem, S.maximal mm)) :
  let F  := S.idealFamily
  let F₁ := (restrictToIdeal S m hm).idealFamily
  let F₂ := (restrictToCoIdeal S m hpos notuniq).idealFamily
  F.ground = (SetFamily.sumProd F₁ F₂).ground := by
  classical
  intro F F₁ F₂

  dsimp [SetFamily.sumProd]

  change S.ground
      = (restrictToIdeal S m hm).ground ∪ (restrictToCoIdeal S m hpos notuniq).ground
    at *

  exact Eq.symm (ground_union_split S m hm hpos notuniq)

--Called from MainStatement.leanか
theorem idealFamily_eq_sumProd_on_NDS
  (S : FuncSetup α) (m : S.Elem) (hm : S.maximal m)
  (hpos : isPoset S) (notuniq : ¬ (∃! mm : S.Elem, S.maximal mm)) :
  let F  := S.idealFamily
  let F₁ := (restrictToIdeal S m hm).idealFamily
  let F₂ := (restrictToCoIdeal S m hpos notuniq).idealFamily
  F.NDS = (SetFamily.sumProd F₁ F₂).NDS := by
  classical
  intro F F₁ F₂
  have hedge :
    F.edgeFinset = (SetFamily.sumProd F₁ F₂).edgeFinset :=
    ideal_edgeFinset_eq_sumProd S m hm hpos notuniq

  have hgr :
    F.ground = (SetFamily.sumProd F₁ F₂).ground :=
    ideal_ground_eq_sumProd_ground S m hm hpos notuniq

  have hnum :
    F.numHyperedges
      = (SetFamily.sumProd F₁ F₂).numHyperedges := by
    dsimp [SetFamily.numHyperedges]
    exact congrArg Finset.card hedge

  have htot :
    F.totalHyperedgeSize
      = (SetFamily.sumProd F₁ F₂).totalHyperedgeSize := by
    dsimp [SetFamily.totalHyperedgeSize]

    simp_all only [F, F₁, F₂]

  have hV :
    (F.ground.card : Int)
      = ((SetFamily.sumProd F₁ F₂).ground.card : Int) := by

    simp_all only [F, F₁, F₂]

  simp_all only [SetFamily.NDS_def, F, F₁, F₂]

--使っている。
omit [DecidableEq α] in
private lemma sum_const_nat (s : Finset α) (c : Nat) :
  ∑ _ ∈ s, c = s.card * c := by
  -- `sum_const` は `s.card • c` を返すので、`Nat.smul_def` で `*` に直す
  have := Finset.sum_const (c) (s := s)
  -- `∑ _∈s, c = s.card • c`
  have : (∑ _ ∈ s, c) = s.card • c := this
  -- `n • m = n * m` を適用
  calc
    (∑ _ ∈ s, c) = s.card • c := this
    _ = s.card * c := by exact rfl

---移すとしたらSetFamilyだが。下で使われている。
private lemma sum_card_union_add_inter_general
  (F₁ F₂ : SetFamily α) :
  (∑ A ∈ F₁.edgeFinset, ∑ B ∈ F₂.edgeFinset, (A ∪ B).card)
  +
  (∑ A ∈ F₁.edgeFinset, ∑ B ∈ F₂.edgeFinset, (A ∩ B).card)
  =
  (F₂.numHyperedges) * (∑ A ∈ F₁.edgeFinset, A.card)
  +
  (F₁.numHyperedges) * (∑ B ∈ F₂.edgeFinset, B.card) := by
  classical
  -- 各ペアで `|A∪B| + |A∩B| = |A| + |B|`
  have hAB :
    ∀ (A B : Finset α), (A ∪ B).card + (A ∩ B).card = A.card + B.card := by
    intro A B
    exact Finset.card_union_add_card_inter A B

  have hsum :
    (∑ A ∈ F₁.edgeFinset, ∑ B ∈ F₂.edgeFinset, (A ∪ B).card)
    +
    (∑ A ∈ F₁.edgeFinset, ∑ B ∈ F₂.edgeFinset, (A ∩ B).card)
    =
    (∑ A ∈ F₁.edgeFinset, ∑ B ∈ F₂.edgeFinset, (A.card + B.card)) := by

    calc
      (∑ A ∈ F₁.edgeFinset, ∑ B ∈ F₂.edgeFinset, (A ∪ B).card) + (∑ A ∈ F₁.edgeFinset, ∑ B ∈ F₂.edgeFinset, (A ∩ B).card)

        = ∑ A ∈ F₁.edgeFinset, ∑ B ∈ F₂.edgeFinset, ((A ∪ B).card + (A ∩ B).card) := by
              rw [← Finset.sum_add_distrib]
              apply Finset.sum_congr rfl
              exact fun x a => Eq.symm Finset.sum_add_distrib
      _ = ∑ A ∈ F₁.edgeFinset,
              (∑ B ∈ F₂.edgeFinset,
                  ((A ∪ B).card + (A ∩ B).card)) := by
                refine Finset.sum_congr rfl ?_
                intro A hA
                exact rfl
      _ = ∑ A ∈ F₁.edgeFinset,
              (∑ B ∈ F₂.edgeFinset, (A.card + B.card)) := by
                refine Finset.sum_congr rfl ?_
                intro A hA
                refine Finset.sum_congr rfl ?_
                intro B hB
                exact hAB A B

  have hsplit :
    ∑ A ∈ F₁.edgeFinset, ∑ B ∈ F₂.edgeFinset, (A.card + B.card)
    =
    (F₂.edgeFinset.card) * (∑ A ∈ F₁.edgeFinset, A.card)
    +
    (F₁.edgeFinset.card) * (∑ B ∈ F₂.edgeFinset, B.card) := by
    have hA :
      ∀ A ∈ F₁.edgeFinset,
        (∑ B ∈ F₂.edgeFinset, (A.card + B.card))
        =
        F₂.edgeFinset.card * A.card + (∑ B ∈ F₂.edgeFinset, B.card) := by
      intro A hA
      calc
        ∑ B ∈ F₂.edgeFinset, (A.card + B.card)
            = (∑ B ∈ F₂.edgeFinset, A.card)
              + (∑ B ∈ F₂.edgeFinset, B.card) := Finset.sum_add_distrib
        _ = F₂.edgeFinset.card * A.card
              + (∑ B ∈ F₂.edgeFinset, B.card) := by

              have := sum_const_nat (s := F₂.edgeFinset) (c := A.card)
              exact congrArg (fun t => t + (∑ B ∈ F₂.edgeFinset, B.card)) this
    calc
      ∑ A ∈ F₁.edgeFinset, ∑ B ∈ F₂.edgeFinset, (A.card + B.card)
          = ∑ A ∈ F₁.edgeFinset,
              (F₂.edgeFinset.card * A.card
               + ∑ B ∈ F₂.edgeFinset, B.card) := by
                refine Finset.sum_congr rfl ?_
                intro A hA
                (expose_names; exact hA_1 A hA)
      _ = (∑ A ∈ F₁.edgeFinset, F₂.edgeFinset.card * A.card)
          + (∑ A ∈ F₁.edgeFinset, ∑ B ∈ F₂.edgeFinset, B.card) := by
                exact Finset.sum_add_distrib
      _ = F₂.edgeFinset.card * (∑ A ∈ F₁.edgeFinset, A.card)
          + F₁.edgeFinset.card * (∑ B ∈ F₂.edgeFinset, B.card) := by
           simp_all only [SetFamily.mem_edgeFinset, and_imp, Finset.sum_const, smul_eq_mul, Nat.add_right_cancel_iff]
           rw [Finset.mul_sum]


  have eqn: (∑ A ∈ F₁.edgeFinset, ∑ B ∈ F₂.edgeFinset, (A ∪ B).card)  + (∑ A ∈ F₁.edgeFinset, ∑ B ∈ F₂.edgeFinset, (A ∩ B).card) = (F₂.edgeFinset.card) * (∑ A ∈ F₁.edgeFinset, A.card)+ (F₁.edgeFinset.card) * (∑ B ∈ F₂.edgeFinset, B.card) := by
    rw [hsum]

    rw [hsplit]

  exact eqn

-- 基本恒等式（減算形，Int 版）：
-- `(∑∑ |A∪B|) = (#F₂)*∑|A| + (#F₁)*∑|B| - (∑∑ |A∩B|)`。

private lemma sum_card_union_general_int
  (F₁ F₂ : SetFamily α) :
  ((∑ A ∈ F₁.edgeFinset, ∑ B ∈ F₂.edgeFinset, (A ∪ B).card) : Int)
  =
  (F₂.numHyperedges : Int) * (∑ A ∈ F₁.edgeFinset, (A.card : Int))
  +
  (F₁.numHyperedges : Int) * (∑ B ∈ F₂.edgeFinset, (B.card : Int))
  -
  (∑ A ∈ F₁.edgeFinset, ∑ B ∈ F₂.edgeFinset, (A ∩ B).card) := by
  classical
  have H :=
    sum_card_union_add_inter_general (F₁ := F₁) (F₂ := F₂)

  have := congrArg (fun n : Nat => (n : Int)) H

  clear H

  have Hℤ :
    ((∑ A ∈ F₁.edgeFinset, ∑ B ∈ F₂.edgeFinset, (A ∪ B).card) : Int)
    +
    (∑ A ∈ F₁.edgeFinset, ∑ B ∈ F₂.edgeFinset, (A ∩ B).card)
    =
    (F₂.numHyperedges : Int) * (∑ A ∈ F₁.edgeFinset, (A.card : Int))
    +
    (F₁.numHyperedges : Int) * (∑ B ∈ F₂.edgeFinset, (B.card : Int)) := by

    exact_mod_cast
      sum_card_union_add_inter_general (F₁ := F₁) (F₂ := F₂)

  have eqn := sub_eq_of_eq_add' (a := (∑ A ∈ F₁.edgeFinset, ∑ B ∈ F₂.edgeFinset, (A ∪ B).card : Int)+ (∑ A ∈ F₁.edgeFinset, ∑ B ∈ F₂.edgeFinset, (A ∩ B).card : Int))
          (b := (∑ A ∈ F₁.edgeFinset, ∑ B ∈ F₂.edgeFinset, (A ∩ B).card : Int))
          (c := (F₂.numHyperedges : Int) * (∑ A ∈ F₁.edgeFinset, (A.card : Int))
              + (F₁.numHyperedges : Int) * (∑ B ∈ F₂.edgeFinset, (B.card : Int))
              - (∑ A ∈ F₁.edgeFinset, ∑ B ∈ F₂.edgeFinset, (A ∩ B).card : Int))
  simp at eqn
  simp_all only [Nat.cast_add, Nat.cast_sum, Nat.cast_mul, sub_add_cancel, forall_const]


/-- 台集合が素に交わるとき、各エッジ対の交差は空。 -/
private lemma inter_card_zero_of_disjoint_ground
  (F₁ F₂ : SetFamily α) (hd : Disjoint F₁.ground F₂.ground)
  {A B : Finset α} (hA : A ∈ F₁.edgeFinset) (hB : B ∈ F₂.edgeFinset) :
  (A ∩ B).card = 0 := by
  classical
  -- A ⊆ ground₁, B ⊆ ground₂
  have hAset : F₁.sets A := (SetFamily.mem_edgeFinset_iff_sets (F := F₁) (A := A)).1 hA
  have hBset : F₂.sets B := (SetFamily.mem_edgeFinset_iff_sets (F := F₂) (A := B)).1 hB
  have hAsub : A ⊆ F₁.ground := F₁.inc_ground hAset
  have hBsub : B ⊆ F₂.ground := F₂.inc_ground hBset

  have hdisjAB : Disjoint A B := by
    refine Finset.disjoint_left.mpr ?_
    intro a haA haB
    have haG : a ∈ F₁.ground := hAsub haA
    have hbG : a ∈ F₂.ground := hBsub haB
    apply (Finset.disjoint_left.mp hd)
    exact hAsub haA
    exact hBsub haB

  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro a ha
  have hmem := Finset.mem_inter.mp ha
  apply (Finset.disjoint_left.mp hdisjAB)
  exact Finset.mem_of_mem_filter a ha
  simp_all only [SetFamily.mem_edgeFinset, and_self, Finset.mem_inter]

/-- 交差サイズの二重和は 0。 -/
private lemma sum_inter_card_eq_zero_of_disjoint_ground
  (F₁ F₂ : SetFamily α) (hd : Disjoint F₁.ground F₂.ground) :
  ∑ A ∈ F₁.edgeFinset, ∑ B ∈ F₂.edgeFinset, (A ∩ B).card = 0 := by
  classical

  have hcongrA :
      ∑ A ∈ F₁.edgeFinset, ∑ B ∈ F₂.edgeFinset, (A ∩ B).card
        = ∑ A ∈ F₁.edgeFinset, 0 := by
    refine Finset.sum_congr rfl ?_
    intro A hA
    have hcongrB :
        ∑ B ∈ F₂.edgeFinset, (A ∩ B).card
          = ∑ B ∈ F₂.edgeFinset, 0 := by
      refine Finset.sum_congr rfl ?_
      intro B hB
      exact inter_card_zero_of_disjoint_ground F₁ F₂ hd hA hB
    simp_all only [SetFamily.mem_edgeFinset, Finset.sum_const_zero, Finset.sum_eq_zero_iff, Finset.card_eq_zero, and_imp,
    Finset.card_empty, implies_true]

  have : ∑ A ∈ F₁.edgeFinset, 0 = 0 := Finset.sum_const_zero
  exact Eq.trans hcongrA this

/-- 【目的】台集合が素に交わるときの簡約版（Int 版）。 -/
private lemma sum_card_union_disjoint_int
  (F₁ F₂ : SetFamily α) (hd : Disjoint F₁.ground F₂.ground) :
  ((∑ A ∈ F₁.edgeFinset, ∑ B ∈ F₂.edgeFinset, (A ∪ B).card) : Int)
  =
  (F₂.numHyperedges : Int) * (∑ A ∈ F₁.edgeFinset, (A.card : Int))
  +
  (F₁.numHyperedges : Int) * (∑ B ∈ F₂.edgeFinset, (B.card : Int)) := by
  classical
  -- 一般式を使い、交差項 0 で簡約
  have H :=
    sum_card_union_general_int (F₁ := F₁) (F₂ := F₂)
  -- 交差二重和 = 0（Nat）→ Int へ
  have h0nat :
      ∑ A ∈ F₁.edgeFinset, ∑ B ∈ F₂.edgeFinset, (A ∩ B).card = 0 :=
    sum_inter_card_eq_zero_of_disjoint_ground F₁ F₂ hd
  have h0int :
      ((∑ A ∈ F₁.edgeFinset, ∑ B ∈ F₂.edgeFinset, (A ∩ B).card) : Int) = 0 := by
    exact_mod_cast h0nat
  -- 置換して `- 0` を消す
  calc
    ((∑ A ∈ F₁.edgeFinset, ∑ B ∈ F₂.edgeFinset, (A ∪ B).card) : Int)
        =
      (F₂.numHyperedges : Int) * (∑ A ∈ F₁.edgeFinset, (A.card : Int))
      + (F₁.numHyperedges : Int) * (∑ B ∈ F₂.edgeFinset, (B.card : Int))
      - ((∑ A ∈ F₁.edgeFinset, ∑ B ∈ F₂.edgeFinset, (A ∩ B).card) : Int) := by
        simp_all only [Nat.cast_zero, sub_zero, Finset.sum_eq_zero_iff, SetFamily.mem_edgeFinset, Finset.card_eq_zero, and_imp]
    _ =
      (F₂.numHyperedges : Int) * (∑ A ∈ F₁.edgeFinset, (A.card : Int))
      + (F₁.numHyperedges : Int) * (∑ B ∈ F₂.edgeFinset, (B.card : Int))
      - 0 := by
        exact congrArg
          (fun t =>
            (F₂.numHyperedges : Int) * (∑ A ∈ F₁.edgeFinset, (A.card : Int))
            + (F₁.numHyperedges : Int) * (∑ B ∈ F₂.edgeFinset, (B.card : Int))
            - t) h0int
    _ =
      (F₂.numHyperedges : Int) * (∑ A ∈ F₁.edgeFinset, (A.card : Int))
      + (F₁.numHyperedges : Int) * (∑ B ∈ F₂.edgeFinset, (B.card : Int)) := by
        exact sub_zero _

private lemma union_inj_on_edges_of_disjoint
  (F₁ F₂ : SetFamily α) (hd : Disjoint F₁.ground F₂.ground) :
  ∀ {p q : Finset α × Finset α},
    p ∈ F₁.edgeFinset.product F₂.edgeFinset →
    q ∈ F₁.edgeFinset.product F₂.edgeFinset →
    p.1 ∪ p.2 = q.1 ∪ q.2 → p = q := by
  classical
  intro p q hp hq hU
  rcases Finset.mem_product.mp hp with ⟨hp1, hp2⟩
  rcases Finset.mem_product.mp hq with ⟨hq1, hq2⟩
  -- A ⊆ ground₁, B ⊆ ground₂
  have hps1 : p.1 ⊆ F₁.ground :=
    F₁.inc_ground ((SetFamily.mem_edgeFinset_iff_sets (F := F₁)).1 hp1)
  have hps2 : p.2 ⊆ F₂.ground :=
    F₂.inc_ground ((SetFamily.mem_edgeFinset_iff_sets (F := F₂)).1 hp2)
  have hqs1 : q.1 ⊆ F₁.ground :=
    F₁.inc_ground ((SetFamily.mem_edgeFinset_iff_sets (F := F₁)).1 hq1)
  have hqs2 : q.2 ⊆ F₂.ground :=
    F₂.inc_ground ((SetFamily.mem_edgeFinset_iff_sets (F := F₂)).1 hq2)

  have hdis : Disjoint F₁.ground F₂.ground := hd

  have ext1 :
      (p.1 ∪ p.2) ∩ F₁.ground = p.1 := by
    apply Finset.ext
    intro a; constructor
    · intro ha
      rcases Finset.mem_inter.mp ha with ⟨hUmem, hG⟩
      rcases Finset.mem_union.mp hUmem with hmem | hmem
      · exact hmem
      ·
        have : a ∈ F₂.ground := hps2 hmem
        have : False := (Finset.disjoint_left.mp hdis) hG this
        exact this.elim
    · intro ha
      exact Finset.mem_inter.mpr ⟨Finset.mem_union.mpr (Or.inl ha), hps1 ha⟩
  have ext2 :
      (q.1 ∪ q.2) ∩ F₁.ground = q.1 := by
    apply Finset.ext
    intro a; constructor
    · intro ha
      rcases Finset.mem_inter.mp ha with ⟨hUmem, hG⟩
      rcases Finset.mem_union.mp hUmem with hmem | hmem
      · exact hmem
      · have : a ∈ F₂.ground := hqs2 hmem
        have : False := (Finset.disjoint_left.mp hdis) hG this
        exact this.elim
    · intro ha
      exact Finset.mem_inter.mpr ⟨Finset.mem_union.mpr (Or.inl ha), hqs1 ha⟩
  have hL : p.1 = q.1 := by
    have := congrArg (fun t => t ∩ F₁.ground) hU
    exact (by
      have := this
      exact Eq.trans (Eq.symm ext1) (Eq.trans this ext2))
  have ext1' :
      (p.1 ∪ p.2) ∩ F₂.ground = p.2 := by
    apply Finset.ext
    intro a; constructor
    · intro ha
      rcases Finset.mem_inter.mp ha with ⟨hUmem, hG⟩
      rcases Finset.mem_union.mp hUmem with hmem | hmem
      ·
        have : a ∈ F₁.ground := hps1 hmem
        have : False := (Finset.disjoint_left.mp hdis) this hG
        exact this.elim
      · exact hmem
    · intro ha
      exact Finset.mem_inter.mpr ⟨Finset.mem_union.mpr (Or.inr ha), hps2 ha⟩
  have ext2' :
      (q.1 ∪ q.2) ∩ F₂.ground = q.2 := by
    apply Finset.ext
    intro a; constructor
    · intro ha
      rcases Finset.mem_inter.mp ha with ⟨hUmem, hG⟩
      rcases Finset.mem_union.mp hUmem with hmem | hmem
      · have : a ∈ F₁.ground := hqs1 hmem
        have : False := (Finset.disjoint_left.mp hdis) this hG
        exact this.elim
      · exact hmem
    · intro ha
      exact Finset.mem_inter.mpr ⟨Finset.mem_union.mpr (Or.inr ha), hqs2 ha⟩
  have hR : p.2 = q.2 := by
    have := congrArg (fun t => t ∩ F₂.ground) hU
    exact (by
      exact Eq.trans (Eq.symm ext1') (Eq.trans this ext2'))
  cases p with
  | mk A B =>
    cases q with
    | mk C D =>
      cases hL; cases hR
      rfl

/-- 和積の総サイズ（Nat）：disjoint なら直積二重和に一致。 -/
private lemma total_size_sumProd_eq_doubleSum_disjoint_nat
  (F₁ F₂ : SetFamily α) (hd : Disjoint F₁.ground F₂.ground) :
  (SetFamily.sumProd F₁ F₂).totalHyperedgeSize
    =
  ∑ A ∈ F₁.edgeFinset, ∑ B ∈ F₂.edgeFinset, (A ∪ B).card := by
  classical
  have hedge :
    (SetFamily.sumProd F₁ F₂).edgeFinset
      =
      (F₁.edgeFinset.product F₂.edgeFinset).image
        (fun p : Finset α × Finset α => p.1 ∪ p.2) :=
    edgeFinset_sumProd F₁ F₂
  have hinj :
    ∀ {p q}, p ∈ F₁.edgeFinset.product F₂.edgeFinset →
             q ∈ F₁.edgeFinset.product F₂.edgeFinset →
             ((fun p : Finset α × Finset α => p.1 ∪ p.2) p
              =
              (fun p : Finset α × Finset α => p.1 ∪ p.2) q) → p = q :=
    union_inj_on_edges_of_disjoint F₁ F₂ hd
  calc
    (SetFamily.sumProd F₁ F₂).totalHyperedgeSize
        = ∑ X ∈ (SetFamily.sumProd F₁ F₂).edgeFinset, X.card := rfl
    _ = ∑ X ∈ (F₁.edgeFinset.product F₂.edgeFinset).image (fun p => p.1 ∪ p.2), X.card := by
          exact congrArg (fun t => ∑ X ∈ t, X.card) hedge
    _ = ∑ p ∈ (F₁.edgeFinset.product F₂.edgeFinset),
            ((p.1 ∪ p.2).card) := by
          exact Finset.sum_image fun ⦃x₁⦄ a ⦃x₂⦄ => hinj a
    _ = ∑ A ∈ F₁.edgeFinset, ∑ B ∈ F₂.edgeFinset, (A ∪ B).card := by
          simp_all only [Finset.product_eq_sprod, Finset.mem_product, SetFamily.mem_edgeFinset, and_imp, Prod.forall,
            Prod.mk.injEq, subset_refl]
          rw [Finset.sum_product]

/-- 和積の総サイズ（Int）：disjoint 版。 -/
private lemma total_size_sumProd_eq_doubleSum_disjoint_int
  (F₁ F₂ : SetFamily α) (hd : Disjoint F₁.ground F₂.ground) :
  ((SetFamily.sumProd F₁ F₂).totalHyperedgeSize : Int)
    =
  (∑ A ∈ F₁.edgeFinset, ∑ B ∈ F₂.edgeFinset, (A ∪ B).card : Nat) := by
  classical
  have hnat := total_size_sumProd_eq_doubleSum_disjoint_nat (F₁ := F₁) (F₂ := F₂) hd
  exact_mod_cast hnat

/-- NDS の分解式（台集合が素に交わるとき） -/
private lemma NDS_sumProd_of_disjoint
  (F₁ F₂ : SetFamily α) (hd : Disjoint F₁.ground F₂.ground) :
  (SetFamily.sumProd F₁ F₂).NDS
    =
    (F₂.numHyperedges : Int) * F₁.NDS
  + (F₁.numHyperedges : Int) * F₂.NDS  := by
  classical
  have hTot :
    ((SetFamily.sumProd F₁ F₂).totalHyperedgeSize : Int)
      =
    ((∑ A ∈ F₁.edgeFinset, ∑ B ∈ F₂.edgeFinset, (A ∪ B).card) : Int) := by

    let tss := total_size_sumProd_eq_doubleSum_disjoint_int (F₁ := F₁) (F₂ := F₂) hd
    rw [tss]
    simp_all only [Nat.cast_sum]

  have hSize :=
    sum_card_union_disjoint_int (F₁ := F₁) (F₂ := F₂) hd
  have hV :
    ((SetFamily.sumProd F₁ F₂).ground.card : Int)
      =
    (F₁.ground.card : Int) + (F₂.ground.card : Int) := by
    -- `sumProd.ground = F₁.ground ∪ F₂.ground`
    have : (SetFamily.sumProd F₁ F₂).ground
              = F₁.ground ∪ F₂.ground := rfl
    have hdis : (F₁.ground ∩ F₂.ground).card = 0 := by
      apply Finset.card_eq_zero.mpr
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro a ha
      rcases Finset.mem_inter.mp ha with ⟨ha1, ha2⟩
      exact (Finset.disjoint_left.mp hd) ha1 ha2
    have := Finset.card_union_add_card_inter (F₁.ground) (F₂.ground)

    have hInt :
      ((F₁.ground ∪ F₂.ground).card : Int)
        =
      (F₁.ground.card : Int) + (F₂.ground.card : Int) := by

      have := this

      have := sub_eq_of_eq_add' (a :=
        ((F₁.ground ∪ F₂.ground).card : Int))
        (b := (F₁.ground.card : Int) + (F₂.ground.card : Int))
        (c := ((F₁.ground ∩ F₂.ground).card : Int))
        (by simp_all only [Finset.card_eq_zero, Finset.card_union_of_disjoint, Finset.card_empty, add_zero, Nat.cast_add, Nat.cast_zero])

      have hc : ((F₁.ground ∩ F₂.ground).card : Int) = 0 := by
        exact_mod_cast hdis

      exact (by
        -- `(u∪v).card = (u.card+v.card) - 0`
        exact congrArg (fun t => t) (by

          have := this

          simp_all only [Finset.card_eq_zero, Finset.card_union_of_disjoint, Finset.card_empty, add_zero,Nat.cast_add, sub_self, Nat.cast_zero]))    -- 最後に `sumProd.ground = _` を使って置き換え
    simp_all only [Finset.card_eq_zero, Finset.card_union_of_disjoint, Finset.card_empty, add_zero, Nat.cast_add]

  have hH :
    ((SetFamily.sumProd F₁ F₂).numHyperedges : Int)
      = (F₁.numHyperedges * F₂.numHyperedges : Nat) := by

    have hedge :=
      edgeFinset_sumProd F₁ F₂
    have hinj :
      ∀ {p q}, p ∈ F₁.edgeFinset.product F₂.edgeFinset →
               q ∈ F₁.edgeFinset.product F₂.edgeFinset →
               ((fun p : Finset α × Finset α => p.1 ∪ p.2) p
                =
                (fun p : Finset α × Finset α => p.1 ∪ p.2) q) → p = q :=
      union_inj_on_edges_of_disjoint F₁ F₂ hd

    have hcard :
      (SetFamily.sumProd F₁ F₂).edgeFinset.card
        = (F₁.edgeFinset.product F₂.edgeFinset).card := by
      calc
        (SetFamily.sumProd F₁ F₂).edgeFinset.card
            = ((F₁.edgeFinset.product F₂.edgeFinset).image (fun p => p.1 ∪ p.2)).card := by
              exact congrArg Finset.card hedge
        _ = (F₁.edgeFinset.product F₂.edgeFinset).card := by
              exact Finset.card_image_iff.mpr (by
                intro p hp q hq hEq
                exact hinj hp hq hEq)

    have := Finset.card_product (F₁.edgeFinset) (F₂.edgeFinset)

    exact (by

      have hn :
        (SetFamily.sumProd F₁ F₂).numHyperedges
          = F₁.edgeFinset.card * F₂.edgeFinset.card := by

          exact Eq.trans (by rfl) (by
            exact Eq.trans hcard this)

      exact_mod_cast hn)

  set e₁ := F₁.numHyperedges
  set e₂ := F₂.numHyperedges
  set v₁ := F₁.ground.card
  set v₂ := F₂.ground.card

  unfold SetFamily.NDS

  have hTot' :
    (2 * ((SetFamily.sumProd F₁ F₂).totalHyperedgeSize : Int))
      =
    2 *
      ((∑ A ∈ F₁.edgeFinset, ∑ B ∈ F₂.edgeFinset, (A ∪ B).card) : Int) := by
    exact congrArg (fun t : Int => 2 * t) hTot

  have hSize' :
    2 *
      ((∑ A ∈ F₁.edgeFinset, ∑ B ∈ F₂.edgeFinset, (A ∪ B).card) : Int)
      =
    2 * ((e₂ : Int) * (∑ A ∈ F₁.edgeFinset, (A.card : Int))
        + (e₁ : Int) * (∑ B ∈ F₂.edgeFinset, (B.card : Int))) := by

    exact congrArg (fun t : Int => 2 * t) hSize

  have hV' :
    ((SetFamily.sumProd F₁ F₂).ground.card : Int)
      = (v₁ : Int) + (v₂ : Int) := hV

  calc
    2 * ((SetFamily.sumProd F₁ F₂).totalHyperedgeSize : Int)
      - ((SetFamily.sumProd F₁ F₂).numHyperedges : Int)
        * ((SetFamily.sumProd F₁ F₂).ground.card : Int)
      = (2 *
          ((∑ A ∈ F₁.edgeFinset, ∑ B ∈ F₂.edgeFinset, (A ∪ B).card) : Int))
        - ((e₁ * e₂ : Nat) : Int) * ((v₁ + v₂ : Nat) : Int) := by
          have := hTot'
          have := hH
          have := hV'
          simp_all only [Nat.cast_mul, Nat.cast_add, e₂, e₁, v₁, v₂]
    _ = (2 * ((e₂ : Int) * (∑ A ∈ F₁.edgeFinset, (A.card : Int))
              + (e₁ : Int) * (∑ B ∈ F₂.edgeFinset, (B.card : Int))))
        - ((e₁ : Int) * (e₂ : Int)) * ((v₁ : Int) + (v₂ : Int)) := by
          simp_all only [Nat.cast_mul, Nat.cast_add, e₂, e₁, v₁, v₂]
    _ =
      (e₂ : Int) * (2 * (∑ A ∈ F₁.edgeFinset, (A.card : Int)))
      + (e₁ : Int) * (2 * (∑ B ∈ F₂.edgeFinset, (B.card : Int)))
      - ((e₁ : Int) * (e₂ : Int)) * ((v₁ : Int) + (v₂ : Int)) := by

          simp_all only [Nat.cast_mul, sub_left_inj, e₂, e₁, v₁, v₂]
          rw [mul_add]
          ac_rfl
    _ =
      (e₂ : Int) * (2 * (∑ A ∈ F₁.edgeFinset, (A.card : Int)) - (e₁ : Int) * (v₁ : Int))
      + (e₁ : Int) * (2 * (∑ B ∈ F₂.edgeFinset, (B.card : Int)) - (e₂ : Int) * (v₂ : Int)) := by
          ring_nf

    _ =
      (F₂.numHyperedges : Int) * F₁.NDS
      + (F₁.numHyperedges : Int) * F₂.NDS := by
          simp_all only [Nat.cast_mul, e₂, e₁, v₁, v₂]
          simp_all only [SetFamily.NDS_def]
          norm_cast

/-- principal と coIdeal の台集合は素に交わる。 -/
private lemma disjoint_principal_coIdeal (S : FuncSetup α) (m : S.Elem) :
  Disjoint (S.principalIdeal m.1 m.2) (coIdeal S m) := by
  classical
  unfold coIdeal
  exact Finset.disjoint_sdiff

/-- `restrictToIdeal` と `restrictToCoIdeal` の NDS 分解。 -/
--called from MainStatement.lean
theorem NDS_restrict_sumProd_split
  (S : FuncSetup α) (m : S.Elem) (hm : S.maximal m)
  (hpos : isPoset S) (notuniq : ¬ (∃! mm : S.Elem, S.maximal mm)) :
  let F₁ := (restrictToIdeal S m hm).idealFamily
  let F₂ := (restrictToCoIdeal S m hpos notuniq).idealFamily
  (SetFamily.sumProd F₁ F₂).NDS
    =
  (F₂.numHyperedges : Int) * F₁.NDS
  + (F₁.numHyperedges : Int) * F₂.NDS := by
  classical
  intro F₁ F₂
  have hd :
    Disjoint F₁.ground F₂.ground := by
    -- ground(F₁)=principal, ground(F₂)=coIdeal
    change Disjoint (S.principalIdeal m.1 m.2) (coIdeal S m)
    exact disjoint_principal_coIdeal S m
  exact NDS_sumProd_of_disjoint F₁ F₂ hd

end SumProduct
end AvgRare
