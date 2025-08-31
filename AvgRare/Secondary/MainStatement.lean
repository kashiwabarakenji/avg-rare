import AvgRare.Functional.FuncSetup
import AvgRare.Basics.SetFamily
import AvgRare.Basics.SetTrace
import AvgRare.Reductions.Reduction
import AvgRare.Secondary.SumProduct
import AvgRare.Secondary.UniqueMax

set_option maxHeartbeats 100000000

universe u

namespace AvgRare
namespace MainStatement
open Classical
open FuncSetup

variable {α : Type u} [DecidableEq α]

open scoped BigOperators

-- base base for induction --
/-- `edgeFinset ⊆ powerset` -/
lemma edge_subset_powerset (F : SetFamily α) :
  F.edgeFinset ⊆ F.ground.powerset := by
  intro A hA
  rcases Finset.mem_filter.mp hA with ⟨hPow, _⟩
  exact hPow

lemma powerset_singleton (x : α) :
  ({x} : Finset α).powerset = ({∅, {x}} : Finset (Finset α)) := by
  apply Finset.ext
  intro A
  constructor
  ·
    intro hA
    have hsub : A ⊆ ({x} : Finset α) := (Finset.mem_powerset.mp hA)
    by_cases hxA : x ∈ A
    · -- A = {x}
      have h_eq : A = ({x} : Finset α) := by
        apply Finset.eq_singleton_iff_unique_mem.mpr
        constructor
        · exact hxA
        · intro y hy
          have : y ∈ ({x} : Finset α) := hsub hy
          exact (Finset.mem_singleton.mp this)
      simp [h_eq]
    · -- x ∉ A → A = ∅
      have h_empty : A = (∅ : Finset α) := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro y hy
        have : y ∈ ({x} : Finset α) := hsub hy
        have : y = x := Finset.mem_singleton.mp this
        have hxInA : x ∈ A := by
          cases this
          exact hy
        exact hxA hxInA

      simp [h_empty]
  ·
    intro h

    have h' : A = (∅ : Finset α) ∨ A = ({x} : Finset α) := by
      rcases (Finset.mem_insert.mp h) with h0 | h1
      · exact Or.inl h0
      · exact Or.inr (Finset.mem_singleton.mp h1)
    apply (Finset.mem_powerset.mpr)
    cases h' with
    | inl h0 =>
        intro y hy
        have : y ∈ (∅ : Finset α) := by
          subst h0
          simp_all only [Finset.mem_insert, Finset.mem_singleton, true_or, Finset.notMem_empty]
        exact (False.elim (by simp_all only [Finset.mem_insert, Finset.mem_singleton, true_or, Finset.notMem_empty]))
    | inr h1 =>
        intro y hy
        simpa [h1] using hy

/-- If the size of the ground set is 1, `edgeFinset = {∅, ground}` -/
lemma edgeFinset_of_card_one
  (S : FuncSetup α)
  (hS : (S.idealFamily).ground.card = 1) :
  (S.idealFamily).edgeFinset
    = ({∅, (S.idealFamily).ground} : Finset (Finset α)) := by
  obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hS
  have hp :
    (S.idealFamily).ground.powerset
      = ({∅, {x}} : Finset (Finset α)) := by

    calc
      (S.idealFamily).ground.powerset
          = (({x} : Finset α)).powerset := by
            simp [hx]
      _ = ({∅, {x}} : Finset (Finset α)) := powerset_singleton x
  apply Finset.ext
  intro A
  constructor
  ·
    intro hA

    have hPow : A ∈ (S.idealFamily).ground.powerset :=
      (edge_subset_powerset (F := S.idealFamily)) hA
    have : A ∈ ({∅, {x}} : Finset (Finset α)) := by
      simpa [hp]
        using hPow
    simpa [hx]
      using this
  ·
    intro hA

    have hA' : A ∈ ({∅, {x}} : Finset (Finset α)) := by
      simpa [hx] using hA
    have hPow : A ∈ (S.idealFamily).ground.powerset := by

      simpa [hp]
        using hA'

    have hEq : A = (∅ : Finset α) ∨ A = (S.idealFamily).ground := by

      rcases (Finset.mem_insert.mp hA) with h0 | h1
      · exact Or.inl h0
      · exact Or.inr (Finset.mem_singleton.mp h1)
    cases hEq with
    | inl h0 =>

        have : (∅ : Finset α) ∈ (S.idealFamily).edgeFinset :=
          FuncSetup.empty_mem_ideal_edge S

        exact h0 ▸ this
    | inr h1 =>
        have : (S.idealFamily).ground ∈ (S.idealFamily).edgeFinset :=
          FuncSetup.ground_mem_ideal_edge S
        exact h1 ▸ this

/-- When the size is 1, `totalHyperedgeSize = 1`，`numHyperedges = 2` -/
lemma sizes_of_card_one
  (S : FuncSetup α)
  (hS : (S.idealFamily).ground.card = 1) :
  (S.idealFamily).totalHyperedgeSize = 1
  ∧ (S.idealFamily).numHyperedges = 2 := by
  -- edgeFinset = {∅, ground}
  have hE :
    (S.idealFamily).edgeFinset
      = ({∅, (S.idealFamily).ground} : Finset (Finset α)) :=
    edgeFinset_of_card_one (S := S) hS

  have hne : (S.idealFamily).ground ≠ (∅ : Finset α) := by
    intro h
    have : (S.idealFamily).ground.card = 0 := by
      simp [h]
    exact Nat.one_ne_zero (by simp_all only [Finset.card_empty, zero_ne_one])
  constructor
  ·
    have : (S.idealFamily).totalHyperedgeSize
        = ∑ A ∈ ({∅, (S.idealFamily).ground} : Finset (Finset α)), A.card := by
      change
        (∑ A ∈ (S.idealFamily).edgeFinset, A.card)
          = _

      simp [hE]
    have := this

    have hsum :
      ∑ A ∈ ({∅, (S.idealFamily).ground} : Finset (Finset α)), A.card = 1 := by
      have hne' : (∅ : Finset α) ≠ (S.idealFamily).ground := by
        exact ne_comm.mp hne
      simp [hne', hS]

    have : (S.idealFamily).totalHyperedgeSize
        = ∑ A ∈ ({∅, (S.idealFamily).ground} : Finset (Finset α)), A.card := this

    simpa [this] using hsum
  ·
    have : (S.idealFamily).numHyperedges
        = ({∅, (S.idealFamily).ground} : Finset (Finset α)).card := by
      change (S.idealFamily).edgeFinset.card = _
      simp [hE]

    have hcard :
      ({∅, (S.idealFamily).ground} : Finset (Finset α)).card = 2 := by
      have hne' : (∅ : Finset α) ≠ (S.idealFamily).ground := by
        exact ne_comm.mp hne
      simp [hne']

    simp [this, hcard]

/-- When the size is 1, NDS = 0 -/
lemma main_base_case
  (S : FuncSetup α)
  (hS : (S.idealFamily).ground.card = 1) :
  (S.idealFamily).NDS = 0 := by
  obtain ⟨hSize, hNum⟩ := sizes_of_card_one (S := S) hS
  simp [SetFamily.NDS, hSize, hNum, hS]

----------------------------------

--- inductive step

private lemma antisymm_restrictToIdeal_of_isPoset
  (S : FuncSetup α) (hpos : isPoset S) (m : S.Elem) (hm : S.maximal m) :
  ∀ {u v : (SumProduct.restrictToIdeal S m hm).Elem},
    (SumProduct.restrictToIdeal S m hm).le u v →
    (SumProduct.restrictToIdeal S m hm).le v u →
    u = v := by
  classical
  intro u v huv hvu
  have : S.le (SumProduct.liftFromIdeal S m hm u) (SumProduct.liftFromIdeal S m hm v) :=
    SumProduct.le_lift_Ideal S m hm huv
  have : (S.le (SumProduct.liftFromIdeal S m hm u) (SumProduct.liftFromIdeal S m hm v))
       ∧ (S.le (SumProduct.liftFromIdeal S m hm v) (SumProduct.liftFromIdeal S m hm u)) := by
    exact ⟨this, SumProduct.le_lift_Ideal S m hm hvu⟩
  rcases this with ⟨h₁, h₂⟩
  have h_eqS : SumProduct.liftFromIdeal S m hm u = SumProduct.liftFromIdeal S m hm v := by
    exact hpos this h₂
  have : u.1 = v.1 :=by
    simp_all only [le_iff_leOn_val]
    injection h_eqS

  exact Subtype.ext this

private lemma antisymm_restrictToCoIdeal_of_isPoset
  (S : FuncSetup α) (hpos : isPoset S) (m : S.Elem)
  (notuniq : ¬∃! mm, S.maximal mm) :
  ∀ {u v : (SumProduct.restrictToCoIdeal S m hpos notuniq).Elem},
    (SumProduct.restrictToCoIdeal S m hpos notuniq).le u v →
    (SumProduct.restrictToCoIdeal S m hpos notuniq).le v u →
    u = v := by
  classical
  intro u v huv hvu
  have h₁ : S.le (SumProduct.liftFromCoIdeal S m hpos notuniq u) (SumProduct.liftFromCoIdeal S m hpos notuniq v) :=
    SumProduct.le_lift_CoIdeal S m hpos notuniq huv
  have h₂ : S.le (SumProduct.liftFromCoIdeal S m hpos notuniq v) (SumProduct.liftFromCoIdeal S m hpos notuniq u) :=
    SumProduct.le_lift_CoIdeal S m hpos notuniq hvu
  have h_eqS :
      SumProduct.liftFromCoIdeal S m hpos notuniq u
    = SumProduct.liftFromCoIdeal S m hpos notuniq v := by
    exact hpos h₁ h₂

  have : u.1 = v.1 := by
    apply congrArg Subtype.val
    simp_all only [le_iff_leOn_val]
    injection h_eqS
    (expose_names; exact Subtype.eq val_eq)
  exact Subtype.ext this

/-- `posetTraceOfUnique` keeps `isPoset` -/

private lemma isPoset_posetTraceOfUnique
  (S : FuncSetup α) [Fintype S.Elem] (geq2: S.ground.card ≥ 2)
  (hpos : isPoset S) (hexu : ∃! m : S.Elem, S.maximal m) :
  isPoset (UniqueMax.posetTraceOfUnique S geq2 hexu ) := by
  classical
  have hm : S.maximal (Classical.choose hexu.exists) := Classical.choose_spec hexu.exists
  dsimp [UniqueMax.posetTraceOfUnique]
  have pos': S.isPoset_excess := by
    exact S.isPoset_of_le_antisymm hpos
  let ipt := UniqueMax.isPoset_posetTraceCore S hpos (m := Classical.choose hexu.exists)
  exact @ipt geq2

-- Secondary main theorem
theorem secondary_main_theorem
  (S : FuncSetup α) [Fintype S.Elem]
  (hpos : isPoset S) :
  (S.idealFamily).NDS ≤ 0 := by

  classical

  have main :
    ∀ n : Nat,
      ∀ (T : FuncSetup α) [Fintype T.Elem],
        isPoset T → T.ground.card = n → (T.idealFamily).NDS ≤ 0 :=
    fun n =>
      Nat.strongRecOn n
        (motive := fun n =>
          ∀ (T : FuncSetup α) [Fintype T.Elem],
            isPoset T → T.ground.card = n → (T.idealFamily).NDS ≤ 0)
        (fun n ih T _ hposT hcard => by
            by_cases h1 : T.ground.card = 1
            · have : (T.idealFamily).ground.card = 1 := by
                exact h1
              have h0 : (T.idealFamily).NDS = 0 :=
                main_base_case (S := T) this
              exact (by
                have := h0
                calc
                  (T.idealFamily).NDS = 0 := this
                  _ ≤ 0 := le_rfl)

            · have hn : T.ground.card = n := hcard
              have hposCard : 0 < T.ground.card := by
                have : T.ground.Nonempty := by
                  let nt := T.nonempty
                  exact Finset.nonempty_coe_sort.mp nt
                exact Finset.card_pos.mpr this
              have hge1 : 1 ≤ T.ground.card := Nat.succ_le_of_lt hposCard
              have hgt1 : 1 < T.ground.card := lt_of_le_of_ne hge1 (by symm; exact h1)
              have hge2 : 2 ≤ T.ground.card := Nat.succ_le_of_lt hgt1
              by_cases hexu : ∃! m : T.Elem, T.maximal m
              ·
                let T' := UniqueMax.posetTraceOfUnique T hge2 hexu
                have hpos' : isPoset T' :=
                  isPoset_posetTraceOfUnique (S := T) (geq2 := hge2)
                    (hpos := hposT) (hexu := hexu)
                have hdec : T'.ground.card = T.ground.card - 1 :=
                  UniqueMax.ground_card_after_trace_of_max (S := T)
                    (m := Classical.choose hexu.exists) (geq2 := hge2)
                -- `T'.ground.card < n`
                have hlt : T'.ground.card < n := by
                  have : T'.ground.card = n - 1 := by
                    simpa [hn] using hdec
                  have : T'.ground.card < n := by
                    simp [this]
                    exact Nat.lt_of_lt_of_eq hposCard hcard
                  exact this

                have hNDS_T' : (T'.idealFamily).NDS ≤ 0 := by
                  simp_all only [SetFamily.NDS_def, tsub_le_iff_right, zero_add, tsub_lt_self_iff,
                    Nat.lt_add_one, and_self, T']
                  apply ih
                  on_goal 2 => { simp_all only
                  }
                  on_goal 2 => {
                    simp_all only
                    rfl
                  }
                  · simp_all only [tsub_lt_self_iff, Nat.lt_add_one, and_self]

                have hmono :
                (T.idealFamily).NDS ≤ (T'.idealFamily).NDS :=
                  UniqueMax.nds_trace_nondecreasing_uniqueMax
                  (S := T) (geq2 := hge2) (hpos := hposT) (hexu := hexu)

                exact le_trans hmono hNDS_T'

              ·

                have hexu: (¬∃! mm, T.maximal mm) := by
                  intro h
                  exact hexu (by exact h)

                have hne : T.ground.Nonempty := by exact Finset.card_pos.mp hposCard--T.nonempty
                obtain ⟨m, hm⟩ :=
                  FuncSetup.exists_maximal_of_finite (S := T) (hpos := hposT) (hne := hne)

                let T₁ := SumProduct.restrictToIdeal T m hm
                let T₂ := SumProduct.restrictToCoIdeal T m hposT-- (notuniq := by exact hexu)

                have hlt₁ :
                  T₁.ground.card < T.ground.card :=
                  SumProduct.restrictToIdeal_card_lt_of_not_unique
                    (S := T) (m := m) (hm := hm) (hpos := hposT) (notconnected := by exact hexu)
                have hlt₂ :
                  (T₂ hexu).ground.card < T.ground.card :=
                  SumProduct.restrictToCoIdeal_card_lt
                    (S := T) (m := m) (hpos := hposT) (notconnected := by exact hexu)

                have hpos₁ : isPoset T₁ := (antisymm_restrictToIdeal_of_isPoset (S := T) hposT m hm)
                have hpos₂ : isPoset (T₂ hexu):=  (antisymm_restrictToCoIdeal_of_isPoset (S := T) hposT m (notuniq := by exact hexu))

                have hcard1: T₁.ground.card < n := by
                  subst hcard
                  simp_all only [Finset.card_pos, Finset.one_le_card, maximal_iff, le_iff_leOn_val, Subtype.forall, SetFamily.NDS_def,
                    tsub_le_iff_right, zero_add, T₁, T₂]
                have isPoset1 : isPoset T₁ := by
                   simp_all only [ maximal_iff, le_iff_leOn_val, Subtype.forall, SetFamily.NDS_def,
                  tsub_le_iff_right, zero_add, T₁, T₂]
                have hNDS₁ : (T₁.idealFamily).NDS ≤ 0 := by
                  exact ih T₁.ground.card hcard1 T₁ isPoset1 rfl
                have hNDS₂ : ((T₂ hexu).idealFamily).NDS ≤ 0 :=
                  ih (T₂ hexu).ground.card
                    (by simpa [hn] using hlt₂) (T₂ hexu) (by
                      simp_all only [ maximal_iff, le_iff_leOn_val, Subtype.forall, SetFamily.NDS_def,
                      tsub_le_iff_right, zero_add, T₁, T₂]
                    ) rfl

                let F₁ := (T₁.idealFamily)
                let F₂ := ((T₂ hexu).idealFamily)

                have hEdges :
                  (SetFamily.sumProd F₁ F₂).edgeFinset
                    =
                    (F₁.edgeFinset.product F₂.edgeFinset).image
                      (fun p : Finset α × Finset α => p.1 ∪ p.2) :=
                  SumProduct.edgeFinset_sumProd F₁ F₂

                have hNDS_congr :
                (T.idealFamily).NDS
                  =
                (SetFamily.sumProd (T₁.idealFamily) ((T₂ hexu).idealFamily)).NDS :=
                 SumProduct.idealFamily_eq_sumProd_on_NDS
                  (S := T) (m := m) (hm := hm) (hpos := hposT) (notuniq := by exact hexu)

                have hProd :
                  (SetFamily.sumProd F₁ F₂).NDS
                    =
                  (F₂.numHyperedges : Int) * F₁.NDS
                  + (F₁.numHyperedges : Int) * F₂.NDS :=
                    SumProduct.NDS_restrict_sumProd_split (S := T) (m := m) (hm := hm)
                    (hpos := hposT) (notuniq := by exact hexu)

                have hcoef₁ : 0 ≤ (((T₂ hexu).idealFamily).numHyperedges:Int) := by
                  exact Int.natCast_nonneg (T₂ hexu).idealFamily.numHyperedges
                have hcoef₂ : 0 ≤ ((T₁.idealFamily).numHyperedges:Int) := by
                  exact Int.natCast_nonneg T₁.idealFamily.numHyperedges

                have hrhs_le :
                  ((T₂ hexu).idealFamily).numHyperedges * (T₁.idealFamily).NDS
                  + (T₁.idealFamily).numHyperedges * ((T₂ hexu).idealFamily).NDS ≤ 0 := by
                  have h1' :
                    (((T₂ hexu).idealFamily).numHyperedges:Int) * (T₁.idealFamily).NDS ≤ 0 := by

                      exact Int.mul_nonpos_of_nonneg_of_nonpos hcoef₁ hNDS₁
                  have h2' :
                    ((T₁.idealFamily).numHyperedges:Int) * ((T₂ hexu).idealFamily).NDS ≤ 0 := by
                     exact Int.mul_nonpos_of_nonneg_of_nonpos hcoef₂ hNDS₂
                  exact Int.add_nonpos h1' h2'

                calc
                  (T.idealFamily).NDS
                      --= (SetFamily.sumProd F₁ F₂).NDS := by exact hEdges
                      = ((T₂ hexu).idealFamily).numHyperedges * (T₁.idealFamily).NDS
                        + (T₁.idealFamily).numHyperedges * ((T₂ hexu).idealFamily).NDS := Eq.trans hNDS_congr hProd
                  _ ≤ 0 := by exact hrhs_le
        )

  exact main S.ground.card S (by simp_all only [SetFamily.NDS_def, tsub_le_iff_right, zero_add]) rfl

/- The main theorem (statement)：
    the preorder induced by `f : V → V` has non-positive NDS. -/
theorem main_nds_nonpos {α : Type u} [DecidableEq α]
  (S : FuncSetup α) :
  (S.idealFamily).NDS ≤ 0 := by
  apply Reduction.main_nds_nonpos_of_secondary
  intro T hT
  have hT' : isPoset T := by
    dsimp [isPoset]
    dsimp [has_le_antisymm]
    exact T.antisymm_of_isPoset hT
  exact secondary_main_theorem T hT'

end MainStatement
end AvgRare
