import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import AvgRare.Basics.SetFamily
import AvgRare.Basics.SetTrace
import AvgRare.Functional.FuncSetup

--Proof of the Rareness of the Maximal Element.
--SetFamily framework could also be shown here, but for simplicity, it is shown here in the FuncSetup framework.

universe u

namespace AvgRare
namespace Reduction

open scoped BigOperators
open Classical

variable {α : Type u} [DecidableEq α]

/-- Rare：Expressed as a natural number inequality (by multiplying both sides) `deg(x) ≤ |E|/2`. -/
def Rare (F : SetFamily α) (x : α) : Prop :=
  2 * F.degree x ≤ F.numHyperedges

--すぐ下で使っている。FuncSetupは使ってない。
--SetFamily.leanに移動でもよいがこのファイルはRare関連のファイルなのでここに置く。
private lemma two_deg_le_num_int_of_Rare
    (F : SetFamily α) (x : α) (hR : Rare F x) :
    (2 * (F.degree x : Int) ≤ (F.numHyperedges : Int)) := by
  -- Nat の不等式を Int に持ち上げる
  -- Int.ofNat_le.mpr : m ≤ n → (m : ℤ) ≤ (n : ℤ)
  have : Int.ofNat (2 * F.degree x) ≤ Int.ofNat F.numHyperedges :=
    Int.ofNat_le.mpr hR
  -- 表記を (· : Int) に戻す
  exact this

--Rareの定義をIntに書き直したもの。
--ReductionからNDSの証明で使っている。
lemma diff_term_nonpos_of_Rare
    (F : SetFamily α) (x : α) (hR : Rare F x) :
    2 * (F.degree x : Int) - (F.numHyperedges : Int) ≤ 0 := by
  -- a - b ≤ 0 ↔ a ≤ b
  have hx : (2 * (F.degree x : Int) ≤ (F.numHyperedges : Int)) :=
    two_deg_le_num_int_of_Rare (F := F) (x := x) hR
  -- `sub_nonpos.mpr` は「a ≤ b」を「a - b ≤ 0」にする
  exact Int.sub_nonpos_of_le hx

private lemma ideal_diff_simClass_is_ideal
    (S : FuncSetup α)
    {u : S.Elem} {I : Finset α}
    (hmax : S.maximal u)
    (hI : (S.idealFamily).sets I) --(huI : u.1 ∈ I)
    :
    (S.idealFamily).sets (I \ S.simClass u) ∧ u.1 ∉ (I \ S.simClass u) := by
  classical
  have hIdeal : SetFamily.isOrderIdealOn (S.leOn) S.ground I := by
    change SetFamily.isOrderIdealOn (S.leOn) S.ground I
    exact (S.sets_iff_isOrderIdeal).1 hI
  have hSub : (I \ S.simClass u) ⊆ S.ground := by
    intro x hx
    have hxI_and_hxNotU := (Finset.mem_sdiff).1 hx
    have hxI : x ∈ I := hxI_and_hxNotU.1
    have hI_sub : I ⊆ S.ground := hIdeal.1
    exact hI_sub hxI
  have hDown :
      ∀ ⦃x⦄, x ∈ (I \ S.simClass u) →
      ∀ ⦃y⦄, y ∈ S.ground →
      S.leOn y x → y ∈ (I \ S.simClass u) := by
    intro x hx y hy h_yx
    have hxI_and_hxNotU := (Finset.mem_sdiff).1 hx
    have hxI    : x ∈ I := hxI_and_hxNotU.1
    have hxNotU : x ∉ S.simClass u := hxI_and_hxNotU.2
    have hyI : y ∈ I := by
      have hyx : S.leOn y x := h_yx
      exact hIdeal.2 (x := x) hxI (y := y) hy hyx
    have hyNotU : y ∉ S.simClass u := by
      intro hyU
      have hySim : S.sim ⟨y, hy⟩ u := by
        rcases (S.mem_simClass_iff u).1 hyU with ⟨hyV, hsim⟩

        exact hsim
      have hxV : x ∈ S.ground := (hIdeal.1) hxI
      have hyx_le : S.le ⟨y, hy⟩ ⟨x, hxV⟩ := by
        have hx' : S.leOn y x ↔ S.le ⟨y, hy⟩ ⟨x, hxV⟩ :=
          S.leOn_iff_subtype (a := y) (b := x) hy hxV
        exact hx'.1 h_yx

      have hxu_sim : S.sim ⟨x, hxV⟩ u :=
        S.sim_of_maximal_above_class (u := u) (x := ⟨x, hxV⟩) (y := ⟨y, hy⟩)
          hmax hySim hyx_le
      have hxU : x ∈ S.simClass u := by
        have : ∃ (hxg : x ∈ S.ground), S.sim ⟨x, hxg⟩ u := by
          exact ⟨hxV, hxu_sim⟩
        exact (S.mem_simClass_iff u).2 this
      exact hxNotU hxU

    exact (Finset.mem_sdiff).2 ⟨hyI, hyNotU⟩

  have hSet : (S.idealFamily).sets (I \ S.simClass u) := by
    change SetFamily.isOrderIdealOn (S.leOn) S.ground (I \ S.simClass u)
    exact And.intro hSub (by intro x hx; exact hDown hx)

  have huNot : u.1 ∉ (I \ S.simClass u) := by
    have huU : u.1 ∈ S.simClass u := by
      have : S.sim u u := S.sim_refl u
      have : ∃ (hu' : u.1 ∈ S.ground), S.sim ⟨u.1, hu'⟩ u := by
        exact ⟨u.property, this⟩
      exact (S.mem_simClass_iff u).2 this
    intro huIn
    have hu_pair := (Finset.mem_sdiff).1 huIn
    exact hu_pair.2 huU
  exact And.intro hSet huNot

noncomputable def Phi
    (S : FuncSetup α) (u : S.Elem) (hmax : S.maximal u) :
    {I // I ∈ (S.idealFamily).edgeFinset ∧ u.1 ∈ I} →
    {J // J ∈ (S.idealFamily).edgeFinset ∧ u.1 ∉ J} :=
  fun ⟨I, hIedge, _⟩ =>
    let hI_sets : (S.idealFamily).sets I :=
      (SetFamily.mem_edgeFinset_iff_sets (F := S.idealFamily) (A := I)).1 hIedge
    let h := ideal_diff_simClass_is_ideal (S := S) (u := u) hmax hI_sets
    let hJedge : (I \ S.simClass u) ∈ (S.idealFamily).edgeFinset :=
      (SetFamily.mem_edgeFinset_iff_sets (F := S.idealFamily) (A := I \ S.simClass u)).2 h.1
    ⟨ I \ S.simClass u, hJedge, h.2 ⟩

--IdealsTraceで引用されている。
lemma Phi_injective
    (S : FuncSetup α) {u : S.Elem} (hmax : S.maximal u) :
    Function.Injective (Phi S u hmax) := by
  classical
  intro a b hEq
  -- 展開
  cases a with
  | mk I hI =>
    cases b with
    | mk J hJ =>
      cases hI with
      | intro hIedge huI =>
        cases hJ with
        | intro hJedge huJ =>
          -- Φ の定義で基底集合の等式へ
          dsimp [Phi] at hEq
          -- 使う補題：U ⊆ I, U ⊆ J
          have hI_sets : (S.idealFamily).sets I :=
            (SetFamily.mem_edgeFinset_iff_sets (F := S.idealFamily) (A := I)).1 hIedge
          have hJ_sets : (S.idealFamily).sets J :=
            (SetFamily.mem_edgeFinset_iff_sets (F := S.idealFamily) (A := J)).1 hJedge
          have UsubI : S.simClass u ⊆ I :=
            S.simClass_subset_of_contains (u := u) (I := I) hI_sets huI
          have UsubJ : S.simClass u ⊆ J :=
            S.simClass_subset_of_contains (u := u) (I := J) hJ_sets huJ
          -- まず基底の Finset 同士の等式を取り出す
          --   I \ U = J \ U
          have hDiff :
              I \ S.simClass u = J \ S.simClass u := by
            -- hEq は Subtype の等式なので、値部分を取り出す
            exact congrArg Subtype.val hEq
          -- I ⊆ J
          have hIJ : I ⊆ J := by
            intro x hxI
            by_cases hxU : x ∈ S.simClass u
            · -- U ⊆ J より
              exact UsubJ hxU
            · -- x ∈ I\U なので等式から x ∈ J\U、したがって x ∈ J
              have hxInDiff : x ∈ I \ S.simClass u :=
                (Finset.mem_sdiff).2 ⟨hxI, hxU⟩
              have hxInDiff' : x ∈ J \ S.simClass u := by
                -- hDiff の両辺に属するので書き換え
                -- `rw [hDiff] at hxInDiff` を避けて等価性で移送
                -- 等式から右辺への移送
                have : (I \ S.simClass u) ⊆ (J \ S.simClass u) := by
                  intro t ht; exact by
                    -- `rw [hDiff]` で十分だが、`rw` を使ってよい
                    -- ここは素直に置換します
                    rw [hDiff] at ht
                    exact ht
                exact this hxInDiff
              have hxJ_and_notU := (Finset.mem_sdiff).1 hxInDiff'
              exact hxJ_and_notU.1
          -- J ⊆ I も同様
          have hJI : J ⊆ I := by
            intro x hxJ
            by_cases hxU : x ∈ S.simClass u
            · exact UsubI hxU
            ·
              have hxInDiff : x ∈ J \ S.simClass u :=
                (Finset.mem_sdiff).2 ⟨hxJ, hxU⟩
              have hxInDiff' : x ∈ I \ S.simClass u := by
                have : (J \ S.simClass u) ⊆ (I \ S.simClass u) := by
                  intro t ht
                  -- 反対向きの包含は hDiff⁻¹
                  -- `rw [← hDiff]` で移送
                  rw [← hDiff] at ht
                  exact ht
                exact this hxInDiff
              have hxI_and_notU := (Finset.mem_sdiff).1 hxInDiff'
              exact hxI_and_notU.1
          -- 以上で I = J
          have hIJ_eq : I = J := Finset.Subset.antisymm hIJ hJI
          -- サブタイプまで持ち上げ
          apply Subtype.ext
          exact hIJ_eq

/-- 単射 `Φ : {A | A∈E ∧ x∈A} → {B | B∈E ∧ x∉B}` があれば `Rare x`。 -/
--単射が存在すればrare。単射の仮定を抜いた形での補題は、Reductionにある。
lemma rare_of_injection_between_filters
  (F : SetFamily α) (x : α)
  (Φ : {A // A ∈ F.edgeFinset ∧ x ∈ A} →
       {B // B ∈ F.edgeFinset ∧ x ∉ B})
  (hΦ : Function.Injective Φ) :
  Rare F x := by
  classical
  let s := F.edgeFinset
  let pin : Finset (Finset α) := s.filter (fun A => x ∈ A)
  let pout : Finset (Finset α) := s.filter (fun A => x ∉ A)

  let eIn :
    {A // A ∈ s ∧ x ∈ A} ≃ {A // A ∈ pin} :=
  { toFun := fun a =>
      ⟨a.1, by
        have h := a.2
        have : a.1 ∈ pin := by
          exact (Finset.mem_filter).2 ⟨h.1, h.2⟩
        exact this⟩
    , invFun := fun b =>
      ⟨b.1, by
        have hb := (Finset.mem_filter).1 b.2
        exact ⟨hb.1, hb.2⟩⟩
    , left_inv := by
        intro a; cases a with
        | mk A hA =>
          rfl
    , right_inv := by
        intro b; cases b with
        | mk B hB =>
          rfl }

  let eOut :
    {A // A ∈ s ∧ x ∉ A} ≃ {A // A ∈ pout} :=
  { toFun := fun a =>
      ⟨a.1, by
        have h := a.2
        have : a.1 ∈ pout := by
          exact (Finset.mem_filter).2 ⟨h.1, h.2⟩
        exact this⟩
    , invFun := fun b =>
      ⟨b.1, by
        have hb := (Finset.mem_filter).1 b.2
        exact ⟨hb.1, hb.2⟩⟩
    , left_inv := by
        intro a; cases a with
        | mk A hA => rfl
    , right_inv := by
        intro b; cases b with
        | mk B hB => rfl }


  have hΦ' :
    Function.Injective (fun a : {A // A ∈ pin} =>
      eOut (Φ (eIn.symm a))) := by
    intro a b h
    have : eIn.symm a = eIn.symm b := by

      apply hΦ

      have := congrArg Subtype.val h

      have hinj := eOut.injective

      have h₁ : Φ (eIn.symm a) = Φ (eIn.symm b) := by
        exact hinj h
      exact hinj h

    simp_all only [Equiv.coe_fn_symm_mk, Equiv.coe_fn_mk, Subtype.mk.injEq, pout, s, eOut, pin, eIn]
    obtain ⟨val_1, property_1⟩ := b
    subst this
    simp_all only [pin, s]

  have hCard_le :
      pin.card ≤ pout.card := by
    have hfin :
        Fintype.card {A // A ∈ pin}
        ≤ Fintype.card {A // A ∈ pout} :=
      Fintype.card_le_of_injective _ hΦ'

    simpa using hfin

  have hDeg : F.degree x = pin.card :=
    (SetFamily.degree_eq_card_filter (F := F) (x := x))
  have hNum : F.numHyperedges = s.card := by
    exact rfl

  have hSplit :
      pin.card + pout.card = s.card := by
    exact card_filter_add_card_filter_not s fun A => x ∈ A

  have h2 :
      2 * pin.card ≤ s.card := by
    have := Nat.add_le_add_left hCard_le pin.card

    have : 2 * pin.card ≤ pin.card + pout.card := by

      have hL : 2 * pin.card = pin.card + pin.card := by

        exact Nat.two_mul pin.card
      have hR : pout.card + pin.card = pin.card + pout.card :=
        Nat.add_comm _ _

      have base := (Nat.add_le_add_left hCard_le pin.card)

      simpa [hL, hR] using base

    simpa [hSplit] using this

  change 2 * F.degree x ≤ F.numHyperedges

  rw [hDeg, hNum]
  exact h2

end Reduction
end AvgRare
