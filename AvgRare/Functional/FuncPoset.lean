import Mathlib.Data.Finset.Basic
--import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.Order.Sub.Basic
import AvgRare.Basics.SetFamily
import AvgRare.Basics.SetTrace --excess is defined here
import AvgRare.Functional.FuncSetup

universe u
open Classical

open scoped BigOperators

namespace AvgRare
namespace FuncSetup

open FuncSetup
open SetFamily

variable {α : Type u} [DecidableEq α] (S : FuncSetup α)

----------------------------

noncomputable def principalIdeal (S : FuncSetup α) (a : α) (ha : a ∈ S.ground) : Finset α := by
  classical
  -- attach is {y // y ∈ ground}, predicate is `S.le y ⟨a,ha⟩`
  exact (S.ground.attach.filter (fun (y : {z // z ∈ S.ground}) => S.le y ⟨a, ha⟩)).map
    ⟨Subtype.val, by simp_all only [Subtype.val_injective]⟩

-- Referenced in the second half of the proof.
/-- Membership test (existential form): `y ∈ ↓a` ↔ `∃ hy, y ∈ ground ∧ (⟨y,hy⟩ ≤ₛ ⟨a,ha⟩)`. -/
lemma mem_principalIdeal_iff (S : FuncSetup α)
  {a y : α} (ha : a ∈ S.ground) :
  y ∈ S.principalIdeal a ha ↔ ∃ hy : y ∈ S.ground, S.le ⟨y, hy⟩ ⟨a, ha⟩ := by
  classical
  constructor
  · intro hy
    rcases Finset.mem_map.mp hy with ⟨u, hu, huv⟩
    -- Extract the condition part
    have hcond : S.le u ⟨a, ha⟩ := (Finset.mem_filter.mp hu).2
    -- `u.val = y`
    cases u with
    | mk uval up =>
      cases huv
      exact ⟨up, hcond⟩
  · rintro ⟨hy, hle⟩
    have hy_att : ⟨y, hy⟩ ∈ S.ground.attach := Finset.mem_attach _ _
    have hy_fil :
        ⟨y, hy⟩ ∈ S.ground.attach.filter (fun z => S.le z ⟨a, ha⟩) :=
      Finset.mem_filter.mpr ⟨hy_att, hle⟩
    exact Finset.mem_map.mpr ⟨⟨y, hy⟩, hy_fil, rfl⟩

/-- Simplified form with ground premise: `y ∈ ↓a` ↔ `⟨y,hy⟩ ≤ₛ ⟨a,ha⟩`. -/
private lemma mem_principalIdeal_iff_le (S : FuncSetup α)
  {a y : α} (ha : a ∈ S.ground) (hy : y ∈ S.ground) :
  y ∈ S.principalIdeal a ha ↔ S.le ⟨y, hy⟩ ⟨a, ha⟩ := by
  constructor
  · intro h; rcases (S.mem_principalIdeal_iff (a:=a) (y:=y) ha).1 h with ⟨hy', hle⟩
    cases Subtype.ext (rfl : (⟨y, hy'⟩ : S.Elem).1 = (⟨y, hy⟩ : S.Elem).1)
    exact hle
  · intro hle; exact (S.mem_principalIdeal_iff (a:=a) (y:=y) ha).2 ⟨hy, hle⟩

-- Used by SumProduct.
lemma self_mem_principalIdeal (m : S.Elem) :
  m.1 ∈ S.principalIdeal m.1 m.2 := by
  classical
  -- By reflexivity: `⟨m, _⟩ ≤ ⟨m, _⟩`
  have : S.le ⟨m.1, m.2⟩ ⟨m.1, m.2⟩ := Relation.ReflTransGen.refl
  -- Use simplified membership test
  exact
    (S.mem_principalIdeal_iff_le (a := m.1) (y := m.1) (ha := m.2) (hy := m.2)).2
      this

-- Used by SumProduct.
lemma principalIdeal_subset_ground (S : FuncSetup α) (x : S.Elem) :
  S.principalIdeal x.1 x.2 ⊆ S.ground := by
  intro a ha
  obtain ⟨val, property⟩ := x
  simp_all only
  rw [principalIdeal] at ha
  simp_all only [le_iff_leOn_val, Finset.mem_map, Finset.mem_filter, Finset.mem_attach, true_and,
    Function.Embedding.coeFn_mk, Subtype.exists, exists_and_left, exists_prop, exists_eq_right_right]

-----------
private lemma principalIdeal_isOrderIdealOn
  (S : FuncSetup α) {a : α} (ha : a ∈ S.ground) :
  SetFamily.isOrderIdealOn (S.leOn) S.ground (S.principalIdeal a ha) := by

  dsimp [SetFamily.isOrderIdealOn]
  constructor
  · dsimp [FuncSetup.principalIdeal]
    simp_all only [le_iff_leOn_val]
    intro x hx
    simp_all only [Finset.mem_map, Finset.mem_filter, Finset.mem_attach, true_and, Function.Embedding.coeFn_mk,
      Subtype.exists, exists_and_left, exists_prop, exists_eq_right_right]
  ·
    intro x hx y hy_mem

    intro hs
    have hx' := (S.mem_principalIdeal_iff (a:=a) (y:=x) ha).1 hx
    simp at hx'
    let mpi := (S.mem_principalIdeal_iff (a:=a) (y:=y) ha).2
    apply mpi
    use hy_mem
    have : S.leOn y a := S.leOn_trans hs hx'.2
    exact (leOn_iff S hy_mem ha).mp this


def isPoset_excess (S : FuncSetup α) : Prop :=
  excess (S.idealFamily) = 0

/- `isPoset` (≡ excess=0) implies `|ground| = #classes`. -/
-- Used later.
private lemma ground_card_eq_numClasses_of_isPoset
  (S : FuncSetup α) (h : isPoset_excess S) :
  (S.idealFamily).ground.card = numClasses (S.idealFamily) := by
  classical
  -- excess = |ground| − #classes = 0 ⇒ |ground| ≤ #classes
  have hle₁ :
      (S.idealFamily).ground.card ≤ numClasses (S.idealFamily) := by

    exact tsub_eq_zero_iff_le.mp (by
      exact h)

  have hle₂ :
      numClasses (S.idealFamily) ≤ (S.idealFamily).ground.card :=
    numClasses_le_ground_card (F := S.idealFamily)
  exact Nat.le_antisymm hle₁ hle₂

/- `isPoset S` implies each class in `classSet (S.idealFamily)` has size 1. -/
-- Used later.
private lemma classes_card_one_of_isPoset
  (S : FuncSetup α) (h : isPoset_excess S) :
  ∀ C ∈ classSet (S.idealFamily), C.card = 1 := by
  classical
  let F := S.idealFamily
  -- Nonempty
  have hnon : ∀ C ∈ classSet F, C.Nonempty :=
    classSet_nonempty (F := F)
  -- Pairwise disjoint
  have hdisj :
      ∀ C ∈ classSet F, ∀ D ∈ classSet F, C ≠ D → Disjoint C D :=
    by intro C hC D hD hne; exact classSet_disjoint_of_ne (F := F) hC hD hne
  -- Covering
  have hcover : F.ground = Finset.biUnion (classSet F) (fun C => C) :=
    ground_eq_biUnion_classSet (F := F)
  have hcard : F.ground.card = (classSet F).card :=
    ground_card_eq_numClasses_of_isPoset (S := S) h
  have hiff :=
    card_eq_blocks_iff_all_blocks_card_one
      (s := F.ground) (P := classSet F) hdisj hcover hnon
  exact (by
    exact (Iff.mp hiff hcard))

-- Posets are antisymmetric. Used extensively.
lemma antisymm_of_isPoset
  (S : FuncSetup α) (h : isPoset_excess S) :
  ∀ {u v : S.Elem}, S.le u v → S.le v u → u = v := by
  classical
  intro u v hxy hyx
  -- First establish `sim u v`
  have hsim : S.sim u v := And.intro hxy hyx
  -- From `isPoset`, all classes have size 1
  have hall1 : ∀ C ∈ classSet (S.idealFamily), C.card = 1 :=
    classes_card_one_of_isPoset (S := S) h
  -- Apply lemma 3)
  exact FuncSetup.eq_of_sim_of_all_classes_card_one S hall1 hsim

instance functional_poset (S : FuncSetup α) (h : isPoset_excess S) :
   PartialOrder S.Elem := by
  refine { le := S.le,
           le_refl := fun a => by exact FuncSetup.le_refl S a,
           le_trans := fun a b c hab hbc => by exact FuncSetup.le_trans S hab hbc,
           le_antisymm := fun a b hab hba => by exact antisymm_of_isPoset S h hab hba }

-- Conversely, when all equivalence classes in FuncSetup have size 1, it becomes a poset.
private lemma isPoset_of_classes_card_one (S : FuncSetup α) (h : ∀ C ∈ classSet (S.idealFamily), C.card = 1) :
  isPoset_excess S := by
  classical
  dsimp [isPoset_excess]
  dsimp [excess]
  dsimp [SetFamily.numClasses]
  --dsimp [SetFamily.classSet]
  rw [SetFamily.card_ground_eq_sum_card_classes]
  simp_all only [Finset.sum_const, smul_eq_mul, mul_one, tsub_self]

-- When FuncSetup.le is anti-symmetric, it becomes a poset.
-- Used externally.
lemma isPoset_of_le_antisymm (S : FuncSetup α) (h : ∀ {u v : S.Elem}, S.le u v → S.le v u → u = v) :
  isPoset_excess S := by
  -- Show that every simClass is a singleton.
  have : ∀ (x : S.Elem), (S.simClass x).card  = 1 := by
    intro x
    dsimp [FuncSetup.simClass]
    dsimp [FuncSetup.simClassElem]
    dsimp [FuncSetup.sim]
    simp
    simp_all only [FuncSetup.le_iff_leOn_val, Subtype.forall, Subtype.mk.injEq, Finset.coe_mem]
    refine Finset.card_eq_one.mpr ?_
    use x
    obtain ⟨val, property⟩ := x
    simp_all only [Finset.coe_mem]
    ext
    simp_all only [Finset.coe_mem, Finset.mem_image, Finset.mem_filter, Finset.mem_attach, true_and, Subtype.exists,
      exists_and_left, exists_prop, exists_eq_right_right, Finset.mem_singleton]
    apply Iff.intro
    · intro a
      obtain ⟨left, right⟩ := a
      obtain ⟨left, right_1⟩ := left
      apply h
      · simp_all only
      · simp_all only
      · simp_all only
      · simp_all only
    · intro a
      subst a
      simp_all only [and_self, and_true]
      tauto

  have :  ∀ C ∈ classSet (S.idealFamily), C.card = 1 := by
    intro C hC
    dsimp [SetFamily.classSet] at hC
    rw [Finset.mem_image] at hC
    obtain ⟨a,ha⟩ := hC
    let sf :=  FuncSetup.simClass_eq_parallelClass S (S.toElem! ha.1)
    --simp at sf
    simp_all only [FuncSetup.le_iff_leOn_val, Subtype.forall, Subtype.mk.injEq, FuncSetup.simClass_eq_parallelClass,
    Finset.coe_mem]
    obtain ⟨left, right⟩ := ha
    subst right
    exact this _ left

  exact isPoset_of_classes_card_one S this

  -------

private lemma iterate_has_collision
  {β : Type _} [Fintype β] (f : β → β) (x : β) :
  ∃ i j : Fin (Fintype.card β + 1), i ≠ j ∧
    Nat.iterate f i.1 x = Nat.iterate f j.1 x := by
  classical
  -- Pigeonhole principle: Fin (|β|+1) → β cannot be injective
  have hnotinj :
    ¬ Function.Injective (fun i : Fin (Fintype.card β + 1) => Nat.iterate f i.1 x) := by
    intro hinj
    -- If injective, then |Fin (n)| ≤ |β|, i.e., n ≤ |β|. Here n = |β|+1, contradiction.
    have hcard := Fintype.card_le_of_injective _ hinj
    -- card_fin
    have : Fintype.card (Fin (Fintype.card β + 1)) ≤ Fintype.card β := hcard
    -- i.e., |β|+1 ≤ |β| is false
    have : Fintype.card β + 1 ≤ Fintype.card β := by
      simp_all only [Fintype.card_fin, add_le_iff_nonpos_right, nonpos_iff_eq_zero, one_ne_zero]
    exact (Nat.not_succ_le_self (Fintype.card β)) this
  -- Concrete instance of non-injectivity
  -- ¬Injective ↔ ∃ i≠j, f i = f j
  -- The order in the (= vs ≠) arrangement may vary, but here we just need to construct a pair
  classical
  -- Expand
  have : ∃ i j, i ≠ j ∧
      (fun k : Fin (Fintype.card β + 1) => Nat.iterate f k.1 x) i =
      (fun k : Fin (Fintype.card β + 1) => Nat.iterate f k.1 x) j := by
    -- Could directly expand with `by_contra`, but here we leave it to classical choice
    -- Short: extract with Classical.not_forall.mp
    -- Here you can accept this as a lemma

    let nf := not_forall.mp (by
          intro h
          let hi := hnotinj (by
              intros i j hij
              simp_all only
              ext : 1
              norm_cast at hij
            )
          simp_all only
          )
    simp_all only [ne_eq]
    obtain ⟨w, h⟩ := nf
    simp_all
    obtain ⟨w_1, h⟩ := h
    obtain ⟨left, right⟩ := h
    apply Exists.intro
    · apply Exists.intro
      · apply And.intro
        on_goal 2 => { exact left
        }
        · simp_all only [not_false_eq_true]

  rcases this with ⟨i, j, hneq, heq⟩
  exact ⟨i, j, hneq, heq⟩

def isPoset : Prop :=
  has_le_antisymm S

/-- If iteration develops a cycle, antisymmetry forces it to be a fixed point (cycle of length 1). -/
-- Used in UniqueMax.lean.
lemma eventually_hits_fixpoint
  (S : FuncSetup α) [Fintype S.Elem] (hpos : isPoset S)
  (x : S.Elem) :
  ∃ m : S.Elem, S.le x m ∧ S.cover m m := by
  classical
  -- Collision in iteration by pigeonhole principle
  obtain ⟨i, j, hneq, heq⟩ :=
    iterate_has_collision (β := S.Elem) (f := S.f) x
  -- For convenience, rearrange to i<j side
  have hij : i.1 ≠ j.1 := by
    simp_all only [ne_eq]
    obtain ⟨val, property⟩ := x
    apply Aesop.BuiltinRules.not_intro
    intro a
    simp_all only
    omega

  have hlt_or := lt_or_gt_of_ne hij
  -- WLOG： i<j
  cases hlt_or with
  | inl hlt =>
      let t := j.1 - i.1
      have htpos : 0 < t := Nat.sub_pos_of_lt hlt
      let y := Nat.iterate S.f i.1 x
      -- Cycle: iterate f t y = y
      have cyc : Nat.iterate S.f t y = y := by
        -- Use `Nat.iterate_add` to connect i and (j-i)
        have hj : i.1 + t = j.1 := Nat.add_sub_of_le (Nat.le_of_lt hlt)
        -- Calculation sequence
        calc
          Nat.iterate S.f t y
              = Nat.iterate S.f (i.1 + t) x := by
                  -- y = iterate i x
                  -- iterate t (iterate i x) = iterate (i+t) x
                  simp [y]
                  --rw [Function.iterate_add_apply]
                  rw [← @Function.iterate_add_apply]
                  simp_all only [ne_eq, Fin.val_fin_lt, tsub_pos_iff_lt, t]
                  ext : 1
                  congr
                  omega
          _   = Nat.iterate S.f j.1 x := by
                  -- j = i + t
                  simp [hj]
          _   = Nat.iterate S.f i.1 x := by exact id (Eq.symm heq)
          _   = y := rfl

      have ht1 : Nat.succ (t - 1) = t := Nat.succ_pred_eq_of_pos htpos
      have gt1: t >= 1:= by exact htpos
      have fxy :S.f^[t + ↑i] x = y := by
        simp_all only [ne_eq, Fin.val_fin_lt, tsub_pos_iff_lt, Nat.succ_eq_add_one, ge_iff_le,  t, y]
        simp_all only [Nat.sub_add_cancel]
        obtain ⟨val, property⟩ := x
        obtain ⟨val_1, property_1⟩ := y
        ext : 1
        congr
        omega
      have xyle : S.le x y := by
        apply (FuncSetup.le_iff_exists_iter S x y).mpr
        use (t + i)
        exact fxy

      have back : Nat.iterate S.f (t - 1) (S.f y) = y := by
        have : Nat.iterate S.f (1 + (t - 1)) y = y := by
          have := cyc
          have : Nat.iterate S.f t y = y := cyc
          simp_all only [ne_eq, Fin.val_fin_lt, tsub_pos_iff_lt, Nat.succ_eq_add_one, ge_iff_le, add_tsub_cancel_of_le, t, y]

        rw [← @Function.iterate_add_apply] at this
        have fxy :S.f^[t + ↑i] x = y := by
          simp_all only [ne_eq, Fin.val_fin_lt, tsub_pos_iff_lt, Nat.succ_eq_add_one, ge_iff_le, add_tsub_cancel_of_le, t, y]
        rw [Function.iterate_add_apply] at fxy
        rw [←Function.iterate_succ_apply]
        rw [ht1]
        exact cyc

      -- One step: y ≤ f y
      have y_le_fy : S.le y (S.f y) :=
        Relation.ReflTransGen.tail
          (Relation.ReflTransGen.refl) rfl
      -- (t-1) steps: f y ≤ y
      have : S.cover x (S.f x) := by
        exact rfl
      have fy_le_y : S.le (S.f y) y:= by
        apply (FuncSetup.le_iff_exists_iter S (S.f y) y).mpr
        use (t - 1)
        exact back

      have : S.f y = y := by
        exact hpos fy_le_y y_le_fy

      use y
      dsimp [cover]
      constructor
      · exact xyle
      · exact this

  | inr hgt =>

      let t := i.1 - j.1
      have htpos : 0 < t := Nat.sub_pos_of_lt hgt
      let y := Nat.iterate S.f j.1 x
      have cyc : Nat.iterate S.f t y = y := by
        have hj : j.1 + t = i.1 := Nat.add_sub_of_le (Nat.le_of_lt hgt)

        calc
          Nat.iterate S.f t y
              = Nat.iterate S.f (j.1 + t) x := by
                  simp [y]
                  rw [← @Function.iterate_add_apply]
                  ext : 1
                  have : t + ↑j = ↑j + t := by exact Nat.add_comm t ↑j
                  rw [this]

          _   = Nat.iterate S.f i.1 x := by

                  simp [hj]
          _   = Nat.iterate S.f i.1 x := by exact rfl
          _   = y := by exact heq
      have ht1 : Nat.succ (t - 1) = t := Nat.succ_pred_eq_of_pos htpos
      have gt1: t >= 1:= by exact htpos
      have fxy :S.f^[t + ↑j] x = y := by
        simp_all only [ne_eq, Fin.val_fin_lt, tsub_pos_iff_lt, Nat.succ_eq_add_one, ge_iff_le, Nat.sub_add_cancel, t, y]
        rw [Function.iterate_add_apply]
        simp_all only

      have xyle : S.le x y := by
        apply (FuncSetup.le_iff_exists_iter S x y).mpr
        use (t + j)
        exact fxy

      have back : Nat.iterate S.f (t - 1) (S.f y) = y := by
        have : Nat.iterate S.f (1 + (t - 1)) y = y := by
          have := cyc
          have : Nat.iterate S.f t y = y := cyc
          simp_all only [ne_eq, Fin.val_fin_lt, tsub_pos_iff_lt, Nat.succ_eq_add_one, ge_iff_le, add_tsub_cancel_of_le, t, y]

        rw [← @Function.iterate_add_apply] at this
        have fxy :S.f^[t + ↑j] x = y := by
          simp_all only [ne_eq, Fin.val_fin_lt, tsub_pos_iff_lt, Nat.succ_eq_add_one, ge_iff_le, add_tsub_cancel_of_le, t, y]
        rw [Function.iterate_add_apply] at fxy
        rw [←Function.iterate_succ_apply]
        rw [ht1]
        exact cyc

      have y_le_fy : S.le y (S.f y) :=
        Relation.ReflTransGen.tail
          (Relation.ReflTransGen.refl) rfl

      have : S.cover x (S.f x) := by
        exact rfl
      have fy_le_y : S.le (S.f y) y:= by

        apply (FuncSetup.le_iff_exists_iter S (S.f y) y).mpr
        use (t - 1)
        exact back

      have : S.f y = y := by
        exact hpos fy_le_y y_le_fy

      use y
      dsimp [cover]
      constructor
      · exact xyle
      · exact this

--Existence of maximal element.
--Also used from MainStatement.
lemma exists_maximal_of_finite
  (S : FuncSetup α) [Fintype S.Elem] (hpos : isPoset S)
  (hne : S.ground.Nonempty) :
  ∃ m : S.Elem, S.maximal m := by
  classical
  -- Start from any x and reach a fixed point
  obtain ⟨x, hx⟩ := hne
  let x0 : S.Elem := ⟨x, by exact hx⟩
  obtain ⟨m, x_le_m, hmfix⟩ := eventually_hits_fixpoint S hpos x0
  exact ⟨m, maximal_of_fixpoint S hmfix⟩

lemma principalOn_inj(S : FuncSetup α) {x y : S.Elem}
  (hpos : isPoset S)
  (hxy : S.principalIdeal x x.2= S.principalIdeal y y.2) : x = y := by
  have hxmem : x.1 ∈ S.principalIdeal x x.2 := by
    -- x ∈ ground ∧ S.le x x（refl）
    have hxG : x.1 ∈ S.ground := x.2
    have hxx : S.le x x := Relation.ReflTransGen.refl
    have hxPair : x.1 ∈ S.ground ∧ S.le ⟨x.1, hxG⟩ x := And.intro hxG hxx
    exact (S.mem_principalIdeal_iff x.2 (a := x.1)).2 ⟨hxPair.1, hxPair.2⟩
  have hx_in_y : x.1 ∈ S.principalIdeal y y.2 := by
    exact hxy ▸ hxmem
  simp at hx_in_y
  let mpi := (S.mem_principalIdeal_iff y.2).1 hx_in_y
  obtain ⟨hy, hhy⟩ := mpi
  have hxy_le : S.le x y := by exact hhy

  have hymem : y.1 ∈ S.principalIdeal y y.2 := by

    have hyG : y.1 ∈ S.ground := y.2
    have hyy : S.le y y := Relation.ReflTransGen.refl
    exact (S.mem_principalIdeal_iff (a := y.1) (y := y) y.2).2 ⟨hyG, hyy⟩

  have hy_in_x : y.1 ∈ S.principalIdeal x x.2 := by
    exact hxy ▸ hymem
  simp at hy_in_x
  obtain ⟨hx, hxh⟩ := (S.mem_principalIdeal_iff x.2).1 hy_in_x
  have hyx_le: S.le y x := by exact hxh
  exact hpos hhy hxh

-- Used, but FuncSetup also has a similar lemma.
lemma empty_isOrderIdealOn (S : FuncSetup α) :
  SetFamily.isOrderIdealOn (S.leOn) S.ground (∅ : Finset α) := by
  dsimp [SetFamily.isOrderIdealOn]
  constructor
  · -- ∅ ⊆ ground
    intro x hx; cases hx
  · -- Downward closed: premise is false
    intro x hx; cases hx

-- This might overlap with other lemmas.
/-- principalIdeal is an edge (element of `idealFamily`) -/
lemma principalIdeal_mem_edge (S : FuncSetup α) (x : S.Elem) :
  S.principalIdeal x.1 x.2 ∈ (S.idealFamily).edgeFinset := by
  -- Use `sets ↔ isOrderIdealOn` to prove this
  have hI :
    SetFamily.isOrderIdealOn (S.leOn) S.ground (S.principalIdeal x.1 x.2) :=
    principalIdeal_isOrderIdealOn (S := S) x.2
  have hxSets :
    (S.idealFamily).sets (S.principalIdeal x.1 x.2) := by
    -- Use the right direction of `sets_iff_isOrderIdeal`
    have := (S.sets_iff_isOrderIdeal (I := S.principalIdeal x.1 x.2))
    exact this.mpr hI
  -- Use `mem_edgeFinset_iff_sets` to get edge
  exact
    (SetFamily.mem_edgeFinset_iff_sets
      (F := S.idealFamily) (A := S.principalIdeal x.1 x.2)).2 hxSets

/- Empty set is also an edge. -/
-- FuncSetup has a similar lemma.
lemma empty_mem_edge (S : FuncSetup α) :
  (∅ : Finset α) ∈ (S.idealFamily).edgeFinset := by
  -- From the fact that empty set is an ideal
  have hI : SetFamily.isOrderIdealOn (S.leOn) S.ground (∅ : Finset α) :=
    empty_isOrderIdealOn S
  have hSets : (S.idealFamily).sets (∅ : Finset α) := by
    have := (S.sets_iff_isOrderIdeal (I := (∅ : Finset α)))
    exact this.mpr hI
  exact
    (SetFamily.mem_edgeFinset_iff_sets (F := S.idealFamily) (A := (∅ : Finset α))).2 hSets

end FuncSetup
end AvgRare
