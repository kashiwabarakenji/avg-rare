import Mathlib.Data.Finset.Basic
import Mathlib.Logic.Function.Iterate
import Mathlib.Data.Setoid.Basic
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Logic.Relation
import Mathlib.Logic.Function.Iterate
import AvgRare.Basics.SetFamily
import LeanCopilot

universe u

namespace AvgRare
structure FuncSetup (α : Type u) [DecidableEq α] where
  V      : Finset α
  f      : α → α
  mapsTo : ∀ {x}, x ∈ V → f x ∈ V
--deriving Repr

namespace FuncSetup
variable {α : Type u} [DecidableEq α]
variable (S : FuncSetup α)

abbrev Elem := {x : α // x ∈ S.V}
def fV : S.Elem → S.Elem := fun ⟨x,hx⟩ => ⟨S.f x, S.mapsTo hx⟩
def Reach (x y : S.Elem) : Prop := ∃ n, Nat.iterate S.fV n x = y

def pre : Preorder S.Elem where
  le := S.Reach
  le_refl := by
    intro x; exact ⟨0, rfl⟩
  le_trans := by
    intro x y z ⟨n, hn⟩ ⟨m, hm⟩
    refine ⟨n + m, ?_⟩
    -- f^[n+m] x を f^[m] (f^[n] x) にする：m,n の順で iterate_add_apply を使い、あとで n+m に入れ替え
    have h := Function.iterate_add_apply S.fV m n x
      -- h : S.fV^[m + n] x = (S.fV^[m]) ((S.fV^[n]) x)
    -- 左辺を n+m に書き換えた形を得る
    have h' : (S.fV^[n + m]) x = (S.fV^[m]) ((S.fV^[n]) x) := by
      -- `m + n` → `n + m` のみ左辺を書き換える
      simpa [Nat.add_comm] using h
    -- これで hn, hm を順に適用
    calc
      (S.fV^[n + m]) x
          = (S.fV^[m]) ((S.fV^[n]) x) := h'
      _   = (S.fV^[m]) y := by rw [hn]
      _   = z := by rw [hm]
/-
def pre : Preorder S.Elem where
  le := S.Reach
  le_refl := by intro x; exact ⟨0, by simp⟩
  le_trans := by

    intro x y z ⟨n, hn⟩ ⟨m, hm⟩
    refine ⟨n + m, ?_⟩
    -- f^[n+m] x = f^[m] (f^[n] x) を展開して hn, hm で順に書き換える
    rw [Function.iterate_add]
    rw [←hn] at hm
    have :S.fV^[m+n] x = z:= by
      subst hm hn
      obtain ⟨val, property⟩ := x
      rw [Function.iterate_add_apply]
    rw [←this]
    rw [Nat.add_comm]
    subst hm hn
    simp_all only [Function.comp_apply]
    obtain ⟨val, property⟩ := x
    rw [Function.iterate_add_apply]
-/

instance : Preorder S.Elem := S.pre

def ker : Setoid S.Elem where
  r x y := (x ≤ y) ∧ (y ≤ x)
  iseqv := {
   refl := by intro x; exact ⟨⟨0,rfl⟩,⟨0,rfl⟩⟩,
   symm := by intro x y h; exact ⟨h.2, h.1⟩,
   trans := by intro x y z h1 h2; exact ⟨le_trans h1.1 h2.1, le_trans h2.2 h1.2⟩
  }


abbrev QuotElem := Quot S.ker
def toQuot (x : S.Elem) : S.QuotElem := Quot.mk _ x

def Valid : Prop := ∀ x : S.Elem, S.fV x ≠ x

def isOrderIdeal (S : FuncSetup α) (A : Finset S.Elem) : Prop :=
  ∀ {x y : S.Elem}, y ≤ x → x ∈ A → y ∈ A

noncomputable instance (S : FuncSetup α) : DecidablePred (isOrderIdeal S) := Classical.decPred _

lemma ker_le_of_rel_left  (S : FuncSetup α) {x y : S.Elem} (h : S.ker.r x y) : y ≤ x := h.2
lemma ker_le_of_rel_right (S : FuncSetup α) {x y : S.Elem} (h : S.ker.r x y) : x ≤ y := h.1

lemma ideal_saturated_under_ker (S : FuncSetup α)
  {A : Finset S.Elem} (hA : isOrderIdeal S A) :
  ∀ {x y : S.Elem}, S.ker.r x y → x ∈ A → y ∈ A := by
  intro x y hxy hx
  exact hA (S.ker_le_of_rel_left hxy) hx

/-
lemma degree_sum_eq_total_size_of_hyperedges (F : SetFamily α) :
  (∑ v ∈ F.ground, F.degreeNat v) = F.total_size_of_hyperedgesNat :=
  -- Finset の交換・filter/card で証明
  sorry

lemma sum_normalized_degree_eq_nds (F : SetFamily α) :
  (∑ v ∈ F.ground, F.normalized_degree v) = F.normalized_degree_sum := by
  -- 上の補題と代数整理で終了
  sorry
-/

lemma reach_iff_iterate (x y : S.Elem) :
  S.Reach x y ↔ ∃ n : Nat, Nat.iterate S.fV n x = y := Iff.rfl

/-- 2.4: |同値類| ≥ 2 の成分は `preQuot` で極大（sink）である -/
lemma scc_size_ge_two_is_maximal (C : Set (S.Elem)) :
  True := by  -- TODO: 型を最終形に合わせて精緻化
  trivial

def leQuot (a b : S.QuotElem) : Prop :=
  ∃ x y : S.Elem, a = Quot.mk _ x ∧ b = Quot.mk _ y ∧ x ≤ y

/-- `QuotElem` 上の半順序：代表を選んで `≤` を判定し、それが良定義であることを示す -/
def preQuot : Preorder S.QuotElem where
  -- 主要定義：`le` を `Quot.liftOn₂` で与える
  le := S.leQuot
  le_refl := by
    intro a
    -- 代表に戻して反射律
    refine Quot.induction_on a (fun x => ⟨x, x, rfl, rfl, (S.pre).le_refl x⟩)
  le_trans := by
    intro a b c hab hbc
    rcases hab with ⟨x, y, hax, hby, hxy⟩
    rcases hbc with ⟨y', z, hb'y, hcz, hyz⟩
    -- b の 2 つの表現から y ~ y' を得る
    -- `Quot.mk _ y = Quot.mk _ y'` を作り、そこから核関係へ
    have hyyq : Quot.mk (S.ker) y = Quot.mk (S.ker) y' := by
      -- b = ⟦y⟧ かつ b = ⟦y'⟧ なので ⟦y⟧ = ⟦y'⟧
      exact (Eq.trans (by rw [←hby]) hb'y)
    have hyy : S.ker.r y y' := by
      --subst hby hcz hax
      rw [Quot.eq] at hyyq
      rw [Equivalence.eqvGen_iff] at hyyq
      · exact hyyq
      · show Equivalence ⇑S.ker
        exact S.ker.iseqv
    have hyy' : y ≤ y' := S.ker_le_of_rel_right hyy
    have hxz  : x ≤ z  := (S.pre).le_trans x y z hxy ((S.pre).le_trans y y' z hyy' hyz)
    exact ⟨x, z, hax, hcz, hxz⟩

/-- 1ステップ遷移：x→f x。 -/
def Step (x y : S.Elem) : Prop := S.fV x = y

/-- 到達可能性は Step の反射推移閉包と一致（定義同値）。 -/
private lemma iterate_succ_point (n : Nat) (x : S.Elem) :
  Nat.iterate S.fV (n+1) x = S.fV (Nat.iterate S.fV n x) := by
  -- iterate_succ' は関数等式。点 x で評価し，合成の定義を展開
  have e_fun : S.fV^[n.succ] = S.fV ∘ S.fV^[n] := Function.iterate_succ' S.fV n
  have e_pt  : (S.fV^[n.succ]) x = (S.fV ∘ S.fV^[n]) x :=
    congrArg (fun g => g x) e_fun
  -- (f ∘ g) x = f (g x)
  have e_comp : (S.fV ∘ S.fV^[n]) x = S.fV (S.fV^[n] x) := rfl
  exact Eq.trans e_pt e_comp

lemma reach_eq_reflTrans (x y : S.Elem) :
  S.Reach x y ↔ Relation.ReflTransGen (S.Step) x y := by
  constructor
  · -- (→)  n 回の反復 ⇒ n 本の Step
    intro h
    rcases h with ⟨n, hn⟩
    -- まず x ⟶* (f^[n] x) を，x だけ一般化して n で帰納
    have hx_to_iter : Relation.ReflTransGen S.Step x (Nat.iterate S.fV n x) := by
      induction' n with n ih generalizing x
      · exact Relation.ReflTransGen.refl
      ·
        -- ih : ReflTransGen Step x (f^[n] x)
        -- 1 手： (f^[n] x) → (f^[n+1] x)
        have e : Nat.iterate S.fV (n+1) x = S.fV (Nat.iterate S.fV n x) :=
          iterate_succ_point (S:=S) n x
        -- Step a b は fV a = b。向きを合わせる：
        have step1 : S.Step (Nat.iterate S.fV n x) (Nat.iterate S.fV (n+1) x) := by
          -- e : (f^[n+1]) x = f ( (f^[n]) x )
          -- したがって f ( (f^[n]) x ) = (f^[n+1]) x
          have e' : S.fV (Nat.iterate S.fV n x) = Nat.iterate S.fV (n+1) x :=
            Eq.symm e
          exact e'
        -- 既存の鎖 ih を 1 手 step1 で伸ばす
        exact Relation.ReflTransGen.head rfl (ih (S.fV x) hn)
    -- (f^[n]) x = y で右端を書き換え
    cases hn
    exact hx_to_iter
  · -- (←)  反射推移閉包 ⇒ 反復回数
    intro h
    -- `h : ReflTransGen Step x y` を帰納
    induction h with
    | @refl  =>
        exact ⟨0, rfl⟩
    | @tail a b hxa hab ih  =>
        -- ih : ∃ n, (f^[n]) x = b
        rcases ih with ⟨n, hn⟩
        -- (f^[n+1]) x = f ( (f^[n]) x )
        have e1 : Nat.iterate S.fV (n+1) x
                    = S.fV (Nat.iterate S.fV n x) :=
          iterate_succ_point (S:=S) n x
        -- 右辺の (f^[n]) x を a に置換
        have e2 : Nat.iterate S.fV (n+1) x = S.fV a :=
          Eq.trans e1 (congrArg S.fV hn)
        -- Step a b（= f a = b）で仕上げ
        have e3 : Nat.iterate S.fV (n+1) x = b :=
          Eq.trans e2 hab
        exact ⟨n+1, e3⟩


/-
lemma reach_eq_reflTrans (x y : S.Elem) :
  S.Reach x y ↔ Relation.ReflTransGen (S.Step) x y := by
  constructor
  · -- (→)  n 回の反復 ⇒ n 本の Step
    intro h
    rcases h with ⟨n, hn⟩
    -- まず x ⟶* (f^[n] x) を，x だけ一般化して n で帰納
    have hx_to_iter : Relation.ReflTransGen S.Step x (Nat.iterate S.fV n x) := by
      induction' n with n ih generalizing x
      · exact Relation.ReflTransGen.refl
      ·
        -- ih : ReflTransGen Step x (f^[n] x)
        -- 1 手： (f^[n] x) → (f^[n+1] x)
        have e : Nat.iterate S.fV (n+1) x = S.fV (Nat.iterate S.fV n x) :=
          iterate_succ_point (S:=S) n x
        -- Step a b は fV a = b。向きを合わせる：
        have step1 : S.Step (Nat.iterate S.fV n x) (Nat.iterate S.fV (n+1) x) := by
          -- e : (f^[n+1]) x = f ( (f^[n]) x )
          -- したがって f ( (f^[n]) x ) = (f^[n+1]) x
          have e' : S.fV (Nat.iterate S.fV n x) = Nat.iterate S.fV (n+1) x :=
            Eq.symm e
          exact e'
        exact Relation.ReflTransGen.head rfl (ih (S.fV x) hn)
    -- 最後に y へ置換（hn : (f^[n]) x = y）
    -- まず hn の対称を作って右辺を (f^[n]) x に変える
    have : Relation.ReflTransGen S.Step x y := by
      -- ReflTransGen は目標の点を等式で書き換えられる
      -- (x ⟶* (f^[n] x)) かつ (f^[n] x = y) ⇒ x ⟶* y
      -- `Relation.ReflTransGen.congr_right` が無いので単純に「cases hn」で書き換える
      cases hn
      exact hx_to_iter
    exact this
  · -- (←)  反射推移閉包 ⇒ 反復回数
    intro h
    induction h with
    | @refl  =>
        exact ⟨0, rfl⟩
    | @tail a b c hab hbc  =>

        have e : Nat.iterate S.fV (n+1) a = S.fV (Nat.iterate S.fV n a) :=
          iterate_succ_point (S:=S) n a
        -- 連鎖： (f^[n+1]) a = f ( (f^[n]) a ) = f b = c
        have : Nat.iterate S.fV (n+1) a = c := by
          -- Nat.iterate S.fV n a = b を fV に写像
          have e2 : S.fV (Nat.iterate S.fV n a) = S.fV b :=
            congrArg S.fV hn
          -- Step b c： S.fV b = c
          have e3 : S.fV b = c := hbc
          -- 結合
          exact Eq.trans (Eq.trans e e2) e3
        exact ⟨n+1, this⟩
-/


/-- SCC 商上での「一歩」：代表を取って f を1回当てる像。 -/
def stepQuot (a b : S.QuotElem) : Prop :=
  ∀ x, a = Quot.mk _ x → ∃ y, b = Quot.mk _ y ∧ S.Step x y

/-- 商上の outdegree は高々1（関数性から）。 -/
lemma outdeg_le_one_on_quot (a : S.QuotElem) :
  ¬ (∃ b c, b ≠ c ∧ stepQuot S a b ∧ stepQuot S a c) := by
  classical
  intro h
  rcases h with ⟨b, c, hbc, hb, hc⟩
  -- a の代表を 1 つ取る
  rcases Quot.exists_rep a with ⟨x, hx⟩
  -- b, c の 1 手先の代表
  rcases hb x hx.symm with ⟨y₁, hb_eq, hb_step⟩
  rcases hc x hx.symm with ⟨y₂, hc_eq, hc_step⟩
  -- f は関数：f x = y₁, f x = y₂ ⇒ y₁ = y₂
  have hy : y₁ = y₂ := by
    -- hb_step : S.fV x = y₁, hc_step : S.fV x = y₂
    -- したがって y₁ = S.fV x = y₂
    have h1 : y₁ = S.fV x := Eq.symm hb_step
    have h2 : S.fV x = y₂ := hc_step
    exact Eq.trans h1 h2
  -- よって ⟦y₁⟧ = ⟦y₂⟧、b = c に矛盾
  have hbc' : b = c := by
    calc
      b = Quot.mk _ y₁ := hb_eq
      _ = Quot.mk _ y₂ := by
            exact congrArg (fun z => Quot.mk (S.ker) z) hy
      _ = c := by
            exact Eq.symm hc_eq
  exact hbc hbc'


/-- 商上の反対称性（=有向閉路なし）※ SCC 凝縮の基本事実。 -/
lemma antisymm_on_quot :
  ∀ {a b}, (S.preQuot.le) a b → (S.preQuot.le) b a → a = b := by
  intro a b hab hba
  rcases hab with ⟨x, y, hax, hby, hxy⟩
  rcases hba with ⟨x', y', hbx', hay', hx'y'⟩
  -- b の二通りの表現から y ~ x'
  have hyx' : S.ker.r y x' := by
    -- ⟦y⟧ = b = ⟦x'⟧
    have e : Quot.mk (S.ker) y = Quot.mk (S.ker) x' := by
      have e1 : Quot.mk (S.ker) y = b := Eq.symm hby
      have e2 : b = Quot.mk (S.ker) x' := hbx'
      exact Eq.trans e1 e2
    exact Quotient.eq''.mp e
  -- a の二通りの表現から x ~ y'
  have hxy' : S.ker.r x y' := by
    -- ⟦x⟧ = a = ⟦y'⟧
    have e : Quot.mk (S.ker) x = Quot.mk (S.ker) y' := by
      have e1 : Quot.mk (S.ker) x = a := Eq.symm hax
      have e2 : a = Quot.mk (S.ker) y' := hay'
      exact Eq.trans e1 e2
    exact Quotient.eq''.mp e

  -- ker から ≤ を取り出す
  have hy_le_x' : y ≤ x' := S.ker_le_of_rel_right hyx'
  have hx'_le_y : x' ≤ y := S.ker_le_of_rel_left  hyx'
  have hx_le_y' : x ≤ y' := S.ker_le_of_rel_right hxy'
  have hy'_le_x : y' ≤ x := S.ker_le_of_rel_left  hxy'
  -- y ≤ x' ≤ y' ≤ x を連結して y ≤ x
  have hy_le_y' : y ≤ y' := (S.pre).le_trans y x' y' hy_le_x' hx'y'
  have hy_le_x  : y ≤ x  := (S.pre).le_trans y y' x  hy_le_y'  hy'_le_x
  -- もともと x ≤ y（hxy）なので ker.r x y
  have hker_xy : S.ker.r x y := ⟨hxy, hy_le_x⟩
  -- よって ⟦x⟧ = ⟦y⟧、a = b
  have equot : Quot.mk (S.ker) x = Quot.mk (S.ker) y := Quot.sound hker_xy
  -- a = ⟦x⟧, b = ⟦y⟧
  have : a = b := by
    calc
      a = Quot.mk (S.ker) x := hax
      _ = Quot.mk (S.ker) y := equot
      _ = b := by exact Eq.symm hby
  exact this

/-- 以後、`preQuot` をインスタンスとして使いたい場合は次を有効化 -/
instance : Preorder S.QuotElem := S.preQuot

/-- これで `QuotElem` 上の極大（sink）を自然に定義できる -/
def isMaximal (q : S.QuotElem) : Prop := ¬ ∃ r : S.QuotElem, q < r
-- あるいは ≤ を使う版なら：
-- def isMaximal' (q : S.QuotElem) : Prop := ¬ ∃ r, q ≠ r ∧ q ≤ r

end FuncSetup
end AvgRare
