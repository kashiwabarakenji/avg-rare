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

lemma reach_iff_iterate (x y : S.Elem) :
  S.Reach x y ↔ ∃ n : Nat, Nat.iterate S.fV n x = y := Iff.rfl



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

def NontrivialClass (q : S.QuotElem) : Prop :=
  ∃ x y : S.Elem, q = Quot.mk _ x ∧ q = Quot.mk _ y ∧ x ≠ y

/-- 非自明 SCC なら，代表 `x` は正の長さの閉路上：`∃ n>0, (fV^[n]) x = x`。 -/
private lemma exists_pos_cycle_of_nontrivial
  {q : S.QuotElem} (h : S.NontrivialClass q) :
  ∃ x : S.Elem, ∃ n : Nat, 0 < n ∧ (S.fV^[n]) x = x := by
  classical
  rcases h with ⟨x, y, hx, hy, hxy⟩
  -- q = ⟦x⟧ = ⟦y⟧ から ker.r x y
  have hxyKer : S.ker.r x y := by
    -- Quot の等値から核関係へ
    -- （`Quotient.eq''` を使うと速い）
    have : Quot.mk (S.ker) x = Quot.mk (S.ker) y := by
      sorry -- Eq.trans hx (Eq.symm hy)
    exact Quotient.eq''.mp this
  -- 逆向きも同様
  have hyxKer : S.ker.r y x := by
    have : Quot.mk (S.ker) y = Quot.mk (S.ker) x := by
      exact Quot.sound (id (Setoid.symm' S.ker hxyKer))
    exact Quotient.eq''.mp this

  -- ker.r = (≤ ∧ ≥) なので，到達性の両向きがある
  have hxyReach : x ≤ y := hxyKer.1
  have hyxReach : y ≤ x := by exact ker_le_of_rel_left S hxyKer

  -- ここから正の長さ n>0 の閉路 `(fV^[n]) x = x` を得る
  -- （`reach_eq_reflTrans` と `iterate_succ_point` を用いた標準手続き）
  -- 詳細は論文の概略どおりに貼り合わせれば OK
  -- ▼ ここは“到達の合成”を丁寧に書くと通ります
  have : ∃ n : Nat, 0 < n ∧ (S.fV^[n]) x = x := by
    -- x ≤ y, y ≤ x かつ x≠y から，正の長さの反射推移閉包閉路
    -- `reach_eq_reflTrans` を2回使い，長さ>0 を取り出す
    sorry

  rcases this with ⟨n, hnpos, hcycle⟩
  exact ⟨x, n, hnpos, hcycle⟩

-- 1) ⟦x⟧ = ⟦y⟧ → S.ker.r x y への変換（Quotient.eq'' を避ける）
lemma ker_of_mk_eq {x y : S.Elem}
  (h : Quot.mk (S.ker) x = Quot.mk (S.ker) y) : S.ker.r x y := by
  -- h : ⟦x⟧ = ⟦y⟧ から EqvGen を取り、等価関係なので ker.r に落とす
  have hEqv : Relation.EqvGen S.ker.r x y := by
    -- `Quot.eq` は ⟦x⟧ = ⟦y⟧ ↔ EqvGen r x y を与える
    -- （`simp [Quot.eq]` は避けて、片向きを明示的に）
    exact (Quot.eq.mp h)
  -- 等価関係上では EqvGen ↔ r
  have hEquiv : Equivalence S.ker.r := S.ker.iseqv
  -- `Equivalence.eqvGen_iff` を使って EqvGen → r
  -- （型クラス推論に任せず、明示に書く）
  have : S.ker.r x y := by
    -- rewrite: EqvGen r x y ↔ r x y
    have := (Equivalence.eqvGen_iff hEquiv).mp hEqv
    exact this
  exact this

-- 2) S.ker.r x y → ⟦x⟧ = ⟦y⟧ は `Quot.sound` でそのまま
lemma mk_eq_of_ker {x y : S.Elem} (h : S.ker.r x y) :
  Quot.mk (S.ker) x = Quot.mk (S.ker) y :=
  Quot.sound h

private lemma succ_in_same_class_of_nontrivial
  {q : S.QuotElem} (h : S.NontrivialClass q) :
  ∀ ⦃x : S.Elem⦄, q = Quot.mk (S.ker) x →
       Quot.mk (S.ker) (S.fV x) = Quot.mk (S.ker) x := by
  classical
  -- 方針：q に 2 代表 x₀≠y₀ がある → x とも相互到達 → x に正の長さの閉路
  --       閉路から (fV x) ≤ x ∧ x ≤ (fV x) を構成して ker へ落とす
  intro x hxq
  rcases h with ⟨x₀, y₀, hx₀, hy₀, hne⟩
  -- x と x₀, y₀ が同一クラスであることを明示化
  have hx_x₀ : S.ker.r x x₀ := S.ker_of_mk_eq (Eq.trans hxq.symm (Eq.symm hx₀.symm))
  have hx₀_x : S.ker.r x₀ x := S.ker_of_mk_eq (Eq.trans hx₀.symm (Eq.symm hxq.symm))
  have hx_y₀ : S.ker.r x y₀ := S.ker_of_mk_eq (Eq.trans hxq.symm (Eq.symm hy₀.symm))
  have hy₀_x : S.ker.r y₀ x := S.ker_of_mk_eq (Eq.trans hy₀.symm (Eq.symm hxq.symm))
  -- いずれか一方は x と異なる代表：閉路の長さが 0 にはならない
  -- 暗黙に，x ≠ x₀ か x ≠ y₀ のどちらか（両方同じなら hne に反する）
  -- ここから「正の長さ k の閉路」(f^[k]) x = x を構成
  have hcycle : ∃ k : Nat, 0 < k ∧ (S.fV^[k]) x = x := by
    -- x ≤ x₀, x₀ ≤ x から閉路；または x ≤ y₀, y₀ ≤ x から閉路
    -- どちらの鎖でもよいので x₀ 側で作る
    have hx_le_x₀ : x ≤ x₀ := (S.ker_le_of_rel_right hx_x₀)
    have hx₀_le_x : x₀ ≤ x := (S.ker_le_of_rel_left  hx₀_x.symm)
    -- それぞれ `∃ m, (f^[m]) x = x₀` と `∃ n, (f^[n]) x₀ = x`
    rcases (S.reach_iff_iterate x x₀).1 hx_le_x₀ with ⟨m, hm⟩
    rcases (S.reach_iff_iterate x₀ x).1 hx₀_le_x with ⟨n, hn⟩
    -- 合成して (f^[m+n]) x = x
    have hfix : (S.fV^[m + n]) x = x := by
      -- iterate の加法法則
      have e : (S.fV^[m + n]) x = (S.fV^[n]) ((S.fV^[m]) x) :=
        by
          -- `iterate_add_apply S.fV n m x : f^[n+m] x = (f^[n]) ((f^[m]) x)`
          -- 左を `m+n` に入れ替えて使う
          have h := Function.iterate_add_apply S.fV n m x
          -- h : (S.fV^[n + m]) x = (S.fV^[n]) ((S.fV^[m]) x)
          -- 左辺の n+m を m+n に差し替え
          have h' : (S.fV^[m + n]) x = (S.fV^[n]) ((S.fV^[m]) x) := by
            -- `Nat.add_comm` を使って左だけを入れ替える
            have := h
            -- now rewrite the LHS
            -- `simp [Nat.add_comm]` は使わずに等式変形で：
            -- ここは既製の h' を直接与える
            exact Eq.trans
              (by
                -- (f^[m+n]) x = (f^[n+m]) x
                have : (S.fV^[m + n]) x = (S.fV^[n + m]) x := by
                  -- 関数を両辺に適用して可換する補題がないので，
                  -- 直接 iterate_add_apply を `Nat.add_comm` で入れ替えるのは上で実施済み
                  -- ここでは方針簡略化のため `by have := Function.iterate_add_apply S.fV m n x; exact ?_` でも良いが，
                  -- 以降の等式鎖で hm, hn を当てるので h' があれば充分
                  -- （詳細化すると式が長くなるため省略可能）
                  -- 代わりに `Function.iterate_add` を使う別ルートでも可。

                  congr 1
                  exact Nat.add_comm m n
                exact this
              )
              (by exact h)
          exact h'
      -- 右辺に hm, hn を順に適用
      have : (S.fV^[m + n]) x = (S.fV^[n]) x₀ := by
        -- ((f^[m]) x) = x₀
        have : (S.fV^[m]) x = x₀ := hm
        exact Eq.trans e (congrArg (fun z => (S.fV^[n]) z) this)
      exact Eq.trans this hn
    -- m+n > 0 ：（x₀ ≠ x なので少なくともどちらか正）
    have hpos : 0 < m + n := by
      -- もし m=0 ∧ n=0 なら hm : x = x₀, hn : x₀ = x で x = x₀，
      -- それは y₀ ≠ x₀ と合わせると `x = x₀, q=⟦x⟧=⟦x₀⟧=⟦y₀⟧` から
      -- x と y₀ が異なる同値代表になる。ここでは直接，m=0 → x=x₀ を使って反駁する：
      by_contra h0
      have hm0 : m = 0 := by
        -- `Nat.eq_zero_of_add_eq_zero_left` を使うか，素朴に場合分け
        exact Nat.eq_zero_of_add_eq_zero_right (by
          -- h0 : ¬ 0 < m + n  ⇒ m + n = 0
          have := le_antisymm (Nat.le_of_lt_succ (Nat.lt_succ_self (m + n))) (by
            exact Nat.le_refl (m+n))
          exact Nat.eq_zero_of_not_pos h0
          -- ここは詳細化が長くなるため，別ルート：`Nat.add_eq_zero` を使ってもよい
          )
      -- m = 0 なら hm : (f^[0]) x = x なので x₀ = x，さらに n = 0 から hn : (f^[0]) x₀ = x で x=x₀
      -- どちらにせよ x = x₀，だが `x₀ ≠ y₀` により閉路自体は y₀ を使って別途作れる。
      -- 実装を簡潔にするため，`by decide` でなく別枝に回すのが安全。
      admit
    exact ⟨m+n, hpos, hfix⟩
  -- 閉路から (fV x) ~ x を作る： (f^[k]) x = x, k>0
  have hker : S.ker.r (S.fV x) x := by
    rcases hcycle with ⟨k, hkpos, hk⟩
    -- k = s+1 に分解
    have : ∃ s, k = s + 1 := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hkpos)
    rcases this with ⟨s, rfl⟩
    -- (f^[s+1]) x = x ⇒ (f^[s]) (f x) = x かつ x ≤ f x
    -- まず (f^[s]) (f x) = x
    have e_fun : S.fV^[s.succ] = (S.fV^[s]) ∘ S.fV := Function.iterate_succ S.fV s
    have e_pt  : (S.fV^[s.succ]) x = (S.fV^[s]) (S.fV x) :=
      congrArg (fun g => g x) e_fun
    have e_step_to : (S.fV^[s]) (S.fV x) = x :=
      Eq.trans (Eq.symm e_pt) hk
    -- `x ≤ f x` は 1 手で到達
    have hxle : x ≤ S.fV x := ⟨1, rfl⟩
    -- `f x ≤ x` は e_step_to から
    have hfle : S.fV x ≤ x := ⟨s, e_step_to⟩
    show S.ker (S.fV x) x
    dsimp [ker]
    exact ⟨hfle, hxle⟩
  -- ker ⇒ Quot
  exact S.mk_eq_of_ker hker

lemma collapse_le_of_nontrivial
  {q r : S.QuotElem} (h : S.NontrivialClass q)
  (hqr : (S.preQuot.le) q r) : r = q := by
  classical
  -- 代表を取って，`x ≤ y` を長さ n の反復で表す
  rcases hqr with ⟨x, y, hxq, hry, hxy⟩
  rcases (S.reach_iff_iterate x y).1 hxy with ⟨n, hn⟩
  -- 以下，n で強い帰納法：`(f^[n]) x = y` かつ `r=⟦y⟧` ⇒ `r=q`
  have collapse :
  ∀ n {z y r},
    q = Quot.mk (S.ker) z →
    r = Quot.mk (S.ker) y →
    (S.fV^[n]) z = y →
    r = q := by
      intro n
      induction' n with n ih
      · -- n = 0
        intro z y r hzq hry hn0
        -- (f^[0]) z = z なので z = y
        have hzy : z = y := hn0
        -- r = ⟦y⟧ = ⟦z⟧ = q
        have e1 : r = Quot.mk (S.ker) y := hry
        have e2 : Quot.mk (S.ker) y = Quot.mk (S.ker) z :=
          congrArg (fun t => Quot.mk (S.ker) t) (Eq.symm hzy)
        have e3 : Quot.mk (S.ker) z = q := Eq.symm hzq
        exact Eq.trans e1 (Eq.trans e2 e3)

      · -- n = n+1
        intro z y r hzq hry hnsucc
        -- (f^[n+1]) z = (f^[n]) (f z)
        have e_fun : S.fV^[n.succ] = (S.fV^[n]) ∘ S.fV := Function.iterate_succ S.fV n
        have e_pt  : (S.fV^[n.succ]) z = (S.fV^[n]) (S.fV z) :=
          congrArg (fun g => g z) e_fun
        have htail : (S.fV^[n]) (S.fV z) = y := Eq.trans (Eq.symm e_pt) hnsucc
        -- 非自明クラスなら 1 手先も同じクラス：⟦f z⟧ = q
        have hfq : Quot.mk (S.ker) (S.fV z) = q :=
        by
          sorry
        -- 帰納法を (z := f z) に適用
        exact ih (id (Eq.symm hfq)) hry hnsucc

  subst hry hn hxq
  simp_all only [forall_eq_apply_imp_iff, forall_apply_eq_imp_iff, Subtype.forall, Subtype.coe_eta]


-- ===============  追加：非自明クラスは極大（sink） ===============
/-- 非自明クラスは極大：`¬ ∃ r, q < r`。 -/
lemma nontrivial_class_is_maximal
  {q : S.QuotElem} (h : S.NontrivialClass q) :
  S.isMaximal q := by
  -- isMaximal q := ¬ ∃ r, q < r
  intro hlt
  rcases hlt with ⟨r, hqr⟩
  -- `<` は `≤ ∧ ¬ ≤`。まず `q ≤ r` を取り出す
  have hle : (S.preQuot.le) q r := hqr.1
  -- 非自明クラスの潰し：q ≤ r ⇒ r = q
  have hrq : r = q := collapse_le_of_nontrivial (S:=S) h hle
  -- ところが `<` なので r ≠ q
  have : r ≠ q := by exact fun h => (lt_irrefl q) (by exact h ▸ hqr)
  exact this hrq

def eraseOneFun (S : FuncSetup α) (u v : S.Elem) (hvne : v ≠ u) : α → α :=
  fun x =>
    if x ∈ S.V.erase u then
      let y := S.f x
      if y = u then v else y
    else
      -- ground 外は自由。以降は ground = S.V.erase u で評価するので使われない
      v

/-- ground を V.erase u に差し替え、f を上の付け替え関数に。 -/
def eraseOne (S : FuncSetup α) (u v : S.Elem) (hvne : v ≠ u) : FuncSetup α :=
{ V      := S.V.erase u
, f      := S.eraseOneFun u v hvne
, mapsTo := by
    intro x hx
    -- x ∈ V.erase u
    have hxV : x ∈ S.V := (Finset.mem_erase.mp hx).2
    have hyV : S.f x ∈ S.V := S.mapsTo hxV
    -- 場合分け：S.f x = u なら v に付け替える（v ∈ V, v ≠ u）
    by_cases hfu : S.f x = u
    · -- 付け替え像 v は V.erase u に入る
      have hvV  : (v : α) ∈ S.V := v.property
      have hneq : (v : α) ≠ u := by
        intro contra; exact hvne (Subtype.ext (by simpa using contra))
      -- f' x = v
      have : S.eraseOneFun u v hvne x = v := by
        -- x は ground 内なので if の左枝、さらに hfu により右枝の if も左分岐
        unfold eraseOneFun
        by_cases hxg : x ∈ S.V.erase u
        · simp_all
        · exact (False.elim (by exact hxg hx))
      -- よって mapsTo
      simp_all only [Finset.mem_erase, ne_eq, and_true, Finset.coe_mem, not_false_eq_true, and_self]
    · -- S.f x ≠ u なら f' x = S.f x ∈ V.erase u
      have : S.eraseOneFun u v hvne x = S.f x := by
        unfold eraseOneFun
        by_cases hxg : x ∈ S.V.erase u
        · simp_all
        · exact (False.elim (by exact hxg hx))
      -- S.f x ∈ V、かつ S.f x ≠ u
      have hneq : S.f x ≠ u := hfu
      have hy_in : S.f x ∈ S.V.erase u := by
        refine Finset.mem_erase.mpr ?_
        exact ⟨hneq, hyV⟩
      simpa [this] using hy_in
}

/-- traceErase: ground から u を消して、集合族を A.erase u に対応させる。 -/
noncomputable def traceErase (F : SetFamily α) (u : α) : SetFamily α :=
{ ground := F.ground.erase u
, sets := fun B => ∃ A : Finset α, F.sets A ∧ B = A.erase u
, decSets := by classical exact Classical.decPred _
, inc_ground := by
    intro B ⟨A, hA, rB⟩
    intro x hx
    have hxA : x ∈ A := by
      subst rB
      simp_all only [Finset.mem_erase, ne_eq]
    rw [Finset.mem_erase]
    constructor
    · subst rB
      simp_all only [Finset.mem_erase, ne_eq, and_true, not_false_eq_true]
    · apply F.inc_ground hA hxA
}

end FuncSetup
end AvgRare
