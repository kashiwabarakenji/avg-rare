import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Basic
import Mathlib.Logic.Function.Iterate
import AvgRare.Basics.SetFamily   -- 依存を薄く保ちつつ将来の接続を意識
import LeanCopilot

/-
FuncSetup.lean — 機能的前順序（functional preorder）のセットアップ（論文 §2）

このファイルでは、有限台集合 `V : Finset α` と「V 上に閉じた」写像
  f : {x // x ∈ V} → {x // x ∈ V}
から誘導される前順序を、被覆関係 `⋖` とその反射推移閉包 `≤` として定義します。

論文で使う主な言明（Lemma 2.2, 2.4 など）は他ファイルの準備が整ってから埋めます。

注意:
- ここでは `Preorder` の typeclass は使いません（純粋に関係で進めます）。
- 有限性は `V : Finset α` を介して担保し、要素型は `Elem := {x // x ∈ V}` の部分型で扱います。
- `simpa using` は用いません。必要に応じて `simp` / `simp_all` を使います。
-/

universe u

open scoped BigOperators
open Classical

namespace AvgRare

variable {α : Type u} [DecidableEq α]

/-- 機能的前順序の“入力データ”。`ground`（有限台集合）と，
    その上に閉じた自己写像 `f` を与える。 -/
structure FuncSetup (α : Type u)  [DecidableEq α] where
  ground : Finset α
  nonempty : Nonempty ground  --ground.Nonemptyの方がいいそう。
  f      : {x // x ∈ ground} → {y // y ∈ ground}

--namespace FuncSetup
namespace FuncSetup

variable (S : FuncSetup α)

--何の意味がある？
--@[simp] lemma ground_def : S.ground = S.ground := rfl

/-- 台集合の要素型（部分型）。 -/
abbrev Elem := {x : α // x ∈ S.ground}

/-
--現状使ってない
@[simp] lemma mem_ground_coe (x : S.Elem) : x.1 ∈ S.ground := x.2
-/

--instance instDecidableEqElem : DecidableEq S.Elem := inferInstance

/-- 被覆関係：`x ⋖ y` iff `f x = y`。 -/
def cover (x y : S.Elem) : Prop := S.f x = y

/-- 前順序：被覆の反射推移閉包。 -/
def le (x y : S.Elem) : Prop := Relation.ReflTransGen S.cover x y

/-- 記法：`x ≤ₛ y` / `x ⋖ₛ y` -/
--あんまりうまくいってないかも。
scoped infix:50 " ≤ₛ " => FuncSetup.le
scoped infix:50 " ⋖ₛ " => FuncSetup.cover

/-- 反射。 -/
lemma le_refl (x : S.Elem) : S.le x x := by
  -- Relation.ReflTransGen.refl
  exact Relation.ReflTransGen.refl

/-- 推移。 -/
lemma le_trans {x y z : S.Elem} (hxy : S.le x y) (hyz : S.le y z) : S.le x z := by
  -- Relation.ReflTransGen.trans
  exact Relation.ReflTransGen.trans hxy hyz

--isPosetと同じ条件
def has_le_antisymm  : Prop :=
∀ {x y : S.Elem}, (S.le x y) → (S.le y x) → x = y

--後半の議論で参照。
def isPoset : Prop :=
  has_le_antisymm S

/-- 被覆から 1 ステップで `≤`。 -/
lemma cover_to_le {x y : S.Elem} (h : S.cover x y) : S.le x y := by
  -- Relation.ReflTransGen.single
  exact Relation.ReflTransGen.single h

/-- 同じ元からの `cover` の像は一意 -/
--下で使われている。
lemma cover_out_unique (S : FuncSetup α){u y z : S.Elem} :
  S.cover u y → S.cover u z → y = z := by
  intro hy hz

  dsimp [FuncSetup.cover] at hy hz
  -- hy : S.f u = y, hz : S.f u = z
  have h' := hz
  -- 左辺 `S.f u` を hy で置換すると `y = z`
  -- （simpa を使わず、書き換え＋ exact）
  rw [hy] at h'
  exact h'


/-- 「反復で到達できる」写像反復。 -/
--traceFunctionalでそとでつかっているみたい。
def iter (k : Nat) : S.Elem → S.Elem :=
  Nat.iterate S.f k

/-
@[simp] lemma iter_zero (x : S.Elem) : S.iter 0 x = x := by
  -- Nat.iterate f 0 = id
  unfold iter
  simp

--使える場面はあるかもしれないが現状使ってない。
@[simp] lemma iter_succ (k : Nat) (x : S.Elem) :
    S.iter (k+1) x = S.f (S.iter k x) := by
  -- Nat.iterate.succ
  unfold iter
  simp
  exact Function.iterate_succ_apply' S.f k x
-/

/-
--その他、このあたりはどこで使う？

/- 便利：基の α への射影。 -/
def toGround (x : S.Elem) : α := x.1
@[simp] lemma toGround_mk {x : α} {hx : x ∈ S.ground} :
    S.toGround ⟨x, hx⟩ = x := rfl

/-- `f` の基底 α 成分（必要ならデバッグ用）。 -/
def fBase (x : S.Elem) : α := (S.f x).1
@[simp] lemma fBase_def (x : S.Elem) : S.fBase x = (S.f x).1 := rfl
-/

/-
/-- 「グラフ的」表現のための有向辺集合。 -/
def edges : Finset (S.Elem × S.Elem) :=
  S.ground.attach.image (fun x => (x, S.f x))

lemma edges_mem {e : S.Elem × S.Elem} :
    e ∈ S.edges ↔ ∃ x : S.Elem, e = (x, S.f x) := by
  classical
  unfold edges
  constructor
  · intro h
    rcases Finset.mem_image.mp h with ⟨x, hx, rfl⟩
    -- x ∈ ground.attach は自明
    simp_all
  · rintro ⟨x, rfl⟩
    refine Finset.mem_image.mpr ?_
    refine ⟨x, ?_, rfl⟩
    simp  -- x ∈ ground.attach
-/

/-- ground の元 `x : α` とその証明から `S.Elem` を作るユーティリティ。 -/
def toElem! {x : α} (hx : x ∈ S.ground) : S.Elem := ⟨x, hx⟩

@[simp] lemma toElem!_val {x : α} (hx : x ∈ S.ground) :
    (S.toElem! hx).1 = x := rfl
@[simp] lemma toElem!_mem {x : α} (hx : x ∈ S.ground) :
    (S.toElem! hx).2 = hx := rfl

-- toElem! の往復（既存なら @[simp] を付けると後の書き換えが楽）。
--使っている。
@[simp] lemma toElem!_coe (S : FuncSetup α) (x : S.Elem) :
    S.toElem! x.property = x := by
  cases x with
  | mk x hx => rfl

-- S.Elem の不等号から underlying へ
--一箇所使っている。
lemma coe_ne_of_ne {S : FuncSetup α} {x y : S.Elem} (h : x ≠ y) :
    (x : α) ≠ (y : α) := by
  intro hxy
  apply h
  apply Subtype.ext
  exact hxy

/-
/-- `f` の像は常に ground の中。 -/
@[simp] lemma f_mem_ground (x : S.Elem) : (S.f x).1 ∈ S.ground := (S.f x).2
-/

/-! ## 2) 「機能性」：出次数高々 1 -/

-- 極大関係

/-- 極大：`x` の上は全部 `x` に戻る（前順序版）。 -/
def maximal (x : S.Elem) : Prop :=
  ∀ ⦃y⦄, S.le x y → S.le y x

@[simp] lemma maximal_iff (x : S.Elem) :
    S.maximal x ↔ (∀ ⦃y⦄, S.le x y → S.le y x) := Iff.rfl

/-- `f u = u` なら `u` は極大（反対称性不要） -/
--使われている。
lemma maximal_of_fixpoint  (S : FuncSetup α){u : S.Elem} (huu : S.cover u u) :
  S.maximal u := by
  intro v huv
  -- 「u から到達できるのは u のみ」を反復閉包で帰納
  have reach_eq : ∀ w, S.le u w → w = u := by
    intro w hw
    induction hw with
    | @refl =>
        rfl
    | @tail w x hw ih hwx =>
        -- `hw : u ≤ w`, `hwx : cover w x`, 帰納法の仮定 `ih : w = u`
        have hux : S.cover u x := by
          cases ih
          exact congrArg S.f (id (Eq.symm hwx))
        have hx : x = u := by
          exact cover_out_unique S hux huu
        exact hx
  have hveq : v = u := reach_eq v huv
  cases hveq
  exact Relation.ReflTransGen.refl


--同値類関係

/-- 同値関係：`x ∼ y` iff `x ≤ y ∧ y ≤ x`。 -/
def sim (x y : S.Elem) : Prop := S.le x y ∧ S.le y x

/-- `sim` は同値関係。 -/
lemma sim_refl (x : S.Elem) : S.sim x x := by
  constructor <;> exact S.le_refl x

lemma sim_symm {x y : S.Elem} (h : S.sim x y) : S.sim y x := by
  constructor
  · exact h.2
  · exact h.1

lemma sim_trans {x y z : S.Elem} (hxy : S.sim x y) (hyz : S.sim y z) : S.sim x z := by
  constructor
  · exact S.le_trans hxy.1 hyz.1
  · exact S.le_trans hyz.2 hxy.2

/-- `sim` を `Setoid` に。 -/
--現状使ってない
def simSetoid : Setoid S.Elem where
  r := S.sim
  iseqv := ⟨S.sim_refl, S.sim_symm, S.sim_trans⟩



/-- 「同値類が非自明（別の点がある）」の実用形。 -/
def nontrivialClass {α : Type u} [DecidableEq α] (S : FuncSetup α) (x : S.Elem) : Prop :=
  ∃ y : S.Elem, y ≠ x ∧ S.sim x y

lemma fixed_point_unique {α : Type u} [DecidableEq α] (S : FuncSetup α) (u : S.Elem)
    (h_fixed : S.f u = u) {v : S.Elem} (h_le : S.le u v) : u = v := by
  induction h_le with
  | refl => rfl
  | tail hb h_cover ih =>
    rename_i b c
    have : S.f b = c:= by exact h_cover
    rw [ih] at h_fixed
    rw [h_fixed] at this
    rw [←ih] at this
    exact this

/-- 非自明同値類に属する `u` は自己固定点ではない（`f u ≠ u`）。 -/
--2箇所で使っている。
lemma f_ne_of_nontrivialClass (S : FuncSetup α) {u : S.Elem}
    (h : S.nontrivialClass u) : S.f u ≠ u := by
  rcases h with ⟨y, hy_ne, hy_sim⟩
  intro hfix -- 仮に等しいとすると
  -- u ≤ y から `fixed_point_unique` で u = y
  have : u = y := S.fixed_point_unique u hfix hy_sim.1
  exact hy_ne this.symm

/-! ## 1) 功能的前順序 S から ground 上の関係を作る -/

--このあたりはleOnに関すること。Elemに関する順序？
/-- `leOn S y x` : ground 上の要素 `y, x : α` について，
S の部分型 `S.Elem` 上の `S.le ⟨y,hy⟩ ⟨x,hx⟩` が成り立つことを「存在」で述べる。 -/
def leOn (S : FuncSetup α) (y x : α) : Prop :=
  ∃ (hy : y ∈ S.ground) (hx : x ∈ S.ground),
      FuncSetup.le S ⟨y, hy⟩ ⟨x, hx⟩

--結構使っている
lemma leOn_iff_subtype (S : FuncSetup α) {a b : α}
  (ha : a ∈ S.ground) (hb : b ∈ S.ground) :
  S.leOn a b ↔ S.le ⟨a, ha⟩ ⟨b, hb⟩ := by
  constructor
  · rintro ⟨ha', hb', h⟩
    -- 証明部の差だけなので書換えで揃える
    have ea : (⟨a, ha'⟩ : S.Elem) = ⟨a, ha⟩ := Subtype.ext (rfl)
    have eb : (⟨b, hb'⟩ : S.Elem) = ⟨b, hb⟩ := Subtype.ext (rfl)
    cases ea; cases eb; exact h
  · intro h; exact ⟨ha, hb, h⟩

lemma leOn_refl (S : FuncSetup α) {x : α} (hx : x ∈ S.ground) :
  S.leOn x x :=
by
  exact ⟨hx, hx, Relation.ReflTransGen.refl⟩

lemma leOn_trans (S : FuncSetup α) {y x z : α}
  (h₁ : S.leOn y x) (h₂ : S.leOn x z) :
  S.leOn y z :=
by
  rcases h₁ with ⟨hy, hx, h_yx⟩
  rcases h₂ with ⟨hx', hz, h_xz⟩
  -- 中点 x の証明部を揃える（値は同じなので Subtype.ext rfl）
  have h_yx' : S.le ⟨y, hy⟩ ⟨x, hx'⟩ := by
    -- ゴール側の第2引数を ⟨x,hx⟩ に書き換えてから h_yx を使う
    have e : (⟨x, hx⟩ : S.Elem) = ⟨x, hx'⟩ := Subtype.ext (by rfl)
    -- 目標を書換え
    -- `cases e` で ⟨x,hx'⟩ を ⟨x,hx⟩ に統一
    cases e
    exact h_yx
  -- S.le の推移律（= ReflTransGen.trans）で連結
  have h_yz : S.le ⟨y, hy⟩ ⟨z, hz⟩ :=
    Relation.ReflTransGen.trans h_yx' h_xz
  exact ⟨hy, hz, h_yz⟩

--leOn_iff_subtypeと同じ
lemma leOn_iff (S : FuncSetup α)
  {a b : α} (hb : b ∈ S.ground) (ha : a ∈ S.ground) :
  S.leOn b a ↔ S.le ⟨b, hb⟩ ⟨a, ha⟩ := by
  -- ここは S の定義に合わせて既存の補題名を使うか、`rfl` 展開で書いてください。
  -- 例えば `def leOn (x y : α) := ∃ hx hy, S.le ⟨x,hx⟩ ⟨y,hy⟩` なら
  --   ↔ の両方向は `⟨hb, ha⟩` で直ちに取れます。
  unfold FuncSetup.leOn
  simp_all only [exists_true_left]

-- サブタイプ上の比較と ground 上の比較の橋渡し
-- （S.le が「S.leOn をサブタイプへ持ち上げたもの」になっていれば定義等号で証明できます）
@[simp] lemma le_iff_leOn_val
    (S : FuncSetup α) (x y : S.Elem) :
    S.le x y ↔ S.leOn (x : α) (y : α) := by
    obtain ⟨val, property⟩ := x
    obtain ⟨val_1, property_1⟩ := y
    simp_all only
    apply Iff.intro
    · intro a
      dsimp [FuncSetup.leOn]
      simp_all only [exists_const]
    · intro a
      induction a
      simp_all only [exists_true_left]

--------------------

noncomputable def coeFinset (S : FuncSetup α) (I : Finset S.Elem) : Finset α :=
  I.image (fun x => (x.1 : α))

noncomputable def liftFinset
  (S : FuncSetup α) (J : Finset α) (hJ : J ⊆ S.ground) : Finset S.Elem :=
  J.attach.map
    ⟨(fun t => (⟨t.1, hJ t.2⟩ : S.Elem)),
     by
       intro u v h; cases u; cases v; cases h; rfl⟩

@[simp] lemma mem_coeFinset (S : FuncSetup α) (I : Finset S.Elem) {x : α} :
  x ∈ S.coeFinset I ↔ ∃ y ∈ I, (y : α) = x := by
  classical
  constructor
  · intro hx
    rcases Finset.mem_image.mp hx with ⟨y, hyI, rfl⟩
    exact ⟨y, hyI, rfl⟩
  · rintro ⟨y, hyI, rfl⟩
    exact Finset.mem_image.mpr ⟨y, hyI, rfl⟩

@[simp] lemma mem_coeFinset_val_iff
    (S : FuncSetup α) {I : Finset S.Elem} {a : α} :
    a ∈ S.coeFinset I ↔ ∃ z : S.Elem, z ∈ I ∧ (z : α) = a := by
  constructor
  · intro ha
    rcases Finset.mem_image.mp ha with ⟨z, hzI, rfl⟩
    exact ⟨z, hzI, rfl⟩
  · rintro ⟨z, hzI, rfl⟩
    exact Finset.mem_image.mpr ⟨z, hzI, rfl⟩

@[simp] lemma mem_coeFinset_iff
    (S : FuncSetup α) {I : Finset S.Elem} {a : α} (ha : a ∈ S.ground) :
    a ∈ S.coeFinset I ↔ ⟨a, ha⟩ ∈ I := by
  constructor
  · intro haI
    rcases (mem_coeFinset_val_iff (S:=S)).mp haI with ⟨z, hzI, hz⟩
    -- `z : S.Elem` と `z.1 = a` から `z = ⟨a,ha⟩` を得る
    have : z = ⟨a, ha⟩ := Subtype.ext (by simpa [Subtype.ext] using congrArg id hz)
    subst this
    simp_all only [FuncSetup.mem_coeFinset, Subtype.exists, exists_and_right, exists_eq_right, exists_const]
  · intro hz
    -- 逆向きは像の定義そのもの
    exact Finset.mem_image.mpr ⟨⟨a, ha⟩, hz, rfl⟩

@[simp] lemma mem_liftFinset_iff
  (S : FuncSetup α) {J : Finset α} {hJ : J ⊆ S.ground} {z : S.Elem} :
  z ∈ S.liftFinset J hJ ↔ (z : α) ∈ J := by
  classical
  unfold FuncSetup.liftFinset
  constructor
  · intro hz
    rcases Finset.mem_map.mp hz with ⟨t, ht, hmap⟩
    -- t : {a // a ∈ J}, ht : t ∈ J.attach, hmap : ⟨t.1, hJ t.2⟩ = z
    -- よって (z : α) = t.1 ∈ J
    have : (z : α) = t.1 := by cases z; cases t; cases hmap; rfl
    exact this ▸ t.2
  · intro hz
    refine Finset.mem_map.mpr ?_
    refine ⟨⟨z.1, hz⟩, ?_, ?_⟩
    · exact Finset.mem_attach _ _
    · cases z; rfl

/-- 目的の補題：`coeFinset ∘ liftFinset = id` （`J ⊆ ground` が前提） -/
@[simp] lemma coeFinset_liftFinset
  (S : FuncSetup α) (J : Finset α) (hJ : J ⊆ S.ground) :
  S.coeFinset (S.liftFinset J hJ) = J := by
  classical
  apply Finset.ext
  intro a
  constructor
  · intro ha
    -- a ∈ coeFinset (lift J) → ∃ z ∈ lift J, z.1 = a → a ∈ J
    rcases (mem_coeFinset_val_iff S).1 ha with ⟨z, hzLift, hz⟩
    -- z ∈ lift ↔ z.1 ∈ J
    have : (z : α) ∈ J := (mem_liftFinset_iff S).1 hzLift
    -- z.1 = a で書き換え
    subst hz
    simp_all only [mem_liftFinset_iff, FuncSetup.mem_coeFinset, Subtype.exists, exists_and_left, exists_prop,
    exists_eq_right_right]

  · intro haJ
    -- a ∈ J → ある z=⟨a, hJ haJ⟩ が lift に入り、その像に a が入る
    have hz : (⟨a, hJ haJ⟩ : S.Elem) ∈ S.liftFinset J hJ :=
      (mem_liftFinset_iff S).2 haJ
    exact (mem_coeFinset_val_iff S).2 ⟨⟨a, hJ haJ⟩, hz, rfl⟩



--------

/-! ## 3) Lemma 3.1：maximal ⇒ rare -/

--Monotonicity.leanで利用。
lemma sim_of_maximal_above_class
    (S : FuncSetup α) {u x y : S.Elem}
    (hmax : S.maximal u)
    (hyU : S.sim y u) (hyx : S.le y x) :
    S.sim x u := by
  -- `u ≤ x` と `x ≤ u` の両方を示せば良い
  constructor
  · -- まず `u ≤ x`
    have hux : S.le u x := S.le_trans hyU.2 hyx
    -- 最大性：`u ≤ x → x ≤ u`
    exact hmax hux
  · -- つぎに `u ≤ x` は上で得た `hux`
    exact S.le_trans hyU.2 hyx

/-- ground 上の要素型 `S.Elem` における `u` の同値類（Finset 版）。 -/
noncomputable def simClassElem (S : FuncSetup α) (u : S.Elem) : Finset S.Elem :=
  S.ground.attach.filter (fun v => S.sim v u)

/-- `α` 側へ戻した同値類（`idealFamily : SetFamily α` が扱うのはこちら）。 -/
noncomputable def simClass (S : FuncSetup α) (u : S.Elem) : Finset α :=
  (S.simClassElem u).image (Subtype.val)

/-- `v ∈ simClassElem u` の判定は「ちょうど `S.sim v u`」。 -/
@[simp] lemma mem_simClassElem
    (S : FuncSetup α) (u : S.Elem) (v : S.Elem) :
    v ∈ S.simClassElem u ↔ S.sim v u := by
  classical
  unfold simClassElem
  constructor
  · intro hv
    have hv' := Finset.mem_filter.mp hv
    exact hv'.2
  · intro hsim
    have hvattach : v ∈ S.ground.attach := by
      -- `attach` の要素は（証明部分はどうであれ）常に自分自身が所属します
      -- `simp` だけで出ます
      simp_all only [Finset.mem_attach]
    exact Finset.mem_filter.mpr ⟨hvattach, hsim⟩

/-- `a ∈ simClass u` の判定。 -/
lemma mem_simClass_iff
    (S : FuncSetup α) (u : S.Elem) {a : α} :
    a ∈ S.simClass u ↔ ∃ (ha : a ∈ S.ground), S.sim ⟨a, ha⟩ u := by
  classical
  unfold simClass
  constructor
  · intro haimg
    rcases Finset.mem_image.mp haimg with ⟨v, hv, rfl⟩

    have hsim : S.sim v u := (S.mem_simClassElem u v).1 hv
    exact ⟨v.property, hsim⟩
  · intro h
    rcases h with ⟨ha, hsim⟩
    let v : S.Elem := ⟨a, ha⟩
    have hv : v ∈ S.simClassElem u := (S.mem_simClassElem u v).2 hsim
    exact Finset.mem_image.mpr ⟨v, hv, rfl⟩

----ここからIdeal関連

/-- S に対応する order-ideal family を ground 型 `α` 上の `SetFamily` として与える。 -/
--FuncSetupからidealFaimilyが定理できると便利なので定義だけ与える。
--と思ったが、FuncSetupでIdealを使ったものを集めたファイルがないので、分離するとよいかも。
noncomputable def idealFamily (S : FuncSetup α) : SetFamily α :=
  SetFamily.orderIdealFamily (le := leOn S) (V := S.ground)

@[simp] lemma sets_iff_isOrderIdeal
    (S : FuncSetup α) {I : Finset α} :
    (S.idealFamily).sets I ↔ SetFamily.isOrderIdealOn (S.leOn) S.ground I := Iff.rfl

/-- `S.ground` は `idealFamily` の edge（＝理想）である。 -/
lemma ground_mem_ideal_edge (S : FuncSetup α) :
  S.ground ∈ (S.idealFamily).edgeFinset := by
  classical
  -- `S.ground` が order ideal であることを直展開で示す
  have hIdeal : SetFamily.isOrderIdealOn (S.leOn) S.ground S.ground := by
    dsimp [SetFamily.isOrderIdealOn]
    constructor
    · intro x hx; exact hx
    · intro x hx y hy _; exact hy
  -- sets ↔ isOrderIdealOn で写してから、edgeFinset へ
  have hSets : (S.idealFamily).sets S.ground :=
    (S.sets_iff_isOrderIdeal).2 hIdeal
  exact (SetFamily.mem_edgeFinset_iff_sets (F := S.idealFamily) (A := S.ground)).2 hSets

/-- `∅` も `idealFamily` の edge である。 -/
lemma empty_mem_ideal_edge (S : FuncSetup α) :
  (∅ : Finset α) ∈ (S.idealFamily).edgeFinset := by
  classical
  -- 空集合は自明に order ideal
  have hIdeal : SetFamily.isOrderIdealOn (S.leOn) S.ground (∅ : Finset α) := by
    dsimp [SetFamily.isOrderIdealOn]
    constructor
    · intro x hx; cases hx
    · intro x hx; cases hx
  have hSets : (S.idealFamily).sets (∅ : Finset α) :=
    (S.sets_iff_isOrderIdeal).2 hIdeal
  exact (SetFamily.mem_edgeFinset_iff_sets (F := S.idealFamily) (A := ∅)).2 hSets

/-- `idealFamily` の `edgeFinset` は空でない。 -/
lemma ideal_edge_nonempty (S : FuncSetup α) :
  (S.idealFamily).edgeFinset.Nonempty := by
  classical
  exact ⟨S.ground, ground_mem_ideal_edge S⟩

/-- よって `numHyperedges ≥ 1`。 -/
lemma numHyperedges_ge_one (S : FuncSetup α) :
  1 ≤ (S.idealFamily).numHyperedges := by
  classical
  -- `numHyperedges = card edgeFinset`
  have hpos : 0 < (S.idealFamily).edgeFinset.card :=
    Finset.card_pos.mpr (ideal_edge_nonempty S)
  -- `0 < n` から `1 ≤ n`
  exact Nat.succ_le_of_lt hpos

/-- `ground ≠ ∅` なら、`∅` と `ground` がどちらも edge でしかも異なるので card ≥ 2。 -/
lemma numHyperedges_ge_two
  (S : FuncSetup α) (hne : S.ground.Nonempty) :
  2 ≤ (S.idealFamily).numHyperedges := by
  classical
  let P : Finset (Finset α) := insert S.ground ({∅} : Finset (Finset α))
  have hPsub : P ⊆ (S.idealFamily).edgeFinset := by
    intro A hA
    rcases Finset.mem_insert.mp hA with rfl | hA0
    · exact ground_mem_ideal_edge S
    · have : A = (∅ : Finset α) := Finset.mem_singleton.mp hA0; subst this
      exact empty_mem_ideal_edge S
  have hg_ne : S.ground ≠ (∅ : Finset α) :=
    Finset.nonempty_iff_ne_empty.mp hne
  have hPcard : 2 = P.card := by
    have : S.ground ∉ ({∅} : Finset (Finset α)) := by
      intro h; exact hg_ne (Finset.mem_singleton.mp h)
    simp_all only [ne_eq, Finset.mem_singleton, not_false_eq_true, Finset.card_insert_of_notMem, Finset.card_singleton,
    Nat.reduceAdd, P]
  -- `card_le_card` で押す
  have := Finset.card_le_card hPsub
  simpa [SetFamily.numHyperedges, hPcard] using this

lemma simClass_subset_of_contains
    (S : FuncSetup α) {u : S.Elem} {I : Finset α}
    (hI : (S.idealFamily).sets I) (huI : u.1 ∈ I) :
    S.simClass u ⊆ I := by
  classical
  -- isOrderIdealOn に展開
  have hIdeal : SetFamily.isOrderIdealOn (S.leOn) S.ground I := by
    -- `[simp] lemma sets_iff_isOrderIdeal` が `Iff.rfl` なので書換えだけで OK
    -- `rw` で潰す（`simpa using` は使わない）
    change SetFamily.isOrderIdealOn (S.leOn) S.ground I
    exact (S.sets_iff_isOrderIdeal).1 hI
  -- 以降：U の元 a を任意に取り、I に属することを示す
  intro a haU
  rcases (S.mem_simClass_iff u).1 haU with ⟨ha, hsim⟩
  -- `a ≤ u` を取り出す
  have h_le : S.le ⟨a, ha⟩ u := hsim.1
  -- `leOn a u.1` に持ち上げ
  have h_leOn : S.leOn a u.1 := by
    -- `leOn_iff_subtype` を使う
    have : S.leOn a u.1 ↔ S.le ⟨a, ha⟩ u :=
      S.leOn_iff_subtype (a := a) (b := u.1) ha u.property
    exact this.mpr h_le
  -- isOrderIdealOn の下方閉により `a ∈ I`
  have hI_sub : I ⊆ S.ground := hIdeal.1
  have hxI : u.1 ∈ I := huI
  --have hxV : u.1 ∈ S.ground := hI_sub hxI
  -- 下方閉：`x∈I, y∈V, leOn y x → y∈I`
  have := hIdeal.2 (x := u.1) hxI (y := a) (by exact ha) h_leOn
  exact this



--下で使っている。単なるidealが下に閉じているという性質のleOn版か。今はそとから参照されてないので、private。
private lemma mem_of_le_of_mem_inIdeal
  (S : FuncSetup α) {I : Finset S.Elem}
  (hIdeal : SetFamily.isOrderIdealOn S.leOn S.ground (S.coeFinset I))
  {x y : S.Elem}
  (hleOn : S.leOn (x : α) (y : α)) (hy : y ∈ I) :
  x ∈ I := by
  have hyGround : (y : α) ∈ S.ground := y.property
  -- y∈I → (y:α)∈coeFinset I
  have hyIn : (y : α) ∈ S.coeFinset I :=
    (S.mem_coeFinset_iff (I := I) (a := y) hyGround).2 hy
  -- downward closed で (x:α)∈coeFinset I
  have hxIn : (x : α) ∈ S.coeFinset I :=
    hIdeal.2 (x := (y : α)) hyIn (y := (x : α)) (by exact x.property) hleOn
  -- 逆向きで x∈I に戻す
  have : ∃ z ∈ I, (z : α) = (x : α) := (S.mem_coeFinset_val_iff).1 hxIn
  rcases this with ⟨z, hzI, hz⟩
  cases z with
  | mk z hzground =>
    cases x with
    | mk x hxground =>
      cases hz
      simpa using hzI

--variable (S : FuncSetup α) (x y : S.Elem)
--variable (S : FuncSetup α) [DecidableRel (S.le)]
noncomputable def Iy (S : FuncSetup α) (y : S.Elem) : Finset S.Elem :=
  S.ground.attach.filter (fun z : S.Elem => S.le z y)

-- 目標： hb : b ∈ S.ground, hleOn : S.leOn b a, haGround : a ∈ S.coeFinset Iy
--       から b ∈ S.coeFinset Iy を出す
--xとyに大小関係があれば、yを含むidealは、xも含む。重要補題。
--基礎補題を集めたファイルを作って分離してもよい。

lemma le_iff_forall_ideal_mem
  (S : FuncSetup α) (x y : S.Elem) :
  S.le x y ↔
    (∀ I : Finset S.Elem,
      (S.idealFamily).sets (S.coeFinset I) → y ∈ I → x ∈ I) := by
  constructor
  · -- (→) : `x ≤ y` なら、任意のイデアル I で `y ∈ I → x ∈ I`
    intro hxy I hI hyI
    -- イデアルの定義は α 上の order-ideal なので、`coeFinset I` に持ち上げる
    have hIdeal :
        SetFamily.isOrderIdealOn (S.leOn) S.ground (S.coeFinset I) :=
      (S.sets_iff_isOrderIdeal).1 hI
    -- y ∈ I から y.1 ∈ coeFinset I
    have hy' : (y.1 : α) ∈ S.coeFinset I := by

      exact (mem_coeFinset_iff S (I:=I) (a:=y.1) (ha:=y.2)).2 hyI
    -- order-ideal のダウンワード閉包で x.1 ∈ coeFinset I を得る
    have hx' : (x.1 : α) ∈ S.coeFinset I := by
      -- `S.leOn` は α 上の関係。`x y : S.Elem` からは `S.leOn x.1 y.1`
      have hleOn : S.leOn x.1 y.1 := by exact (S.le_iff_leOn_val x y).mp hxy--S.le_to_leOn hxy
      simp_all only [ FuncSetup.mem_coeFinset, Subtype.exists, exists_and_right,
         exists_eq_right, Subtype.coe_eta, Finset.coe_mem, exists_const]
      exact S.mem_of_le_of_mem_inIdeal hIdeal hleOn  hyI

    -- もう一度 subtype に戻す
    simp_all only [FuncSetup.mem_coeFinset, Subtype.exists, exists_and_right,
    exists_eq_right, Subtype.coe_eta, Finset.coe_mem, exists_const]

  · -- (←) : 逆向き。`Iy` を y 以下の元の集合として取る
    intro hAll
    -- `Iy := { z ∈ ground | z ≤ y }` を Finset S.Elem で
    let Iy : Finset S.Elem :=
      S.ground.attach.filter (fun z => S.le z y)
    have hyIy : y ∈ Iy := by
      -- y は ground にあり、かつ y ≤ y
      have hy₀ : y ∈ S.ground.attach := by
        exact Finset.mem_attach S.ground y
      have : S.le y y := S.le_refl y
      simpa [Iy] using Finset.mem_filter.mpr ⟨hy₀, this⟩
    -- `S.coeFinset Iy` は α 上のイデアルであることを示す
    have hIy_sets : (S.idealFamily).sets (S.coeFinset Iy) := by
      -- isOrderIdealOn へ落とす（あなたの `sets_iff_isOrderIdeal` を利用）
      have : SetFamily.isOrderIdealOn (S.leOn) S.ground (S.coeFinset Iy) := by
        -- ⟨downward_closed, subset_ground⟩ を And で与える
        refine And.intro ?dc ?subset
        · -- ?dc : downward closed
          -- 目標: ∀ a ∈ ground, ∀ b, S.leOn b a → a ∈ S.coeFinset Iy → b ∈ S.coeFinset Iy
          simp_all only [Finset.mem_filter, Finset.mem_attach, true_and, Iy]
          intro z hz
          simp_all only [FuncSetup.mem_coeFinset, Finset.mem_filter, Finset.mem_attach, true_and, Subtype.exists,
            ]
          simp_all only [FuncSetup.le_iff_leOn_val, FuncSetup.sets_iff_isOrderIdeal, exists_and_left, exists_prop,
            exists_eq_right_right]
        · -- ?subset : S.coeFinset Iy ⊆ S.ground
          intro a haIn
          -- a ∈ coeFinset Iy から代表元 z を取り出す
          rcases (S.mem_coeFinset_val_iff).1 haIn with ⟨z, hzIy, hz⟩
          -- フィルタ左成分から z ∈ ground.attach
          have hzInAttach : z ∈ S.ground.attach :=
            (Finset.mem_filter).1 hzIy |>.left
          -- attach から ground へ
          have hzGround : z.1 ∈ S.ground := by
            subst hz
            simp_all only [ Finset.mem_filter, Finset.mem_attach, true_and,
              FuncSetup.mem_coeFinset, Subtype.exists, Finset.coe_mem, Iy]

          -- ので a ∈ ground
          -- `rw [hz]` を使わず等式で置換してもOK
          have : a ∈ S.ground := by
            -- a = z.1
            -- `subst` でも良い
            -- `convert hzGround using 1; exact hz.symm`
            exact Eq.ndrec hzGround hz

          intro y_1 a_1 a_2
          subst hz
          simp_all only [Finset.mem_attach, FuncSetup.mem_coeFinset, Subtype.exists, Finset.coe_mem,Iy]
          simp_all
          apply S.leOn_trans
          exact a_2
          exact hzIy
          -- 目標は b ∈ S.coeFinset Iy なので、存在証明で入れる
      simp_all only [Finset.mem_filter, Finset.mem_attach, true_and, Iy]
      exact this

    -- 仮定 `hAll` を Iy に適用すると x ∈ Iy
    have hxIy : x ∈ Iy := hAll Iy hIy_sets hyIy
    -- 以上より `x ≤ y` が従う
    have hxLe : S.le x y := (Finset.mem_filter.mp hxIy).2
    exact hxLe

/-- 論文 Lemma 3.3：
`u, v` が同じ同値類（S.sim）であることと，`idealFamily S` における parallel が同値。 -/
--この関係はfunctionalでなくても成り立つはずであるがここではfunctionalなものに対して証明している。
theorem parallel_iff_sim
  (S : FuncSetup α) (u v : S.Elem) :
  (S.idealFamily).Parallel u v ↔ FuncSetup.sim S u v := by
  constructor
  · intro hPar
    -- (∀ I, sets (coeFinset I) → (u∈I ↔ v∈I)) に言い換える

    have hUV :
      ∀ I : Finset S.Elem,
        (S.idealFamily).sets (S.coeFinset I) →
        (u ∈ I ↔ v ∈ I) := by
      dsimp [SetFamily.Parallel, FuncSetup.coeFinset] at *
      intro I hI
      constructor
      · intro hu
        have : (Finset.image (fun x => ↑x) I) ∈ {A | S.idealFamily.sets A ∧ ↑u ∈ A} :=
        by
          rw [@Set.mem_setOf_eq]
          constructor
          · exact hI
          · simp_all only [ Finset.mem_image, Subtype.exists, exists_and_right, exists_eq_right,
            Subtype.coe_eta, Finset.coe_mem, exists_const]
        simp_all only [ Set.mem_setOf_eq, Finset.mem_image, Subtype.exists, exists_and_right,
          exists_eq_right, Subtype.coe_eta, Finset.coe_mem, exists_const, true_and]
      · intro hv
        have : (Finset.image (fun x => ↑x) I) ∈ {A | S.idealFamily.sets A ∧ ↑v ∈ A} :=
        by
          rw [@Set.mem_setOf_eq]
          constructor
          · exact hI
          · simp_all only [Finset.mem_image, Subtype.exists, exists_and_right, exists_eq_right,
            Subtype.coe_eta, Finset.coe_mem, exists_const]
        rw [←hPar] at this
        rw [Set.mem_setOf_eq] at this
        simp_all only [Finset.mem_image, Subtype.exists, exists_and_right, exists_eq_right,
          Subtype.coe_eta, Finset.coe_mem, exists_const]

    -- 右向きに le_iff を使って S.le u v

    have huv : S.le u v := by
      let lifim := (le_iff_forall_ideal_mem S u v).mpr
      apply lifim
      intro I a a_1
      simp_all only [SetFamily.Parallel]

    -- 左向きに le_iff を使って S.le v u
    have hvu : S.le v u := by
      let lifim := (le_iff_forall_ideal_mem S v u).mpr
      apply lifim
      intro I a a_1
      simp_all only [SetFamily.Parallel]
    dsimp [FuncSetup.sim]
    exact ⟨huv, hvu⟩

  · intro hSim
    -- `le_iff_forall_ideal_mem` を左右に使って各 ideal での会員同値を出す
    rcases hSim with ⟨huv, hvu⟩
    dsimp [SetFamily.Parallel] at *
    ext J

    constructor
    swap
    · intro hu

      rw [@Set.mem_setOf_eq]
      rw [@Set.mem_setOf_eq] at hu
      constructor
      · exact hu.1
      · have : J ⊆ S.ground := by
          exact S.idealFamily.inc_ground hu.1

        let lifim := (le_iff_forall_ideal_mem S u v).mp huv (S.liftFinset J this)
        rw [S.coeFinset_liftFinset] at lifim
        specialize lifim hu.1
        simp_all only [FuncSetup.le_iff_leOn_val, FuncSetup.sets_iff_isOrderIdeal, FuncSetup.mem_liftFinset_iff, forall_const]

    · intro hv
      -- 対称に同様
      rw [@Set.mem_setOf_eq]
      rw [@Set.mem_setOf_eq] at hv
      constructor
      · exact hv.1
      · have : J ⊆ S.ground := by
          exact S.idealFamily.inc_ground hv.1

        let lifim := (le_iff_forall_ideal_mem S v u).mp hvu (S.liftFinset J this)
        rw [S.coeFinset_liftFinset] at lifim
        specialize lifim hv.1
        simp_all only [FuncSetup.le_iff_leOn_val, FuncSetup.sets_iff_isOrderIdeal, FuncSetup.mem_liftFinset_iff, forall_const]

-- 既存: parallel_iff_sim (S : FuncSetup α) (u v : S.Elem)
-- をそのまま使い、必要なら underlying へ落とすだけ。
--そとから使っている。Monotonicity.leanでもIdealTraceでも。
@[simp]
lemma parallel_of_sim_coe (S : FuncSetup α) {x y : S.Elem}
    (h : FuncSetup.sim S x y) :
    (S.idealFamily).Parallel (x : α) (y : α) := by
  -- `Parallel` の引数が α のとき、`x y : S.Elem` は自動で coercion されます。
  -- 既存の `parallel_iff_sim` を使うだけで OK。
  have hxy : (S.idealFamily).Parallel x y :=
    (parallel_iff_sim S x y).2 h
  -- ここで `x y` は自動 coercion され、目標型に一致します。
  exact hxy

--FuncSetupを使っているので、SetFamilyには移せない。
--`simClass u` と `ParallelClass F u` の同値性。
--そとからも使っている。
@[simp]
lemma simClass_eq_parallelClass
  (S : FuncSetup α) (u : S.Elem) :
  S.simClass u = (S.idealFamily).ParallelClass (u : α) := by
  classical
  ext a; constructor
  · intro ha
    rcases (S.mem_simClass_iff u).1 ha with ⟨ha', hsim⟩
    have hpar : (S.idealFamily).Parallel (u : α) a :=
      (S.parallel_iff_sim u ⟨a, ha'⟩).2 (S.sim_symm hsim)
    exact Finset.mem_filter.mpr ⟨ha', hpar⟩
  · intro ha
    rcases Finset.mem_filter.1 ha with ⟨ha', hpar⟩
    have hsim : S.sim u ⟨a, ha'⟩ := (S.parallel_iff_sim u ⟨a, ha'⟩).1 hpar
    exact (S.mem_simClass_iff u).2 ⟨ha', S.sim_symm hsim⟩

/-オリジナル証明
lemma simClass_eq_parallelClass
  (S : FuncSetup α) (u : S.Elem) :
  S.simClass u = (S.idealFamily).ParallelClass  (u : α) := by
  classical
  -- 要素 a : α による外延性
  apply Finset.ext
  intro a
  constructor
  · -- → : a ∈ simClass u ⇒ a ∈ ParallelClass F u
    intro ha
    -- mem_simClass_iff : a ∈ simClass u ↔ ∃ ha, S.sim ⟨a,ha⟩ u
    rcases (S.mem_simClass_iff u).mp ha with ⟨ha', hsim⟩
    -- `Parallel` と `sim` の同値（coercion に注意）
    have hpar :
        (S.idealFamily).Parallel u a := --⟨a, ha'⟩ :=
      (S.parallel_iff_sim u ⟨a, ha'⟩).2 (S.sim_symm hsim)
    -- ParallelClass の membership は filter での条件
    exact
      Finset.mem_filter.mpr (And.intro ha' hpar)
  · -- ← : a ∈ ParallelClass F u ⇒ a ∈ simClass u
    intro ha
    -- filter のメンバ判定をほどく
    have hsub : a ∈ (S.idealFamily).ground ∧
                (S.idealFamily).Parallel (u : α) a :=
      Finset.mem_filter.mp ha
    rcases hsub with ⟨ha', hpar⟩
    -- Parallel ↔ sim から sim へ
    have hsim' : S.sim u ⟨a, ha'⟩ :=
      (S.parallel_iff_sim u ⟨a, ha'⟩).1 hpar
    -- mem_simClass_iff の → 方向
    exact (S.mem_simClass_iff u).mpr ⟨ha', S.sim_symm hsim'⟩
-/

--下で使っている。
private lemma mem_simClass_of_sim
  (S : FuncSetup α) {u v : S.Elem} (h : S.sim u v) :
  (v : α) ∈ S.simClass u :=
  (S.mem_simClass_iff u).2 ⟨v.2, S.sim_symm h⟩

/-オリジナル証明
private lemma mem_simClass_of_sim
  (S : FuncSetup α) {u v : S.Elem} (h : S.sim u v) :
  (v : α) ∈ S.simClass u := by
  classical
  -- 対称性で `S.sim v u` にしてから、mem_simClass_iff を使う
  have hsym : S.sim v u := S.sim_symm h
  -- `⟨(v : α), v.2⟩ = v` で書換
  have hv : (⟨(v : α), v.2⟩ : S.Elem) = v := by
    apply Subtype.ext; rfl
  -- mem_simClass_iff の → 方向に渡す
  --   目標: ∃ hv, S.sim ⟨(v:α), hv⟩ u
  --   ここでは hv := v.2 を選べばよい
  exact
    (S.mem_simClass_iff u).mpr
      ⟨v.2, by
        -- `S.sim ⟨(v : α), v.2⟩ u` へ変形
        -- hsym : S.sim v u, かつ hv : ⟨(v:α),v.2⟩ = v
        -- 書換で OK
        -- （エディタでは `rw [hv]`）
        exact hsym⟩
-/

--そとからも使っている。
lemma eq_of_sim_of_all_classes_card_one
  (S : FuncSetup α)
  (h1 : ∀ C ∈ (S.idealFamily).classSet , C.card = 1) :
  ∀ {u v : S.Elem}, S.sim u v → u = v := by
  classical
  intro u v hsim
  have hv_mem : (v : α) ∈ S.simClass u := mem_simClass_of_sim S hsim
  have hu_mem : (u : α) ∈ S.simClass u := mem_simClass_of_sim S (S.sim_refl u)
  -- `ParallelClass (u:α)` が `classSet` の元
  have hC :
      (S.idealFamily).ParallelClass (u : α) ∈ (S.idealFamily).classSet := by
    unfold SetFamily.classSet
    exact Finset.mem_image.mpr ⟨(u : α), u.2, rfl⟩
  -- card = 1 を `simClass` へ移送
  have hEq := simClass_eq_parallelClass S u
  have hcard_one : (S.simClass u).card = 1 := by
    have hc := h1 _ hC
    -- `rw` で左右を書き換え
    -- `hc : card (ParallelClass (u:α)) = 1`
    -- `hEq : simClass u = ParallelClass (u:α)`
    simp_all only [SetFamily.mem_ParallelClass_iff, Finset.coe_mem, SetFamily.Parallel, sets_iff_isOrderIdeal, true_and,
    and_self]
  -- 単集合化
  rcases Finset.card_eq_one.1 hcard_one with ⟨a, ha⟩
  have hv := by rw [ha] at hv_mem; exact Finset.mem_singleton.1 hv_mem
  have hu := by rw [ha] at hu_mem; exact Finset.mem_singleton.1 hu_mem
  -- 値が等しいので Subtype も等しい
  apply Subtype.ext
  exact Eq.trans hu (Eq.symm hv)

/- オリジナル証明
lemma eq_of_sim_of_all_classes_card_one
  (S : FuncSetup α)
  (h1 : ∀ C ∈ (S.idealFamily).classSet , C.card = 1) :
  ∀ {u v : S.Elem}, S.sim u v → u = v := by
  classical
  intro u v hsim
  -- `sim u v` から `(v:α) ∈ simClass u`
  have hv_mem : (v : α) ∈ S.simClass u :=
    mem_simClass_of_sim S hsim
  -- `u` 自身も `sim` の反射でクラスに入る
  have hu_mem : (u : α) ∈ S.simClass u := by
    -- refl：S.sim u u
    have hrefl : S.sim u u := S.sim_refl u
    exact mem_simClass_of_sim S hrefl
  -- `simClass u = ParallelClass F u`
  have hEq := simClass_eq_parallelClass S u
  -- これより `card (simClass u) = 1`
  have hcard_one :
      (S.simClass u).card = 1 := by
    -- `ParallelClass F u ∈ classSet F`
    have hC : (S.idealFamily).ParallelClass  (u : α)
              ∈ (S.idealFamily).classSet  := by
      -- classSet = ground.image (λ a, ParallelClass F a)
      -- 代表 `u.1` は ground にある
      have hu : (u : α) ∈ (S.idealFamily).ground := u.2
      unfold SetFamily.classSet
      exact Finset.mem_image.mpr ⟨(u : α), hu, rfl⟩
    -- 書換えて `h1` を適用
    -- （エディタでは `rw [hEq]`）
    have := h1 ((S.idealFamily).ParallelClass  (u : α)) hC
    -- `S.simClass u = ParallelClass ...` を左辺に反映
    -- ここでは最終形だけ使います
    simp_all only [SetFamily.mem_ParallelClass_iff, Finset.coe_mem, SetFamily.Parallel, FuncSetup.sets_iff_isOrderIdeal, true_and, and_self]

  -- `card = 1` から「単集合」であることを取り出す
  rcases Finset.card_eq_one.mp hcard_one with ⟨a, ha_single⟩
  -- メンバシップを単集合に移して等式化
  have : (v : α) = a := by
    -- `hv_mem : v ∈ simClass u` と `simClass u = {a}`
    -- から `v = a`
    -- （エディタでは `have := hv_mem; rw [hEq, ha_singleton] at this; exact Finset.mem_singleton.mp this`）
    -- ここでは結論だけ：
    rw [ha_single] at hv_mem
    exact Finset.mem_singleton.1 hv_mem

  have : (u : α) = a := by
    -- 同様に `u` もクラスに属す
    rw [ha_single] at hu_mem
    exact Finset.mem_singleton.1 hu_mem
  -- 以上から `(u : α) = (v : α)`
  have huv : (u : α) = (v : α) := by
    -- どちらも `= a`
    exact Eq.trans this (Eq.symm ‹(v : α) = a›)
  -- サブタイプ等式へ
  apply Subtype.ext
  exact huv
-/

noncomputable def principalIdeal (S : FuncSetup α) (a : α) (ha : a ∈ S.ground) : Finset α := by
  classical
  -- attach は {y // y ∈ ground}、述語は `S.le y ⟨a,ha⟩`
  exact (S.ground.attach.filter (fun (y : {z // z ∈ S.ground}) => S.le y ⟨a, ha⟩)).map
    ⟨Subtype.val, by simp_all only [Subtype.val_injective]⟩

--後半の議論で参照。
/-- 会員判定（存在形）：`y ∈ ↓a` ↔ `∃ hy, y ∈ ground ∧ (⟨y,hy⟩ ≤ₛ ⟨a,ha⟩)`。 -/
lemma mem_principalIdeal_iff (S : FuncSetup α)
  {a y : α} (ha : a ∈ S.ground) :
  y ∈ S.principalIdeal a ha ↔ ∃ hy : y ∈ S.ground, S.le ⟨y, hy⟩ ⟨a, ha⟩ := by
  classical
  constructor
  · intro hy
    rcases Finset.mem_map.mp hy with ⟨u, hu, huv⟩
    -- 条件部を取り出す
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

/-- ground 側を前提にした簡約形：`y ∈ ↓a` ↔ `⟨y,hy⟩ ≤ₛ ⟨a,ha⟩`。 -/
lemma mem_principalIdeal_iff_le (S : FuncSetup α)
  {a y : α} (ha : a ∈ S.ground) (hy : y ∈ S.ground) :
  y ∈ S.principalIdeal a ha ↔ S.le ⟨y, hy⟩ ⟨a, ha⟩ := by
  constructor
  · intro h; rcases (S.mem_principalIdeal_iff (a:=a) (y:=y) ha).1 h with ⟨hy', hle⟩
    cases Subtype.ext (rfl : (⟨y, hy'⟩ : S.Elem).1 = (⟨y, hy⟩ : S.Elem).1)
    exact hle
  · intro hle; exact (S.mem_principalIdeal_iff (a:=a) (y:=y) ha).2 ⟨hy, hle⟩

lemma self_mem_principalIdeal (m : S.Elem) :
  m.1 ∈ S.principalIdeal m.1 m.2 := by
  classical
  -- 反射律で `⟨m, _⟩ ≤ ⟨m, _⟩`
  have : S.le ⟨m.1, m.2⟩ ⟨m.1, m.2⟩ := Relation.ReflTransGen.refl
  -- 会員判定（簡約形）で即
  exact
    (S.mem_principalIdeal_iff_le (a := m.1) (y := m.1) (ha := m.2) (hy := m.2)).2
      this

lemma principalIdeal_subset_ground (S : FuncSetup α) (x : S.Elem) :
  S.principalIdeal x.1 x.2 ⊆ S.ground := by
  intro a ha
  obtain ⟨val, property⟩ := x
  simp_all only
  rw [principalIdeal] at ha
  simp_all only [le_iff_leOn_val, Finset.mem_map, Finset.mem_filter, Finset.mem_attach, true_and,
    Function.Embedding.coeFn_mk, Subtype.exists, exists_and_left, exists_prop, exists_eq_right_right]



/-- 7) principal ideal は ideal（`isOrderIdealOn` 版）。 -/
lemma principalIdeal_isOrderIdealOn
  (S : FuncSetup α) {a : α} (ha : a ∈ S.ground) :
  SetFamily.isOrderIdealOn (S.leOn) S.ground (S.principalIdeal a ha) := by
  -- isOrderIdealOn の定義：a ≤ b, b∈I なら a∈I
  dsimp [SetFamily.isOrderIdealOn]
  constructor
  · dsimp [FuncSetup.principalIdeal]
    simp_all only [le_iff_leOn_val]
    intro x hx
    simp_all only [Finset.mem_map, Finset.mem_filter, Finset.mem_attach, true_and, Function.Embedding.coeFn_mk,
      Subtype.exists, exists_and_left, exists_prop, exists_eq_right_right]
  ·
    intro x hx y hy_mem
    -- hx_mem : y ∈ principalIdeal a
    -- ground 側の判定に出すため、y∈ground と ⟨y,hy⟩ ≤ ⟨a,ha⟩ を取り出す
    intro hs
    have hx' := (S.mem_principalIdeal_iff (a:=a) (y:=x) ha).1 hx
    simp at hx'
    let mpi := (S.mem_principalIdeal_iff (a:=a) (y:=y) ha).2
    apply mpi
    use hy_mem
    have : S.leOn y a := S.leOn_trans hs hx'.2
    exact (leOn_iff S hy_mem ha).mp this






section IterateRTG
variable {α : Type*} (f : α → α)

--SetFamilyもFuncSetupも出てこない、一般的な補題は、Generalに置くべきかもしれない。
--ただし、fが出てきているので、実質的にFuncSetupの枠組み。stepRelもFuncSetupの枠組みで定義した方がいいかも。
-- 関係 R_f : x R_f y ↔ f x = y
def stepRel : α → α → Prop := fun x y => f x = y

lemma iterate_commute_right (f : α → α) :
    ∀ n x, Nat.iterate f n (f x) = f (Nat.iterate f n x) := by
  intro n
  induction' n with n ih
  · intro x; rfl
  · intro x
    -- iterate (n+1) (f x) = iterate n (f (f x))
    have h1 : Nat.iterate f (n+1) (f x) = Nat.iterate f n (f (f x)) := by
      -- 定義展開
      simp [Nat.iterate]
    -- 右側を `ih` で一段ほどく
    have h2 : Nat.iterate f n (f (f x)) = f (Nat.iterate f n (f x)) := by
      -- `ih` を `x := f x` に適用
      simpa using ih (f x)
    -- さらに `ih` で `(f^[n]) (f x)` を置換
    have h3 : f (Nat.iterate f n (f x)) = f (f (Nat.iterate f n x)) := by
      -- `ih x : (f^[n]) (f x) = f ((f^[n]) x)` を `f ∘ _` の中で使用
      simpa using congrArg f (ih x)
    -- 仕上げ：定義で `(f^[n+1]) x = (f^[n]) (f x)` に戻す
    calc
      Nat.iterate f (n+1) (f x)
          = Nat.iterate f n (f (f x)) := h1
      _   = f (Nat.iterate f n (f x)) := h2
      _   = f (f (Nat.iterate f n x)) := h3
      _   = f (Nat.iterate f (n+1) x) := by
              -- `Nat.iterate f (n+1) x = Nat.iterate f n (f x)`
              simp [Nat.iterate]
              simp_all only [Function.iterate_succ, Function.comp_apply]

/-- 主要補題：`ReflTransGen (stepRel f) x y ↔ ∃ k, (f^[k]) x = y` -/
lemma reflTransGen_iff_exists_iterate
    (f : α → α) {x y : α} :
    Relation.ReflTransGen (stepRel f) x y ↔ ∃ k : ℕ, Nat.iterate f k x = y := by
  constructor
  · -- →：反射推移閉包の帰納
    intro h
    induction h with
    | @refl  =>
        exact ⟨0, rfl⟩
    | @tail  b c hxb hbc ih =>
        rcases ih with ⟨k, hk⟩
        refine ⟨k + 1, ?_⟩
        calc
          Nat.iterate f (k+1) x
              = Nat.iterate f k (f x) := by
                  simp [Nat.iterate]
          _   = f (Nat.iterate f k x) := iterate_commute_right f k x
          _   = f b := by exact congrArg f hk
          _   = c := hbc
  · -- ←：k による単純帰納で「k 歩の鎖」を作る
    intro h
    rcases h with ⟨k, hk⟩
    -- x ⟶* (f^[k] x) の鎖を k で作る
    have hx_to_iter : Relation.ReflTransGen (stepRel f) x (Nat.iterate f k x) := by
      revert x
      induction' k with k ih
      · intro x;
        intro hk
        subst hk
        simp_all only [Function.iterate_zero, id_eq]
        rfl

      · intro x
        -- まず x ⟶* (f^[k] x)（ih）、最後の 1 歩：(f^[k] x) ⟶ (f^[k+1] x)
        have step : stepRel f (Nat.iterate f k x) (Nat.iterate f (k+1) x) := by
          have h1 : Nat.iterate f (k+1) x = Nat.iterate f k (f x) := by
            simp [Nat.iterate]
          have h2 : Nat.iterate f k (f x) = f (Nat.iterate f k x) :=
            iterate_commute_right f k x
          exact (Eq.trans (Eq.symm h2) (Eq.symm h1))
        -- ⊢ Relation.ReflTransGen (stepRel f) x (f^[k + 1] x)
        exact fun hk => Relation.ReflTransGen.head rfl (ih hk)

    -- 目的は x ⟶* y。ゴール側を y から (f^[k] x) に書換えて解決
    -- `Nat.iterate f k x = y` を左向きに使えばゴールが一致
    -- `rw [← hk]` でゴールの右端を置換してから `exact hx_to_iter`
    -- tactic を最小限使います（`simpa using` は不使用）
    have : Relation.ReflTransGen (stepRel f) x y := by
      -- ゴールを書換え
      -- （ターミナル・ゴールの書換えは `have`/`exact` だと難しいので、`match` を避けて `show`+`rw`）
      show Relation.ReflTransGen (stepRel f) x y
      -- 右辺を (f^[k]) x に戻す
      -- `have` で一旦ゴールをセットできないので、`have hx` を返す形にします
      -- ここは tactic バインダで簡潔に：
      exact (by
        -- `rw` はゴール側の書換えに使える： `y` を `(f^[k]) x` に戻す
        -- 具体的には「`(f^[k]) x = y` の対称形」を使う
        have hk' : y = Nat.iterate f k x := hk.symm
        -- `Eq.rec` を避け、`hk' ▸ _` でゴールを書換える
        -- `▸` は `rw` と同様に使える
        simpa [hk'] using hx_to_iter
      )
    exact this

/-- 論文 Lemma 2.2：
`x ≤ y` ↔ ある `k ≥ 0` で `f^[k] x = y`。 -/
lemma le_iff_exists_iter {α} [DecidableEq α] (S : FuncSetup α) (x y : S.Elem) :
    S.le x y ↔ ∃ k : Nat, S.iter k x = y := by
  -- ReflTransGen ↔ 反復到達 の標準対応
  -- 後で詳細証明を埋める。
  dsimp [FuncSetup.le]
  unfold FuncSetup.cover
  exact reflTransGen_iff_exists_iterate (fun xx => S.f xx)

-- まず小補題： g u = u なら g^[n] u = u
private lemma iterate_fixpoint {β} (g : β → β) (u : β) (n : ℕ) (hu : g u = u) :
    Nat.iterate g n u = u := by
  induction' n with n ih
  · simp [Nat.iterate]
  · -- iterate (n+1) u = iterate n (g u) = iterate n u = u
    -- `simpa using` を使わずに `simp` で処理
    have : Nat.iterate g (n + 1) u = Nat.iterate g n (g u) := by
      simp [Nat.iterate]
    -- 右辺を書き換えて閉じる
    -- g u = u かつ ih : iterate g n u = u
    -- `simp` に両方を渡すと左辺が u になる
    have : Nat.iterate g n (g u) = u := by
      -- g u を u に、さらに ih を使う
      -- （`simp` は可、`simpa using` は使わない）
      -- 具体的には： iterate g n (g u) = iterate g n u = u
      --             ↑hu               ↑ih
      -- 1回目の書換え
      have : Nat.iterate g n (g u) = Nat.iterate g n u := by
        -- `congrArg` でもよいが、ここは置換で十分
        -- g u を u へ
        -- `simp` を使ってもOK
        -- （細かい書換えは `simp [hu]` で反映）
        simp [hu]
      -- 2回目：ih で u
      -- `simp` で ih を使う
      -- `simp [this, ih]` でも可だが、順に適用
      -- ここでは this による置換→ ih 適用の順に
      -- 置換
      -- `rw` を使うと変数束縛が増えるので、このまま `simp` で潰す
      -- 最終行でまとめて `simp [hu, ih]`
      simp_all only
    -- まとめて閉じる
    -- 上の詳細展開は冗長なので、一気に：
    -- `simp [Nat.iterate, hu, ih]` だけでも通る
    simp [Nat.iterate, hu, ih]

/-- イテレートは単調：`i ≤ j` なら `(f^[i]) x ≤ (f^[j]) x`。 -/
--同じものがある可能性あり。
lemma le_between_iter {α} [DecidableEq α]  (S : FuncSetup α) (x : S.Elem) :
  ∀ {i j : ℕ}, i ≤ j → S.le ((S.f^[i]) x) ((S.f^[j]) x)
| i, j, hij => by
  -- j = i + d にして d で帰納
  rcases Nat.exists_eq_add_of_le hij with ⟨d, rfl⟩
  -- 目標： (f^[i]) x ≤ (f^[i + d]) x
  induction d with
  | zero =>
      exact Relation.ReflTransGen.refl
  | succ d ih =>
      -- 1歩： (f^[i+d]) x ⋖ (f^[i+d+1]) x
      have hstep :
          S.cover ((S.f^[i + d]) x) ((S.f^[i + d + 1]) x) := by
        -- cover の定義は等式。iterate の標準補題で与える
        -- iterate_succ_apply' : (f^[n+1]) x = f ((f^[n]) x)
        -- 対称を取れば f ((f^[n]) x) = (f^[n+1]) x
        dsimp [FuncSetup.cover]
        exact (Function.iterate_succ_apply' S.f (i + d) x).symm
      -- 既に (f^[i]) x ≤ (f^[i+d]) x なので、最後に1歩つけ足す
      simp at ih
      refine Relation.ReflTransGen.tail ?_ hstep
      convert ih
      dsimp [FuncSetup.cover]
      dsimp [FuncSetup.leOn]
      dsimp [FuncSetup.le]
      simp_all only [le_add_iff_nonneg_right, zero_le, Function.iterate_succ, Function.comp_apply, Subtype.coe_eta,
        Finset.coe_mem, exists_const]



end IterateRTG


--Parallel関係
--これもFuncSetupが出てこない一般的な補題に見えるが、fがあるので、実質FuncSetupになっている。stepRelも定義する必要あり。
omit [DecidableEq α] in
lemma maximal_of_nontrivialClass_lemma
    (f : α → α) [Fintype α] {u v : α}
    (huv : Relation.ReflTransGen (stepRel f) u v ∧
           Relation.ReflTransGen (stepRel f) v u)
    (hneq : u ≠ v) :
    (∀ x, Relation.ReflTransGen (stepRel f) u x →
          Relation.ReflTransGen (stepRel f) x u) := by
  intro x hux
  -- u ~ v からイテレート表示を取る
  rcases (reflTransGen_iff_exists_iterate f).1 huv.1 with ⟨k, hk⟩
  rcases (reflTransGen_iff_exists_iterate f).1 huv.2 with ⟨ℓ, hℓ⟩
  rcases (reflTransGen_iff_exists_iterate f).1 hux   with ⟨m, hm⟩

  -- 周期 L := ℓ + k に対し f^[L] u = u
  --   f^[ℓ] v = u かつ v = f^[k] u から
  have hL' : Nat.iterate f (ℓ + k) u = u := by
    -- f^[ℓ + k] u = f^[ℓ] (f^[k] u) = f^[ℓ] v = u
    have h1 : Nat.iterate f (ℓ + k) u
                = Nat.iterate f ℓ (Nat.iterate f k u) :=
      Function.iterate_add_apply f ℓ k u
    -- 右辺を v に置換
    have h2 : Nat.iterate f ℓ (Nat.iterate f k u)
                = Nat.iterate f ℓ v := by
      -- hk : f^[k] u = v を右辺に適用
      -- `rw` で十分
      rw [hk]
    -- 連結して u
    exact Eq.trans (Eq.trans h1 h2) hℓ

  -- 記法：L := ℓ + k, t := L*(m+1) - m
  let L := ℓ + k
  have hL : Nat.iterate f L u = u := by
    -- hL' は (ℓ + k)。L の展開で一致
    -- `rfl` で L をほどき `hL'` を使う
    -- `simp` は使わず、`rfl` による置換で OK
    -- 具体的には `show Nat.iterate f (ℓ + k) u = u; exact hL'`
    -- （`L` は `ℓ + k` と定義したので）
    change Nat.iterate f (ℓ + k) u = u
    exact hL'

  let t : ℕ := L * (m + 1) - m

  -- m ≤ L*(m+1) を示して、t + m = L*(m+1) を得る
  have Lpos : 0 < L := by
    -- k=0 だと hk から v = u になり hneq と矛盾。よって k>0、ゆえに L>0
    -- 堅めにやるには反証で：
    by_contra hLz
    -- L = 0 ⇒ k = 0 ∧ ℓ = 0
    have : L = 0 := le_antisymm (le_of_not_gt hLz) (Nat.zero_le _)

    apply False.elim
    subst hℓ hm
    simp_all only [not_lt, Nat.le_zero_eq, Nat.add_eq_zero, add_zero, Function.iterate_zero, id_eq, and_self, ne_eq,
      not_true_eq_false, L]

  -- 実は Lpos は使わないので無視してOK。
  have hmle : m ≤ L * (m + 1) := by
    -- m ≤ m+1 ≤ L*(m+1)
    have h1 : m ≤ m + 1 := Nat.le_succ m
    have h2 : m + 1 ≤ L * (m + 1) := by
      -- 1 ≤ L ⇒ (m+1) ≤ L*(m+1)
      -- たとえ L=0 でも (m+1) ≤ 0 は成り立ちませんが、ここでは
      -- `Nat.mul_le_mul_right` は 1 ≤ L が要る。安全策として L≥1 を示すかわりに
      -- 自明な `m ≤ L*(m+1)` は、L*(m+1) ≥ m を直接示せます：
      -- L*(m+1) ≥ 0 ≥ m は成り立たないので、以下のように別ルートで：
      -- 実際には `Nat.le_of_lt` を使うのは過剰なので、この行は次の一行に差し替えます。
      exact Nat.le_mul_of_pos_left (m + 1) Lpos
    exact Nat.le_trans h1 h2

  have ht_add : t + m = L * (m + 1) := by
    -- (L*(m+1) - m) + m = L*(m+1)
    -- `Nat.sub_add_cancel` を使う
    -- まず t を定義通り展開
    change (L * (m + 1) - m) + m = L * (m + 1)
    exact Nat.sub_add_cancel hmle

  -- 目標： x ⟶* u。イテレート表示で作る
  -- `reflTransGen_iff_exists_iterate` の ← を使う準備として等式を作る
  have h_iter_eq : Nat.iterate f t x = u := by
    -- x = f^[m] u を左辺に、t+m = L*(m+1) を右辺に
    -- まず (iterate_add) で左辺を右辺に移す
    -- base : f^[t] (f^[m] u) = f^[t+m] u
    have base := Eq.symm (Function.iterate_add_apply f t m u)
    -- base : Nat.iterate f t (Nat.iterate f m u) = Nat.iterate f (t + m) u
    -- 左辺の (f^[m] u) を x に置換
    have base' : Nat.iterate f t x = Nat.iterate f (t + m) u := by
      -- `rw` を base に適用
      -- いったんコピーしてから書換え
      have tmp := base

      have tmp' := tmp

      clear tmp
      -- calc で書き直し
      calc
        Nat.iterate f t x
            = Nat.iterate f t (Nat.iterate f m u) := by
                -- `x` を展開（hm の逆向き）
                -- `rw [←hm]` を使う
                rw [←hm]
        _   = Nat.iterate f (t + m) u := base
    -- つづいて t+m を L*(m+1) に、さらに (L*(m+1)) を「(f^[L])^[m+1]」へ
    have h_right1 : Nat.iterate f (t + m) u = Nat.iterate f (L * (m + 1)) u := by
      -- `rw [ht_add]`
      -- ゴール側を書き換え
      -- `calc` を使っても良いが単発の `rw` で十分
      -- `exact` で返すために中間値に置く
      -- 直接：
      --   by simpa [ht_add] とはせず、`rw` で。
      -- ここも `calc` を使います。
      have : t + m = L * (m + 1) := ht_add

      subst hℓ hm
      simp_all only [Nat.sub_add_cancel, ne_eq, L, t]

    -- 最終まとめ： base' と ht_add、さらに乗法版 iterate で u
    -- まず base' の右辺を ht_add で置換
    --   f^[t] x = f^[t+m] u  →  = f^[L*(m+1)] u
    -- そのうえで 乗法版 iterate と `iterate_fixpoint` で u
    -- 乗法： f^[L*(m+1)] u = (f^[L])^[m+1] u
    have h_mul : Nat.iterate f (L * (m + 1)) u
                  = Nat.iterate (Nat.iterate f L) (m + 1) u := by
      let fi := Function.iterate_mul f L (m + 1)
      exact congrFun fi u

    -- g := f^[L] は u を固定する（hL）
    have h_fix : Nat.iterate (Nat.iterate f L) (m + 1) u = u :=
      iterate_fixpoint (Nat.iterate f L) u (m + 1) hL

    calc
      Nat.iterate f t x
          = Nat.iterate f (t + m) u := base'
      _   = Nat.iterate f (L * (m + 1)) u := by
              -- ここで `rw [ht_add]`
              -- `simp` は使わずに `rw`
              -- ただし `calc` 内では `simp`/`rw` はその場で使えます
              -- 直接：
              have : t + m = L * (m + 1) := ht_add
              exact by
                -- 置換して refl
                -- `rw` と違い、`exact` で返す必要があるので Eq.rec を意識せずに
                -- `cases` で置換します
                -- ここでは素直に：
                --   by rw [this]
                -- を tactic で書けないので、もう一段 `calc` はやめて
                -- 上の `by` ブロック内で `rw` を使います。
                -- 簡潔に：
                --    `rw [this]`
                -- で終了
                -- （この `by` ブロックは tactic 文脈なので `rw` が使えます）
                rw [this]
      _   = Nat.iterate (Nat.iterate f L) (m + 1) u := h_mul
      _   = u := by
              -- `h_fix` を当てる
              exact h_fix

  -- イテレート等式から ReflTransGen を得る（← 方向）
  exact (reflTransGen_iff_exists_iterate f).2 ⟨t, h_iter_eq⟩

--パラレルな元であれば、uからxにいければxからuにいける。
--極大性は使ってない。parallel_iff_simは使う立場。
--nontrivialClassの仮定を使って書き換えられそう。
--nds_monotone_under_traceで利用されている。
--この言明には、functionalという仮定が必要。
theorem maximal_of_parallel_nontrivial
    (S : FuncSetup α) {u v : α}
    (hu : u ∈ S.ground) (hv : v ∈ S.ground)
    (hpar : (S.idealFamily).Parallel u v)
    (hneq : u ≠ v) :
    ∀ x : S.Elem,
      Relation.ReflTransGen (stepRel S.f) (S.toElem! hu) x →
      Relation.ReflTransGen (stepRel S.f) x (S.toElem! hu) := by
  classical
  -- parallel ⇒ sim
  have hsim : S.sim (S.toElem! hu) (S.toElem! hv) :=
    (S.parallel_iff_sim (S.toElem! hu) (S.toElem! hv)).1 hpar
  -- sim ⇒ 両向きの ReflTransGen(stepRel S.f)
  have huv : Relation.ReflTransGen (stepRel S.f) (S.toElem! hu) (S.toElem! hv) := by
    -- le → ∃k → ReflTransGen
    have hle := hsim.1
    rcases (S.le_iff_exists_iter (S.toElem! hu) (S.toElem! hv)).1 hle with ⟨k, hk⟩
    exact (reflTransGen_iff_exists_iterate S.f).2 ⟨k, hk⟩
  have hvu : Relation.ReflTransGen (stepRel S.f) (S.toElem! hv) (S.toElem! hu) := by
    have hle := hsim.2
    rcases (S.le_iff_exists_iter (S.toElem! hv) (S.toElem! hu)).1 hle with ⟨k, hk⟩
    exact (reflTransGen_iff_exists_iterate S.f).2 ⟨k, hk⟩
  have hneq' : (S.toElem! hu) ≠ (S.toElem! hv) := by
    intro h; exact hneq (congrArg Subtype.val h)
  -- 一般補題を S.Elem, f := S.f に適用
  have hmax :=
    maximal_of_nontrivialClass_lemma
      (α := S.Elem) (f := S.f)
      (u := S.toElem! hu) (v := S.toElem! hv)
      ⟨huv, hvu⟩ hneq'
  -- 仕上げ
  intro x hx; exact hmax x hx

------------------------



/- 記法を開く（必要な箇所で使えるように）。 -/
--open FuncSetup (le cover)


/-
/-- 逆に、`v` が `u` のクラスに入るなら `sim u v`。 -/
--つかってないかも。
lemma sim_of_mem_simClass
  (S : FuncSetup α) {u : S.Elem} {a : α}
  (ha : a ∈ S.ground) (hmem : a ∈ S.simClass u) :
  S.sim ⟨a, ha⟩ u := by
  classical
  have := (S.mem_simClass_iff u).mp hmem
  -- this : ∃ ha', S.sim ⟨a, ha'⟩ u
  rcases this with ⟨_, hsim⟩
  -- ground 証明が違っても Subtype.ext で同一視
  -- ⟨a, ha⟩ と ⟨a, _⟩ は値が同じなので transport で書き換え
  -- 実際には値部分が同じなので hsim をそのまま使えます
  exact hsim
-/

/- ground 上の比較を subtype に引き上げる便利関数。 -/
--def toElem! (S : FuncSetup α) {x : α} (hx : x ∈ S.ground) : S.Elem := ⟨x, hx⟩

/-! ## 2) Lemma 3.3：同値（∼）と parallel の同値 -/

----使ってないもの。


/-- （使い勝手用）非自明同値類のとき，後継 `f u` を
    「u と異なる ground の元」として取り出す形。 -/
-- hvは暗黙につかっている。
--現状使ってない。
lemma exists_succ_partner_of_nontrivial {α : Type u} [DecidableEq α]
    (S : FuncSetup α) {u : α} (hu : u ∈ S.ground)
    (h : S.nontrivialClass (S.toElem! hu)) :
    ∃ (v : α) (_ : v ∈ S.ground), v ≠ u := by
  classical
  let ue : S.Elem := ⟨u, hu⟩
  let ve : S.Elem := S.f ue
  refine ⟨ve.1, ve.2, ?_⟩
  -- `ve ≠ ue` を `Subtype.ext` で基の α に落とす
  have hne : ve ≠ ue := S.f_ne_of_nontrivialClass (u := ue) h
  intro hval
  apply hne
  apply Subtype.ext
  exact hval

-- 部分型の同値 ≠ から基底の ≠ を取り出す補助。現状使ってない。
private lemma ne_val_of_ne {x y : {a // a ∈ S.ground}} (h : x ≠ y) : x.1 ≠ y.1 := by
  intro hval
  apply h
  apply Subtype.ext
  exact hval
/-
--今の所使ってない。ほぼ定義そのままなのでいらないかも。
--これはideal関連ではない。
lemma exists_partner_on_ground
    {u : S.Elem} (h : S.nontrivialClass u) :
     ∃ (v : α) (hv : v ∈ S.ground), v ≠ u.1 ∧ S.sim u ⟨v, hv⟩ := by
  -- ∃ v, (v ∈ S.ground) ∧ ((hv : v ∈ S.ground) → v ≠ u.1 ∧ S.sim u ⟨v, hv⟩) := by
  -- h から subtype の相手 y を取り出す
  rcases h with ⟨y, hy_ne, hy_sim⟩
  -- v := y.1, hv := y.2 をそのまま使う
  refine ⟨y.1, y.2, ?neq, ?hsim⟩
  -- 値が等しければ subtype が等しいので hy_ne に反する：Subtype.ext を使用
  · intro hval
    apply hy_ne
    apply Subtype.ext
    exact hval
  -- ⟨y.1, y.2⟩ は定義的に y なので、そのまま置換して終わり
  · change S.sim u y
    exact hy_sim
-/

--principalIdealにかんすること。別のところで使っている。




/-
/- 7) principal ideal は ideal（`α` 上の isOrderIdealOn 版）。
    既存の `sets_iff_isOrderIdeal` と合う側です。 -/
lemma principalOn_isOrderIdealOn
  (S : FuncSetup α) (hx : x ∈ S.ground) :
  isOrderIdealOn (S.leOn) S.ground ((S.principalIdeal (S.toElem! hx)) hx) := by
-/
  -- isOrderIdealOn の定義：I ⊆ V ∧ (x∈I → y∈V → leOn y x → y∈I)

/-! ## 8) 理想の個数は `|ground|+1` 以上 -/

end FuncSetup

end AvgRare
