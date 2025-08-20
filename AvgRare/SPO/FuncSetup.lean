import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Basic
import Mathlib.Logic.Function.Iterate
import AvgRare.Basics.SetFamily   -- 依存を薄く保ちつつ将来の接続を意識
import AvgRare.Basics.Ideals      -- 参照だけ（ここでは使わなくても OK）
import LeanCopilot

/-
FuncSetup.lean — 機能的前順序（functional preorder）のセットアップ（論文 §2）

このファイルでは、有限台集合 `V : Finset α` と「V 上に閉じた」写像
  f : {x // x ∈ V} → {x // x ∈ V}
から誘導される前順序を、被覆関係 `⋖` とその反射推移閉包 `≤` として定義します。

論文で使う主な言明（Lemma 2.2, 2.4 など）は **言明だけ** 用意し、
証明は後で他ファイルの準備が整ってから埋めます。

注意:
- ここでは `Preorder` の typeclass は使いません（純粋に関係で進めます）。
- 有限性は `V : Finset α` を介して担保し、要素型は `Elem := {x // x ∈ V}` の部分型で扱います。
- `simpa using` は用いません。必要に応じて `simp` / `simp_all` を使います。
-/

universe u

open scoped BigOperators
open Classical

namespace AvgRare
namespace SPO

variable {α : Type u} [DecidableEq α]

/-- 機能的前順序の“入力データ”。`ground`（有限台集合）と，
    その上に閉じた自己写像 `f` を与える。 -/
structure FuncSetup (α : Type u) [DecidableEq α] where
  ground : Finset α
  f      : {x // x ∈ ground} → {y // y ∈ ground}

namespace FuncSetup

variable (S : FuncSetup α)

@[simp] lemma ground_def : S.ground = S.ground := rfl

/-- 台集合の要素型（部分型）。 -/
abbrev Elem := {x : α // x ∈ S.ground}

@[simp] lemma mem_ground_coe (x : S.Elem) : x.1 ∈ S.ground := x.2

instance instDecidableEqElem : DecidableEq S.Elem := inferInstance

/-- 被覆関係：`x ⋖ y` iff `f x = y`。 -/
def cover (x y : S.Elem) : Prop := S.f x = y

/-- 前順序：被覆の反射推移閉包。 -/
def le (x y : S.Elem) : Prop := Relation.ReflTransGen S.cover x y

/-- 記法：`x ≤ₛ y` / `x ⋖ₛ y` -/
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

/-- 被覆から 1 ステップで `≤`。 -/
lemma cover_to_le {x y : S.Elem} (h : S.cover x y) : S.le x y := by
  -- Relation.ReflTransGen.single
  exact Relation.ReflTransGen.single h

/-- 「反復で到達できる」写像反復。 -/
def iter (k : Nat) : S.Elem → S.Elem :=
  Nat.iterate S.f k

@[simp] lemma iter_zero (x : S.Elem) : S.iter 0 x = x := by
  -- Nat.iterate f 0 = id
  unfold iter
  simp

@[simp] lemma iter_succ (k : Nat) (x : S.Elem) :
    S.iter (k+1) x = S.f (S.iter k x) := by
  -- Nat.iterate.succ
  unfold iter
  simp
  exact Function.iterate_succ_apply' S.f k x

/-- 論文 Lemma 2.2：
`x ≤ y` ↔ ある `k ≥ 0` で `f^[k] x = y`。 -/
lemma le_iff_exists_iter (x y : S.Elem) :
    S.le x y ↔ ∃ k : Nat, S.iter k x = y := by
  -- ReflTransGen ↔ 反復到達 の標準対応
  -- 後で詳細証明を埋める。
  sorry

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
def simSetoid : Setoid S.Elem where
  r := S.sim
  iseqv := ⟨S.sim_refl, S.sim_symm, S.sim_trans⟩

/-- 極大：`x` の上は全部 `x` に戻る（前順序版）。 -/
def maximal (x : S.Elem) : Prop :=
  ∀ ⦃y⦄, S.le x y → S.le y x

@[simp] lemma maximal_iff (x : S.Elem) :
    S.maximal x ↔ (∀ ⦃y⦄, S.le x y → S.le y x) := Iff.rfl

/-- 「同値類が非自明（別の点がある）」の実用形。 -/
def nontrivialClass (x : S.Elem) : Prop :=
  ∃ y : S.Elem, y ≠ x ∧ S.sim x y

/- Lemma 2.4（カードを使わない形）：
同値類が非自明なら、その点は極大。 -/
--lemma maximal_of_nontrivialClass {x : S.Elem}
--    (hx : S.nontrivialClass x) : S.maximal x := by
--  -- 詳細は後で。Lemma 2.2 を使って「戻る」ことを示す標準手順。
--  sorry

/-- 同値類内の任意点も極大。 -/
lemma all_maximal_in_nontrivial_class
    {x y : S.Elem} (hxy : S.sim x y) (hx : S.nontrivialClass x) :
    S.maximal y := by
  -- `x` 極大 ⇒ `y` も極大（対称性＋推移）
  sorry



/- 便利：基の α への射影。 -/
def toGround (x : S.Elem) : α := x.1
@[simp] lemma toGround_mk {x : α} {hx : x ∈ S.ground} :
    S.toGround ⟨x, hx⟩ = x := rfl

/-- `f` の基底 α 成分（必要ならデバッグ用）。 -/
def fBase (x : S.Elem) : α := (S.f x).1
@[simp] lemma fBase_def (x : S.Elem) : S.fBase x = (S.f x).1 := rfl

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

/-- ground の元 `x : α` とその証明から `S.Elem` を作るユーティリティ。 -/
def toElem! {x : α} (hx : x ∈ S.ground) : S.Elem := ⟨x, hx⟩

@[simp] lemma toElem!_val {x : α} (hx : x ∈ S.ground) :
    (S.toElem! hx).1 = x := rfl
@[simp] lemma toElem!_mem {x : α} (hx : x ∈ S.ground) :
    (S.toElem! hx).2 = hx := rfl

/-- `f` の像は常に ground の中。 -/
@[simp] lemma f_mem_ground (x : S.Elem) : (S.f x).1 ∈ S.ground := (S.f x).2

/-- **復活版**：非自明同値類に属する `u` は自己固定点ではない（`f u ≠ u`）。 -/
lemma f_ne_of_nontrivialClass {u : S.Elem}
    (h : S.nontrivialClass u) : S.f u ≠ u := by
  /- 方針：もし `S.f u = u` なら，`u` から到達できる点は `u` のみ。
     しかし非自明同値類なら `u ≤ y` かつ `y ≠ u` なる `y` が存在して矛盾。
     ここは前半整備なので証明は後で埋めます。 -/
  sorry

/-- （使い勝手用）非自明同値類のとき，後継 `f u` を
    「u と異なる ground の元」として取り出す形。 -/
lemma exists_succ_partner_of_nontrivial
    {u : α} (hu : u ∈ S.ground)
    (h : S.nontrivialClass (S.toElem! hu)) :
    ∃ (v : α) (hv : v ∈ S.ground), v ≠ u := by
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

-- 部分型の同値 ≠ から基底の ≠ を取り出す補助
private lemma ne_val_of_ne {x y : {a // a ∈ S.ground}} (h : x ≠ y) : x.1 ≠ y.1 := by
  intro hval
  apply h
  apply Subtype.ext
  exact hval

/-- `S.ground.erase u` 上の像を作るための“付け替え写像”（本体）。
    `x` はすでに `S.ground.erase u` 上の点（部分型）として与えられる。 -/
def eraseOneMap
    (u v : {a // a ∈ S.ground}) (hvne : v ≠ u) :
    {x // x ∈ S.ground.erase u.1} → {y // y ∈ S.ground.erase u.1} :=
  fun x => by
    classical
    -- x : {x // x ∈ S.ground.erase u} から ground への包含をほどく
    have hx_in_ground : x.1 ∈ S.ground := (Finset.mem_erase.mp x.2).2
    -- 元の写像で 1 歩進める
    let y : {a // a ∈ S.ground} := S.f ⟨x.1, hx_in_ground⟩
    -- 場合分け：y = u なら v に付け替え，そうでなければ y のまま
    by_cases hyu : y = u
    · -- 出力は v。v が `ground.erase u` に入ることを示す。
      have hv_val_ne : v.1 ≠ u.1 := by
        intro hval
        apply hvne
        apply Subtype.ext
        exact hval
      have hv_in_erase : v.1 ∈ S.ground.erase u.1 := by
        -- mem_erase ↔ (≠ ∧ ∈)
        exact Finset.mem_erase.mpr ⟨hv_val_ne, v.2⟩
      exact ⟨v.1, hv_in_erase⟩
    · -- 出力は y。y が `ground.erase u` に入ることを示す。
      have hy_val_ne : y.1 ≠ u.1 := by
        intro hval
        apply hyu
        apply Subtype.ext
        exact hval
      have hy_in_erase : y.1 ∈ S.ground.erase u.1 := by
        exact Finset.mem_erase.mpr ⟨hy_val_ne, y.2⟩
      exact ⟨y.1, hy_in_erase⟩

/-- ground を `ground.erase u` に差し替え，`f` を上の付け替え写像に。 -/
def eraseOne (u v : {a // a ∈ S.ground}) (hvne : v ≠ u) : FuncSetup α :=
{ ground := S.ground.erase u.1
, f      := S.eraseOneMap u v hvne }

def eraseOneUsingSucc (u : S.Elem)
    (hNontriv : S.nontrivialClass u) : FuncSetup α :=
  FuncSetup.eraseOne S u (S.f u)
    (FuncSetup.f_ne_of_nontrivialClass (S := S) hNontriv)

-- 便利記法：S の台集合上の要素
--abbrev Elem := S.Elem

noncomputable def principalIdeal (S : FuncSetup α) (a : α) (ha : a ∈ S.ground) : Finset α := by
  classical
  -- attach は {y // y ∈ ground}、述語は `S.le y ⟨a,ha⟩`
  exact (S.ground.attach.filter (fun (y : {z // z ∈ S.ground}) => S.le y ⟨a, ha⟩)).map
    ⟨Subtype.val, by simp_all only [Subtype.val_injective]⟩


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
  classical
  constructor
  · intro h
    rcases (S.mem_principalIdeal_iff (a:=a) (y:=y) ha).1 h with ⟨hy', hle⟩
    -- 証明部を差し替え（部分型の値は同じなので `Subtype.ext` で輸送）
    have ey : (⟨y, hy'⟩ : S.Elem) = ⟨y, hy⟩ := Subtype.ext (by rfl)
    -- `simpa` を使わず書換えで閉じる
    -- `hle : S.le ⟨y,hy'⟩ ⟨a,ha⟩` を ey で左引数だけ置換
    -- 置換は `Eq.ndrec` 相当だが、ここでは `cases ey` で十分
    cases ey
    exact hle
  · intro hle
    exact (S.mem_principalIdeal_iff (a:=a) (y:=y) ha).2 ⟨hy, hle⟩




/-

variable (S : FuncSetup α)

@[inline] def toElem! {x : α} (hx : x ∈ S.ground) : S.Elem := ⟨x, hx⟩

@[simp] lemma toElem!_val {x : α} {hx : x ∈ S.ground} :
    (S.toElem! (x:=x) hx).1 = x := rfl

@[simp] lemma toElem!_mem {x : α} {hx : x ∈ S.ground} :
    (S.toElem! (x:=x) hx).2 = hx := rfl
-/

end FuncSetup

section IterateRTG
variable {α : Type*} (f : α → α)

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


lemma maximal_of_nontrivialClass
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
    -- すると hk : f^[0] u = v、すなわち u = v で矛盾
    -- `cases` で k=0,ℓ=0 を入れてもよいが、ここでは L=0 だけで十分
    -- L=0 から k=0 は必ずしも出せませんが、hk だけで矛盾が作れます：
    -- 「u ⟶* v」で k=0 しかないなら v=u。厳密には `hk` の値に依存しますが、
    -- ここでは簡潔に：
    -- `have : u = v := by simpa [Nat.iterate, this] using hk` を避けるため、
    -- 直接 `cases` で k=0 として扱ってもOKです。
    -- ただ、以後の証明で L>0 は不要（m ≤ L*(m+1) は L=0 でも成り立つ）ので、Lpos は実は不要です。
    -- 従って、このブロック自体を削っても構いません。
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
      -- hm : f^[m] u = x
      -- 左辺の `Nat.iterate f t (Nat.iterate f m u)` を `Nat.iterate f t x` に
      -- 置換する
      -- `rw [hm]` を at に
      -- `simp` は使わず `rw` でOK
      -- （`tmp` の左辺内部がきちんと書換えられる）
      -- 注意：Lean によっては `rw [hm] at tmp` の後、`exact tmp`
      -- と書くのが最も確実です。
      -- 実際の書換え：
      -- （`tmp` は等式なので `at` が必要）
      -- ここで具体的に：
      --   tmp : Nat.iterate f t (Nat.iterate f m u) = Nat.iterate f (t + m) u
      --   →    Nat.iterate f t x = Nat.iterate f (t + m) u
      -- となります。
      have tmp' := tmp
      -- 書換え
      -- `rw` はゴール／仮定に対する戦術なので、`have` の行で `rw` するのではなく、
      -- 新しい仮定を作ってから `rw` を当てます。
      -- ここでは `tmp'` に当てる：
      --   `rw [hm] at tmp'`
      -- これにより型が変わるので、そのまま返します。
      -- ただし、このエディタ外では `rw` を `tmp'` に当てることができないため、
      -- 代替として `calc` で同じ式を作ります。
      -- より簡潔に、`calc` で直接：
      --   f^[t] x = f^[t] (f^[m] u) := by rw [←hm]
      --   ...    = f^[t+m] u         := by exact base
      -- を書きます。
      -- こちらの方が確実です。
      -- 差し替え：
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
      -- `this` を用いて右辺を書き換え
      -- `Eq.trans` を使ってもよいですが、ここも `calc` で：
      --   f^[t+m] u = f^[L*(m+1)] u
      --   （指数の等式に基づく置換）
      -- 置換は `rw` の方が簡潔です。
      -- `rw [this]` を `Nat.iterate f (t+m) u` 側に当てたいので、
      -- 下のトップレベルでまとめて使います。
      -- いったん戻ります。

      -- 直接返す：
      -- `by cases this; rfl` の形にできます（指数が同じなら refl）
      -- ただし `cases` は指数の等式で置換してしまうので、ここは：
      --   `have := this; cases this; rfl`
      -- でもOK。簡潔に `rw [this]` は tactic 文脈が必要。
      -- ここでは calc の方へ寄せます：
      -- 置換を呼び出し元で行うため、この補題は使わずに先で `rw` します。
      -- （このローカル have は不要になったので消します）
      -- 以降、上で `base'` を使う側で `rw [ht_add]` を直接当てます。
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
    -- 以上を直列に当てていく
    -- まず base' を取得
    -- その右辺を `rw [ht_add]`、さらに `rw [h_mul]`、最後に `rw [h_fix]`
    -- tactic を使わず `calc` で書きます。
    -- base' : f^[t] x = f^[t+m] u
    -- なので：
    -- f^[t] x
    --   = f^[t+m] u           : base'
    --   = f^[L*(m+1)] u       : by rw [ht_add]
    --   = (f^[L])^[m+1] u     : by rw [h_mul]
    --   = u                   : by rw [h_fix]
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

end IterateRTG

/- 記法を開く（必要な箇所で使えるように）。 -/
open FuncSetup (le cover)


end SPO
end AvgRare

/-
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

--------

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
-/
