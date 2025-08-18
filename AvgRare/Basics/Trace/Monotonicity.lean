import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import AvgRare.Basics.SetFamily
import AvgRare.Basics.Trace.Common

universe u

namespace AvgRare
open scoped BigOperators
open Classical

variable {α : Type u} [DecidableEq α]

/-! ------------------------------------------------------------
  便利補題：Indicator 和 = 個数（Nat 版）
  X 上で `if v∈B then 1 else 0` を足すと |B|（ただし B ⊆ X）
------------------------------------------------------------- -/
private lemma sum_indicator_eq_card_nat
  (X B : Finset α) (hBX : B ⊆ X) :
  ∑ v ∈ X, (if v ∈ B then (1 : Nat) else 0) = B.card := by
  classical
  -- (X.filter (·∈B)).card = ∑_{v∈X} if v∈B then 1 else 0
  have h1 :
      (X.filter (fun v => v ∈ B)).card
        = ∑ v ∈ X, (if v ∈ B then (1 : Nat) else 0) := by
    -- Finset.card_filter (Nat 版)
    have h := (Finset.card_filter (s := X) (p := fun v => v ∈ B))
    -- h : (X.filter (fun v => v ∈ B)).card
    --     = (∑ v ∈ X, dite (v ∈ B) (fun _ => 1) (fun _ => 0))
    -- 右辺のditeはifにβ簡約される
    -- すでに if 形式なのでそのまま使える
    exact h
  -- filter を B に戻す（B ⊆ X だから落ちない）
  have hfilter : X.filter (fun v => v ∈ B) = B := by
    apply Finset.ext
    intro v
    constructor
    · intro hv
      exact (Finset.mem_filter.mp hv).2
    · intro hv
      exact Finset.mem_filter.mpr ⟨hBX hv, hv⟩
  -- まとめ
  -- ∑_{v∈X} if v∈B then 1 else 0 = (X.filter (·∈B)).card = B.card
  have : ∑ v ∈ X, (if v ∈ B then (1 : Nat) else 0) = B.card := by
    -- h1 を左右反転して使う
    have := congrArg id h1
    -- h1 : (X.filter ...).card = ∑ ...
    -- これを = の両辺を入れ替えてから hfilter で置換
    -- まず左辺を B.card に
    --   (X.filter ...).card = B.card
    -- を作る
    -- 上の h1 を使わず、直接置換した等式を作る方が明快
    -- (X.filter ...).card = B.card
    have hleft : (X.filter (fun v => v ∈ B)).card = B.card := by
      rw [hfilter]
    -- 右辺はそのまま
    -- よって求める等式
    --   ∑ v∈X, if v∈B then 1 else 0 = B.card
    -- を得るため、h1 を右辺に、hleft を左辺にそれぞれ代入
    -- h1: (X.filter ...).card = sum ...
    -- したがって sum ... = (X.filter ...).card
    -- それに hfilter で置換
    -- 形式的に書く：
    --   have := h1.symm; rw [hfilter] at this; exact this
    -- でもよい
    have hx := h1.symm
    -- hx : ∑ ... = (X.filter ...).card
    -- 右辺を B.card に
    rw [hfilter] at hx
    exact hx
  exact this

--これ以降は、1頂点ずつtraceする場合は使わないかも。
/-! ------------------------------------------------------------
  主結果（Nat 版）：
  ∑_{B ⊆ X} |B| = |X| · 2^{|X|-1}
------------------------------------------------------------- -/
lemma sum_card_over_powerset_nat (X : Finset α) :
  ∑ B ∈ X.powerset, B.card = X.card * Nat.pow 2 (X.card - 1) := by
  classical
  -- B.card を indicator に展開して和の順序を交換
  have hBX : ∀ {B}, B ∈ X.powerset → B ⊆ X := by
    intro B hB
    exact (Finset.mem_powerset.mp hB)
  -- ステップ1：|B| を indicator 和に
  have step1 :
    ∑ B ∈ X.powerset, B.card
      = ∑ B ∈ X.powerset, ∑ v ∈ X, (if v ∈ B then 1 else 0) := by
    apply Finset.sum_congr rfl
    intro B hB
    -- |B| = ∑_{v∈X} 1_{v∈B}
    have hb := sum_indicator_eq_card_nat X B (hBX hB)
    -- hb : ∑ v ∈ X, (if v ∈ B then 1 else 0) = B.card
    -- 両辺を入れ替える
    have hb' : B.card = ∑ v ∈ X, (if v ∈ B then 1 else 0) := by
      exact hb.symm
    -- これで左辺の B.card を右辺の和に置換
    exact hb'
  -- ステップ2：和の順序交換
  have step2 :
    ∑ B ∈ X.powerset, (∑ v ∈ X, (if v ∈ B then (1 : Nat) else 0))
      = ∑ v ∈ X, (∑ B ∈ X.powerset, (if v ∈ B then (1 : Nat) else 0)) := by
    exact Finset.sum_comm
  -- 固定 v の寄与を数える
  have count_v :
    ∀ {v}, v ∈ X →
      ∑ B ∈ X.powerset, (if v ∈ B then (1 : Nat) else 0)
        = (X.powerset.filter (fun B => v ∈ B)).card := by
    intro v hv
    -- ∑_{B∈P(X)} if v∈B then 1 else 0 = #(B⊆X ∧ v∈B)
    -- card_filter の左右反転形を使う
    -- (X.powerset.filter (·)) の card = その indicator 和
    -- よって indicator 和 = その card
    -- 厳密に：
    have h := (Finset.card_filter (s := X.powerset) (p := fun B => v ∈ B))
    -- h : (X.powerset.filter ...).card
    --   = ∑ B∈X.powerset, if v∈B then 1 else 0
    -- 両辺入れ替え
    have : ∑ B ∈ X.powerset, (if v ∈ B then (1 : Nat) else 0)
            = (X.powerset.filter (fun B => v ∈ B)).card := by
      exact h.symm
    exact this
  -- v を含む部分集合 ↔ (X.erase v) の部分集合に v を挿入（全単射）
  have filter_eq_image :
    ∀ {v}, v ∈ X →
      (X.powerset.filter (fun B => v ∈ B))
        = (X.erase v).powerset.image (fun T => insert v T) := by
    intro v hv
    apply Finset.ext
    intro B
    constructor
    · intro hB
      rcases Finset.mem_filter.1 hB with ⟨hBX', hvB⟩
      -- B.erase v ⊆ X.erase v
      have sub1 : B.erase v ⊆ X.erase v := by
        intro x hx
        have hxB : x ∈ B := (Finset.mem_erase.1 hx).2
        have hxX : x ∈ X := (Finset.mem_powerset.1 hBX') hxB
        have hx_ne : x ≠ v := (Finset.mem_erase.1 hx).1
        exact Finset.mem_erase.2 ⟨hx_ne, hxX⟩
      have sub1' : B.erase v ∈ (X.erase v).powerset := by
        exact Finset.mem_powerset.mpr sub1
      -- 画像のメンバーであることを示す
      refine Finset.mem_image.2 ?_
      refine ⟨B.erase v, sub1', ?_⟩
      -- insert v (B.erase v) = B  （v∈B）
      have : insert v (B.erase v) = B := by
        -- Finset.insert_erase hvB
        exact Finset.insert_erase hvB
      exact this
    · intro h
      rcases Finset.mem_image.1 h with ⟨T, hT, hB⟩
      -- T ⊆ X.erase v
      have hTsub : T ⊆ X.erase v := Finset.mem_powerset.1 hT
      -- v ∉ T
      have hvT : v ∉ T := by
        have hv_notin : v ∉ X.erase v := by
          simp [hv]
        -- T ⊆ X.erase v ⇒ v∉T
        exact fun hv' => hv_notin (hTsub hv')
      -- `insert v T ⊆ X` かつ `v ∈ insert v T`
      -- powerset 側の条件と filter 側の条件を満たす
      have hsubX : insert v T ⊆ X := by
        intro x hx
        by_cases hxv : x = v
        · -- x=v
          exact by
            subst hxv
            exact hv
        · -- x∈T
          have hxT : x ∈ T := by
            -- x∈insert v T, x≠v ⇒ x∈T
            have := by
              exact α
            --(Finset.mem_insert.mpr (Or.inr rfl))
            -- より簡単に
            -- from hx : x∈insert v T, we deduce x∈T when x≠v
            -- 展開して使う
            have hx' : x ∈ T := by
              -- Finset.mem_insert の分解
              have hx'' := (Finset.mem_insert.mp hx)
              cases hx'' with
              | inl hvx =>
                  -- hvx : x = v （矛盾）
                  exact False.elim (hxv hvx)
              | inr hxt =>
                  exact hxt
            -- ここから X へ
            have hxX : x ∈ X := (Finset.mem_erase.1 (hTsub hx')).2
            exact hx'
          exact Finset.mem_of_mem_erase (hTsub hxT)
      have hv_in : v ∈ insert v T := by
        exact by
          apply Finset.mem_insert_self
      -- 以上より filter へ入る
      have : insert v T ∈ X.powerset := by
        exact Finset.mem_powerset.mpr hsubX
      -- さらに v∈insert v T
      -- よって filter に入る
      rw [Finset.mem_filter]
      constructor
      · subst hB
        simp_all only [Finset.mem_powerset, implies_true, Finset.sum_ite_mem, Finset.sum_const, smul_eq_mul, mul_one,
         Finset.sum_boole, Nat.cast_id, Finset.mem_insert, or_false, Finset.mem_image]
      · subst hB
        simp_all only [Finset.mem_powerset, implies_true, Finset.sum_ite_mem, Finset.sum_const, smul_eq_mul, mul_one,
          Finset.sum_boole, Nat.cast_id, Finset.mem_insert, or_false, Finset.mem_image]

  -- `image` の単射性（v∉T 上で insert v は単射）
  have inj_insert :
    ∀ {v}, v ∈ X →
      Set.InjOn (fun T : Finset α => insert v T) (↑(X.erase v).powerset) := by
    intro v hv
    intro T1 hT1 T2 hT2 hEq
    -- v∉Ti
    have hvT1 : v ∉ T1 := by
      have : T1 ⊆ X.erase v := Finset.mem_powerset.1 hT1
      intro hv1
      have : v ∈ X.erase v := this hv1
      -- 矛盾
      have : False := by
        -- simp [hv] at this
        -- 直接展開して矛盾
        -- v∈X.erase v ↔ v∈X ∧ v≠v
        -- 後半が偽
        -- ここは `simp [hv]` を使う代わりに論理で書く
        -- v∈X.erase v なら v∈X ∧ v≠v
        -- しかし hv : v∈X かつ 自明に v=v
        exact False.elim (by
          -- 無矛盾化のため空の False.elim は使えないので、`by cases` でつぶすのもOK
          -- ここでは別ルート：Finset.mem_erase の iff を使う
          have hx := (Finset.mem_erase.mp this)
          -- hx : v ≠ v ∧ v ∈ X
          -- 矛盾は hx.1 : v ≠ v
          exact hx.1 rfl)
      exact this.elim
    have hvT2 : v ∉ T2 := by
      have : T2 ⊆ X.erase v := Finset.mem_powerset.1 hT2
      intro hv2
      have : v ∈ X.erase v := this hv2
      -- 同様に矛盾
      have : False := by
        have hx := (Finset.mem_erase.mp this)
        exact hx.1 rfl
      exact this.elim
    -- 両辺を erase v して戻す
    have := congrArg (fun (S : Finset α) => S.erase v) hEq
    -- erase (insert v T) = T （v∉T）
    have hL : (insert v T1).erase v = T1 := by
      exact Finset.erase_insert hvT1
    have hR : (insert v T2).erase v = T2 := by
      exact Finset.erase_insert hvT2
    -- 置換
    simp_all only [Finset.mem_powerset, implies_true, Finset.sum_ite_mem, Finset.sum_const, smul_eq_mul, mul_one,
      Finset.sum_boole, Nat.cast_id, Finset.coe_powerset, Finset.coe_erase, Set.mem_preimage, Set.mem_powerset_iff,
      Finset.erase_insert_eq_erase, not_false_eq_true, Finset.erase_eq_of_notMem]

  -- 以上を用いて計算
  calc
    ∑ B ∈ X.powerset, B.card
        = ∑ B ∈ X.powerset, ∑ v ∈ X, (if v ∈ B then 1 else 0) := step1
    _   = ∑ v ∈ X, ∑ B ∈ X.powerset, (if v ∈ B then 1 else 0) := step2
    _   = ∑ v ∈ X, (X.powerset.filter (fun B => v ∈ B)).card := by
          apply Finset.sum_congr rfl
          intro v hv
          exact count_v hv
    _   = ∑ v ∈ X, (X.erase v).powerset.card := by
          apply Finset.sum_congr rfl
          intro v hv
          -- filter を image に、さらに image の card = 元の card（単射）
          have hfeq := filter_eq_image (v := v) hv
          have hcard :
            (X.powerset.filter (fun B => v ∈ B)).card
              = ((X.erase v).powerset.image (fun T => insert v T)).card := by
            rw [hfeq]
          have himg :
            ((X.erase v).powerset.image (fun T => insert v T)).card
              = (X.erase v).powerset.card := by
            have := Finset.card_image_iff.mpr (inj_insert (v := v) hv)
            exact this
          -- 連結
          rw [hcard, himg]
    _   = ∑ _v ∈ X, Nat.pow 2 (X.card - 1) := by
          -- |P(X\{v})| = 2^{|X|-1}
          apply Finset.sum_congr rfl
          intro v hv
          -- (X.erase v).powerset.card = 2 ^ (X.erase v).card
          have hpow : (X.erase v).powerset.card = Nat.pow 2 (X.erase v).card := by
            -- Finset.card_powerset
            have hp := (Finset.card_powerset (s := X.erase v))
            -- hp : (X.erase v).powerset.card = 2 ^ (X.erase v).card
            exact hp
          -- (X.erase v).card = X.card - 1
          have hcard : (X.erase v).card = X.card - 1 := by
            -- Finset.card_erase_of_mem
            exact Finset.card_erase_of_mem hv
          -- 置換
          rw [hpow]
          rw [hcard]
    _   = X.card * Nat.pow 2 (X.card - 1) := by
          -- 定数和：∑_{v∈X} c = |X| * c
          -- Finset.sum_const_nat を使う
          exact Finset.sum_const_nat fun x => congrFun rfl

/-- Int 版：`∑_{B ⊆ X} |B| = |X| · 2^{|X| - 1}` -/
lemma sum_card_over_powerset_int (X : Finset α) :
  ((∑ B ∈ X.powerset, B.card : Nat) : Int)
    = (X.card : Int) * (2 : Int) ^ (X.card - 1) := by
  classical
  have hNat := sum_card_over_powerset_nat (α := α) X
  -- 左辺を Int に持ち上げ
  have hL : (Nat.cast (∑ B ∈ X.powerset, B.card)) = (∑ B ∈ X.powerset, B.card : Nat) := by
    rfl
  -- 右辺を Int に持ち上げ
  have hR :
    (Nat.cast (X.card * Nat.pow 2 (X.card - 1)))
      = (X.card : Int) * (2 : Int) ^ (X.card - 1) := by
    -- cast (a*b) = cast a * cast b
    -- cast (2^(...)) = (2:Int)^(...)
    rw [Nat.cast_mul]
    simp_all only [Nat.pow_eq, Nat.cast_mul, Nat.cast_id, Nat.cast_pow, Nat.cast_ofNat]
  -- 置換
  -- cast (lhs) = cast (rhs)
  rw [←hL]
  rw [hNat]
  exact hR

/-- 冪集合の要素数：`|𝒫 X| = 2^{|X|}`（Int 版） -/
lemma card_powerset_int (X : Finset α) :
  ((X.powerset.card : Nat) : Int) = (2 : Int) ^ (X.card) := by
  classical
  -- Nat 版：|P(X)| = 2^{|X|}
  have hNat : (X.powerset.card : Nat) = Nat.pow 2 X.card := by
    exact (Finset.card_powerset (s := X))
  -- Int へ持ち上げ
  have hCast :
    ((X.powerset.card : Nat) : Int)
      = ((Nat.pow 2 X.card : Nat) : Int) := by
    exact congrArg (fun n : Nat => (n : Int)) hNat
  -- 右辺を (2:Int)^|X| に
  have hPow :
    ((Nat.pow 2 X.card : Nat) : Int) = (2 : Int) ^ X.card := by
    simp_all only [Finset.card_powerset, Nat.pow_eq, Nat.cast_pow, Nat.cast_ofNat]

  -- 結論
  rw [hCast]
  exact hPow


end AvgRare

/-
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import AvgRare.Basics.SetFamily
import AvgRare.Basics.Trace.Common


universe u

namespace AvgRare
open scoped BigOperators
open Classical

variable {α : Type u} [DecidableEq α]

/-
=======================================================
  ローカル補助：冪集合・指示和・“下閉包 ∪ の上界”を準備
  ここから下はこのファイルだけで完結します。
========================================================
-/
private lemma sum_indicator_eq_card_nat
  (X B : Finset α) (hBX : B ⊆ X) :
  ∑ v ∈ X, (if v ∈ B then (1 : Nat) else 0) = B.card := by
  classical
  -- 1) indicator の和を filter 側の定数和に移す
  have h1 :
      ∑ v ∈ X, (if v ∈ B then (1 : Nat) else 0)
        = ∑ v ∈ X.filter (fun v => v ∈ B), (1 : Nat) := by
    -- sum_filter : ∑_{x∈s.filter p} f x = ∑_{x∈s} (if p x then f x else 0)
    -- なので、左右をひっくり返して使う
    have := Finset.sum_filter
              (s := X) (p := fun v => v ∈ B) (f := fun _ => (1 : Nat))
    -- this : ∑ v∈X.filter (·∈B), 1 = ∑ v∈X, if v∈B then 1 else 0
    simpa using this.symm

  -- 2) 定数 1 の和は個数
  have h2 :
      ∑ v ∈ X.filter (fun v => v ∈ B), (1 : Nat)
        = (X.filter (fun v => v ∈ B)).card := by
    -- `sum_const_nat` : ∑_{x∈s} c = s.card * c
    -- ここでは c = 1 なので s.card
    simp_all only [Finset.sum_ite_mem, Finset.sum_const, smul_eq_mul, mul_one]

  -- 3) filter を B に戻す（B ⊆ X を使用）
  have hfilter : X.filter (fun v => v ∈ B) = B := by
    apply Finset.ext; intro v; constructor
    · intro hv; exact (Finset.mem_filter.mp hv).2
    · intro hv; exact Finset.mem_filter.mpr ⟨hBX hv, hv⟩

  -- まとめ
  simp_all only [Finset.sum_ite_mem, Finset.sum_const, smul_eq_mul, mul_one]

lemma sum_card_over_powerset_nat (X : Finset α) :
  ∑ B ∈ X.powerset, B.card = X.card * Nat.pow 2 (X.card - 1) := by
  classical
  -- まず ∑_{B⊆X} |B| を indicator で ∑_{v∈X} に入れ替える
  have hBX : ∀ {B}, B ∈ X.powerset → B ⊆ X := by
    intro B hB; exact (Finset.mem_powerset.mp hB)
  have step1 :
    ∑ B ∈ X.powerset, B.card
      = ∑ B ∈ X.powerset, (∑ v ∈ X, (if v ∈ B then (1 : Nat) else 0)) := by
    apply Finset.sum_congr rfl
    intro B hB
    -- `B ⊆ X` を使って indicator の和が |B| になる
    simp_all only [Finset.mem_powerset, implies_true, Finset.sum_ite_mem, Finset.sum_const, smul_eq_mul, mul_one]
    congr
    ext a : 1
    simp_all only [Finset.mem_inter, iff_and_self]
    intro a_1
    exact hB a_1
  -- 和の順序交換
  have step2 :
    ∑ B ∈ X.powerset, (∑ v ∈ X, (if v ∈ B then (1 : Nat) else 0))
      = ∑ v ∈ X, (∑ B ∈ X.powerset, (if v ∈ B then (1 : Nat) else 0)) := by
    -- `Finset.sum_comm` の 2変数版
    exact Finset.sum_comm
  -- 固定 v に対し、`v∈B` のときだけ 1 を数えるので個数＝`(X.erase v).powerset.card`
  have count_v :
    ∀ {v}, v ∈ X →
      ∑ B ∈ X.powerset, (if v ∈ B then (1 : Nat) else 0)
        = (X.erase v).powerset.card := by
    intro v hv
    -- `insert v` と `erase v` で 1-1 対応：T ⊆ X.erase v ↔ B := insert v T
    -- まず `{B⊆X | v∈B}` と `image (insert v)` の同一視
    have eqFilt :
      (X.powerset.filter (fun B => v ∈ B))
        = (X.erase v).powerset.image (fun T => insert v T) := by
      ext B; constructor
      · intro hB
        have hBX : B ⊆ X := by
          simp_all only [Finset.mem_powerset, implies_true, Finset.sum_ite_mem, Finset.sum_const, smul_eq_mul, mul_one,
            Finset.sum_boole, Nat.cast_id, Finset.mem_filter]
        have hvB : v ∈ B := (Finset.mem_filter.mp hB).2
        refine Finset.mem_image.mpr ?_
        refine ⟨B.erase v, ?_, ?_⟩
        · -- `B.erase v ⊆ X.erase v`
          have : B.erase v ⊆ X.erase v := by
            intro x hx
            have hxB : x ∈ B := (Finset.mem_erase.mp hx).2
            have hxX : x ∈ X := hBX hxB
            have hx_ne : x ≠ v := (Finset.mem_erase.mp hx).1
            exact Finset.mem_erase.mpr ⟨hx_ne, hxX⟩
          -- powerset へ
          exact Finset.mem_powerset.mpr this
        · -- 画像は insert v (B.erase v) = B
          -- v∈B なので erase/insert が戻る
          -- `Finset.insert_erase` は `h : v ∈ B` を仮定
          simp [Finset.insert_erase hvB]
      · intro hB
        rcases Finset.mem_image.mp hB with ⟨T, hT, rfl⟩
        have hT_sub : T ⊆ X.erase v := (Finset.mem_powerset.mp hT)
        have hv_notin_T : v ∉ T := by
          have : v ∉ X.erase v := by simp [hv]
          -- T ⊆ X.erase v ⇒ v∉T
          exact fun hvT => this (hT_sub hvT)
        -- `insert v T ⊆ X` かつ `v ∈ insert v T`
        refine Finset.mem_filter.mpr ?_
        constructor
        · -- `insert v T ⊆ X`
          have : T ⊆ X := by
            intro x hx; exact (Finset.mem_erase.mp (hT_sub hx)).2
          -- 挿入しても X を越えない（v∈X、T⊆X）
          refine Finset.mem_powerset.mpr ?_
          intro x hx
          by_cases hxv : x = v
          · subst hxv; exact hv
          · have : x ∈ T := by
              -- x∈insert v T, x≠v ⇒ x∈T
              simpa [Finset.mem_insert, hxv] using hx
            (expose_names; exact this_1 this)
        · -- v ∈ insert v T
          exact by simp
    -- これで `filter` の個数＝右の image の個数
    have cardFilt :
      (X.powerset.filter (fun B => v ∈ B)).card
        = ((X.erase v).powerset.image (fun T => insert v T)).card := by
      rw [eqFilt]
    -- 右辺は `image` の単射性から powerset の個数に等しい
    have injIns : Set.InjOn (fun T : Finset α => insert v T) (↑(X.erase v).powerset) := by
      intro T1 hT1 T2 hT2 hEq
      -- `v ∉ T` の上で `insert v` は単射
      have hvT1 : v ∉ T1 := by
        have : T1 ⊆ X.erase v := (Finset.mem_powerset.mp hT1)
        exact fun hv1 => by
          have hv_in : v ∈ X.erase v := this hv1
          simp [hv] at hv_in
      have hvT2 : v ∉ T2 := by
        have : T2 ⊆ X.erase v := (Finset.mem_powerset.mp hT2)
        exact fun hv2 => by
          have hv_in : v ∈ X.erase v := this hv2
          simp [hv] at hv_in
      -- `erase v` をかけると戻る
      have : T1 = T2 := by
        -- `Finset.insert_injective_on` があれば使ってOK。無ければ手作業で：
        -- 両辺から v を消すと等しい
        have := congrArg (fun (S : Finset α) => S.erase v) hEq
        -- v∉T なので `erase (insert v T) = T`
        simpa [Finset.erase_insert, hvT1, hvT2] using this
      exact this
    have cardImage :
      ((X.erase v).powerset.image (fun T => insert v T)).card
        = (X.erase v).powerset.card := by
      -- sum_image 用の既知補題 `card_image_iff` でも可。ここは InjOn から。
      exact Finset.card_image_iff.mpr injIns
    -- 以上で「indicator の和 = filter の個数 = (X.erase v).powerset.card」
    calc
      ∑ B ∈ X.powerset, (if v ∈ B then 1 else 0)
          = ∑ _B ∈ (X.powerset.filter (fun B => v ∈ B)), (1 : Nat) := by
              -- 0/1 の和を filter へ
              -- 「if p then 1 else 0」の和は filter の個数
              -- 直接：分配して 0 側は消える（`Finset.sum_filter` を自前展開）
              have : X.powerset.filter (fun B => v ∈ B) ⊆ X.powerset := by
                exact Finset.filter_subset _ _
              -- 分解：s = s.filter p ⊔ s.filter ¬p
              have hdisj : Disjoint (X.powerset.filter (fun B => v ∈ B))
                                    (X.powerset.filter (fun B => v ∉ B)) := by
                exact Finset.disjoint_filter_filter_neg X.powerset X.powerset fun B => v ∈ B
              have hUnion :
                (X.powerset.filter (fun B => v ∈ B))
                ∪ (X.powerset.filter (fun B => v ∉ B))
                = X.powerset := by
                exact Finset.filter_union_filter_neg_eq (fun B => v ∈ B) X.powerset
              -- 和の分解
              have := by
                 exact α
              -- ここから `rw` で整理
              -- ∑ over powerset (if ...) = ∑ over filter(...)=1 + ∑ over filter(¬...)=0
              -- 直接書き換える方が短いので `simp` を使います
              -- ただし `simpa` を避けるため `simp` を2回
              -- 最終式だけ書きます：
              -- （簡潔に）
              -- use standard simp:
              -- `by classical; simpa [Finset.sum_filter, Finset.add_comm, Finset.filter_true_of_mem]`
              -- というスタイルでもOKですが、ここでは省略
              -- ↓ 1 行で済ませます
              simp_all only [Finset.mem_powerset, implies_true, Finset.sum_ite_mem, Finset.sum_const, smul_eq_mul, mul_one,
                 Finset.sum_boole, Nat.cast_id, Finset.card_powerset, Finset.card_erase_of_mem, Finset.coe_powerset,
                 Finset.coe_erase, Nat.cast_pow, Nat.cast_ofNat]
      _   = (X.powerset.filter (fun B => v ∈ B)).card := by
              -- 定数 1 の和 = 個数
              rw [Finset.sum_const, nsmul_eq_mul]
              simp_all only [Finset.mem_powerset, implies_true, Finset.sum_ite_mem, Finset.sum_const, smul_eq_mul, mul_one,
                Finset.sum_boole, Nat.cast_id, Finset.card_powerset, Finset.card_erase_of_mem, Finset.coe_powerset,
                Finset.coe_erase, Nat.cast_pow, Nat.cast_ofNat]
      _   = (X.erase v).powerset.card := by
              rw [cardFilt, cardImage]

  -- まとめ
  calc
    ∑ B ∈ X.powerset, B.card
        = ∑ B ∈ X.powerset, (∑ v ∈ X, (if v ∈ B then 1 else 0)) := step1
    _   = ∑ v ∈ X, (∑ B ∈ X.powerset, (if v ∈ B then 1 else 0)) := step2
    _   = ∑ v ∈ X, (X.erase v).powerset.card := by
            apply Finset.sum_congr rfl; intro v hv; exact count_v hv
    _   = ∑ _v ∈ X, Nat.pow 2 (X.card - 1) := by
            -- `card_powerset` と `card_erase_of_mem`
            apply Finset.sum_congr rfl
            intro v hv
            have : (X.erase v).powerset.card = Nat.pow 2 (X.erase v).card := by
              -- powerset の要素数
              rw [Finset.card_powerset]
              exact rfl
            -- X.erase v のカードは X.card - 1
            have : (X.erase v).card = X.card - 1 := by
              -- `card_erase_add_one`
              have := Finset.card_erase_add_one hv
              -- X.card = (X.erase v).card + 1
              -- よって (X.erase v).card = X.card - 1
              exact Finset.card_erase_of_mem hv
            -- 置換
            -- まず powerset.card を 2^(|X.erase v|) に
            -- つぎに |X.erase v| を X.card - 1 に
            -- 2行に分けて `rw`
            have hpow := Finset.card_powerset (s := X.erase v)
            -- hpow : (X.erase v).powerset.card = 2 ^ (X.erase v).card
            -- 置換
            rw [hpow, this]
            simp_all only [Finset.mem_powerset, implies_true, Finset.sum_ite_mem, Finset.sum_const, smul_eq_mul, mul_one,
               Finset.card_powerset, Finset.card_erase_of_mem, Finset.sum_boole, Nat.cast_id, Nat.pow_eq]
    _   = X.card * Nat.pow 2 (X.card - 1) := by
            -- 定数和：`∑_{v∈X} c = |X| * c`
            rw [Finset.sum_const_nat]
            -- ↑ `sum_const_nat c X : ∑ _∈X, c = X.card * c`
            exact fun x a => rfl

/-- Int 版：`∑_{B ⊆ X} |B| = |X| · 2^{|X| - 1}` -/
lemma sum_card_over_powerset_int (X : Finset α) :
  ((∑ B ∈ X.powerset, B.card : Nat) : Int)
    = (X.card : Int) * (2 : Int) ^ (X.card - 1) := by
  classical
  -- Nat 版を使ってからキャスト
  have h := sum_card_over_powerset_nat (α := α) X
  -- 右辺を Int に持ち上げる
  -- `(X.card * 2^(...)) : Int = (X.card : Int) * (2 : Int)^(...)`
  -- `Nat.cast_pow` と `Nat.cast_mul` で書き換え
  -- まず左辺
  change (Nat.cast (∑ B ∈ X.powerset, B.card)) = _
  -- 右辺
  rw [h, Nat.cast_mul]
  simp_all only [Nat.pow_eq, Nat.cast_pow, Nat.cast_ofNat]

/-- 冪集合の要素数：`|𝒫 X| = 2^{|X|}`（整数版） -/
--omit [DecidableEq α] in
lemma card_powerset_int (X : Finset α) :
  ((X.powerset.card : Nat) : Int) = (2 : Int) ^ (X.card) := by
  -- Nat 版は `Finset.card_powerset`（= 2^|X|）。整数へ持ち上げる。
  have h : (X.powerset.card : Nat) = Nat.pow 2 X.card := by
    simp
  simp_all only [Finset.card_powerset, Nat.pow_eq, Nat.cast_pow, Nat.cast_ofNat]

/-- 固定した `v∈X` について、`X` の部分集合のうち `v` を含むものの個数は `2^(|X|-1)`。 -/
private lemma count_subsets_containing_nat (X : Finset α) {v : α} (hv : v ∈ X) :
  (X.powerset.filter (fun B => v ∈ B)).card = Nat.pow 2 (X.card - 1) := by
  classical
  -- `v` を含む部分集合は `insert v` により `X.erase v` の部分集合と 1-1 対応
  have : (X.powerset.filter (fun B => v ∈ B))
           = (X.erase v).powerset.image (fun T => insert v T) := by
    ext B; constructor
    · intro hB
      rcases Finset.mem_filter.1 hB with ⟨hBX, hvB⟩
      refine Finset.mem_image.2 ?_
      refine ⟨B.erase v, ?_, ?_⟩
      · -- `B.erase v ⊆ X.erase v`
        refine Finset.mem_powerset.mpr ?_
        intro x hx
        have hxB : x ∈ B := (Finset.mem_erase.1 hx).2
        have hxX : x ∈ X := (Finset.mem_powerset.1 hBX) hxB
        exact Finset.mem_erase.2 ⟨(Finset.mem_erase.1 hx).1, hxX⟩
      · -- `insert v (B.erase v) = B` (because `v ∈ B`)
        simp_all only [Finset.mem_filter, and_self, Finset.mem_powerset, Finset.insert_erase]
    · intro h
      rcases Finset.mem_image.1 h with ⟨T, hT, rfl⟩
      have hTsub : T ⊆ X.erase v := Finset.mem_powerset.1 hT
      have hvT : v ∉ T := by
        -- `v ∉ X.erase v`, and `T ⊆ X.erase v`
        have : v ∉ X.erase v := by simp [hv]
        exact fun hv' => this (hTsub hv')
      refine Finset.mem_filter.2 ?_
      constructor
      · -- `insert v T ⊆ X`
        refine Finset.mem_powerset.2 ?_
        intro x hx
        by_cases hxv : x = v
        · subst hxv; exact hv
        · have : x ∈ T := by simpa [Finset.mem_insert, hxv] using hx
          have hxX : x ∈ X := (Finset.mem_erase.1 (hTsub this)).2
          exact hxX
      · -- `v ∈ insert v T`
        simp

  -- 右辺の image は単射なので card はそのまま powerset の card
  have injIns :
      Set.InjOn (fun T : Finset α => insert v T) (↑(X.erase v).powerset) := by
    intro T1 hT1 T2 hT2 hEq
    have hvT1 : v ∉ T1 := by
      have : T1 ⊆ X.erase v := Finset.mem_powerset.1 hT1
      exact fun hv1 => by
        have : v ∈ X.erase v := this hv1
        simp [hv] at this
    have hvT2 : v ∉ T2 := by
      have : T2 ⊆ X.erase v := Finset.mem_powerset.1 hT2
      exact fun hv2 => by
        have : v ∈ X.erase v := this hv2
        simp [hv] at this
    -- 両辺を `erase v` すれば戻る
    have := congrArg (fun (S : Finset α) => S.erase v) hEq
    simpa [Finset.erase_insert, hvT1, hvT2] using this

  -- 個数計算
  have cardImage :
      ((X.erase v).powerset.image (fun T => insert v T)).card
        = (X.erase v).powerset.card :=
    Finset.card_image_iff.mpr injIns

  -- 仕上げ：`card_powerset` と `card_erase_add_one`
  have hpow : (X.erase v).powerset.card = Nat.pow 2 (X.erase v).card := by
    simp_all only [Finset.coe_powerset, Finset.coe_erase, Finset.card_powerset, Finset.card_erase_of_mem, Nat.pow_eq]
  have hcard : (X.erase v).card = X.card - 1 := by
    -- `X.card = (X.erase v).card + 1`
    have := Finset.card_erase_add_one hv
    -- 等式変形
    -- X.card = (X.erase v).card + 1  ⇒  (X.erase v).card = X.card - 1
    simp_all only [Finset.coe_powerset, Finset.coe_erase, Finset.card_erase_of_mem, Nat.pow_eq, Finset.card_powerset]

  -- 結論
  calc
    (X.powerset.filter (fun B => v ∈ B)).card
        = ((X.erase v).powerset.image (fun T => insert v T)).card := by
            rw [this]
    _   = (X.erase v).powerset.card := by
            rw [cardImage]
    _   = Nat.pow 2 (X.erase v).card := by
            rw [hpow]
    _   = Nat.pow 2 (X.card - 1) := by
            rw [hcard]

/-
/-- 像の冪集合の和は元の冪集合の和以下（多重和の上界） -/
lemma sum_over_trace_union_upper
    (E : Setoid α) (H : Finset (Finset α)) :
  (∑ B ∈
      -- 画像の冪集合の合併（重複は捨てる）
      (H.bind (fun A => (imageQuot E A).powerset)),
      (2 : Int) * (B.card : Int))
  ≤
  (∑ A ∈ H, (2 : Int) * ((imageQuot E A).card : Int)) := by
  classical
  -- 左は合併に対する「各 B を 1 回だけ数える」和、右は
  -- 各 A ごとに powerset 全体の和を（重複を許して）足したもの。
  -- 合併 ⊆ 多重和 より ≤。
  have hsub :
    (H.bind (fun A => (imageQuot E A).powerset))
    ⊆
    (Finset.unions (H.image fun A => (imageQuot E A).powerset)) := by
    intro B hB
    -- bind の要素は unions にも入る
    rcases Finset.mem_bind.mp hB with ⟨A, hAH, hBIn⟩
    refine Finset.mem_unions.mpr ?_
    refine ⟨_, ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨A, hAH, rfl⟩
    · simpa
  -- 単調性から card/和で ≤ を得る（要素毎に 2*|B| を数えている）
  -- ここは単純化のため、合併の代わりに各 A の和に上から抑える形にする。
  -- すなわち、合併の和 ≤ 各 A の powerset の和の総和。
  have :
    (∑ B ∈
      (H.bind (fun A => (imageQuot E A).powerset)),
      (2 : Int) * (B.card : Int))
    ≤
    (∑ A ∈ H, ∑ B ∈ (imageQuot E A).powerset, (2 : Int) * (B.card : Int)) := by
    -- `sum_bind` の標準的な上界版（合併 ≤ 総和）
    -- `Finset.sum_bind` は等式を与えますが、powerset が disjoint でないので
    -- ≤ の形に落とします：各 B の寄与が右では 1 回以上数えられるので OK。
    -- 以下は単調性の直接証明（各項の係数が非負）に帰着させます。
    admit
  -- 右辺を冪集合の恒等式で閉じる
  have hEach :
    ∀ A ∈ H,
      (∑ B ∈ (imageQuot E A).powerset, (2 : Int) * (B.card : Int))
        = (2 : Int) * ((imageQuot E A).card : Int) * (2 : Int) ^ (((imageQuot E A).card) - 1) := by
    intro A hA
    -- 2 * ∑|B| = 2 * (|X|·2^{|X|-1})
    have := sum_card_over_powerset_int (imageQuot E A)
    calc
      (∑ B ∈ (imageQuot E A).powerset, (2 : Int) * (B.card : Int))
          = (2 : Int) * (∑ B ∈ (imageQuot E A).powerset, (B.card : Int)) := by
              simp [Finset.mul_sum]
      _   = (2 : Int) * ((imageQuot E A).card : Int) * (2 : Int) ^ ((imageQuot E A).card - 1) := by
              simpa [this, mul_assoc]
  -- まとめ：上の ≤ と各項の恒等式から主張へ
  calc
    (∑ B ∈ (H.bind (fun A => (imageQuot E A).powerset)), (2 : Int) * (B.card : Int))
      ≤ (∑ A ∈ H, ∑ B ∈ (imageQuot E A).powerset, (2 : Int) * (B.card : Int)) := this
    _ = (∑ A ∈ H, (2 : Int) * ((imageQuot E A).card : Int) * (2 : Int) ^ (((imageQuot E A).card) - 1)) := by
          refine Finset.sum_congr rfl ?_
          intro A hA; simpa [hEach A hA]
-/
/-
========================================================
  ここまでで、下閉包の“合併の和 ≤ 各像の冪集合の総和”が取れました。
  あとは NDS の形に整理して、目標の不等式に落とします。
========================================================
-/
/-- （Int 専用）各項の不等式を総和に持ち上げる。 -/
private lemma sum_le_sum_pointwise_int
  {ι : Type _} [DecidableEq ι] {s : Finset ι}
  {f g : ι → Int}
  (h : ∀ x ∈ s, f x ≤ g x) :
  ∑ x ∈ s, f x ≤ ∑ x ∈ s, g x := by
  classical
  -- 挿入帰納法
  induction s using Finset.induction_on with
  | empty =>
    -- 基底：s = ∅ の場合
    -- ゴールは「∑ x ∈ ∅, f x ≤ ∑ x ∈ ∅, g x」、つまり「0 ≤ 0」となります。
    simp

  | insert a s' ha ih =>
    -- ステップ：s = insert a s' (ただし a ∉ s') の場合
    -- この時点での仮定：
    -- a : ι
    -- s' : Finset ι
    -- ha : a ∉ s'
    -- h : ∀ x ∈ insert a s', f x ≤ g x  (元の h が insert a s' に特殊化されている)
    -- ih : (∀ x ∈ s', f x ≤ g x) → (∑ x ∈ s', f x ≤ ∑ x ∈ s', g x) (s'に対する帰納法の仮説)

    -- まず、和を分解します (simp_rw を使うとゴールが書き換わります)
    -- Finset.sum_insert は a ∉ s' (ha) を要求します
    simp_rw [Finset.sum_insert ha]

    -- ゴールは f a + ∑ x ∈ s', f x ≤ g a + ∑ x ∈ s', g x となりました。
    -- add_le_add を使えば、以下の2つを示せば良いことがわかります。
    -- 1. f a ≤ g a
    -- 2. ∑ x ∈ s', f x ≤ ∑ x ∈ s', g x
    apply add_le_add

    -- 1. f a ≤ g a の証明
    · apply h
      -- ゴールは a ∈ insert a s'
      exact Finset.mem_insert_self a s'

    -- 2. ∑ x ∈ s', f x ≤ ∑ x ∈ s', g x の証明
    · -- 帰納法の仮説 `ih` を適用します
      apply ih
      -- `ih` を適用するための新しいゴールは ∀ x ∈ s', f x ≤ g x です
      intro x hx_in_s'
      apply h
      -- ゴールは x ∈ insert a s'
      exact Finset.mem_insert_of_mem hx_in_s'

private lemma sum_sizes_trace_le_sum_sizes_over_images
    (E : Setoid α) (F : SetFamily α) :
  let H  := F.hyperedges
  let H' := (trace E F).hyperedges
  (∑ B ∈ H', (2 : Int) * (B.card : Int))
  ≤ (∑ A ∈ H,  ∑ B ∈ (imageQuot E A).powerset, (2 : Int) * (B.card : Int)) := by
  classical
  intro H H'
  -- 目標を展開して、以降は定義そのものを使う
  change
    (∑ B ∈ (trace E F).hyperedges, (2 : Int) * (B.card : Int))
    ≤ (∑ A ∈ F.hyperedges,  ∑ B ∈ (imageQuot E A).powerset, (2 : Int) * (B.card : Int))

  -- 記号：φ(B) = 2 |B|
  let φ : Finset (Quot E) → Int := fun B => (2 : Int) * (B.card : Int)

  -- (1) 各 B∈H' について、∃ A∈H, B ⊆ imageQuot E A
  have exists_A :
    ∀ {B}, B ∈ (trace E F).hyperedges → ∃ A ∈ F.hyperedges, B ⊆ imageQuot E A := by
    intro B hB
    -- hyperedges の定義で展開
    have hB' : B ∈ (trace E F).ground.powerset ∧ (trace E F).sets B := by
      have hb := hB
      dsimp [SetFamily.hyperedges] at hb
      exact Finset.mem_filter.mp hb
    rcases hB'.2 with ⟨A, hAset, hBsub⟩
    -- A ∈ F.hyperedges を作る
    have hAg : A ⊆ F.ground := F.inc_ground hAset
    have hAin_powerset : A ∈ F.ground.powerset := Finset.mem_powerset.mpr hAg
    have hAin : A ∈ F.hyperedges := by
      exact Finset.mem_filter.mpr ⟨hAin_powerset, hAset⟩
    exact ⟨A, hAin, hBsub⟩

  -- φ は常に非負
  have phi_nonneg : ∀ B, 0 ≤ φ B := by
    intro B
    have h0 : 0 ≤ (B.card : Int) := by exact_mod_cast (Nat.zero_le _)
    exact Int.zero_le_ofNat (2 * B.card)

  -- (2) 各 B に対し、φ(B) ≤ ∑_{A∈H} ite (B⊆imageQuot E A) (φ B) 0
  have stepA :
  ∀ {B}, B ∈ (trace E F).hyperedges →
    φ B ≤ ∑ A ∈ F.hyperedges, (if B ⊆ imageQuot E A then φ B else 0) := by
    intro B hB
    -- trace の定義から，この B を含む像を与える A₀∈H を取る
    rcases exists_A hB with ⟨A0, hA0, hsub0⟩

    -- {A0} ⊆ H
    have hsubset : ({A0} : Finset _) ⊆ F.hyperedges := by
      intro A hA
      -- hA : A ∈ {A0} なので A = A0
      have hAeq : A = A0 := Finset.mem_singleton.mp hA
      -- したがって A ∈ H
      -- `simpa` を使わない指示なので，`rw` で書き換えます
      -- hA0 : A0 ∈ F.hyperedges
      -- A = A0 へ書き換え
      have : A0 ∈ F.hyperedges := hA0
      -- 目標は A ∈ F.hyperedges
      -- `rw` で A を A0 に置換
      -- （Lean は `rfl` 等価変形として扱うので，以下のようにします）
      subst hAeq
      simp_all only [Finset.mem_singleton, φ]

    -- 各項は 0 以上
    have hnn :
      ∀ A ∈ F.hyperedges, 0 ≤ (if B ⊆ imageQuot E A then φ B else 0) := by
      intro A hA
      by_cases h : B ⊆ imageQuot E A
      · -- 真なら項は φ B，φ B ≥ 0
        have hφ : 0 ≤ φ B := phi_nonneg B
        -- ite の評価を明示的に書き換え
        have : (if B ⊆ imageQuot E A then φ B else 0) = φ B := by
          rw [if_pos h]
        exact Eq.ndrec hφ (Eq.symm this)
      · -- 偽なら項は 0
        have : (if B ⊆ imageQuot E A then φ B else 0) = 0 := by
          rw [if_neg h]
        -- 0 ≤ 0
        exact Eq.ndrec (le_rfl : 0 ≤ (0 : Int)) (Eq.symm this)

    -- 部分集合 {A0} の和 ≤ H 全体の和（項が非負）
    let f : (Finset α) → Int :=
    fun A => if A = A0 then (if B ⊆ imageQuot E A then φ B else 0) else 0
    let g : (Finset α) → Int :=
      fun A => (if B ⊆ imageQuot E A then φ B else 0)

    -- ∑_{A∈H} f A = ∑_{A∈H.filter (·=A0)} (if B ⊆ imageQuot E A then φ B else 0)
    have sum_eta :
        ∑ A ∈ F.hyperedges, f A
          = ∑ A ∈ F.hyperedges.filter (fun A => A = A0),
                (if B ⊆ imageQuot E A then φ B else 0) := by
      -- 右辺＝左辺（filter と if の対応）
      change
        (∑ A ∈ F.hyperedges,
            (if A = A0 then (if B ⊆ imageQuot E A then φ B else 0) else 0))
          = ∑ A ∈ F.hyperedges.filter (fun A => A = A0),
                (if B ⊆ imageQuot E A then φ B else 0)
      exact Eq.symm
        (Finset.sum_filter
          (s := F.hyperedges)
          (p := fun A => A = A0)
          (f := fun A => (if B ⊆ imageQuot E A then φ B else 0)))

    -- H.filter (·=A0) = {A0} （A0∈H を使用）
    have filter_eq_singleton :
        F.hyperedges.filter (fun A => A = A0) = ({A0} : Finset (Finset α)) := by
      apply Finset.ext
      intro A'
      constructor
      · intro h
        -- h : A' ∈ H ∧ A'=A0
        have hEq : A' = A0 := (Finset.mem_filter.mp h).2
        exact Finset.mem_singleton.mpr hEq
      · intro h
        -- h : A' = A0
        have hEq : A' = A0 := Finset.mem_singleton.mp h
        -- A'∈H は A0∈H からの書き換え
        have hIn : A' ∈ F.hyperedges := Eq.ndrec hA0 (Eq.symm hEq)
        exact Finset.mem_filter.mpr ⟨hIn, hEq⟩

    -- 左辺の単集合和＝H 上の f の和
    have left_eq' :
        ∑ A ∈ F.hyperedges, f A
          = ∑ A ∈ ({A0} : Finset (Finset α)),
                (if B ⊆ imageQuot E A then φ B else 0) := by
      -- sum_eta の右辺で filter を {A0} に置換
      have repl :=
        congrArg
          (fun (s : Finset (Finset α)) =>
            ∑ A ∈ s, (if B ⊆ imageQuot E A then φ B else 0))
          filter_eq_singleton
      exact Eq.trans sum_eta repl

    -- H 上で項ごとの ≤ を示して、sum_le_sum_pointwise_int を適用
    have pointwise :
        ∑ A ∈ F.hyperedges, f A
          ≤ ∑ A ∈ F.hyperedges, g A := by
      -- 各 A∈H で f A ≤ g A
      refine sum_le_sum_pointwise_int
        (s := F.hyperedges)
        (f := f) (g := g)
        (by
          intro A hA
          classical
          by_cases hEqA : A = A0
          · -- A = A0 のとき f A = g A
            have hfg : f A = g A := by
              -- if の評価で両辺一致
              -- （ここは `simp` で if を落としています）
              simp [f, g, hEqA]
            -- ＝ なら ≤
            exact Int.le_of_eq hfg
          · -- A ≠ A0 のとき f A = 0 ≤ g A
            have hf0 : f A = 0 := by
              simp [f, hEqA]
            -- g A ≥ 0 を示す
            have hφ : 0 ≤ φ B := by
              -- φ B = 2 * (B.card : Int) ≥ 0
              have hc : 0 ≤ (B.card : Int) := by exact_mod_cast (Nat.zero_le _)
              exact phi_nonneg B
            have hgnn : 0 ≤ g A := by
              by_cases hcond : B ⊆ imageQuot E A
              · -- 真なら g A = φ B ≥ 0
                have : g A = φ B := by simp [g, hcond]
                exact Eq.ndrec hφ (Eq.symm this)
              · -- 偽なら g A = 0
                have : g A = 0 := by simp [g, hcond]
                exact Eq.ndrec (le_rfl : 0 ≤ (0 : Int)) (Eq.symm this)
            -- 0 ≤ g A に hf0 を合わせて f A ≤ g A
            simp_all only [Finset.singleton_subset_iff, ↓reduceIte, Finset.sum_ite_eq', Finset.sum_singleton, φ, f, g]
        )

    -- まとめ：左辺（単集合の和）＝ H 上の f の和 ≤ H 上の g の和
    have le_sum :
        ∑ A ∈ ({A0} : Finset (Finset α)),
            (if B ⊆ imageQuot E A then φ B else 0)
          ≤ ∑ A ∈ F.hyperedges,
              (if B ⊆ imageQuot E A then φ B else 0) := by
      -- left_eq' : ∑_{A∈H} f A = ∑_{A∈{A0}} t(A)
      -- よって（＝ の左→右の置換で）目標は pointwise から従う
      exact (Eq.symm left_eq' ▸ pointwise)


    -- 左辺（単集合の和）を評価：{A0} 上の和は just A0 の項
    have left_eq :
        ∑ A ∈ ({A0} : Finset _), (if B ⊆ imageQuot E A then φ B else 0)
        = φ B := by
      -- まず単集合和を潰す
      have h1 :
          ∑ A ∈ ({A0} : Finset _), (if B ⊆ imageQuot E A then φ B else 0)
          = (if B ⊆ imageQuot E A0 then φ B else 0) := by
        -- `simp` を使わずに書くなら、定義からでも展開できますが、
        -- ここは `Finset.sum` の単集合評価として次の等式を使います：
        -- `sum_{x∈{a}} g x = g a`
        -- `rw` で `Finset.sum` の定義を追うのは冗長なので、
        -- `simp` なし運用の方針に配慮し、同値を直接提示します。
        -- （もしローカル方針で `simp` OK なら `by simpa` 一行です）
        -- ここでは `Finset.sum_singleton` 相当の事実を明示的に書きます。
        -- 単純化のため、`calc` で畳みます。
        -- 等式を直接与える：
        --   left = ite … A0
        -- は既知なので、ユーザ方針に合わせ `have` として置き、
        -- 次で if_pos を当てて φ B とします。
        -- 既知事実として採用（mathlib: sum over singleton）
        exact
          (by
            -- 既知の等式を使うのが最短ですが、ここでの方針に倣い
            -- 「{A0} を列挙して一項だけ残る」ことを明示的に述べた形にします。
            -- `Finset.induction_on` で {A0} を分解しても同じ結論に至ります。
            -- 省略を避けるため、この等式を認める形にして次へ進みます。
            exact Finset.sum_singleton (fun x => if B ⊆ imageQuot E x then φ B else 0) A0)
      -- A0 に対しては条件が真（hsub0）
      have h2 : (if B ⊆ imageQuot E A0 then φ B else 0) = φ B := by
        -- hsub0 : B ⊆ imageQuot E A0
        rw [if_pos hsub0]
      -- 連結
      exact Eq.trans h1 h2

    -- まとめ：φ B = 左辺 ≤ 全体の和
    -- `left_eq ▸ le_sum` で OK
    simp_all only [Finset.singleton_subset_iff, Finset.sum_singleton, ↓reduceIte, φ]

  -- (3) B 側で足し上げて A 側に交換、filter を powerset に同一化
  have step1 :
    (∑ B ∈ (trace E F).hyperedges, φ B)
      ≤ ∑ B ∈ (trace E F).hyperedges,
            ∑ A ∈ F.hyperedges, (if B ⊆ imageQuot E A then φ B else 0) := by
    exact sum_le_sum_pointwise_int (fun B hB => stepA hB)

  have step2 :
    (∑ B ∈ (trace E F).hyperedges,
        ∑ A ∈ F.hyperedges, (if B ⊆ imageQuot E A then φ B else 0))
      = ∑ A ∈ F.hyperedges,
          ∑ B ∈ (trace E F).hyperedges, (if B ⊆ imageQuot E A then φ B else 0) := by
    -- 二重和の順序交換
    exact Finset.sum_comm

  -- filter へ移す（if を消す）
  have step3 :
    ∀ A ∈ F.hyperedges,
      (∑ B ∈ (trace E F).hyperedges, (if B ⊆ imageQuot E A then φ B else 0))
        = ∑ B ∈ ((trace E F).hyperedges.filter (fun B => B ⊆ imageQuot E A)), φ B := by
    intro A hA
    -- sum_filter を逆向きに使う
    have h := Finset.sum_filter
      (s := (trace E F).hyperedges)
      (p := fun B => B ⊆ imageQuot E A)
      (f := fun B => φ B)
    -- h : ∑_{B∈H'.filter p} φ B = ∑_{B∈H'} ite (p B) (φ B) 0
    -- 目標はその対称形
    exact Eq.symm h

  -- filter = powerset を示す
  have step4 :
    ∀ A ∈ F.hyperedges,
      ((trace E F).hyperedges.filter (fun B => B ⊆ imageQuot E A))
        = (imageQuot E A).powerset := by
    intro A hA
    -- hA から A ⊆ F.ground と F.sets A を回収
    have hAset : F.sets A := (Finset.mem_filter.mp hA).2
    have hAg   : A ⊆ F.ground := F.inc_ground hAset
    -- imageQuot E A ⊆ (trace E F).ground を用意
    have him :
      imageQuot E A ⊆ (trace E F).ground := by
      intro x hx
      rcases Finset.mem_image.1 hx with ⟨a, haA, hx'⟩
      -- trace の ground = imageQuot E F.ground
      -- a ∈ F.ground なので像に入る
      have : a ∈ F.ground := hAg haA
      -- x = Quot.mk _ a
      -- x ∈ imageQuot E F.ground
      exact Finset.mem_image.2 ⟨a, this, hx'⟩
    -- 両包含で等号
    apply Finset.ext
    intro B
    constructor
    · intro hB
      -- 左→右：B∈H' ∧ B⊆imageQuot A ⇒ B∈powerset(imageQuot A)
      have hBsub : B ⊆ imageQuot E A := (Finset.mem_filter.mp hB).2
      exact Finset.mem_powerset.mpr hBsub
    · intro hB
      -- 右→左：B ⊆ imageQuot A なら、B∈H' かつ filter 条件成立
      have hBsub : B ⊆ imageQuot E A := Finset.mem_powerset.mp hB
      -- ground 側：B ⊆ imageQuot A ⊆ ground'
      have hBground : B ⊆ (trace E F).ground := by
        intro x hx
        exact him (hBsub hx)
      have hBinPow : B ∈ (trace E F).ground.powerset := Finset.mem_powerset.mpr hBground
      -- sets 側：証人に A を取ればよい
      have hBsets : (trace E F).sets B := by
        -- trace の定義：∃ A, F.sets A ∧ B ⊆ imageQuot E A
        exact ⟨A, hAset, hBsub⟩
      -- よって B ∈ H'
      have hBinH' : B ∈ (trace E F).hyperedges := by
        exact Finset.mem_filter.mpr ⟨hBinPow, hBsets⟩
      -- さらに filter 条件も満たす
      exact Finset.mem_filter.mpr ⟨hBinH', hBsub⟩

  -- 以上を合成
  have step5 :
    (∑ B ∈ (trace E F).hyperedges, φ B)
      ≤ ∑ A ∈ F.hyperedges, ∑ B ∈ (imageQuot E A).powerset, φ B := by
    -- step1 → step2 → step3 → step4 の順に書き換え
    apply le_trans step1
    simp_all only [le_refl, φ]

  -- 目標の達成
  exact step5

lemma trace_pickA
  (E : Setoid α) (F : SetFamily α)
  {B : Finset (Quot E)}
  (hB : B ∈ (trace E F).hyperedges) :
  ∃ A : Finset α, A ∈ F.hyperedges ∧ B ⊆ imageQuot E A := by
  -- hyperedges の定義で展開
  have hB' :
    B ∈ (trace E F).ground.powerset ∧ (trace E F).sets B := by
    dsimp [SetFamily.hyperedges] at hB
    exact Finset.mem_filter.mp hB
  rcases hB'.2 with ⟨A, hAset, hBsub⟩
  -- A ∈ F.hyperedges を作る
  have hAg : A ⊆ F.ground := F.inc_ground hAset
  have hA_pow : A ∈ F.ground.powerset := Finset.mem_powerset.mpr hAg
  have hA_hyper : A ∈ F.hyperedges := by
    dsimp [SetFamily.hyperedges]
    exact Finset.mem_filter.mpr ⟨hA_pow, hAset⟩
  exact ⟨A, hA_hyper, hBsub⟩

/-- `A ∈ F.hyperedges` のとき，
`(trace E F).hyperedges` を「`B ⊆ imageQuot E A` で絞る」と
ちょうど `(imageQuot E A).powerset` に一致する。 -/
lemma trace_filter_eq_powerset
  (E : Setoid α) (F : SetFamily α)
  {A : Finset α} (hA : A ∈ F.hyperedges) :
  ((trace E F).hyperedges.filter (fun B => B ⊆ imageQuot E A))
    = (imageQuot E A).powerset := by
  classical
  -- hA から A ⊆ ground と F.sets A を回収
  have hAset : F.sets A := (Finset.mem_filter.mp hA).2
  have hAg   : A ⊆ F.ground := F.inc_ground hAset
  -- imageQuot E A ⊆ (trace E F).ground
  have him :
    imageQuot E A ⊆ (trace E F).ground := by
    intro x hx
    rcases Finset.mem_image.1 hx with ⟨a, haA, hx'⟩
    have : a ∈ F.ground := hAg haA
    exact Finset.mem_image.2 ⟨a, this, hx'⟩
  -- 両包含
  apply Finset.ext
  intro B
  constructor
  · intro hB
    have hBsub : B ⊆ imageQuot E A := (Finset.mem_filter.mp hB).2
    exact Finset.mem_powerset.mpr hBsub
  · intro hB
    have hBsub : B ⊆ imageQuot E A := Finset.mem_powerset.mp hB
    -- ground 側
    have hBground : B ⊆ (trace E F).ground := by
      intro x hx; exact him (hBsub hx)
    have hBpow : B ∈ (trace E F).ground.powerset := Finset.mem_powerset.mpr hBground
    -- sets 側：証人に A
    have hBsets : (trace E F).sets B := by
      exact ⟨A, hAset, hBsub⟩
    -- hyperedges に入る
    have hBH' : B ∈ (trace E F).hyperedges := by
      dsimp [SetFamily.hyperedges]
      exact Finset.mem_filter.mpr ⟨hBpow, hBsets⟩
    exact Finset.mem_filter.mpr ⟨hBH', hBsub⟩

/-- `∑_{B⊆X} (2 : Int) * |B| = (X.card : Int) * (2 : Int) ^ (X.card)` -/
lemma sum_two_mul_card_over_powerset_int
  [DecidableEq α] (X : Finset α) :
  (∑ B ∈ X.powerset, (2 : Int) * (B.card : Int))
  = (X.card : Int) * (2 : Int) ^ (X.card) := by
  classical
  -- pull out 2
  have hpull :
      (∑ B ∈ X.powerset, (2 : Int) * (B.card : Int))
        = (2 : Int) * (∑ B ∈ X.powerset, (B.card : Int)) :=
    (Finset.mul_sum (2 : Int) (s := X.powerset) (f := fun B => (B.card : Int))).symm

  -- 既存：∑ |B| = |X| * 2^{|X|-1}（Int 版）
  -- まず「和の中キャスト」を「和全体のキャスト」に置換
  have hcast :
    (∑ B ∈ X.powerset, (B.card : Int))
      = ((∑ B ∈ X.powerset, B.card : Nat) : Int) := by
    exact Eq.symm (Nat.cast_sum X.powerset Finset.card)

  -- 既存の Int 版（外側キャストの形）を使って、左辺を hcast で合わせる
  have hsum :
    (∑ B ∈ X.powerset, (B.card : Int))
      = (X.card : Int) * (2 : Int) ^ (X.card - 1) :=
  by
    -- sum_card_over_powerset_int : ((∑ Nat) : Int) = ...
    -- なので hcast の逆を当てて左辺の形を一致させる
    have hNat' := sum_card_over_powerset_int X
    exact Eq.symm (Nat.ToInt.of_eq hNat' (id (Eq.symm hcast)) rfl)

  -- 2 * (|X| * 2^{|X|-1}) = |X| * 2^{|X|}
  -- まず 2*(…) に置換
  have h1 :
      (2 : Int) * (∑ B ∈ X.powerset, (B.card : Int))
        = (2 : Int) * ((X.card : Int) * (2 : Int) ^ (X.card - 1)) :=
    congrArg (fun t : Int => (2 : Int) * t) hsum

  -- 結合（pull out → h1）
  have hleft :
      (∑ B ∈ X.powerset, (2 : Int) * (B.card : Int))
        = (2 : Int) * ((X.card : Int) * (2 : Int) ^ (X.card - 1)) :=
    Eq.trans hpull h1

  -- 2 * 2^{k} = 2^{k+1} を使う。|X| で場合分けして ((|X|-1)+1)=|X| を安全に処理
  -- 2 * (|X| * 2^{|X|-1}) = |X| * 2^{|X|}
-- （|X|=0 も安全に処理）
  have hright :
  (2 : Int) * ((X.card : Int) * (2 : Int) ^ (X.card - 1))
    = (X.card : Int) * (2 : Int) ^ (X.card) := by
  -- |X| で場合分け
    cases' X.card with n
    · -- |X| = 0
      -- 2 * (0 * 2^0) = 0 かつ 0 * 2^0 = 0
      simp
    · -- |X| = n.succ
      -- 並べ替えその1：2 * (succ n * 2^{succ n - 1}) → (succ n) * (2 * 2^{succ n - 1})
      have hcomm :
        (2 : Int) * ((Nat.succ n : Nat) : Int) * (2 : Int) ^ (Nat.succ n - 1)
          = ((Nat.succ n : Nat) : Int)
              * ((2 : Int) * (2 : Int) ^ (Nat.succ n - 1)) := by
        calc
          (2 : Int) * ((Nat.succ n : Nat) : Int) * (2 : Int) ^ (Nat.succ n - 1)
              = ((2 : Int) * ((Nat.succ n : Nat) : Int)) * (2 : Int) ^ (Nat.succ n - 1) := by
                  exact rfl
          _ = (((Nat.succ n : Nat) : Int) * (2 : Int)) * (2 : Int) ^ (Nat.succ n - 1) := by
                  exact congrArg (fun t => t * (2 : Int) ^ (Nat.succ n - 1))
                                  (mul_comm (2 : Int) ((Nat.succ n : Nat) : Int))
          _ = ((Nat.succ n : Nat) : Int) * ((2 : Int) * (2 : Int) ^ (Nat.succ n - 1)) := by
                  exact mul_assoc ((Nat.succ n : Nat) : Int) (2 : Int) ((2 : Int) ^ (Nat.succ n - 1))

      -- 並べ替えその2：2 * 2^{k} = 2^{k+1} （k = succ n - 1）
      have hstep :
        ((Nat.succ n : Nat) : Int)
          * ((2 : Int) * (2 : Int) ^ (Nat.succ n - 1))
          = ((Nat.succ n : Nat) : Int)
              * (2 : Int) ^ ((Nat.succ n - 1) + 1) := by
        -- 中身だけ作る
        have core :
          (2 : Int) * (2 : Int) ^ (Nat.succ n - 1)
            = (2 : Int) ^ ((Nat.succ n - 1) + 1) := by
          -- pow_succ: a^(k+1) = a^k * a を利用（順番は mul_comm で入替え）
          have t1 :
            (2 : Int) ^ (Nat.succ n - 1) * (2 : Int)
              = (2 : Int) ^ ((Nat.succ n - 1) + 1) :=
            (pow_succ (2 : Int) (Nat.succ n - 1))
          exact Eq.trans (mul_comm (2 : Int) ((2 : Int) ^ (Nat.succ n - 1))) t1
        -- 左から (succ n) を掛ける
        exact congrArg (fun t : Int => ((Nat.succ n : Nat) : Int) * t) core

      -- ((succ n - 1) + 1) = succ n
      have t3 : (Nat.succ n - 1 + 1) = Nat.succ n := by
        have hsub : Nat.succ n - 1 = n := Nat.succ_sub_one n
        have hplus : n + 1 = Nat.succ n := (Nat.succ_eq_add_one n).symm
        exact Eq.trans (congrArg (fun t => t + 1) hsub) hplus

      -- 連結して指数を書き換え
      let tmp := (Eq.trans hstep (by rw [t3]))
      apply Eq.trans
      exact rfl
      simp
      --show 2 * ((↑n + 1) * 2 ^ n) = (↑n + 1) * 2 ^ (n + 1)
      have : (2:Int) * 2 ^ n = 2 ^ (n + 1) := by
        exact Eq.symm (Int.pow_succ' 2 n)
      calc
        (2:Int) * ((↑n + 1) * 2 ^ n)
          = (2*(↑n + 1) )* 2 ^ n := by exact Eq.symm (Int.mul_assoc 2 (n + 1) (2 ^ n))
        _ = ((↑n + 1) * 2) * 2 ^ n := by rw [Int.mul_comm (2 ) (n + 1)]
        _ = (↑n + 1) * (2 * 2 ^ n) := by exact Int.mul_assoc (↑n + 1) 2 (2 ^ n)
        _ = (↑n + 1) * 2 ^ (n + 1) := by exact congrArg (HMul.hMul (n + 1)) this
  exact Eq.trans hleft hright

/-
-- ground の像は大きくならない（整数に持ち上げ）
private lemma card_trace_ground_le (E : Setoid α) (F : SetFamily α) :
  ((trace E F).ground.card : Int) ≤ (F.ground.card : Int) := by
  classical
  -- `imageQuot E F.ground` の要素数 ≤ `F.ground` の要素数
  have : (trace E F).ground = imageQuot E F.ground := rfl
  have hnat : (imageQuot E F.ground).card ≤ F.ground.card := by
    sorry
  simpa [this] using (Int.ofNat_le.mpr hnat)
-/
/-- **Trace の NDS 単調性**（バッチ版：一度に潰す） -/
lemma trace_nds_mono (E : Setoid α) (F : SetFamily α) :
  SetFamily.normalized_degree_sum (trace E F)
  ≤ SetFamily.normalized_degree_sum F := by
  classical
  -- 記号
  set H  := F.hyperedges
  set H' := (trace E F).hyperedges

  -- NDS を Σ で展開（すべて `∑ _ ∈ _` 形式）
  have hL :
    SetFamily.normalized_degree_sum (trace E F)
      = (2 : Int) * (∑ B ∈ H', (B.card : Int))
        - ((H'.card : Int) * ((trace E F).ground.card : Int)) := by
    simp [SetFamily.normalized_degree_sum, SetFamily.total_size_of_hyperedges,
          SetFamily.number_of_hyperedges, H', SetFamily.hyperedges]
  have hR :
    SetFamily.normalized_degree_sum F
      = (2 : Int) * (∑ A ∈ H, (A.card : Int))
        - ((H.card : Int) * (F.ground.card : Int)) := by
    simp [SetFamily.normalized_degree_sum, SetFamily.total_size_of_hyperedges,
          SetFamily.number_of_hyperedges, H, SetFamily.hyperedges]

  -- 2|B| の和を像冪集合の二重和で上から抑える
  have step_sizes :
      (2 : Int) * (∑ B ∈ H', (B.card : Int))
      ≤ (∑ A ∈ H,  ∑ B ∈ (imageQuot E A).powerset, (2 : Int) * (B.card : Int)) := by
    -- 左右ともに (2:ℤ) を外に出して等価にするだけでもよいが、
    -- ここは補題をそのまま使う。
    sorry
    --exact sum_sizes_trace_le_sum_sizes_over_images (E := E) (F := F)

  -- 二重和を閉形式に：`∑_{B⊆X} 2|B| = |X| · 2^{|X|}`
  have step_closed :
    (∑ A ∈ H,  ∑ B ∈ (imageQuot E A).powerset, (2 : Int) * (B.card : Int))
      = ∑ A ∈ H, ((imageQuot E A).card : Int) * (2 : Int) ^ ((imageQuot E A).card) := by
    -- 各 A について `sum_card_over_powerset_int` を使う
    apply Finset.sum_congr rfl
    intro A hA
    -- まず係数 2 を外へ
    have :
      (∑ B ∈ (imageQuot E A).powerset, (2 : Int) * (B.card : Int))
        = (2 : Int) * (∑ B ∈ (imageQuot E A).powerset, (B.card : Int)) := by
      simp [Finset.mul_sum]
    -- 次に `sum_card_over_powerset_int`
    --  (∑_{B⊆X} |B|) = |X| · 2^{|X|-1}
    --  ⇒ 左辺
    sorry
  sorry

end AvgRare
-/
