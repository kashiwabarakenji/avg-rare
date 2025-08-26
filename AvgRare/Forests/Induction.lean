import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Logic.Relation
import AvgRare.Basics.SetFamily
import AvgRare.SPO.FuncSetup
import AvgRare.SPO.Forest

universe u


namespace AvgRare
namespace Forests.Induction
open Classical
variable {α : Type u} [DecidableEq α]
open AvgRare
open SPO
open FuncSetup
open PaperSync


private lemma iterate_has_collision
  {β : Type _} [Fintype β] (f : β → β) (x : β) :
  ∃ i j : Fin (Fintype.card β + 1), i ≠ j ∧
    Nat.iterate f i.1 x = Nat.iterate f j.1 x := by
  classical
  -- 鳩ノ巣：Fin (|β|+1) → β は単射になれない
  have hnotinj :
    ¬ Function.Injective (fun i : Fin (Fintype.card β + 1) => Nat.iterate f i.1 x) := by
    intro hinj
    -- 単射なら |Fin (n)| ≤ |β|、つまり n ≤ |β|。ここで n = |β|+1 なので矛盾。
    have hcard := Fintype.card_le_of_injective _ hinj
    -- card_fin
    have : Fintype.card (Fin (Fintype.card β + 1)) ≤ Fintype.card β := hcard
    -- つまり |β|+1 ≤ |β| は偽
    have : Fintype.card β + 1 ≤ Fintype.card β := by
      simp_all only [Fintype.card_fin, add_le_iff_nonpos_right, nonpos_iff_eq_zero, one_ne_zero]
    exact (Nat.not_succ_le_self (Fintype.card β)) this
  -- 非単射の具体化
  -- ¬Injective ↔ ∃ i≠j, f i = f j
  -- 順序は（= と ≠）の並びが逆の版もありますが、ここでは組を作って返すだけでOK
  classical
  -- 展開
  have : ∃ i j, i ≠ j ∧
      (fun k : Fin (Fintype.card β + 1) => Nat.iterate f k.1 x) i =
      (fun k : Fin (Fintype.card β + 1) => Nat.iterate f k.1 x) j := by
    -- 直接 `by_contra` 展開してもOKですが、ここは classical choice に任せます
    -- 短く：Classical.not_forall.mp で取り出し
    -- ここでは補題として受け入れてもらって構いません

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

/-- 反復に周期が出たら、反対称性により長さ 1 のサイクル（不動点）になる。 -/
private lemma eventually_hits_fixpoint
  (S : SPO.FuncSetup α) [Fintype S.Elem] (hpos : isPoset S)
  (x : S.Elem) :
  ∃ m : S.Elem, S.le x m ∧ S.cover m m := by
  classical
  -- 鳩ノ巣で反復の衝突
  obtain ⟨i, j, hneq, heq⟩ :=
    iterate_has_collision (β := S.Elem) (f := S.f) x
  -- 便宜上 i<j 側に並べ替え
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
      -- 周期：iterate f t y = y
      have cyc : Nat.iterate S.f t y = y := by
        -- `Nat.iterate_add` を使って i と (j-i) をつなぐ
        have hj : i.1 + t = j.1 := Nat.add_sub_of_le (Nat.le_of_lt hlt)
        -- 計算列
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
      -- t>0 なら、y→f y と f y→y が両立して反対称性に矛盾、よって f y = y
      -- 具体的には：iterate (t-1) (f y) = y を作って `reflTransGen_iff_exists_iterate` で ≤ を作る
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
        apply (AvgRare.SPO.le_iff_exists_iter S x y).mpr
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

      -- 1歩で y ≤ f y
      have y_le_fy : S.le y (S.f y) :=
        Relation.ReflTransGen.tail
          (Relation.ReflTransGen.refl) rfl
      -- (t-1) 歩で f y ≤ y
      have : S.cover x (S.f x) := by
        exact rfl
      have fy_le_y : S.le (S.f y) y:= by
        -- 反復↔到達の補題を使う
        -- reflTransGen_iff_exists_iterate: stepRel f x y ↔ ∃k, iterate f k x = y
        apply (AvgRare.SPO.le_iff_exists_iter S (S.f y) y).mpr
        use (t - 1)
        exact back

      have : S.f y = y := by
        exact antisymm_of_isPoset S hpos fy_le_y y_le_fy

      use y
      dsimp [cover]
      constructor
      · exact xyle
      · exact this

  | inr hgt =>
      -- 対称に i/j を入れ替えて同様に処理（同じコード）

      let t := i.1 - j.1
      have htpos : 0 < t := Nat.sub_pos_of_lt hgt
      let y := Nat.iterate S.f j.1 x
      -- 周期：iterate f t y = y
      have cyc : Nat.iterate S.f t y = y := by
        -- `Nat.iterate_add` を使って i と (j-i) をつなぐ
        have hj : j.1 + t = i.1 := Nat.add_sub_of_le (Nat.le_of_lt hgt)
        -- 計算列
        calc
          Nat.iterate S.f t y
              = Nat.iterate S.f (j.1 + t) x := by
                  simp [y]
                  rw [← @Function.iterate_add_apply]
                  --simp_all only [ne_eq, Fin.val_fin_lt, tsub_pos_iff_lt, t]
                  ext : 1
                  have : t + ↑j = ↑j + t := by exact Nat.add_comm t ↑j
                  rw [this]

          _   = Nat.iterate S.f i.1 x := by
                  -- j = i + t
                  simp [hj]
          _   = Nat.iterate S.f i.1 x := by exact rfl
          _   = y := by exact heq
      -- t>0 なら、y→f y と f y→y が両立して反対称性に矛盾、よって f y = y
      -- 具体的には：iterate (t-1) (f y) = y を作って `reflTransGen_iff_exists_iterate` で ≤ を作る
      have ht1 : Nat.succ (t - 1) = t := Nat.succ_pred_eq_of_pos htpos
      have gt1: t >= 1:= by exact htpos
      have fxy :S.f^[t + ↑j] x = y := by
        simp_all only [ne_eq, Fin.val_fin_lt, tsub_pos_iff_lt, Nat.succ_eq_add_one, ge_iff_le, Nat.sub_add_cancel, t, y]
        rw [Function.iterate_add_apply]
        simp_all only

      have xyle : S.le x y := by
        apply (AvgRare.SPO.le_iff_exists_iter S x y).mpr
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

      -- 1歩で y ≤ f y
      have y_le_fy : S.le y (S.f y) :=
        Relation.ReflTransGen.tail
          (Relation.ReflTransGen.refl) rfl
      -- (t-1) 歩で f y ≤ y
      have : S.cover x (S.f x) := by
        exact rfl
      have fy_le_y : S.le (S.f y) y:= by
        -- 反復↔到達の補題を使う
        -- reflTransGen_iff_exists_iterate: stepRel f x y ↔ ∃k, iterate f k x = y
        apply (AvgRare.SPO.le_iff_exists_iter S (S.f y) y).mpr
        use (t - 1)
        exact back

      have : S.f y = y := by
        exact antisymm_of_isPoset S hpos fy_le_y y_le_fy

      use y
      dsimp [cover]
      constructor
      · exact xyle
      · exact this

lemma exists_maximal_of_finite
  (S : SPO.FuncSetup α) [Fintype S.Elem] (hpos : isPoset S)
  (hne : S.ground.Nonempty) :
  ∃ m : S.Elem, S.maximal m := by
  classical
  -- 任意の x から出発して不動点に到達
  obtain ⟨x, hx⟩ := hne
  let x0 : S.Elem := ⟨x, by exact hx⟩
  obtain ⟨m, x_le_m, hmfix⟩ := eventually_hits_fixpoint S hpos x0
  exact ⟨m, maximal_of_fixpoint S hmfix⟩

/-- 連結な functional 半順序では極大元はちょうど 1 つ存在。 -/
theorem exists_unique_maximal_of_connected
  (S : SPO.FuncSetup α) [Fintype S.Elem]
  (hpos : isPoset S) (hconn : isConnected S)
  (hne : S.ground.Nonempty) :
  ∃! m : S.Elem, S.maximal m := by
  -- 存在
  obtain ⟨m, hm⟩ := exists_maximal_of_finite S hpos hne
  -- 一意性：既証明の unique_maximal_of_connected
  refine ⟨m, hm, ?uniq⟩
  intro m' hm'
  -- 連結性の下で極大は高々1つ
  have : m = m' :=
    unique_maximal_of_connected (S := S) (hpos := hpos) (hconn := hconn) (hu := hm) (hv := hm')
  exact this.symm ▸ rfl

-----ここから極大要素のtraceに関すること。

noncomputable def posetTraceCore (S : SPO.FuncSetup α) (m : S.Elem) : SPO.FuncSetup α :=
{ ground := S.ground.erase m.1
, f := by
    -- 与えられた x∈ground\{m} に対し、
    -- もし `S.f x = m` なら x 自身へ（新しい根にする）、
    -- そうでなければ `S.f x` をそのまま使う（ただし m でないことの証明を付す）
    refine fun x => by
      classical
      let x₀ : S.Elem := ⟨x.1, (Finset.mem_erase.mp x.2).2⟩
      by_cases hx : S.f x₀ = m
      · exact ⟨x.1, by
          -- x∈ground\{m} の証明
          simp_all only [Finset.coe_mem, x₀]⟩
      · exact ⟨(S.f x₀).1, by
          -- f x ≠ m を使って f x∈ground\{m} を示す
          simp_all only [Finset.mem_erase, ne_eq, Finset.coe_mem, and_true, x₀]
          apply Aesop.BuiltinRules.not_intro
          intro a
          apply hx
          simp_all only
          exact hx (Subtype.ext a)
        ⟩
}

/- （定義から）`posetTraceCore` の台集合は `erase m`。 -/
@[simp] lemma posetTraceCore_ground
  (S : SPO.FuncSetup α) (m : S.Elem) :
  (posetTraceCore S m).ground = S.ground.erase m.1 :=
rfl

/-!
`posetTraceCore` の本体は、与えられた `x ∈ ground \ {m}` に対して
`S.f x = m` なら `x` 自身へ、そうでなければ `S.f x` をそのまま使う、という定義でした。
以下では、この定義から即物的に出る「カバーの保存」に関する基本補題を2つ埋めます。
-/

/-! ### 2) 目標に向けた“局所”補題（m を指していない矢だけ保存） -/

/-- `S.cover x y` かつ `y ≠ m` なら、`posetTraceCore` でも同じ矢が残る。 -/
lemma cover_preserved_if_target_ne_m
  (S : SPO.FuncSetup α) (m : S.Elem)
  {x y : α}
  (hx : x ∈ S.ground.erase m.1) (hy : y ∈ S.ground.erase m.1)
  (hxy : S.cover ⟨x, (Finset.mem_erase.mp hx).2⟩ ⟨y, (Finset.mem_erase.mp hy).2⟩) :
  (posetTraceCore S m).cover ⟨x, hx⟩ ⟨y, hy⟩ := by
  -- 展開の用意
  let xS : S.Elem := ⟨x, (Finset.mem_erase.mp hx).2⟩
  let yS : S.Elem := ⟨y, (Finset.mem_erase.mp hy).2⟩
  -- `y ≠ m`（値の成分）を取り出す
  have hy_ne : y ≠ m.1 := (Finset.mem_erase.mp hy).1
  -- `S.cover x y` は `S.f x = y`
  have hfy : S.f xS = yS := hxy
  -- したがって `S.f x ≠ m`（値を見ると `y ≠ m` なので）
  have hfx_ne_m : S.f xS ≠ m := by
    intro hbad
    -- 値成分を見ると矛盾
    have : (S.f xS).1 = m.1 := congrArg Subtype.val hbad
    have : y = m.1 := by
      simp_all [xS, yS]
    exact hy_ne this
  -- `posetTraceCore` の定義で `S.f x ≠ m` の枝に入るので、
  -- ちょうど `S.f x` をそのまま返す。よって等号で示せる。
  -- 書き下し（by_cases）で定義を解く：
  change (posetTraceCore S m).f ⟨x, hx⟩ = ⟨y, hy⟩
  -- 定義展開
  dsimp [posetTraceCore]
  -- `by_cases` で場合分け（ここでは `false` ケース）
  --have : Decidable (S.f xS = m) := Classical.decEq
  by_cases h : S.f xS = m
  · exact (hfx_ne_m h).elim
  -- `else` 側の構成は `⟨(S.f xS).1, _⟩`。それが `⟨y, _⟩` に一致することを示す。
  -- 値が一致するので `Subtype.ext` で十分。
  apply Subtype.ext
  -- 値成分の等式は `S.f xS = yS` から直ちに従う。
  apply congrArg Subtype.val
  simp_all only [ne_eq, not_false_eq_true, xS, yS]
  simp_all only [↓reduceDIte]

/-- 逆向き：`S.f x ≠ m` なら、`posetTraceCore` でのカバーは元のカバーに戻る。 -/
lemma cover_reflect_if_source_not_to_m
  (S : SPO.FuncSetup α) (m : S.Elem)
  {x y : α}
  (hx : x ∈ S.ground.erase m.1) (hy : y ∈ S.ground.erase m.1)
  (hfx_ne_m : S.f ⟨x, (Finset.mem_erase.mp hx).2⟩ ≠ m)
  (h : (posetTraceCore S m).cover ⟨x, hx⟩ ⟨y, hy⟩) :
  S.cover ⟨x, (Finset.mem_erase.mp hx).2⟩ ⟨y, (Finset.mem_erase.mp hy).2⟩ := by
  -- 展開の用意
  let xS : S.Elem := ⟨x, (Finset.mem_erase.mp hx).2⟩
  let yS : S.Elem := ⟨y, (Finset.mem_erase.mp hy).2⟩
  -- 目標は `S.f xS = yS`
  change S.f xS = yS
  -- `posetTraceCore` の定義で `S.f xS ≠ m` の枝に入っている。
  -- よって `(posetTraceCore S m).f ⟨x,hx⟩ = ⟨(S.f xS).1, _⟩`
  -- それが `⟨y,hy⟩` に等しいという仮定 `h` から、値成分が等しい。
  -- その値成分等式で `Subtype.ext` を使って結論にする。
  have : (posetTraceCore S m).f ⟨x, hx⟩ = ⟨y, hy⟩ := h
  -- 定義展開して `by_cases`（ここでは `false` ケース）
  dsimp [posetTraceCore] at this
  --have : Decidable (S.f xS = m) := Classical.decEq _
  by_cases h' : S.f xS = m
  · exact (hfx_ne_m h').elim
  -- `else` 分岐の構成と等しいので、値成分が一致
  have hv : (S.f xS).1 = y := by
    -- `Subtype.ext` を逆向きに使うため、まず値の等式を作る
    have := congrArg Subtype.val this
    subst this
    simp_all only [ne_eq, not_false_eq_true, posetTraceCore_ground, xS]
    simp_all only [↓reduceDIte]

  -- これで `Subtype.ext` から `S.f xS = yS`
  apply Subtype.ext
  exact hv






--variable {α : Type _} [DecidableEq α]

/-! ### カバー 1 手の分解：S' のカバーは「自ループ」か「元のカバー」 -/

/-- `S' = posetTraceCore S m` でのカバーは，
    その元が `m` を指していないなら元のカバーに戻り，
    `m` を指しているなら自分自身への自ループに限られる。 -/
lemma cover_in_posetTraceCore_elim
  (S : SPO.FuncSetup α) (m : S.Elem)
  {x y : (posetTraceCore S m).Elem}
  (hxy : (posetTraceCore S m).cover x y) :
  y = x ∨
    S.cover
      ⟨x.1, (Finset.mem_erase.mp x.2).2⟩
      ⟨y.1, (Finset.mem_erase.mp y.2).2⟩ := by
  -- 元の世界の要素として見直す
  let xS : S.Elem := ⟨x.1, (Finset.mem_erase.mp x.2).2⟩
  let yS : S.Elem := ⟨y.1, (Finset.mem_erase.mp y.2).2⟩
  -- `S.f xS = m` かで場合分け
  by_cases hfx : S.f xS = m
  · -- この場合、定義上 S' では `x ↦ x`（自ループ）
    -- カバー等式から値成分を比較して y = x を得る
    have hv : ((posetTraceCore S m).f x).1 = y.1 := congrArg Subtype.val hxy
    -- 定義展開して値を見ると `x.1`
    dsimp [posetTraceCore] at hv
    --have : Decidable (S.f xS = m) := Classical.decEq _
    -- then 分岐なので値は `x.1`
    have hv' : x.1 = y.1 := by
      -- `hv` は「if-then-else の値 = y.1」。then 側は `x.1`
      -- `by_cases` と値の一致で結論する
      by_cases h' : S.f xS = m
      · simp_all only [posetTraceCore_ground, ↓reduceDIte, Subtype.coe_eta, xS]
      · exact False.elim (h' hfx)
    -- Subtype の等式へ
    left
    apply Subtype.ext
    exact hv'.symm
  · -- `S.f xS ≠ m` なら，先に示した補題で元のカバーへ戻る
    have hxmem : x.1 ∈ S.ground.erase m.1 := x.2
    have hymem : y.1 ∈ S.ground.erase m.1 := y.2
    have hc :
      S.cover ⟨x.1, (Finset.mem_erase.mp hxmem).2⟩
              ⟨y.1, (Finset.mem_erase.mp hymem).2⟩ :=
      cover_reflect_if_source_not_to_m
        (S := S) (m := m) (x := x.1) (y := y.1)
        hxmem hymem hfx hxy
    right
    exact hc


/-! ### S' の到達関係（`le`）を S に写し戻す -/

/-- `S' = posetTraceCore S m` の到達関係は，
    自ループを捨てつつ 1 手ずつ元のカバーに戻すことで `S.le` へ写る。 -/
lemma le_reflect_to_S_posetTraceCore
  (S : SPO.FuncSetup α) (m : S.Elem)
  {x y : (posetTraceCore S m).Elem}
  (hxy : Relation.ReflTransGen (posetTraceCore S m).cover x y) :
  Relation.ReflTransGen S.cover
    ⟨x.1, (Finset.mem_erase.mp x.2).2⟩
    ⟨y.1, (Finset.mem_erase.mp y.2).2⟩ := by
  -- 記法
  let S' := posetTraceCore S m
  let toS : (S').Elem → S.Elem := fun z =>
    ⟨z.1, (Finset.mem_erase.mp z.2).2⟩
  -- 帰納法で `S'.le x y` を潰す
  refine Relation.ReflTransGen.rec ?h0 ?hstep hxy
  · -- refl
    exact Relation.ReflTransGen.refl
  · -- tail: x ≤' b → cover b c → x ≤ c
    intro b c hb hbc ih
    -- カバー 1 手を分解
    have hsplit := cover_in_posetTraceCore_elim (S := S) (m := m) (x := b) (y := c) hbc
    -- 場合分け
    cases hsplit with
    | inl h_eq =>
        -- 自ループだったので，その手を捨ててそのまま
        -- y = b なので，目標の末尾も b に置き換わる
        -- `ih : S.le (toS x) (toS b)` を `S.le (toS x) (toS c)` に変形
        -- `Subtype.ext` から `toS b = toS c`
        have : toS b = toS c := by
          apply Subtype.ext
          apply congrArg Subtype.val
          exact congrArg toS (id (Eq.symm h_eq))
        -- 書き換え
        -- `ih : ReflTransGen S.cover (toS x) (toS b)`
        -- だが結論は `(toS x) (toS c)` なので，等式で置換
        subst h_eq
        simp_all only [posetTraceCore_ground, toS, S']

    | inr h_cov =>
        -- 元のカバーが得られたので，末尾に 1 手付ける
        exact Relation.ReflTransGen.tail ih h_cov


/-! ### 反対称性：S が半順序なら S' も半順序 -/

/-- `S` が半順序なら `posetTraceCore S m` も半順序。 -/
lemma isPoset_posetTraceCore
  (S : SPO.FuncSetup α) (hpos : isPoset S) (m : S.Elem) :
  isPoset (posetTraceCore S m)  := by
  -- 反対称性だけ示せば良い
  have :(posetTraceCore S m).has_le_antisymm  := by
    intro x y hxy hyx
    -- `S'.le x y` と `S'.le y x` を `S.le` に移す
    have H₁ :
      Relation.ReflTransGen S.cover
        ⟨x.1, (Finset.mem_erase.mp x.2).2⟩
        ⟨y.1, (Finset.mem_erase.mp y.2).2⟩ :=
      le_reflect_to_S_posetTraceCore (S := S) (m := m) (x := x) (y := y) hxy
    have H₂ :
      Relation.ReflTransGen S.cover
        ⟨y.1, (Finset.mem_erase.mp y.2).2⟩
        ⟨x.1, (Finset.mem_erase.mp x.2).2⟩ :=
      le_reflect_to_S_posetTraceCore (S := S) (m := m) (x := y) (y := x) hyx
    -- ここで `antisymm_of_isPoset` を使う

    have : (⟨x.1, (Finset.mem_erase.mp x.2).2⟩ : S.Elem)
         = (⟨y.1, (Finset.mem_erase.mp y.2).2⟩ : S.Elem) :=
      antisymm_of_isPoset (S := S) hpos H₁ H₂
    -- 値成分が等しいので，S' の要素としても等しい
    apply Subtype.ext
    apply congrArg Subtype.val
    simp_all only [le_iff_leOn_val, posetTraceCore_ground, Subtype.mk.injEq]
    obtain ⟨val_1, property_1⟩ := x
    subst this
    simp_all only [posetTraceCore_ground]
    exact rfl

  exact isPoset_of_le_antisymm (posetTraceCore S m) this

/-! ### 自動版（極大元を一意に選んで消す）：`posetTrace` -/

noncomputable def posetTrace (S : FuncSetup α) [Fintype S.Elem]
  (hpos : isPoset S) (hconn : isConnected S) (hne : S.ground.Nonempty) :
  FuncSetup α :=
by
  classical
  let mhm := exists_unique_maximal_of_connected (S := S)
                (hpos := hpos) (hconn := hconn) (hne := hne)
  -- `m` を取り出す（証明部分は `Classical.choose_spec mhm` で必要なら後から参照）
  let m : {x // x ∈ S.ground} := Classical.choose mhm

  -- ここでは m の存在さえ使えればよいので、そのままコアを呼ぶ
  exact posetTraceCore S m

--posetTraceした結果も半順序であることを示す補題
lemma isPoset_posetTrace
  (S : FuncSetup α) [Fintype S.Elem]
  (hpos : isPoset S) (hconn : isConnected S) (hne : S.ground.Nonempty) :
  isPoset (posetTrace S (hpos := hpos) (hconn := hconn) (hne := hne)) := by
  classical
  -- 定義から取り出した極大 `m` に対して `isPoset_posetTraceCore` を適用するだけ
  obtain ⟨m, hm, _huniq⟩ :=
    exists_unique_maximal_of_connected (S := S)
      (hpos := hpos) (hconn := hconn) (hne := hne)
  -- `posetTrace` の定義を展開

  --change isPoset (posetTraceCore S m)

  let ipt := isPoset_posetTraceCore (S := S) (hpos := hpos) (m := m)
  dsimp [posetTrace]
  exact isPoset_posetTraceCore S hpos (choose (exists_unique_maximal_of_connected S hpos hconn hne))

end Forests.Induction
end AvgRare
