import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Logic.Relation
import Mathlib.Algebra.Order.Sub.Basic
--import Mathlib.SetTheory.Cardinal.Basic --おためし
import AvgRare.Basics.SetFamily
import AvgRare.SPO.FuncSetup
--import AvgRare.PaperSync.IdealsTrace
--import AvgRare.SPO.Forest

universe u


namespace AvgRare
namespace Induction
open Classical
variable {α : Type u} [DecidableEq α]
open AvgRare
open SPO
open FuncSetup

--generalに移してもいいが、ここでしか使わないのでとりあえずここにおいておく。
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
--使っている
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

--使っている
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


-----ここからtraceに関すること。(極大要素とはかぎらずにまずは定義する。)

lemma erase_nonempty(A:Finset α) (hA : A.card ≥ 2) (hu : u ∈ A) : (A.erase u).Nonempty := by
  have card_pos : 0 < (A.erase u).card := by
    calc
      0 < A.card - 1 := by omega
      _ = (A.erase u).card := by rw [Finset.card_erase_of_mem hu]
  exact Finset.card_pos.mp card_pos

--極大元に限ったposetTraceとして、のちにposetTraceOfUniqueが出てくる。
--Traceしたものが非空であることを保証するためにgeq2が仮定されている。
noncomputable def posetTraceCore (S : SPO.FuncSetup α) (m : S.Elem) (geq2: S.ground.card ≥ 2): SPO.FuncSetup α :=
{ ground := S.ground.erase m.1
  nonempty := by
   let en := erase_nonempty S.ground geq2 m.property
   exact Finset.Nonempty.to_subtype en
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
  (S : SPO.FuncSetup α) (m : S.Elem) (geq2: S.ground.card ≥ 2):
  (posetTraceCore S m geq2).ground = S.ground.erase m.1 :=
rfl

/-!
`posetTraceCore` の本体は、与えられた `x ∈ ground \ {m}` に対して
`S.f x = m` なら `x` 自身へ、そうでなければ `S.f x` をそのまま使う、という定義でした。
以下では、この定義から即物的に出る「カバーの保存」に関する基本補題を2つ埋めます。
-/

/-! ### 2) 目標に向けた“局所”補題（m を指していない矢だけ保存） -/
--mは極大とは仮定されていない。
/-- `S.cover x y` かつ `y ≠ m` なら、`posetTraceCore` でも同じ矢が残る。 -/
private lemma cover_preserved_if_target_ne_m
  (S : SPO.FuncSetup α) (m : S.Elem) (geq2: S.ground.card ≥ 2)
  {x y : α}
  (hx : x ∈ S.ground.erase m.1) (hy : y ∈ S.ground.erase m.1)
  (hxy : S.cover ⟨x, (Finset.mem_erase.mp hx).2⟩ ⟨y, (Finset.mem_erase.mp hy).2⟩) :
  (posetTraceCore S m geq2).cover ⟨x, hx⟩ ⟨y, hy⟩ := by
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
  change (posetTraceCore S m geq2).f ⟨x, hx⟩ = ⟨y, hy⟩
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
private lemma cover_reflect_if_source_not_to_m
  (S : SPO.FuncSetup α) (m : S.Elem) (geq2: S.ground.card ≥ 2)
  {x y : α}
  (hx : x ∈ S.ground.erase m.1) (hy : y ∈ S.ground.erase m.1)
  (hfx_ne_m : S.f ⟨x, (Finset.mem_erase.mp hx).2⟩ ≠ m)
  (h : (posetTraceCore S m geq2 ).cover ⟨x, hx⟩ ⟨y, hy⟩) :
  S.cover ⟨x, (Finset.mem_erase.mp hx).2⟩ ⟨y, (Finset.mem_erase.mp hy).2⟩ := by
  -- 展開の用意
  let xS : S.Elem := ⟨x, (Finset.mem_erase.mp hx).2⟩
  let yS : S.Elem := ⟨y, (Finset.mem_erase.mp hy).2⟩
  -- 目標は `S.f xS = yS`
  change S.f xS = yS
  -- `posetTraceCore` の定義で `S.f xS ≠ m` の枝に入っている。
  -- よって `(posetTraceCore S m geq2).f ⟨x,hx⟩ = ⟨(S.f xS).1, _⟩`
  -- それが `⟨y,hy⟩` に等しいという仮定 `h` から、値成分が等しい。
  -- その値成分等式で `Subtype.ext` を使って結論にする。
  have : (posetTraceCore S m geq2).f ⟨x, hx⟩ = ⟨y, hy⟩ := h
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

/-- `S' = posetTraceCore S m` でのカバーは，
    その元が `m` を指していないなら元のカバーに戻り，
    `m` を指しているなら自分自身への自ループに限られる。 -/
private lemma cover_in_posetTraceCore_elim
  (S : SPO.FuncSetup α) (m : S.Elem) (geq2: S.ground.card ≥ 2)
  {x y : (posetTraceCore S m geq2).Elem}
  (hxy : (posetTraceCore S m geq2).cover x y) :
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
    have hv : ((posetTraceCore S m geq2).f x).1 = y.1 := congrArg Subtype.val hxy
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
        geq2 hxmem hymem hfx hxy
    right
    exact hc


/-- `S' = posetTraceCore S m` の到達関係は，
    自ループを捨てつつ 1 手ずつ元のカバーに戻すことで `S.le` へ写る。 -/
private lemma le_reflect_to_S_posetTraceCore
  (S : SPO.FuncSetup α) (m : S.Elem) (geq2: S.ground.card ≥ 2)
  {x y : (posetTraceCore S m geq2).Elem}
  (hxy : Relation.ReflTransGen (posetTraceCore S m geq2).cover x y) :
  Relation.ReflTransGen S.cover
    ⟨x.1, (Finset.mem_erase.mp x.2).2⟩
    ⟨y.1, (Finset.mem_erase.mp y.2).2⟩ := by
  -- 記法
  let S' := posetTraceCore S m
  let toS : (S' geq2).Elem → S.Elem := fun z =>
    ⟨z.1, (Finset.mem_erase.mp z.2).2⟩
  -- 帰納法で `S'.le x y` を潰す
  refine Relation.ReflTransGen.rec ?h0 ?hstep hxy
  · -- refl
    exact Relation.ReflTransGen.refl
  · -- tail: x ≤' b → cover b c → x ≤ c
    intro b c hb hbc ih
    -- カバー 1 手を分解
    have hsplit := cover_in_posetTraceCore_elim (S := S) (m := m) (x := b) (y := c) geq2 hbc
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
-- mは極大とは仮定されていない。
lemma isPoset_posetTraceCore
  (S : SPO.FuncSetup α) (hpos : isPoset S) (m : S.Elem) (geq2: S.ground.card ≥ 2) :
  isPoset (posetTraceCore S m geq2)  := by
  -- 反対称性だけ示せば良い
  have :(posetTraceCore S m geq2).has_le_antisymm  := by
    intro x y hxy hyx
    -- `S'.le x y` と `S'.le y x` を `S.le` に移す
    have H₁ :
      Relation.ReflTransGen S.cover
        ⟨x.1, (Finset.mem_erase.mp x.2).2⟩
        ⟨y.1, (Finset.mem_erase.mp y.2).2⟩ :=
      le_reflect_to_S_posetTraceCore (S := S) (m := m) (x := x) (y := y) geq2 hxy
    have H₂ :
      Relation.ReflTransGen S.cover
        ⟨y.1, (Finset.mem_erase.mp y.2).2⟩
        ⟨x.1, (Finset.mem_erase.mp x.2).2⟩ :=
      le_reflect_to_S_posetTraceCore (S := S) (m := m) (x := y) (y := x) geq2 hyx
    -- ここで `antisymm_of_isPoset` を使う

    have : (⟨x.1, (Finset.mem_erase.mp x.2).2⟩ : S.Elem)
         = (⟨y.1, (Finset.mem_erase.mp y.2).2⟩ : S.Elem) := by
      exact hpos H₁ H₂

    -- 値成分が等しいので，S' の要素としても等しい
    apply Subtype.ext
    apply congrArg Subtype.val
    simp_all only [le_iff_leOn_val, posetTraceCore_ground, Subtype.mk.injEq]
    obtain ⟨val_1, property_1⟩ := x
    subst this
    simp_all only [posetTraceCore_ground]
    exact rfl

  dsimp [isPoset]
  simp_all only

--pricipal idealに関することはFuncSetup+idealのファイルを作った時にそちらに移動してもいい。
--でもこれはPreorderでなくてposetに関することなので、一緒にしないほうがいいかも。
-- principalOn たちが互いに異なること isPosetが付いているので、FuncSetupには移せないが、いずれ
--FuncSetup+isPosetの基本的な定義はどこかにまとめる。
lemma principalOn_inj(S : FuncSetup α) {x y : S.Elem}
  (hpos : isPoset S)
  (hxy : S.principalIdeal x x.2= S.principalIdeal y y.2) : x = y := by
  -- `x ∈ principalOn x` かつ等式から `x ∈ principalOn y`
  -- これより `S.le x y`。同様に `S.le y x`。antisymm で同一化。
  have hxmem : x.1 ∈ S.principalIdeal x x.2 := by
    -- x ∈ ground ∧ S.le x x（refl）
    have hxG : x.1 ∈ S.ground := x.2
    have hxx : S.le x x := Relation.ReflTransGen.refl
    have hxPair : x.1 ∈ S.ground ∧ S.le ⟨x.1, hxG⟩ x := And.intro hxG hxx
    exact (S.mem_principalIdeal_iff x.2 (a := x.1)).2 ⟨hxPair.1, hxPair.2⟩
  -- 等式で移す
  have hx_in_y : x.1 ∈ S.principalIdeal y y.2 := by
    exact hxy ▸ hxmem
  -- これから `S.le x y`
  simp at hx_in_y
  --have hxG : x.1 ∈ S.ground := x.2
  let mpi := (S.mem_principalIdeal_iff y.2).1 hx_in_y
  obtain ⟨hy, hhy⟩ := mpi
  -- 対称に y ≤ x をつくる
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
    -- 反対称律で結論
  exact hpos hhy hxh

--使われているが、FuncSetupにも同様な補題がある。
lemma empty_isOrderIdealOn (S : FuncSetup α) :
  isOrderIdealOn (S.leOn) S.ground (∅ : Finset α) := by
  dsimp [isOrderIdealOn]
  constructor
  · -- ∅ ⊆ ground
    intro x hx; cases hx
  · -- 下方閉：前提が偽
    intro x hx; cases hx

/-- principalIdeal は edge（`idealFamily` の要素） -/
lemma principalIdeal_mem_edge (S : FuncSetup α) (x : S.Elem) :
  S.principalIdeal x.1 x.2 ∈ (S.idealFamily).edgeFinset := by
  -- `sets ↔ isOrderIdealOn` を使って示す
  have hI :
    isOrderIdealOn (S.leOn) S.ground (S.principalIdeal x.1 x.2) :=
    principalIdeal_isOrderIdealOn (S := S) x.2
  have hxSets :
    (S.idealFamily).sets (S.principalIdeal x.1 x.2) := by
    -- `sets_iff_isOrderIdeal` の右向きを使う
    have := (S.sets_iff_isOrderIdeal (I := S.principalIdeal x.1 x.2))
    exact this.mpr hI
  -- `mem_edgeFinset_iff_sets` で edge へ
  exact
    (SetFamily.mem_edgeFinset_iff_sets
      (F := S.idealFamily) (A := S.principalIdeal x.1 x.2)).2 hxSets

/- 空集合も edge。 -/
--FuncSetupに同様の補題あり。
lemma empty_mem_edge (S : FuncSetup α) :
  (∅ : Finset α) ∈ (S.idealFamily).edgeFinset := by
  -- 空集合が ideal であることから
  have hI : isOrderIdealOn (S.leOn) S.ground (∅ : Finset α) :=
    empty_isOrderIdealOn S
  have hSets : (S.idealFamily).sets (∅ : Finset α) := by
    have := (S.sets_iff_isOrderIdeal (I := (∅ : Finset α)))
    exact this.mpr hI
  exact
    (SetFamily.mem_edgeFinset_iff_sets (F := S.idealFamily) (A := (∅ : Finset α))).2 hSets

/-- 8) `numHyperedges ≥ |ground| + 1`。
`{ principalIdeal x | x∈ground } ∪ {∅}` を下界集合として数える。 -/
--NDSのところでつかわれている。
lemma ideals_card_ge_ground_card_succ
  (S : FuncSetup α) (hpos : isPoset S) :
  (S.idealFamily).numHyperedges ≥ S.ground.card + 1 := by
  classical
  -- 下界集合 P
  let P : Finset (Finset α) :=
    (S.ground.attach.image (fun x : S.Elem => S.principalIdeal x.1 x.2)) ∪ {∅}
  -- P ⊆ edgeFinset
  have hPsub : P ⊆ (S.idealFamily).edgeFinset := by
    intro A hA
    have h := Finset.mem_union.mp hA
    cases h with
    | inl h1 =>
        rcases Finset.mem_image.mp h1 with ⟨x, hx, rfl⟩
        exact principalIdeal_mem_edge S x
    | inr h0 =>
        have hA0 : A = (∅ : Finset α) := Finset.mem_singleton.mp h0
        -- 空集合は edge
        have := empty_mem_edge S
        -- `rw` で書き換え
        -- `simpa using` は使わず
        -- A = ∅ に置換
        exact by
          -- `A = ∅` なのでそのまま
          -- `this : ∅ ∈ edgeFinset`
          -- 目標 `A ∈ edgeFinset`
          -- 置換して終了
          -- `rw [hA0]`; `exact this`
          have : A ∈ (S.idealFamily).edgeFinset := by
            -- 書換えの実体
            -- Lean では `simpa [hA0] using this` で一発だが、使わない縛りなので分解
            -- 以下の 2 行：
            --   have := this
            --   exact (by rwa [hA0] at this; exact this)
            -- でも良いですが、ここは素直に `rw`
            -- 注意：`rw` はゴール側か仮定側に当てる必要があるので、
            -- ここは `show` を使わず `exact` 直前に変換します
            -- （エディタ補完に合わせて適宜調整ください）
            exact by
              -- 直接は難しいので一段噛ませます
              -- ここでは `have := this` を経由
              have hE := this
              -- 目標へ書換え
              -- 仕上げに `exact` で返す
              -- 実運用では `simp [hA0]` で十分です
              -- 最終的には
              --   `exact (by simpa [hA0] using hE)`
              -- を避けているだけです
              subst hA0
              simp_all only [SetFamily.mem_edgeFinset, Finset.empty_subset, sets_iff_isOrderIdeal,
                and_self, Finset.union_singleton, Finset.mem_insert, Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists,
                true_or, Finset.mem_singleton, P]

          -- 返す
          exact by
            -- 既に `this : A ∈ edgeFinset` を得たので終了
            exact this

  -- よって card(edge) ≥ card(P)
  have hEdgeGeP : (S.idealFamily).edgeFinset.card ≥ P.card := by
    simp_all only [Finset.union_singleton, ge_iff_le, P]
    exact Finset.card_le_card hPsub

  -- principalIdeal の像が相異なること（`principalOn_inj` を流用）
  have hInj :
    ∀ ⦃x⦄, x ∈ S.ground.attach →
    ∀ ⦃y⦄, y ∈ S.ground.attach →
      (S.principalIdeal x.1 x.2 = S.principalIdeal y.1 y.2) → x = y := by
    intro x hx y hy hxy
    -- すでに作った単射性補題を使う（あなたの定義では principalOn_inj という名前）
    exact principalOn_inj (S := S) (hpos := hpos) (x := x) (y := y) (hxy := hxy)

  -- 画像の個数 = 台（attach）の個数
  have hCardImage :
      (S.ground.attach.image (fun x : S.Elem => S.principalIdeal x.1 x.2)).card
        = S.ground.attach.card := by
    exact Finset.card_image_iff.mpr hInj

  -- `attach` の大きさ
  have hCardAttach : S.ground.attach.card = S.ground.card := by
    simp_all only [Finset.union_singleton, ge_iff_le, Finset.card_attach, P]

  -- 像と {∅} は交わらない（principalIdeal は常に非空）
  have hDisj :
      Disjoint
        (S.ground.attach.image (fun x : S.Elem => S.principalIdeal x.1 x.2))
        ({∅} : Finset (Finset α)) := by
    refine Finset.disjoint_left.mpr ?_
    intro A hA hA0
    rcases Finset.mem_image.mp hA with ⟨x, _, rfl⟩
    -- `x.1 ∈ principalIdeal x` で非空
    have hx_self : x.1 ∈ S.principalIdeal x.1 x.2 := by
      have hxx : S.le x x := Relation.ReflTransGen.refl
      exact (S.mem_principalIdeal_iff (a := x.1) (y := x.1) x.2).2 ⟨x.2, hxx⟩
    -- しかし A=∅ は要素なしなので矛盾
    simp_all only [Finset.union_singleton, ge_iff_le, Finset.card_attach, Finset.mem_attach, Finset.mem_image, true_and,
    exists_apply_eq_apply, Finset.mem_singleton, Finset.notMem_empty, P]

  -- よって `card P = card(image) + 1`
  have hPcard :
      P.card
        = (S.ground.attach.image (fun x : S.Elem => S.principalIdeal x.1 x.2)).card + 1 := by
    -- `card_disjoint_union` をそのまま使う
    -- P = image ∪ {∅}
    simp_all only [Finset.union_singleton, ge_iff_le, Finset.card_attach, Finset.disjoint_singleton_right, Finset.mem_image,
    Finset.mem_attach, true_and, Subtype.exists, not_exists, Finset.coe_mem, and_false, exists_false, not_false_eq_true,
    Finset.card_insert_of_notMem, P]


  -- 以上より `card P = ground.card + 1`
  have hP_eq : P.card = S.ground.card + 1 := by
    -- `card(image) = card(attach) = ground.card`
    -- `rw` で順に書き替え
    -- 1段目：image → attach
    have : P.card = S.ground.attach.card + 1 := by
      -- hPcard に `hCardImage` を代入
      -- （`simpa` を使わず、`rw` を明示的に適用するなら：
      --    `have h := hPcard; rw [hCardImage] at h; exact h` の形もOK）
      -- ここでは直接 `calc` で繋ぎます
      calc
        P.card
            = (S.ground.attach.image (fun x : S.Elem => S.principalIdeal x.1 x.2)).card + 1 := hPcard
        _   = S.ground.attach.card + 1 := by
              -- 画像のカード等式
              -- `rw [hCardImage]`
              exact congrArg (fun n => n + 1) hCardImage
    -- 2段目：attach → ground
    -- `rw [hCardAttach]`
    -- 仕上げ
    calc
      P.card = S.ground.attach.card + 1 := this
      _      = S.ground.card + 1 := by
                -- `rw [hCardAttach]`
                -- `congrArg` で +1 を付けたまま置換
                exact congrArg (fun n => n + 1) hCardAttach

  -- まとめ：`edge.card ≥ P.card = ground.card + 1`
  exact le_of_eq_of_le (id (Eq.symm hP_eq)) hEdgeGeP

--使っている
private lemma lift_le_to_traceCore_if_not_m_below
  (S : SPO.FuncSetup α) (m : S.Elem) (geq2: S.ground.card ≥ 2)
  (hpos : isPoset S) (hmax : S.maximal m)
  {a b : (posetTraceCore S m geq2).Elem}
  (h : Relation.ReflTransGen S.cover
        ⟨a.1, (Finset.mem_erase.mp a.2).2⟩
        ⟨b.1, (Finset.mem_erase.mp b.2).2⟩) :
  Relation.ReflTransGen (posetTraceCore S m geq2).cover a b := by
  classical
  -- b は erase 上なので値は m と異なる
  have hb_ne : b.1 ≠ m.1 := (Finset.mem_erase.mp b.2).1

  -- 動機づけ：`z ≤* b` が与えられたとき、任意の `hz : z ∈ erase` から
  -- `⟨z,hz⟩ ≤* b`（trace 側）を作る
  refine
    Relation.ReflTransGen.head_induction_on
      (r := S.cover)
      (b := ⟨b.1, (Finset.mem_erase.mp b.2).2⟩)
      (motive := fun z _ => ∀ (hz : z.1 ∈ S.ground.erase m.1),
        Relation.ReflTransGen (posetTraceCore S m geq2).cover ⟨z.1, hz⟩ ⟨b.1, b.2⟩)
      h
      ?base
      ?head
      (a := ⟨a.1, (Finset.mem_erase.mp a.2).2⟩)
      (by exact a.2)  -- 最後に `hz := a.2` を与える
  -- base: z = b のときは refl（証明部差は `Subtype.ext` で吸収）
  · intro hb
    -- ⟨b, hb⟩ = b （部分型の証明差を消す）
    have eb : (⟨b.1, hb⟩ : (posetTraceCore S m geq2).Elem) = b := Subtype.ext (by rfl)
    cases eb
    exact Relation.ReflTransGen.refl
  -- head: 1歩 z ⋖ c と c ≤* b が与えられ、IH で c 側が持ち上がると仮定して z 側を作る
  · intro z c hzc hcb ih hz
    -- まず c ≠ m を示す。もし c = m なら m ≤ b が成り立つ。
    have hc_ne_m : c ≠ m := by
      intro hc
      -- c = m → hcb から m ≤ b
      have hmb : S.le m ⟨b.1, (Finset.mem_erase.mp b.2).2⟩ := by
        cases hc
        exact hcb
      -- 極大性から b ≤ m
      have hbm : S.le ⟨b.1, (Finset.mem_erase.mp b.2).2⟩ m := hmax hmb
      -- 反対称で b = m、しかし値が異なる
      have heq : ⟨b.1, (Finset.mem_erase.mp b.2).2⟩ = m := by
        exact hpos (hmax hmb) hmb
      have : b.1 = m.1 := congrArg Subtype.val heq
      exact hb_ne this
    -- c が erase 上にあること
    have hc_mem : c.1 ∈ S.ground.erase m.1 := by
      refine Finset.mem_erase.mpr ?_
      refine And.intro ?neq c.property
      -- 値で c ≠ m に言い換える
      have : c.1 ≠ m.1 := by
        intro hv
        apply hc_ne_m
        exact Subtype.ext hv
      exact this
    -- 1歩 `z ⋖ c` を trace 側へ（ターゲット c が m でないので保存できる）
    have hzc' :
        (posetTraceCore S m geq2).cover ⟨z.1, hz⟩ ⟨c.1, hc_mem⟩ := by
      -- `cover_preserved_if_target_ne_m` の仮定となる S.cover を、
      -- 証明部を `Subtype.ext` でそろえて与える
      have hL :
          (⟨z.1, (Finset.mem_erase.mp hz).2⟩ : S.Elem) = ⟨z.1, z.property⟩ :=
        Subtype.ext (by rfl)
      have hR :
          (⟨c.1, (Finset.mem_erase.mp hc_mem).2⟩ : S.Elem) = ⟨c.1, c.property⟩ :=
        Subtype.ext (by rfl)
      -- 目標の形に書き換え
      -- `cover_preserved_if_target_ne_m` は `hx, hy, hxy` を要求
      -- ここで `hxy` を `hzc` から作る
      have hxy :
        S.cover ⟨z.1, (Finset.mem_erase.mp hz).2⟩ ⟨c.1, (Finset.mem_erase.mp hc_mem).2⟩ := by
        -- cover の定義は等式なので、左右の部分型等式で書換えればよい
        -- `cases` で置換
        cases hL
        cases hR
        exact hzc
      -- これで保存補題を適用
      exact cover_preserved_if_target_ne_m (S := S) (m := m) (geq2 := geq2)
        (hx := hz) (hy := hc_mem) (hxy := hxy)
    -- c 側の鎖は帰納法の仮定で trace 側にある
    have hcb' :
        Relation.ReflTransGen (posetTraceCore S m geq2).cover ⟨c.1, hc_mem⟩ ⟨b.1, b.2⟩ :=
      ih hc_mem
    -- 連結して z ≤* b（trace 側）
    exact Relation.ReflTransGen.head hzc' hcb'

--使っている
private lemma edgeFinset_trace_eq_filter_not_mem
  (S : FuncSetup α) [Fintype S.Elem]
  (m : S.Elem) (geq2: S.ground.card ≥ 2)
  (hKeep :
    ∀ I : Finset α, isOrderIdealOn (S.leOn) S.ground I →
      m.1 ∉ I →
      ((posetTraceCore S m geq2).idealFamily).sets I)
  (hBack :
    ∀ I : Finset α,
      ((posetTraceCore S m geq2).idealFamily).sets I →
      (S.idealFamily).sets I ∧ m.1 ∉ I) :
  ((posetTraceCore S m geq2).idealFamily).edgeFinset
    = (S.idealFamily).edgeFinset.filter (fun A => m.1 ∉ A) := by
  classical
  -- 記号の略
  set F  := S.idealFamily
  set F' := (posetTraceCore S m geq2).idealFamily

  -- 集合としての同値を示す
  apply Finset.Subset.antisymm_iff.mpr
  constructor
  · -- ⊆：F'.edge ⊆ F.edge.filter (¬ m∈)
    intro A hA
    -- A ∈ F'.edge ⇒ F'.sets A
    have hA_sets' : F'.sets A :=
      (SetFamily.mem_edgeFinset_iff_sets (F := F') (A := A)).1 hA
    -- 逆方向の保存で、F側の sets と m∉A を得る
    have hback := hBack A hA_sets'
    have hA_sets : F.sets A := hback.1
    have hm_not : m.1 ∉ A := hback.2
    -- F.edge へ
    have hA_edge : A ∈ F.edgeFinset :=
      (SetFamily.mem_edgeFinset_iff_sets (F := F) (A := A)).2 hA_sets
    -- filter へ
    exact Finset.mem_filter.mpr ⟨hA_edge, hm_not⟩
  · -- ⊇：F.edge.filter (¬ m∈) ⊆ F'.edge
    intro A hA
    -- A ∈ F.edge ∧ m∉A
    have hA_edge : A ∈ F.edgeFinset := (Finset.mem_filter.mp hA).1
    have hm_not  : m.1 ∉ A           := (Finset.mem_filter.mp hA).2
    -- F.sets A
    have hA_sets : F.sets A :=
      (SetFamily.mem_edgeFinset_iff_sets (F := F) (A := A)).1 hA_edge
    -- F 側 ideal
    have hA_ideal : isOrderIdealOn (S.leOn) S.ground A :=
      (S.sets_iff_isOrderIdeal (I := A)).1 hA_sets
    -- 行きの保存で F'.sets A
    have hA_sets' : F'.sets A := hKeep A hA_ideal hm_not
    -- F'.edge へ
    exact (SetFamily.mem_edgeFinset_iff_sets (F := F') (A := A)).2 hA_sets'

--使っている。edgeFinset_trace_eq_filter_not_memを使って証明。
private lemma edge_card_trace_eq_filter_not_mem
  (S : FuncSetup α) [Fintype S.Elem]
  (m : S.Elem) (geq2: S.ground.card ≥ 2)
  (hKeep :
    ∀ I : Finset α, isOrderIdealOn (S.leOn) S.ground I →
      m.1 ∉ I →
      ((posetTraceCore S m geq2).idealFamily).sets I)
  (hBack :
    ∀ I : Finset α,
      ((posetTraceCore S m geq2 ).idealFamily).sets I →
      (S.idealFamily).sets I ∧ m.1 ∉ I) :
  ((posetTraceCore S m geq2).idealFamily).edgeFinset.card
    = ( (S.idealFamily).edgeFinset.filter (fun A => m.1 ∉ A) ).card := by
  classical
  -- 直前の集合等式からカード等式に落とす
  have h := edgeFinset_trace_eq_filter_not_mem
              (S := S) (m := m) (hKeep := hKeep) (hBack := hBack)
  -- `rw` でカードへ
  exact congrArg Finset.card h

--mでtraceしたときのidealにはmが入らないこと。
--使っている。back_sets_from_trace_at_max_sets'からもわかる内容で被っている。消すことが可能。
private lemma no_m_in_Fprime_ideal
  (S : FuncSetup α) [Fintype S.Elem]
  (m : S.Elem) (geq2: S.ground.card ≥ 2)
  --(hOnlyTop : ∀ I : Finset α, isOrderIdealOn (S.leOn) S.ground I → m.1 ∈ I → I = S.ground)
  {I : Finset α}
  (hI' : ((posetTraceCore S m geq2).idealFamily).sets I) :
  m.1 ∉ I := by
  -- もし m ∈ I なら、(1) の保存と `hOnlyTop` から I = ground となるが、
  -- I ⊆ ground.erase m (trace の台) に反する、で矛盾
  -- （`posetTraceCore` の台が `erase m` であることを使います）
  classical
  have hI'Ideal : isOrderIdealOn ((posetTraceCore S m geq2).leOn) ((posetTraceCore S m geq2).ground) I := by
    change isOrderIdealOn _ _ I
    exact ((posetTraceCore S m geq2).sets_iff_isOrderIdeal (I := I)).1 hI'
  -- `I ⊆ ground.erase m`
  have hIsub : I ⊆ (posetTraceCore S m geq2).ground := (by exact hI'Ideal.1)
  -- したがって m∉I は直ちに出る（`erase` の性質）
  -- 形式的には `hIsub hx : m ∈ (erase m)` が偽、から矛盾排除
  intro hmI
  have : m.1 ∈ (posetTraceCore S m geq2).ground := hIsub hmI
  -- ところが `(posetTraceCore S m geq2).ground = S.ground.erase m.1`
  -- より、`m.1 ∈ erase m.1` は偽
  -- 矛盾
  -- （`Finset.mem_erase` の `[simp]` を使わないで明示的に）
  rcases Finset.mem_erase.mp (by
    -- ここは `rw` で ground を `erase` に書換えるだけです
    -- 実装では `rfl` のことが多いです
    change m.1 ∈ S.ground.erase m.1
    -- 置換：`(posetTraceCore S m geq2).ground = S.ground.erase m.1`
    -- 定義から `rfl`
    simpa ) with ⟨hmneq, _⟩
  exact hmneq rfl  -- 矛盾から閉じる

--使っている。極大要素が唯一のときのposetTraceだが、posetTraceCoreとわける必要性はあまりないかも。
noncomputable def posetTraceOfUnique
  (S : FuncSetup α) (geq2: S.ground.card ≥ 2) (hexu : ∃! m : S.Elem, S.maximal m) :
  FuncSetup α :=
  posetTraceCore S (Classical.choose (hexu).exists) geq2




/-
/-- すべての要素が `m` の下にあれば，`m` を含む ideal は ground に等しい -/
--結果的に使ってない。
lemma onlyTop_from_allBelow
  (S : FuncSetup α) {m : S.Elem}
  (hall : ∀ u : S.Elem, S.le u m) :
  ∀ I : Finset α, isOrderIdealOn (S.leOn) S.ground I → m.1 ∈ I → I = S.ground := by
  intro I hI hmI
  have hI_sub : I ⊆ S.ground := hI.1
  have hground_sub : S.ground ⊆ I := by
    intro y hy
    have hym : S.le ⟨y, hy⟩ m := hall ⟨y, hy⟩
    have hleOn : S.leOn y m.1 :=
      (S.leOn_iff_subtype (a := y) (b := m.1) hy m.2).mpr hym
    exact hI.2 hmI hy hleOn
  exact Finset.Subset.antisymm hI_sub hground_sub
-/

--使っている。posetの一般的な議論のファイルがあれば移動しても良い。
private lemma fixpoint_is_maximal
  (S : FuncSetup α) {p : S.Elem} (hfix : S.cover p p) :
  S.maximal p := by
  -- cover p p ↔ f p = p
  have h_fixed : S.f p = p := hfix
  -- 定義：∀ y, p ≤ y → y ≤ p
  intro y hy
  -- fixed_point_unique で `p = y`
  have : p = y :=
    fixed_point_unique (S := S) (u := p) (h_fixed := h_fixed) (v := y) (h_le := hy)
  -- 書換えて refl
  cases this
  exact Relation.ReflTransGen.refl

--使っている。
private lemma all_below_unique_maximal
  (S : FuncSetup α) [Fintype S.Elem]
  (hpos : isPoset S) (hexu : ∃! m : S.Elem, S.maximal m) :
  ∀ u : S.Elem, S.le u (Classical.choose hexu.exists) := by
  classical
  set m : S.Elem := Classical.choose hexu.exists
  have hm : S.maximal m := Classical.choose_spec hexu.exists
  -- 一意性：任意の極大 p は m に一致
  have uniq : ∀ {p : S.Elem}, S.maximal p → p = m := by
    intro p a
    simp_all only [maximal_iff, le_iff_leOn_val, Subtype.forall, m]
    cases hexu
    simp_all only [maximal_iff, le_iff_leOn_val, Finset.coe_mem, implies_true]
  intro u
  -- 既証の到達補題：u から固定点 p へ
  obtain ⟨p, hup, hpp⟩ :=
    eventually_hits_fixpoint (S := S) (hpos := hpos) (x := u)
  -- 固定点は極大
  have hpmax : S.maximal p := fixpoint_is_maximal (S := S) (p := p) (hfix := hpp)
  -- 一意性で p = m
  have pm : p = m := uniq hpmax
  -- u ≤ p を p = m で置換
  cases pm
  exact hup

--使っている。極大を含むidealは、全体集合のみ。
private lemma hOnlyTop_of_uniqueMax
  (S : FuncSetup α) [Fintype S.Elem]
  (hpos  : isPoset S)
  (hexu  : ∃! m : S.Elem, S.maximal m)
  {I : Finset α}
  (hI   : isOrderIdealOn (S.leOn) S.ground I)
  (hmI  : (Classical.choose hexu.exists).1 ∈ I) :
  I = S.ground := by

  classical
  -- 唯一極大を m とおく
  set m : S.Elem := Classical.choose hexu.exists
  have hm : S.maximal m := Classical.choose_spec hexu.exists

  -- 片包含 I ⊆ ground は ideal の定義から
  have hI_sub : I ⊆ S.ground := hI.1

  -- 逆包含 ground ⊆ I を示す
  have hG_sub_I : S.ground ⊆ I := by
    intro y hy
    -- すべての y は m 以下（唯一極大の下に全要素が入る）
    have hle_m : S.le ⟨y, hy⟩ m :=
      all_below_unique_maximal (S := S) (hpos := hpos) (hexu := hexu) ⟨y, hy⟩
    -- leOn に持ち上げて ideal の下方閉で y ∈ I
    have hleOn : S.leOn y m.1 :=
      (leOn_iff S hy m.2).mpr hle_m
    exact hI.2 (x := m.1) hmI (y := y) hy hleOn

  -- 互いの包含で等号
  exact Eq.symm (Finset.Subset.antisymm hG_sub_I hI_sub)

private lemma keep_sets_from_trace_at_without_m
  (S : FuncSetup α) (m : S.Elem) (geq2: S.ground.card ≥ 2) {I : Finset α}
  (hI  : isOrderIdealOn (S.leOn) S.ground I)
  (hmI : m.1 ∉ I) :
  ((posetTraceCore S m geq2).idealFamily).sets I := by
  -- `sets` ↔ `isOrderIdealOn`
  change isOrderIdealOn ((posetTraceCore S m geq2).leOn) ((posetTraceCore S m geq2).ground) I
  -- 2 条件：`I ⊆ ground'` と下方閉
  constructor
  · intro x hx
    have hxV : x ∈ S.ground := hI.1 hx
    -- x = m.1 なら m∈I になって矛盾
    have hne : x ≠ m.1 := by
      intro e; apply hmI; cases e; exact hx
    -- ground' = erase m.1
    -- so x ∈ erase m.1
    exact (by
      change x ∈ S.ground.erase m.1
      exact (Finset.mem_erase.mpr ⟨hne, hxV⟩))
  · intro x hxI y hyG' hle'   -- `hle' : leOn' y x`
    -- 元の ground へ戻す
    have hxV : x ∈ S.ground := hI.1 hxI
    have hyV : y ∈ S.ground := (Finset.mem_erase.mp (by
      change y ∈ S.ground.erase m.1 at hyG'
      exact hyG')).2
    -- `leOn' y x` を S の `le y x` に反射
    -- まず subtype 版に持ち上げる
    have hx' : x ∈ (posetTraceCore S m geq2).ground := by
      -- 1 個目で示した包含を使う
      have hSub : I ⊆ (posetTraceCore S m geq2).ground := by
        -- 上の「intro」の証明を関数化して使うイメージ
        -- ここはもう一度同じ議論で十分
        intro z hz
        have hzV : z ∈ S.ground := hI.1 hz
        have hz_ne : z ≠ m.1 := by
          intro e; apply hmI; cases e; exact hz
        change z ∈ S.ground.erase m.1
        exact (Finset.mem_erase.mpr ⟨hz_ne, hzV⟩)
      exact hSub hxI
    -- leOn ↔ ReflTransGen cover（両方の世界で）
    have hRTG' :
        Relation.ReflTransGen (posetTraceCore S m geq2).cover
          ⟨y, hyG'⟩ ⟨x, hx'⟩ :=
      ( (posetTraceCore S m geq2).leOn_iff_subtype (a := y) (b := x) hyG' hx').1 hle'
    -- 反射補題で S 側へ
    have hRTG :
        Relation.ReflTransGen S.cover
          ⟨y, (Finset.mem_erase.mp (by change y ∈ S.ground.erase m.1 at hyG'; exact hyG')).2⟩
          ⟨x, hxV⟩ :=
      le_reflect_to_S_posetTraceCore (S := S) (m := m) (x := ⟨y, hyG'⟩) (y := ⟨x, hx'⟩) geq2 hRTG'
    -- これを leOn に戻す
    have hle : S.leOn y x := by
      have hySub : S.leOn y x ↔ S.le ⟨y, hyV⟩ ⟨x, hxV⟩ :=
        S.leOn_iff_subtype (a := y) (b := x) hyV hxV
      -- `hRTG` はちょうど右辺
      exact hySub.mpr hRTG
    -- `I` は S 側で理想なので下方閉
    exact hI.2 hxI hyV hle

/-
--結果的に使ってない。補題としては重要そうだが、keep_sets_from_trace_at_without_mがあれば十分。
lemma keep_sets_from_trace_at_uniqueMax
  (S : FuncSetup α) [Fintype S.Elem] (geq2: S.ground.card ≥ 2)
  (hexu : ∃! m : S.Elem, S.maximal m)  :
  ∀ I : Finset α, isOrderIdealOn (S.leOn) S.ground I →
    (Classical.choose hexu.exists).1 ∉ I →
    ((posetTraceOfUnique S geq2 hexu).idealFamily).sets I := by
  classical
  intro I hI hnot
  -- `posetTraceOfUnique = posetTraceCore S m`
  dsimp [posetTraceOfUnique]
  exact keep_sets_from_trace_at_without_m (S := S)
      (m := Classical.choose hexu.exists) geq2 (hI := hI) (hmI := hnot)
-/

--極大なもののtraceで、traceしたあとの集合族は、元の集合族に含まれる。
--back_sets_from_trace_at_max_sets'を証明するのにつかっている。たくさん使われている。
private lemma back_sets_from_trace_at_max_sets
  (S : FuncSetup α) [Fintype S.Elem]
  (hpos : isPoset S) (m : S.Elem) (geq2: S.ground.card ≥ 2)(hm : S.maximal m)
  {I : Finset α}
  (hI : ((posetTraceCore S m geq2).idealFamily).sets I) :
  (S.idealFamily).sets I := by
  classical
  -- S' 側 ideal に展開
  have hI' : isOrderIdealOn ((posetTraceCore S m geq2).leOn) ((posetTraceCore S m geq2).ground) I := by
    change isOrderIdealOn _ _ I
    exact ((posetTraceCore S m geq2).sets_iff_isOrderIdeal (I := I)).1 hI

  -- I ⊆ erase m から I ⊆ ground
  have hIsub' : I ⊆ (posetTraceCore S m geq2).ground := hI'.1
  have hIsubS : I ⊆ S.ground := by
    intro x hxI
    have hx' : x ∈ (posetTraceCore S m geq2).ground := hIsub' hxI
    rcases Finset.mem_erase.mp (by change x ∈ S.ground.erase m.1; exact hIsub' hxI) with ⟨_, hxG⟩
    exact hxG

  -- S 側 ideal を作る
  have hIdealS : isOrderIdealOn (S.leOn) S.ground I := by
    dsimp [isOrderIdealOn]
    constructor
    · exact hIsubS
    · intro x hxI y hyG hleOn
      -- x ≠ m（I ⊆ erase m なので）
      have hx_ne_m : x ≠ m.1 := by
        have hx' : x ∈ (posetTraceCore S m geq2).ground := hIsub' hxI
        rcases Finset.mem_erase.mp (by change x ∈ S.ground.erase m.1; exact hIsub' hxI) with ⟨hxne, _⟩
        exact hxne
      -- 分岐：y = m / y ≠ m
      by_cases hy_eq : y = m.1
      · -- y = m の場合：`S.leOn y x` が成り立つと x=m に矛盾
        have hxG : x ∈ S.ground := hIsubS hxI
        have h_yx : S.le ⟨y, hyG⟩ ⟨x, hxG⟩ := (leOn_iff S hyG hxG).mp hleOn
        have hmx : S.le m ⟨x, hxG⟩ := by cases hy_eq; exact h_yx
        have hxm : S.le ⟨x, hxG⟩ m := hm hmx
        have : (⟨x, hxG⟩ : S.Elem) = m := by exact hpos (hm hmx) hmx
        have : x = m.1 := congrArg Subtype.val this
        have : False := hx_ne_m this
        exact this.elim
      · -- y ≠ m：S の ≤ を S' に持ち上げ、S' 側の下方閉で y ∈ I
        -- y, x はともに erase m 上
        have hyE : y ∈ S.ground.erase m.1 := by
          refine Finset.mem_erase.mpr ?_
          refine And.intro ?neq hyG
          intro h; exact hy_eq h
        have hxG : x ∈ S.ground := hIsubS hxI
        have hxE : x ∈ S.ground.erase m.1 := by
          refine Finset.mem_erase.mpr ?_
          refine And.intro hx_ne_m hxG
        -- S.leOn y x を S.le に戻す
        have hSle : S.le ⟨y, hyG⟩ ⟨x, hxG⟩ :=
          (leOn_iff S hyG hxG).mp hleOn
        -- 持ち上げ：`lift_le_to_traceCore_if_not_m_below`
        have hS'le :
            Relation.ReflTransGen (posetTraceCore S m geq2).cover
              ⟨y, hyE⟩ ⟨x, hxE⟩ :=
          lift_le_to_traceCore_if_not_m_below
            (S := S) (m := m) (hpos := hpos) (hmax := hm)
            (a := ⟨y, hyE⟩) (b := ⟨x, hxE⟩) (h := hSle)
        -- `leOn` に戻す
        have hy' : y ∈ (posetTraceCore S m geq2).ground := by
          change y ∈ S.ground.erase m.1; exact hyE
        have hx' : x ∈ (posetTraceCore S m geq2).ground := by
          change x ∈ S.ground.erase m.1; exact hxE
        have hleOn' :
            (posetTraceCore S m geq2).leOn y x :=
          (leOn_iff (posetTraceCore S m geq2) hy' hx').mpr hS'le
        -- S' 側 ideal の下方閉
        exact hI'.2 (x := x) hxI (y := y) hy' hleOn'

  -- `sets ↔ isOrderIdealOn` で戻す
  exact (S.sets_iff_isOrderIdeal (I := I)).2 hIdealS

/-- 「帰り」：`posetTraceCore` 側の ideal は S 側でも ideal、かつ `m ∉ I`。 -/
---使っている。
lemma back_sets_from_trace_at_max_sets'
  (S : FuncSetup α) [Fintype S.Elem]
  (hpos : isPoset S) {m : S.Elem}(geq2: S.ground.card ≥ 2) (hm : S.maximal m)
  {I : Finset α}
  (hI : ((posetTraceCore S m geq2).idealFamily).sets I) :
  (S.idealFamily).sets I ∧ m.1 ∉ I :=
by
  -- 先に sets へ戻す（既出補題）
  have hSets :
      (S.idealFamily).sets I :=
    back_sets_from_trace_at_max_sets (S := S) (hpos := hpos) (m := m) (hm := hm) (hI := hI)
  -- `m ∉ I` は台が `erase m` から
  have hI' :
      isOrderIdealOn ((posetTraceCore S m geq2).leOn) ((posetTraceCore S m geq2).ground) I := by
    change isOrderIdealOn _ _ I
    exact ((posetTraceCore S m geq2).sets_iff_isOrderIdeal (I := I)).1 hI
  have hSub' : I ⊆ (posetTraceCore S m geq2).ground := hI'.1
  have hm_not : m.1 ∉ I := by
    intro hmI
    have : m.1 ∈ (posetTraceCore S m geq2).ground := hSub' hmI
    rcases Finset.mem_erase.mp (by change m.1 ∈ S.ground.erase m.1; simpa) with ⟨heq, _⟩
    exact heq rfl
  exact And.intro hSets hm_not

--一般的な変形なのでGeneral.leanに移動してもよい。
lemma arith_reduce (V n t : Nat) (hV : 1 ≤ V) :
  ((V : Int)
    + (-(V : Int)
       + ( -((n : Int) * (V : Int))
           + ((t : Int) + (t : Int)) )))
  =
  ( -(n : Int)
    + ( -((n : Int) * (↑(V - 1)))
        + ((t : Int) + (t : Int)) ) ) := by
  classical
  -- ↑(V-1) を (V:ℤ) - 1 に直す
  have hCast : (↑(V - 1) : Int) = (V : Int) - 1 := (Nat.cast_sub hV)

  -- 左辺を簡約： (V) + (-(V) + X) = X
  have hL :
      (V : Int)
        + (-(V : Int)
            + ( -((n : Int) * (V : Int))
                + ((t : Int) + (t : Int)) ))
      =
      ( -((n : Int) * (V : Int))
        + ((t : Int) + (t : Int)) ) := by
    calc
      (V : Int) + (-(V : Int) + _)
          = ((V : Int) + (-(V : Int))) + _ := by
                rw [add_assoc]
      _   = 0 + _ := by
                -- a + (-a) = 0
                exact Eq.symm (Int.zero_add (↑V + -↑V + (-(↑n * ↑V) + (↑t + ↑t))))
      _   = _ := by
                rw [zero_add]
                simp_all only [Nat.cast_sub, Nat.cast_one, add_neg_cancel, zero_add]

  -- 右辺を簡約： -(n) + (-(n*(V-1)) + (t+t)) を展開して -(n*V) + (t+t) に
  have hR :
      ( -(n : Int)
        + ( -((n : Int) * (↑(V - 1)))
            + ((t : Int) + (t : Int)) ) )
      =
      ( -((n : Int) * (V : Int))
        + ((t : Int) + (t : Int)) ) := by
    -- まず ↑(V-1) を (V:ℤ)-1 に置換
    have := hCast
    -- `rw [this]` を段階的に適用
    calc
      -(n : Int) + ( -((n : Int) * (↑(V - 1)))
                      + ((t : Int) + (t : Int)) )
          = -(n : Int) + ( -((n : Int) * ((V : Int) - 1))
                            + ((t : Int) + (t : Int)) ) := by
                rw [this]
      _   = -(n : Int) + ( -(((n : Int) * (V : Int)) - (n : Int))
                            + ((t : Int) + (t : Int)) ) := by
                -- n*(V-1) = n*V - n
                -- `mul_sub` と `mul_one`
                have hmul :
                    (n : Int) * ((V : Int) - 1)
                      = (n : Int) * (V : Int) - (n : Int) := by
                  calc
                    (n : Int) * ((V : Int) - 1)
                        = (n : Int) * (V : Int) - (n : Int) * (1 : Int) := by
                              exact (mul_sub (n : Int) (V : Int) (1 : Int))
                    _   = (n : Int) * (V : Int) - (n : Int) := by
                              -- (n:ℤ)*1 = n
                              simp_all only [add_neg_cancel_left, Nat.cast_sub, Nat.cast_one, mul_one]

                -- LHS の `- (n * ((V:ℤ)-1))` を上の等式で書換
                -- `rw` のために一旦 `show` の形で与える
                -- 実際には `simp` でもよいが明示的に `rw` する
                have : -((n : Int) * ((V : Int) - 1))
                          = -(((n : Int) * (V : Int)) - (n : Int)) := by
                  -- 直前の hmul を使うだけ
                  exact congrArg Neg.neg hmul
                -- これを使って置換
                simp_all only [add_neg_cancel_left, Nat.cast_sub, Nat.cast_one, neg_sub]
      _   = -(n : Int) + ( (n : Int) - (n : Int) * (V : Int)
                            + ((t : Int) + (t : Int)) ) := by
                -- `-(A - B) = B - A`
                rw [Int.neg_sub ((n : Int) * (V : Int)) (n : Int)]
      _   = ( (-(n : Int) + (n : Int)) - (n : Int) * (V : Int)
              + ((t : Int) + (t : Int)) ) := by
                -- b - a = b + (-a)、結合で並べ替え
                -- まず外の `a + (b + c)` → `(a + b) + c`
                simp_all only [add_neg_cancel_left, Nat.cast_sub, Nat.cast_one, neg_add_cancel, zero_sub]
                omega
                -- ここまでで所望の並びに
      _   = ( -((n : Int) * (V : Int))
              + ((t : Int) + (t : Int)) ) := by
                -- `-(n) + n = 0`
                have : (-(n : Int)) + (n : Int) = 0 := by
                  exact Int.add_left_neg ↑n
                -- 0 + x = x
                calc
                  ( (-(n : Int) + (n : Int)) - (n : Int) * (V : Int)
                    + ((t : Int) + (t : Int)) )
                        = ( 0 - (n : Int) * (V : Int)
                            + ((t : Int) + (t : Int)) ) := by
                              rw [this]
                  _     = ( -((n : Int) * (V : Int))
                            + ((t : Int) + (t : Int)) ) := by
                              -- 0 - a = -a
                              simp [sub_eq_add_neg, add_comm, add_assoc]

  -- 左右を突き合わせて終了
  exact hL.trans hR.symm

--使っている
private lemma numHyperedges_trace_pred_of_max
  (S : SPO.FuncSetup α) [Fintype S.Elem]
  (m : S.Elem)(geq2: S.ground.card ≥ 2)
  (hOnlyTop :
    ∀ I : Finset α, isOrderIdealOn (S.leOn) S.ground I → m.1 ∈ I → I = S.ground)
  (hKeep :
    ∀ I : Finset α, isOrderIdealOn (S.leOn) S.ground I → m.1 ∉ I →
      ((posetTraceCore S m geq2).idealFamily).sets I)
  -- “帰り”：`posetTraceCore` 側 ideal ⇒ S 側 ideal ∧ `m∉I`
  (hBack :
    ∀ I : Finset α, ((posetTraceCore S m geq2).idealFamily).sets I →
      (S.idealFamily).sets I ∧ m.1 ∉ I) :
  ((posetTraceCore S m geq2).idealFamily).numHyperedges + 1
    = (S.idealFamily).numHyperedges := by
  classical
  -- 記号略
  set F  := S.idealFamily
  set F' := (posetTraceCore S m geq2).idealFamily

  -- F' の edge は F の「m を含まない」ものちょうど
  have hEdgeEq :
      F'.edgeFinset = F.edgeFinset.filter (fun A => m.1 ∉ A) :=
    edgeFinset_trace_eq_filter_not_mem (S := S) (m := m)
      (hKeep := hKeep) (hBack := hBack)

  -- F で「m を含む edge」は {ground} だけ
  have h_onlyTop_filter :
      (F.edgeFinset.filter (fun A => m.1 ∈ A)) = {S.ground} := by
    apply Finset.Subset.antisymm_iff.mpr; constructor
    · intro A hA
      have hA_edge : A ∈ F.edgeFinset := (Finset.mem_filter.mp hA).1
      have hmA    : m.1 ∈ A           := (Finset.mem_filter.mp hA).2
      have hA_ideal : isOrderIdealOn (S.leOn) S.ground A :=
        (S.sets_iff_isOrderIdeal (I := A)).1
          ((SetFamily.mem_edgeFinset_iff_sets (F := F) (A := A)).1 hA_edge)
      exact Finset.mem_singleton.mpr (hOnlyTop A hA_ideal hmA)
    · intro A hA
      have hAeq : A = S.ground := Finset.mem_singleton.mp hA
      have hGroundSets : F.sets S.ground :=
        (S.sets_iff_isOrderIdeal (I := S.ground)).2
          (by dsimp [isOrderIdealOn]; exact And.intro (by intro x hx; exact hx)
                (by intro x hx y hy _; exact hy))
      have hGroundEdge : S.ground ∈ F.edgeFinset :=
        (SetFamily.mem_edgeFinset_iff_sets (F := F) (A := S.ground)).2 hGroundSets
      have hmG : m.1 ∈ S.ground := m.2
      have h0 : S.ground ∈ F.edgeFinset.filter (fun A => m.1 ∈ A) :=
        Finset.mem_filter.mpr ⟨hGroundEdge, hmG⟩
      cases hAeq; exact h0

  -- カード分解
  have hSplit :
      (F.edgeFinset.filter (fun A => m.1 ∉ A)).card
        = F.edgeFinset.card - 1 := by
    have := Finset.filter_card_add_filter_neg_card_eq_card
               (s := F.edgeFinset) (p := fun A : Finset α => m.1 ∈ A)
    -- 左項のカードは単集合 → 1
    have hleft :
        (F.edgeFinset.filter (fun A => m.1 ∈ A)).card = 1 := by
      -- `card {ground} = 1`
      have : (F.edgeFinset.filter (fun A => m.1 ∈ A)) = {S.ground} := h_onlyTop_filter
      exact congrArg Finset.card this ▸ Finset.card_singleton _
    exact by
      -- b = card - a
      have := Nat.eq_sub_of_add_eq' (hleft ▸ this)
      exact this
  -- F' 側カード
  have hF' :
      F'.edgeFinset.card
        = (F.edgeFinset.filter (fun A => m.1 ∉ A)).card := by
    exact congrArg Finset.card hEdgeEq
  -- まとめ
  have : F'.edgeFinset.card = F.edgeFinset.card - 1 := by
    simpa [hF'] using hSplit
  -- numHyperedges に戻す
  dsimp [SetFamily.numHyperedges]
  simp [this]
  let nhg := FuncSetup.numHyperedges_ge_one S
  dsimp [SetFamily.numHyperedges] at nhg
  dsimp [F]
  exact Nat.sub_add_cancel nhg

/-- ② サイズ和：ちょうど `|V|` 減る（`isConnected` 不要版）。 -/
--使っている。
private lemma totalHyperedgeSize_trace_sub_card_ground_of_max
  (S : FuncSetup α) [Fintype S.Elem]
  (m : S.Elem)(geq2: S.ground.card ≥ 2)
  (hOnlyTop :
    ∀ I : Finset α, isOrderIdealOn (S.leOn) S.ground I → m.1 ∈ I → I = S.ground)
  (hKeep :
    ∀ I : Finset α, isOrderIdealOn (S.leOn) S.ground I → m.1 ∉ I →
      ((posetTraceCore S m geq2).idealFamily).sets I)
  (hBack :
    ∀ I : Finset α, ((posetTraceCore S m geq2).idealFamily).sets I →
      (S.idealFamily).sets I ∧ m.1 ∉ I) :
  (S.idealFamily).totalHyperedgeSize
    = ((posetTraceCore S m geq2).idealFamily).totalHyperedgeSize
      + S.ground.card := by
  classical
  -- 先に示した集合等式と「{ground} だけ落ちる」を用いて
  set F  := S.idealFamily
  set F' := (posetTraceCore S m geq2).idealFamily
  have hEdgeEq :
      F'.edgeFinset = F.edgeFinset.filter (fun A => m.1 ∉ A) :=
    edgeFinset_trace_eq_filter_not_mem
      (S := S) (m := m) (hKeep := hKeep) (hBack := hBack)
  have h_onlyTop_filter :
      (F.edgeFinset.filter (fun A => m.1 ∈ A)) = {S.ground} := by
    -- 同上
    apply Finset.Subset.antisymm_iff.mpr; constructor
    · intro A hA
      have hA_edge : A ∈ F.edgeFinset := (Finset.mem_filter.mp hA).1
      have hmA    : m.1 ∈ A           := (Finset.mem_filter.mp hA).2
      have hA_ideal : isOrderIdealOn (S.leOn) S.ground A :=
        (S.sets_iff_isOrderIdeal (I := A)).1
          ((SetFamily.mem_edgeFinset_iff_sets (F := F) (A := A)).1 hA_edge)
      exact Finset.mem_singleton.mpr (hOnlyTop A hA_ideal hmA)
    · intro A hA
      have hAeq : A = S.ground := Finset.mem_singleton.mp hA
      have hGroundSets : F.sets S.ground :=
        (S.sets_iff_isOrderIdeal (I := S.ground)).2
          (by dsimp [isOrderIdealOn]; exact And.intro (by intro x hx; exact hx)
                (by intro x hx y hy _; exact hy))
      have hGroundEdge : S.ground ∈ F.edgeFinset :=
        (SetFamily.mem_edgeFinset_iff_sets (F := F) (A := S.ground)).2 hGroundSets
      have hmG : m.1 ∈ S.ground := m.2
      have h0 : S.ground ∈ F.edgeFinset.filter (fun A => m.1 ∈ A) :=
        Finset.mem_filter.mpr ⟨hGroundEdge, hmG⟩
      cases hAeq; exact h0

  -- 分割して和を取る（`sum_union` と単集合の和 = `ground.card`）
  have hUnion : F'.edgeFinset ∪ {S.ground} = F.edgeFinset := by
    -- `hEdgeEq` と `h_onlyTop_filter` から同様に構築
    apply Finset.ext; intro A
    constructor
    · intro hA
      cases Finset.mem_union.mp hA with
      | inl h1 =>
          have : A ∈ F.edgeFinset.filter (fun B => m.1 ∉ B) := by
            simp_all only [ sets_iff_isOrderIdeal, posetTraceCore_ground,
              Finset.union_singleton, Finset.mem_insert, Finset.mem_filter, SetFamily.mem_edgeFinset, not_false_eq_true, and_self,
              F', F]
          exact Finset.mem_of_mem_filter A this
      | inr h0 =>
          have hAeq : A = S.ground := Finset.mem_singleton.mp h0
          have hGround : S.ground ∈ F.edgeFinset := by
            have hGroundSets : F.sets S.ground :=
              (S.sets_iff_isOrderIdeal (I := S.ground)).2
                (by dsimp [isOrderIdealOn]; exact And.intro (by intro x hx; exact hx)
                      (by intro x hx y hy _; exact hy))
            exact (SetFamily.mem_edgeFinset_iff_sets (F := F) (A := S.ground)).2 hGroundSets
          cases hAeq; exact hGround
    · intro hA
      by_cases hmA : m.1 ∈ A
      · -- ground 側
        have hA_sets : F.sets A := (SetFamily.mem_edgeFinset_iff_sets (F := F) (A := A)).1 hA
        have hA_ideal : isOrderIdealOn (S.leOn) S.ground A :=
          (S.sets_iff_isOrderIdeal (I := A)).1 hA_sets
        have hAeq : A = S.ground := hOnlyTop A hA_ideal hmA
        exact Finset.mem_union.mpr (Or.inr (by cases hAeq; exact Finset.mem_singleton_self _))
      · -- F' 側
        have hFilt : A ∈ F.edgeFinset.filter (fun B => m.1 ∉ B) :=
          Finset.mem_filter.mpr ⟨hA, hmA⟩
        have : A ∈ F'.edgeFinset := by
          simp_all only [sets_iff_isOrderIdeal, posetTraceCore_ground,
            SetFamily.mem_edgeFinset, Finset.mem_filter, not_false_eq_true, and_self, F', F]
        exact Finset.mem_union.mpr (Or.inl this)

  have hDisj : Disjoint F'.edgeFinset ({S.ground} : Finset (Finset α)) := by
    refine Finset.disjoint_left.mpr ?_
    intro A hA hA0
    have hAeq : A = S.ground := Finset.mem_singleton.mp hA0
    have hAsets' : F'.sets A :=
      (SetFamily.mem_edgeFinset_iff_sets (F := F') (A := A)).1 hA
    have hm_not : m.1 ∉ A := (hBack A hAsets').2
    have hmG : m.1 ∈ S.ground := m.2
    cases hAeq; exact (hm_not hmG).elim

  have hSumSplit :
      (∑ A ∈ F.edgeFinset, A.card)
        = (∑ A ∈ F'.edgeFinset, A.card)
          + (∑ A ∈ ({S.ground} : Finset (Finset α)), A.card) := by
    -- 台を union に書換えて `sum_union`
    have : (∑ A ∈ (F'.edgeFinset ∪ ({S.ground} : Finset (Finset α))), A.card)
            = (∑ A ∈ F'.edgeFinset, A.card)
              + (∑ A ∈ ({S.ground} : Finset (Finset α)), A.card) :=
      Finset.sum_union hDisj
    -- `hUnion` で台を置換
    simp_all only [ Finset.coe_mem, sets_iff_isOrderIdeal, posetTraceCore_ground,
      Finset.union_singleton, Finset.disjoint_singleton_right, Finset.mem_filter, SetFamily.mem_edgeFinset,
      not_true_eq_false, and_false, not_false_eq_true, Finset.sum_singleton,  F', F]

  have hSingleton :
      (∑ A ∈ ({S.ground} : Finset (Finset α)), A.card) = S.ground.card := by
    simp

  dsimp [SetFamily.totalHyperedgeSize]
  calc
    (∑ A ∈ F.edgeFinset, A.card)
        = (∑ A ∈ F'.edgeFinset, A.card)
          + (∑ A ∈ ({S.ground} : Finset (Finset α)), A.card) := hSumSplit
    _   = (∑ A ∈ F'.edgeFinset, A.card) + S.ground.card := by
            exact congrArg (fun n => (∑ A ∈ F'.edgeFinset, A.card) + n) hSingleton

/- ③ 台集合：ちょうど 1 減る -/
--外から参照していた。
lemma ground_card_after_trace_of_max
  (S : FuncSetup α) [Fintype S.Elem]
  (m : S.Elem)(geq2: S.ground.card ≥ 2) :
  ((posetTraceCore S m geq2).ground).card = S.ground.card - 1 := by
  classical
  have : (posetTraceCore S m geq2).ground = S.ground.erase m.1 := rfl
  have hm : m.1 ∈ S.ground := m.2
  have h := Finset.card_erase_add_one (s := S.ground) (a := m.1) hm
  exact Nat.eq_sub_of_add_eq h


/- ④ NDS の差の恒等式 -/
--仮定から条件を抜いた版で使用。
private lemma nds_diff_eq_root_delete_identity_of_max
  (S : FuncSetup α) [Fintype S.Elem]
  --(hpos : isPoset S)
  (m : S.Elem) (geq2: S.ground.card ≥ 2)
  -- 「m を含む ideal は ground」
  (hOnlyTop :
    ∀ I : Finset α, isOrderIdealOn (S.leOn) S.ground I → m.1 ∈ I → I = S.ground)
  -- 「m を含まない ideal は trace 後も残る」
  (hKeep :
    ∀ I : Finset α, isOrderIdealOn (S.leOn) S.ground I → m.1 ∉ I →
      ((posetTraceCore S m geq2).idealFamily).sets I)
  -- “帰り”：`posetTraceCore` 側 ideal ⇒ S 側 ideal ∧ `m∉I`
  (hBack :
    ∀ I : Finset α, ((posetTraceCore S m geq2).idealFamily).sets I →
      (S.idealFamily).sets I ∧ m.1 ∉ I) :
  let S' := posetTraceCore S m geq2
  (S.idealFamily).NDS
    = (S'.idealFamily).NDS
      + (S.ground.card - (S.idealFamily).numHyperedges + 1 : Int) := by
  classical
  intro S'
  -- 略記
  set F  := S.idealFamily
  set F' := S'.idealFamily
  -- ①②③ を適用
  have hNum : F'.numHyperedges + 1 = F.numHyperedges :=
    numHyperedges_trace_pred_of_max (S := S) (m := m)
      (hOnlyTop := hOnlyTop) (hKeep := hKeep) (hBack := hBack)
  have hSize :
    F.totalHyperedgeSize = F'.totalHyperedgeSize + S.ground.card :=
    totalHyperedgeSize_trace_sub_card_ground_of_max
      (S := S) (m := m) (geq2 := geq2) (hOnlyTop := hOnlyTop) (hKeep := hKeep) (hBack := hBack)
  have hV : S'.ground.card = S.ground.card - 1 :=
    ground_card_after_trace_of_max (S := S) (m := m) geq2

  -- 整数化と代入は以前と同じ
  have hNumZ :
      (F.numHyperedges : Int) = ((F'.numHyperedges + 1 : Nat) : Int) :=
    (congrArg (fun n : Nat => (n : Int)) hNum.symm)
  have hSizeZ :
      (F.totalHyperedgeSize : Int)
        = ((F'.totalHyperedgeSize + S.ground.card : Nat) : Int) :=
    (congrArg (fun n : Nat => (n : Int)) hSize)
  have hVZ :
      (F'.ground.card : Int) = ((S.ground.card - 1 : Nat) : Int) :=
    (congrArg (fun n : Nat => (n : Int)) hV)

  -- 左辺の整理（算術補題を利用）
  have hCalc :
      F.NDS
        = (2 * (F'.totalHyperedgeSize : Int)
              - (F'.numHyperedges : Int) * ((S.ground.card - 1 : Nat) : Int))
          + ((S.ground.card : Int) - (F'.numHyperedges : Int)) := by
    dsimp [SetFamily.NDS]
    rw [hSizeZ, hNumZ]
    have hCastAdd₁ :
        ((F'.totalHyperedgeSize + S.ground.card : Nat) : Int)
          = (F'.totalHyperedgeSize : Int) + (S.ground.card : Int) :=
      (Nat.cast_add _ _)
    have hCastAdd₂ :
        ((F'.numHyperedges + 1 : Nat) : Int)
          = (F'.numHyperedges : Int) + 1 :=
      (Nat.cast_add _ _)
    simp [mul_add, add_mul, two_mul, add_comm, add_left_comm,
          add_assoc, sub_eq_add_neg]
    -- `↑(V-1)` を `(V:ℤ)-1` に直して等式形を合わせる
    have hVpos : 1 ≤ S.ground.card :=
      Nat.succ_le_of_lt (Finset.card_pos.mpr ⟨m.1, m.2⟩)
    exact arith_reduce (V := S.ground.card) (n := F'.numHyperedges)
                       (t := F'.totalHyperedgeSize) (hV := hVpos)

  -- 右辺も同様に形合わせ
  have hRight :
      F'.NDS + (S.ground.card - F.numHyperedges + 1 : Int)
        = (2 * (F'.totalHyperedgeSize : Int)
              - (F'.numHyperedges : Int) * ((S.ground.card - 1 : Nat) : Int))
          + ((S.ground.card : Int) - (F'.numHyperedges : Int)) := by
    dsimp [SetFamily.NDS]
    rw [hVZ]
    have hNatRew :
        (S.ground.card - F.numHyperedges + 1 : Int)
          = (S.ground.card - (F'.numHyperedges + 1) + 1 : Int) := by
      have hNat :
          S.ground.card - F.numHyperedges + 1
            = S.ground.card - (F'.numHyperedges + 1) + 1 :=
        (congrArg (fun n : Nat => S.ground.card - n + 1) hNum.symm)
      norm_cast
      simp_all only [ Finset.coe_mem, sets_iff_isOrderIdeal, posetTraceCore_ground,
        Finset.card_erase_of_mem, Nat.cast_add, Nat.cast_inj, SetFamily.NDS_def, F', S', F]

    have hToZ :
        (S.ground.card - (F'.numHyperedges + 1) + 1 : Int)
          = (S.ground.card : Int) - (F'.numHyperedges : Int) := by
      simp [sub_eq_add_neg, add_comm, add_left_comm]
    rw [hNatRew, hToZ]

  exact hCalc.trans hRight.symm

/-- NDS 差の恒等式（唯一極大元版：`hOnlyTop` と `hKeep` は不要）。 -/
private theorem nds_diff_eq_root_delete_identity_uniqueMax
  (S : FuncSetup α) [Fintype S.Elem] (geq2: S.ground.card ≥ 2)
  (hpos : isPoset S) (hexu : ∃! m : S.Elem, S.maximal m) :
  let S' := posetTraceOfUnique S geq2 hexu
  (S.idealFamily).NDS
    = (S'.idealFamily).NDS
      + (S.ground.card - (S.idealFamily).numHyperedges + 1 : Int) := by
  classical
  intro S'
  -- m とその極大性
  set m : S.Elem := Classical.choose hexu.exists
  have hm : S.maximal m := Classical.choose_spec hexu.exists

  -- 「m を含む ideal は ground」
  have hOnlyTop :
    ∀ I : Finset α, isOrderIdealOn (S.leOn) S.ground I → m.1 ∈ I → I = S.ground :=
    fun I hI hmI =>
      hOnlyTop_of_uniqueMax (S := S) (hpos := hpos) (hexu := hexu) (hI := hI) (hmI := hmI)

  -- 「m を含まない ideal は trace 後も ideal」（一般補題）
  have hKeep :
    ∀ I : Finset α, isOrderIdealOn (S.leOn) S.ground I → m.1 ∉ I →
      ((posetTraceCore S m geq2).idealFamily).sets I :=
    fun I hI hnot =>
      keep_sets_from_trace_at_without_m (S := S) (m := m) (geq2 := geq2) (hI := hI) (hmI := hnot)

  -- “帰り”：core 側 ideal ⇒ S 側 ideal ∧ `m∉I`（既証）
  have hBack :
    ∀ I : Finset α, ((posetTraceCore S m geq2).idealFamily).sets I →
      (S.idealFamily).sets I ∧ m.1 ∉ I :=
    fun I hI' =>
      back_sets_from_trace_at_max_sets' (S := S) (hpos := hpos) (m := m) (hm := hm) (hI := hI')

  -- すでに通っている of_max 版で締める
  have base :=
    nds_diff_eq_root_delete_identity_of_max
      (S := S) (m := m) (geq2 := geq2)
      (hOnlyTop := hOnlyTop) (hKeep := hKeep) (hBack := hBack)

  -- `posetTraceOfUnique S hexu = posetTraceCore S m` を反映
  dsimp [posetTraceOfUnique, m] at base
  exact base

/-- （唯一極大での trace は NDS を減らさない） -/
--そとから使われている。
lemma nds_trace_nondecreasing_uniqueMax
  (S : FuncSetup α) [Fintype S.Elem] (geq2 : S.ground.card ≥ 2)
  (hpos : isPoset S) (hexu : ∃! m : S.Elem, S.maximal m) :
  let S' := posetTraceOfUnique S geq2 hexu
  (S.idealFamily).NDS ≤ (S'.idealFamily).NDS := by
  classical
  intro S'
  -- 記号
  set F  := S.idealFamily
  set F' := S'.idealFamily

  -- 恒等式：NDS(S) = NDS(S') + (|V| - num(S) + 1)
  have hEq :
      F.NDS = F'.NDS + (S.ground.card - F.numHyperedges + 1 : Int) :=
    nds_diff_eq_root_delete_identity_uniqueMax
      (S := S) (geq2 := geq2) (hpos := hpos) (hexu := hexu)

  -- 既証の下界：num(S) ≥ |V| + 1
  have hLower : F.numHyperedges ≥ S.ground.card + 1 :=
    ideals_card_ge_ground_card_succ (S := S) (hpos := hpos)

  -- 自然数の不等式から、括弧が ≤ 0 を導く
  have hNat : S.ground.card + 1 ≤ F.numHyperedges := by exact hLower
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hNat
  have hkZ : (F.numHyperedges : Int) =
             ((S.ground.card + 1 + k : Nat) : Int) :=
    congrArg (fun n : Nat => (n : Int)) hk

  have hTerm_nonpos :
      (S.ground.card : Int) - (F.numHyperedges : Int) + 1 ≤ 0 := by
    -- num = (|V|+1)+k に書換えて計算すると −k
    calc
      (S.ground.card : Int) - (F.numHyperedges : Int) + 1
          = (S.ground.card : Int)
              - ((S.ground.card + 1 + k : Nat) : Int) + 1 := by
                rw [hkZ]
      _   = (S.ground.card : Int)
              - (((S.ground.card + 1 : Nat) : Int) + (k : Int)) + 1 := by
                -- ((a+1+k) : ℤ) = ((a+1) : ℤ) + k
                exact congrArg (fun t => (S.ground.card : Int) - t + 1)
                               (Nat.cast_add (S.ground.card + 1) k)
      _   = (S.ground.card : Int)
              - ((S.ground.card : Int) + 1 + (k : Int)) + 1 := by
                -- ((a+1) : ℤ) = (a : ℤ) + 1
                exact congrArg (fun t => (S.ground.card : Int) - (t + (k : Int)) + 1)
                               (Nat.cast_add (S.ground.card) 1)
      _   = - (k : Int) := by
                -- 整数の四則で整理
                simp [sub_eq_add_neg, add_comm, add_left_comm]
    -- −k ≤ 0
    have hk_nonneg : 0 ≤ (k : Int) := Int.natCast_nonneg k
    exact neg_nonpos.mpr hk_nonneg

  -- 恒等式＋括弧 ≤ 0 から NDS(S) ≤ NDS(S')
  -- まず RHS を上から抑える
  have hStep :
      F'.NDS + ((S.ground.card : Int) - (F.numHyperedges : Int) + 1)
        ≤ F'.NDS := by
    have := add_le_add_left hTerm_nonpos (F'.NDS)
    -- 右側の `+ 0` を落とす
    -- （`simp` は `simpa` ではありません）
    simpa using this

  -- 左辺を恒等式で置換
  have : F.NDS ≤ F'.NDS := by
    -- `F.NDS = ...` に書換えて `hStep` を適用
    -- `cases` で等式を置換
    have h := hEq
    simp_all only [SetFamily.NDS_def, ge_iff_le, Nat.cast_add, Nat.cast_one, add_le_iff_nonpos_right, F, F', S']

  exact this


end Induction
end AvgRare

/-


/-- 6) NDS の差分恒等式。 -/
--isCOnnected仮定版。isConnectedの代わりに極大元が1つの仮定の補題が安定すれば、将来的には消してもいいかも。
lemma nds_diff_eq_root_delete_identity
  (S : FuncSetup α) [Fintype S.Elem]
  (hpos : isPoset S) (hconn : isConnected S) (hne : S.ground.Nonempty)
  (hOnlyTop :
    ∀ I : Finset α, isOrderIdealOn (S.leOn) S.ground I → (theMaxElem S hpos hconn hne).1 ∈ I → I = S.ground)
  (hKeep :
    ∀ I : Finset α, isOrderIdealOn (S.leOn) S.ground I →
      (theMaxElem S hpos hconn hne).1 ∉ I →
      ((posetTraceCore S (theMaxElem S hpos hconn hne)).idealFamily).sets I) :
  let S' := (posetTraceCore S (theMaxElem S hpos hconn hne))
  (S.idealFamily).NDS
    = (S'.idealFamily).NDS
      + (S.ground.card - (S.idealFamily).numHyperedges + 1 : Int) := by
classical
  intro S'
  -- 略記
  set F  := S.idealFamily
  set F' := S'.idealFamily

  -- 既証の 3 本
  have hNum : F'.numHyperedges + 1 = F.numHyperedges :=
    numHyperedges_trace_pred (S := S) (hpos := hpos) (hconn := hconn)
      (hne := hne) (hOnlyTop := hOnlyTop) (hKeep := hKeep)
  have hSize :
    F.totalHyperedgeSize = F'.totalHyperedgeSize + S.ground.card :=
    totalHyperedgeSize_trace_sub_card_ground
      (S := S) (hpos := hpos) (hconn := hconn) (hne := hne)
      (hOnlyTop := hOnlyTop) (hKeep := hKeep)
  have hV   :
    S'.ground.card = S.ground.card - 1 :=
    ground_card_after_trace (S := S) (hpos := hpos) (hconn := hconn) (hne := hne)

  -- `Nat → Int` に持ち上げておく（書換え用）
  have hNumZ :
      (F.numHyperedges : Int) = ((F'.numHyperedges + 1 : Nat) : Int) :=
    (congrArg (fun n : Nat => (n : Int)) hNum.symm)
  have hSizeZ :
      (F.totalHyperedgeSize : Int)
        = ((F'.totalHyperedgeSize + S.ground.card : Nat) : Int) :=
    (congrArg (fun n : Nat => (n : Int)) hSize)
  have hVZ :
      (F'.ground.card : Int) = ((S.ground.card - 1 : Nat) : Int) :=
    (congrArg (fun n : Nat => (n : Int)) hV)

  -- 左辺 NDS を 3 本で置換して展開
  -- NDS = 2 * total - num * |V|
  -- total = total' + |V|,  num = num' + 1,  |V'| = |V| - 1
  have hCalc :
      F.NDS
        = (2 * (F'.totalHyperedgeSize : Int)
              - (F'.numHyperedges : Int) * ((S.ground.card - 1 : Nat) : Int))
          + ((S.ground.card : Int) - (F'.numHyperedges : Int)) := by
    -- 展開して整理：整数の四則
    dsimp [SetFamily.NDS]
    -- total, num を書換え（num は `← hNumZ` で右を左に）
    rw [hSizeZ,  hNumZ]
    -- `((a+b : ℕ) : ℤ) = (a : ℤ) + (b : ℤ)`、`((c+1 : ℕ) : ℤ) = (c : ℤ) + 1`
    -- を使って分配し、まとめる
    -- また、|V'| = |V| - 1 も後で使うため保持
    have hCastAdd₁ :
        ((F'.totalHyperedgeSize + S.ground.card : Nat) : Int)
          = (F'.totalHyperedgeSize : Int) + (S.ground.card : Int) :=
      by exact (Nat.cast_add _ _)
    have hCastAdd₂ :
        ((F'.numHyperedges + 1 : Nat) : Int)
          = (F'.numHyperedges : Int) + 1 :=
      by exact (Nat.cast_add _ _)
    -- これで左辺を「(2t' - n'(|V|-1)) + (|V| - n')」の形まで整理
    -- 計算自体は `simp` と分配律で閉じます
    simp [mul_add, add_mul, two_mul, add_comm, add_left_comm,
          add_assoc, sub_eq_add_neg]
    exact arith_reduce (V := S.ground.card) (n := F'.numHyperedges) (t := F'.totalHyperedgeSize) (hV := Nat.succ_le_of_lt (Finset.card_pos.mpr hne))

  -- 右辺も NDS をほどいて、先の形に一致させる
  have hRight :
      F'.NDS + (S.ground.card - F.numHyperedges + 1 : Int)
        = (2 * (F'.totalHyperedgeSize : Int)
              - (F'.numHyperedges : Int) * ((S.ground.card - 1 : Nat) : Int))
          + ((S.ground.card : Int) - (F'.numHyperedges : Int)) := by
    -- NDS(F') をほどく
    dsimp [SetFamily.NDS]
    -- |V'| を |V|-1 に
    rw [hVZ]
    -- 後ろの「+ …」は `hNum` で `F.num = F'.num + 1` に書換える
    have hNatRew :
        (S.ground.card - F.numHyperedges + 1 : Int)
          = (S.ground.card - (F'.numHyperedges + 1) + 1 : Int) := by
      have hNat :
          S.ground.card - F.numHyperedges + 1
            = S.ground.card - (F'.numHyperedges + 1) + 1 :=
        (congrArg (fun n : Nat => S.ground.card - n + 1) hNum.symm)
      let ca := (congrArg (fun n : Nat => (n : Int)) hNat)
      --show ↑S.ground.card - ↑F.numHyperedges + 1 = ↑S.ground.card - (↑F'.numHyperedges + 1) + 1
      simp
      exact hNumZ

    -- さらに自然数式を整数式に直す：
    -- `a - (b+1) + 1` は整数では `a - b`
    have hToZ :
        (S.ground.card - (F'.numHyperedges + 1) + 1 : Int)
          = (S.ground.card : Int) - (F'.numHyperedges : Int) := by
      -- 整数上の恒等式として成立（展開して約分）
      -- `ring` 相当の整理（Nat→Int はすでに外側で終えている）
      simp [sub_eq_add_neg, add_comm, add_left_comm]
    -- 以上を代入して完成
    rw [hNatRew, hToZ]

  -- 2 つを突き合わせてゴール
  -- 左辺 = 中間式 = 右辺
  exact hCalc.trans hRight.symm

-/
