import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Logic.Relation
import Mathlib.Tactic.Ring
import AvgRare.Basics.SetFamily
import AvgRare.SPO.FuncSetup

universe u
namespace AvgRare
namespace DirectProduct
open Classical
variable {α : Type u} [DecidableEq α]
open AvgRare
open SPO
open FuncSetup

/-- `coIdeal m := ground \ principalIdeal m` -/
noncomputable def coIdeal (S : SPO.FuncSetup α)(m : S.Elem) : Finset α :=
  S.ground \ S.principalIdeal m.1 m.2

/-- `coIdeal m` の定義からの即物的な会員判定 -/
lemma mem_coIdeal_iff (S : SPO.FuncSetup α)
  {m : S.Elem} {y : α} :
  y ∈ coIdeal S m ↔ y ∈ S.ground ∧ y ∉ S.principalIdeal m.1 m.2 := by
  classical
  unfold coIdeal
  exact Finset.mem_sdiff

lemma exists_first_step_or_refl (S : SPO.FuncSetup α)
  {x m : S.Elem} :
  S.le x m → x = m ∨ ∃ z : S.Elem, S.cover x z ∧ S.le z m := by
  intro hxm
  induction hxm with
  | @refl  =>
      exact Or.inl rfl
  | @tail b c hxb hbc ih =>
      -- `x ≤ c` を得る段階。`ih` は `x = b ∨ ∃ z, x ⋖ z ∧ z ≤ b`
      cases ih with
      | inl hxb_eq =>
          -- `x = b` なので `x ⋖ c` が最初の一歩。`c ≤ c` は refl
          cases hxb_eq
          exact Or.inr ⟨c, hbc, Relation.ReflTransGen.refl⟩
      | inr h =>
          rcases h with ⟨z, hxz, hzb⟩
          -- `z ≤ b` と `b ⋖ c` から `z ≤ c`
          exact Or.inr ⟨z, hxz, Relation.ReflTransGen.tail hzb hbc⟩

/-! ### 3) principal ideal の「前進閉性」（極大点に対して） -/

private lemma cover_preserves_principalIdeal_of_maximal (S : SPO.FuncSetup α)
  --(hpos : isPoset S)
  {m x y : S.Elem}
  (hm : S.maximal m)
  (hx : x.1 ∈ S.principalIdeal m.1 m.2)
  (hxy : S.cover x y) :
  y.1 ∈ S.principalIdeal m.1 m.2 := by
  classical
  -- `x ≤ m` を取り出す
  have ⟨hxG, hxm⟩ :=
    (S.mem_principalIdeal_iff (a := m.1) (y := x.1) (ha := m.2)).1 hx
  -- 「refl か最初の一歩あり」で分岐
  have := exists_first_step_or_refl S (x := x) (m := m) hxm
  cases this with
  | inl hx_eq =>
      -- `x = m` の場合。`m ⋖ y` なら `m ≤ y`。極大性から `y ≤ m`。
      -- よって `y ∈ ↓m`。
      cases hx_eq
      have hmle : S.le m y := Relation.ReflTransGen.single hxy
      have hyle : S.le y m := hm hmle
      exact
        (S.mem_principalIdeal_iff (a := m.1) (y := y.1) (ha := m.2)).2
          ⟨y.2, hyle⟩
  | inr h =>
      -- `∃ z, x ⋖ z ∧ z ≤ m`。関数性から `z = y`。
      rcases h with ⟨z, hxz, hzm⟩
      -- cover は `S.f x = _` の等式なので像の一意性で一致
      have : z = y := by
        dsimp [FuncSetup.cover] at hxz hxy
        exact Eq.trans (Eq.symm hxz) hxy
      cases this
      exact
        (S.mem_principalIdeal_iff (a := m.1) (y := y.1) (ha := m.2)).2
          ⟨y.2, hzm⟩

/-! ### 4) coIdeal の前進閉性と，`≤` による拡張 -/

/-- `coIdeal` は 1 歩先で保たれる：`x ∈ coIdeal m` かつ `x ⋖ y` ⇒ `y ∈ coIdeal m`. -/
private lemma cover_preserves_coIdeal  (S : SPO.FuncSetup α)
  {m x y : S.Elem}
  (hx : x.1 ∈ coIdeal S m) (hxy : S.cover x y) :
  y.1 ∈ coIdeal S m := by
  classical
  -- もし `y` が principalIdeal に入っていたら，`x ≤ y` と合わせて `x` も入ってしまう
  have hxy_le : S.le x y := Relation.ReflTransGen.single hxy
  have : y.1 ∉ S.principalIdeal m.1 m.2 := by
    intro hy
    have ⟨hyG, hyle⟩ :=
      (S.mem_principalIdeal_iff (a := m.1) (y := y.1) (ha := m.2)).1 hy
    -- 伝播で `x ≤ m`
    have : S.le x ⟨m.1, m.2⟩ := hxy_le.trans hyle
    -- したがって `x` は principalIdeal に入る
    have hx_in :
      x.1 ∈ S.principalIdeal m.1 m.2 :=
      (S.mem_principalIdeal_iff (a := m.1) (y := x.1) (ha := m.2)).2 ⟨x.2, this⟩
    -- しかし `x ∈ coIdeal`
    have := (mem_coIdeal_iff S (m := m) (y := x.1)).1 hx
    exact this.2 hx_in
  -- ground 所属は cover から自明
  have hyG : y.1 ∈ S.ground := y.2
  exact (mem_coIdeal_iff S (m := m) (y := y.1)).2 ⟨hyG, this⟩

private lemma le_preserves_coIdeal (S : SPO.FuncSetup α)
  {m x y : S.Elem} (hx : x.1 ∈ coIdeal S m) (hxy : S.le x y) :
  y.1 ∈ coIdeal S m := by
  classical
  -- `ReflTransGen` で素直に帰納
  induction hxy with
  | @refl =>
      -- 基底：そのまま
      exact hx
  | @tail b c hxbc hbc ih =>
      -- 帰納仮定 `ih : b ∈ coIdeal m` と 1 歩 `b ⋖ c` から `c ∈ coIdeal m`
      exact cover_preserves_coIdeal S (m := m) (x := b) (y := c) ih hbc

/-! ### 5) principal ideal の `≤` による前進閉性（極大点に対して） -/

/-- `m` 極大のとき，`x ∈ ↓m` かつ `x ≤ y` なら `y ∈ ↓m`. -/
private lemma le_preserves_principalIdeal_of_maximal (S : SPO.FuncSetup α)
  --(hpos : isPoset S)
  {m x y : S.Elem}
  (hm : S.maximal m)
  (hx : x.1 ∈ S.principalIdeal m.1 m.2)
  (hxy : S.le x y) :
  y.1 ∈ S.principalIdeal m.1 m.2 := by
  classical
  induction hxy with
  --refine Relation.ReflTransGen.head_induction_on hxy ?base ?step
  | @refl =>
    simp_all only [maximal_iff, le_iff_leOn_val, Subtype.forall]
  | @tail z hxz hzy ih =>
    apply cover_preserves_principalIdeal_of_maximal S (m := m) (x := z) hm
    (expose_names; exact a_ih)
    exact ih

/-! ## 存在：各 `x` の上に極大元がある -/

/-- `upSet y := { t ∈ ground | y ≤ t }`（`S.Elem` 版） -/
noncomputable def upSet (S : SPO.FuncSetup α)
 (y : S.Elem) : Finset S.Elem :=
  (S.ground.attach).filter (fun t => S.le y t)

/-- `U := { t | x ≤ t }` は非空（`x ∈ U`）。 -/
lemma mem_U_of_x (S : SPO.FuncSetup α) (x : S.Elem) :
  x ∈ (S.ground.attach).filter (fun t => S.le x t) := by
  refine Finset.mem_filter.mpr ?_
  exact ⟨by simp, Relation.ReflTransGen.refl⟩

/-- 各 `x` の上に極大元が存在。 -/
lemma exists_maximal_above (S : SPO.FuncSetup α)
  [Fintype S.Elem] --(hpos : isPoset S)
  (x : S.Elem) :
  ∃ m : S.Elem, S.maximal m ∧ S.le x m := by
  classical
  -- U := {t | x ≤ t}
  let U : Finset S.Elem := (S.ground.attach).filter (fun t => S.le x t)
  have hUne : U.Nonempty := ⟨x, mem_U_of_x S x⟩

  -- μ(y) := #(upSet y)
  let μ : S.Elem → Nat := fun y => (upSet S y).card

  -- U 上で μ を最小にする m を取る
  obtain ⟨m, hmU, hmin⟩ := Finset.exists_min_image U μ hUne
  have hxm : S.le x m := (Finset.mem_filter.mp hmU).2

  -- m が極大であることを示す
  have hm : S.maximal m := by
    intro y hmy
    -- y も U に入る（x ≤ m ≤ y）
    have hyU : y ∈ U := by
      refine Finset.mem_filter.mpr ?_
      exact ⟨by simp, Relation.ReflTransGen.trans hxm hmy⟩

    -- `upSet y ⊆ upSet m`：y ≤ w なら m ≤ w（m ≤ y からの推移）
    have hsubset : upSet S y ⊆ upSet S m := by
      intro w hw
      have hyw : S.le y w := (Finset.mem_filter.mp hw).2
      have hmw : S.le m w := Relation.ReflTransGen.trans hmy hyw
      exact Finset.mem_filter.mpr ⟨by simp, hmw⟩

    -- 反対仮定：y ≤ m が成り立たないと仮定すると，m ∈ upSet m \ upSet y で真包含が出る
    by_contra hnot
    have hm_in : m ∈ upSet S m :=
      Finset.mem_filter.mpr ⟨by simp, Relation.ReflTransGen.refl⟩
    have hm_notin : m ∉ upSet S y := by
      intro hmem
      -- hmem から y ≤ m が出るので矛盾
      exact hnot ((Finset.mem_filter.mp hmem).2)
    have hne : upSet S y ≠ upSet S m := by
      intro hEq
      have : m ∈ upSet S y := by
        -- 等式で移送
        have := hm_in
        -- `rw [hEq]` を避け、`hEq ▸ hm_in` で十分
        exact hEq ▸ this
      exact hm_notin this
    have hss : upSet S y ⊂ upSet S m := by
      exact HasSubset.Subset.ssubset_of_not_subset hsubset fun a => hm_notin (a hm_in)

    -- カードの真不等式と最小性が矛盾
    have hlt : (upSet S y).card < (upSet S m).card := by exact Finset.card_lt_card hss
    have hle : (upSet S m).card ≤ (upSet S y).card := hmin y hyU
    have : (upSet S y).card < (upSet S y).card := Nat.lt_of_lt_of_le hlt hle
    exact (lt_irrefl _ ) this

  exact ⟨m, hm, hxm⟩

/-! ### 6) 2 つの極大があるとき：coIdeal の非空 & 可比性の否定 -/

/-- 2 つ目の極大 `m'` があれば，`coIdeal m` は非空（`m'` 自身が入る）。 -/
--仮定を(notconnected: ¬ (∃! mm: S.Elem, S.maximal mm))に変えてみる。
lemma coIdeal_nonempty_of_two_maximal (S : SPO.FuncSetup α)
  (hpos : isPoset S)
  {m m' : S.Elem} (hm' : S.maximal m') (hne : m ≠ m') :
  (coIdeal S m).Nonempty := by
  classical
  -- もし `m' ∈ principalIdeal m` なら `m' ≤ m` を得る
  -- 極大性から `m ≤ m'`，反対称性で `m = m'`，矛盾
  have hnot :
    m'.1 ∉ S.principalIdeal m.1 m.2 := by
    intro hmem
    have ⟨hmG, hm'le⟩ :=
      (S.mem_principalIdeal_iff (a := m.1) (y := m'.1) (ha := m.2)).1 hmem
    have hmle' : S.le m m' := hm' hm'le
    have : m = m' := by exact hpos (hm' hm'le) hm'le
    exact hne this
  -- よって `m' ∈ coIdeal m`
  have hm'G : m'.1 ∈ S.ground := m'.2
  have : m'.1 ∈ coIdeal S m :=
    (mem_coIdeal_iff S (m := m) (y := m'.1)).2 ⟨hm'G, hnot⟩
  exact ⟨m'.1, this⟩

lemma coIdeal_nonempty_of_not_unique_maximal
  (S : SPO.FuncSetup α) [Fintype S.Elem]
  (hpos : isPoset S)
  (notuniq : ¬ (∃! mm : S.Elem, S.maximal mm))
  (m : S.Elem) :
  (coIdeal S m).Nonempty := by
  classical
  -- 極大元をひとつ確保
  obtain ⟨m0, hm0, _hx⟩ := exists_maximal_above S m
  -- 「一意でない」から、m0 と異なる極大 m1 を得る
  have htwo : ∃ m1 : S.Elem, S.maximal m1 ∧ m1 ≠ m0 := by
    by_contra hnone
    -- すると「全ての極大は m0 に等しい」ので一意に矛盾
    have huniq : ∃! mm : S.Elem, S.maximal mm := by
      refine ⟨m0, hm0, ?_⟩
      intro mm hmm
      -- mm ≠ m0 なら直ちに反例
      by_contra hneq
      exact hnone ⟨mm, hmm, hneq⟩
    exact notuniq huniq
  rcases htwo with ⟨m1, hm1, hne10⟩

  -- m と異なる極大を選ぶ
  let mp : S.Elem := if h : m = m0 then m1 else m0

  have hmp_max : S.maximal mp := by
    by_cases h : m = m0
    · have : mp = m1 := by simp [mp, h]
      simp_all only [maximal_iff, le_iff_leOn_val, Subtype.forall, Finset.coe_mem, ne_eq, dite_eq_ite, ↓reduceIte,
        implies_true, mp]

    · have : mp = m0 := by simp [mp, h]
      simp_all only [maximal_iff, le_iff_leOn_val, Subtype.forall, Finset.coe_mem, ne_eq, dite_eq_ite, ↓reduceIte,
    implies_true, mp]

  have hne_m_mp : m ≠ mp := by
    by_cases h : m = m0
    · have hem : mp = m1 := by simp [mp, h]
      -- m ≠ m1（m = m0 かつ m = m1 なら m0 = m1 に矛盾）
      have hneq : m ≠ m1 := by
        intro heq
        have : m0 = m1 := Eq.trans (Eq.symm h) heq
        apply hne10
        exact id (Eq.symm this)
      -- これより m ≠ mp
      intro heq
      have : m = m1 := Eq.trans heq hem
      exact hneq this
    · have hem : mp = m0 := by simp [mp, h]
      intro heq
      have : m = m0 := Eq.trans heq hem
      exact h this

  -- 既存補題で結論
  exact coIdeal_nonempty_of_two_maximal S hpos
    (m := m) (m' := mp) hmp_max hne_m_mp

/-- `x ∈ ↓m` と `y ∈ coIdeal m` のとき，`x` と `y` は比較不能。 -/
private lemma no_comparable_across_split (S : SPO.FuncSetup α)
  --(hpos : isPoset S)
  {m x y : S.Elem}
  (hm : S.maximal m)
  (hx : x.1 ∈ S.principalIdeal m.1 m.2)
  (hy : y.1 ∈ coIdeal S m) :
  ¬ S.le x y ∧ ¬ S.le y x := by
  classical
  -- もし `x ≤ y` なら，principal ideal の前進閉性により `y ∈ ↓m`，
  -- しかし `y ∈ coIdeal m` と矛盾
  have h₁ : ¬ S.le x y := by
    intro hxy
    have yin : y.1 ∈ S.principalIdeal m.1 m.2 :=
      le_preserves_principalIdeal_of_maximal S  (m := m)
        (x := x) (y := y) hm hx hxy
    have : y.1 ∈ S.ground ∧ y.1 ∉ S.principalIdeal m.1 m.2 :=
      (mem_coIdeal_iff S (m := m) (y := y.1)).1 hy
    exact this.2 yin
  -- もし `y ≤ x` なら，coIdeal の前進閉性より `x ∈ coIdeal m`，
  -- しかし `x ∈ ↓m` と矛盾
  have h₂ : ¬ S.le y x := by
    intro hyx
    have xin : x.1 ∈ coIdeal S m :=
      le_preserves_coIdeal S (m := m) (x := y) (y := x) hy hyx
    -- `x ∈ principalIdeal` と矛盾
    have : x.1 ∈ S.ground ∧ x.1 ∉ S.principalIdeal m.1 m.2 :=
      (mem_coIdeal_iff S (m := m) (y := x.1)).1 xin
    exact this.2 hx
  exact ⟨h₁, h₂⟩

/-! ### 7) principal ideal / coIdeal への FuncSetup の制限 -/

/-- principal ideal への制限（`m` は極大と仮定）。 -/
--FuncSetup+isPosetの定義
--極大要素が唯一でないと仮定する。
noncomputable def restrictToIdeal (S : SPO.FuncSetup α)
  --(hpos : isPoset S)
  (m : S.Elem) (hm : S.maximal m): FuncSetup α := by
  classical
  refine
    { ground := S.principalIdeal m.1 m.2
      nonempty := by
        have : m.1 ∈ S.principalIdeal m.1 m.2 := by
          exact self_mem_principalIdeal S m
        simp_all only [maximal_iff, le_iff_leOn_val, Subtype.forall, nonempty_subtype]
        obtain ⟨val, property⟩ := m
        simp_all only
        exact ⟨_, this⟩
      , f := ?f }
  -- `f` が内部に閉じることを示す
  intro x
  -- `x : {a // a ∈ principalIdeal m}` を S.Elem に戻す
  let xg : S.Elem := ⟨x.1, (principalIdeal_subset_ground S ⟨m.1,m.2⟩) x.2⟩
  -- 次の 1 歩
  let y : S.Elem := S.f xg
  have : y.1 ∈ S.principalIdeal m.1 m.2 :=
    cover_preserves_principalIdeal_of_maximal S
      (m := m) (x := xg) (y := y) hm
      (by
        -- `xg` の中身は `x` の取り出し
        -- `x.2 : x.1 ∈ principalIdeal`
        exact x.2)
      rfl
  exact ⟨y.1, this⟩

/-- 補集合への制限（coIdeal は 1 歩先で閉じる） -/
noncomputable def restrictToCoIdeal (S : SPO.FuncSetup α) (m : S.Elem)  (hpos : isPoset S) (notconnected: ¬ (∃! mm: S.Elem, S.maximal mm)): FuncSetup α := by
  classical
  refine
    { ground := coIdeal S m,
      nonempty := by
        let cno := coIdeal_nonempty_of_not_unique_maximal S (hpos := hpos) notconnected m
        simp_all only [nonempty_subtype]
        obtain ⟨val, property⟩ := m
        exact cno
    , f := ?f }
  intro x
  let xg : S.Elem :=
    ⟨x.1, (mem_coIdeal_iff S (m := m) (y := x.1)).1 x.2 |>.1⟩
  let y : S.Elem := S.f xg
  have : y.1 ∈ coIdeal S m :=
    cover_preserves_coIdeal S (m := m) (x := xg) (y := y)
      (by
        -- `x.2 : x.1 ∈ coIdeal m`
        exact x.2)
      rfl
  exact ⟨y.1, this⟩

lemma ground_union_split
  (S : SPO.FuncSetup α) (m : S.Elem) (hm : S.maximal m)
  (hpos : isPoset S) (notconnected : ¬ (∃! mm : S.Elem, S.maximal mm)) :
  (restrictToIdeal S m hm).ground ∪ (restrictToCoIdeal S m hpos notconnected).ground
    = S.ground := by
  classical
  -- 両辺を定義へ
  change S.principalIdeal m.1 m.2 ∪ coIdeal S m = S.ground
  -- coIdeal の定義
  unfold coIdeal
  -- principalIdeal ⊆ ground
  have hsub : S.principalIdeal m.1 m.2 ⊆ S.ground :=
    S.principalIdeal_subset_ground ⟨m.1, m.2⟩
  -- `s ∪ (t \ s) = t`
  exact Finset.union_sdiff_of_subset hsub

/-- おまけ：直和分割なので互いに素。 -/
lemma ground_disjoint_split
  (S : SPO.FuncSetup α) (m : S.Elem) (hm : S.maximal m)
  (hpos : isPoset S) (notconnected : ¬ (∃! mm : S.Elem, S.maximal mm)) :
  Disjoint (restrictToIdeal S m hm).ground (restrictToCoIdeal S m hpos notconnected).ground := by
  classical
  -- 定義に戻す
  change Disjoint (S.principalIdeal m.1 m.2) (coIdeal S m)
  -- coIdeal = ground \ principalIdeal
  unfold coIdeal
  -- `s` と `t \ s` は常に素
  exact Finset.disjoint_sdiff

/-- 補助：`coIdeal` のサイズと差分公式。 -/
lemma card_coIdeal_eq_sub (S : SPO.FuncSetup α) (m : S.Elem) :
  (coIdeal S m).card = S.ground.card - (S.principalIdeal m.1 m.2).card := by
  classical
  have hsub : S.principalIdeal m.1 m.2 ⊆ S.ground :=
    S.principalIdeal_subset_ground ⟨m.1, m.2⟩
  unfold coIdeal
  exact Finset.card_sdiff hsub

/-- `coIdeal` と `principalIdeal` のサイズ和は `ground` のサイズ。 -/
lemma card_coIdeal_add_card_principal
  (S : SPO.FuncSetup α) (m : S.Elem) :
  (coIdeal S m).card + (S.principalIdeal m.1 m.2).card = S.ground.card := by
  classical
  have hsub : S.principalIdeal m.1 m.2 ⊆ S.ground :=
    S.principalIdeal_subset_ground ⟨m.1, m.2⟩
  have hsdiff :
    (coIdeal S m).card = S.ground.card - (S.principalIdeal m.1 m.2).card :=
    card_coIdeal_eq_sub S m
  -- (A \ B).card + B.card = A.card
  calc
    (coIdeal S m).card + (S.principalIdeal m.1 m.2).card
        = (S.ground.card - (S.principalIdeal m.1 m.2).card)
          + (S.principalIdeal m.1 m.2).card := by
            exact congrArg (fun t => t + (S.principalIdeal m.1 m.2).card) hsdiff
    _ = S.ground.card := by
         apply Nat.sub_add_cancel
         exact Finset.card_le_card hsub

/-- つねに `|coIdeal| < |ground|`。
`m ∈ principalIdeal` なので `principalIdeal` が非空で、差分で 1 以上削れるため。 -/
lemma card_coIdeal_lt_ground (S : SPO.FuncSetup α) (m : S.Elem) :
  (coIdeal S m).card < S.ground.card := by
  classical
  -- principalIdeal は非空
  have hmem : m.1 ∈ S.principalIdeal m.1 m.2 := S.self_mem_principalIdeal m
  have hpos : 0 < (S.principalIdeal m.1 m.2).card :=
    Finset.card_pos.mpr ⟨m.1, hmem⟩
  -- (coIdeal).card + (principal).card = ground.card
  have hsum := card_coIdeal_add_card_principal S m
  -- `principal` が 1 以上なので `(coIdeal)+1 ≤ ground`
  have hle : (coIdeal S m).card + 1 ≤ S.ground.card := by
    have : 1 ≤ (S.principalIdeal m.1 m.2).card := Nat.succ_le_of_lt hpos
    have : (coIdeal S m).card + 1
            ≤ (coIdeal S m).card + (S.principalIdeal m.1 m.2).card :=
      Nat.add_le_add_left this _
    -- 右辺を `ground.card` に置換
    calc
      (coIdeal S m).card + 1
          ≤ (coIdeal S m).card + (S.principalIdeal m.1 m.2).card := this
      _ = S.ground.card := hsum
  -- `t + 1 ≤ N` なら `t < N`
  have : (coIdeal S m).card < Nat.succ ((coIdeal S m).card) :=
    Nat.lt_succ_self _
  exact Nat.lt_of_lt_of_le this (by
    -- `Nat.succ t = t + 1`
    -- `hle : t + 1 ≤ N` を使うために結び替え
    have : Nat.succ ((coIdeal S m).card) = (coIdeal S m).card + 1 := rfl
    -- `this ▸ hle : succ t ≤ N`
    -- これにより `succ_le` で `<` に落とすのも可だが、いまは `lt_of_lt_of_le` で十分
    -- ここは等式置換だけ
    exact (by
      -- `le_of_eq` で等式変換
      -- 実質 `hle` をそのまま使っています
      -- 目的は `succ (coIdeal.card) ≤ ground.card`
      -- `hle` は `(coIdeal.card) + 1 ≤ ground.card`
      -- `rfl` で一致
      simpa using hle))

/-- `notconnected`（極大が一意でない）なら `|principalIdeal| < |ground|`。 -/
lemma card_principal_lt_ground_of_not_unique
  (S : SPO.FuncSetup α) [Fintype S.Elem]
  (hpos : isPoset S) (notconnected : ¬ (∃! mm : S.Elem, S.maximal mm))
  (m : S.Elem) :
  (S.principalIdeal m.1 m.2).card < S.ground.card := by
  classical
  -- `coIdeal` が非空
  have hne : (coIdeal S m).Nonempty :=
    coIdeal_nonempty_of_not_unique_maximal S (hpos := hpos) notconnected m
  -- 非空なら `0 < |coIdeal|`
  obtain ⟨y, hy⟩ := hne
  have hposCo : 0 < (coIdeal S m).card := Finset.card_pos.mpr ⟨y, hy⟩
  -- `(coIdeal).card + (principal).card = ground.card`
  have hsum := card_coIdeal_add_card_principal S m
  -- `(principal)+1 ≤ ground` を作って `<` に落とす
  have hle : (S.principalIdeal m.1 m.2).card + 1 ≤ S.ground.card := by
    have : 1 ≤ (coIdeal S m).card := Nat.succ_le_of_lt hposCo
    have : (S.principalIdeal m.1 m.2).card + 1
            ≤ (S.principalIdeal m.1 m.2).card + (coIdeal S m).card :=
      Nat.add_le_add_left this _
    -- 右辺を ground に置換（和は comm だが等式 hsum は「co + pr」なので一旦可換を噛ませます）
    have hcomm :
      (S.principalIdeal m.1 m.2).card + (coIdeal S m).card
        = (coIdeal S m).card + (S.principalIdeal m.1 m.2).card := by
      exact Nat.add_comm _ _
    calc
      (S.principalIdeal m.1 m.2).card + 1
          ≤ (S.principalIdeal m.1 m.2).card + (coIdeal S m).card := this
      _ = (coIdeal S m).card + (S.principalIdeal m.1 m.2).card := hcomm
      _ = S.ground.card := hsum
  -- `<` へ
  have : (S.principalIdeal m.1 m.2).card < Nat.succ ((S.principalIdeal m.1 m.2).card) :=
    Nat.lt_succ_self _
  exact Nat.lt_of_lt_of_le this (by
    -- `succ = +1`
    have : Nat.succ ((S.principalIdeal m.1 m.2).card)
            = (S.principalIdeal m.1 m.2).card + 1 := rfl
    simpa using hle)

/-- すぐ使える形：`restrictToCoIdeal` の台集合サイズが真に小さい。 -/
lemma restrictToCoIdeal_card_lt
  (S : SPO.FuncSetup α) (m : S.Elem)
  (hpos : isPoset S) (notconnected : ¬ (∃! mm : S.Elem, S.maximal mm)) :
  (restrictToCoIdeal S m hpos notconnected).ground.card < S.ground.card := by
  classical
  -- ground = coIdeal
  change (coIdeal S m).card < S.ground.card
  exact card_coIdeal_lt_ground S m

/-- すぐ使える形：`restrictToIdeal` の台集合サイズが（極大が一意でないなら）真に小さい。 -/
lemma restrictToIdeal_card_lt_of_not_unique
  (S : SPO.FuncSetup α) (m : S.Elem) (hm : S.maximal m)
  [Fintype S.Elem] (hpos : isPoset S)
  (notconnected : ¬ (∃! mm : S.Elem, S.maximal mm)) :
  (restrictToIdeal S m hm).ground.card < S.ground.card := by
  classical
  -- ground = principalIdeal
  change (S.principalIdeal m.1 m.2).card < S.ground.card
  exact card_principal_lt_ground_of_not_unique S (hpos := hpos) notconnected m




/-! ## 一意性：各 `x` の上の極大元は高々 1 つ -/


/-- `x` の上にある極大元の一意性。 -/
lemma unique_maximal_above (S : SPO.FuncSetup α)
  [Fintype S.Elem] (hpos : isPoset S)
  {x m₁ m₂ : S.Elem}
  (hm₁ : S.maximal m₁) (hm₂ : S.maximal m₂)
  (hx₁ : S.le x m₁) (hx₂ : S.le x m₂) :
  m₁ = m₂ := by
  classical
  rcases (le_iff_exists_iter S x m₁).1 hx₁ with ⟨i, hi⟩
  rcases (le_iff_exists_iter S x m₂).1 hx₂ with ⟨j, hj⟩
  by_cases hij : i ≤ j
  · -- m₁ ≤ m₂
    have hchain := S.le_between_iter x hij
    --exact?
    -- 左右を書き換え
    have h₁ : S.le m₁ ((S.f^[j]) x) := by cases hi; exact hchain
    have h₂ : S.le m₁ m₂ := by cases hj; exact h₁
    -- 極大性で逆向きも
    have h₃ : S.le m₂ m₁ := hm₁ h₂
    exact hpos (hm₂ (hm₁ h₂)) h₃
  · -- 対称
    have hji : j ≤ i := le_of_not_ge hij
    have hchain := le_between_iter S x hji
    have h₁ : S.le m₂ ((S.f^[i]) x) := by cases hj; exact hchain
    have h₂ : S.le m₂ m₁ := by cases hi; exact h₁
    have h₃ : S.le m₁ m₂ := hm₂ h₂
    exact hpos (hm₂ (hm₁ h₃)) h₂

/-- まとめ：各 `x` には「上にある極大元」が存在一意。 -/
lemma exists_unique_maxAbove (S : SPO.FuncSetup α)
  [Fintype S.Elem] (hpos : isPoset S) (x : S.Elem) :
  ∃! m : S.Elem, S.maximal m ∧ S.le x m := by
  classical
  -- 存在
  obtain ⟨m, hm, hxm⟩ := exists_maximal_above S x
  refine ⟨m, ⟨hm, hxm⟩, ?uniq⟩
  -- 一意性
  intro m' hm'
  let uma := unique_maximal_above (S := S) (hpos := hpos) (hm₁ := hm) (hm₂ := hm'.1)  (hx₁ := hxm) (hx₂ := hm'.2)
  exact id (Eq.symm uma)

def liftFromIdeal
  (S : SPO.FuncSetup α) (m : S.Elem) (hm : S.maximal m)
  (x : (restrictToIdeal S m hm).Elem) : S.Elem :=
  ⟨ x.1, (S.principalIdeal_subset_ground ⟨m.1, m.2⟩) x.2 ⟩

-- co-ideal 版
def liftFromCoIdeal
  (S : SPO.FuncSetup α) (m : S.Elem) (hpos : isPoset S) (notuniq : ¬∃! mm, S.maximal mm)
  (x : (restrictToCoIdeal S m hpos notuniq).Elem) : S.Elem :=
  ⟨ x.1, (mem_coIdeal_iff S (m := m) (y := x.1)).1 x.2 |>.1 ⟩

/-! ## 1. cover を持ち上げる -/

lemma cover_lift_Ideal
  (S : SPO.FuncSetup α) (m : S.Elem) (hm : S.maximal m)
  {x y : (restrictToIdeal S m hm).Elem} :
  (restrictToIdeal S m hm).cover x y →
  S.cover (liftFromIdeal S m hm x) (liftFromIdeal S m hm y) := by
  classical
  intro h
  -- 定義展開
  dsimp [FuncSetup.cover, restrictToIdeal] at h
  -- f の中身に合わせて x 側の S.Elem を作り直す
  let xg : S.Elem := ⟨x.1, (S.principalIdeal_subset_ground ⟨m.1,m.2⟩) x.2⟩
  -- `h : ⟨(S.f xg).1, _⟩ = y` から値の等式を取り出す
  have hval : (S.f xg).1 = y.1 := congrArg Subtype.val h
  -- 目標：S.f (lift x) = (lift y)
  -- `lift x = xg`，`lift y = ⟨y.1, _⟩`
  dsimp [liftFromIdeal]
  -- 値が等しいので Subtype.ext で終了
  apply Subtype.ext
  exact hval

lemma cover_lift_CoIdeal
  (S : SPO.FuncSetup α) (m : S.Elem) (hpos : isPoset S) (notuniq : ¬∃! mm, S.maximal mm)
  {x y : (restrictToCoIdeal S m hpos notuniq).Elem} :
  (restrictToCoIdeal S m hpos notuniq).cover x y →
  S.cover (liftFromCoIdeal S m hpos notuniq x) (liftFromCoIdeal S m hpos notuniq y) := by
  classical
  intro h
  -- 定義展開
  dsimp [FuncSetup.cover, restrictToCoIdeal] at h
  -- f の中身に合わせて x 側の S.Elem を作り直す
  let xg : S.Elem := ⟨x.1, (mem_coIdeal_iff S (m := m) (y := x.1)).1 x.2 |>.1⟩
  -- 値の等式
  have hval : (S.f xg).1 = y.1 := congrArg Subtype.val h
  -- 目標 S.f (lift x) = lift y
  dsimp [liftFromCoIdeal]
  apply Subtype.ext
  exact hval

/-! ## 2. le（反射推移閉包）を持ち上げる -/

/-- `restrictToIdeal` の `≤` を元の `S` の `≤` に持ち上げる（refine 不使用）。 -/
lemma le_lift_Ideal
  (S : SPO.FuncSetup α) (m : S.Elem) (hm : S.maximal m)
  {x y : (restrictToIdeal S m hm).Elem} :
  (restrictToIdeal S m hm).le x y →
  S.le (liftFromIdeal S m hm x) (liftFromIdeal S m hm y) := by
  classical
  intro hxy
  induction hxy with
  | @refl =>
      exact Relation.ReflTransGen.refl
  | @tail b c hbc hcy ih =>
      -- b ⋖ c（制限側）を S 側の cover に持ち上げる
      have hcov :
          S.cover (liftFromIdeal S m hm b) (liftFromIdeal S m hm c) := by
        apply cover_lift_Ideal S m hm
        exact hcy
      -- 既に (lift x) ≤ (lift b) があり、最後に 1 歩足して (lift c) へ
      exact Relation.ReflTransGen.tail ih hcov

/-- `restrictToCoIdeal` の `≤` を元の `S` の `≤` に持ち上げる（refine 不使用）。 -/
lemma le_lift_CoIdeal
  (S : SPO.FuncSetup α) (m : S.Elem)
  (hpos : isPoset S) (notuniq : ¬ (∃! mm : S.Elem, S.maximal mm))
  {x y : (restrictToCoIdeal S m hpos notuniq).Elem} :
  (restrictToCoIdeal S m hpos notuniq).le x y →
  S.le (liftFromCoIdeal S m hpos notuniq x) (liftFromCoIdeal S m hpos notuniq y) := by
  classical
  intro hxy
  induction hxy with
  | @refl =>
      exact Relation.ReflTransGen.refl
  | @tail b c hbc hcy ih =>
      have hcov :
          S.cover (liftFromCoIdeal S m hpos notuniq b)
                  (liftFromCoIdeal S m hpos notuniq c) := by
        apply cover_lift_CoIdeal S m hpos notuniq
        exact hcy
      exact Relation.ReflTransGen.tail ih hcov

/-! ## 3. 反対称性の移送（= isPoset の保存） -/

lemma antisymm_restrictToIdeal_of_isPoset
  (S : SPO.FuncSetup α) (hpos : isPoset S) (m : S.Elem) (hm : S.maximal m) :
  ∀ {u v : (restrictToIdeal S m hm).Elem},
    (restrictToIdeal S m hm).le u v →
    (restrictToIdeal S m hm).le v u →
    u = v := by
  classical
  intro u v huv hvu
  -- 元の S で反対称
  have : S.le (liftFromIdeal S m hm u) (liftFromIdeal S m hm v) :=
    le_lift_Ideal S m hm huv
  have : (S.le (liftFromIdeal S m hm u) (liftFromIdeal S m hm v))
       ∧ (S.le (liftFromIdeal S m hm v) (liftFromIdeal S m hm u)) := by
    exact ⟨this, le_lift_Ideal S m hm hvu⟩
  rcases this with ⟨h₁, h₂⟩
  have h_eqS : liftFromIdeal S m hm u = liftFromIdeal S m hm v := by
    exact hpos this h₂
      -- 値の等しさに落とし、Subtype.ext で戻す
  have : u.1 = v.1 :=by
    simp_all only [le_iff_leOn_val]
    injection h_eqS

  exact Subtype.ext this

lemma antisymm_restrictToCoIdeal_of_isPoset
  (S : SPO.FuncSetup α) (hpos : isPoset S) (m : S.Elem)
  (notuniq : ¬∃! mm, S.maximal mm) :
  ∀ {u v : (restrictToCoIdeal S m hpos notuniq).Elem},
    (restrictToCoIdeal S m hpos notuniq).le u v →
    (restrictToCoIdeal S m hpos notuniq).le v u →
    u = v := by
  classical
  intro u v huv hvu
  have h₁ : S.le (liftFromCoIdeal S m hpos notuniq u) (liftFromCoIdeal S m hpos notuniq v) :=
    le_lift_CoIdeal S m hpos notuniq huv
  have h₂ : S.le (liftFromCoIdeal S m hpos notuniq v) (liftFromCoIdeal S m hpos notuniq u) :=
    le_lift_CoIdeal S m hpos notuniq hvu
  have h_eqS :
      liftFromCoIdeal S m hpos notuniq u
    = liftFromCoIdeal S m hpos notuniq v := by
    exact hpos h₁ h₂
  have : u.1 = v.1 := by
    apply congrArg Subtype.val
    simp_all only [le_iff_leOn_val]
    injection h_eqS
    (expose_names; exact Subtype.eq val_eq)
  exact Subtype.ext this

-----------------------------------sumProdの話。

lemma mem_edge_sumProd_iff {α} [DecidableEq α]
  (F₁ F₂ : SetFamily α) {X : Finset α} :
  X ∈ (SetFamily.sumProd F₁ F₂).edgeFinset
    ↔ ∃ A ∈ F₁.edgeFinset, ∃ B ∈ F₂.edgeFinset, X = A ∪ B := by
  classical
  constructor
  · intro h
    -- edge ↔ sets で sets の存在形を取り出す
    have hsets :
        (SetFamily.sumProd F₁ F₂).sets X :=
      (SetFamily.mem_edgeFinset_iff_sets (F := SetFamily.sumProd F₁ F₂) (A := X)).1 h
    rcases hsets with ⟨A, B, hA, hB, rfl⟩
    -- それぞれ edgeFinset に持ち上げ
    have hAe : A ∈ F₁.edgeFinset :=
      (SetFamily.mem_edgeFinset_iff_sets (F := F₁) (A := A)).2 hA
    have hBe : B ∈ F₂.edgeFinset :=
      (SetFamily.mem_edgeFinset_iff_sets (F := F₂) (A := B)).2 hB
    exact ⟨A, hAe, B, hBe, rfl⟩
  · intro h
    rcases h with ⟨A, hAe, B, hBe, rfl⟩
    -- 各々を sets に戻して合併が和積の sets
    have hAset : F₁.sets A :=
      (SetFamily.mem_edgeFinset_iff_sets (F := F₁) (A := A)).1 hAe
    have hBset : F₂.sets B :=
      (SetFamily.mem_edgeFinset_iff_sets (F := F₂) (A := B)).1 hBe
    have hXset :
        (SetFamily.sumProd F₁ F₂).sets (A ∪ B) :=
      ⟨A, B, hAset, hBset, rfl⟩
    exact (SetFamily.mem_edgeFinset_iff_sets
            (F := SetFamily.sumProd F₁ F₂) (A := A ∪ B)).2 hXset

/-- `edgeFinset` 自体の同一視（像としての記述）。 -/
lemma edgeFinset_sumProd {α} [DecidableEq α]
  (F₁ F₂ : SetFamily α) :
  (SetFamily.sumProd F₁ F₂).edgeFinset
    =
    (F₁.edgeFinset.product F₂.edgeFinset).image
      (fun p : Finset α × Finset α => p.1 ∪ p.2) := by
  classical
  -- 外延同値で決める
  ext X
  constructor
  · intro h
    -- 直前の同値を image の会員に変換
    have := (mem_edge_sumProd_iff F₁ F₂ (X := X)).1 h
    rcases this with ⟨A, hAe, B, hBe, rfl⟩
    refine Finset.mem_image.mpr ?_
    refine ⟨(A, B), ?prod, rfl⟩
    exact Finset.mem_product.mpr ⟨hAe, hBe⟩
  · intro h
    -- image の会員から直前の同値を使う
    rcases Finset.mem_image.mp h with ⟨p, hp, rfl⟩
    rcases Finset.mem_product.mp hp with ⟨hA, hB⟩
    have : ∃ A ∈ F₁.edgeFinset, ∃ B ∈ F₂.edgeFinset, p.1 ∪ p.2 = A ∪ B :=
      ⟨p.1, hA, p.2, hB, rfl⟩
    have := (mem_edge_sumProd_iff F₁ F₂ (X := p.1 ∪ p.2)).2 this
    exact this

/-成り立たない
lemma idealFamily_eq_sumProd_split
  {α} [DecidableEq α]
  (S : SPO.FuncSetup α) (m : S.Elem) (hm : S.maximal m)
  (hpos : isPoset S) (notuniq : ¬ (∃! mm : S.Elem, S.maximal mm)) :
  let F₁ := (restrictToIdeal S m hm).idealFamily
  let F₂ := (restrictToCoIdeal S m hpos notuniq).idealFamily
  S.idealFamily = SetFamily.sumProd F₁ F₂ := by
  let F₁ := (restrictToIdeal S m hm).idealFamily
  let F₂ := (restrictToCoIdeal S m hpos notuniq).idealFamily
  classical
  -- ground は（定義より） principalIdeal ∪ coIdeal = ground
  have hground :
    (S.idealFamily).ground
      = F₁.ground ∪ F₂.ground := by
    dsimp [F₁, F₂]
    exact (ground_union_split S m hm hpos notuniq).symm

  -- `SetFamily` 拡張外延：ground 等式＋ sets の同値を示す
  -- sets の同値： X が S 全体での順序イデアル
  --  ⇔  A:=X∩I, B:=X∩C が各制限でイデアルで X = A ∪ B
  -- 片方向
  have hsets₁ :
    ∀ X, (S.idealFamily).sets X →
      (SetFamily.sumProd F₁ F₂).sets X := by
    intro X hX
    -- A, B の定義
    let I := S.principalIdeal m.1 m.2
    let C := coIdeal S m
    let A := X ∩ I
    let B := X ∩ C
    have hA : F₁.sets A := by
      -- 「A は principalIdeal 上の順序イデアル」
      -- 下方閉包は `le_preserves_principalIdeal_of_maximal` で足ります
      -- （詳細は既に備えている `exists_first_step_or_refl`/`le_lift_*` を使えば機械的に書けます）
      let efs := exists_first_step_or_refl S m.1
      admit
    have hB : F₂.sets B := by
      -- 「B は coIdeal 上の順序イデアル」
      -- 下方閉包は `le_preserves_coIdeal` で足ります
      admit
    -- X = A ∪ B
    have hXdecomp : X = A ∪ B := by
      -- `C = ground \ I` より、`X = (X∩I) ∪ (X∩C)` は集合恒等式
      -- `Finset.inter` の分配で決まります
      admit
    exact ⟨A, B, hA, hB, hXdecomp⟩

  -- 逆方向
  have hsets₂ :
    ∀ X, (SetFamily.sumProd F₁ F₂).sets X →
      (S.idealFamily).sets X := by
    intro X hX
    rcases hX with ⟨A,B,hA,hB,rfl⟩
    -- `A ⊆ I`, `B ⊆ C` から `A ∪ B ⊆ ground` は自明
    -- 下方閉包は：
    --  z∈A か z∈B の場合分け。`y ≤ z` のとき
    --  - z∈A なら `y ∈ I` は `le_preserves_principalIdeal_of_maximal` で出る。
    --    あとは A のイデアル性で y∈A。
    --  - z∈B なら `y ∈ C` は `le_preserves_coIdeal` で出る。
    --    あとは B のイデアル性で y∈B。
    admit

  -- 以上で `SetFamily` の外延等式を完成
  -- ground は hground，sets は hsets₁/hsets₂
  -- `decSets` は命題等価から自動で一致（`propext`）します
  -- 仕上げ：record ext
  -- （Leanでは `cases` して各フィールドを書き換えるか、`ext` を使います）
  -- ここでは `cases` で：
  ext A
  · exact Eq.to_iff (congrFun (congrArg Membership.mem hground) A)
  · simp_all only [sets_iff_isOrderIdeal, F₁, F₂]
    obtain ⟨val, property⟩ := m
    apply Iff.intro
    · intro a
      simp_all only
    · intro a
      simp_all only
  · exact propext (iff.rfl)
-/

/-! ### 補助１：`leOn` の橋渡し（restrict → 元の S） -/

/-- principal ideal 側：`S₁ := restrictToIdeal S m hm` の `leOn` は
    ground 上では `S` の `leOn` を含意する。 -/
private lemma leOn_of_leOn_restrict_I
  (S : SPO.FuncSetup α) (m : S.Elem) (hm : S.maximal m)
  {x y : α} (hxI : x ∈ S.principalIdeal m.1 m.2) (hyI : y ∈ S.principalIdeal m.1 m.2)
  (hxy : (restrictToIdeal S m hm).leOn x y) :
  S.leOn x y := by
  -- `leOn` を `Elem` の `le` に落としてから `le_lift_Ideal` で持ち上げる
  classical
  -- ground への持ち上げ
  have hxG : x ∈ S.ground := (S.principalIdeal_subset_ground ⟨m.1,m.2⟩) hxI
  have hyG : y ∈ S.ground := (S.principalIdeal_subset_ground ⟨m.1,m.2⟩) hyI
  -- `leOn ↔ le` を使う（既存）
  have : (restrictToIdeal S m hm).le ⟨x, hxI⟩ ⟨y, hyI⟩ := by
    -- `leOn` の定義相当（環境の `le_iff_leOn_val`）を使って落とす
    -- ここでは「val に対する `leOn` が成り立つなら `Elem` の `le`」を取り出します
    -- すなわち `(restrict).leOn x y` → `(restrict).le ⟨x,hxI⟩ ⟨y,hyI⟩`
    -- 環境で既に使っている `le_iff_leOn_val` を用います：
    have hiff := (restrictToIdeal S m hm).le_iff_leOn_val (x := ⟨x,hxI⟩) (y := ⟨y,hyI⟩)
    -- hiff : _ ↔ _
    -- 右向きに使う
    exact (leOn_iff (restrictToIdeal S m hm) hxI hyI).mp hxy
  -- これを `S.le` に持ち上げる
  have : S.le (liftFromIdeal S m hm ⟨x,hxI⟩) (liftFromIdeal S m hm ⟨y,hyI⟩) :=
    le_lift_Ideal S m hm this
  -- さらに `S.le` を `S.leOn` に戻す
  have hiffS := S.le_iff_leOn_val (x := ⟨x,hxG⟩) (y := ⟨y,hyG⟩)
  -- `liftFromIdeal` は値が同じなので `Subtype.ext` 経由で `le` の対象は一致
  -- よってこの `le` から `leOn` が従う
  exact (leOn_iff S hxG hyG).mpr this


/-- co-ideal 側：`S₂ := restrictToCoIdeal S m hpos notuniq` の `leOn` は
    ground 上では `S` の `leOn` を含意する。 -/
private lemma leOn_of_leOn_restrict_C
  (S : SPO.FuncSetup α) (m : S.Elem)
  (hpos : isPoset S) (notuniq : ¬ (∃! mm : S.Elem, S.maximal mm))
  {x y : α} (hxC : x ∈ coIdeal S m) (hyC : y ∈ coIdeal S m)
  (hxy : (restrictToCoIdeal S m hpos notuniq).leOn x y) :
  S.leOn x y := by
  classical
  have hxG : x ∈ S.ground := (mem_coIdeal_iff S (m := m) (y := x)).1 hxC |>.1
  have hyG : y ∈ S.ground := (mem_coIdeal_iff S (m := m) (y := y)).1 hyC |>.1
  have : (restrictToCoIdeal S m hpos notuniq).le ⟨x, hxC⟩ ⟨y, hyC⟩ := by
    -- `leOn ↔ le` を restrict 側で使う
    have hiff := (restrictToCoIdeal S m hpos notuniq).le_iff_leOn_val
                    (x := ⟨x,hxC⟩) (y := ⟨y,hyC⟩)
    exact (leOn_iff (restrictToCoIdeal S m hpos notuniq) hxC hyC).mp hxy
  have : S.le (liftFromCoIdeal S m hpos notuniq ⟨x,hxC⟩)
               (liftFromCoIdeal S m hpos notuniq ⟨y,hyC⟩) :=
    le_lift_CoIdeal S m hpos notuniq this
  have hiffS := S.le_iff_leOn_val (x := ⟨x,hxG⟩) (y := ⟨y,hyG⟩)
  exact (leOn_iff S hxG hyG).mpr this

/-! ### 補助２：ground の分割の便利形 -/

private lemma mem_I_or_C_of_ground
  (S : SPO.FuncSetup α) (m : S.Elem) (hm : S.maximal m)
  (hpos : isPoset S) (notuniq : ¬ (∃! mm : S.Elem, S.maximal mm))
  {x : α} (hxG : x ∈ S.ground) :
  x ∈ S.principalIdeal m.1 m.2 ∨ x ∈ coIdeal S m := by
  classical
  -- `ground = I ∪ C`
  have hsplit :=
    ground_union_split S m hm hpos notuniq
  -- 書き換え
  have : x ∈ (restrictToIdeal S m hm).ground ∪ (restrictToCoIdeal S m hpos notuniq).ground := by
    -- `hxG : x ∈ S.ground` を union へ移送
    -- hsplit : I ∪ C = ground の対称を使ってもよい
    -- ここは `hsplit.symm ▸ hxG`
    simp_all only

  -- 定義で戻す
  have : x ∈ S.principalIdeal m.1 m.2 ∪ coIdeal S m := this
  -- 和集合の会員判定
  exact Finset.mem_union.mp this

private lemma build_restrict_le_I
  (S : SPO.FuncSetup α) (m : S.Elem) (hm : S.maximal m)
  {y x : α} (hyG : y ∈ S.ground) (hxG : x ∈ S.ground)
  (hyI : y ∈ S.principalIdeal m.1 m.2) (hxI : x ∈ S.principalIdeal m.1 m.2)
  (h : S.le ⟨y,hyG⟩ ⟨x,hxG⟩) :
  (restrictToIdeal S m hm).le ⟨y,hyI⟩ ⟨x,hxI⟩ := by
  classical
  -- 帰納で、中間点 `b` が I に居続けることを保ちながら構成
  -- 強化された命題：`∀ b, S.le ⟨y,hyG⟩ b → b.1 ∈ I → restrict.le ⟨y,hyI⟩ ⟨b.1,_⟩`
  -- を b := ⟨x,hxG⟩ に適用する。
  have main :
    ∀ (b : S.Elem), S.le ⟨y,hyG⟩ b → (hb:b.1 ∈ S.principalIdeal m.1 m.2) →
      (restrictToIdeal S m hm).le ⟨y,hyI⟩ ⟨b.1, by exact hb⟩ := by
    intro b hb_le hbI
    -- `hb_le : S.le ⟨y,hyG⟩ b`
    -- `hbI  : b.1 ∈ I`
    induction hb_le with
    | @refl =>
        -- b = ⟨y,hyG⟩。`hbI` は `hyI` に一致しているはずだが、`refl` なのでそのまま
        exact Relation.ReflTransGen.refl
    | @tail p q hpq hpq_to_b ih =>
        -- 形：y ≤ p かつ p ⋖ q、そして q から b まで
        -- まず帰納仮定を p に適用するため、p が I に入ることを示す
        -- いまの `hbI` は最終点 b に対するもの。p の I 所属は、この枝では不要：
        -- 我々の `ih` は `y ≤ p` の場合についての命題を返している。
        -- ただし、この `ih` が返すのは y から p までの restrict 鎖。
        -- 続けて p ⋖ q を restrict の cover に作り直して `tail` を付ける。
        -- p が I に属すことは、y∈I と y≤p から従うので用意する。
        have hp_in_I : p.1 ∈ S.principalIdeal m.1 m.2 := by
          -- y∈I と y ≤ p
          have y_le_p : S.le ⟨y,hyG⟩ p := by
            -- `hb_le` は `Relation.ReflTransGen.tail` を繋いだ鎖なので、今の分岐では
            -- ちょうど `y ≤ p` の部分が `ih` の前提にあたる。
            exact hpq --ih.elim (fun _ => Relation.ReflTransGen.refl) (fun h => h)
          exact
            le_preserves_principalIdeal_of_maximal (S := S)
              (m := m) (x := ⟨y,hyG⟩) (y := p) hm
              (by exact hyI) y_le_p
        -- つぎに `p ⋖ q` を restrict 側の cover に持ち上げる
        have hcov_restrict :
            (restrictToIdeal S m hm).cover
              ⟨p.1, hp_in_I⟩
              ⟨q.1,
                -- q も I に入る：p∈I と p ≤ q（= 1 歩）から
                by
                  have : S.le p q := by
                    apply Relation.ReflTransGen.single
                    exact hpq_to_b
                  exact
                    le_preserves_principalIdeal_of_maximal (S := S)
                      (m := m) (x := p) (y := q) hm hp_in_I this⟩ := by
          -- 値の等式で `Subtype.ext`
          -- まず `S.f ⟨p.1,_⟩ = q` を得る
          have hf_pq : S.f ⟨p.1, p.2⟩ = q := by
            -- `hpq : S.cover p q` は定義上 `S.f p = q`
            simp_all only [le_iff_leOn_val, forall_const, Subtype.coe_eta]
            exact hpq_to_b
          -- 入力の証明部分を差し替えた引数に移す
          -- `⟨p.1, hp_in_I⟩` と `⟨p.1, p.2⟩` は値が同じなので等しい
          --have heq_in :
          --    ⟨p.1, (S.principalIdeal_subset_ground ⟨m.1,m.2⟩) hp_in_I⟩
          --  = ⟨p.1, p.2⟩ := by
          --  apply Subtype.ext; rfl
          -- よって `S.f` を適用して等式を移送
          have hf_on_input :
              S.f ⟨p.1, (S.principalIdeal_subset_ground ⟨m.1,m.2⟩) hp_in_I⟩
            = q := by
            -- `congrArg` で f をかける
            --have := congrArg (fun z => S.f z) heq_in
            -- 右辺は `S.f ⟨p.1,p.2⟩ = q`
            -- 連結させて結論
            simp_all only [le_iff_leOn_val, forall_const, Subtype.coe_eta]


          -- restrict 側の cover は定義上「`restrict.f p' = q'`」なので、
          -- 値の等しさで `Subtype.ext`
          dsimp [FuncSetup.cover, restrictToIdeal]
          -- 目標：`⟨(S.f …).1, _⟩ = ⟨q.1, _⟩` は、`.1` の等しさで十分
          apply Subtype.ext
          -- `.1` の等しさ：上で作った `hf_on_input` を val で落とす
          have := congrArg Subtype.val hf_on_input
          -- 左辺は `(S.f …).1`、右辺は `q.1`
          exact this
        -- これで `ih`（y→p の restrict 鎖）に 1 歩 `p→q` を足して y→q の restrict 鎖を得る
        apply  Relation.ReflTransGen.tail
        exact ih hp_in_I

        exact hcov_restrict

  -- b := ⟨x,hxG⟩ に適用して終了
  have := main ⟨x,hxG⟩ h hxI
  -- 目的の終点は `⟨x,hxI⟩` なので、そのまま一致
  exact this

/--（前方向の証明内で使う）`S.le ⟨y,hyG⟩ ⟨x,hxG⟩` から
  `restrictToCoIdeal` 側の `le ⟨y,hyC⟩ ⟨x,hxC⟩` を構成する。 -/
private lemma build_restrict_le_C
  (S : SPO.FuncSetup α) (m : S.Elem)
  (hpos : isPoset S) (notuniq : ¬ (∃! mm : S.Elem, S.maximal mm))
  {y x : α} (hyG : y ∈ S.ground) (hxG : x ∈ S.ground)
  (hyC : y ∈ coIdeal S m) (hxC : x ∈ coIdeal S m)
  (h : S.le ⟨y,hyG⟩ ⟨x,hxG⟩) :
  (restrictToCoIdeal S m hpos notuniq).le ⟨y,hyC⟩ ⟨x,hxC⟩ := by
  classical
  -- 同様に強化命題で帰納
  have main :
    ∀ (b : S.Elem), S.le ⟨y,hyG⟩ b →(hb:b.1 ∈ coIdeal S m) →
      (restrictToCoIdeal S m hpos notuniq).le ⟨y,hyC⟩ ⟨b.1, by exact hb⟩ := by
    intro b hb_le hbC
    induction hb_le with
    | @refl =>
        exact Relation.ReflTransGen.refl
    | @tail p q hpq hpq_to_b ih =>

        -- y ≤ p の鎖 ih と 1 歩 p ⋖ q
        -- p ∈ C（coIdeal は前進閉性）
        have hp_in_C : p.1 ∈ coIdeal S m := by
          have y_le_p : S.le ⟨y,hyG⟩ p := by
            exact hpq
            --ih.elim (fun _ => Relation.ReflTransGen.refl) (fun h => h)
          exact
            le_preserves_coIdeal (S := S) (m := m)
              (x := ⟨y,hyG⟩) (y := p) (hx := hyC) (hxy := y_le_p)

        ----------------------------------------------------------------
        -- ここから `restrict` 側の 1 歩（cover）を丁寧に作る
        ----------------------------------------------------------------

        -- 1) coIdeal 会員から ground 会員を取り出し、S.Elem を作る
        have hp_ground :
          p.1 ∈ S.ground :=
          (mem_coIdeal_iff S (m := m) (y := p.1)).1 hp_in_C |>.1
        let pG : S.Elem := ⟨p.1, hp_ground⟩

        -- 2) S 側の 1 歩：hpq は S.cover p q、すなわち S.f p = q
        have hf_pq : S.f ⟨p.1, p.2⟩ = q := by
          exact hpq_to_b
          --dsimp [FuncSetup.cover] at hpq; exact hpq

        -- 3) 入力の証明差し替え：pG = ⟨p.1, p.2⟩ （値が同じ）
        have heq_dom : pG = ⟨p.1, p.2⟩ := by
          apply Subtype.ext; rfl

        -- 4) 2 と 3 から、S.f pG = q を得る
        have hf_on_input : S.f pG = q := by
          have := congrArg (fun z => S.f z) heq_dom
          exact Eq.trans this hf_pq

        -- 5) q も C に入る（coIdeal は 1 歩先で閉じる）
        have hq_in_C : q.1 ∈ coIdeal S m :=
          cover_preserves_coIdeal (S := S)
            (m := m) (x := p) (y := q) (hx := hp_in_C) (hxy := hpq_to_b)


        -- 6) restrict 側の cover を構成：
        --    (restrict.f ⟨p.1, hp_in_C⟩) = ⟨q.1, hq_in_C⟩
        have hcov_restrict :
            (restrictToCoIdeal S m hpos notuniq).cover
              ⟨p.1, hp_in_C⟩ ⟨q.1, hq_in_C⟩ := by
          -- 定義展開して値の等しさに還元
          dsimp [FuncSetup.cover, restrictToCoIdeal]
          -- 目標は Subtype の等式なので、値 .1 の等しさで十分
          apply Subtype.ext
          -- `(S.f pG).1 = q.1`
          apply congrArg Subtype.val hf_on_input


        -- 7) 帰納鎖 ih に 1 歩をつなぐ
        apply Relation.ReflTransGen.tail
        exact ih hp_in_C
        exact hcov_restrict

  -- b := ⟨x,hxG⟩ に適用
  exact main ⟨x,hxG⟩ h hxC


/-! ## 本命：`sets` の同値 -/

lemma ideal_sets_iff_sumProd
  (S : SPO.FuncSetup α) (m : S.Elem) (hm : S.maximal m)
  (hpos : isPoset S) (notuniq : ¬ (∃! mm : S.Elem, S.maximal mm))
  {X : Finset α} :
  (S.idealFamily).sets X ↔
  ∃ A B,
    ((restrictToIdeal S m hm).idealFamily).sets A ∧
    ((restrictToCoIdeal S m hpos notuniq).idealFamily).sets B ∧
    X = A ∪ B := by
  classical
  -- 記号省略
  let I : Finset α := S.principalIdeal m.1 m.2
  let C : Finset α := coIdeal S m
  let F  := S.idealFamily
  let F₁ := (restrictToIdeal S m hm).idealFamily
  let F₂ := (restrictToCoIdeal S m hpos notuniq).idealFamily
  constructor
  · -- →：X を X∩I と X∩C に割る
    intro hX
    -- X が全体の順序イデアル
    -- A, B を定義
    let A : Finset α := X ∩ I
    let B : Finset α := X ∩ C
    -- A が F₁ のイデアル
    have hA : F₁.sets A := by
      -- isOrderIdealOn の定義を展開
      -- F₁ = orderIdealFamily (le := (restrict.leOn)) (V := I)
      -- 証明対象： A ⊆ I, かつ downward closed
      dsimp [SetFamily.sets, SetFamily, FuncSetup.idealFamily, orderIdealFamily] at *
      -- A ⊆ I
      have hAsub : A ⊆ I := by
        intro x hx
        exact (Finset.mem_inter.mp hx).2
      -- downward closed（restrict 側の leOn → S 側の leOn に橋渡し）
      have hdc :
        ∀ ⦃x⦄, x ∈ A → ∀ ⦃y⦄, y ∈ I →
          (restrictToIdeal S m hm).leOn y x → y ∈ A := by
        intro x hxA y hyI hle₁
        -- x ∈ X
        have hxX : x ∈ X := (Finset.mem_inter.mp hxA).1
        -- y ∈ ground
        have hyG : y ∈ S.ground :=
          (S.principalIdeal_subset_ground ⟨m.1,m.2⟩) hyI
        -- restrict の leOn から S の leOn へ
        have hleS : S.leOn y x :=
          leOn_of_leOn_restrict_I S m hm (hxI := hyI)
                                   (hyI := (Finset.mem_inter.mp hxA).2) hle₁
        -- X の downward closed（全体側）を使う
        -- hX : isOrderIdealOn (leOn S) S.ground X
        -- すなわち：X ⊆ ground かつ、x∈X, y∈ground, leOn_S y x → y∈X
        have : y ∈ X := by
          -- isOrderIdealOn の定義を展開
          -- hX.1: X ⊆ ground, hX.2: downward closed
          cases hX with
          | intro hsub hdown =>
            -- hdown : ∀ x∈X, ∀ y∈ground, leOn_S y x → y∈X
            exact hdown (by exact hxX) (by exact hyG) (by exact hleS)
        -- A = X∩I に戻す
        exact Finset.mem_inter.mpr ⟨this, hyI⟩
      -- 以上 2 条件で `isOrderIdealOn` 完了
      exact And.intro hAsub hdc

    -- B が F₂ のイデアル
    have hB : F₂.sets B := by
      -- 同様に展開して書く
      dsimp [SetFamily.sets, SetFamily, FuncSetup.idealFamily, orderIdealFamily] at *
      -- B ⊆ C
      have hBsub : B ⊆ C := by
        intro x hx
        exact (Finset.mem_inter.mp hx).2
      -- downward closed
      have hdc :
        ∀ ⦃x⦄, x ∈ B → ∀ ⦃y⦄, y ∈ C →
          (restrictToCoIdeal S m hpos notuniq).leOn y x → y ∈ B := by
        intro x hxB y hyC hle₂
        -- x ∈ X
        have hxX : x ∈ X := (Finset.mem_inter.mp hxB).1
        -- y ∈ ground
        have hyG : y ∈ S.ground := (mem_coIdeal_iff S (m := m) (y := y)).1 hyC |>.1
        -- restrict の leOn から S の leOn へ
        have hleS : S.leOn y x :=
          leOn_of_leOn_restrict_C S m hpos notuniq (hxC := hyC)
                                  (hyC := (Finset.mem_inter.mp hxB).2) hle₂
        -- X の downward closed で y ∈ X
        have : y ∈ X := by
          cases hX with
          | intro hsub hdown =>
              exact hdown (by exact hxX) (by exact hyG) (by exact hleS)
        -- B = X∩C に戻す
        exact Finset.mem_inter.mpr ⟨this, hyC⟩
      exact And.intro hBsub hdc

    -- X = A ∪ B
    have hXeq : X = A ∪ B := by
      -- ground の直和分割から `X = (X∩I) ∪ (X∩C)`
      -- Finset の分配恒等式で済む
      -- `C = ground \ I`
      have : C = S.ground \ I := rfl
      -- 一般事実：`X ∩ (U ∪ V) = (X ∩ U) ∪ (X ∩ V)`
      -- 今回は `ground = I ∪ C` を使って `X = X ∩ ground = X ∩ (I ∪ C)`
      have hsplit :=
        ground_union_split S m hm hpos notuniq
      -- `X = X ∩ ground`
      have : X = X ∩ S.ground := by
        -- hX.1 : X ⊆ ground
        cases hX with
        | intro hsub hdown =>
          -- `X ⊆ ground` かつ `X ⊆ ground` なので `X = X ∩ ground`
          -- `Finset.inter_eq_left` が使えますが、ここは素直に外延
          -- （短くまとめるため、既知の補題を使ってよいなら `by
          --    exact Finset.inter_eq_left.mpr hsub` です）
          simp_all only [sets_iff_isOrderIdeal, F₁, A, I, F₂, B, C]
          ext a : 1
          simp_all only [Finset.mem_inter, iff_self_and]
          intro a_1
          exact hsub a_1

      -- 連鎖
      calc
        X = X ∩ S.ground := this
        _ = X ∩ ((restrictToIdeal S m hm).ground ∪ (restrictToCoIdeal S m hpos notuniq).ground) := by
              -- ground の分割
              have := congrArg (fun (t : Finset α) => X ∩ t)
                               (ground_union_split S m hm hpos notuniq)
              exact id (Eq.symm this)
        _ = (X ∩ I) ∪ (X ∩ C) := by
              exact
                Finset.inter_union_distrib_left X (restrictToIdeal S m hm).ground
                  (restrictToCoIdeal S m hpos notuniq).ground
        _ = A ∪ B := rfl

    -- まとめて存在を返す
    exact ⟨A, B, hA, hB, hXeq⟩

  · -- ←：`X = A ∪ B` で、`A` は I 上のイデアル、`B` は C 上のイデアル ⇒ X は全体のイデアル
    intro hx
    rcases hx with ⟨A, B, hA, hB, rfl⟩
    -- `X = A ∪ B` に置き換わっている
    -- isOrderIdealOn の定義で示す
    dsimp [SetFamily.sets, SetFamily, FuncSetup.idealFamily, orderIdealFamily] at *
    -- まず `A ⊆ I`, `B ⊆ C`
    have hAsubI : A ⊆ I := (And.left hA)
    have hBsubC : B ⊆ C := (And.left hB)
    -- ground 包含：`I ⊆ ground`, `C ⊆ ground` から
    have hIsubG : I ⊆ S.ground :=
      S.principalIdeal_subset_ground ⟨m.1,m.2⟩
    have hCsubG : C ⊆ S.ground := by
      intro x hxC
      -- `x ∈ ground \ I` から ground
      exact (mem_coIdeal_iff S (m := m) (y := x)).1 hxC |>.1
    have hXsubG : (A ∪ B) ⊆ S.ground := by
      intro x hx
      have hx' := Finset.mem_union.mp hx
      cases hx' with
      | inl hxA => exact hIsubG (hAsubI hxA)
      | inr hxB => exact hCsubG (hBsubC hxB)

    -- downward closed：`x ∈ A ∪ B`, `y ∈ ground`, `S.leOn y x` ⇒ `y ∈ A ∪ B`
    have hdown :
      ∀ ⦃x⦄, x ∈ A ∪ B → ∀ ⦃y⦄, y ∈ S.ground → S.leOn y x → y ∈ A ∪ B := by
      intro x hxU y hyG hleS
      -- 分割：x が A 側か B 側か
      have hxU' := Finset.mem_union.mp hxU
      cases hxU' with
      | inl hxA =>
          -- x ∈ A ⊆ I。比較可能なら y も I に落ちる（不可比較性より）
          -- まず y がどちら側かを決める
          -- もし y ∈ C なら `y ≤ x` と `x ∈ I` に矛盾
          have hyI : y ∈ I := by
            -- 反対仮定：y ∈ C だと矛盾
            by_contra hyNotI
            have hyC : y ∈ C := by
              -- ground の分割から
              have := mem_I_or_C_of_ground S m hm hpos notuniq hyG
              cases this with
              | inl hyI0 => exact False.elim (hyNotI hyI0)
              | inr hyC0 => exact hyC0
            -- Elem 化して不可比較性
            let yE : S.Elem := ⟨y, hyG⟩
            let xE : S.Elem := ⟨x, hIsubG (hAsubI hxA)⟩
            -- `S.leOn y x` を `S.le y x` へ
            have h_yx : S.le yE xE :=
              (S.le_iff_leOn_val (x := yE) (y := xE)).mpr hleS
            -- 不可比較（y∈C, x∈I）
            dsimp [C] at hyC
            have hnc := no_comparable_across_split S (m := m) (x := xE) (y:= yE)
                          (hm := hm)
                          (hx := by exact hAsubI hxA)
                          (hy := hyC)

            simp_all only [Finset.mem_union, true_or, le_iff_leOn_val, not_true_eq_false, and_false, C, I, yE, xE]

          -- y ∈ I が分かったので、restrict 側の leOn を作って A の下方閉包を適用
          -- `S.leOn y x` から `restrictToIdeal` の `leOn y x` を得るには、
          -- Elem の `le` に落としてから閉性で I 内に鎖を保持し直す……が、
          -- ここでは既に「S 側の leOn → restrict 側の leOn」を使わずとも、
          -- A の定義（I 上のイデアル）に必要なのは「restrict 側の leOn」。
          -- したがって橋渡しの逆向きが必要だが、上の「不可比較」で y∈I を確保したので、
          -- いったん S 側から restrict 側へ写せます：
          -- `S.leOn y x` → `S.le ⟨y,hyG⟩ ⟨x,_⟩`
          have h_yx_Sle : S.le ⟨y, hyG⟩ ⟨x, hIsubG (hAsubI hxA)⟩ :=
            (S.le_iff_leOn_val (x := ⟨y,hyG⟩) (y := ⟨x,hIsubG (hAsubI hxA)⟩)).mpr hleS
          -- `y,x ∈ I` なので、鎖は principal ideal 内にとどまり、
          -- restrict 側の `le` が作れる（既出の構成に基づく；環境にあるならそれを使用）
          -- ここでは `le_iff_leOn_val` を逆に使って restrict 側の `leOn`
          -- へ戻します。
          have hyx_restrict_leOn :
              (restrictToIdeal S m hm).leOn y x := by
            -- いったん restrict 側の `le` を構成するための補助があると楽ですが、
            -- すでに `le_preserves_principalIdeal_of_maximal` があるので、
            -- `S.le y x` の各ステップは I にとどまります。したがって
            -- restrict の `f` でそのまま ReflTransGen を作れます。
            -- 形式的には、`le_iff_leOn_val` を使うために `le` を出せば十分です。
            -- その構成は既に `le_iff_leOn_val` の ↔ の片側に吸収されている想定なので、
            -- ここではそれを使います。
            -- つまり：restrict 側の `le` を `leOn` に戻します。
            -- `le` の存在は上の議論で出せるため、以下は「その存在を前提に」戻す形。
            -- 実際のコードでは、`le_iff_leOn_val` の逆向きを使います。
            have h_restrict_le :
                (restrictToIdeal S m hm).le ⟨y, hyI⟩ ⟨x, hAsubI hxA⟩ :=
              build_restrict_le_I S m hm
                (hyG := hyG)
                (hxG := hIsubG (hAsubI hxA))
                (hyI := hyI)
                (hxI := hAsubI hxA)
                (h := h_yx_Sle)

            -- ② `le` ↔ `leOn` を使って `leOn` へ戻す
            have hiff :=
              (restrictToIdeal S m hm).le_iff_leOn_val
                (x := ⟨y, hyI⟩) (y := ⟨x, hAsubI hxA⟩)
            -- 環境によっては (x := …) (y := …) という引数名かもしれません。合う方を使ってください。
            -- 例： (x := ⟨y, hyI⟩) (y := ⟨x, hAsubI hxA⟩)

            have hyx_restrict_leOn :
                (restrictToIdeal S m hm).leOn y x :=
              by exact (leOn_iff (restrictToIdeal S m hm) hyI (hAsubI hxA)).mpr h_restrict_le

            exact (leOn_iff (restrictToIdeal S m hm) hyI (hAsubI hxA)).mpr h_restrict_le
          -- A の downward closed を適用
          have hA_closed := (And.right hA)
          have : y ∈ A := hA_closed hxA hyI hyx_restrict_leOn
          exact Finset.mem_union.mpr (Or.inl this)

      | inr hxB =>
          -- x ∈ B ⊆ C の場合は対称
          -- y が I だと不可比較性に矛盾するので、y ∈ C が従う
          have hyC : y ∈ C := by
            -- 反対仮定で矛盾
            by_contra hyNotC
            have hyI : y ∈ I := by
              -- ground の分割から
              have := mem_I_or_C_of_ground S m hm hpos notuniq hyG
              cases this with
              | inl hyI0 => exact hyI0
              | inr hyC0 => exact False.elim (hyNotC hyC0)
            -- Elem 化
            let yE : S.Elem := ⟨y, hyG⟩
            let xE : S.Elem := ⟨x, hCsubG (hBsubC hxB)⟩
            -- `S.leOn y x` → `S.le y x`
            have h_yx : S.le yE xE :=
              (S.le_iff_leOn_val (x := yE) (y := xE)).mpr hleS
            -- 不可比較（y∈I, x∈C）
            -- こちらも `no_comparable_across_split` を x↔y 入れ替えで
            -- `¬ S.le y x` を出して矛盾
            have hnc := no_comparable_across_split S (m := m) (x := yE) (y := xE)
                          (hm := hm)
                          (hx := by exact hyI)
                          (hy := by
                            -- x∈C
                            exact hBsubC hxB )
            exact (hnc.1) h_yx
          -- いま y ∈ C。restrict 側の leOn を作って B の下方閉包
          have h_yx_Sle : S.le ⟨y, hyG⟩ ⟨x, hCsubG (hBsubC hxB)⟩ :=
            (S.le_iff_leOn_val (x := ⟨y,hyG⟩) (y := ⟨x,hCsubG (hBsubC hxB)⟩)).mpr hleS
          have hyx_restrict_leOn :
              (restrictToCoIdeal S m hpos notuniq).leOn y x := by
            -- こちらも上と同様に、`S.le` から restrict 側の `le` を作る帰納を挟み、
            -- `le_iff_leOn_val` の逆向きで `leOn` に戻します。
            have hiff := (restrictToCoIdeal S m hpos notuniq).le_iff_leOn_val
                            (x := ⟨y, by exact hyC⟩)
                            (y := ⟨x, by exact hBsubC hxB⟩)
            have h_restrict_le :
                (restrictToCoIdeal S m hpos notuniq).le
                  ⟨y, hyC⟩ ⟨x, hBsubC hxB⟩ :=
              build_restrict_le_C S m hpos notuniq
                (hyG := hyG)
                (hxG := hCsubG (hBsubC hxB))
                (hyC := hyC)
                (hxC := hBsubC hxB)
                (h := h_yx_Sle)

            -- ② `le` ↔ `leOn` で `leOn` へ
            have hiff :=
              (restrictToCoIdeal S m hpos notuniq).le_iff_leOn_val
                (x := ⟨y, hyC⟩) (y := ⟨x, hBsubC hxB⟩)
            -- （必要なら (x := …) (y := …) 版に置換）

            have hyx_restrict_leOn :
                (restrictToCoIdeal S m hpos notuniq).leOn y x := by
              exact
                (leOn_iff (restrictToCoIdeal S m hpos notuniq) hyC (hBsubC hxB)).mpr h_restrict_le

            exact (leOn_iff (restrictToCoIdeal S m hpos notuniq) hyC (hBsubC hxB)).mpr h_restrict_le
          -- B の下方閉包
          have hB_closed := (And.right hB)
          have : y ∈ B := hB_closed hxB hyC hyx_restrict_leOn
          exact Finset.mem_union.mpr (Or.inr this)

    -- 以上で `isOrderIdealOn` の 2 条件が揃った
    exact And.intro hXsubG hdown

/-- edgeFinset の一致（これが NDS 等式には十分） -/
lemma ideal_edgeFinset_eq_sumProd
  (S : SPO.FuncSetup α) (m : S.Elem) (hm : S.maximal m)
  (hpos : isPoset S) (notuniq : ¬ (∃! mm : S.Elem, S.maximal mm)) :
  let F  := S.idealFamily
  let F₁ := (restrictToIdeal S m hm).idealFamily
  let F₂ := (restrictToCoIdeal S m hpos notuniq).idealFamily
  F.edgeFinset = (SetFamily.sumProd F₁ F₂).edgeFinset := by
  classical
  intro F F₁ F₂
  ext X
  constructor
  · intro hX
    have hset : F.sets X :=
      (SetFamily.mem_edgeFinset_iff_sets (F := F) (A := X)).1 hX
    have hsum : (SetFamily.sumProd F₁ F₂).sets X :=
      (ideal_sets_iff_sumProd S m hm hpos notuniq).1 hset
    exact (SetFamily.mem_edgeFinset_iff_sets (F := SetFamily.sumProd F₁ F₂) (A := X)).2 hsum
  · intro hX
    have hset : (SetFamily.sumProd F₁ F₂).sets X :=
      (SetFamily.mem_edgeFinset_iff_sets (F := SetFamily.sumProd F₁ F₂) (A := X)).1 hX
    have hset' : F.sets X :=
      (ideal_sets_iff_sumProd S m hm hpos notuniq).2 hset
    exact (SetFamily.mem_edgeFinset_iff_sets (F := F) (A := X)).2 hset'

lemma ideal_ground_eq_sumProd_ground
  (S : SPO.FuncSetup α) (m : S.Elem) (hm : S.maximal m)
  (hpos : isPoset S) (notuniq : ¬ (∃! mm : S.Elem, S.maximal mm)) :
  let F  := S.idealFamily
  let F₁ := (restrictToIdeal S m hm).idealFamily
  let F₂ := (restrictToCoIdeal S m hpos notuniq).idealFamily
  F.ground = (SetFamily.sumProd F₁ F₂).ground := by
  classical
  intro F F₁ F₂
  -- sumProd の ground は定義上 F₁.ground ∪ F₂.ground
  -- 先の union 補題を使う
  dsimp [SetFamily.sumProd]
  -- ground の等式だけ取り出しやすい形に書くなら、
  -- sumProd を `by cases` 展開してもOK。ここでは分割補題をそのまま使います。
  -- 具体的には：
  --   F.ground = S.ground
  --   F₁.ground = principalIdeal, F₂.ground = coIdeal
  -- なので直前の ground_union_split と同値です。
  -- よって：
  change S.ground
      = (restrictToIdeal S m hm).ground ∪ (restrictToCoIdeal S m hpos notuniq).ground
    at *
  -- 反転して使うなら対称性
  exact Eq.symm (ground_union_split S m hm hpos notuniq)

lemma idealFamily_eq_sumProd_on_NDS
  (S : SPO.FuncSetup α) (m : S.Elem) (hm : S.maximal m)
  (hpos : isPoset S) (notuniq : ¬ (∃! mm : S.Elem, S.maximal mm)) :
  let F  := S.idealFamily
  let F₁ := (restrictToIdeal S m hm).idealFamily
  let F₂ := (restrictToCoIdeal S m hpos notuniq).idealFamily
  F.NDS = (SetFamily.sumProd F₁ F₂).NDS := by
  classical
  intro F F₁ F₂
  -- edgeFinset 一致
  have hedge :
    F.edgeFinset = (SetFamily.sumProd F₁ F₂).edgeFinset :=
    ideal_edgeFinset_eq_sumProd S m hm hpos notuniq
  -- ground 一致
  have hgr :
    F.ground = (SetFamily.sumProd F₁ F₂).ground :=
    ideal_ground_eq_sumProd_ground S m hm hpos notuniq
  -- 3 つの構成要素（#H, total size, |V|）が一致 ⇒ NDS 一致
  -- #H
  have hnum :
    F.numHyperedges
      = (SetFamily.sumProd F₁ F₂).numHyperedges := by
    dsimp [SetFamily.numHyperedges]
    -- card の引数が同じなので書き換え
    exact congrArg Finset.card hedge
  -- total size
  have htot :
    F.totalHyperedgeSize
      = (SetFamily.sumProd F₁ F₂).totalHyperedgeSize := by
    dsimp [SetFamily.totalHyperedgeSize]
    -- sum の集合が同じなので書き換え
    -- `sum` の等式は `Finset.sum_bij` でもよいですが、edgeFinset 等式からの `rw` で足ります
    -- （Lean 上は `rw [hedge]`）
    -- ただし方針上 `rw` を避けたいときは `Eq.rec` で置換してもOK
    -- ここでは簡潔に：
    --   exact by cases hedge; rfl
    simp_all only [F, F₁, F₂]
  -- ground.card
  have hV :
    (F.ground.card : Int)
      = ((SetFamily.sumProd F₁ F₂).ground.card : Int) := by
    -- `card` を `ground` の等式で置換
    simp_all only [F, F₁, F₂]

  -- まとめて NDS
  simp_all only [SetFamily.NDS_def, F, F₁, F₂]


-------ここからndsの話？分割地点候補。

--使っている。
omit [DecidableEq α] in
private lemma sum_const_nat (s : Finset α) (c : Nat) :
  ∑ _ ∈ s, c = s.card * c := by
  -- `sum_const` は `s.card • c` を返すので、`Nat.smul_def` で `*` に直す
  have := Finset.sum_const (c) (s := s)
  -- `∑ _∈s, c = s.card • c`
  have : (∑ _ ∈ s, c) = s.card • c := this
  -- `n • m = n * m` を適用
  calc
    (∑ _ ∈ s, c) = s.card • c := this
    _ = s.card * c := by exact rfl

/-
lemma sum_card_union_general
  (F₁ F₂ : SetFamily α) :
  ∑ A ∈ F₁.edgeFinset, ∑ B ∈ F₂.edgeFinset, (A ∪ B).card
    =
    (F₂.numHyperedges) * (∑ A ∈ F₁.edgeFinset, A.card)
  + (F₁.numHyperedges) * (∑ B ∈ F₂.edgeFinset, B.card)
  - (∑ A ∈ F₁.edgeFinset, ∑ B ∈ F₂.edgeFinset, (A ∩ B).card) := by
  classical
  -- 各項で恒等式：|A|+|B| = |A∪B| + |A∩B|
  have hAB :
    ∀ (A B : Finset α), A.card + B.card = (A ∪ B).card + (A ∩ B).card := by
    intro A B
    exact (by
      -- 既知：`card_union_add_card_inter`
      -- 形は `card (A ∪ B) + card (A ∩ B) = card A + card B`
      -- それを左右反転
      have := Finset.card_union_add_card_inter A B
      -- `A ∪ B` と `A ∩ B` は可換なので左右入れ替えだけで OK
      -- ただし既存は右辺＝左辺なので `Eq.symm` で向きを合わせる
      exact Eq.symm this)
  -- まず右辺の第1項：A 側の和を取り出す
  -- ∑_{A,B} (A ∪ B).card = ∑_{A,B} (A.card + B.card) - ∑_{A,B} (A ∩ B).card
  --                         = (∑_A ∑_B A.card) + (∑_A ∑_B B.card) - …
  --                         = (#F₂) * (∑_A A.card) + (#F₁) * (∑_B B.card) - …
  -- これを式で実行する：
  -- 左辺を hAB で置換して整理
  have : ∑ A ∈ F₁.edgeFinset, ∑ B ∈ F₂.edgeFinset, (A ∪ B).card
      =
      ∑ A ∈ F₁.edgeFinset, ∑ B ∈ F₂.edgeFinset, (A.card + B.card) -
      ∑ A ∈ F₁.edgeFinset, ∑ B ∈ F₂.edgeFinset, (A ∩ B).card := by
    -- まず `∑ (A,B) (A∪B).card + ∑ (A,B) (A∩B).card = ∑ (A,B) (A.card + B.card)`
    -- を出して、あとは移項
    have hsum :
      (∑ A ∈ F₁.edgeFinset, ∑ B ∈ F₂.edgeFinset, (A ∪ B).card)
      + (∑ A ∈ F₁.edgeFinset, ∑ B ∈ F₂.edgeFinset, (A ∩ B).card)
      =
      (∑ A ∈ F₁.edgeFinset, ∑ B ∈ F₂.edgeFinset, (A.card + B.card)) := by
      -- ペアごとに hAB を適用して二重和
        calc
          (∑ A ∈ F₁.edgeFinset, ∑ B ∈ F₂.edgeFinset, (A ∪ B).card) + (∑ A ∈ F₁.edgeFinset, ∑ B ∈ F₂.edgeFinset, (A ∩ B).card)
        --  = (∑ A ∈ F₁.edgeFinset,(∑ B ∈ F₂.edgeFinset, (A ∪ B).card) + (∑ B ∈ F₂.edgeFinset, (A ∩ B).card)) := by
        --    exact Finset.sum_add_distrib

            = ∑ A ∈ F₁.edgeFinset, ∑ B ∈ F₂.edgeFinset, ((A ∪ B).card + (A ∩ B).card) := by
              rw [← Finset.sum_add_distrib]
              apply Finset.sum_congr rfl
              exact fun x a => Eq.symm Finset.sum_add_distrib

          _ = ∑ A ∈ F₁.edgeFinset, ∑ B ∈ F₂.edgeFinset, (A.card + B.card) := by
              simp_rw [←hAB]
    exact Nat.eq_sub_of_add_eq hsum

  -- したがって、あとは二重和の分離と「定数和＝個数×定数」で整理するだけ
  -- まず右辺第1項：
  have h1 :
    ∑ A ∈ F₁.edgeFinset, ∑ B ∈ F₂.edgeFinset, (A.card + B.card)
      =
      (F₂.edgeFinset.card) * (∑ A ∈ F₁.edgeFinset, A.card)
    + (F₁.edgeFinset.card) * (∑ B ∈ F₂.edgeFinset, B.card) := by
    -- 左辺を A 側・B 側で分離
    have :=
      Finset.sum_congr rfl (fun (A:Finset α) hA => by
        -- ∑_B (A.card + B.card) = (∑_B A.card) + (∑_B B.card)
        have hsplit :
          ∑ B ∈ F₂.edgeFinset, (A.card + B.card)
            =
            (∑ B ∈ F₂.edgeFinset, A.card)
          + (∑ B ∈ F₂.edgeFinset, B.card) := by
          exact Finset.sum_add_distrib
        -- `∑_B A.card = (#F₂) * A.card` を使う
        have hconst :
          ∑ B ∈ F₂.edgeFinset, A.card
            = F₂.edgeFinset.card * A.card := by
          -- `sum_const`（`•`）→ Nat の積に直す
          have := Finset.sum_const (A.card) (s := F₂.edgeFinset)
          -- `nsmul` を積に直す補題（`Nat.smul_def`）
          -- `∑ _∈s, c = s.card • c` なので `•` を「繰り返し加算＝積」に置換
          -- ここは `Nat.smul_def` で良い
          -- `sum_const` は `∑ _∈s, c = s.card • c`
          -- したがって `= s.card * c`
          -- `simp` を使わないので手で書き換えます
          -- `Nat.smul_def` : `n • a = n * a`（Nat の加法モノイド）
          have := this
          -- `show F₂.edgeFinset.card * A.card = _` でも良いが、等式向きを合わせるため下で変換
          -- 具体的には `rw` を使わず `Nat.smul_def` で右辺を書き直します
          -- 書換えをしやすいよう `calc` にします
          have : (∑ _ ∈ F₂.edgeFinset, A.card)
                   = F₂.edgeFinset.card • A.card := this
          -- `•` を `*` に差し替え
          -- `by exact` で向きを合わせます
          -- `•` の評価は `Nat.smul_def`
          -- 右辺を最終形に直す
          -- 最後に `rfl` で終了
          -- 簡潔に：
          --   ∑ const = card • const = card * const
          -- を返すだけにします
          -- 直接書き戻し：
          -- （Lean では `by`ブロック内で `exact` で終わらせます）
          -- まとめ：
          --   1) sum_const
          --   2) smul_def
          -- を順に適用
          -- 実コード：
          -- (このままでは冗長なので、最終行で `exact` だけ返します)
          -- ここでは結果式だけ返す：
          exact by
            -- `sum_const` の式を受け取り、`•` を展開
            -- `nsmul_eq_mul` が使える環境ならそれで終了ですが、
            -- 明示的に `Nat.smul_def` を使います
            -- `simp` は使わない方針なので、`rw` で 2 ステップ
            -- 1) 右辺を `•` に
            -- 2) `•` を `*` に
            have hc := Finset.sum_const (A.card) (s := F₂.edgeFinset)
            -- hc : ∑ _∈s, c = s.card • c
            -- 右辺を展開
            -- `Nat.smul_def : n • m = n * m`
            -- 等式向きを合わせるために calc を使う
            calc
              ∑ _ ∈ F₂.edgeFinset, A.card
                  = F₂.edgeFinset.card • A.card := hc
              _ = F₂.edgeFinset.card * A.card := by exact rfl--Nat.smul_def _ _
        -- A 側の外側和に戻す
        have : ∑ B ∈ F₂.edgeFinset, (A.card + B.card)
                =
                F₂.edgeFinset.card * A.card
              +  (∑ B ∈ F₂.edgeFinset, B.card) := by
          exact Eq.trans hsplit (by
            exact congrArg (fun t => t + _) hconst)
        exact this
      )
    -- いま得られた等式を A について総和する
    -- 左辺：そのまま
    -- 右辺：分配法則で
    --   (∑_A (#F₂ * A.card)) + (∑_A ∑_B B.card)
    --   = (#F₂) * (∑_A A.card) + (#F₁) * (∑_B B.card)
    -- を目指す
    -- まずこの `sum_congr` の等式を受け取る
    have hsplitAll := this
    -- 右辺第2項は A に依らない定数和
    --   ∑_A (∑_B B.card) = (#F₁) * (∑_B B.card)
    have hBconst :
      ∑ A ∈ F₁.edgeFinset, (∑ B ∈ F₂.edgeFinset, B.card)
        =
        F₁.edgeFinset.card * (∑ B ∈ F₂.edgeFinset, B.card) := by
      -- sum_const の再利用
      have hc := Finset.sum_const (∑ B ∈ F₂.edgeFinset, B.card) (s := F₁.edgeFinset)
      -- `•`→`*`
      exact by
        calc
          ∑ _ ∈ F₁.edgeFinset, (∑ B ∈ F₂.edgeFinset, B.card)
              = F₁.edgeFinset.card • (∑ B ∈ F₂.edgeFinset, B.card) := hc
          _ = F₁.edgeFinset.card * (∑ B ∈ F₂.edgeFinset, B.card) := Nat.smul_def _ _
    -- 右辺第1項は分配で外に出す
    have hAlinear :
      ∑ A ∈ F₁.edgeFinset, (F₂.edgeFinset.card * A.card)
        =
        F₂.edgeFinset.card * (∑ A ∈ F₁.edgeFinset, A.card) := by
      -- 自然数の分配則で `*` を和の外へ
      -- `Finset.mul_sum` はないので、帰納法か `Nat.left_distrib` を使い `sum_congr` で展開
      -- ここでは `Nat` の可換半環としての分配を各項へ適用するだけ
      -- `∑ (c * a_i) = c * ∑ a_i`
      -- 既知補題 `Finset.mul_sum` がないため、`Nat` の帰納に頼らず次で片付けます
      -- `Nat` の `nsmul` を経由すれば一行で済みます：
      --   c * t = (c • t) なので、`sum_const` の逆向きを使う形
      -- ただし `nsmul_eq_mul` を直接使わず、分配の等式を `sum_congr`で作ります。
      -- シンプルに：`Finset.induction_on` でまとめます。
      refine Finset.induction_on F₁.edgeFinset ?base ?step
      · -- 空集合
        have : (0 : Nat) = 0 := rfl
        exact this
      · intro A s hAnotin ih
        -- 左辺： (c*A.card) + ∑_{s} (c*...)
        -- 右辺： c * (A.card + ∑_{s} ...)
        -- 帰納法で OK
        have := ih
        -- 展開して結ぶ
        -- 書き下しで十分
        -- 左辺
        --    (∑ in insert A s) (c*A.card) = c*A.card + ∑_s (c*...)
        -- 右辺
        --    c * (∑ in insert A s A.card) = c*(A.card + ∑_s A.card)
        --      = c*A.card + c*∑_s A.card
        -- 以上から一致
        -- Lean 的には `Finset.sum_insert` を使います（`A ∉ s` が必要）
        have hL :
          ∑ x ∈ Finset.insert A s, F₂.edgeFinset.card * x.card
            =
            F₂.edgeFinset.card * A.card
          + (∑ x ∈ s, F₂.edgeFinset.card * x.card) := by
          exact Finset.sum_insert (by exact hAnotin)
        have hR :
          F₂.edgeFinset.card
            * (∑ x ∈ Finset.insert A s, x.card)
            =
            F₂.edgeFinset.card * A.card
          + F₂.edgeFinset.card * (∑ x ∈ s, x.card) := by
          -- `sum_insert` → 分配
          have := Finset.sum_insert (by exact hAnotin) (f := fun x => x.card)
          -- 右辺の掛け算を分配
          -- `Nat.mul_add` を使う
          exact by
            calc
              F₂.edgeFinset.card * (∑ x ∈ Finset.insert A s, x.card)
                  = F₂.edgeFinset.card * (A.card + ∑ x ∈ s, x.card) := this
              _ = F₂.edgeFinset.card * A.card
                + F₂.edgeFinset.card * (∑ x ∈ s, x.card) := Nat.mul_add _ _ _
        -- まとめ
        exact by
          -- 左＝右を、上で作った2式と帰納仮定から合成
          calc
            ∑ x ∈ Finset.insert A s, F₂.edgeFinset.card * x.card
                = F₂.edgeFinset.card * A.card
                + (∑ x ∈ s, F₂.edgeFinset.card * x.card) := hL
            _ = F₂.edgeFinset.card * A.card
                + (F₂.edgeFinset.card * (∑ x ∈ s, x.card)) := by
                  exact congrArg (fun t => F₂.edgeFinset.card * A.card + t) ih
            _ = F₂.edgeFinset.card * A.card
                + F₂.edgeFinset.card * (∑ x ∈ s, x.card) := rfl
            _ = F₂.edgeFinset.card
                * (∑ x ∈ Finset.insert A s, x.card) := by
                  exact Eq.symm hR
    -- 以上を合成
    -- hsplitAll : 左辺 = ∑_A (c*A.card) + ∑_A (∑_B B.card)
    -- 右の2項を hAlinear, hBconst で置換
    -- 最後に加法可換で入れ替え
    -- 実装：
    --   hsplitAll を左右そのまま受け取り、右辺を書き換え
    have := hsplitAll
    -- 右辺の変形
    -- `∑_A (c*A.card)` を hAlinear で置換
    -- `∑_A (∑_B B.card)` を hBconst で置換
    -- 最後に定義 `numHyperedges = edgeFinset.card`
    -- を使って仕上げ
    -- 書き換えは `calc` による段階的な等式で与えます
    -- なお、`Nat` の可換性で順序入れ替えは不要（同型）
    -- 直接：
    --   this : 左辺 = 右辺(未整理)
    -- を `Eq.trans` で整理
    exact by
      -- 左辺：
      --   ∑_A ∑_B (A.card + B.card)
      -- 右辺：
      --   ∑_A (c*A.card) + ∑_A (∑_B B.card)
      -- を置換
      refine Eq.trans this ?goal
      -- 置換後の右辺を希望形に
      calc
        (∑ A ∈ F₁.edgeFinset, F₂.edgeFinset.card * A.card)
          + (∑ A ∈ F₁.edgeFinset, ∑ B ∈ F₂.edgeFinset, B.card)
            = F₂.edgeFinset.card * (∑ A ∈ F₁.edgeFinset, A.card)
              + F₁.edgeFinset.card * (∑ B ∈ F₂.edgeFinset, B.card) := by
                -- 2項をそれぞれ hAlinear, hBconst に差し替え
                exact Eq.trans
                  (by
                    -- 左の和を hAlinear
                    have := hAlinear
                    exact congrArg (fun t => t + _) this
                  )
                  (by
                    -- 右の和を hBconst
                    have := hBconst
                    -- 交換して加える
                    -- `a + b = a + b` なのでそのまま
                    exact congrArg (fun t => _ + t) this
                  )
  -- ここまでで
  --   ∑∑ (A∪B) = [上の h1] − ∑∑ (A∩B)
  -- が出たので結合して完成
  -- 右端の `numHyperedges` に置換
  have : F₁.edgeFinset.card = F₁.numHyperedges := rfl
  have : F₂.edgeFinset.card = F₂.numHyperedges := rfl
  -- 式のまとめ
  -- まず先に出した「移項式」を使う
  -- `∑∑ (A∪B) = (…A.card+B.card…) − ∑∑(A∩B)`
  -- を、h1 で置換して完成
  -- 実装：
  --   上で作った 2 つの `have` は `rfl` なので、数式内でそのまま使えます
  exact by
    -- 左辺を前段の「移項式」で置き、右辺の (…A.card+B.card…) を h1 で置換
    have hL := this
    -- 変数名衝突を避けつつ展開
    -- 先の「移項式」は `have` で名付け済み（前段の `have : ... = ...`）
    -- 名前がバッティングするので取り直します
    have hMove :
      ∑ A ∈ F₁.edgeFinset, ∑ B ∈ F₂.edgeFinset, (A ∪ B).card
      =
      ∑ A ∈ F₁.edgeFinset, ∑ B ∈ F₂.edgeFinset, (A.card + B.card)
      - ∑ A ∈ F₁.edgeFinset, ∑ B ∈ F₂.edgeFinset, (A ∩ B).card := by
      -- これは上の大きな `have` です（スコープの都合で取り直し）
      -- そこでは `exact` で出しましたが、いまは参照として再掲します
      -- ここで `sorry` は使えないので、もう一度短く導出しても良いですが、
      -- 上のブロックが長いので、このまま使います
      -- 具体的には、上のブロック全体がこの `have` と同内容です
      -- したがって、その結論をここで `admit` の代わりに直接再証明しないよう配慮します
      -- しかし Lean 的には同じ証明を再度書く必要があるため、上のブロックの最後の `exact` を
      -- ここへ移植した体裁にします：
      -- （上で `exact` に渡した式をこのまま返しておきます）
      -- 便宜上、同じ記述をもう一度返します（冗長だが安全）
      -- ── 実用上、この `have` は上段の `have` 自体を名前で参照すべきですが、
      --    ここでは簡潔性のため再掲しました。
      -- ここでは簡単化して、成立している前提のもと「前段の式」を使う想定で返します。
      -- 実装簡略化のため、いったん `admit` は避け、上で作った式名を利用する構成にするのが最良です。
      -- しかし上ブロックの `have` はローカルなので、ここでは直接 `exact` で上式を返せません。
      -- そのため、**この1行** を次の短い別証明に差し替えます。
      -- 代替：逐点等式を二重和で適用し、移項は `Nat` の加法で処理します。
      -- ここでは簡単化のため、もう一度短く証明します：
      have hsum :
        (∑ A ∈ F₁.edgeFinset, ∑ B ∈ F₂.edgeFinset, (A ∪ B).card)
        + (∑ A ∈ F₁.edgeFinset, ∑ B ∈ F₂.edgeFinset, (A ∩ B).card)
        =
        (∑ A ∈ F₁.edgeFinset, ∑ B ∈ F₂.edgeFinset, (A.card + B.card)) := by
        refine Finset.sum_congr rfl ?_
        intro A hA
        refine Finset.sum_congr rfl ?_
        intro B hB
        exact (Finset.card_union_add_card_inter A B).symm
      -- `a + c = b` → `a = b - c`
      apply (Nat.add_right_cancel
                (a := ∑ A ∈ F₁.edgeFinset, ∑ B ∈ F₂.edgeFinset, (A ∪ B).card)
                (b := ∑ A ∈ F₁.edgeFinset, ∑ B ∈ F₂.edgeFinset, (A.card + B.card))
                (c := ∑ A ∈ F₁.edgeFinset, ∑ B ∈ F₂.edgeFinset, (A ∩ B).card))
      exact hsum
    -- いま hMove と h1 を合成
    -- さらに `numHyperedges = card edgeFinset`
    -- を当てて完成
    -- 文字通り代入するだけ
    have h1' := h1
    -- 仕上げ
    -- 右辺の `edgeFinset.card` を `numHyperedges` に置換
    -- ここは rfl なので、そのまま使えます
    -- 最終式：
    --   LHS = [ (F₂.card)*(∑_A A.card) + (F₁.card)*(∑_B B.card) ] - (∑∑|A∩B|)
    -- を返す
    -- 以上で終了
    exact Eq.trans hMove (by
      -- `edgeFinset.card = numHyperedges` を両箇所に挿入
      -- そのままの形で一致します（`rfl`）
      exact h1'
    )

-/

lemma sum_card_union_add_inter_general
  (F₁ F₂ : SetFamily α) :
  (∑ A ∈ F₁.edgeFinset, ∑ B ∈ F₂.edgeFinset, (A ∪ B).card)
  +
  (∑ A ∈ F₁.edgeFinset, ∑ B ∈ F₂.edgeFinset, (A ∩ B).card)
  =
  (F₂.numHyperedges) * (∑ A ∈ F₁.edgeFinset, A.card)
  +
  (F₁.numHyperedges) * (∑ B ∈ F₂.edgeFinset, B.card) := by
  classical
  -- 各ペアで `|A∪B| + |A∩B| = |A| + |B|`
  have hAB :
    ∀ (A B : Finset α), (A ∪ B).card + (A ∩ B).card = A.card + B.card := by
    intro A B
    exact Finset.card_union_add_card_inter A B
  -- 外側の和について等式を作る（`sum_congr` を外側集合に固定して使う）
  have hsum :
    (∑ A ∈ F₁.edgeFinset, ∑ B ∈ F₂.edgeFinset, (A ∪ B).card)
    +
    (∑ A ∈ F₁.edgeFinset, ∑ B ∈ F₂.edgeFinset, (A ∩ B).card)
    =
    (∑ A ∈ F₁.edgeFinset, ∑ B ∈ F₂.edgeFinset, (A.card + B.card)) := by
    -- 左辺の各 A,B 項に hAB を適用して合体
    -- まず左辺を「A で和を取りつつ、B の和の和の和」に合わせるため、各 A 固定で示す
    -- 実際には、足し算の線形性でそのまま `sum_congr` できます
    calc
      (∑ A ∈ F₁.edgeFinset, ∑ B ∈ F₂.edgeFinset, (A ∪ B).card) + (∑ A ∈ F₁.edgeFinset, ∑ B ∈ F₂.edgeFinset, (A ∩ B).card)

        = ∑ A ∈ F₁.edgeFinset, ∑ B ∈ F₂.edgeFinset, ((A ∪ B).card + (A ∩ B).card) := by
              rw [← Finset.sum_add_distrib]
              apply Finset.sum_congr rfl
              exact fun x a => Eq.symm Finset.sum_add_distrib
      _ = ∑ A ∈ F₁.edgeFinset,
              (∑ B ∈ F₂.edgeFinset,
                  ((A ∪ B).card + (A ∩ B).card)) := by
                refine Finset.sum_congr rfl ?_
                intro A hA
                -- 内側は B についての和の加法
                exact rfl
      _ = ∑ A ∈ F₁.edgeFinset,
              (∑ B ∈ F₂.edgeFinset, (A.card + B.card)) := by
                refine Finset.sum_congr rfl ?_
                intro A hA
                refine Finset.sum_congr rfl ?_
                intro B hB
                exact hAB A B
  -- 右辺の「A.card + B.card」を分離して定数和に落とす
  have hsplit :
    ∑ A ∈ F₁.edgeFinset, ∑ B ∈ F₂.edgeFinset, (A.card + B.card)
    =
    (F₂.edgeFinset.card) * (∑ A ∈ F₁.edgeFinset, A.card)
    +
    (F₁.edgeFinset.card) * (∑ B ∈ F₂.edgeFinset, B.card) := by
    -- 各 A 固定で `∑_B (A.card + B.card)` を計算してから A で総和
    have hA :
      ∀ A ∈ F₁.edgeFinset,
        (∑ B ∈ F₂.edgeFinset, (A.card + B.card))
        =
        F₂.edgeFinset.card * A.card + (∑ B ∈ F₂.edgeFinset, B.card) := by
      intro A hA
      calc
        ∑ B ∈ F₂.edgeFinset, (A.card + B.card)
            = (∑ B ∈ F₂.edgeFinset, A.card)
              + (∑ B ∈ F₂.edgeFinset, B.card) := Finset.sum_add_distrib
        _ = F₂.edgeFinset.card * A.card
              + (∑ B ∈ F₂.edgeFinset, B.card) := by
              -- 定数和
              have := sum_const_nat (s := F₂.edgeFinset) (c := A.card)
              -- 等式の第一項を置換
              exact congrArg (fun t => t + (∑ B ∈ F₂.edgeFinset, B.card)) this
    -- 上の等式を A で総和
    calc
      ∑ A ∈ F₁.edgeFinset, ∑ B ∈ F₂.edgeFinset, (A.card + B.card)
          = ∑ A ∈ F₁.edgeFinset,
              (F₂.edgeFinset.card * A.card
               + ∑ B ∈ F₂.edgeFinset, B.card) := by
                refine Finset.sum_congr rfl ?_
                intro A hA
                (expose_names; exact hA_1 A hA)
      _ = (∑ A ∈ F₁.edgeFinset, F₂.edgeFinset.card * A.card)
          + (∑ A ∈ F₁.edgeFinset, ∑ B ∈ F₂.edgeFinset, B.card) := by
                exact Finset.sum_add_distrib
      _ = F₂.edgeFinset.card * (∑ A ∈ F₁.edgeFinset, A.card)
          + F₁.edgeFinset.card * (∑ B ∈ F₂.edgeFinset, B.card) := by
           simp_all only [SetFamily.mem_edgeFinset, and_imp, Finset.sum_const, smul_eq_mul, Nat.add_right_cancel_iff]
           rw [Finset.mul_sum]

  -- 仕上げ：`(∑∑|∪|) + (∑∑|∩|) = [hsplit の右辺]`
  -- hsum で左辺を `∑∑(A.card+B.card)` に置換して、hsplit を適用
  --⊢ ∑ A ∈ F₁.edgeFinset, ∑ B ∈ F₂.edgeFinset, (A ∪ B).card + ∑ A ∈ F₁.edgeFinset, ∑ B ∈ F₂.edgeFinset, (A ∩ B).card =
  --F₂.numHyperedges * ∑ A ∈ F₁.edgeFinset, A.card + F₁.numHyperedges * ∑ B ∈ F₂.edgeFinset, B.card

  have eqn: (∑ A ∈ F₁.edgeFinset, ∑ B ∈ F₂.edgeFinset, (A ∪ B).card)  + (∑ A ∈ F₁.edgeFinset, ∑ B ∈ F₂.edgeFinset, (A ∩ B).card) = (F₂.edgeFinset.card) * (∑ A ∈ F₁.edgeFinset, A.card)+ (F₁.edgeFinset.card) * (∑ B ∈ F₂.edgeFinset, B.card) := by
    rw [hsum]

    rw [hsplit]

  exact eqn

-- 基本恒等式（減算形，Int 版）：
-- `(∑∑ |A∪B|) = (#F₂)*∑|A| + (#F₁)*∑|B| - (∑∑ |A∩B|)`。

lemma sum_card_union_general_int
  (F₁ F₂ : SetFamily α) :
  ((∑ A ∈ F₁.edgeFinset, ∑ B ∈ F₂.edgeFinset, (A ∪ B).card) : Int)
  =
  (F₂.numHyperedges : Int) * (∑ A ∈ F₁.edgeFinset, (A.card : Int))
  +
  (F₁.numHyperedges : Int) * (∑ B ∈ F₂.edgeFinset, (B.card : Int))
  -
  (∑ A ∈ F₁.edgeFinset, ∑ B ∈ F₂.edgeFinset, (A ∩ B).card) := by
  classical
  -- 先の加法形を Int にキャストして両辺から `∑∑ |A∩B|` を引く
  have H :=
    sum_card_union_add_inter_general (F₁ := F₁) (F₂ := F₂)
  -- すべて `Int` にキャストして整理
  -- 左辺： `(L + I : Nat)` を `Int` 化してから右へ移項
  -- 書き下しで行きます
  have := congrArg (fun n : Nat => (n : Int)) H
  -- 以降、`Int.ofNat` の加法・乗法と分配を使って変形
  -- 左辺を `L + I`、右辺をそのままにして、最後に `- I` を両辺へ
  -- `Int` では通常の引き算が使えるので直書きできます
  -- 仕上げは `ring` なしで加減算の結合律・交換律だけです
  -- ここは簡潔に `calc` で：
  -- まず、`(a+b : Nat)` の cast は `(a : Int) + (b : Int)`
  -- を使います（`Nat.cast_add` 相当）
  -- mathlib では `Nat.cast_add` のような補題がありますが、ここは等式の形で順に差し替えます
  -- 最終的な形は「左辺の L を孤立化」した等式です
  clear H
  -- 直接「加法形 → 減算形」への変換は、以下のように一行です：
  -- (L : ℤ) = RHS - (I : ℤ)
  -- なぜなら (L + I : ℕ) の cast は (L : ℤ) + (I : ℤ) で、両辺から (I : ℤ) を引けばよいから。
  -- したがって詳細な `calc` 展開を省略して、等式を書きます。
  -- 既知の等式を `by exact_mod_cast` で流す手もありますが、ここでは明示します。
  -- まず加法形を Int にした等式を `Hℤ` と置きます：
  have Hℤ :
    ((∑ A ∈ F₁.edgeFinset, ∑ B ∈ F₂.edgeFinset, (A ∪ B).card) : Int)
    +
    (∑ A ∈ F₁.edgeFinset, ∑ B ∈ F₂.edgeFinset, (A ∩ B).card)
    =
    (F₂.numHyperedges : Int) * (∑ A ∈ F₁.edgeFinset, (A.card : Int))
    +
    (F₁.numHyperedges : Int) * (∑ B ∈ F₂.edgeFinset, (B.card : Int)) := by
    -- ただの「両辺を Int キャスト」ですが、`Nat`→`Int` の和・積は自動で上がります
    -- （Lean がまとめてくれます）
    -- `exact` で済ませます
    -- （※ ここは“変形そのもの”ではないのでスタイル上問題ないはず）
    exact_mod_cast
      sum_card_union_add_inter_general (F₁ := F₁) (F₂ := F₂)
  -- 両辺から `∑∑|A∩B|` を引いて完成
  have eqn := sub_eq_of_eq_add' (a := (∑ A ∈ F₁.edgeFinset, ∑ B ∈ F₂.edgeFinset, (A ∪ B).card : Int)+ (∑ A ∈ F₁.edgeFinset, ∑ B ∈ F₂.edgeFinset, (A ∩ B).card : Int))
          (b := (∑ A ∈ F₁.edgeFinset, ∑ B ∈ F₂.edgeFinset, (A ∩ B).card : Int))
          (c := (F₂.numHyperedges : Int) * (∑ A ∈ F₁.edgeFinset, (A.card : Int))
              + (F₁.numHyperedges : Int) * (∑ B ∈ F₂.edgeFinset, (B.card : Int))
              - (∑ A ∈ F₁.edgeFinset, ∑ B ∈ F₂.edgeFinset, (A ∩ B).card : Int))
  simp at eqn
  simp_all only [Nat.cast_add, Nat.cast_sum, Nat.cast_mul, sub_add_cancel, forall_const]
  /- 消して良い。
  have :∑ A ∈ F₁.edgeFinset, ∑ B ∈ F₂.edgeFinset, ↑(A ∪ B).card + ∑ A ∈ F₁.edgeFinset, ∑ B ∈ F₂.edgeFinset, ↑(A ∩ B).card =
    ↑F₂.numHyperedges * ∑ A ∈ F₁.edgeFinset, ↑A.card + ↑F₁.numHyperedges * ∑ A ∈ F₂.edgeFinset, ↑A.card := by
    exact Int.ofNat_inj.mp this
  norm_cast at this
  norm_cast at eqn
  specialize eqn this
  dsimp [SetFamily.numHyperedges]
  dsimp [SetFamily.numHyperedges] at eqn
  simp_all only [Nat.cast_add, Nat.cast_mul, Nat.cast_sum]
  norm_cast
  -/

/-- 台集合が素に交わるとき、各エッジ対の交差は空。 -/
lemma inter_card_zero_of_disjoint_ground
  (F₁ F₂ : SetFamily α) (hd : Disjoint F₁.ground F₂.ground)
  {A B : Finset α} (hA : A ∈ F₁.edgeFinset) (hB : B ∈ F₂.edgeFinset) :
  (A ∩ B).card = 0 := by
  classical
  -- A ⊆ ground₁, B ⊆ ground₂
  have hAset : F₁.sets A := (SetFamily.mem_edgeFinset_iff_sets (F := F₁) (A := A)).1 hA
  have hBset : F₂.sets B := (SetFamily.mem_edgeFinset_iff_sets (F := F₂) (A := B)).1 hB
  have hAsub : A ⊆ F₁.ground := F₁.inc_ground hAset
  have hBsub : B ⊆ F₂.ground := F₂.inc_ground hBset
  -- A と B は素に交わる
  have hdisjAB : Disjoint A B := by
    refine Finset.disjoint_left.mpr ?_
    intro a haA haB
    have haG : a ∈ F₁.ground := hAsub haA
    have hbG : a ∈ F₂.ground := hBsub haB
    apply (Finset.disjoint_left.mp hd)
    exact hAsub haA
    exact hBsub haB
  -- 交差が空集合なので card = 0
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro a ha
  have hmem := Finset.mem_inter.mp ha
  apply (Finset.disjoint_left.mp hdisjAB)
  exact Finset.mem_of_mem_filter a ha
  simp_all only [SetFamily.mem_edgeFinset, and_self, Finset.mem_inter]

/-- 交差サイズの二重和は 0。 -/
lemma sum_inter_card_eq_zero_of_disjoint_ground
  (F₁ F₂ : SetFamily α) (hd : Disjoint F₁.ground F₂.ground) :
  ∑ A ∈ F₁.edgeFinset, ∑ B ∈ F₂.edgeFinset, (A ∩ B).card = 0 := by
  classical
  -- 内側の和を 0 に落とす
  have hcongrA :
      ∑ A ∈ F₁.edgeFinset, ∑ B ∈ F₂.edgeFinset, (A ∩ B).card
        = ∑ A ∈ F₁.edgeFinset, 0 := by
    refine Finset.sum_congr rfl ?_
    intro A hA
    have hcongrB :
        ∑ B ∈ F₂.edgeFinset, (A ∩ B).card
          = ∑ B ∈ F₂.edgeFinset, 0 := by
      refine Finset.sum_congr rfl ?_
      intro B hB
      exact inter_card_zero_of_disjoint_ground F₁ F₂ hd hA hB
    simp_all only [SetFamily.mem_edgeFinset, Finset.sum_const_zero, Finset.sum_eq_zero_iff, Finset.card_eq_zero, and_imp,
    Finset.card_empty, implies_true]

  -- 定数 0 の総和は 0
  have : ∑ A ∈ F₁.edgeFinset, 0 = 0 := Finset.sum_const_zero
  exact Eq.trans hcongrA this

/-- 【目的】台集合が素に交わるときの簡約版（Int 版）。 -/
lemma sum_card_union_disjoint_int
  (F₁ F₂ : SetFamily α) (hd : Disjoint F₁.ground F₂.ground) :
  ((∑ A ∈ F₁.edgeFinset, ∑ B ∈ F₂.edgeFinset, (A ∪ B).card) : Int)
  =
  (F₂.numHyperedges : Int) * (∑ A ∈ F₁.edgeFinset, (A.card : Int))
  +
  (F₁.numHyperedges : Int) * (∑ B ∈ F₂.edgeFinset, (B.card : Int)) := by
  classical
  -- 一般式を使い、交差項 0 で簡約
  have H :=
    sum_card_union_general_int (F₁ := F₁) (F₂ := F₂)
  -- 交差二重和 = 0（Nat）→ Int へ
  have h0nat :
      ∑ A ∈ F₁.edgeFinset, ∑ B ∈ F₂.edgeFinset, (A ∩ B).card = 0 :=
    sum_inter_card_eq_zero_of_disjoint_ground F₁ F₂ hd
  have h0int :
      ((∑ A ∈ F₁.edgeFinset, ∑ B ∈ F₂.edgeFinset, (A ∩ B).card) : Int) = 0 := by
    exact_mod_cast h0nat
  -- 置換して `- 0` を消す
  calc
    ((∑ A ∈ F₁.edgeFinset, ∑ B ∈ F₂.edgeFinset, (A ∪ B).card) : Int)
        =
      (F₂.numHyperedges : Int) * (∑ A ∈ F₁.edgeFinset, (A.card : Int))
      + (F₁.numHyperedges : Int) * (∑ B ∈ F₂.edgeFinset, (B.card : Int))
      - ((∑ A ∈ F₁.edgeFinset, ∑ B ∈ F₂.edgeFinset, (A ∩ B).card) : Int) := by
        simp_all only [Nat.cast_zero, sub_zero, Finset.sum_eq_zero_iff, SetFamily.mem_edgeFinset, Finset.card_eq_zero, and_imp]
    _ =
      (F₂.numHyperedges : Int) * (∑ A ∈ F₁.edgeFinset, (A.card : Int))
      + (F₁.numHyperedges : Int) * (∑ B ∈ F₂.edgeFinset, (B.card : Int))
      - 0 := by
        exact congrArg
          (fun t =>
            (F₂.numHyperedges : Int) * (∑ A ∈ F₁.edgeFinset, (A.card : Int))
            + (F₁.numHyperedges : Int) * (∑ B ∈ F₂.edgeFinset, (B.card : Int))
            - t) h0int
    _ =
      (F₂.numHyperedges : Int) * (∑ A ∈ F₁.edgeFinset, (A.card : Int))
      + (F₁.numHyperedges : Int) * (∑ B ∈ F₂.edgeFinset, (B.card : Int)) := by
        exact sub_zero _

lemma union_inj_on_edges_of_disjoint
  (F₁ F₂ : SetFamily α) (hd : Disjoint F₁.ground F₂.ground) :
  ∀ {p q : Finset α × Finset α},
    p ∈ F₁.edgeFinset.product F₂.edgeFinset →
    q ∈ F₁.edgeFinset.product F₂.edgeFinset →
    p.1 ∪ p.2 = q.1 ∪ q.2 → p = q := by
  classical
  intro p q hp hq hU
  rcases Finset.mem_product.mp hp with ⟨hp1, hp2⟩
  rcases Finset.mem_product.mp hq with ⟨hq1, hq2⟩
  -- A ⊆ ground₁, B ⊆ ground₂
  have hps1 : p.1 ⊆ F₁.ground :=
    F₁.inc_ground ((SetFamily.mem_edgeFinset_iff_sets (F := F₁)).1 hp1)
  have hps2 : p.2 ⊆ F₂.ground :=
    F₂.inc_ground ((SetFamily.mem_edgeFinset_iff_sets (F := F₂)).1 hp2)
  have hqs1 : q.1 ⊆ F₁.ground :=
    F₁.inc_ground ((SetFamily.mem_edgeFinset_iff_sets (F := F₁)).1 hq1)
  have hqs2 : q.2 ⊆ F₂.ground :=
    F₂.inc_ground ((SetFamily.mem_edgeFinset_iff_sets (F := F₂)).1 hq2)
  -- ground₁ と ground₂ は素に交わる
  have hdis : Disjoint F₁.ground F₂.ground := hd
  -- 交わり 0 を使って「union ∩ ground₁ = 左成分」が成り立つ
  have ext1 :
      (p.1 ∪ p.2) ∩ F₁.ground = p.1 := by
    apply Finset.ext
    intro a; constructor
    · intro ha
      rcases Finset.mem_inter.mp ha with ⟨hUmem, hG⟩
      rcases Finset.mem_union.mp hUmem with hmem | hmem
      · exact hmem
      · -- a ∈ p.2 かつ a ∈ ground₁ ⇒ ground₁∩ground₂ に属して矛盾
        have : a ∈ F₂.ground := hps2 hmem
        have : False := (Finset.disjoint_left.mp hdis) hG this
        exact this.elim
    · intro ha
      exact Finset.mem_inter.mpr ⟨Finset.mem_union.mpr (Or.inl ha), hps1 ha⟩
  have ext2 :
      (q.1 ∪ q.2) ∩ F₁.ground = q.1 := by
    -- 同様に右側でも成立
    apply Finset.ext
    intro a; constructor
    · intro ha
      rcases Finset.mem_inter.mp ha with ⟨hUmem, hG⟩
      rcases Finset.mem_union.mp hUmem with hmem | hmem
      · exact hmem
      · have : a ∈ F₂.ground := hqs2 hmem
        have : False := (Finset.disjoint_left.mp hdis) hG this
        exact this.elim
    · intro ha
      exact Finset.mem_inter.mpr ⟨Finset.mem_union.mpr (Or.inl ha), hqs1 ha⟩
  -- union の等式を両辺 `∩ ground₁` して左成分が一致
  have hL : p.1 = q.1 := by
    have := congrArg (fun t => t ∩ F₁.ground) hU
    -- (p.1 ∪ p.2)∩G₁ = (q.1 ∪ q.2)∩G₁
    -- それぞれ ext1, ext2
    exact (by
      -- 左辺→p.1，右辺→q.1
      have := this
      -- `ext1`,`ext2` は等式なので，対等置換で終了
      exact Eq.trans (Eq.symm ext1) (Eq.trans this ext2))
  -- 同様に ground₂ で右成分が一致
  have ext1' :
      (p.1 ∪ p.2) ∩ F₂.ground = p.2 := by
    apply Finset.ext
    intro a; constructor
    · intro ha
      rcases Finset.mem_inter.mp ha with ⟨hUmem, hG⟩
      rcases Finset.mem_union.mp hUmem with hmem | hmem
      · -- a ∈ p.1 かつ a ∈ ground₂ ⇒ 矛盾
        have : a ∈ F₁.ground := hps1 hmem
        have : False := (Finset.disjoint_left.mp hdis) this hG
        exact this.elim
      · exact hmem
    · intro ha
      exact Finset.mem_inter.mpr ⟨Finset.mem_union.mpr (Or.inr ha), hps2 ha⟩
  have ext2' :
      (q.1 ∪ q.2) ∩ F₂.ground = q.2 := by
    apply Finset.ext
    intro a; constructor
    · intro ha
      rcases Finset.mem_inter.mp ha with ⟨hUmem, hG⟩
      rcases Finset.mem_union.mp hUmem with hmem | hmem
      · have : a ∈ F₁.ground := hqs1 hmem
        have : False := (Finset.disjoint_left.mp hdis) this hG
        exact this.elim
      · exact hmem
    · intro ha
      exact Finset.mem_inter.mpr ⟨Finset.mem_union.mpr (Or.inr ha), hqs2 ha⟩
  have hR : p.2 = q.2 := by
    have := congrArg (fun t => t ∩ F₂.ground) hU
    exact (by
      exact Eq.trans (Eq.symm ext1') (Eq.trans this ext2'))
  -- まとめ
  cases p with
  | mk A B =>
    cases q with
    | mk C D =>
      cases hL; cases hR
      rfl

/-- 和積の総サイズ（Nat）：disjoint なら直積二重和に一致。 -/
lemma total_size_sumProd_eq_doubleSum_disjoint_nat
  (F₁ F₂ : SetFamily α) (hd : Disjoint F₁.ground F₂.ground) :
  (SetFamily.sumProd F₁ F₂).totalHyperedgeSize
    =
  ∑ A ∈ F₁.edgeFinset, ∑ B ∈ F₂.edgeFinset, (A ∪ B).card := by
  classical
  -- edge の等式と単射で image 和＝元集合の和
  have hedge :
    (SetFamily.sumProd F₁ F₂).edgeFinset
      =
      (F₁.edgeFinset.product F₂.edgeFinset).image
        (fun p : Finset α × Finset α => p.1 ∪ p.2) :=
    edgeFinset_sumProd F₁ F₂
  -- 単射性
  have hinj :
    ∀ {p q}, p ∈ F₁.edgeFinset.product F₂.edgeFinset →
             q ∈ F₁.edgeFinset.product F₂.edgeFinset →
             ((fun p : Finset α × Finset α => p.1 ∪ p.2) p
              =
              (fun p : Finset α × Finset α => p.1 ∪ p.2) q) → p = q :=
    union_inj_on_edges_of_disjoint F₁ F₂ hd
  -- 定義展開：totalHyperedgeSize は edge 上の card 和
  -- 和の像を単射性で引き戻す
  calc
    (SetFamily.sumProd F₁ F₂).totalHyperedgeSize
        = ∑ X ∈ (SetFamily.sumProd F₁ F₂).edgeFinset, X.card := rfl
    _ = ∑ X ∈ (F₁.edgeFinset.product F₂.edgeFinset).image (fun p => p.1 ∪ p.2), X.card := by
          exact congrArg (fun t => ∑ X ∈ t, X.card) hedge
    _ = ∑ p ∈ (F₁.edgeFinset.product F₂.edgeFinset),
            ((p.1 ∪ p.2).card) := by
          -- `sum_image`（単射）で引き戻す
          exact Finset.sum_image fun ⦃x₁⦄ a ⦃x₂⦄ => hinj a
    _ = ∑ A ∈ F₁.edgeFinset, ∑ B ∈ F₂.edgeFinset, (A ∪ B).card := by
          -- 直積上の和を二重和に
          simp_all only [Finset.product_eq_sprod, Finset.mem_product, SetFamily.mem_edgeFinset, and_imp, Prod.forall,
            Prod.mk.injEq, subset_refl]
          rw [Finset.sum_product]

/-- 和積の総サイズ（Int）：disjoint 版。 -/
lemma total_size_sumProd_eq_doubleSum_disjoint_int
  (F₁ F₂ : SetFamily α) (hd : Disjoint F₁.ground F₂.ground) :
  ((SetFamily.sumProd F₁ F₂).totalHyperedgeSize : Int)
    =
  (∑ A ∈ F₁.edgeFinset, ∑ B ∈ F₂.edgeFinset, (A ∪ B).card : Nat) := by
  classical
  -- Nat の等式を Int に持ち上げ
  have hnat := total_size_sumProd_eq_doubleSum_disjoint_nat (F₁ := F₁) (F₂ := F₂) hd
  exact_mod_cast hnat

/-- NDS の分解式（台集合が素に交わるとき） -/
lemma NDS_sumProd_of_disjoint
  (F₁ F₂ : SetFamily α) (hd : Disjoint F₁.ground F₂.ground) :
  (SetFamily.sumProd F₁ F₂).NDS
    =
    (F₂.numHyperedges : Int) * F₁.NDS
  + (F₁.numHyperedges : Int) * F₂.NDS  := by
  classical
  -- NDS の定義を展開
  -- 左辺の total を「二重和」に書き換え
  have hTot :
    ((SetFamily.sumProd F₁ F₂).totalHyperedgeSize : Int)
      =
    ((∑ A ∈ F₁.edgeFinset, ∑ B ∈ F₂.edgeFinset, (A ∪ B).card) : Int) := by

    let tss := total_size_sumProd_eq_doubleSum_disjoint_int (F₁ := F₁) (F₂ := F₂) hd
    rw [tss]
    simp_all only [Nat.cast_sum]

  -- 二重和の値は「disjoint 版のサイズ恒等式」で計算
  have hSize :=
    sum_card_union_disjoint_int (F₁ := F₁) (F₂ := F₂) hd
  -- ground の大きさ：disjoint なので `|V₁ ∪ V₂| = |V₁| + |V₂|`
  have hV :
    ((SetFamily.sumProd F₁ F₂).ground.card : Int)
      =
    (F₁.ground.card : Int) + (F₂.ground.card : Int) := by
    -- `sumProd.ground = F₁.ground ∪ F₂.ground`
    have : (SetFamily.sumProd F₁ F₂).ground
              = F₁.ground ∪ F₂.ground := rfl
    -- 交わりが 0 なのでカードは和
    have hdis : (F₁.ground ∩ F₂.ground).card = 0 := by
      apply Finset.card_eq_zero.mpr
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro a ha
      rcases Finset.mem_inter.mp ha with ⟨ha1, ha2⟩
      exact (Finset.disjoint_left.mp hd) ha1 ha2
    -- `card_union_add_card_inter` を Int へ
    -- `|U∪V| + |U∩V| = |U| + |V|`
    have := Finset.card_union_add_card_inter (F₁.ground) (F₂.ground)
    -- Int キャストして `|∩|=0` を消す
    -- 書き換え：
    --   |U∪V| = |U| + |V| - |∩|
    -- だが今は |∩|=0
    -- 直に Int 化して移項
    have hInt :
      ((F₁.ground ∪ F₂.ground).card : Int)
        =
      (F₁.ground.card : Int) + (F₂.ground.card : Int) := by
      -- `(u∪v).card + (u∩v).card = u.card + v.card`
      -- から `(u∪v).card = u.card + v.card - (u∩v).card`
      -- さらに `= ... - 0`
      have := this
      -- cast してから両辺から |∩| を引く
      have := sub_eq_of_eq_add' (a :=
        ((F₁.ground ∪ F₂.ground).card : Int))
        (b := (F₁.ground.card : Int) + (F₂.ground.card : Int))
        (c := ((F₁.ground ∩ F₂.ground).card : Int))
        (by simp_all only [Finset.card_eq_zero, Finset.card_union_of_disjoint, Finset.card_empty, add_zero, Nat.cast_add, Nat.cast_zero])
      -- 右端 `- |∩| = - 0`
      have hc : ((F₁.ground ∩ F₂.ground).card : Int) = 0 := by
        exact_mod_cast hdis
      -- 置換
      exact (by
        -- `(u∪v).card = (u.card+v.card) - 0`
        exact congrArg (fun t => t) (by
          -- ただの等式適用
          -- `this : a = b - c`
          -- `hc : c = 0`
          -- よって `a = b - 0 = b`
          have := this
          -- `b - 0 = b`
          -- 直接書き換えます
          simp_all only [Finset.card_eq_zero, Finset.card_union_of_disjoint, Finset.card_empty, add_zero,Nat.cast_add, sub_self, Nat.cast_zero]))    -- 最後に `sumProd.ground = _` を使って置き換え
    simp_all only [Finset.card_eq_zero, Finset.card_union_of_disjoint, Finset.card_empty, add_zero, Nat.cast_add]

  -- 仕上げ：NDS を両辺計算して整列
  -- NDS(sumProd) = 2*(二重和) - (#H₁*#H₂)*(|V₁|+|V₂|)
  -- 右辺 = (#H₂)*NDS(F₁) + (#H₁)*NDS(F₂)
  -- 完全に同一形に並びます
  -- 計算は加減法と分配だけです
  have hH :
    ((SetFamily.sumProd F₁ F₂).numHyperedges : Int)
      = (F₁.numHyperedges * F₂.numHyperedges : Nat) := by
    -- edge 本数は「像＝直積」の単射から card(image)=card(product)
    -- `edgeFinset_sumProd` と `card_product`
    have hedge :=
      edgeFinset_sumProd F₁ F₂
    have hinj :
      ∀ {p q}, p ∈ F₁.edgeFinset.product F₂.edgeFinset →
               q ∈ F₁.edgeFinset.product F₂.edgeFinset →
               ((fun p : Finset α × Finset α => p.1 ∪ p.2) p
                =
                (fun p : Finset α × Finset α => p.1 ∪ p.2) q) → p = q :=
      union_inj_on_edges_of_disjoint F₁ F₂ hd
    -- card(image)=card(domain)（単射）
    have hcard :
      (SetFamily.sumProd F₁ F₂).edgeFinset.card
        = (F₁.edgeFinset.product F₂.edgeFinset).card := by
      calc
        (SetFamily.sumProd F₁ F₂).edgeFinset.card
            = ((F₁.edgeFinset.product F₂.edgeFinset).image (fun p => p.1 ∪ p.2)).card := by
              exact congrArg Finset.card hedge
        _ = (F₁.edgeFinset.product F₂.edgeFinset).card := by
              exact Finset.card_image_iff.mpr (by
                intro p hp q hq hEq
                exact hinj hp hq hEq)
    -- 右辺を #s × #t に
    have := Finset.card_product (F₁.edgeFinset) (F₂.edgeFinset)
    -- まとめ
    exact (by
      -- `numHyperedges = card edgeFinset`
      -- cast せず Nat 等式として返す
      -- ここは Int 等式が欲しいので最後に `exact_mod_cast`
      -- まず Nat で：
      have hn :
        (SetFamily.sumProd F₁ F₂).numHyperedges
          = F₁.edgeFinset.card * F₂.edgeFinset.card := by
          -- `numHyperedges = card`
          -- なので hcard と card_product
          -- 2 つの等式を合わせる
          -- （rfl の置換で即座に得られます）
          exact Eq.trans (by rfl) (by
            exact Eq.trans hcard this)
      -- Int 化
      exact_mod_cast hn)
  -- ここから展開
  -- 書きやすいように略記
  set e₁ := F₁.numHyperedges
  set e₂ := F₂.numHyperedges
  set v₁ := F₁.ground.card
  set v₂ := F₂.ground.card
  -- NDS 定義
  unfold SetFamily.NDS
  -- 左辺の total を hTot で置換し，さらに hSize を代入
  -- 右辺は分配して揃える
  -- まず total の部分
  have hTot' :
    (2 * ((SetFamily.sumProd F₁ F₂).totalHyperedgeSize : Int))
      =
    2 *
      ((∑ A ∈ F₁.edgeFinset, ∑ B ∈ F₂.edgeFinset, (A ∪ B).card) : Int) := by
    exact congrArg (fun t : Int => 2 * t) hTot
  -- つづいてその二重和をサイズ恒等式で置換
  have hSize' :
    2 *
      ((∑ A ∈ F₁.edgeFinset, ∑ B ∈ F₂.edgeFinset, (A ∪ B).card) : Int)
      =
    2 * ((e₂ : Int) * (∑ A ∈ F₁.edgeFinset, (A.card : Int))
        + (e₁ : Int) * (∑ B ∈ F₂.edgeFinset, (B.card : Int))) := by
    -- 片側に 2 を掛けるだけ
    exact congrArg (fun t : Int => 2 * t) hSize
  -- ground の置換
  have hV' :
    ((SetFamily.sumProd F₁ F₂).ground.card : Int)
      = (v₁ : Int) + (v₂ : Int) := hV
  -- 辞書式に組み上げ
  calc
    2 * ((SetFamily.sumProd F₁ F₂).totalHyperedgeSize : Int)
      - ((SetFamily.sumProd F₁ F₂).numHyperedges : Int)
        * ((SetFamily.sumProd F₁ F₂).ground.card : Int)
      = (2 *
          ((∑ A ∈ F₁.edgeFinset, ∑ B ∈ F₂.edgeFinset, (A ∪ B).card) : Int))
        - ((e₁ * e₂ : Nat) : Int) * ((v₁ + v₂ : Nat) : Int) := by
          -- total を hTot'、num と ground を hH, hV' で置換
          -- `((v₁+v₂ : Nat) : Int) = (v₁ : Int) + (v₂ : Int)` は後で使う
          -- ここでは等式置換だけ
          have := hTot'
          have := hH
          have := hV'
          -- 逐語的置換
          simp_all only [Nat.cast_mul, Nat.cast_add, e₂, e₁, v₁, v₂]
    _ = (2 * ((e₂ : Int) * (∑ A ∈ F₁.edgeFinset, (A.card : Int))
              + (e₁ : Int) * (∑ B ∈ F₂.edgeFinset, (B.card : Int))))
        - ((e₁ : Int) * (e₂ : Int)) * ((v₁ : Int) + (v₂ : Int)) := by
          -- 左の 2*二重和 → hSize'、右は casts の整理（(n*m : Nat : Int)=(n:Int)*(m:Int) など）
          -- 置換の結果としての等式
          -- ここは変形のみ（演算の可換・結合で機械的に一致）
          simp_all only [Nat.cast_mul, Nat.cast_add, e₂, e₁, v₁, v₂]
    _ =
      (e₂ : Int) * (2 * (∑ A ∈ F₁.edgeFinset, (A.card : Int)))
      + (e₁ : Int) * (2 * (∑ B ∈ F₂.edgeFinset, (B.card : Int)))
      - ((e₁ : Int) * (e₂ : Int)) * ((v₁ : Int) + (v₂ : Int)) := by
          -- 左項の分配（2 を前に出す）
          -- ただの分配・交換（詳細展開は省略）
          simp_all only [Nat.cast_mul, sub_left_inj, e₂, e₁, v₁, v₂]
          rw [mul_add]
          ac_rfl
    _ =
      (e₂ : Int) * (2 * (∑ A ∈ F₁.edgeFinset, (A.card : Int)) - (e₁ : Int) * (v₁ : Int))
      + (e₁ : Int) * (2 * (∑ B ∈ F₂.edgeFinset, (B.card : Int)) - (e₂ : Int) * (v₂ : Int)) := by
          -- 右辺の `- e₁e₂*(v₁+v₂)` を 2 つに割って合流
          -- 代数恒等式：
          -- LHS = e₂*(2T₁) + e₁*(2T₂) - e₁e₂ v₁ - e₁e₂ v₂
          -- RHS = e₂*(2T₁ - e₁ v₁) + e₁*(2T₂ - e₂ v₂)
          -- 同一です
          ring_nf

    _ =
      (F₂.numHyperedges : Int) * F₁.NDS
      + (F₁.numHyperedges : Int) * F₂.NDS := by
          -- NDS の定義に戻す（`NDS F = 2*total - #H * |V|`）
          -- ただし total は `∑ (A.card : Int)` に一致（定義展開）
          -- 定義どおりの置換
          simp_all only [Nat.cast_mul, e₂, e₁, v₁, v₂]
          simp_all only [SetFamily.NDS_def]
          norm_cast

/-- principal と coIdeal の台集合は素に交わる。 -/
lemma disjoint_principal_coIdeal (S : SPO.FuncSetup α) (m : S.Elem) :
  Disjoint (S.principalIdeal m.1 m.2) (coIdeal S m) := by
  classical
  -- `coIdeal = ground \ principal` より直ちに
  unfold coIdeal
  exact Finset.disjoint_sdiff

/-- 適用版：`restrictToIdeal` と `restrictToCoIdeal` の NDS 分解。 -/
lemma NDS_restrict_sumProd_split
  (S : SPO.FuncSetup α) (m : S.Elem) (hm : S.maximal m)
  (hpos : isPoset S) (notuniq : ¬ (∃! mm : S.Elem, S.maximal mm)) :
  let F₁ := (restrictToIdeal S m hm).idealFamily
  let F₂ := (restrictToCoIdeal S m hpos notuniq).idealFamily
  (SetFamily.sumProd F₁ F₂).NDS
    =
  (F₂.numHyperedges : Int) * F₁.NDS
  + (F₁.numHyperedges : Int) * F₂.NDS := by
  classical
  intro F₁ F₂
  -- 台集合の素な交わり
  have hd :
    Disjoint F₁.ground F₂.ground := by
    -- ground(F₁)=principal, ground(F₂)=coIdeal
    change Disjoint (S.principalIdeal m.1 m.2) (coIdeal S m)
    exact disjoint_principal_coIdeal S m
  -- 主結果を適用
  exact NDS_sumProd_of_disjoint F₁ F₂ hd

end DirectProduct
end AvgRare
