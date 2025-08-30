import AvgRare.SPO.FuncSetup
import AvgRare.Basics.SetFamily
import AvgRare.Basics.Trace.Common
--import AvgRare.SPO.Forest
import AvgRare.PaperSync.IdealsTrace
import AvgRare.Forests.DirectProduct
import AvgRare.Forests.Induction

set_option maxHeartbeats 100000000

universe u

namespace AvgRare
namespace PaperSync
open Classical
open SPO
open DirectProduct
open FuncSetup

variable {α : Type u} [DecidableEq α]

open scoped BigOperators

/-- `edgeFinset ⊆ powerset`（定義から直ちに従う） -/
lemma edge_subset_powerset (F : SetFamily α) :
  F.edgeFinset ⊆ F.ground.powerset := by
  intro A hA
  -- edgeFinset = powerset.filter _
  rcases Finset.mem_filter.mp hA with ⟨hPow, _⟩
  exact hPow

/-- 単元集合の冪集合は `{∅, {x}}` -/
lemma powerset_singleton (x : α) :
  ({x} : Finset α).powerset = ({∅, {x}} : Finset (Finset α)) := by
  apply Finset.ext
  intro A
  constructor
  · -- → 方向：A ⊆ {x} なら A = ∅ または A = {x}
    intro hA
    have hsub : A ⊆ ({x} : Finset α) := (Finset.mem_powerset.mp hA)
    by_cases hxA : x ∈ A
    · -- A = {x}
      have h_eq : A = ({x} : Finset α) := by
        -- 「A は x を含み、かつ A の任意の元は x」から一意性で単元集合
        apply Finset.eq_singleton_iff_unique_mem.mpr
        constructor
        · exact hxA
        · intro y hy
          have : y ∈ ({x} : Finset α) := hsub hy
          exact (Finset.mem_singleton.mp this)
      -- {∅, {x}} への所属
      -- （この時は右側の {x} に一致）
      simp [h_eq]
    · -- x ∉ A → A = ∅
      have h_empty : A = (∅ : Finset α) := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro y hy
        have : y ∈ ({x} : Finset α) := hsub hy
        have : y = x := Finset.mem_singleton.mp this
        have hxInA : x ∈ A := by
          cases this
          exact hy
        exact hxA hxInA
      -- {∅, {x}} への所属（この時は左側の ∅ に一致）
      simp [h_empty]
  · -- ← 方向：A = ∅ または A = {x} なら A ⊆ {x}
    intro h
    -- {∅, {x}} のメンバ判定を「＝∅ ∨ ＝{x}」に直す
    have h' : A = (∅ : Finset α) ∨ A = ({x} : Finset α) := by
      -- {∅, {x}} は `insert ∅ { {x} }` なので `mem_insert` と `mem_singleton` で分解
      rcases (Finset.mem_insert.mp h) with h0 | h1
      · exact Or.inl h0
      · exact Or.inr (Finset.mem_singleton.mp h1)
    -- A ⊆ {x} を示して powerset に入れる
    apply (Finset.mem_powerset.mpr)
    cases h' with
    | inl h0 =>
        intro y hy
        -- A = ∅ なら自動的に空包含
        -- `hy : y ∈ A` は矛盾なので何でも従う
        have : y ∈ (∅ : Finset α) := by
          -- `rw [h0]` で十分
          subst h0
          simp_all only [Finset.mem_insert, Finset.mem_singleton, true_or, Finset.notMem_empty]
        exact (False.elim (by simp_all only [Finset.mem_insert, Finset.mem_singleton, true_or, Finset.notMem_empty]))
    | inr h1 =>
        -- A = {x} なら {x} ⊆ {x}
        intro y hy
        -- 目標は y ∈ {x}
        -- hy : y ∈ A = {x}
        -- よって明らか
        simpa [h1] using hy

/-- 台集合が1元なら `edgeFinset = {∅, ground}` -/
lemma edgeFinset_of_card_one
  (S : SPO.FuncSetup α)
  (hS : (S.idealFamily).ground.card = 1) :
  (S.idealFamily).edgeFinset
    = ({∅, (S.idealFamily).ground} : Finset (Finset α)) := by
  -- ground = {x} と書ける
  obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hS
  -- まず powerset を単元の形に落とす
  have hp :
    (S.idealFamily).ground.powerset
      = ({∅, {x}} : Finset (Finset α)) := by
    -- `hx : (S.idealFamily).ground = {x}`
    -- 左辺を書き換えてから `powerset_singleton`
    -- LHS = ({x}).powerset
    -- RHS = {∅, {x}}
    -- `rw` を使って丁寧につなぐ
    calc
      (S.idealFamily).ground.powerset
          = (({x} : Finset α)).powerset := by
            -- ground = {x}
            -- ここは単なる書換え
            simp [hx]
      _ = ({∅, {x}} : Finset (Finset α)) := powerset_singleton x
  -- `edgeFinset ⊆ powerset` と ∅, ground の両メンバ性から両側包含で同値
  apply Finset.ext
  intro A
  constructor
  · -- → 方向
    intro hA
    -- powerset に入る
    have hPow : A ∈ (S.idealFamily).ground.powerset :=
      (edge_subset_powerset (F := S.idealFamily)) hA
    -- powerset を `{∅, {x}}` に書き換えて場合分け
    -- 最後に ground = {x} を戻す
    have : A ∈ ({∅, {x}} : Finset (Finset α)) := by
      simpa [hp]
        using hPow
    -- {∅, {x}} のメンバを {∅, ground} のメンバへ
    -- （ground = {x} なので置換）
    simpa [hx]
      using this
  · -- ← 方向
    intro hA
    -- {∅, ground} のメンバを {∅, {x}} に戻し、powerset に入り、filter で回収
    have hA' : A ∈ ({∅, {x}} : Finset (Finset α)) := by
      simpa [hx] using hA
    have hPow : A ∈ (S.idealFamily).ground.powerset := by
      -- `hp : powerset = {∅, {x}}` の逆向きで
      simpa [hp]
        using hA'
    -- あとは「ideal である」フィルタ条件を満たすことを言う必要があるが、
    -- このケース（台集合1）では ∅ と ground のみで、いずれも既知の補題で edge に入る。
    -- よって A が ∅ か ground のどちらかであることに絞ればよい。
    -- {∅, ground} のメンバ性から分岐：
    have hEq : A = (∅ : Finset α) ∨ A = (S.idealFamily).ground := by
      -- 今の hA は {∅, ground} のメンバ
      -- 直接 Or に直す
      rcases (Finset.mem_insert.mp hA) with h0 | h1
      · exact Or.inl h0
      · exact Or.inr (Finset.mem_singleton.mp h1)
    cases hEq with
    | inl h0 =>
        -- ∅ は既知の補題で edge へ
        -- `empty_mem_ideal_edge`
        -- 目標 A ∈ edgeFinset
        -- A = ∅ なので書換えで閉じる
        -- using を避けるため rewrite してから exact
        -- `rw` で A を ∅ に差し替え
        -- `change` でも可
        -- ここは素直に `rw [h0]` の後、既知補題を入れる
        -- （`exact` は最後に使う）
        --
        -- 書換え
        -- （`change` でゴールを書き換えても良いが、`rw` で十分）
        -- A を ∅ に置換
        have : (∅ : Finset α) ∈ (S.idealFamily).edgeFinset :=
          FuncSetup.empty_mem_ideal_edge S
        -- 仕上げ
        -- `h0 ▸ this` で A 版に戻す
        exact h0 ▸ this
    | inr h1 =>
        -- ground も既知補題で edge へ
        have : (S.idealFamily).ground ∈ (S.idealFamily).edgeFinset :=
          FuncSetup.ground_mem_ideal_edge S
        exact h1 ▸ this

/-- 台集合が1個のとき，`totalHyperedgeSize = 1`，`numHyperedges = 2` -/
lemma sizes_of_card_one
  (S : FuncSetup α)
  (hS : (S.idealFamily).ground.card = 1) :
  (S.idealFamily).totalHyperedgeSize = 1
  ∧ (S.idealFamily).numHyperedges = 2 := by
  -- edgeFinset = {∅, ground}
  have hE :
    (S.idealFamily).edgeFinset
      = ({∅, (S.idealFamily).ground} : Finset (Finset α)) :=
    edgeFinset_of_card_one (S := S) hS
  -- ground ≠ ∅ （card = 1 より）
  have hne : (S.idealFamily).ground ≠ (∅ : Finset α) := by
    intro h
    have : (S.idealFamily).ground.card = 0 := by
      simp [h]
    exact Nat.one_ne_zero (by simp_all only [Finset.card_empty, zero_ne_one])
  constructor
  · -- totalHyperedgeSize = 1
    -- ∑ A ∈ {∅, ground}, A.card = 0 + 1
    -- `simp` で評価
    -- 注意：∅ と ground は異なる（上で hne）
    -- `by classical` は最上で有効
    have : (S.idealFamily).totalHyperedgeSize
        = ∑ A ∈ ({∅, (S.idealFamily).ground} : Finset (Finset α)), A.card := by
      -- 定義展開と edge の書換え
      -- totalHyperedgeSize := ∑ A ∈ edgeFinset, A.card
      -- ここは `rfl` で定義→書換え
      -- まず定義を展開
      -- `change` で左辺を書換える
      change
        (∑ A ∈ (S.idealFamily).edgeFinset, A.card)
          = _
      -- 右辺へ置換
      simp [hE]
    -- これで右辺が二点和になった
    -- ground の濃度は 1（hS）なので `Finset.card_singleton`
    -- `simp` で 0 + (ground.card) を 1 に落とす
    -- 仕上げ
    -- `simp` の前にこの等式を使って右辺に差し替え
    -- 以後はこの等式で書き換えてから `simp`
    -- 実行
    -- 書換え
    -- （`simp` は「using」ではないので可）
    -- ground.card = 1 は hS
    -- `Finset.card_empty` は 0
    -- `Finset.card_unordered` 不要
    -- まとめて `simp` に渡す
    have := this
    -- 右辺をそのまま評価
    -- `simp` のターゲットにするため `rw` で書換え
    -- まず totalHyperedgeSize を右辺へ
    -- 注意：`rw` はゴールが等式ではないので、ここは `have` を壊して直接使う方が簡単
    -- 直接 `simp` で閉じる：
    -- `simp` で `{∅, ground}` 上の和を評価
    -- ヒントとして ground ≠ ∅ と hS を渡す
    -- 仕上げ：`simp` で 0 + 1
    -- 実際の一行：
    have hsum :
      ∑ A ∈ ({∅, (S.idealFamily).ground} : Finset (Finset α)), A.card = 1 := by
      -- メンバのカードは 0 と ground.card
      -- ground.card = 1
      -- ∅ と ground は異なる
      -- `simp` が `{a,b}` の和を `...` にしてくれる
      -- `by_cases` は不要
      -- `simp` の引数で補助事実を渡す
      -- まず「∅ ≠ ground」を `ne_of_lt` 等にせず、`hne` の対称で渡す
      have hne' : (∅ : Finset α) ≠ (S.idealFamily).ground := by
        exact ne_comm.mp hne
      -- 評価
      -- `Finset.card_empty` と `hS`
      -- `simp` は `Finset.mem_pair` などを使って展開してくれる
      -- `simp [hne', hS]`
      -- ただし和の評価で `Finset.sum_pair` 相当が走る
      -- 実行
      simp [hne', hS]
    -- 最終的に totalHyperedgeSize = 1
    -- 先に得た等式で差し替えて確定
    -- this : totalHyperedgeSize = 上の和
    -- よって両辺とも 1
    -- 書換えのあと `exact` で閉じる
    -- `rw` で置換
    -- `rw [this]` によってゴールは `上の和 = 1`
    -- すでに `hsum : 上の和 = 1` があるので終了
    -- 実行
    -- まずゴールを書き換え
    have : (S.idealFamily).totalHyperedgeSize
        = ∑ A ∈ ({∅, (S.idealFamily).ground} : Finset (Finset α)), A.card := this
    -- 置換して確定
    -- `rw` だと等式の左辺に適用したいが、今はゴールが等式なので `calc` でも良い
    -- シンプルに：
    -- 置換
    -- （ローカルで再 `rw`）
    -- ここは一行で
    simpa [this] using hsum
  · -- numHyperedges = 2
    -- edgeFinset の濃度が 2（{∅, ground} の濃度）
    have : (S.idealFamily).numHyperedges
        = ({∅, (S.idealFamily).ground} : Finset (Finset α)).card := by
      change (S.idealFamily).edgeFinset.card = _
      simp [hE]
    -- ∅ と ground は異なるのでちょうど 2
    have hcard :
      ({∅, (S.idealFamily).ground} : Finset (Finset α)).card = 2 := by
      have hne' : (∅ : Finset α) ≠ (S.idealFamily).ground := by
        exact ne_comm.mp hne
      -- `simp` でカード 2
      simp [hne']
    -- 仕上げ
    -- `numHyperedges = 2`
    -- 置換して終了
    simp [this, hcard]

/-- **main\_base\_case**：台集合が 1 のとき NDS = 0 -/
lemma main_base_case
  (S : SPO.FuncSetup α)
  (hS : (S.idealFamily).ground.card = 1) :
  (S.idealFamily).NDS = 0 := by
  -- 上で出したサイズ評価を使って定義に代入するだけ
  obtain ⟨hSize, hNum⟩ := sizes_of_card_one (S := S) hS
  -- NDS = 2 * totalHyperedgeSize - numHyperedges * ground.card
  -- ここで totalHyperedgeSize = 1, numHyperedges = 2, ground.card = 1
  -- よって 2 * 1 - 2 * 1 = 0
  -- すべて Int に持ち上がっているので `simp` で評価できる
  -- 定義展開
  -- 注意：`NDS` の定義は `Int` への `↑` を含むので `simp` でまとめて計算
  -- 実行
  simp [SetFamily.NDS, hSize, hNum, hS]

----------------------------------

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

/-- `posetTraceOfUnique` は `isPoset` を保つ。 -/
--このファイル内では使ってない。準主定理の帰納法で使う。
lemma isPoset_posetTraceOfUnique
  (S : FuncSetup α) [Fintype S.Elem] (geq2: S.ground.card ≥ 2)
  (hpos : isPoset S) (hexu : ∃! m : S.Elem, S.maximal m) :
  isPoset (Induction.posetTraceOfUnique S geq2 hexu ) := by
  classical
  have hm : S.maximal (Classical.choose hexu.exists) := Classical.choose_spec hexu.exists
  -- `isPoset_posetTraceCore` を適用
  dsimp [Induction.posetTraceOfUnique]
  have pos': isPoset_excess S := by
    exact isPoset_of_le_antisymm S hpos
  let ipt := Induction.isPoset_posetTraceCore S hpos (m := Classical.choose hexu.exists)
  exact @ipt geq2

lemma secondary_main_theorem
  (S : SPO.FuncSetup α) [Fintype S.Elem]
  (hpos : isPoset S) :
  (S.idealFamily).NDS ≤ 0 := by

  classical
    ------------------------------------------------------------------
    -- 強い帰納法を「一般形の補題」として定義（refine を使わない）
    ------------------------------------------------------------------
  have main :
    ∀ n : Nat,
      ∀ (T : FuncSetup α) [Fintype T.Elem],
        isPoset T → T.ground.card = n → (T.idealFamily).NDS ≤ 0 :=
    fun n =>
      Nat.strongRecOn n
        (motive := fun n =>
          ∀ (T : FuncSetup α) [Fintype T.Elem],
            isPoset T → T.ground.card = n → (T.idealFamily).NDS ≤ 0)
        (fun n ih T _ hposT hcard => by
            -- ここからが「これまで書いていた本体（ベース / ステップ）」です。
            -- n=1 の基底
            by_cases h1 : T.ground.card = 1
            · have : (T.idealFamily).ground.card = 1 := by
                -- idealFamily の ground は T.ground と一致（既存の等式で書換）
                -- 必要なら既存補題名に差し替え
                exact h1
              have h0 : (T.idealFamily).NDS = 0 :=
                main_base_case (S := T) this
              -- 目標に合わせて ≤ 0 に直す
              exact (by
                have := h0
                calc
                  (T.idealFamily).NDS = 0 := this
                  _ ≤ 0 := le_rfl)
            -- n ≥ 2 の場合
            · have hn : T.ground.card = n := hcard
              have hposCard : 0 < T.ground.card := by
                have : T.ground.Nonempty := by
                  let nt := T.nonempty
                  exact Finset.nonempty_coe_sort.mp nt
                exact Finset.card_pos.mpr this
              have hge1 : 1 ≤ T.ground.card := Nat.succ_le_of_lt hposCard
              have hgt1 : 1 < T.ground.card := lt_of_le_of_ne hge1 (by symm; exact h1)
              have hge2 : 2 ≤ T.ground.card := Nat.succ_le_of_lt hgt1
              -- 極大が一意かどうかで分岐
              by_cases hexu : ∃! m : T.Elem, T.maximal m
              -- （A）極大一意：トレースで 1 減らして単調性＋帰納法
              ·
                let T' := Induction.posetTraceOfUnique T hge2 hexu
                have hpos' : isPoset T' :=
                  isPoset_posetTraceOfUnique (S := T) (geq2 := hge2)
                    (hpos := hposT) (hexu := hexu)
                have hdec : T'.ground.card = T.ground.card - 1 :=
                  Induction.ground_card_after_trace_of_max (S := T)
                    (m := Classical.choose hexu.exists) (geq2 := hge2)
                -- `T'.ground.card < n`
                have hlt : T'.ground.card < n := by
                  -- 書換のあと `Nat.sub_lt` を使う代わりに n の等式で落とす
                  -- `hn : T.ground.card = n`
                  -- 右辺を書換：`T'.ground.card = n - 1`
                  -- よって `< n` は `Nat.sub_lt` の自明な場合（n≥1）から従う
                  -- 実際には `rw [hn] at hdec; exact Nat.sub_lt (Nat.succ_le.mp hge2) (Nat.zero_lt_one)`
                  -- などで閉じられます。環境の好みで調整してください。
                  have : T'.ground.card = n - 1 := by
                    -- 右辺を書換
                    simpa [hn] using hdec
                  -- n≥2 なので n-1 < n
                  have : T'.ground.card < n := by
                    -- `rw [this]` のあと `Nat.pred_lt`/`Nat.sub_lt` 系で閉じる
                    -- ここは一行で：

                    simp [this]
                    exact Nat.lt_of_lt_of_eq hposCard hcard
                  exact this
                -- 帰納法適用
                have hNDS_T' : (T'.idealFamily).NDS ≤ 0 := by
                  simp_all only [SetFamily.NDS_def, tsub_le_iff_right, zero_add, tsub_lt_self_iff,
                    Nat.lt_add_one, and_self, T']
                  apply ih
                  on_goal 2 => { simp_all only
                  }
                  on_goal 2 => {
                    simp_all only
                    rfl
                  }
                  · simp_all only [tsub_lt_self_iff, Nat.lt_add_one, and_self]


                -- トレースで NDS は減らない
                have hmono :
                (T.idealFamily).NDS ≤ (T'.idealFamily).NDS :=
                  Induction.nds_trace_nondecreasing_uniqueMax
                  (S := T) (geq2 := hge2) (hpos := hposT) (hexu := hexu)

                exact le_trans hmono hNDS_T'
              -- （B）極大複数：ideal / coideal に分割し、積公式で合流
              ·

                --極大が複数取れることを示す必要あり。
                have hexu: (¬∃! mm, T.maximal mm) := by
                  intro h
                  exact hexu (by exact h)

                -- 最大元は存在
                have hne : T.ground.Nonempty := by exact Finset.card_pos.mp hposCard--T.nonempty
                obtain ⟨m, hm⟩ :=
                  Induction.exists_maximal_of_finite (S := T) (hpos := hposT) (hne := hne)
                -- 制限
                let T₁ := restrictToIdeal T m hm
                let T₂ := restrictToCoIdeal T m hposT-- (notuniq := by exact hexu)
                -- どちらも台集合が真に小さい
                have hlt₁ :
                  T₁.ground.card < T.ground.card :=
                  restrictToIdeal_card_lt_of_not_unique
                    (S := T) (m := m) (hm := hm) (hpos := hposT) (notconnected := by exact hexu)
                have hlt₂ :
                  (T₂ hexu).ground.card < T.ground.card :=
                  restrictToCoIdeal_card_lt
                    (S := T) (m := m) (hpos := hposT) (notconnected := by exact hexu)
                -- poset 性（新補題で反対称性を確保）
                have hpos₁ : isPoset T₁ := (antisymm_restrictToIdeal_of_isPoset (S := T) hposT m hm)
                have hpos₂ : isPoset (T₂ hexu):=  (antisymm_restrictToCoIdeal_of_isPoset (S := T) hposT m (notuniq := by exact hexu))
                -- 帰納法を両方に適用
                have hcard1: T₁.ground.card < n := by
                  subst hcard
                  simp_all only [Finset.card_pos, Finset.one_le_card, maximal_iff, le_iff_leOn_val, Subtype.forall, SetFamily.NDS_def,
                    tsub_le_iff_right, zero_add, T₁, T₂]
                have isPoset1 : isPoset T₁ := by
                   simp_all only [ maximal_iff, le_iff_leOn_val, Subtype.forall, SetFamily.NDS_def,
                  tsub_le_iff_right, zero_add, T₁, T₂]
                have hNDS₁ : (T₁.idealFamily).NDS ≤ 0 := by
                  exact ih T₁.ground.card hcard1 T₁ isPoset1 rfl
                have hNDS₂ : ((T₂ hexu).idealFamily).NDS ≤ 0 :=
                  ih (T₂ hexu).ground.card
                    (by simpa [hn] using hlt₂) (T₂ hexu) (by
                      simp_all only [ maximal_iff, le_iff_leOn_val, Subtype.forall, SetFamily.NDS_def,
                      tsub_le_iff_right, zero_add, T₁, T₂]
                    ) rfl

                let F₁ := (T₁.idealFamily)
                let F₂ := ((T₂ hexu).idealFamily)

                -- S のイデアル族が ideal/coideal の sumProd に分解される等式（既存の分解補題名に置換）
                -- 例: idealFamily_sumProd_restrict (S := T) (m := m) (hm := hm) (hpos := hposT) (notuniq := hexu)


                -- edgeFinset の等式（今回使いたい補題）
                have hEdges :
                  (SetFamily.sumProd F₁ F₂).edgeFinset
                    =
                    (F₁.edgeFinset.product F₂.edgeFinset).image
                      (fun p : Finset α × Finset α => p.1 ∪ p.2) :=
                  edgeFinset_sumProd F₁ F₂

                have hNDS_congr :
                (T.idealFamily).NDS
                  =
                (SetFamily.sumProd (T₁.idealFamily) ((T₂ hexu).idealFamily)).NDS :=
                 DirectProduct.idealFamily_eq_sumProd_on_NDS
                  (S := T) (m := m) (hm := hm) (hpos := hposT) (notuniq := by exact hexu)

                -- いただいた新補題：sumProd の NDS が “積公式” になる
                have hProd :
                  (SetFamily.sumProd F₁ F₂).NDS
                    =
                  (F₂.numHyperedges : Int) * F₁.NDS
                  + (F₁.numHyperedges : Int) * F₂.NDS :=
                    NDS_restrict_sumProd_split (S := T) (m := m) (hm := hm)
                    (hpos := hposT) (notuniq := by exact hexu)

                -- 係数は非負、項は ≤ 0
                have hcoef₁ : 0 ≤ (((T₂ hexu).idealFamily).numHyperedges:Int) := by
                  exact Int.natCast_nonneg (T₂ hexu).idealFamily.numHyperedges
                have hcoef₂ : 0 ≤ ((T₁.idealFamily).numHyperedges:Int) := by
                  exact Int.natCast_nonneg T₁.idealFamily.numHyperedges

                have hrhs_le :
                  ((T₂ hexu).idealFamily).numHyperedges * (T₁.idealFamily).NDS
                  + (T₁.idealFamily).numHyperedges * ((T₂ hexu).idealFamily).NDS ≤ 0 := by
                  have h1' :
                    (((T₂ hexu).idealFamily).numHyperedges:Int) * (T₁.idealFamily).NDS ≤ 0 := by

                      exact Int.mul_nonpos_of_nonneg_of_nonpos hcoef₁ hNDS₁
                  have h2' :
                    ((T₁.idealFamily).numHyperedges:Int) * ((T₂ hexu).idealFamily).NDS ≤ 0 := by
                     exact Int.mul_nonpos_of_nonneg_of_nonpos hcoef₂ hNDS₂
                  exact Int.add_nonpos h1' h2'
                  --refine False.elim ih

                calc
                  (T.idealFamily).NDS
                      --= (SetFamily.sumProd F₁ F₂).NDS := by exact hEdges
                      = ((T₂ hexu).idealFamily).numHyperedges * (T₁.idealFamily).NDS
                        + (T₁.idealFamily).numHyperedges * ((T₂ hexu).idealFamily).NDS := Eq.trans hNDS_congr hProd
                  _ ≤ 0 := by exact hrhs_le
        )
  ------------------------------------------------------------------
  -- 仕上げ：`main` を `S.ground.card` に適用
  ------------------------------------------------------------------
  exact main S.ground.card S (by simp_all only [SetFamily.NDS_def, tsub_le_iff_right, zero_add]) rfl

/- 主定理（言明）：
    `f : V → V` から誘導された前順序のイデアル族の NDS は非正。 -/
theorem main_nds_nonpos {α : Type u} [DecidableEq α]
  (S : SPO.FuncSetup α) :
  (S.idealFamily).NDS ≤ 0 := by
  apply PaperSync.main_nds_nonpos_of_secondary
  intro T hT
  have hT' : isPoset T := by
    dsimp [isPoset]
    dsimp [has_le_antisymm]
    exact antisymm_of_isPoset T hT
  exact secondary_main_theorem T hT'

end PaperSync
end AvgRare
