import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import LeanCopilot

universe u

open scoped BigOperators

namespace AvgRare

/-
SetFamily.lean  —  基本集合族とNDS。

集合族に関する基本的な定義と計数を行う。
- ここでは poset/ideal など順序に依存する概念は扱いません（Ideals 側へ）。
- トレースは Commonへ。
- FuncSetup が出てくるものは、FuncSetupへ。
-/

variable {α : Type u} [DecidableEq α]

/-- 有限台集合 `ground` 上の集合族。`sets A` は `A` が族のメンバである述語。
    計数・列挙のため、`edgeFinset` を powerset からの filter で構成できるように、
    `decSets`（可判別性）と `inc_ground`（台集合に含まれること）を仮定する。 -/
@[ext]
structure SetFamily (α : Type u) [DecidableEq α] where
  ground     : Finset α
  sets       : Finset α → Prop
  decSets    : DecidablePred sets
  inc_ground : ∀ {A : Finset α}, sets A → A ⊆ ground

namespace SetFamily

variable (F : SetFamily α)

attribute [simp] SetFamily.ground

instance instDecidablePred_sets (F : SetFamily α) : DecidablePred F.sets :=
  F.decSets


/-- 列挙用：族のメンバ全体を `powerset` から述語で filter して得る Finset。 -/
def edgeFinset : Finset (Finset α) :=
  F.ground.powerset.filter (fun A => decide (F.sets A))

/-- `edgeFinset` の要素は台集合に含まれる。 -/
lemma subset_ground_of_mem_edge {A : Finset α}
    (hA : A ∈ F.edgeFinset) : A ⊆ F.ground := by
  classical
  rcases Finset.mem_filter.mp hA with ⟨hPow, _⟩
  exact Finset.mem_powerset.mp hPow

/-- `edgeFinset` と述語 `sets` の一致。以後の計数で便利。 -/
lemma mem_edgeFinset_iff {A : Finset α} :
    A ∈ F.edgeFinset ↔ F.sets A := by
  classical
  constructor
  · intro h
    rcases Finset.mem_filter.mp h with ⟨hPow, hDec⟩
    -- decide (F.sets A) = true から F.sets A を回収
    simp_all only [Finset.mem_powerset, decide_eq_true_eq]
  · intro hA
    have hSub : A ⊆ F.ground := F.inc_ground hA
    have hPow : A ∈ F.ground.powerset := Finset.mem_powerset.mpr hSub
    have hDec : decide (F.sets A) = true := by simp_all only [Finset.mem_powerset, decide_true]

    exact Finset.mem_filter.mpr ⟨hPow, hDec⟩

/-- ハイパーエッジ数。 -/
def numHyperedges : Nat :=
  F.edgeFinset.card

/-- サイズ総和。 -/
def totalHyperedgeSize : Nat :=
  ∑ A ∈ F.edgeFinset, A.card

/-- 要素 `x` の次数（その要素を含むエッジの個数）。 -/
def degree (x : α) : Nat :=
  ∑ A ∈ F.edgeFinset, (if x ∈ A then (1 : Nat) else 0)

/-- NDS（正規化された次数和）：
`2 * (サイズ総和) - (エッジ数) * (台集合の大きさ)` を `Int` で定義。 -/
def NDS (F : SetFamily α) : Int :=
  2 * (F.totalHyperedgeSize : Int) - (F.numHyperedges : Int) * (F.ground.card : Int)

/-- Rare（稀）要素：`deg(x) ≤ |E|/2` を（両辺 2 倍して）自然数の不等式で表現。 -/
def Rare (F : SetFamily α) (x : α) : Prop :=
  2 * F.degree x ≤ F.numHyperedges

variable (F : SetFamily α)

@[simp] lemma NDS_def :
    NDS F = 2 * (F.totalHyperedgeSize : Int)
             - (F.numHyperedges : Int) * (F.ground.card : Int) := rfl

/-- `degree` を「含むエッジの個数」として書き直した版。 -/
lemma degree_eq_card_filter (x : α) :
    F.degree x = (F.edgeFinset.filter (fun A => x ∈ A)).card := by
  classical
  unfold degree
  -- `∑ (if p then 1 else 0)` を `∑ over s.filter p 1` に移す
  have h :
      (∑ A ∈ F.edgeFinset, (if x ∈ A then (1 : Nat) else 0))
        = (∑ A ∈ F.edgeFinset.filter (fun A => x ∈ A), (1 : Nat)) := by
    -- `sum_filter`：左辺 ↔ 右辺
    -- `simp` の向きの都合で `symm` を使う
    simp_all only [Finset.sum_boole, Nat.cast_id, Finset.sum_const, smul_eq_mul, mul_one]
  -- 右辺は定数 1 の総和＝個数
  simp_all only [Finset.sum_boole, Nat.cast_id, Finset.sum_const, smul_eq_mul, mul_one]

/-- `edgeFinset` は powerset の部分集合。 -/
lemma edgeFinset_subset_powerset :
    F.edgeFinset ⊆ F.ground.powerset := by
  classical
  intro A hA
  exact (Finset.mem_filter.mp hA).1

/-- `edgeFinset` 上のメンバは台集合に含まれる（便利な再掲）。 -/
lemma mem_edgeFinset_subset_ground {A : Finset α}
    (hA : A ∈ F.edgeFinset) : A ⊆ F.ground :=
  F.subset_ground_of_mem_edge hA

/-- 台集合の制限。ハイパーエッジは元のエッジの部分集合で、かつ `U` に含まれるもの。 -/
--どこで必要なのか考える。
noncomputable def restrict (U : Finset α) : SetFamily α := by
  classical
  refine
  { ground := U
    , sets   := fun B => ∃ A : Finset α, F.sets A ∧ B ⊆ A ∧ B ⊆ U
    , decSets := Classical.decPred _
    , inc_ground := ?_ }
  intro B hB
  rcases hB with ⟨A, hA, hBsubA, hBsubU⟩
  exact hBsubU

@[simp] lemma mem_edgeFinset :
  A ∈ F.edgeFinset ↔ A ⊆ F.ground ∧ F.sets A := by
  classical
  constructor
  · intro h
    rcases Finset.mem_filter.mp h with ⟨hPow, hDec⟩
    have hSub : A ⊆ F.ground := Finset.mem_powerset.mp hPow
    have hSets : F.sets A := by
      -- ここは decide ↔ 命題の橋渡しを simp に任せる
      simpa using (show decide (F.sets A) = true from hDec)
    exact ⟨hSub, hSets⟩
  · intro h
    rcases h with ⟨hSub, hSets⟩
    have hPow : A ∈ F.ground.powerset := Finset.mem_powerset.mpr hSub
    have hDec : decide (F.sets A) = true := by simpa using hSets
    exact Finset.mem_filter.mpr ⟨hPow, hDec⟩

@[simp] lemma mem_edgeFinset_iff_sets : (A ∈ F.edgeFinset) ↔ F.sets A := by
  classical
  constructor
  · intro h; have := (F.mem_edgeFinset (A := A)).1 h; exact this.2
  · intro h; have : A ⊆ F.ground := F.inc_ground h
    exact (F.mem_edgeFinset (A := A)).2 ⟨this, h⟩

/-- 並行性：族 `F` において「`u` を含むエッジの集合」と
「`v` を含むエッジの集合」が一致する。 -/
@[simp] def Parallel (F : SetFamily α) (u v : α) : Prop :=
  {A : Finset α | F.sets A ∧ u ∈ A} = {A : Finset α | F.sets A ∧ v ∈ A}

lemma parallel_refl (F : SetFamily α) (u : α) : Parallel F u u := rfl
lemma parallel_symm {F : SetFamily α} {u v : α} :
    Parallel F u v → Parallel F v u := fun h => h.symm



section CountLemmas

variable {β : Type*}
/- 使ってないみたい。
/- 和 `∑ a∈s, (if p a then 1 else 0)` は `s.filter p` の個数に一致。 -/
lemma sum_indicator_card_filter (s : Finset β) (p : β → Prop) [DecidablePred p] :
    ∑ a ∈ s, (if p a then (1 : Nat) else 0) = (s.filter p).card := by
  classical
  refine Finset.induction_on s ?h0 ?hstep
  · -- 空集合
    simp
  · intro a s ha_notmem ih
    by_cases hpa : p a
    · -- p a = true
      have : (s.filter p).card.succ
            = (insert a s |>.filter p).card := by
        -- filter_insert（p a=true）→ a が 1 個増える（a∉sなので重複なし）
        have hfi : (insert a s).filter p = insert a ((s.filter p)) := by
          -- `Finset.filter_insert` と `hpa`、`ha_notmem`
          -- `simp` を避け、等式で書換え
          -- 既知：`filter p (insert a s) = if p a then insert a (filter p s) else filter p s`
          -- ここでは `p a = true`
          have := Finset.filter_insert (s := s) (p := p) a
          -- 書き換え
          have : (insert a s).filter p
              = (if p a then insert a (s.filter p) else s.filter p) := this
          -- true ケースに潰す
          have : (insert a s).filter p = insert a (s.filter p) := by
            simpa [hpa]
          exact this
        -- いまの等式から card をとる
        -- `a ∉ s.filter p`（a∉s なので当然）
        have hnot : a ∉ s.filter p := by
          intro ha'
          have : a ∈ s := (Finset.mem_of_subset (Finset.filter_subset _ _) ha')
          exact ha_notmem this
        -- `card (insert a t) = card t + 1` （a∉t）
        have hcard := Finset.card_insert_of_notMem hnot
        -- 目的の向きに整形
        -- `card (insert a (s.filter p)) = (s.filter p).card + 1`
        -- 逆向きに書いておく
        have : (insert a ((s.filter p))).card = (s.filter p).card + 1 := hcard
        -- succ = +1
        -- `Nat.succ n = n + 1`
        have : (s.filter p).card.succ = (insert a (s.filter p)).card := by
          -- `Nat.succ` の定義で置換
          -- `Nat.succ n = n + 1`
          -- ここでは `rw [Nat.succ_eq_add_one]`
          -- ただし simpa 禁止のため段階的に
          simp_all only [Finset.sum_boole, Nat.cast_id, Finset.mem_filter, and_true, not_false_eq_true, Finset.card_insert_of_notMem, Nat.succ_eq_add_one]
        simp_all only [Finset.sum_boole, Nat.cast_id, Finset.mem_filter, and_true, not_false_eq_true, Finset.card_insert_of_notMem, Nat.succ_eq_add_one]
        -- これで完了

      -- 和の側：挿入で 1 足し
      -- sum over insert = sum over s + (if p a then 1 else 0) = ih + 1
      have hs : ∑ x ∈ insert a s, (if p x then (1:Nat) else 0)
              = (if p a then 1 else 0) + ∑ x ∈ s, (if p x then 1 else 0) := by
        -- `sum_insert`（a∉s）
        have := Finset.sum_insert (by exact ha_notmem) (f := fun x => if p x then (1:Nat) else 0)
        -- `sum_insert` は `f a + sum_s` の形。型を合わせて使う
        exact this
      -- まとめ
      -- 左辺：hs、右辺：ih と上の card 等式
      -- （`Nat.succ` を `+1` に戻す）
      -- `Nat.succ_eq_add_one`
      have : ∑ x ∈ insert a s, (if p x then (1:Nat) else 0)
             = (s.filter p).card + 1 := by
        -- 書き換え
        -- hs と ih、hpa を使う
        -- 先に hs を適用
        calc
          _ = (if p a then 1 else 0) + ∑ x ∈ s, (if p x then (1:Nat) else 0) := hs
          _ = 1 + (∑ x ∈ s, (if p x then (1:Nat) else 0)) := by
                -- p a = true
                have : (if p a then 1 else 0) = (1:Nat) := by exact by simp_all only [Finset.sum_boole, Nat.cast_id, Nat.succ_eq_add_one, ↓reduceIte]
                rw [this]
          _ = 1 + (s.filter p).card := by rw [ih]
          _ = (s.filter p).card + 1 := Nat.add_comm 1 _
      -- 右辺：filter のカード
      -- 先に `Nat.succ_eq_add_one` と上で得た `succ = card(insert ...)`
      have hcard_ins :
        (insert a s |>.filter p).card = (s.filter p).card + 1 := by
        -- すでに上の `this` が `succ = card(insert ...)` の対称形
        -- 直上で作った等式 `this` は sum 側、紛らわしいので別名に
        -- ここは `Nat.succ` の等式を使った `this` (hfi/hcard 組) から
        -- `card (filter (insert ...)) = (s.filter p).card + 1` が出ています
        -- 上で `this` として `∑ = ...` を付けたので名称が被るため書き直し:
        -- 再構築は冗長なので、簡潔にもう一度：
        have hfi : (insert a s).filter p = insert a (s.filter p) := by
          have := Finset.filter_insert (s := s) (p := p) a
          have : (insert a s).filter p
              = (if p a then insert a (s.filter p) else s.filter p) := this
          -- true ケース
          exact by simpa [hpa] using this
        -- すると `card(filter insert) = card(insert ...) = ... + 1`
        have hnot : a ∉ s.filter p := by
          intro ha'
          have : a ∈ s := (Finset.mem_of_subset (Finset.filter_subset _ _) ha')
          exact ha_notmem this
        have : (insert a (s.filter p)).card = (s.filter p).card + 1 :=
          Finset.card_insert_of_notMem hnot
        -- 置換
        simpa [hfi]
      -- 以上で両辺一致
      -- まとめる：
      -- 目標：sum(insert) = card(filter(insert))
      -- 左辺は上の `this`、右辺は `hcard_ins`
      -- （記号衝突を避け、ここでは `hs_sum` と `hs_card` に分けて再利用）
      -- 既に左辺 `this` を作ったので、置換して終了
      -- 実際にはこのブロックで十分
      -- 目標を書き換えて終了
      -- （`exact` で置ける）
      -- ここでは、先ほどの `this` は sum 側だったので、再度命名してから `exact` します。
      exact by
        -- sum(insert) = (s.filter p).card + 1 かつ
        -- card(filter(insert)) = (s.filter p).card + 1
        -- よって等しい
        have hsum : ∑ x ∈ insert a s, (if p x then (1:Nat) else 0)
                  = (s.filter p).card + 1 := by
          -- 直上で作った sum 等式
          -- 再掲
          -- （すでに `this` 名が使われているので再作成）
          -- 同内容をもう一度書くのは冗長ですが、明示で安全にします。
          calc
            _ = (if p a then 1 else 0) + ∑ x ∈ s, (if p x then (1:Nat) else 0) := by
                  exact hs
            _ = 1 + (∑ x ∈ s, (if p x then (1:Nat) else 0)) := by
                  have : (if p a then 1 else 0) = (1:Nat) := by
                    simp_all only [Finset.sum_boole, Nat.cast_id, Nat.succ_eq_add_one, ↓reduceIte, Nat.cast_add, Nat.cast_one]
                  rw [this]
            _ = 1 + (s.filter p).card := by rw [ih]
            _ = (s.filter p).card + 1 := Nat.add_comm 1 _
        -- これと hcard_ins を合わせて
        exact by
          -- 目標：sum(insert) = card(filter(insert))
          -- 置換
          rw [hsum, hcard_ins]
    · -- p a = false
      -- 挿入後の和は ih のまま
      have hs : ∑ x ∈ insert a s, (if p x then (1:Nat) else 0)
              = ∑ x ∈ s, (if p x then (1:Nat) else 0) := by
        have := Finset.sum_insert (by exact ha_notmem) (f := fun x => if p x then (1:Nat) else 0)
        -- 左辺の先頭項は 0
        -- `if p a then 1 else 0 = 0`
        have hz : (if p a then (1:Nat) else 0) = 0 := by simp_all only [Finset.sum_boole, Nat.cast_id, ↓reduceIte, zero_add]
        -- 上の sum_insert: `f a + sum_s`
        -- ゆえに `0 + sum_s = sum_s`
        -- 置換
        have := by
          calc
            (if p a then (1:Nat) else 0) + ∑ x ∈ s, (if p x then (1:Nat) else 0)
                = 0 + ∑ x ∈ s, (if p x then (1:Nat) else 0) := by rw [hz]
            _ = ∑ x ∈ s, (if p x then (1:Nat) else 0) := by exact Nat.zero_add _
        -- まとめ
        exact by
          -- `sum_insert` から始めて置換
          have := Finset.sum_insert (by exact ha_notmem)
              (f := fun x => if p x then (1:Nat) else 0)
          -- その等式を `rw` で使い、次に上の 0 消去を使う
          -- ここは直接 `rw` が煩雑なので、別経路の等式として使う
          -- 簡潔に：`bycases` で `p a = false` を使えば上と同じ結果に到達
          -- 最後は直接目標を `exact` で閉じます
          -- 既に `hs` に等式を収束させています
          simp_all only [Finset.sum_boole, Nat.cast_id, ↓reduceIte, zero_add]

      -- filter 側：¬p の方が 1 増える
      have hfi_false : (insert a s).filter (fun x => ¬ p x) = insert a (s.filter (fun x => ¬ p x)) := by
        -- `filter_insert` に p := (fun x => ¬ p x)
        have := Finset.filter_insert (s := s) (p := fun x => ¬ p x) a
        -- 今は `¬ p a = true` なので true ケース
        have : (insert a s).filter (fun x => ¬ p x)
            = (if (¬ p a) then insert a (s.filter (fun x => ¬ p x))
               else s.filter (fun x => ¬ p x)) := this
        have : (insert a s).filter (fun x => ¬ p x)
            = insert a (s.filter (fun x => ¬ p x)) := by
          -- ここで `¬ p a` は true
          have : (¬ p a) := by
            have : p a = False := by simp_all only [Finset.sum_boole, Nat.cast_id, not_false_eq_true, ↓reduceIte]
            -- `p a = false` から `¬ p a`
            exact by
              -- 反転
              simp_all only [Finset.sum_boole, Nat.cast_id, not_false_eq_true, ↓reduceIte, eq_iff_iff, iff_false]

          simp_all only [Finset.sum_boole, Nat.cast_id, not_false_eq_true, ↓reduceIte]
        exact this
      -- `a ∉ s.filter (¬p)`
      have hnot : a ∉ s.filter (fun x => ¬ p x) := by
        intro ha'
        have : a ∈ s := (Finset.mem_of_subset (Finset.filter_subset _ _) ha')
        exact ha_notmem this
      have hcard_ins :
          (insert a s |>.filter (fun x => ¬ p x)).card
          = (s.filter (fun x => ¬ p x)).card + 1 := by
        -- 上の等式から card_insert_of_not_mem
        have := Finset.card_insert_of_notMem hnot
        -- 置換
        simpa [hfi_false] using this
      -- また、`(insert a s).filter p = s.filter p`（p a=false）
      have hfi_true :
          (insert a s |>.filter p) = s.filter p := by
        -- 先ほどの p 版の filter_insert の false ケース
        have := Finset.filter_insert (s := s) (p := p) a
        have : (insert a s).filter p
            = (if p a then insert a (s.filter p) else s.filter p) := this
        -- p a = false
        have : (insert a s).filter p = s.filter p := by simpa [hpa] using this
        exact this
      -- 目標：sum = card(filter p)
      -- `hs` と `ih`、`hfi_true` を合わせれば OK
      calc
        ∑ x ∈ insert a s, (if p x then (1:Nat) else 0)
            = ∑ x ∈ s, (if p x then (1:Nat) else 0) := hs
        _ = (s.filter p).card := ih
        _ = ((insert a s).filter p).card := by rw [hfi_true]
-/
/-- `card (s.filter p) + card (s.filter (¬p)) = card s`。 -/
lemma card_filter_add_card_filter_not (s : Finset β) (p : β → Prop) [DecidablePred p] :
    (s.filter p).card + (s.filter (fun b => ¬ p b)).card = s.card := by
  classical
  refine Finset.induction_on s ?h0 ?hstep
  · simp
  · intro a s ha ih
    by_cases hpa : p a
    · -- p a
      -- 左辺： (insert a (filter p s)).card + (filter ¬p s).card
      have hfi_p :
          (insert a s).filter p = insert a (s.filter p) := by
        have := Finset.filter_insert (s := s) (p := p) a
        simpa [hpa] using this
      have hfi_np :
          (insert a s).filter (fun b => ¬ p b) = (s.filter (fun b => ¬ p b)) := by
        have := Finset.filter_insert (s := s) (p := fun b => ¬ p b) a
        -- ここでは `¬ p a = false`
        have : ¬ p a = False := by simp_all only [not_true_eq_false, ↓reduceIte, eq_iff_iff, iff_false, not_false_eq_true]
        -- false ケース
        simp_all only [not_true_eq_false, ↓reduceIte, eq_iff_iff, iff_false, not_false_eq_true]
      have hnot : a ∉ s.filter p := by
        intro ha'
        have : a ∈ s := (Finset.mem_of_subset (Finset.filter_subset _ _) ha')
        exact ha this
      have hcard_insert :
          (insert a (s.filter p)).card = (s.filter p).card + 1 :=
        Finset.card_insert_of_notMem hnot
      calc
        ((insert a s).filter p).card + ((insert a s).filter (fun b => ¬ p b)).card
            = (insert a (s.filter p)).card + (s.filter (fun b => ¬ p b)).card := by
                rw [hfi_p, hfi_np]
        _ = (s.filter p).card + 1 + (s.filter (fun b => ¬ p b)).card := by
                rw [hcard_insert]
        _ = (s.filter p).card + (s.filter (fun b => ¬ p b)).card + 1 := by
                exact Nat.add_right_comm (Finset.filter p s).card 1 {b ∈ s | ¬p b}.card
        _ = s.card + 1 := by
                rw [ih]
        _ = (insert a s).card := by
                -- `card_insert_of_not_mem`
                have := Finset.card_insert_of_notMem ha
                -- `card (insert a s) = card s + 1`
                exact this.symm
    · -- p a = false
      -- 対称な議論
      have hfi_p :
          (insert a s).filter p = (s.filter p) := by
        have := Finset.filter_insert (s := s) (p := p) a
        simpa [hpa] using this
      have hfi_np :
          (insert a s).filter (fun b => ¬ p b) = insert a (s.filter (fun b => ¬ p b)) := by
        have := Finset.filter_insert (s := s) (p := fun b => ¬ p b) a
        -- ここでは `¬ p a = true`
        have : (¬ p a) = True := by simp_all only [not_false_eq_true, ↓reduceIte]
        -- true ケース
        simp_all only [↓reduceIte, eq_iff_iff, iff_true]
      have hnot : a ∉ s.filter (fun b => ¬ p b) := by
        intro ha'
        have : a ∈ s := (Finset.mem_of_subset (Finset.filter_subset _ _) ha')
        exact ha this
      have hcard_insert :
          (insert a (s.filter (fun b => ¬ p b))).card
          = (s.filter (fun b => ¬ p b)).card + 1 :=
        Finset.card_insert_of_notMem hnot
      calc
        ((insert a s).filter p).card + ((insert a s).filter (fun b => ¬ p b)).card
            = (s.filter p).card + (insert a (s.filter (fun b => ¬ p b))).card := by
                rw [hfi_p, hfi_np]
        _ = (s.filter p).card + (s.filter (fun b => ¬ p b)).card + 1 := by
                rw [hcard_insert]
                exact rfl
        _ = s.card + 1 := by
                rw [ih]
        _ = (insert a s).card := by
                have := Finset.card_insert_of_notMem ha
                exact this.symm

end CountLemmas
end SetFamily
/-

/-- 有限台集合 `ground` と，その部分集合族 `sets`（判定述語＋可判定性） 古い定義-/
@[ext]
structure SetFamily (α : Type u) [DecidableEq α] where
  ground    : Finset α
  sets      : Finset α → Prop
  decSets   : DecidablePred sets
  inc_ground :
    ∀ {s : Finset α}, sets s → s ⊆ ground

attribute [instance] SetFamily.decSets

namespace SetFamily

variable {α : Type u} [DecidableEq α]



/-- 族の全メンバー（有限集合の有限集合） -/
noncomputable def hyperedges (F : SetFamily α) : Finset (Finset α) :=
  F.ground.powerset.filter F.sets

/-- 超辺の個数（Nat） -/
noncomputable def number_of_hyperedgesNat (F : SetFamily α) : Nat :=
  F.hyperedges.card

/-- 頂点の次数（Nat）：その頂点を含む超辺数 -/
noncomputable def degreeNat (F : SetFamily α) (v : α) : Nat :=
  (F.hyperedges.filter (fun s => v ∈ s)).card

/-- 超辺サイズ総和（Nat）：`∑_{A∈F} |A|` -/
noncomputable def total_size_of_hyperedgesNat (F : SetFamily α) : Nat :=
  F.hyperedges.sum Finset.card

/-- 論文で使う整数スケール版：`2*deg(v) - |I|` -/
noncomputable def normalized_degree (F : SetFamily α) (v : α) : Int :=
  (2 : Int) * (F.degreeNat v : Int) - (F.number_of_hyperedgesNat : Int)

/-- 論文で使う整数スケール版：`2*Σ|A| - |I|*|ground|` -/
noncomputable def normalized_degree_sum (F : SetFamily α) : Int :=
  (2 : Int) * (F.total_size_of_hyperedgesNat : Int)
  - (F.number_of_hyperedgesNat : Int) * (F.ground.card : Int)

/-- 頂点 v が rare か（`normalized_degree ≤ 0`） -/
def is_rare (F : SetFamily α) (v : α) : Prop :=
  F.normalized_degree v ≤ 0

/-- 二重計数：`ground` 上の次数総和 = 超辺サイズ総和（Nat 版）平均次数の議論をするには復活させてもいいかも。 -/
lemma degree_sum_eq_total_size_of_hyperedgesNat (F : SetFamily α) :
    (∑ v ∈ F.ground, F.degreeNat v) = F.total_size_of_hyperedgesNat := by
  classical
  -- 記号短縮
  set V := F.ground
  set H := F.hyperedges
  -- LHS を「if で数える形」に展開

  have hdeg :
      ∀ v ∈ V,
        (F.degreeNat v)
          = ∑ A ∈ H, (if v ∈ A then (1 : Nat) else 0) := by
    intro v hv
    -- `degreeNat v = card (H.filter (· ∋ v))` を if-和へ
    have := by
      -- `card_filter` を ∑ if に置換する定番形
      -- (H.filter p).card = ∑ A∈H, if p A then 1 else 0
      simpa using (Finset.card_filter (s := H) (p := fun A => v ∈ A))
    -- 上の `this : (H.filter (fun A => v ∈ A)).card = ...`
    -- を そのまま使えば OK
    simp [SetFamily.degreeNat, H]


  -- RHS（Σ|A|）を「if で数える形」に展開
  have hcard :
      ∀ {A}, A ∈ H → A.card = ∑ v ∈ V, (if v ∈ A then 1 else 0) := by
    intro A hA
    -- A ⊆ V を得る（H は V の powerset の filter なので）
    have hA_subV : A ⊆ V := by
      have : A ∈ V.powerset := (Finset.mem_filter.mp hA).1
      simpa [Finset.mem_powerset] using this
    -- `A.card` を V 上のインジケータ和に持ち上げる
    -- `card = ∑_{v∈A} 1` を，`A ⊆ V` を使って `∑_{v∈V} if v∈A then 1 else 0` に等しいへ
    calc
      A.card = (Finset.filter (fun v => v ∈ A) V).card := by
        -- A⊆V なので V を A で filter するとちょうど A
        -- （要素同値を示してから card を取る）
        have : V.filter (fun v => v ∈ A) = A := by
          ext v
          constructor
          · intro hv
            exact (Finset.mem_filter.mp hv).2
          · intro hv
            exact Finset.mem_filter.mpr ⟨hA_subV hv, hv⟩
        simp [this]
      _ = ∑ v ∈ V, (if v ∈ A then 1 else 0) := by
        -- `card_filter` の Nat 版（定番）
        simpa using (Finset.card_filter (s := V) (p := fun v => v ∈ A))

  -- 以上を使って Fubini（和の交換）
  calc
    (∑ v ∈ V, F.degreeNat v)
        = ∑ v ∈ V, ∑ A ∈ H, (if v ∈ A then 1 else 0) := by
          refine Finset.sum_congr rfl ?_
          intro v hv; simpa using hdeg v hv
    _   = ∑ A ∈ H, ∑ v ∈ V, (if v ∈ A then 1 else 0) := by
          exact Finset.sum_comm
    _   = ∑ A ∈ H, A.card := by
          refine Finset.sum_congr rfl ?_
          intro A hA;
          simp [hcard hA]
    _   = F.total_size_of_hyperedgesNat := rfl

/-- 各頂点の整数版 normalized_degree の総和 = 整数版 NDS -/
lemma sum_normalized_degree_eq_nds (F : SetFamily α) :
    (∑ v ∈ F.ground, F.normalized_degree v) = F.normalized_degree_sum := by
  classical
  -- Nat → Int：∑deg = ∑|A|
  have hNat : (∑ v ∈ F.ground, F.degreeNat v)
                = F.total_size_of_hyperedgesNat :=
    degree_sum_eq_total_size_of_hyperedgesNat (F := F)
  have hDC :
      (∑ v ∈ F.ground, (F.degreeNat v : Int))
        = (F.total_size_of_hyperedgesNat : Int) := by
    -- cast(∑ Nat) → ∑ cast(Nat)
    have := congrArg (fun n : Nat => (n : Int)) hNat
    -- 左辺 cast を ∑ に配る
    simpa [Nat.cast_sum] using this

  -- 以降は代数整理だけ
  unfold normalized_degree normalized_degree_sum
  have h1 :
      (∑ v ∈ F.ground, (2 : Int) * (F.degreeNat v : Int))
        = (2 : Int) * (∑ v ∈ F.ground, (F.degreeNat v : Int)) := by
    simp [Finset.mul_sum]
  have h2 :
      (∑ v ∈ F.ground, (F.number_of_hyperedgesNat : Int))
        = (F.ground.card : Int) * (F.number_of_hyperedgesNat : Int) := by
    simp [Finset.sum_const]

  calc
    (∑ v ∈ F.ground, ((2 : Int) * (F.degreeNat v : Int) - (F.number_of_hyperedgesNat : Int)))
        = (∑ v ∈ F.ground, (2 : Int) * (F.degreeNat v : Int))
          - (∑ v ∈ F.ground, (F.number_of_hyperedgesNat : Int)) := by
            simp [Finset.sum_sub_distrib]
    _   = (2 : Int) * (∑ v ∈ F.ground, (F.degreeNat v : Int))
          - (F.ground.card : Int) * (F.number_of_hyperedgesNat : Int) := by
            simp [h1, h2]
    _   = (2 : Int) * (F.total_size_of_hyperedgesNat : Int)
          - (F.number_of_hyperedgesNat : Int) * (F.ground.card : Int) := by
            -- 二重計数を適用
            simp [hDC, mul_comm]


end SetFamily
end AvgRare

--attribute [simp] Finset.mem_attach
--attribute [simp] Quot.eq -- 代表の単純化に使う場合は危険でない範囲で

--@[simp] lemma imageQuot_ground (E : Setoid α) (F : SetFamily α) :
--  imageQuot E F.ground = (trace E F).ground := rfl

-/
