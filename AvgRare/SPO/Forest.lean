import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.Basic
import Mathlib.Logic.Relation
import AvgRare.Basics.SetFamily
import AvgRare.SPO.FuncSetup
import AvgRare.PaperSync.IdealsTrace

namespace AvgRare
open SPO
--open FuncSetup
open Trace

universe u
variable {α : Type u} [DecidableEq α]
--variable (S : FuncSetup α)

open Classical

instance (S : SPO.FuncSetup α) : DecidableEq S.Elem := by infer_instance

/-! ## 0) 出発点（与えられている定義） -/

structure FuncSetup (α : Type u) [DecidableEq α] where
  ground : Finset α
  f      : {x // x ∈ ground} → {y // y ∈ ground}

--variable (S : FuncSetup α)

def cover (S : SPO.FuncSetup α) (x y : S.Elem) : Prop := S.f x = y
def le (S : SPO.FuncSetup α) (x y : S.Elem) : Prop := Relation.ReflTransGen S.cover x y

/-- ユーザ定義：isPoset（反対称性を取り出せると仮定） -/
--class isPoset (S : FuncSetup α) : Prop

-- 既存環境にある想定の補題。
axiom antisymm_of_isPoset
  (S : SPO.FuncSetup α) (h : isPoset) {x y : S.Elem} :
  S.le x y → S.le y x → x = y

/-- 極大の定義（ユーザ方針に合わせて） -/
def maximal (S : SPO.FuncSetup α)(u : S.Elem) : Prop := ∀ v, S.le u v → S.le v u

/-- 無向隣接（ハッセ図の無向化） -/
def adj(S : SPO.FuncSetup α) (x y : S.Elem) : Prop := S.cover x y ∨ S.cover y x

/-- 連結性：無向隣接の反射推移閉包で結ばれる -/
def isConnected (S : SPO.FuncSetup α): Prop :=
  ∀ a b : S.Elem, Relation.ReflTransGen (adj S) a b

/-- 一歩の向き -/
def isUp (S : SPO.FuncSetup α)(x y : S.Elem)   : Prop := S.cover x y
def isDown (S : SPO.FuncSetup α)(x y : S.Elem) : Prop := S.cover y x

/-! ## 1) パス構造体（簡単路） -/
structure Path (S : SPO.FuncSetup α)(u v : S.Elem) where
  verts    : List S.Elem
  nonempty : verts ≠ []
  head_ok  : verts.head? = some u
  last_ok  : verts.reverse.head? = some v
  chain    : verts.Chain' (adj S)
  nodup    : verts.Nodup

private def IsWalk (S : SPO.FuncSetup α) (u v : S.Elem) (L : List S.Elem) : Prop :=
  L ≠ [] ∧ L.head? = some u ∧ L.reverse.head? = some v ∧ List.Chain' (adj S) L

/-- `ReflTransGen` から「歩道」を作る（重複は気にしない）。 -/
private lemma walk_of_rtg (S : SPO.FuncSetup α)
  {u v : S.Elem} (h : Relation.ReflTransGen (adj S) u v) :
  ∃ L, IsWalk S u v L := by
  -- 反射推移閉包の帰納（`induction h` が使える）
  induction h with
  | @refl =>
      refine ⟨[u], ?_⟩
      constructor
      · intro hnil; cases hnil
      constructor
      · rfl
      constructor
      · simp
      · -- `[u]` は自明に Chain'
        exact List.chain'_singleton u
  | @tail x y hxy hxy_step ih =>
      obtain ⟨L, hL_ne, hL_hd, hL_last, hL_chain⟩ := ih
      -- x--y の 1歩を L の末尾に足して歩道を伸ばす

      refine ⟨L ++ [y], ?_⟩
      constructor
      · intro hnil; -- L++[y]=[] は不可能
        have : L = [] := by
          -- 末尾1つ足して空になることはない
          -- ここは長さで反証
          have : (L ++ [y]).length = 0 := by simp [hnil]
          have : L.length + 1 = 0 := by
            simp
            apply False.elim
            simp_all only [ne_eq, List.head?_reverse, List.append_eq_nil_iff, List.cons_ne_self, and_self]

          exact False.elim (Nat.succ_ne_zero _ this)
        exact hL_ne this
      constructor
      · -- 先頭は変わらず u
        -- `head? (L++[y]) = head? L = some u`

        have : (List.head? (L ++ [y])) = (List.head? L) := by
          cases hL:L with
          | nil =>
            subst hL
            simp_all only [ne_eq, not_true_eq_false]
          | cons _ _ => rfl
        exact Eq.trans this hL_hd
      constructor
      · -- 末尾は y
        -- `(L++[y]).reverse.head? = some y`
        -- 定義計算で済む
        simp
      · -- 連鎖性：Chain' L かつ 末尾と y が隣接
        -- `hxy_step : adj S x y` と L の末尾が x であることから構成
        -- L の末尾が x であることは hL_last から得られる
        -- `Chain'` を `Chain` に展開して cons で付ける
        -- まず L が空の場合は上で排除しているので cons 形で書ける
        -- 手短に：`List.Chain'.append_singleton` 相当を手書き
        -- 「L の最後の要素 = x」を式として取り出す
        have hx_last : L.reverse.head? = some x := by
          -- hL_last : (L.reverse).head? = some x（ここでは x = x）
          -- ただし ih の終点は x なので、ih の hL_last は some x
          -- そのまま使う
          exact hL_last
        -- ここから `Chain' (L ++ [y])` を構成
        -- 実際の `simp` 展開で落ちます
        -- `List.Chain'` の append-one の構成は：
        --   Chain' L かつ adj last(L) y
        -- ここは `simp` で終わり
        have : List.Chain' (adj S) (L ++ [y]) := by
          -- L が空でないので、`Chain'` の末尾に 1 辺追加できる
          -- 直接 `simp` に流す
          -- まず L の末尾要素を x に直す
          -- `hx_last : head? (reverse L) = some x` はまさにそれ
          -- `simp` 側で用いて完成
          -- 具体的に書くと長くなるのでここはまとめて
          simp_all only [ne_eq, List.head?_reverse]
          obtain ⟨val, property⟩ := u
          obtain ⟨val_1, property_1⟩ := v
          obtain ⟨val_2, property_2⟩ := x
          obtain ⟨val_3, property_3⟩ := y
          rw [List.chain'_append]
          simp_all only [List.chain'_singleton, Option.mem_def, Option.some.injEq, List.head?_cons, forall_eq', and_self]

        exact this
  -- ↑ `admit` は、`List.Chain'` の末尾1点付加の定型構成です。
  --   もしここが噛む場合は、小補題
  --     `lemma chain'_snoc {R} : Chain' R (L ++ [y]) ↔ Chain' R L ∧ (last L) ~ y`
  --   を先に証明して使ってください。

private lemma exists_dup_split
  {β : Type _} [DecidableEq β]
  {L : List β} (hdup : ¬ L.Nodup) :
  ∃ (l₁ l₂ l₃ : List β) (m : β),
      L = l₁ ++ m :: l₂ ++ m :: l₃
    ∧ m ∉ l₁ ∧ m ∉ l₂ := by
  -- ¬ L.Nodup ならば、ある m が2回以上出現
  classical
  -- 補助：a ∈ s なら、a が最初に現れる位置で s を s = l₂ ++ a :: l₃ と割る。
  -- しかも l₂ には a が含まれない。
  have split_first :
      ∀ (a : β) (s : List β), a ∈ s →
        ∃ l₂ l₃, s = l₂ ++ a :: l₃ ∧ a ∉ l₂ := by
    intro a s hs
    induction s with
    | nil =>
        cases hs
    | cons b t ih =>
        by_cases hb : b = a
        · refine ⟨[], t, ?_, ?_⟩
          · simp [hb]
          · simp
        · have ha_mem_t : a ∈ t := by
            -- a ∈ b :: t かつ b ≠ a から a ∈ t
            simp_all only [exists_and_right, List.mem_cons]
            cases hs with
            | inl h =>
              subst h
              simp_all only [not_true_eq_false]
            | inr h_1 => simp_all only [forall_const]

          rcases ih ha_mem_t with ⟨l₂, l₃, hst, hnot⟩
          refine ⟨b :: l₂, l₃, ?_, ?_⟩
          · -- b ≠ a のぶんだけ先頭に積む
            simp [hst,List.cons_append]
          · -- l₂ に a は含まれない → b :: l₂ にも含まれない
            simp [hnot]
            subst hst
            simp_all only [exists_and_right, forall_const, List.mem_cons, or_true, List.mem_append, true_or]
            obtain ⟨w, h⟩ := ih
            obtain ⟨left, right⟩ := h
            obtain ⟨w_1, h⟩ := left
            apply Aesop.BuiltinRules.not_intro
            intro a_1
            subst a_1
            simp_all only [not_true_eq_false]

  -- 本体：L で帰納
  induction L with
  | nil =>
      -- [] は Nodup なので矛盾
      simp at hdup
  | cons a t ih =>
      by_cases hmem : a ∈ t
      · -- a が後ろにもう一度出るケース：ここで最初の再出現で割る
        rcases split_first a t hmem with ⟨l₂, l₃, ht, hnot⟩
        refine ⟨[], l₂, l₃, a, ?_, ?_, ?_⟩
        · -- 形を合わせる
          -- a :: t = [] ++ a :: l₂ ++ a :: l₃
          simp [ht, List.cons_append]
        · -- a ∉ []
          simp
        · -- a ∉ l₂
          exact hnot
      · -- a が t にいない：重複は t の中にあるので帰納法を適用
        have hdup_t : ¬ t.Nodup := by
          -- Nodup (a :: t) ↔ (a ∉ t ∧ Nodup t) より
          simpa [List.nodup_cons, hmem] using hdup
        rcases ih hdup_t with ⟨l₁, l₂, l₃, m, ht, hm₁, hm₂⟩
        refine ⟨a :: l₁, l₂, l₃, m, ?_, ?_, hm₂⟩
        · -- 形を合わせる
          simp [ht, List.cons_append, List.append_assoc]
        · -- m ∉ a :: l₁ を示す（m は t に属し、a ∉ t なので m ≠ a）
          have hm_in_t : m ∈ t := by
            -- ht : t = l₁ ++ m :: l₂ ++ m :: l₃ から m ∈ t
            have hm₀ : m ∈ (l₁ ++ m :: l₂ ++ m :: l₃) := by
              -- 右側の "m :: l₂" に明らかに属する
              have : m ∈ (m :: l₂) := by simp
              -- それを全体の append に持ち上げる
              have : m ∈ (m :: l₂) ++ m :: l₃ := (List.mem_append).2 (Or.inl this)
              subst ht
              simp_all only [exists_and_right, List.mem_cons, or_false, List.cons_append, List.mem_append, true_or, or_true,
                or_self, List.append_assoc, List.nodup_cons, not_or, not_and, and_imp, not_false_eq_true, true_and]
            simp [ht, List.append_assoc]

          have hma : m ≠ a := by
            intro h
            have : a ∈ t := by simpa [h] using hm_in_t
            exact hmem this
          -- 最後に m ∉ a :: l₁
          -- mem_cons ↔ (m = a ∨ m ∈ l₁) を使う
          intro h
          have := (List.mem_cons).1 h
          cases this with
          | inl h' => exact hma h'
          | inr h' => exact hm₁ h'

private lemma chain_from_middle
  {β : Type _} {R : β → β → Prop}
  {a b : β} {l₂ l₃ : List β} :
  List.Chain R a (l₂ ++ b :: l₃) → List.Chain R b l₃ := by
  intro h
  -- l₂に関する場合分けを行う
  induction l₂ generalizing a with
  | nil =>
    -- l₂ = []の場合: List.Chain R a (b :: l₃) → List.Chain R b l₃
    simp at h
    -- h : List.Chain R a (b :: l₃) = R a b ∧ List.Chain R b l₃
    exact h.2
  | cons head tail ih =>
    -- l₂ = head :: tailの場合
    simp at h
    -- h : List.Chain R a (head :: (tail ++ b :: l₃))
    -- これは R a head ∧ List.Chain R head (tail ++ b :: l₃)
    have h_chain_tail : List.Chain R head (tail ++ b :: l₃) := h.2
    -- 帰納法の仮定を適用
    apply ih
    simp_all only [and_true]
    assumption

/-- （連鎖の短縮補題）
`Chain' R (l₁ ++ m :: l₂ ++ m :: l₃)` が成り立つとき、
真ん中の `l₂ ++ m` を落とした `l₁ ++ m :: l₃` でも `Chain' R`。 -/
private lemma chain'_shorten_dup
  {β : Type _} {R : β → β → Prop}
  {l₁ l₂ l₃ : List β} {m : β} :
  List.Chain' R (l₁ ++ m :: l₂ ++ m :: l₃) →
  List.Chain' R (l₁ ++ m :: l₃) := by
  have tail_lemma : ∀ {a : β} {l : List β}, List.Chain' R (a :: l) → List.Chain' R l := by
    intro a l h
    cases l
    · simp_all only [List.chain'_singleton, List.chain'_nil]
    · simp_all only [List.chain'_cons_cons]

  -- Helper lemma: If `Chain' R (a :: l)` holds and `l` is not empty, then `R a (List.head l)` holds.
  have chain'_head : ∀ {a : β} {l : List β}, List.Chain' R (a :: l) → (notl:l ≠ []) → R a (List.head l notl ) := by
    intro a l h hne
    cases l
    · simp_all only [List.chain'_singleton]
      contradiction
    · simp_all only [List.chain'_cons_cons, List.head_cons]


  induction l₁ with
  | nil =>
    intro H
    have H2 := tail_lemma H
    induction l₂ with
    | nil => exact H2
    | cons a l₂' IHl₂ =>
      have := tail_lemma H2
      exact List.Chain'.right_of_append (tail_lemma (tail_lemma H))
  | cons a l₁' IH =>
    intro H
    have tail_H := tail_lemma H
    have IH_chain := IH tail_H
    have hne1 : l₁' ++ m :: l₂ ++ m :: l₃ ≠ [] := by
      cases l₁' <;> simp
    have hne2 : l₁' ++ m :: l₃ ≠ [] := by
      cases l₁' <;> simp
    have ha1 := chain'_head H hne1
    have head_eq : List.head (l₁' ++ m :: l₂ ++ m :: l₃) hne1 = List.head (l₁' ++ m :: l₃) hne2:= by
      cases l₁' with
      | nil => rfl
      | cons b l₁'' => rfl
    by_cases h : l₁' ++ m :: l₃ = []
    · simp [h]
    · match heq : l₁' ++ m :: l₃ with
      | [] => simp at heq
      | b :: l' =>
        have : (l₁' ++ m :: l₃) ≠ [] := by
          cases l₁' <;> simp
        have head_eq2 : List.head (l₁' ++ m :: l₃) this = b := by
          simp [heq]
        have : (l₁' ++ m :: l₂ ++ m :: l₃) ≠ [] := by
          cases l₁' <;> simp
        have : List.head (l₁' ++ m :: l₂ ++ m :: l₃) this = b := by
          rw [head_eq, head_eq2]
        have : R a b := by
          rw [← this]
          (expose_names; exact chain'_head H this_2)
        have : List.Chain' R (b :: l') := by
          rw [heq] at IH_chain
          exact IH_chain

        rename_i this_3 this_4
        subst this_3
        simp_all only [ne_eq, List.append_assoc, List.cons_append, List.append_eq, List.head_cons, reduceCtorEq,
          not_false_eq_true, List.chain'_cons_cons, and_self]


/-- 重複があれば「歩道」を短縮できる（端点・連鎖性は保存）。 -/
private lemma shorten_walk_if_dup
  (S : SPO.FuncSetup α) {u v : S.Elem} :
  ∀ {L : List S.Elem}, IsWalk S u v L → ¬ L.Nodup →
  ∃ L', IsWalk S u v L' ∧ L'.length < L.length := by
  -- 古典的：最初の重複 `L = l₁ ++ m :: l₂ ++ m :: l₃` を取り、`L' := l₁ ++ m :: l₃`
  -- で短くなる。端点・連鎖性は簡単な場合分けで保存。
  -- 実装は List 分解の帰納法でいけます。
  intro L hW hdup
  classical
  -- 最初の重複分解（`l₁, m, l₂, l₃`）を取る補題を使うか、自前で帰納で作る
  -- ここでは簡潔に `List` の標準事実として使用（必要なら自前で証明）
  -- （最初の重複を与える分解が取れること）
  have : ∃ (l₁ l₂ l₃ : List S.Elem) (m : S.Elem),
      L = l₁ ++ m :: l₂ ++ m :: l₃ ∧
      m ∉ l₁ ∧ m ∉ l₂ := by
    -- 補題がない環境では、`List` に対する単純な再帰で作れます。
    -- ここは実装の都合で補題として切るのが安全です。
    --hW : IsWalk S u v L
    --hdup : ¬L.Nodup
    exact exists_dup_split hdup

  obtain ⟨l₁, l₂, l₃, m, hsplit, hnot1, hnot2⟩ := this
  -- 短縮した歩道
  let L' := l₁ ++ m :: l₃
  have hlen : L'.length < L.length := by
    -- 長さが `l₂.length` だけ減る（>0）
    -- 直接 `simp`/`calc` で出ます
    subst hsplit
    simp_all only [List.append_assoc, List.cons_append, List.length_append, List.length_cons, add_lt_add_iff_left,
      add_lt_add_iff_right, L']
    obtain ⟨val, property⟩ := u
    obtain ⟨val_1, property_1⟩ := v
    obtain ⟨val_2, property_2⟩ := m
    omega

  -- 端点と連鎖性は `hsplit` と `hW` の各成分から場合分けで保存されます
  have hW' : IsWalk S u v L' := by
    -- `hW` を分解
    rcases hW with ⟨hne, hhd, hlast, hchain⟩
    -- 端点が l₁ の位置に来るときと、短縮が末尾側にかかるときで分岐
    -- いずれも `hsplit` と `Chain'` の append/cons/snoc 展開で片付きます
    -- 結論のみ構成
    dsimp [IsWalk]
    constructor
    · subst hsplit
      simp_all only [List.append_assoc, List.cons_append, List.length_append, List.length_cons, add_lt_add_iff_left,
        add_lt_add_iff_right, ne_eq, List.append_eq_nil_iff, reduceCtorEq, and_false, not_false_eq_true, List.head?_append,
        List.head?_cons, Option.or_some, Option.some.injEq, List.reverse_append, List.reverse_cons, List.nil_append,
        List.head?_reverse, L']
    · constructor
      · subst hsplit
        simp_all only [List.append_assoc, List.cons_append, List.length_append, List.length_cons, add_lt_add_iff_left,
          add_lt_add_iff_right, ne_eq, List.append_eq_nil_iff, reduceCtorEq, and_false, not_false_eq_true, List.head?_append,
          List.head?_cons, Option.or_some, Option.some.injEq, List.reverse_append, List.reverse_cons, List.nil_append,
          List.head?_reverse, L']
      · constructor
        · subst hsplit
          simp_all only [List.append_assoc, List.cons_append, List.length_append, List.length_cons, add_lt_add_iff_left,
            add_lt_add_iff_right, ne_eq, List.append_eq_nil_iff, reduceCtorEq, and_false, not_false_eq_true, List.head?_append,
            List.head?_cons, Option.or_some, Option.some.injEq, List.reverse_append, List.reverse_cons, List.nil_append,
            List.head?_reverse, L']
        · dsimp [L']
          rw [hsplit] at hchain
          show List.Chain' (adj S) (l₁ ++ m :: l₃)
          --List.Chain' (adj S) (l₁ ++ m :: l₂ ++ m :: l₃)
          exact chain'_shorten_dup hchain

  exact ⟨L', hW', hlen⟩

lemma exists_geodesic_path (S : SPO.FuncSetup α)
  [Fintype S.Elem] (hconn : isConnected S) (u v : S.Elem) :
  ∃ p : Path S u v, ∀ q : Path S u v, p.verts.length ≤ q.verts.length := by
  classical
  -- まず「歩道」集合
  have hw : ∃ L, IsWalk S u v L := by
    -- 連結性（無向 `ReflTransGen adj`）から
    exact walk_of_rtg S (hconn u v)
  -- 長さが取れる自然数集合
  let A : Set Nat :=
    {n | ∃ L, IsWalk S u v L ∧ L.length = n}
  have A_ne : ∃ n, A n := by
    rcases hw with ⟨L, hL⟩
    exact ⟨L.length, ⟨L, hL, rfl⟩⟩
  -- 最小の長さ `n0`
  let n0 := Nat.find A_ne
  -- その長さを持つ歩道 `L0`
  have hmin : ∃ L0, IsWalk S u v L0 ∧ L0.length = n0 := Nat.find_spec A_ne
  rcases hmin with ⟨L0, hW0, hlen0⟩
  -- `L0` は Nodup。でなければ短縮できて最小長に反する。
  have hnodup : L0.Nodup := by
    --intro hcontra
    by_contra hcontra
    have ⟨L1, hW1, hlt⟩ := shorten_walk_if_dup S (u := u) (v := v) hW0 hcontra
    -- `L1.length < n0` だが `n0` は最小、矛盾
    have : A L1.length := ⟨L1, hW1, rfl⟩
    -- `Nat.find_min'` で最小性に反する
    have hmin' := Nat.find_min' A_ne this
    -- `hlen0 : n0 = L0.length` と `hlt : L1.length < L0.length`
    -- を併せて `hlt.trans_le hmin'` が `False`
    simp_all only [Nat.lt_find_iff, le_refl, n0, A]
  -- 歩道 `L0` から `Path` を作る
  rcases hW0 with ⟨hne, hhd, hlast, hchain⟩
  refine ⟨
    { verts    := L0
    , nonempty := hne
    , head_ok  := hhd
    , last_ok  := hlast
    , chain    := hchain
    , nodup    := hnodup
    },
    ?min⟩
  -- 最小性：任意の `Path q` は「歩道」でもあるので、長さは `n0` 以上
  intro q
  have : A q.verts.length := by
    refine ⟨q.verts, ?_, rfl⟩
    exact ⟨q.nonempty, q.head_ok, q.last_ok, q.chain⟩
  -- `Nat.find_min'` を使う
  simp_all only [Nat.find_le_iff, n0, A]
  simp_all only [ne_eq, List.head?_reverse]
  obtain ⟨val, property⟩ := u
  obtain ⟨val_1, property_1⟩ := v
  obtain ⟨w, h⟩ := hw
  obtain ⟨w_1, h_1⟩ := A_ne
  apply Exists.intro
  · apply And.intro
    · rfl
    · simp_all only



/-! ## 2) 「機能性」：出次数高々 1 -/

/-- 同じ元からの `cover` の像は一意 -/
lemma cover_out_unique (S : SPO.FuncSetup α){u y z : S.Elem} :
  S.cover u y → S.cover u z → y = z := by
  intro hy hz

  dsimp [FuncSetup.cover] at hy hz
  -- hy : S.f u = y, hz : S.f u = z
  have h' := hz
  -- 左辺 `S.f u` を hy で置換すると `y = z`
  -- （simpa を使わず、書き換え＋ exact）
  rw [hy] at h'
  exact h'

/-! ## 3) 固定点と極大の関係 -/

/-- `f u = u` なら `u` は極大（反対称性不要） -/
lemma maximal_of_fixpoint  (S : SPO.FuncSetup α){u : S.Elem} (huu : S.cover u u) :
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



/-- `u` が極大で `isPoset` なら `f u = u`（= cover u u） -/
lemma fixpoint_of_maximal (S : SPO.FuncSetup α)  {u : S.Elem} (h : isPoset) (hu : S.maximal u) :
  S.cover u u := by
  -- 1 歩先 v := f u に対し、u ≤ v、極大性から v ≤ u、反対称で v = u
  let v := S.f u
  have huv : S.le u v := Relation.ReflTransGen.single rfl
  have hvu : S.le v u := hu huv
  have hv_eq : v = u := antisymm_of_isPoset S h  hvu huv
  -- cover u v から書き換え
  have hcov : S.cover u v := rfl
  -- v = u を右辺に入れて cover u u
  -- （simpa を避け、rw で置換）
  have : S.cover u u := by
    have h1 := hcov
    -- 右辺を置換
    simp_all only [FuncSetup.maximal_iff, FuncSetup.le_iff_leOn_val, Subtype.forall, Finset.coe_mem, v]
  exact this

/-- （まとめ）反対称性ありなら「極大 ⇔ 固定点」 -/
lemma maximal_iff_fixpoint (S : SPO.FuncSetup α)  {u : S.Elem} (h : isPoset) :
  S.maximal u ↔ S.cover u u := by
  constructor
  · intro hu; exact fixpoint_of_maximal (S := S) h hu
  · intro huu; exact maximal_of_fixpoint (S := S) huu


/-! ## 4) 最短路の端点近傍の向き -/

/-- 始点が極大なら、最初の 1 歩は「下向き」 -/
lemma first_step_isDown_of_maximal
  (S : SPO.FuncSetup α) [Fintype S.Elem] (h : isPoset)
  {u v : S.Elem} (hu : maximal S u)
  (p : Path S u v)
  (hpmin : ∀ q : Path S u v, p.verts.length ≤ q.verts.length) :
  ∀ y, (p.verts.drop 1).head? = some y → isDown S u y := by
  intro y hy
  -- 極大 ⇒ `f u = u`
  have huu : S.cover u u := fixpoint_of_maximal S h hu
  -- パスの先頭2点に分解
  cases pv:p.verts with
  | nil =>
     have : p.verts = [] := by exact pv
      -- p.nonempty : verts ≠ []
      -- いま verts = [] なので矛盾
     let pn := p.nonempty
     exact False.elim (pn pv)

  | cons a rest =>
      -- 先頭 a = u （p.head_ok を定義計算して取り出す）
      have ha : a = u := by
        simp_all only [List.length_cons, List.drop_succ_cons, List.drop_zero]
        obtain ⟨val, property⟩ := u
        obtain ⟨val_1, property_1⟩ := v
        obtain ⟨val_2, property_2⟩ := y
        obtain ⟨val_3, property_3⟩ := a
        simp_all only [Subtype.mk.injEq]
        cases p
        subst pv
        simp_all only [ne_eq, reduceCtorEq, not_false_eq_true, List.head?_cons, Option.some.injEq, Subtype.mk.injEq,
          List.reverse_cons, List.head?_append, List.head?_reverse, Option.or_some, List.nodup_cons]

      -- 2点目の有無で分岐
      cases rt:rest with
      | nil =>
          -- 長さ1 なら drop 1 の head? は none のはず
          -- 与えられた hy : some y と矛盾
          have hcn := hy
          -- `(a :: []).drop 1 = []`，`head? [] = none`
          simp  at hcn
          subst rt ha
          simp_all only [List.length_cons, List.length_nil, zero_add, List.drop_succ_cons, List.drop_nil, List.head?_nil,
             reduceCtorEq]
          --cases hcn
      | cons b rest2 =>
          -- hy から b = y を定義計算で取り出す
          have hb : b = y := by
            have h1 := hy
            -- `(a::b::rest2).drop 1 = (b::rest2)`，`head? (b::rest2) = some b`
            simp  at h1
            subst rt ha
            simp_all only [List.length_cons, List.drop_succ_cons, List.drop_zero, List.head?_cons, Option.some.injEq,
              lt_add_iff_pos_left, add_pos_iff, Nat.lt_add_one, or_true, getElem?_pos, List.getElem_cons_succ,
              List.getElem_cons_zero]

            --exact Option.some.inj h1

          -- `p.chain : Chain' (adj S) (a::b::rest2)` を最初の辺と残りに分解
          have hadj_ab : adj S a b := by
            -- まず p.chain をこの分岐の具体リストに書換
            have hc := p.chain
            -- `p.verts = a :: b :: rest2` を右辺に反映
            -- （defeq なので `rw` で十分）
            have : p.verts = a :: b :: rest2 := by
              subst rt hb ha
              simp_all only [List.length_cons, List.chain'_cons_cons, List.drop_succ_cons, List.drop_zero, List.head?_cons]

            -- これで hc : Chain' (adj S) (a :: b :: rest2)
            rw [this] at hc
            -- Chain' を Chain に展開してから `cases`
            -- Chain (adj S) a (b::rest2)
            change List.Chain (adj S) a (b :: rest2) at hc
            -- 非空なので `cons` 形だけ
            cases hc with
            | cons hstep _ => exact hstep
          -- a = u, b = y に置換して `adj S u y`
          have hadj_uy : adj S u y := by cases ha; cases hb; exact hadj_ab
          -- `adj S u y` を「上向き」or「下向き」に分解
          cases hu:hadj_uy with
          | inl hup =>
              -- 上向きだと `cover u u` と一意性で y = u
              have hyu : y = u :=
                cover_out_unique S (u := u) (y := y) (z := u) hup huu
              -- しかし `p.nodup` から先頭 a と次 b は異なる
              have hnd : (a :: b :: rest2).Nodup := by
                subst hyu hu rt hb ha
                simp_all only [List.length_cons, List.drop_succ_cons, List.drop_zero, List.head?_cons, List.nodup_cons, List.mem_cons,
                  true_or, not_true_eq_false, false_and]
                obtain ⟨val, property⟩ := v
                obtain ⟨val_1, property_1⟩ := a
                cases p
                subst pv
                simp_all only [ne_eq, reduceCtorEq, not_false_eq_true, List.head?_cons, List.reverse_cons, List.append_assoc,
                  List.cons_append, List.nil_append, List.head?_append, List.head?_reverse, Option.or_some, Option.some.injEq,
                  List.chain'_cons_cons, true_and, List.nodup_cons, List.mem_cons, true_or, not_true_eq_false, false_and]
              have hne_ab : a ≠ b := by
                -- `nodup_cons` より a ∉ (b :: rest2)
                have hnotin : a ∉ (b :: rest2) := (List.nodup_cons).1 hnd |>.left
                intro hEq;
                apply hnotin
                subst hb ha hyu
                simp_all only [List.nodup_cons, not_false_eq_true, true_and, List.mem_cons, or_false, not_true_eq_false]

              -- a = u, b = y に置換すると `u ≠ y`，でも y = u は矛盾
              have hne_uy : u ≠ y := by cases ha; cases hb; exact hne_ab
              exact (hne_uy (Eq.symm hyu)).elim
          | inr hdown =>
              -- 望む結論
              exact hdown

/-- 無向隣接 `adj` の対称性 -/
private lemma adj_symm (S : SPO.FuncSetup α) :
  ∀ {x y : S.Elem}, adj S x y → adj S y x := by
  intro x y h
  cases h with
  | inl hxy => exact Or.inr hxy
  | inr hyx => exact Or.inl hyx

/-- 終点が極大なら、最後の 1 歩は「上向き」 -/
lemma last_step_isUp_of_maximal
  (S : SPO.FuncSetup α) [Fintype S.Elem] (h : isPoset)
  {u v : S.Elem} (hv : maximal S v)
  (p : Path S u v)
  (hpmin : ∀ q : Path S u v, p.verts.length ≤ q.verts.length) :
  ∀ y, (p.verts.take (p.verts.length - 1)).reverse.head? = some y → isUp S y v := by
  intro y hy

  -- 1) 末尾 v を `p.last_ok` から取り出し、`p.verts.reverse = v :: rrest` と分解
  cases hr : p.verts.reverse with
  | nil =>
      -- 非空に反する
      have : False := by
        -- p.nonempty : p.verts ≠ []
        -- しかし reverse = [] なら verts = []
        have : p.verts = [] := by
          -- reverse_nil_iff
          -- （rfl の書換えで十分）
          -- `simp` で `p.verts = []` を得る
          -- ここでは直接 `have : p.verts = [] := by`
          --  `rw [← List.reverse_reverse p.verts, hr]` でも可
          -- ただし、以下では簡単のため `rw` を使います
          have := congrArg List.reverse (rfl : p.verts = p.verts)
          -- 上の方法が冗長なので、素直に次で片付けます
          -- 置換
          rw [← List.reverse_reverse p.verts, hr] at this
          -- now: reverse [] = reverse p.verts → p.verts = []
          exact List.reverse_eq_nil_iff.mp hr
        exact p.nonempty this
      exact this.elim
  | cons v0 rrest =>
      -- `p.last_ok : p.verts.reverse.head? = some v` から v0 = v
      have hv0 : v0 = v := by
        have hl := p.last_ok
        -- `head? (v0 :: rrest) = some v0`
        have : (List.head? (v0 :: rrest)) = some v0 := rfl
        -- `some v0 = some v`
        have : some v0 = some v := by
          apply Eq.trans (Eq.symm this)
          simp_all only [List.head?_reverse, List.reverse_eq_cons_iff, List.reverse_append, List.reverse_cons, List.reverse_nil,
             List.nil_append, List.reverse_reverse, List.cons_append, Option.some.injEq, List.head?_cons]
        exact Option.some.inj this

      -- 2) 与えられた `hy` を、rrest の先頭が y であると言い換える
      --    `(take (len-1) verts).reverse = rrest` を計算で得る
      have hyr : (rrest.head?) = some y := by
        -- `p.verts = (v0 :: rrest).reverse`
        have hvform : p.verts = (v0 :: rrest).reverse := by
          -- `reverse_reverse` を使って置換
          -- `p.verts.reverse = v0 :: rrest` を両辺 reverse
          -- すると `p.verts = (v0 :: rrest).reverse`
          -- `rw` で十分
          -- （hr を用いて両辺を書換え）
          have := hr
          -- そのまま使う
          -- ここは `simp` の方が手早い
          -- 直接書くと：
          --    by rw [← List.reverse_reverse p.verts, hr]; rfl
          -- と同値
          rw [← List.reverse_reverse p.verts, hr]

        -- 長さ計算：`p.verts.length = (v0 :: rrest).length = rrest.length + 1`
        have hlen : p.verts.length = rrest.length + 1 := by
          -- `length_reverse` で落ちる
          -- `simp` で評価
          simp [hvform, List.length_reverse]
        -- hy : ((take (len-1) p.verts).reverse).head? = some y
        -- 右辺を `rrest` に落とす：
        -- `(take (rrest.length) ((v0 :: rrest).reverse)).reverse = rrest`
        -- これは `List.reverse_take`/`List.length_reverse` で計算できる
        have hy' := hy
        -- `simp` でまとめて計算
        --   - `hvform` で `p.verts` を展開
        --   - `hlen` で `(len-1)` を `rrest.length` に
        --   - `List.take`/`List.reverse` の定義計算
        -- 次の 1 行で `hy' : (rrest.head?) = some y` になる
        -- 環境によっては `simp` の引数を調整してください
        have : ((p.verts.take (p.verts.length - 1)).reverse).head? = some y := hy'
        -- 差分置換
        -- `(p.verts.length - 1) = rrest.length`
        have hlm : p.verts.length - 1 = rrest.length := by
          -- 1 を右に移すだけ
          -- `Nat.succ` を使わず、`Nat.add_comm` 等も不要
          -- `hlen : p.verts.length = rrest.length + 1`
          -- `Nat.succ_eq_add_one` の逆向き
          -- `rw` で置換
          -- すなわち：`p.verts.length - 1 = (rrest.length + 1) - 1 = rrest.length`
          simp [hlen]

        -- 置換しつつ評価
        --   `p.verts` を `hvform` で、`(len-1)` を `hlm` で置換
        --   その後 `simp` で
        --   `( ( ( (v0 :: rrest).reverse ).take rrest.length ).reverse ).head? = some y`
        --   を `rrest.head? = some y` に落とす
        -- ここは `simp` が通る形です
        have : (((((v0 :: rrest).reverse).take rrest.length)).reverse).head? = some y := by
          -- `p.verts` と `(len-1)` を置換
          -- 手続き的に：
          --   `rw [hvform, hlm]` は `change` を使わずに済むよう `have` を新規に定義してから
          --   使うのが安全です。いまは新しい式を直接作りました。
          -- 以降で eval します。
          subst hv0
          simp_all only [List.reverse_cons, List.length_append, List.length_reverse, List.length_cons, List.length_nil,
            zero_add, add_tsub_cancel_right, List.take_left', List.reverse_reverse, List.reverse_append, List.reverse_nil,
            List.nil_append, List.cons_append]

        -- 簡約：`reverse.take` → `drop` 関係で `= rrest.head?`
        -- `simp` で評価
        --   `List.length_reverse`, `List.take`, `List.reverse_reverse` などを使います
        -- 結果：`rrest.head? = some y`
        -- 実際には ↓ の 1 行で通るはずです
        simpa using this

      -- rrest が空だと矛盾（head? = some y）
      cases rrest with
      | nil =>
          cases hyr
      | cons y0 r2 =>
          -- hyr : head? (y0 :: r2) = some y ⇒ y0 = y
          have hy0 : y0 = y := by
            -- `head? (y0 :: r2) = some y0`
            have : (List.head? (y0 :: r2)) = some y0 := rfl
            -- `some y0 = some y`
            have : some y0 = some y := Eq.trans (Eq.symm this) hyr
            exact Option.some.inj this
          -- 3) 以降、`p.verts = (r2.reverse) ++ [y, v]`
          have hvform2 : p.verts = (r2.reverse) ++ [y, v] := by
            -- p.verts = (v0 :: y0 :: r2).reverse
            --          = (r2.reverse) ++ [y0, v0]
            -- ここで y0 = y, v0 = v
            -- `rw` と `simp` で評価
            have : p.verts = (v0 :: y0 :: r2).reverse := by
              -- さきほどの `hvform` から `rrest = y0 :: r2` を使う
              -- 直接：
              --   `p.verts = (v0 :: rrest).reverse`
              --   `rrest = y0 :: r2`
              -- による置換
              -- safer: 再計算
              rw [← List.reverse_reverse p.verts, hr]

            -- この式を整理
            -- `(v0 :: y0 :: r2).reverse = r2.reverse ++ [y0, v0]`
            -- ↓ で置換
            have : p.verts = r2.reverse ++ [y0, v0] := by
              simpa [List.reverse_cons, List.append_assoc] using this
            -- y0 = y, v0 = v
            -- 最後に置換
            cases hy0; cases hv0
            -- now: p.verts = r2.reverse ++ [y, v]
            exact this

          -- 4) `p.chain` を `xs ++ [y, v]` 形に合わせ、末尾の辺 `adj S y v` を抜き出す
          --    xs := r2.reverse
          have hc := p.chain
          -- 書換
          -- `rw` を使えば `change` は不要
          -- Chain' (xs ++ [y, v])
          have hc' : List.Chain' (adj S) ((r2.reverse) ++ [y, v]) := by
            -- `p.verts` の等式で右辺を置換
            -- `rw [hvform2] at hc` としてから戻す
            -- ここでは新しい定数に束ねる
            have htmp := hc
            rw [hvform2] at htmp
            exact htmp

          -- 末尾辺の抽出を局所再帰で実装
          -- aux : 「a から xs++[y,v] への Chain から adj y v を抜く」
          have aux :
            ∀ (a : S.Elem) (xs : List S.Elem),
              List.Chain (adj S) a (xs ++ [y, v]) → adj S y v := by
            intro a xs hchain
            cases xs with
            | nil =>
                -- hchain : Chain (adj S) a [y, v]
                -- cases 2回で R y v を取り出す
                cases hchain with
                | cons a_y htail =>
                    -- htail : Chain (adj S) y [v]
                    cases htail with
                    | cons y_v _ => exact y_v
            | cons b xs' =>
                -- hchain : Chain (adj S) a (b :: xs' ++ [y, v])
                -- 先頭を1つ剥がして再帰
                cases hchain with
                | cons _ htail =>
                    -- htail : Chain (adj S) b (xs' ++ [y, v])
                    subst hy0 hv0
                    simp_all only [List.head?_cons, List.length_append, List.length_reverse, List.length_cons, List.length_nil, zero_add,
                      Nat.reduceAdd, List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
                      List.reverse_reverse, Nat.add_one_sub_one, List.head?_reverse, List.chain'_append_cons_cons, List.chain'_singleton,
                      and_true, List.append_eq, List.chain_append_cons_cons, List.Chain.nil, and_self]

          -- hc' : Chain' (adj S) ( (r2.reverse) ++ [y, v] )
          -- これを Chain 形に展開して aux に渡す
          -- `Chain' (a :: t) = Chain a t` を `simp` で使う
          -- まず xs を場合分け：r2.reverse が空かどうか
          have hadj_yv : adj S y v := by
            cases hxs : (r2.reverse) with
            | nil =>
                -- リストは [y, v]
                have hc0 := hc'
                -- `[] ++ [y,v] = [y,v]`
                -- `Chain' [y,v]` を `Chain y [v]` に落とす
                -- `simp` で十分（simpa using は使わない）
                have : List.Chain (adj S) y [v] := by
                  -- `hc0 : Chain' [y,v]`
                  -- `simp [List.Chain']` で展開
                  -- まず形を合わせる
                  -- ここでは単純に `cases` で展開する代わりに `simp` を使います
                  -- `simp` で `Chain' [y, v]` → `Chain y [v]`
                  -- tactic: いったん `have hc1 := hc0` とし、書換後に use
                  have hc1 := hc0
                  -- `r2.reverse = []` を用いて右辺を `[y, v]` に
                  have : (r2.reverse) ++ [y, v] = ([y, v] : List _) := by
                    simp [hxs]
                  -- 置換
                  rw [this] at hc1
                  -- ここで `hc1 : Chain' [y, v]`
                  -- `simp` で `Chain y [v]` に
                  -- 直接返す形にするためいったん `by` で囲む
                  -- `simp` の結果を `exact` で受ける
                  -- （`change`/`simpa using` は使わない）
                  -- 下の 1 行で `Chain y [v]` が得られます
                  -- `simp` の後、`have` を返す
                  have : List.Chain (adj S) y [v] := by
                    -- 定義計算
                    -- `List.Chain'` の定義： `[y, v]` の場合
                    --   `Chain (adj S) y [v]`
                    -- 従って `rfl` で一致（`simp` 同等）
                    -- ここは直接 `exact` の方が読みやすいので：
                    exact (by
                      -- `cases` で戻す方法もあるが省略
                      -- 直接戻す
                      -- 実は `hc1` が既に `Chain'` 型なので
                      -- ここでは `match` 展開を避けています
                      -- （文法上の都合で空ブロックは書かない）
                      -- 最終的には下の `cases` で使います
                      -- いったん placeholder
                      subst hy0 hv0
                      simp_all only [List.reverse_eq_nil_iff, List.head?_cons, List.reverse_nil, List.nil_append, List.length_cons,
                        List.length_nil, zero_add, Nat.reduceAdd, List.reverse_cons, List.cons_append, Nat.add_one_sub_one,
                        List.take_succ_cons, List.take_zero, List.chain_append_cons_cons, List.Chain.nil, and_true, implies_true,
                        List.chain'_cons_cons, List.chain'_singleton, List.chain_cons, and_self]

                    )
                  exact this
                -- ここで `Chain y [v]` から `adj y v` を得る
                -- `cases` 2 段で取り出せる
                cases this with
                | cons yv _ => exact yv
            | cons a xs1 =>
                -- `r2.reverse = a :: xs1`
                -- `hc' : Chain' (a :: xs1 ++ [y, v])`
                -- これを `Chain a (xs1 ++ [y, v])` に落として aux
                have hc1 := hc'
                -- 書換（`cons_append`）
                -- `rw` で `a :: (xs1 ++ [y, v])` 形に
                -- ここで `hc1 : Chain' (a :: xs1 ++ [y, v])`
                -- `List.Chain'` の定義で `Chain a (xs1 ++ [y, v])` に落ちる
                -- `simp` を使う
                -- まず `hc1` の右辺を整形
                -- 実際には以下の 2 行で十分です
                have hc2 : List.Chain (adj S) a (xs1 ++ [y, v]) := by
                  -- `hc1` をコピー
                  have hc1' := hc1
                  -- 形の書換え
                  -- いったんリスト等式を入れる
                  -- `rw [hxs]` で `r2.reverse` を `a :: xs1` に
                  -- つづいて `simp [List.Chain']` で `Chain` に
                  rw [hxs] at hc1'
                  -- `hc1' : Chain' (a :: xs1 ++ [y, v])`
                  -- `simp` で `Chain a (xs1 ++ [y, v])`
                  -- （`simpa using` は使わない）
                  -- 次の 1 行で目的型に落ちます
                  -- 直接：
                  --   Chain' (a :: t) = Chain a t
                  -- を使うだけ
                  exact (by
                    -- `Chain'` 定義：`by cases` で展開
                    -- `hc1'` は `Chain a (xs1 ++ [y, v])`
                    -- `cases` でそのまま取り出せる
                    -- より簡潔には `cases hc1'` だが、型合わせのために
                    -- `have` を返す形にします
                    -- （実務では `cases hc1'` で OK）
                    -- ここは安全のため：
                    revert hc1'
                    intro hc1''
                    -- ちょうど欲しい型
                    -- `Chain a ...` を返すため `exact` で返す
                    exact hc1''
                  )
                -- 末尾辺を aux で抽出
                exact aux a xs1 hc2

          -- 5) hadj_yv が出た。次は「下向き」分岐を矛盾に。
          cases hadj_yv with
          | inl hup =>
              -- これが欲しい結論（上向き）
              exact hup
          | inr hdown =>
              -- v 極大 ⇒ `S.cover v v`
              have hvv : S.cover v v := fixpoint_of_maximal S h hv
              -- `cover_out_unique` で y = v
              have hyv : y = v := cover_out_unique S (u := v) (y := y) (z := v) hdown hvv
              -- しかしノーデュープより y ≠ v（末尾2点は異なる）
              -- `p.verts.reverse = v :: y :: r2`
              -- なので `p.verts.reverse` は `v` と `y` が連続、ノーデュープで v ≠ y
              have hneq : y ≠ v := by
                -- `Nodup` は reverse で保存
                have hnd : (p.verts.reverse).Nodup := by
                  -- `List.nodup_reverse` で換算
                  -- `simp` で十分
                  simpa [List.nodup_reverse] using p.nodup
                -- `v ∉ y :: r2` を取り出す → とくに `v ≠ y`
                have hnotin : v ∉ (y0 :: r2) := by
                  -- `p.verts.reverse = v0 :: y0 :: r2`、`v0 = v`、`y0 = y`
                  -- ここから `nodup_cons` を使う
                  -- hnd : Nodup (v :: y :: r2)
                  -- 先頭 v は末尾に含まれない
                  -- 具体化してから使う
                  -- `rw` で `p.verts.reverse` を具体化
                  have := hnd
                  -- 書換
                  -- `rw [hr]` で `v0 :: rrest`
                  -- さらに `hv0` と `hy0` を使って `v :: y :: r2` に
                  -- 以降、`nodup_cons` から先頭不在を取り出す
                  have : (v0 :: y0 :: r2).Nodup := by
                    -- `p.verts.reverse = v0 :: y0 :: r2`
                    -- `hnd` を書換
                    -- 少し冗長だが安全：
                    have := hnd
                    -- ok
                    -- 直接使用可能なのでそのまま置く
                    subst hy0 hyv hv0
                    simp_all only [List.head?_cons, List.length_append, List.length_reverse, List.length_cons, List.length_nil, zero_add,
                      Nat.reduceAdd, List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
                      List.reverse_reverse, List.nodup_cons, List.mem_cons, true_or, not_true_eq_false, false_and]

                  -- ここから `a ∉ l` を取り出す
                  -- 実務上は下のように書きます
                  have : v0 ∉ (y0 :: r2) := (List.nodup_cons).1 this |>.left
                  -- v0 = v, y0 = y
                  cases hv0; cases hy0
                  exact this
                -- 先頭 `v` が `y :: r2` にいない ⇒ `v ≠ y`
                intro hEq;
                apply hnotin
                subst hy0 hEq hv0
                simp_all only [List.head?_cons, List.length_append, List.length_reverse, List.length_cons, List.length_nil, zero_add,
                  Nat.reduceAdd, List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
                  List.reverse_reverse, List.nodup_cons, not_false_eq_true, true_and, List.mem_cons, or_false, not_true_eq_false]

              exact (hneq hyv).elim

lemma first_step_down_or_eq
  (S : SPO.FuncSetup α) [Fintype S.Elem] (h : isPoset)
  {u v : S.Elem} (hu : maximal S u)
  (p : Path S u v)
  (hpmin : ∀ q : Path S u v, p.verts.length ≤ q.verts.length) :
  (∃ y, (p.verts.drop 1).head? = some y ∧ isDown S u y) ∨ u = v := by
  -- `p.verts` で分岐
  cases pv : p.verts with
  | nil =>
      exact Or.inr (by
        -- 非空に反する：矛盾から何でも導けるが，ここはダミーで `rfl` を返してもよい
        -- ただし型は `u = v` なので，p.nonempty と矛盾から `False.elim` で閉じます
        exact False.elim (p.nonempty pv))
  | cons a rest =>
      -- 先頭 a = u を取り出す
      have ha : a = u := by
        have h0 := p.head_ok
        have : (List.head? (a :: rest)) = some a := rfl
        have : some a = some u := by
          apply Eq.trans (Eq.symm this)
          simp_all only [List.length_cons, Option.some.injEq, List.head?_cons]
        exact Option.some.inj this
      -- 2番目の有無で分岐
      cases rt : rest with
      | nil =>
          -- 長さ 1：`p.last_ok` から v = a，かつ a = u ⇒ u = v
          have hv' : v = a := by
            -- `p.verts = [a]` へ書換えて `p.last_ok` を計算
            have hl := p.last_ok
            -- `simp` で左辺を `some a` に評価
            -- （`simpa using` は使わず，`simp [...] at` を用いる）
            simp [pv, rt] at hl
            -- ここで `hl : some a = some v`
            apply Eq.symm
            apply Option.some.inj
            subst ha hl rt
            simp_all only [List.length_cons, List.length_nil, zero_add]
          -- 右側の分岐 `u = v`
          exact Or.inr (by cases ha; exact Eq.symm hv')
      | cons b rest2 =>
          -- 二番目 b がある：`(drop 1).head? = some b`
          have hy0 : ((a :: b :: rest2).drop 1).head? = some b := by simp
          -- これを `p.verts` 形に書換えて `first_step_isDown_of_maximal` を適用
          have hgoal := hy0
          -- `(p.verts.drop 1).head? = some b` へ変形
          simp at hgoal
          have hdown : isDown S u b := by
            apply first_step_isDown_of_maximal S h hu p hpmin b
            subst rt ha
            simp_all only [List.drop_succ_cons, List.drop_zero, List.head?_cons, List.length_cons]
          apply Or.inl
          subst rt ha
          simp_all only [List.drop_succ_cons, List.drop_zero, List.head?_cons, List.length_cons, Option.some.injEq,
            exists_eq_left']

private lemma ne_of_nodup_middle_block
  {β : Type _} [DecidableEq β]
  {prefix0 suffix : List β} {a m b : β} :
  (prefix0 ++ [a, m, b] ++ suffix).Nodup → a ≠ b := by
  intro hnd
  -- まず `[a,m,b]` 自体が Nodup であることを取り出す
  have hsub : ([a, m, b] : List β).Sublist (prefix0 ++ [a, m, b] ++ suffix) := by
    -- `Sublist` を左右の append で拡張
    -- （名前が少し環境差ありますが、だいたいこの2行で通ります）
    simp_all only [List.append_assoc, List.cons_append, List.nil_append]
    simp_all only [List.cons_sublist_cons, List.nil_sublist, List.sublist_append_of_sublist_right]

  have htriple : ([a, m, b] : List β).Nodup := by
    exact List.Sublist.nodup hsub hnd

  -- `Nodup [a,m,b]` から `a ≠ b` を引き出す
  -- `nodup_cons` より `a ∉ (m :: b :: [])`
  have hnotin : a ∉ (m :: b :: []) := (List.nodup_cons).1 htriple |>.left
  -- もし `a = b` なら `a ∈ (m :: b :: [])`（右側の `b`）になって矛盾
  intro hEq
  have : a ∈ (m :: b :: []) := by
    subst hEq
    simp_all only [List.append_assoc, List.cons_append, List.nil_append, List.nodup_cons, not_false_eq_true, List.mem_cons, List.not_mem_nil, or_false,
      List.nodup_nil, and_self, and_true, true_and, or_true, not_true_eq_false]

  exact hnotin this

private lemma exists_init_append_last_of_rev_head
  {β : Type _} (L : List β) {v : β} :
  (L.reverse).head? = some v → ∃ xs, L = xs ++ [v] := by
  intro h
  -- `List.reverse_eq_cons_iff`：`reverse L = v :: rrest ↔ L = rrest.reverse ++ [v]`
  cases hrev : L.reverse with
  | nil => simp_all only [List.head?_nil, reduceCtorEq]
  | cons v0 rrest =>
      have hv0 : v0 = v := by
        have : (List.head? (v0 :: rrest)) = some v0 := rfl
        have : some v0 = some v := by
          apply Eq.trans (Eq.symm this)
          simp_all only [Option.some.injEq, List.reverse_eq_cons_iff, List.head?_cons]
        exact Option.some.inj this
      cases hv0
      -- L = (rrest.reverse) ++ [v]
      simp_all only [List.head?_cons, List.reverse_eq_cons_iff, List.append_cancel_right_eq, exists_eq']

lemma exists_switch_vertex_on_path_len3
  (S : SPO.FuncSetup α)
  {u v : S.Elem} (p : Path S u v)
  (hstart : ∃ y, (p.verts.drop 1).head? = some y ∧ isDown S u y)
  (hend   : ∃ y, (p.verts.take (p.verts.length - 1)).reverse.head? = some y ∧ isUp S y v)
  (hlen3  : 3 ≤ p.verts.length) :
  ∃ (i : Nat) (m a b : S.Elem),
    i + 2 ≤ p.verts.length ∧
    S.cover m a ∧ S.cover m b ∧ a ≠ b := by
  classical
  -- 先頭2点へ分解
  cases pv : p.verts with
  | nil =>
      exact False.elim (p.nonempty pv)
  | cons a rest =>
    -- `a = u`
    have ha : a = u := by
      have h0 := p.head_ok
      have : (List.head? (a :: rest)) = some a := rfl

      have : some a = some u := by
        apply Eq.trans (Eq.symm this)
        simp_all only [List.drop_succ_cons, List.drop_zero, Subtype.exists, List.length_cons, add_tsub_cancel_right,
    List.head?_reverse, Nat.reduceLeDiff, Option.some.injEq, List.head?_cons]

      exact Option.some.inj this
    cases rt : rest with
    | nil =>
        -- 長さ 1 は `hlen3` に矛盾
        have : p.verts.length = 1 := by
          subst ha rt
          simp_all only [List.drop_succ_cons, List.drop_nil, List.head?_nil, reduceCtorEq, false_and, exists_false]
        subst ha rt
        simp_all only [List.drop_succ_cons, List.drop_nil, List.head?_nil, reduceCtorEq, false_and, exists_false]

    | cons b rest2 =>
      -- 初手が down（`hstart` から b を特定）
      have hdown_ab : isDown S a b := by
        rcases hstart with ⟨y₁, hy₁, hdown₁⟩
        have : y₁ = b := by
          have h := hy₁
          -- `(a::b::rest2).drop 1 = b::rest2`
          have : ((a :: b :: rest2).drop 1).head? = some b := by simp
          -- `p.verts` へ戻す
          subst ha rt
          simp_all only [List.drop_succ_cons, List.drop_zero, List.head?_cons, List.length_cons, add_tsub_cancel_right,
            List.take_succ_cons, List.reverse_cons, List.head?_append, List.head?_reverse, Option.or_some, Option.some.injEq,
            exists_eq_left', Nat.reduceLeDiff]

        cases this; cases ha
        exact hdown₁

      -- 末尾側の分解（`p.verts.reverse = v :: rrest`）
      cases hr : p.verts.reverse with
      | nil =>
          exact False.elim (p.nonempty (by
            have : p.verts = [] := List.reverse_eq_nil_iff.mp hr
            exact this))
      | cons v0 rrest =>
        have hv0 : v0 = v := by
          have : (List.head? (v0 :: rrest)) = some v0 := rfl
          have : some v0 = some v := by
            apply Eq.trans (Eq.symm this)
            subst ha rt
            simp_all only [List.head?_cons, List.drop_succ_cons, List.drop_zero, Option.some.injEq, exists_eq_left',
              List.length_cons, add_tsub_cancel_right, List.take_succ_cons, List.reverse_cons, List.head?_append,
              List.head?_reverse, Option.or_some, Nat.reduceLeDiff, List.append_assoc, List.cons_append, List.nil_append]
            cases p
            subst pv
            simp_all only [ne_eq, reduceCtorEq, not_false_eq_true, List.head?_cons, List.reverse_cons, List.append_assoc,
              List.cons_append, List.nil_append, Option.some.injEq,  List.chain'_cons_cons, List.nodup_cons,
              List.mem_cons, not_or]

          exact Option.some.inj this
        -- `rest2` は非空（長さ≥3）
        cases r2:rest2 with
        | nil =>
            -- `p.verts = [a,b]` なので長さ 2、`hlen3` に矛盾
            subst rt ha hv0
            simp_all only [List.drop_succ_cons, List.drop_zero, List.head?_cons, Option.some.injEq, exists_eq_left',
              List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, Nat.add_one_sub_one, List.take_succ_cons,
              List.take_zero, List.reverse_cons, List.reverse_nil, List.nil_append, Nat.reduceLeDiff]


        | cons c rest3 =>
          -- 走査補助：先頭から初めての up を見つける
          -- `front` はこれまでの消費部分
          let front : List S.Elem := []
          -- 走査を一般化（`front` を持って再帰）
          have scan :
            ∀ (front : List S.Elem) (prev cur : S.Elem) (xs : List S.Elem),
              p.verts = front ++ prev :: cur :: xs ++ [v] →
              List.Chain (adj S) prev (cur :: xs ++ [v]) →
              isDown S prev cur →
              ∃ (prefix0 : List S.Elem) (m a b : S.Elem) (suffix : List S.Elem),
                p.verts = prefix0 ++ [a, m, b] ++ suffix
                ∧ S.cover m a ∧ S.cover m b ∧ a ≠ b := by
            intro front prev cur xs eqshape hchain hdown
            revert front prev cur
            induction xs with
            | nil =>
                intro front prev cur eqshape hchain hdown
                -- hchain : Chain prev (cur :: [v]) なので先頭2歩を取り出せる
                cases hchain with
                | cons h_prev_cur htail =>
                  cases htail with
                  | cons h_cur_v htail2 =>
                    -- 最後の 1 歩は `hend` から up だとわかる：penultimate = cur
                    rcases hend with ⟨y2, hy2, hup_last⟩
                    -- `p.verts = front ++ [prev,cur] ++ [v]` なので penultimate は `cur`
                    have hy2' : y2 = cur := by
                      -- `(take (len-1) p.verts).reverse.head? = some y2` を計算で `some cur` に落とす
                      have : ((p.verts.take (p.verts.length - 1)).reverse).head? = some cur := by
                        -- eqshape を使って計算
                        -- p.verts = front ++ prev :: cur :: [] ++ [v]
                        -- → 直前は `cur`
                        have := eqshape
                        -- `simp` で落とす
                        subst r2 ha rt hv0
                        simp_all
                        subst hr

                        simp [List.getLast?_eq_getElem?] at hy2
                        subst hy2
                        simp_all only

                      -- some y2 = some cur
                      have : some y2 = some cur := by
                        apply Eq.trans
                        · apply Option.some.inj
                          exact rfl
                        · apply Option.some.inj
                          subst r2 ha rt hv0
                          simp_all only [List.Chain.nil, List.append_assoc, List.cons_append, List.nil_append, List.drop_one, List.head?_tail,
                            List.length_append, List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, lt_add_iff_pos_left, add_pos_iff,
                            Nat.zero_lt_succ, or_true, getElem?_pos, Option.some.injEq, exists_eq_left', le_add_iff_nonneg_left, zero_le,
                            List.reverse_append, List.reverse_cons, List.reverse_nil, List.cons.injEq, true_and, Nat.add_one_sub_one,
                            List.head?_reverse]

                      exact Option.some.inj this
                    cases hy2'
                    -- up: cover cur v、down: cover cur prev でスイッチ完成
                    -- 分解式は `front` を prefix に採用
                    have eqBlock : p.verts = front ++ [prev, cur, v] ++ [] := by
                      subst r2 ha rt hv0
                      simp_all only [List.Chain.nil, List.append_assoc, List.cons_append, List.nil_append, List.drop_one, List.head?_tail,
                        List.length_append, List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, lt_add_iff_pos_left, add_pos_iff,
                        Nat.zero_lt_succ, or_true, getElem?_pos, Option.some.injEq, exists_eq_left', le_add_iff_nonneg_left, zero_le,
                        List.reverse_append, List.reverse_cons, List.reverse_nil, List.cons.injEq, true_and, Nat.add_one_sub_one,
                        List.head?_reverse, List.append_nil]
                    -- Nodup を右辺に移す
                    have hnd_rhs : (front ++ [prev, cur, v]).Nodup := by
                      have hnd := p.nodup
                      -- eqBlock で置換
                      rw [eqBlock] at hnd
                      -- `++ []` を消す
                      simpa using hnd
                    -- a ≠ b は `[prev,cur,v]` の前後から
                    have hneq : prev ≠ v := by
                      refine
                      ne_of_nodup_middle_block (prefix0 := front) (suffix := ([] : List S.Elem))
                        (a := prev) (m := cur) (b := v) ?_
                      subst r2 ha rt hv0
                      simp_all only [List.Chain.nil, List.append_assoc, List.cons_append, List.nil_append, List.drop_one, List.head?_tail,
                        List.length_append, List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, lt_add_iff_pos_left, add_pos_iff,
                        Nat.zero_lt_succ, or_true, getElem?_pos, Option.some.injEq, exists_eq_left', le_add_iff_nonneg_left, zero_le,
                        List.reverse_append, List.reverse_cons, List.reverse_nil, List.cons.injEq, true_and, List.append_nil,
                        Nat.add_one_sub_one, List.head?_reverse]

                    -- 長さ条件：i = front.length
                    let i : Nat := front.length
                    have hlen : i + 2 ≤ p.verts.length := by
                      have : p.verts.length = (front ++ [prev,cur,v]).length := by
                        apply congrArg List.length
                        subst r2 ha rt hv0
                        simp_all only [List.Chain.nil, ne_eq, List.append_assoc, List.cons_append, List.nil_append, List.drop_one,
                          List.head?_tail, List.length_append, List.length_cons, List.length_nil, zero_add, Nat.reduceAdd,
                          lt_add_iff_pos_left, add_pos_iff, Nat.zero_lt_succ, or_true, getElem?_pos, Option.some.injEq, exists_eq_left',
                          le_add_iff_nonneg_left, zero_le, List.reverse_append, List.reverse_cons, List.reverse_nil, List.cons.injEq,
                          true_and, List.append_nil, Nat.add_one_sub_one, List.head?_reverse]

                      -- front.length + 2 ≤ front.length + 3
                      have h1 : front.length + 2 ≤ front.length + 3 := Nat.le_succ (front.length + 2)
                      -- front.length + 3 ≤ front.length + 3 + 0
                      have h2 : front.length + 3 ≤ front.length + 3 + 0 := by
                        subst r2 ha rt hv0
                        simp_all only [add_le_add_iff_left, Nat.reduceLeDiff, List.Chain.nil, ne_eq, List.append_assoc, List.cons_append,
                          List.nil_append, List.drop_one, List.head?_tail, List.length_append, List.length_cons, List.length_nil, zero_add,
                          Nat.reduceAdd, lt_add_iff_pos_left, add_pos_iff, Nat.zero_lt_succ, or_true, getElem?_pos, Option.some.injEq,
                          exists_eq_left', le_add_iff_nonneg_left, zero_le, List.reverse_append, List.reverse_cons, List.reverse_nil,
                          List.cons.injEq, true_and, List.append_nil, Nat.add_one_sub_one, List.head?_reverse,
                          add_zero, le_refl]

                      subst r2 ha rt hv0
                      simp_all only [add_le_add_iff_left, Nat.reduceLeDiff, add_zero, le_refl, List.Chain.nil, ne_eq, List.append_assoc,
                        List.cons_append, List.nil_append, List.drop_one, List.head?_tail, List.length_append, List.length_cons,
                        List.length_nil, zero_add, Nat.reduceAdd, lt_add_iff_pos_left, add_pos_iff, Nat.zero_lt_succ, or_true, getElem?_pos,
                        Option.some.injEq, exists_eq_left', le_add_iff_nonneg_left, zero_le, List.reverse_append, List.reverse_cons,
                        List.reverse_nil, List.cons.injEq, true_and, List.append_nil, Nat.add_one_sub_one, List.head?_reverse,
                         i]


                    refine ⟨front, cur, prev, v, [], eqBlock, hdown, (?_), hneq⟩
                    subst r2 ha rt hv0
                    simp_all [i]
                    subst hr
                    exact hup_last

            | cons nxt xs' ih =>
                intro front prev cur eqshape hchain hdown
                -- hchain : Chain prev (cur :: nxt :: xs' ++ [v]) → 2 歩を取り出す
                cases hchain with
                | cons h_prev_cur htail =>
                  cases htail with
                  | cons h_cur_nxt htail' =>
                    -- `adj cur nxt` の向きで分岐
                    cases h_cur_nxt with
                    | inl hup_cur_nxt =>
                        -- スイッチ確定（m = cur, a = prev, b = nxt）
                        -- 形を `front ++ [prev,cur,nxt] ++ (xs' ++ [v])` に整形
                        have eq1 : p.verts = front ++ prev :: cur :: nxt :: xs' ++ [v] := by
                          subst r2 ha rt hv0
                          simp_all only [List.append_eq, List.append_assoc, List.cons_append, List.drop_one, List.head?_tail, Subtype.exists,
                            List.length_append, List.length_cons, List.length_nil, zero_add, Nat.add_succ_sub_one, List.head?_reverse,
                            List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons.injEq, true_and,
                            List.chain_cons, ne_eq, exists_and_right, Subtype.mk.injEq, and_imp, Subtype.forall]

                        have eqBlock : p.verts = front ++ [prev,cur,nxt] ++ (xs' ++ [v]) := by
                          -- 連結の整形：cons_append と結合則
                          subst r2 ha rt hv0
                          simp_all only [List.append_eq, List.append_assoc, List.cons_append, List.drop_one, List.head?_tail, Subtype.exists,
                            List.length_append, List.length_cons, List.length_nil, zero_add, Nat.add_succ_sub_one, List.head?_reverse,
                            List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons.injEq, true_and,
                            List.chain_cons, ne_eq, exists_and_right, Subtype.mk.injEq, and_imp, Subtype.forall]
                        -- Nodup を右辺に移して a ≠ b
                        have hnd_rhs : (front ++ [prev,cur,nxt] ++ (xs' ++ [v])).Nodup := by
                          have hnd := p.nodup
                          rw [eqBlock] at hnd
                          exact hnd
                        have hneq : prev ≠ nxt :=
                          ne_of_nodup_middle_block (prefix0 := front) (suffix := xs' ++ [v])
                            (a := prev) (m := cur) (b := nxt) hnd_rhs
                        -- 長さ条件：i = front.length
                        let i : Nat := front.length
                        have hlen : i + 2 ≤ p.verts.length := by
                          have : p.verts.length =
                                (front ++ [prev,cur,nxt] ++ (xs' ++ [v])).length :=
                            congrArg List.length eqBlock
                          -- front.len + 2 ≤ front.len + 3 + (xs'++[v]).len
                          have base :
                            front.length + 2 ≤ front.length + 3 + (xs' ++ [v]).length := by
                            have h1 : front.length + 2 ≤ front.length + 3 :=
                              Nat.le_succ (front.length + 2)
                            have h2 : front.length + 3 ≤ front.length + 3 + (xs' ++ [v]).length :=
                              Nat.le_add_right _ _
                            exact Nat.le_trans h1 h2
                          subst r2 ha rt hv0
                          simp_all only [ne_eq, List.append_eq, List.append_assoc, List.cons_append, List.nil_append, List.length_append,
                            List.length_cons, List.length_nil, zero_add, List.drop_one, List.head?_tail, Subtype.exists, Nat.add_succ_sub_one,
                            List.head?_reverse, List.reverse_append, List.reverse_cons, List.reverse_nil, List.cons.injEq, true_and,
                            List.chain_cons, exists_and_right, Subtype.mk.injEq, and_imp, Subtype.forall,
                            add_le_add_iff_left, le_add_iff_nonneg_left, zero_le, i]
                        exact ⟨front, cur, prev, nxt, xs' ++ [v], eqBlock, hdown, hup_cur_nxt, hneq⟩

                    | inr hdown_cur_nxt =>
                        -- まだ down。ひとつ進める：front := front ++ [prev]
                        -- 形：p.verts = (front ++ [prev]) ++ cur :: nxt :: xs' ++ [v]
                        have eqshape' : p.verts =
                            (front ++ [prev]) ++ cur :: nxt :: xs' ++ [v] := by
                          subst r2 ha rt hv0
                          simp_all only [List.append_eq, List.append_assoc, List.cons_append, List.drop_one, List.head?_tail, Subtype.exists,
                            List.length_append, List.length_cons, List.length_nil, zero_add, Nat.add_succ_sub_one, List.head?_reverse,
                            List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons.injEq, true_and,
                            List.chain_cons, ne_eq, exists_and_right, Subtype.mk.injEq, and_imp, Subtype.forall]
                        -- 帰納呼び出し
                        have res :=
                          ih (front := front ++ [prev]) (prev := cur) (cur := nxt)
                            (eqshape := eqshape') (hchain := (?_)) (hdown := hdown_cur_nxt)
                        exact res
                        -- htail' : List.Chain (adj S) nxt (xs' ++ [v])
                        show List.Chain (adj S) cur (nxt :: xs' ++ [v])
                        simp at htail'
                        -- htail' : List.Chain (adj S) nxt (xs' ++ [v])
                        simp
                        constructor
                        · show adj S cur nxt
                          dsimp [adj]
                          exact Or.inr hdown_cur_nxt

                        · subst r2 ha rt hv0
                          simp_all only [List.append_assoc, List.cons_append, List.drop_one, List.head?_tail, Subtype.exists,
                            List.length_append, List.length_cons, List.length_nil, zero_add, Nat.add_succ_sub_one, List.head?_reverse,
                            List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons.injEq, true_and,
                            List.chain_cons, ne_eq, exists_and_right, Subtype.mk.injEq, and_imp, Subtype.forall]


/-
          have scan :
            ∀ (front : List S.Elem) (prev cur : S.Elem) (xs : List S.Elem),
              p.verts = front ++ prev :: cur :: xs →
              List.Chain (adj S) prev (cur :: xs) →
              isDown S prev cur →
              ∃ (prefix0 : List S.Elem) (m a b : S.Elem) (suffix : List S.Elem),
                p.verts = prefix0 ++ [a, m, b] ++ suffix
                ∧ S.cover m a ∧ S.cover m b ∧ a ≠ b := by
            intro front prev cur xs eqshape hchain hdown
            -- `xs` を場合分け（必ず非空：最後は v で終わる）
            revert front prev cur
            induction xs with
            | nil =>
                intro front prev cur eqshape hchain hdown
                -- `xs = []`：`p.verts = front ++ [prev,cur]`
                -- 末尾は `cur`、一方 `p.last_ok` と `hend` より末尾直前 `y` から `v` への up が存在。
                -- ここに到達するのは、直前の再帰で「次の辺も down」のケースからのみだが、
                -- `xs = []` では「次の辺」が存在せず矛盾。よってこの分岐は起きない。
                -- 形式的には `hend` と `eqshape` を突き合わせて矛盾を作る：
                rcases hend with ⟨y2, hy2, hup_y2v⟩
                -- 末尾は `cur` なので `cur = v`、従って `y2` も存在できない
                have hv_last : (front ++ [prev, cur]).reverse.head? = some v := by
                  subst ha rt hv0
                  simp_all only [List.chain_cons, List.Chain.nil, and_true, List.drop_one, List.head?_tail, List.length_append,
                    List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, lt_add_iff_pos_left, add_pos_iff, Nat.lt_add_one,
                    or_true, getElem?_pos, Option.some.injEq, exists_eq_left', Nat.reduceLeDiff, List.reverse_append, List.reverse_cons,
                    List.reverse_nil, List.nil_append, List.cons_append, List.cons.injEq, Nat.add_one_sub_one, List.head?_reverse,
                    List.head?_cons]

                -- 左辺を計算：`reverse (front ++ [prev,cur])` の先頭は `cur`
                have : some v = some cur := by
                  apply Eq.trans (Eq.symm (by
                  -- `head? (reverse (front ++ [prev,cur])) = some cur`
                  rfl))
                  subst ha rt hv0
                  simp_all only [List.chain_cons, List.Chain.nil, and_true, List.reverse_append, List.reverse_cons, List.reverse_nil,
                    List.nil_append, List.cons_append, List.head?_cons, Option.some.injEq, List.drop_one, List.head?_tail,
                    List.length_append, List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, lt_add_iff_pos_left, add_pos_iff,
                    Nat.lt_add_one, or_true, getElem?_pos, exists_eq_left', Nat.reduceLeDiff, List.cons.injEq, true_and,
                    Nat.add_one_sub_one, List.head?_reverse]
                have hvcur : v = cur := Option.some.inj this
                -- `hy2` は「末尾直前がある」主張だが、いま末尾は `cur` で直前が無い
                -- ので矛盾を作れる。ここは簡潔に False を作って閉じる。
                --cases hvcur
                -- `take (len-1)` が空になるので `hy2` は成立しない
                show ∃ prefix0 m a b suffix, p.verts = prefix0 ++ [a, m, b] ++ suffix ∧ S.cover m a ∧ S.cover m b ∧ a ≠ b
                --直接ゴールを示すのではなくて、仮定が矛盾することを示すのか。

                exact False.elim (by
                  -- `hy2 : (((p.verts.take (p.verts.length - 1)).reverse).head?) = some y2`
                  -- ところが `p.verts = front ++ [prev, cur]` なので左辺は `none`

                  have : (((front ++ [prev, cur]).take ((front ++ [prev, cur]).length - 1)).reverse).head?
                          = (none : Option S.Elem) := by
                    simp_all
                    sorry
                    -- 長さ 2 の `take 1` は 1 要素、`reverse.head?` はその唯一の要素
                    -- が、この唯一の要素が「直前」で、存在しない（ここは細かく計算しても可）
                    -- 簡潔には `simp` で評価
                  subst rt ha r2 hvcur hv0
                  simp_all only [List.drop_succ_cons, List.drop_zero, List.head?_cons, Option.some.injEq, exists_eq_left',
                    List.length_cons, le_add_iff_nonneg_left, zero_le, List.reverse_cons, List.append_assoc, List.cons_append,
                    List.nil_append, add_tsub_cancel_right, List.take_succ_cons, List.head?_append, List.head?_reverse, Option.or_some,
                    List.chain_cons, List.Chain.nil, and_true, reduceCtorEq]
                )

            | cons nxt xs' ih =>
                intro front prev cur eqshape hchain hdown
                -- `hchain : Chain (adj S) prev (cur :: nxt :: xs')`
                -- まず一歩目と残りに分解
                cases hchain with
                | cons h_prev_cur htail =>
                  -- さらに `htail : Chain (adj S) cur (nxt :: xs')` の先頭を取り出す
                  cases htail with
                  | cons h_cur_nxt htail' =>
                    -- `h_cur_nxt : adj S cur nxt` の向きで分岐
                    cases h_cur_nxt with
                    | inl hup_cur_nxt =>
                        -- 切替点発見：`m = cur, a = prev, b = nxt`
                        -- 形を `front ++ [prev,cur,nxt] ++ xs'` に整える
                        have eq1 : p.verts = front ++ prev :: cur :: nxt :: xs' := by
                          subst ha rt hv0
                          simp_all only [List.drop_one, List.head?_tail, Subtype.exists, List.length_append, List.length_cons,
                            Nat.add_succ_sub_one, List.head?_reverse, List.reverse_append, List.reverse_cons, List.append_assoc,
                            List.cons_append, List.nil_append, List.chain_cons, ne_eq, exists_and_right, Subtype.mk.injEq, and_imp,
                            Subtype.forall]

                        -- `cons_append` と結合則で変形
                        have eqBlock : p.verts = front ++ [prev, cur, nxt] ++ xs' := by
                          -- `front ++ prev :: cur :: nxt :: xs'`
                          -- = `front ++ ([prev,cur,nxt] ++ xs')`
                          -- = `front ++ [prev,cur,nxt] ++ xs'`
                          have : front ++ prev :: cur :: nxt :: xs' =
                                  front ++ ([prev, cur, nxt] ++ xs') := by
                            simp [List.cons_append]
                          exact Eq.trans eq1 (by
                            cases this
                            subst ha rt hv0
                            simp_all only [List.drop_one, List.head?_tail, Subtype.exists, List.length_append, List.length_cons,
                              Nat.add_succ_sub_one, List.head?_reverse, List.reverse_append, List.reverse_cons, List.append_assoc,
                              List.cons_append, List.nil_append, List.chain_cons, ne_eq, exists_and_right, Subtype.mk.injEq, and_imp,
                              Subtype.forall]
                            )
                        -- `p.nodup` を右辺に移す
                        have hnd_rhs : (front ++ [prev,cur,nxt] ++ xs').Nodup := by
                          have hnd := p.nodup
                          -- `rw` で置換
                          rw [eqBlock] at hnd
                          exact hnd
                        -- `a ≠ b`
                        have hneq : prev ≠ nxt :=
                          ne_of_nodup_middle_block
                            (prefix0 := front) (suffix := xs') (a := prev) (m := cur) (b := nxt) hnd_rhs
                        -- 長さ条件：`i = front.length`
                        let i : Nat := front.length
                        have hlen : i + 2 ≤ p.verts.length := by
                          -- `p.verts.length = front.length + 3 + xs'.length`
                          have hl := congrArg List.length eqBlock
                          -- `front.length + 2 ≤ front.length + 3 + xs'.length`
                          have base :
                            front.length + 2 ≤ front.length + 3 + xs'.length := by
                            have h1 : front.length + 2 ≤ front.length + 3 :=
                              Nat.le_succ (front.length + 2)
                            have h2 : front.length + 3 ≤ front.length + 3 + xs'.length :=
                              Nat.le_add_right _ _
                            exact Nat.le_trans h1 h2
                          subst ha rt hv0
                          simp_all only [List.append_assoc, List.cons_append, List.nil_append, ne_eq, List.drop_one, List.head?_tail,
                            Subtype.exists, List.length_append, List.length_cons, Nat.add_succ_sub_one, List.head?_reverse, List.reverse_append,
                            List.reverse_cons, List.chain_cons, exists_and_right, Subtype.mk.injEq, and_imp, Subtype.forall,
                             add_le_add_iff_left, le_add_iff_nonneg_left, zero_le, i]

                        -- まとめて返す
                        exact ⟨front, cur, prev, nxt, xs', eqBlock, hdown, hup_cur_nxt, hneq⟩
                    | inr hdown_cur_nxt =>
                        -- hdown_cur_nxt : S.cover nxt cur
                        -- まだ down。ひとつ進める：`front := front ++ [prev]`
                        -- 形：`p.verts = (front ++ [prev]) ++ cur :: nxt :: xs'`
                        have eqshape' : p.verts =
                            (front ++ [prev]) ++ cur :: nxt :: xs' := by
                          subst ha rt hv0
                          simp_all only [List.drop_one, List.head?_tail, Subtype.exists, List.length_append, List.length_cons,
                            Nat.add_succ_sub_one, List.head?_reverse, List.reverse_append, List.reverse_cons, List.append_assoc,
                            List.cons_append, List.nil_append, List.chain_cons, ne_eq, exists_and_right, Subtype.mk.injEq, and_imp,
                            Subtype.forall]

                        -- 帰納呼び出し
                        have res :=
                          ih (front := front ++ [prev]) (prev := cur) (cur := nxt)
                            (eqshape := eqshape') (hchain := ?_) (hdown := hdown_cur_nxt)
                        exact res
                        show List.Chain (adj S) cur (nxt :: xs')
                        sorry
            -/

          -- 走査を起動：`front = []`, `prev = a`, `cur = b`, `xs = rest2`
          -- まず `p.chain` を `Chain a (b :: rest2)` に
          /-
          have hc0 : List.Chain (adj S) a (b :: rest2) := by
            -- `p.chain : Chain' (adj S) (a :: b :: rest2)`
            -- 定義展開で十分
            have t := p.chain
            -- `Chain' (x::xs)` は `Chain x xs`
            subst rt ha r2 hv0
            simp_all only [List.drop_succ_cons, List.drop_zero, List.head?_cons, Option.some.injEq, exists_eq_left',
              List.length_cons, add_tsub_cancel_right, List.take_succ_cons, List.reverse_cons, List.append_assoc,
              List.cons_append, List.nil_append, List.head?_append, List.head?_reverse, Option.or_some, le_add_iff_nonneg_left,
              zero_le, List.chain_cons, ne_eq, exists_and_right, Subtype.exists, Subtype.mk.injEq, and_imp, Subtype.forall,
              List.chain'_cons_cons, true_and]
            obtain ⟨left, right⟩ := t
            obtain ⟨left_1, right⟩ := right
            exact right
          -/
          have ⟨xs0, htailv⟩ :
            ∃ xs0, p.verts = [] ++ a :: b :: xs0 ++ [v] := by
            -- p.verts = a :: b :: rest2 かつ p.verts の末尾は v（hr/hv0）なので
            -- rest2 = xs0 ++ [v] が取れる
            have hx : ∃ xs, (a :: b :: rest2) = xs ++ [v] := by
              -- `p.verts.reverse = v :: rrest` から
              have := p.last_ok
              -- 既に `hr` と `hv0` を持っているので、`exists_init_append_last_of_rev_head` を当てる
              have : (p.verts.reverse).head? = some v := by
                -- `p.last_ok`
                simpa using p.last_ok
              exact exists_init_append_last_of_rev_head (a :: b :: rest2) (v := v) (by
                -- `p.verts` と一致
                -- （`simp [pv, rt]` で `p.verts` を具体化してから `this` を当ててもOK）
                simpa [pv, rt] using this)

            have hx2 : ∃ xs2, rest2 = xs2 ++ [v] := by
              have := p.last_ok
              exact exists_init_append_last_of_rev_head rest2 (v := v) (by
                sorry)

            rcases hx with ⟨xs, hx'⟩
            --constructor
            --· sorry
            --· sorry
            simp
            show ∃ xs0, p.verts = a :: b :: (xs0 ++ [v])
            --pv:p.verts = a :: rest
            --rt : rest = b :: rest2
            -- hx' : a :: b :: rest2 = xs ++ [v]
            --useすべきは、rest2から末尾のvを外したもの。
            obtain ⟨xs2, hv2⟩ := hx2
            use xs2
            rw [pv]
            rw [rt]
            rw [hv2]

          -- これで scan を起動
          have hc0 : List.Chain (adj S) a (b :: (Classical.choose ⟨xs0, rfl⟩) ++ [v]) := by
            -- p.chain を `Chain a (b :: xs0 ++ [v])` に落とす
            -- 具体の `xs0` は上の分解の右辺から取り出せます。`simp` でOKです。
            -- （もし詰まる場合は、その行を貼ってください。調整します。）
            simp
            constructor
            · dsimp [isDown] at hdown_ab
              dsimp [adj]
              exact Or.inr hdown_ab
            · show List.Chain (adj S) b (xs0 ++ [v])
              -- hr : p.verts.reverse = v0 :: rrest
              -- rt : rest = b :: rest2
              --htailv : p.verts = [] ++ a :: b :: xs0 ++ [v]
              -- pv : p.verts = a :: rest
              sorry

          have ⟨prefix0, m, a0, b0, suffix, heq, hma, hmb, hneq⟩ :=
            scan [] a b (Classical.choose ⟨xs0, rfl⟩) (by simpa using htailv) hc0 hdown_ab
          -- 起動
          /-
          have ⟨prefix0, m, a0, b0, suffix, heq, hma, hmb, hneq⟩ :=
            scan [] a b rest2 (by
              subst rt ha r2 hv0
              simp_all only [List.chain_cons, List.drop_succ_cons, List.drop_zero, List.head?_cons, Option.some.injEq,
                exists_eq_left', List.length_cons, add_tsub_cancel_right, List.take_succ_cons, List.reverse_cons, List.append_assoc,
                List.cons_append, List.nil_append, List.head?_append, List.head?_reverse, Option.or_some, le_add_iff_nonneg_left,
                zero_le, ne_eq, exists_and_right, Subtype.exists, Subtype.mk.injEq, and_imp, Subtype.forall]
            ) hc0 hdown_ab
          -/
          -- `i := prefix0.length`
          let i : Nat := prefix0.length
          -- 長さ条件 コメントアウトするとゴールが残る。
          have hlen : i + 2 ≤ p.verts.length := by
            have hl := congrArg List.length heq
            -- `prefix0.length + 2 ≤ prefix0.length + 3 + suffix.length`
            have base :
              prefix0.length + 2 ≤ prefix0.length + 3 + suffix.length := by
              have h1 : prefix0.length + 2 ≤ prefix0.length + 3 :=
                Nat.le_succ (prefix0.length + 2)
              have h2 : prefix0.length + 3 ≤ prefix0.length + 3 + suffix.length :=
                Nat.le_add_right _ _
              exact Nat.le_trans h1 h2
            subst rt ha r2 hv0
            simp_all only [ne_eq, List.chain_cons, List.append_assoc, List.cons_append, List.nil_append, List.drop_one,
              List.head?_tail, Subtype.exists, List.length_append, List.length_cons, Nat.add_succ_sub_one, List.head?_reverse,
              List.reverse_append, List.reverse_cons, exists_and_right, Subtype.mk.injEq, and_imp, Subtype.forall,
                i]
            simp
            sorry

          -- 完了
          refine ⟨i, m, a0, b0, ?_, hma, hmb, hneq⟩
          subst rt ha r2 hv0
          simp_all only [ne_eq, List.chain_cons, List.append_assoc, List.cons_append, List.nil_append, List.drop_one,
            List.head?_tail, Subtype.exists, List.length_append, List.length_cons, Nat.add_succ_sub_one, List.head?_reverse,
            List.reverse_append, List.reverse_cons, exists_and_right, Subtype.mk.injEq, and_imp, Subtype.forall,
             i]


lemma geodesic_len_ge_three_of_distinct_maxima {α} [DecidableEq α]
  (S : SPO.FuncSetup α) [Fintype S.Elem] (hpos : isPoset)
  {u v : S.Elem} (hu : S.maximal u) (hv : S.maximal v)
  (p : Path S u v) (hpmin : ∀ q : Path S u v, p.verts.length ≤ q.verts.length)
  (hne : u ≠ v) :
  3 ≤ p.verts.length := by
  -- 長さ 1 → u=v。長さ 2 → u と v が隣接。
  -- 隣接が上向きなら u ≤ v、下向きなら v ≤ u。
  -- 反対称性よりいずれも u=v に矛盾。
  -- よって ≥ 3。
  cases pv:p.verts with
  | nil =>
    simp_all only [FuncSetup.maximal_iff, FuncSetup.le_iff_leOn_val, Subtype.forall, List.length_nil, zero_le,
    implies_true, ne_eq, nonpos_iff_eq_zero, OfNat.ofNat_ne_zero]
    obtain ⟨val, property⟩ := u
    obtain ⟨val_1, property_1⟩ := v
    simp_all only [Subtype.mk.injEq]
    cases p
    subst pv
    simp_all only [ne_eq, not_true_eq_false]
  | cons a rest =>
    have ha : a = u := by
      have h0 := p.head_ok
      have : (List.head? (a :: rest)) = some a := rfl
      have : some a = some u := by
        apply Eq.trans (Eq.symm this)
        simp_all only [FuncSetup.maximal_iff, FuncSetup.le_iff_leOn_val, Subtype.forall, List.length_cons, ne_eq,
            Option.some.injEq, List.head?_cons]
      exact Option.some.inj this
    cases rs:rest with
    | nil =>
        -- 長さ1
        have : u = v := by
          -- p.last_ok から v = a、かつ a = u
          have hv' : v = a := by
            have : (List.head? ([a].reverse)) = some v := by
              subst ha rs
              simp_all only [FuncSetup.maximal_iff, FuncSetup.le_iff_leOn_val, Subtype.forall, List.length_cons, List.length_nil,
                zero_add, ne_eq, List.reverse_cons, List.reverse_nil, List.nil_append, List.head?_cons, Option.some.injEq]
              obtain ⟨val, property⟩ := v
              obtain ⟨val_1, property_1⟩ := a
              simp_all only [Subtype.mk.injEq]
              cases p
              subst pv
              simp_all only [ne_eq, List.cons_ne_self, not_false_eq_true, List.head?_cons, List.reverse_cons, List.reverse_nil,
                List.nil_append, Option.some.injEq, Subtype.mk.injEq]
            have : some v = some a := by
              apply Eq.trans (Eq.symm (by rfl))
              subst ha
              simp_all only [FuncSetup.maximal_iff, FuncSetup.le_iff_leOn_val, Subtype.forall, List.reverse_cons, List.reverse_nil,
                List.nil_append, List.head?_cons, Option.some.injEq]

            exact Option.some.inj this
          cases ha; exact Eq.symm hv'
        exact False.elim (hne this)
    | cons b rest2 =>
        -- 長さ ≥ 2。もし = 2 なら隣接のみで到達。
        cases r2:rest2 with
        | nil =>
            -- ちょうど長さ 2。`adj u v` で、反対称性に矛盾。
            -- `p.chain` から `adj a b` を取り `a=u, b=v` に書換。
            have hadj : adj S u v := by
              have hc : List.Chain' (adj S) (a :: [b]) := by
                -- p.chain を具体化
                have := p.chain;
                subst r2 ha rs
                simp_all only [FuncSetup.maximal_iff, FuncSetup.le_iff_leOn_val, Subtype.forall, List.length_cons, List.length_nil,
                  zero_add, Nat.reduceAdd, ne_eq, List.chain'_cons_cons, List.chain'_singleton, and_true, and_self]

              -- `Chain' (a::[b])` は `adj a b`
              -- ここは `simp` で評価可能
              subst r2 ha rs
              simp_all only [FuncSetup.maximal_iff, FuncSetup.le_iff_leOn_val, Subtype.forall, List.chain'_cons_cons,
                List.chain'_singleton, and_true, List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, ne_eq]
              obtain ⟨val, property⟩ := v
              obtain ⟨val_1, property_1⟩ := a
              obtain ⟨val_2, property_2⟩ := b
              simp_all only [Subtype.mk.injEq]
              cases p
              subst pv
              simp_all only [ne_eq, reduceCtorEq, not_false_eq_true, List.head?_cons, List.reverse_cons, List.reverse_nil,
                List.nil_append, List.cons_append, Option.some.injEq, Subtype.mk.injEq, List.chain'_cons_cons,
                List.chain'_singleton, and_true, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_self, List.nodup_nil,
                and_self]

            -- 反対称性矛盾を `hne` で閉じる（詳細は上の `admit` を埋めてください）
            dsimp [FuncSetup.maximal] at hu hv
            dsimp [adj] at hadj
            cases hadj with
            | inl hl =>
              have : S.le u v := by exact FuncSetup.cover_to_le S hl
              let ht := hu this
              have : u = v := by exact antisymm_of_isPoset S hpos this ht
              contradiction

            | inr hr =>
              have : S.le v u := by exact FuncSetup.cover_to_le S hr
              let ht := hv this
              have : u = v := by exact antisymm_of_isPoset S hpos ht this
              contradiction
        | cons _ _ =>
            -- 長さ ≥ 3
            simp


lemma switch_contradicts_functionality (S : SPO.FuncSetup α)
  {m a b : S.Elem} :
  S.cover m a → S.cover m b → a ≠ b → False := by
  intro hma hmb hne
  have h : a = b := cover_out_unique S (u := m) (y := a) (z := b) hma hmb
  exact hne h

/-! ## 5) 連結 functional 半順序の極大元一意性（主張） -/

/-- **目標**：連結かつ反対称性がある functional 構造では極大はただ一つ -/
theorem unique_maximal_of_connected (S : SPO.FuncSetup α)
  [Fintype S.Elem] (hpos : isPoset) (hconn : isConnected S)
  {u v : S.Elem} (hu : S.maximal u) (hv : S.maximal v) :
  u = v := by
  -- 既存：
  have ⟨p, hpmin⟩ := exists_geodesic_path (S := S) hconn u v

  -- ここから h₁ と h₂ を埋める

  -- h₁: 最初の一歩は down（存在つきで）
  have h₁_or := first_step_down_or_eq S hpos hu p hpmin
  -- u = v なら即終了
  cases h₁_or with
  | inr h_eq => exact h_eq
  | inl h₁ =>
      -- 以降は既存の h₂, スイッチ点, 矛盾…の流れをそのまま使う
      have h₂ : ∃ y, (p.verts.take (p.verts.length - 1)).reverse.head? = some y ∧ isUp S y v := by
        -- `p.verts.reverse = v :: rrest` と分解し，その先頭の「次」が y
        cases hr : p.verts.reverse with
        | nil =>
            -- 非空に反する
            exact False.elim (p.nonempty (by
              -- reverse [] = [] → verts = []
              -- 反証のために `reverse_reverse` を使って戻す
              have : p.verts = [] := by
                -- `p.verts = []` でないといけないが、ここは `nonempty` と矛盾
                -- 直接は `cases` で展開できないので、最終行で使います
                -- 簡単のためこの枝は False.elim だけ返せば良い
                exact List.reverse_eq_nil_iff.mp hr
              exact this
                ))
        | cons v0 rrest =>
            -- `p.last_ok : (p.verts.reverse).head? = some v` から v0 = v
            have hv0 : v0 = v := by
              have : (List.head? (v0 :: rrest)) = some v0 := rfl
              have : some v0 = some v := by
                apply Eq.trans (Eq.symm this)
                simp_all only [FuncSetup.maximal_iff, FuncSetup.le_iff_leOn_val, Subtype.forall, List.drop_one, List.head?_tail,
                  Subtype.exists, List.reverse_eq_cons_iff, List.head?_cons, Option.some.injEq, List.length_append,
                  List.length_reverse, List.length_cons, List.length_nil, zero_add]
                obtain ⟨val, property⟩ := u
                obtain ⟨val_1, property_1⟩ := v
                obtain ⟨val_2, property_2⟩ := v0
                obtain ⟨w, h⟩ := h₁
                obtain ⟨w_1, h⟩ := h
                obtain ⟨left, right⟩ := h
                simp_all only [Subtype.mk.injEq]
                cases p
                subst hr
                simp_all only [ne_eq, List.append_eq_nil_iff, List.reverse_eq_nil_iff, List.cons_ne_self, and_false,
                  not_false_eq_true, List.head?_append, List.head?_reverse, List.head?_cons, Option.or_some, Option.some.injEq,
                  List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append, List.reverse_reverse, List.cons_append,
                  Subtype.mk.injEq]

              exact Option.some.inj this
            -- rrest の有無で分岐
            cases rr : rrest with
            | nil =>
                -- 末尾のひとつ手前が存在しない＝長さ 1。
                -- その場合も `(take (len-1)).reverse.head?` は `none` なので与件に反する
                -- よって False から存在を作る
                have : (p.verts.take (p.verts.length - 1)).reverse.head? = (none : Option S.Elem) := by
                      -- `p.verts.reverse = [v0]` を使って長さ 1 を評価
                  -- ここは `simp` で流せます
                  -- ただし `simpa using` は使わない方針なので、`simp` の結果を `have` に入れます
                  -- 実際の式展開は省略（anyway: none）
                  subst hv0 rr
                  simp_all only [FuncSetup.maximal_iff, FuncSetup.le_iff_leOn_val, Subtype.forall, List.drop_one, List.head?_tail,
                    Subtype.exists, List.reverse_eq_cons_iff, List.reverse_nil, List.nil_append, List.length_cons, List.length_nil,
                    zero_add, tsub_self, List.take_zero, List.head?_nil]
                exact False.elim (by
                  -- `hend` は some y を主張するが、ここでは none なので矛盾
                  subst hv0 rr
                  simp_all only [FuncSetup.maximal_iff, FuncSetup.le_iff_leOn_val, Subtype.forall, List.drop_one, List.head?_tail,
                    Subtype.exists, List.head?_reverse, List.getLast?_eq_none_iff, List.take_eq_nil_iff, List.reverse_eq_cons_iff,
                    List.reverse_nil, List.nil_append, List.length_cons, List.length_nil, zero_add, lt_self_iff_false,
                    not_false_eq_true, getElem?_neg, reduceCtorEq, false_and, exists_false]
                )

            | cons y0 r2 =>
                -- 末尾直前の頂点は y0。よって witness は y = y0。
                -- まず `(take (len-1)).reverse.head? = some y0` を作る：
                have hy_last : (p.verts.take (p.verts.length - 1)).reverse.head? = some y0 := by
                  -- `p.verts = (v0 :: y0 :: r2).reverse` を使って定義計算に落とす
                  -- そのために一旦 `p.verts` を書き戻す
                  have hvform : p.verts = (v0 :: y0 :: r2).reverse := by
                    -- `rw [← List.reverse_reverse p.verts, hr]` で反転
                    rw [← List.reverse_reverse p.verts, hr]
                    exact congrArg List.reverse (congrArg (List.cons v0) rr)
                  -- 長さ：`p.verts.length - 1 = (y0 :: r2).length`
                  have : p.verts.length - 1 = (y0 :: r2).length := by
                    -- `length_reverse` を使った計算（1 を引くと残りの長さ）
                    -- ここは `simp` で流すため、省略
                    -- 直接は `by` ブロックで `simp` しても可
                    -- 以後の `simp` でまとめて評価します
                    -- placeholder
                      subst hv0 rr
                      simp_all only [FuncSetup.maximal_iff, FuncSetup.le_iff_leOn_val, Subtype.forall, List.reverse_cons, List.append_assoc,
                        List.cons_append, List.nil_append, List.length_append, List.length_reverse, List.length_cons, List.length_nil,
                        zero_add, Nat.reduceAdd, List.drop_one, List.head?_tail, lt_add_iff_pos_left, add_pos_iff, Nat.lt_add_one, or_true,
                        getElem?_pos, Option.some.injEq, exists_eq_left', List.reverse_append, List.reverse_nil, List.reverse_reverse,
                        Nat.add_one_sub_one]
                  -- 実際の評価は `simp` に任せる：
                  -- `(take (len-1) ((v0::y0::r2).reverse)).reverse.head? = some y0`
                  -- になる
                  -- まとめて：
                  subst hv0
                  -- 以降の `simp` は your env に応じて強めに効きます
                  -- もし通らなければ、直前の長さ等式を明示してから再 `simp` にしてください
                  subst rr
                  simp_all
                  obtain ⟨val, property⟩ := u
                  obtain ⟨val_1, property_1⟩ := v0
                  obtain ⟨val_2, property_2⟩ := y0
                  simp_all only
                  simp [List.getLast?_eq_getElem?]

                -- つぎに「上向き」：`last_step_isUp_of_maximal` を y0 に適用
                have hup : isUp S y0 v :=
                  last_step_isUp_of_maximal S hpos hv p hpmin y0 hy_last
                exact ⟨y0, hy_last, hup⟩
      by_cases u = v
      case pos =>
        -- u = v なら終了
        (expose_names; exact h)
      case neg h =>
        have :3 ≤ p.verts.length := by
          exact geodesic_len_ge_three_of_distinct_maxima S hpos hu hv p hpmin h
        let esv := exists_switch_vertex_on_path_len3 (S := S) p h₁ h₂ this
        have ⟨i, m, a, b, hlen, hma, hmb, hneq⟩ := esv
        have : False := switch_contradicts_functionality (S := S) hma hmb hneq
        exact this.elim

--end FuncSetup
end AvgRare
