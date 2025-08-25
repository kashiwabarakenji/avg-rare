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

/-- 連結なら最短の簡単路が取れる（存在のみ主張） -/
lemma exists_geodesic_path (S : SPO.FuncSetup α)
  [Fintype S.Elem] (hconn : isConnected S) (u v : S.Elem) :
  ∃ p : Path S u v, ∀ q : Path S u v, p.verts.length ≤ q.verts.length := by
  sorry


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


/-- パス上で「下→上」への切替点があれば、ある頂点 m から
    2 本の異なる上向きが出る（スイッチ頂点） -/
lemma exists_switch_vertex_on_path (S : SPO.FuncSetup α)
  {u v : S.Elem} (p : Path S u v)
  (hstart : ∃ y, (p.verts.drop 1).head? = some y ∧ isDown S u y)
  (hend   : ∃ y, (p.verts.take (p.verts.length - 1)).reverse.head? = some y ∧ isUp S y v) :
  ∃ (i : Nat) (m a b : S.Elem),
    i + 2 ≤ p.verts.length ∧
    S.cover m a ∧ S.cover m b ∧ a ≠ b := by
  -- 方向列の符号変化点（down→up）をとる組合せ論
  sorry

/-- スイッチ頂点は機能性（出次数 ≤ 1）に反する -/
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

      have ⟨i, m, a, b, hlen, hma, hmb, hneq⟩ :=
        exists_switch_vertex_on_path (S := S) p h₁ h₂
      have : False := switch_contradicts_functionality (S := S) hma hmb hneq
      exact this.elim

--end FuncSetup
end AvgRare


/-
-- SCC凝縮グラフがDAG（= 反対称）で outdegree ≤ 1 であること
def IsRootedForest : Prop :=
  (∀ a b, S.preQuot.le a b → S.preQuot.le b a → a = b) ∧
  (∀ a, ¬ ∃ b c, b ≠ c ∧ FuncSetup.stepQuot S a b ∧ FuncSetup.stepQuot S a c)

/-- 森に対する二次主定理（非正性、言明）。 -/
lemma nds_rooted_forest_nonpos (S : FuncSetup α)
    (hforest : IsRootedForest S) :
  SetFamily.normalized_degree_sum (idealsQuot S) ≤ 0 := by
  -- `nds_leaf_step` による帰納法で証明
  sorry
-/
