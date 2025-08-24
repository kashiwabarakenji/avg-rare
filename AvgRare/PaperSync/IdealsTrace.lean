import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.Order.GroupWithZero.Unbundled.Defs
import AvgRare.Basics.SetFamily
import AvgRare.Basics.Ideals
import AvgRare.SPO.FuncSetup
import AvgRare.SPO.TraceFunctional
import AvgRare.Basics.Trace.Common   -- Trace.traceAt / Trace.Parallel / Trace.eraseMap
import AvgRare.Basics.Trace.Monotonicity
import LeanCopilot

/-
IdealsTrace.lean — 「functional preorder × ideals × trace」の結合層（論文 §3）

論文で出てくるような高レベル補題の言明と、主定理から準主定理への帰着まで
-/

universe u
open Classical

open scoped BigOperators

namespace AvgRare
namespace PaperSync
open Trace
open SPO

variable {α : Type u} [DecidableEq α]

--idealFamilyの定義は、FuncSetupで与える。

--Lemma 2.4（カードを使わない形）：
-- 目標：非自明同値類 ⇒ 極大
--ここも{α}が必要。下の定理で使っている。
theorem maximal_of_nontrivialClass
    (S : SPO.FuncSetup α) {x : S.Elem}
    (hx : S.nontrivialClass x) : S.maximal x := by
  -- 非自明同値類 ⇒ パラレル相手 y と x≠y を取る
  rcases hx with ⟨y, hneq, hsim⟩
  -- parallel on α が欲しいので、型合わせ補題で作る
  have hpar : (S.idealFamily).Parallel (x : α) (y : α) :=
    S.parallel_of_sim_coe hsim
  -- α レベルの `maximal_of_parallel_nontrivial` を適用
  -- 引数として ground 含意が要るので property で供給
  have H :=
    maximal_of_parallel_nontrivial S
      (u := (x : α)) (v := (y : α))
      (hu := x.property) (hv := y.property)
      (hpar := hpar)
      (hneq := Subtype.coe_ne_coe.mpr (id (Ne.symm hneq)))
  -- H :
  --   ∀ z : S.Elem,
  --     RTG (stepRel S.f) (S.toElem! x.property) z →
  --     RTG (stepRel S.f) z (S.toElem! x.property)
  -- `toElem!` を潰して、以降 x と同一視
  have Hx :
      ∀ z : S.Elem,
        Relation.ReflTransGen (stepRel S.f) x z →
        Relation.ReflTransGen (stepRel S.f) z x := by
    intro z hz
    -- `@[simp] toElem!_coe` で両端を x に書き換える
    have hz' :
        Relation.ReflTransGen (stepRel S.f) (S.toElem! x.property) z := by
      -- 左辺のみ書換え
      -- `simp` を使わず、明示的に書き換えたい場合は `rw` を使います。
      -- （ユーザ方針に合わせて `simpa using` は使いません）
      -- ただし `Relation.ReflTransGen` の左引数を書き換えるには
      -- `rw [toElem!_coe]` が効きます。
      -- ここでは簡潔に：
      --   from hz  （`toElem!_coe` により左が一致）
      exact hz
    -- 右辺の書換えは結論側で
    have hxback :=
      H z hz'
    -- 右辺も書換え
    -- `toElem!_coe` により `... z (S.toElem! x.property)` を `... z x` に
    -- 置換できる（`@[simp]` を付けてあれば自動で潰れます）
    exact hxback
  -- ここから「maximal の定義」を満たすことを示す
  -- maximal x : ∀ {z}, x ≤ z → z ≤ x
  intro z hxz
  -- x ≤ z から RTG x z を得る
  have hxz_rtg : Relation.ReflTransGen (stepRel S.f) x z := by exact hxz --rtg_of_le S hxz
  -- Hx で逆向きを入手
  have hzx_rtg : Relation.ReflTransGen (stepRel S.f) z x :=
    Hx z hxz_rtg
  -- RTG z x から z ≤ x を回収（`le_iff_exists_iter` の ← 向き）
  -- 具体的には、`reflTransGen_iff_exists_iterate`（S.Elem 版）と
  -- `le_iff_exists_iter` を合成します。
  -- ここでは最小限のため、`le_iff_exists_iter` を直接使います：
  --   RTG z x ⇒ ∃k, iter k z = x ⇒ z ≤ x
  -- まず ∃k を取り出す（既存の IterateRTG の補題名に合わせて置換）
  rcases (reflTransGen_iff_exists_iterate (S.f)).1 hzx_rtg with ⟨k, hk⟩
  -- `le_iff_exists_iter` の → 向きを使って z ≤ x を得る
  --   （等式の向きに注意）
  -- `le_iff_exists_iter S z x` : S.le z x ↔ ∃ k, S.iter k z = x
  have : S.le z x := by
    -- 右向き（→）を使うので `apply (S.le_iff_exists_iter z x).2`
    --let lie := (@le_iff_exists_iter _ S z x).2
    exact H z hxz

  exact this

/-- 論文 Lemma 3.1（言明）：
S の極大元 `u` は，`idealFamily S` において rare。 -/

lemma rare_of_maximal
  (S : SPO.FuncSetup α) {u : S.Elem} (hmax : S.maximal u) :
  (S.idealFamily).Rare u.1 := by
  classical
  -- Φ（単射）を用意
  let Φ :=
    Phi (u := u) (hmax := hmax)
  have hΦ : Function.Injective Φ :=
    Phi_injective (u := u) S hmax
  -- 一般補題に適用
  exact rare_of_injection_between_filters
          (F := S.idealFamily) (x := u.1) Φ hΦ

/- 論文 Lemma 3.6(1) の言明：-/
lemma NDS_le_trace_of_nontrivialClass
  (S : SPO.FuncSetup α) {u : S.Elem}
  (hx : S.nontrivialClass u) :
  (S.idealFamily).NDS ≤ (traceAt u.1 (S.idealFamily)).NDS := by
  classical
  -- 1) パラレルパートナーを α レベルで取得
  rcases exists_parallel_partner_from_nontrivial (S := S) (u := u) hx with
    ⟨v, hne, hv, hpar⟩
  -- 2) NDS の差分等式
  have hEq :
    (S.idealFamily).NDS
      = (traceAt u.1 (S.idealFamily)).NDS
        + 2 * ((S.idealFamily).degree u.1 : Int)
        - ((S.idealFamily).numHyperedges : Int) :=
    NDS_eq_of_parallel
      (F := S.idealFamily) (u := u.1) (v := v)
      (huv := hpar) (hne := hne.symm) (hu := u.property)

  -- 3) nontrivial ⇒ maximal ⇒ Rare
  have hmax : S.maximal u := maximal_of_nontrivialClass S (x := u) hx
  have hRare : (S.idealFamily).Rare u.1 := rare_of_maximal (S := S) (u := u) hmax
  -- 4) 差分項が非正
  have hnonpos :
      2 * ((S.idealFamily).degree u.1 : Int)
        - ((S.idealFamily).numHyperedges : Int) ≤ 0 :=
    diff_term_nonpos_of_Rare (F := S.idealFamily) (x := u.1) hRare
  -- 5) 等式＋非正 ⇒ ≤
  have :(traceAt (↑u) S.idealFamily).NDS + 2 * ↑(S.idealFamily.degree ↑u) - ↑S.idealFamily.numHyperedges = (traceAt (↑u) S.idealFamily).NDS + (2 * ↑(S.idealFamily.degree ↑u) - ↑S.idealFamily.numHyperedges):= by
    exact
      Int.add_sub_assoc (traceAt (↑u) S.idealFamily).NDS (2 * ↑(S.idealFamily.degree ↑u))
        ↑S.idealFamily.numHyperedges
  rw [this] at hEq
  --rw [←add_assoc (traceAt (↑u) S.idealFamily).NDS 2 * ↑(S.idealFamily.degree ↑u) S.idealFamily.NDS] at hEq
  exact le_of_eq_add_of_nonpos hEq hnonpos


------------------------

/- principal idealがIdealであること？ -/
--現状ではどこからも使ってないが、後半使うかも。そのときは、半順序かも。
--FuncSetupに移動するのも、ideal関係だしへん。principal Idealの話は、IdealsかForestに移動かも？
lemma idealFamily_mem_principal
  (S : FuncSetup α) (x : S.Elem) :
  isOrderIdealOn (le := S.leOn) (V := S.ground) (S.principalIdeal x.1 x.2)  := by
  dsimp [FuncSetup.principalIdeal]
  simp
  dsimp [isOrderIdealOn]
  simp
  constructor
  · obtain ⟨val, property⟩ := x
    intro x hx
    simp_all only [Finset.mem_map, Finset.mem_filter, Finset.mem_attach, true_and, Function.Embedding.coeFn_mk,
      Subtype.exists, exists_and_right, exists_eq_right]
    obtain ⟨w, h⟩ := hx
    simp_all only

  · intro xx hx lexy y hy leyx
    constructor
    · exact FuncSetup.leOn_trans S leyx hx
    · exact hy



/-
--使っていたところをコメントアウトしたし同等な補題を別のことで示したのでけしていいかも。
@[simp] lemma ground_traceAt (F : SetFamily α) (u : α) :
    (Trace.traceAt u F).ground = F.ground.erase u := by
  -- `traceAt` の定義が `ground := F.ground.erase u` なら `rfl` で落ちます。
  -- そうでない場合も `ext x; simp` で示せます。
  ext x; simp [Trace.traceAt]
-/


end PaperSync
end AvgRare
