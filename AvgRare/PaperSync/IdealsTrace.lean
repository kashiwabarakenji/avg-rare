import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.Order.GroupWithZero.Unbundled.Defs
import Mathlib.Algebra.Order.Sub.Basic
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
open SetFamily

variable {α : Type u} [DecidableEq α]

--idealFamilyの定義は、FuncSetupで与える。

--Lemma 2.4（カードを使わない形）：
-- 目標：非自明同値類 ⇒ 極大
--ここも{α}が必要。下の定理で使っている。
theorem maximal_of_nontrivialClass {α : Type u} [DecidableEq α]
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
    FuncSetup.maximal_of_parallel_nontrivial S
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
        Relation.ReflTransGen (FuncSetup.stepRel S.f) x z →
        Relation.ReflTransGen (FuncSetup.stepRel S.f) z x := by
    intro z hz
    -- `@[simp] toElem!_coe` で両端を x に書き換える
    have hz' :
        Relation.ReflTransGen (FuncSetup.stepRel S.f) (S.toElem! x.property) z := by
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
  have hxz_rtg : Relation.ReflTransGen (FuncSetup.stepRel S.f) x z := by exact hxz --rtg_of_le S hxz
  -- Hx で逆向きを入手
  have hzx_rtg : Relation.ReflTransGen (FuncSetup.stepRel S.f) z x :=
    Hx z hxz_rtg
  -- RTG z x から z ≤ x を回収（`le_iff_exists_iter` の ← 向き）
  -- 具体的には、`reflTransGen_iff_exists_iterate`（S.Elem 版）と
  -- `le_iff_exists_iter` を合成します。
  -- ここでは最小限のため、`le_iff_exists_iter` を直接使います：
  --   RTG z x ⇒ ∃k, iter k z = x ⇒ z ≤ x
  -- まず ∃k を取り出す（既存の IterateRTG の補題名に合わせて置換）
  rcases (FuncSetup.reflTransGen_iff_exists_iterate (S.f)).1 hzx_rtg with ⟨k, hk⟩
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

lemma rare_of_maximal {α : Type u} [DecidableEq α]
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
lemma NDS_le_trace_of_nontrivialClass {α : Type u} [DecidableEq α]
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

def isPoset (S : FuncSetup α) : Prop :=
  excess (S.idealFamily) = 0

lemma exists_pair_with_same_image_of_card_image_lt
  {α β : Type u} [DecidableEq α] [DecidableEq β]
  (s : Finset α) (f : α → β)
  (h : (s.image f).card < s.card) :
  ∃ x ∈ s, ∃ y ∈ s, x ≠ y ∧ f x = f y := by

  classical
  by_contra hno
  -- hno : ¬ ∃ x ∈ s, ∃ y ∈ s, x ≠ y ∧ f x = f y
  have hinj : ∀ x ∈ s, ∀ y ∈ s, f x = f y → x = y := by
    intro x hx y hy hxy
    by_cases hxy' : x = y
    · exact hxy'
    · have : ∃ x ∈ s, ∃ y ∈ s, x ≠ y ∧ f x = f y :=
        ⟨x, hx, y, hy, hxy', hxy⟩
      exact False.elim (hno this)
  have hcard : (s.image f).card = s.card := by
    -- `card_image_iff` は「像の濃度＝元の濃度 ↔ injOn」。
    -- Finset 版はこの形で使えます。
    exact Finset.card_image_iff.mpr hinj
  -- これで `h : (s.image f).card < s.card` と矛盾
  have : s.card < s.card := by
    -- `rw` で書き換えて矛盾を顕在化
    -- （simpa using は使わない）
    have hh := h
    rw [hcard] at hh
    exact hh
  exact (lt_irrefl _ this).elim

  lemma exists_nontrivialClass_of_excess_pos {α : Type u} [DecidableEq α]
  (S : FuncSetup α)
  (hpos : 0 < excess (S.idealFamily)) :
  ∃ u : S.Elem, S.nontrivialClass u := by

  classical
  let F := (S.idealFamily)
  have hlt_classes :
      (F.numClasses) < F.ground.card := by
    -- `excess F = ground.card - numClasses F`
    -- なので `0 < ...` から `numClasses F < ground.card`
    -- `Nat.sub_pos.mp : 0 < a - b → b < a` を使う
    dsimp [excess] at hpos
    dsimp [F]
    exact Nat.lt_of_sub_pos hpos

  -- `classSet F = F.ground.image (λ a, ParallelClass F a)`
  -- なので `(F.ground.image cls).card < F.ground.card` が成立
  have himg :
      (F.ground.image (fun a : α => F.ParallelClass a)).card < F.ground.card := by
    -- `numClasses = (classSet).card = (ground.image ...).card`
    -- 定義を展開して同値変形
    change (F.classSet).card < F.ground.card at hlt_classes
    -- そのまま
    simpa [SetFamily.numClasses, SetFamily.classSet]
      using hlt_classes
  -- 鳩の巣原理（Finset 版）を適用
  obtain ⟨a, ha, b, hb, hneq, hcls⟩ :=
    exists_pair_with_same_image_of_card_image_lt
      (s := F.ground) (f := fun x : α => F.ParallelClass x) himg
  -- `ParallelClass F a = ParallelClass F b` から `Parallel F a b`
  have hpar_ab : F.Parallel a b := by
    -- `b ∈ ground` かつ `Parallel F b b`（自明）より
    -- `b ∈ ParallelClass F b`。クラス等号で `b ∈ ParallelClass F a`。
    -- よって `Parallel F a b`。
    have hb_in : b ∈ F.ParallelClass b := by
      -- `Parallel F b b` は反射律（定義から自明）
      have : F.Parallel b b := by
        -- `Parallel` は {A | sets A ∧ b ∈ A} = {A | sets A ∧ b ∈ A}
        -- という恒等式
        rfl
      -- `ParallelClass F b = ground.filter (λ x, Parallel F b x)`
      -- よって `hb : b ∈ ground` と上の事実から membership
      -- `Finset.mem_filter` を使う
      have : b ∈ F.ground ∧ F.Parallel b b := And.intro hb this
      -- 展開（`filter` のメンバー判定）
      -- `simp` は使用可（`simpa using` は使わないという縛りのみ）
      have : b ∈ F.ground.filter (fun x => F.Parallel b x) := by
        -- `by_cases` なくても `simp` で十分
        -- `simp [Finset.mem_filter, hb]` でも OK
        have : b ∈ F.ground := hb
        -- 仕上げ
        simp [this, Finset.mem_filter]

      -- 表記合わせ
      -- 上の `this` は `b ∈ ParallelClass F b`
      simpa [SetFamily.ParallelClass] using this
    -- クラス等号から membership を移送
    have : b ∈ F.ParallelClass a := by
      -- `hcls : ParallelClass F a = ParallelClass F b`
      -- なので書き換え
      -- avoid `simpa using`: 直接 `rw` で
      have hb' := hb_in
      -- `hb_in : b ∈ ParallelClass F b`
      -- rewrite
      rw [← hcls] at hb'
      exact hb'
    -- `b ∈ ground.filter (λ x, Parallel F a x)` なので predicate が成り立つ
    -- すなわち `Parallel F a b`
    -- `Finset.mem_filter` を展開
    have : b ∈ F.ground ∧ F.Parallel a b := by
      -- 同様に `simp` で開く
      -- `this : b ∈ ParallelClass F a`
      -- `ParallelClass F a = ground.filter ...`
      simpa [SetFamily.ParallelClass, Finset.mem_filter] using this
    exact this.right
  -- いま `a ≠ b` かつ `Parallel F a b`。subtype を立てて `nontrivialClass` を得る。
  let u : S.Elem := ⟨a, ha⟩
  let v : S.Elem := ⟨b, hb⟩
  have hneq_uv : u ≠ v := by
    intro h'
    -- 値成分に射影して矛盾
    have : a = b := congrArg (fun (z : S.Elem) => z.1) h'
    exact hneq this
  -- `parallel_iff_sim` で `sim u v` を入手
  have hsim : FuncSetup.sim S u v := by
    -- 等価を右向きに使う
    have : (F).Parallel u v := by
      -- `u v` は `a b` と同一視（coee）
      -- いま `hpar_ab : Parallel F a b` を流用
      -- そのまま使える（coeeにより型一致）
      exact hpar_ab
    exact (FuncSetup.parallel_iff_sim S u v).mp hpar_ab
    -- ↑ `mp`/`mpr` の向きに注意：上では "Parallel → sim" を使いたいので
    --   `.mp` ではなく `.mpr` or `.1` ？ ここは書き換えます：
  -- （修正）：
  have hsim' : FuncSetup.sim S u v :=
    (S.parallel_iff_sim u v).1 hpar_ab
  -- 仕上げ
  use u
  dsimp [FuncSetup.nontrivialClass]
  use v
  simp_all [F, u, v]
  intro a_1
  simp_all only [not_true_eq_false]

/-- （前半の結論）準主定理を仮定して主定理を導く：強い帰納法版。 -/
theorem main_nds_nonpos_of_secondary {α : Type u} [DecidableEq α]
  (secondary_nds_nonpos :
    ∀ (T : FuncSetup α), isPoset T → (T.idealFamily).NDS ≤ 0)
  (S : FuncSetup α) :
  (S.idealFamily).NDS ≤ 0 := by
  classical
  -- 強い帰納法：P(k) := ∀ T, excess(T)=k → NDS(T) ≤ 0
  refine
    (Nat.strongRecOn
      (excess (S.idealFamily))
      (motive := fun k =>
        ∀ (T : FuncSetup α),
          excess (T.idealFamily) = k → (T.idealFamily).NDS ≤ 0)
      ?step) S rfl
  -- step: k の場合を示す
  · intro k IH T hk
    cases k with
    | zero =>
      have hposet : isPoset T := hk
      exact secondary_nds_nonpos T hposet
    | succ k' =>
      -- 0 < excess(T)
      have hpos : 0 < excess (T.idealFamily) := by
        rw [hk]; exact Nat.succ_pos _
      -- 非自明同値類
      obtain ⟨u, hnontriv⟩ :=
        exists_nontrivialClass_of_excess_pos (S := T) hpos
      -- NDS は trace で増えない
      have hNDS_mono :
          (T.idealFamily).NDS ≤ (Trace.traceAt u.1 (T.idealFamily)).NDS :=
        NDS_le_trace_of_nontrivialClass (S := T) (u := u) hnontriv
      -- 相方 v と sim
      obtain ⟨v, hneq_uv, hsim⟩ := hnontriv
      have hpar : (T.idealFamily).Parallel u v :=
        (T.parallel_iff_sim u v).2 hsim
      -- ground 非空
      have h_nonempty : (T.idealFamily).ground.card ≥ 1 := by
        have : 0 < (T.idealFamily).ground.card :=
          Finset.card_pos.mpr ⟨u.1, u.2⟩
        exact Nat.succ_le_of_lt this
      -- ground は family の要素
      have h_ground_sets :
          (T.idealFamily).sets (T.idealFamily).ground := by
        change isOrderIdealOn (T.leOn) T.ground (T.idealFamily).ground
        simp_all only [SetFamily.NDS_def, Nat.zero_lt_succ, traceAt_ground, Finset.coe_mem, Finset.card_erase_of_mem,
          Nat.cast_sub, Nat.cast_one, ne_eq, SetFamily.Parallel, FuncSetup.sets_iff_isOrderIdeal, ge_iff_le,
          Finset.one_le_card]
        obtain ⟨val, property⟩ := u
        obtain ⟨val_1, property_1⟩ := v
        simp_all only [Subtype.mk.injEq]
        rw [isOrderIdealOn]
        apply And.intro
        · rfl
        · intro x a y a_1 a_2
          exact a_1
      have h_excess :
          excess (Trace.traceAt u.1 (T.idealFamily))
            = excess (T.idealFamily) - 1 := by
        have hu : u.1 ∈ (T.idealFamily).ground := u.2
        -- v.1 ∈ ground, u.1 ≠ v.1
        have hv : v.1 ∈ (T.idealFamily).ground := v.2
        have hneqα : u.1 ≠ v.1 := by
          intro h'; have : u = v := Subtype.ext (by exact h'); exact hneq_uv (id (Eq.symm this))
        exact excess_trace
          (F := T.idealFamily) (hasU := h_ground_sets) (Nonemp := h_nonempty)
          (u := u.1) (v := v.1)
          (hu := hu) (hv := hv) (huv := hneqα) (hp := hpar)
      -- trace 後も functional
      have hNontriv' : FuncSetup.nontrivialClass T u :=
        ⟨v, And.intro hneq_uv hsim⟩  -- 順序を揃える
      let tisf := traced_is_functional_family T (u := u) hNontriv'
      obtain ⟨T', hTrace⟩ := tisf
      -- `excess (T'.idealFamily) = k'`
      have hex_T' : excess (T'.idealFamily) = k' := by
        calc
          excess (T'.idealFamily)
              = excess (Trace.traceAt u.1 (T.idealFamily)) := by
                rw [hTrace]
          _   = excess (T.idealFamily) - 1 := by exact h_excess
          _   = Nat.succ k' - 1 := by rw [hk]
          _   = k' := Nat.succ_sub_one k'
      -- 帰納法適用（k' < k.succ）
      have hIH_T' : (T'.idealFamily).NDS ≤ 0 :=
        IH k' (Nat.lt_succ_self k') T' hex_T'
      -- 仕上げ
      have hNDS_eq :
          (Trace.traceAt u.1 (T.idealFamily)).NDS
            = (T'.idealFamily).NDS := by
        rw [← hTrace]
      calc
        (T.idealFamily).NDS
            ≤ (Trace.traceAt u.1 (T.idealFamily)).NDS := hNDS_mono
        _   = (T'.idealFamily).NDS := hNDS_eq
        _   ≤ 0 := hIH_T'

---ここからは、isPosetのときに、本当にposetになっていることを示す。証明の一部はSetFunctionに。



/- `isPoset`（≡ excess=0）なら `|ground| = #classes`。 -/
lemma ground_card_eq_numClasses_of_isPoset
  (S : FuncSetup α) (h : isPoset S) :
  (S.idealFamily).ground.card = numClasses (S.idealFamily) := by
  classical
  -- excess = |ground| − #classes = 0 ⇒ |ground| ≤ #classes
  have hle₁ :
      (S.idealFamily).ground.card ≤ numClasses (S.idealFamily) := by
    -- `Nat.sub_eq_zero.mp : a - b = 0 → a ≤ b`
    -- 定義 `excess := ground.card - numClasses`
    -- 実ファイルでは `simp [excess, numClasses] at h`
    -- ここでは直接：

    exact tsub_eq_zero_iff_le.mp (by
      -- `excess (S.idealFamily) = 0` が `h`
      -- そのまま使う
      exact h)
  -- 逆向き：#classes ≤ |ground|
  have hle₂ :
      numClasses (S.idealFamily) ≤ (S.idealFamily).ground.card :=
    numClasses_le_ground_card (F := S.idealFamily)
  exact Nat.le_antisymm hle₁ hle₂

/- `isPoset S` なら `classSet (S.idealFamily)` の各クラスの大きさは 1。 -/
lemma classes_card_one_of_isPoset
  (S : FuncSetup α) (h : isPoset S) :
  ∀ C ∈ classSet (S.idealFamily), C.card = 1 := by
  classical
  let F := S.idealFamily
  -- 非空
  have hnon : ∀ C ∈ classSet F, C.Nonempty :=
    classSet_nonempty (F := F)
  -- 互いに素
  have hdisj :
      ∀ C ∈ classSet F, ∀ D ∈ classSet F, C ≠ D → Disjoint C D :=
    by intro C hC D hD hne; exact classSet_disjoint_of_ne (F := F) hC hD hne
  -- 被覆
  have hcover : F.ground = Finset.biUnion (classSet F) (fun C => C) :=
    ground_eq_biUnion_classSet (F := F)
  -- 全体サイズ＝ブロック個数（isPoset → equality）
  have hcard : F.ground.card = (classSet F).card :=
    ground_card_eq_numClasses_of_isPoset (S := S) h
  -- 抽象補題を適用
  have hiff :=
    card_eq_blocks_iff_all_blocks_card_one
      (s := F.ground) (P := classSet F) hdisj hcover hnon
  -- `s.card = P.card` の「→」向きを使う
  -- 実ファイルでは `exact (hiff.mp hcard)`
  exact (by
    -- 1 行：`exact (Iff.mp hiff hcard)`
    exact (Iff.mp hiff hcard))



lemma antisymm_of_isPoset
  (S : FuncSetup α) (h : isPoset S) :
  ∀ {u v : S.Elem}, S.le u v → S.le v u → u = v := by
  classical
  intro u v hxy hyx
  -- まず `sim u v`
  have hsim : S.sim u v := And.intro hxy hyx
  -- `isPoset` から「全クラスのサイズ＝1」
  have hall1 : ∀ C ∈ classSet (S.idealFamily), C.card = 1 :=
    classes_card_one_of_isPoset (S := S) h
  -- 3) を適用
  exact FuncSetup.eq_of_sim_of_all_classes_card_one S hall1 hsim

instance functional_poset (S : FuncSetup α) (h : isPoset S) :
   PartialOrder S.Elem := by
  refine { le := S.le,
           le_refl := fun a => by exact FuncSetup.le_refl S a,
           le_trans := fun a b c hab hbc => by exact FuncSetup.le_trans S hab hbc,
           le_antisymm := fun a b hab hba => by exact antisymm_of_isPoset S h hab hba }

--逆にFuncSetupがすべての同値類のサイズが1のときに、isPosetになる。
lemma isPoset_of_classes_card_one (S : FuncSetup α) (h : ∀ C ∈ classSet (S.idealFamily), C.card = 1) :
  isPoset S := by
  classical
  dsimp [isPoset]
  dsimp [excess]
  dsimp [SetFamily.numClasses]
  --dsimp [SetFamily.classSet]
  rw [card_ground_eq_sum_card_classes]
  simp_all only [Finset.sum_const, smul_eq_mul, mul_one, tsub_self]

--FuncSetupのleがanti-symmetricなときに、isPosetになる。
lemma isPoset_of_le_antisymm (S : FuncSetup α) (h : ∀ {u v : S.Elem}, S.le u v → S.le v u → u = v) :
  isPoset S := by
  --任意のsimClassが1要素集合であることを示す。
  have : ∀ (x : S.Elem), (S.simClass x).card  = 1 := by
    intro x
    dsimp [SPO.FuncSetup.simClass]
    dsimp [SPO.FuncSetup.simClassElem]
    dsimp [SPO.FuncSetup.sim]
    simp
    simp_all only [FuncSetup.le_iff_leOn_val, Subtype.forall, Subtype.mk.injEq, Finset.coe_mem]
    refine Finset.card_eq_one.mpr ?_
    use x
    obtain ⟨val, property⟩ := x
    simp_all only [Finset.coe_mem]
    ext
    simp_all only [Finset.coe_mem, Finset.mem_image, Finset.mem_filter, Finset.mem_attach, true_and, Subtype.exists,
      exists_and_left, exists_prop, exists_eq_right_right, Finset.mem_singleton]
    apply Iff.intro
    · intro a
      obtain ⟨left, right⟩ := a
      obtain ⟨left, right_1⟩ := left
      apply h
      · simp_all only
      · simp_all only
      · simp_all only
      · simp_all only
    · intro a
      subst a
      simp_all only [and_self, and_true]
      tauto

  have :  ∀ C ∈ classSet (S.idealFamily), C.card = 1 := by
    intro C hC
    dsimp [SetFamily.classSet] at hC
    rw [Finset.mem_image] at hC
    obtain ⟨a,ha⟩ := hC
    let sf :=  SPO.FuncSetup.simClass_eq_parallelClass S (S.toElem! ha.1)
    simp at sf
    rw [←sf] at ha
    specialize this (S.toElem! ha.1)
    have :(S.idealFamily.ParallelClass (S.toElem! ha.1)).card = 1:= by
      simp_all only [FuncSetup.le_iff_leOn_val, Subtype.forall, Subtype.mk.injEq, FuncSetup.toElem!_val]
    simp_all only [FuncSetup.le_iff_leOn_val, Subtype.forall, Subtype.mk.injEq, FuncSetup.toElem!_val]

  exact isPoset_of_classes_card_one S this

end PaperSync
end AvgRare
