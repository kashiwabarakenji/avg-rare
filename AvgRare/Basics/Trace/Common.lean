import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import AvgRare.Basics.SetFamily
import AvgRare.Basics.Ideals
import LeanCopilot

/-
Common.lean — Trace と汎用補助

このファイルでは
* 1点トレース `Trace.traceAt`
* 並行性 `Trace.Parallel`
* その場で使える小補助

を提供します。証明が重い主張（単射性など）は「言明だけ」を先に置き、
後で `IdealsTrace.lean` 等で埋める方針です。
-/

universe u
open Classical
open scoped BigOperators

namespace AvgRare
namespace Trace
open SetFamily

variable {α : Type u} [DecidableEq α]

/-- 1点トレース：各ハイパーエッジから要素 `x` を取り除いた族。
`ground` は `F.ground.erase x` に落とす。 -/
--idealだけでなく、集合族一般にTraceを定義している。
noncomputable def traceAt (x : α) (F : SetFamily α) : SetFamily α := by
  classical
  refine
  { ground := F.ground.erase x
    , sets   := fun B =>
        ∃ A : Finset α, F.sets A ∧ B = A.erase x
    , decSets := Classical.decPred _
    , inc_ground := ?_ }
  intro B hB
  rcases hB with ⟨A, hA, hBsub, hBsubU⟩
  intro y
  simp only [Finset.mem_erase]
  intro h
  constructor
  · exact h.1
  · exact F.inc_ground hA (by
      -- `y ∈ A.erase x` なら `y ∈ A` なので、`A ⊆ F.ground` を使う
      simp_all only [ne_eq])

@[simp] lemma traceAt_ground (x : α) (F : SetFamily α) :
    (traceAt x F).ground = F.ground.erase x := rfl

/-
--ここからは使わないかも。今のところ使うかどうか不明なのでコメントアウト。
/-- `Subtype` のエッジを `erase u` に写す自然な射。 -/
def eraseMap (F : SetFamily α) (u : α) :
    {A // F.sets A} → Finset α := fun A => (Subtype.val A).erase u

@[simp] lemma eraseMap_apply (F : SetFamily α) (u : α) (A : {A // F.sets A}) :
    eraseMap F u A = (A.val).erase u := rfl
-/


--traceした時のhyperedgeがどうなるかの補題。数が減らないこともこれでわかるのかも。
--uにパラレルな要素を仮定してない。両辺一致はするが、両方とも数が減っているかもしれないということか。
--使っていたところをコメントアウトしたので現状使ってない。
--traceしても同値類の大きさが変わらないというところに使うので、Common.leanに移動。
lemma edgeFinset_traceAt_eq_image_erase (F : SetFamily α) (u : α) :
  (traceAt u F).edgeFinset = F.edgeFinset.image (λ A => A.erase u) := by
  ext B
  constructor
  · -- (→) traceAt の edgeFinset にある集合は元エッジの erase
    intro hB
    simp only [SetFamily.edgeFinset, traceAt, Finset.mem_filter,
               Finset.mem_powerset] at hB
    obtain ⟨hBsub, hSets⟩ := hB
    match decide (∃ A, F.sets A ∧ B = A.erase u) with
    | true =>
      simp only [decide_eq_true_eq] at hSets
      rcases hSets with ⟨A, hAsets, rfl⟩
      rw [Finset.mem_image]
      refine ⟨A, ?_, rfl⟩
      simp only [SetFamily.edgeFinset, Finset.mem_filter,
                 Finset.mem_powerset]
      constructor
      · exact F.inc_ground hAsets
      · exact decide_eq_true hAsets
    | false =>
      simp only [decide_eq_true_eq] at hSets
      rw [Finset.mem_image]
      obtain ⟨A, hAin, rfl⟩ := hSets
      use A
      constructor
      · exact (SetFamily.mem_edgeFinset_iff_sets F).mpr hAin
      · exact rfl

  · -- (←) 元エッジ A の erase は traceAt のエッジ
    intro hB
    simp only [Finset.mem_image] at hB
    rcases hB with ⟨A, hAin, rfl⟩
    simp only [SetFamily.edgeFinset, traceAt,
      Finset.mem_filter, Finset.mem_powerset]
    simp only [SetFamily.edgeFinset, Finset.mem_filter,
      Finset.mem_powerset] at hAin
    obtain ⟨hAsub, hAsets⟩ := hAin
    constructor
    · -- erase ⊆ ground.erase
      intro x hx
      rw [Finset.mem_erase] at hx
      rw [Finset.mem_erase]
      constructor
      · exact hx.1
      · exact hAsub hx.2
    · -- sets 部分は match で強制する
      simp_all only [decide_eq_true_eq]
      exact ⟨A, hAsets, rfl⟩




lemma trace_filter_eq_image_filter_of_ne
  (F : SetFamily α) (u w : α) (hwu : w ≠ u) :
  (traceAt u F).edgeFinset.filter (fun B => w ∈ B)
  =
  (F.edgeFinset.filter (fun A => w ∈ A)).image (fun A => A.erase u) := by
  classical
  -- まず全体が image という事実を filter にかける
  have H := edgeFinset_traceAt_eq_image_erase (F := F) (u := u)
  -- `w ≠ u` なら `w ∈ A.erase u ↔ w ∈ A`
  -- これで「filter 後の像 = 像後の filter」が素直に言えます（injective は不要）。
  apply Finset.ext
  intro B
  constructor
  · intro hB
    rcases Finset.mem_filter.mp hB with ⟨hBmem, hBw⟩
    have : B ∈ (F.edgeFinset.image fun A => A.erase u) := by simpa [H] using hBmem
    rcases Finset.mem_image.mp this with ⟨A, hA, rfl⟩
    -- `w ∈ A.erase u` から `w ∈ A`（w ≠ u を使用）
    have : w ∈ A := by
      -- Finset.mem_erase: w ∈ A.erase u ↔ (w ≠ u ∧ w ∈ A)
      simpa [Finset.mem_erase, hwu] using hBw
    exact Finset.mem_image.mpr ⟨A, (Finset.mem_filter.mpr ⟨hA, this⟩), rfl⟩
  · intro hB
    rcases Finset.mem_image.mp hB with ⟨A, hA, rfl⟩
    rcases Finset.mem_filter.mp hA with ⟨hAedge, hAw⟩
    -- 右から左へ：A.erase u がトレース側の edge で、かつ w を含む
    refine Finset.mem_filter.mpr ?_
    constructor
    · simpa [H]
      using (Finset.mem_image.mpr ⟨A, hAedge, rfl⟩ :
        A.erase u ∈ (F.edgeFinset.image fun A => A.erase u))
    · -- `w ∈ A.erase u`（w ≠ u を使用）
      -- again: mem_erase ↔ (w ≠ u ∧ w ∈ A)
      simpa [Finset.mem_erase, hwu] using hAw

-- 補助：S.filter p = S.filter q ↔ ∀ x∈S, p x ↔ q x
lemma filter_eq_iff_on {β} [DecidableEq β]
  {S : Finset β} {p q : β → Prop}
  [DecidablePred p] [DecidablePred q] :
  S.filter p = S.filter q ↔ (∀ x ∈ S, p x ↔ q x) := by
  constructor
  · intro h x hx
    -- 等式の両辺で x の帰属が同値
    have := congrArg (fun (T : Finset β) => x ∈ T) h
    -- x∈S を仮定して filter の展開
    simpa [Finset.mem_filter, hx] using this
  · intro h
    ext x; constructor <;> intro hx
    · rcases (Finset.mem_filter).1 hx with ⟨hxS, hpx⟩
      have : q x := (h x hxS).1 hpx
      exact (Finset.mem_filter).2 ⟨hxS, this⟩
    · rcases (Finset.mem_filter).1 hx with ⟨hxS, hqx⟩
      have : p x := (h x hxS).2 hqx
      exact (Finset.mem_filter).2 ⟨hxS, this⟩

--パラレルパートナーの存在は必要なかった。
lemma parallel_off_u_preserved_by_trace
  {α : Type*}
  [DecidableEq α]
  (F : SetFamily α) (u w z : α)
  (hw : w ≠ u) (hz : z ≠ u) :
  Parallel_edge (traceAt u F) w z ↔ Parallel_edge F w z := by
  -- 既知：エッジ集合は erase の像
  have himg :
      (traceAt u F).edgeFinset
        = F.edgeFinset.image (fun A : Finset α => A.erase u) :=
    edgeFinset_traceAt_eq_image_erase F u

  -- （→）方向
  constructor
  · intro htr
    -- trace 側のフィルタ等式を、像集合上の述語同値に言い換え
    have h_on_image :
      ∀ B ∈ (F.edgeFinset.image (fun A => A.erase u)),
        (w ∈ B) ↔ (z ∈ B) := by
      -- filter_eq_iff_on を使うために書き換え
      have := (filter_eq_iff_on
        (S := (traceAt u F).edgeFinset)
        (p := fun B => w ∈ B) (q := fun B => z ∈ B)).1
        (by simp [himg]
            dsimp [Parallel_edge] at htr
            simp [himg] at htr
            exact htr
        )

      -- いまの this は (trace 側の) 外側集合＝像集合の上での同値
      simpa [himg] using this
    -- これを元集合側に引き戻す（画像の元は A.erase u）
    -- A∈F.edgeFinset に対し、B := A.erase u と置けば B は像集合の元
    have h_on_domain :
      ∀ A ∈ F.edgeFinset, (w ∈ A) ↔ (z ∈ A) := by
      intro A hA
      have : (w ∈ A.erase u) ↔ (z ∈ A.erase u) := by
        exact h_on_image (A.erase u)
          (by exact Finset.mem_image.mpr ⟨A, hA, rfl⟩)
      -- w,z ≠ u なので erase を通してもメンバーシップは不変
      -- x ∈ A.erase u ↔ (x ≠ u ∧ x ∈ A)
      have hw' : (w ∈ A.erase u) ↔ (w ∈ A) := by
        simp [Finset.mem_erase, hw]  -- hw で簡約
      have hz' : (z ∈ A.erase u) ↔ (z ∈ A) := by
        simp [Finset.mem_erase, hz]
      -- 置換して結論
      simpa [hw', hz'] using this
    -- ドメイン側の述語同値から filter の等式へ戻す
    exact
      (filter_eq_iff_on (S := F.edgeFinset)
        (p := fun A => w ∈ A) (q := fun A => z ∈ A)).2 h_on_domain

  -- （←）方向も同じ理屈を逆にたどる
  · intro hdom
    have h_on_domain :
      ∀ A ∈ F.edgeFinset, (w ∈ A) ↔ (z ∈ A) :=
      (filter_eq_iff_on
        (S := F.edgeFinset)
        (p := fun A => w ∈ A) (q := fun A => z ∈ A)).1 hdom
    -- 画像側での同値（A.erase u を介して移すだけ）
    have h_on_image :
      ∀ B ∈ (F.edgeFinset.image (fun A => A.erase u)),
        (w ∈ B) ↔ (z ∈ B) := by
      intro B hB
      rcases (Finset.mem_image).1 hB with ⟨A, hA, rfl⟩
      have hw' : (w ∈ A.erase u) ↔ (w ∈ A) := by
        simp [Finset.mem_erase, hw]
      have hz' : (z ∈ A.erase u) ↔ (z ∈ A) := by
        simp [Finset.mem_erase, hz]
      simpa [hw', hz'] using (h_on_domain A hA)
    -- 画像側の述語同値から trace 側の filter 等式へ
    have : (traceAt u F).edgeFinset.filter (fun B => w ∈ B)
           = (traceAt u F).edgeFinset.filter (fun B => z ∈ B) := by
      -- いったん像集合に書き換え
      have := (filter_eq_iff_on
        (S := F.edgeFinset.image (fun A => A.erase u))
        (p := fun B => w ∈ B) (q := fun B => z ∈ B)).2 h_on_image
      simpa [himg] using this
    exact this

omit [DecidableEq α] in
lemma parallel_off_u_preserved_by_trace2
  [DecidableEq α] (F : SetFamily α) (u w z : α)
  (hw : w ≠ u) (hz : z ≠ u) :
  Parallel (traceAt u F) w z ↔ Parallel F w z := by
  let pe := parallel_off_u_preserved_by_trace F u w z hw hz
  rw [Parallel_edge_iff_Parallel ] at pe
  rw [Parallel_edge_iff_Parallel ] at pe
  exact pe

noncomputable def excess (F : SetFamily α) : ℕ :=
  F.ground.card - numClasses F

lemma ParallelClass_trace_eq_erase
  (F : SetFamily α) (u a : α)
  (ha : a ∈ F.ground.erase u) :
  ParallelClass (traceAt u F) a = (ParallelClass F a).erase u := by
  classical
  -- 述語レベルで会員判定を対応付ける
  apply Finset.ext
  intro b
  -- 左→右
  have LtoR : b ∈ ParallelClass (traceAt u F) a →
              b ∈ (ParallelClass F a).erase u := by
    intro hb
    -- b ∈ ground.erase u かつ Parallel(trace) a b
    have hb' :
      (b ∈ (traceAt u F).ground ∧ Parallel (traceAt u F) a b) :=
      (mem_ParallelClass_iff (traceAt u F) a b).1 hb
    -- b ≠ u は ground.erase u から
    have hb_ne_u : b ≠ u := (Finset.mem_erase.mp hb'.1).1
    -- Parallel(trace) a b ↔ Parallel F a b （b ≠ u だから保存）
    have hiff :=
      parallel_off_u_preserved_by_trace2
        (F := F) (u := u) (w := a) (z := b)
        (hw := (Finset.mem_erase.mp ha).1) (hz := hb_ne_u)
    -- Parallel F a b を得る
    have hab : Parallel F a b := by
      exact (Iff.mp hiff) hb'.2
    -- b ∈ ground は ground.erase u から
    have hbg : b ∈ F.ground := (Finset.mem_erase.mp hb'.1).2
    -- 右辺の会員判定
    have hbC : b ∈ ParallelClass F a :=
      (mem_ParallelClass_iff F a b).2 (And.intro hbg hab)
    -- さらに erase u の会員（b ≠ u）へ
    exact Finset.mem_erase.mpr (And.intro hb_ne_u hbC)
  -- 右→左
  have RtoL : b ∈ (ParallelClass F a).erase u →
              b ∈ ParallelClass (traceAt u F) a := by
    intro hb
    have hb_ne_u : b ≠ u := (Finset.mem_erase.mp hb).1
    have hbC     : b ∈ ParallelClass F a := (Finset.mem_erase.mp hb).2
    have hbC' :
      (b ∈ F.ground ∧ Parallel F a b) :=
      (mem_ParallelClass_iff F a b).1 hbC
    -- Parallel F a b ↔ Parallel(trace) a b（保存）
    have hiff :=
      parallel_off_u_preserved_by_trace2
        (F := F) (u := u) (w := a) (z := b)
        (hw := (Finset.mem_erase.mp ha).1) (hz := hb_ne_u)
    have hab_t : Parallel (traceAt u F) a b := by
      simp_all only [Finset.mem_erase, ne_eq, mem_ParallelClass_iff, traceAt_ground, not_false_eq_true, and_self, Parallel,
        true_and, implies_true, and_true, iff_true]
    -- ground.erase u での所属
    have hbg_t : b ∈ (traceAt u F).ground := by
      have : b ∈ F.ground.erase u :=
        Finset.mem_erase.mpr (And.intro hb_ne_u hbC'.1)
      -- 定義展開で置換
      -- (traceAt u F).ground = F.ground.erase u
      have : b ∈ (traceAt u F).ground := by
        -- 直接 rfl なので cast で十分
        exact cast (by rfl) this
      exact this
    exact (mem_ParallelClass_iff (traceAt u F) a b).2
           (And.intro hbg_t hab_t)
  constructor
  · intro h; exact LtoR h
  · intro h; exact RtoL h

/-- `classSet (traceAt u F)` は `classSet F` を `erase u` した像。
    代表が `u` の場合は `v` に差し替えて扱う（`u‖v` を使用）。 -/
lemma classSet_trace_eq_image_erase_of_parallel
  (F : SetFamily α) {u v : α}
  (hu : u ∈ F.ground) (hv : v ∈ F.ground)
  (hne : u ≠ v) (hp : Parallel F u v) :
  classSet (traceAt u F) = (classSet F).image (fun C => C.erase u) := by
  classical
  -- 左⊆右
  apply Finset.ext
  intro D
  constructor
  · intro hD
    -- D = class(trace) a（a ∈ ground.erase u）から構成
    obtain ⟨a, ha, hDdef⟩ :
        ∃ a, a ∈ F.ground.erase u ∧
              D = ParallelClass (traceAt u F) a := by
      -- classSet(trace) = (ground.erase u).image (class(trace))
      -- なので mem_image から取り出す
      have h := (Finset.mem_image.mp hD)
      -- h : ∃ a, a ∈ ground.erase u ∧ D = class(trace) a
      obtain ⟨a, ha, hDdef⟩ := h
      exact ⟨a, ha, hDdef.symm⟩
    -- D = (ParallelClass F a).erase u
    have hD' :
        D = (ParallelClass F a).erase u :=
      by
        -- ParallelClass_trace_eq_erase の対称形で書換
        have h := ParallelClass_trace_eq_erase (F := F) (u := u) (a := a) ha
        -- h : class(trace) a = (class F a).erase u
        -- D = class(trace) a を左へ
        -- Eq の書き換えは `rw` ではなく明示 `cast` で行う
        -- ここでは最終的に `D = ...` を示したいので、直接等式計算
        exact Eq.trans hDdef h
    -- 以上から D は右辺像の元
    have hsrc : ParallelClass F a ∈ classSet F := by
      -- classSet F = ground.image (class F)
      -- a ∈ ground.erase u なので a ∈ ground
      have ha_g : a ∈ F.ground := (Finset.mem_erase.mp ha).2
      exact Finset.mem_image.mpr (Exists.intro a (And.intro ha_g rfl))
    apply Finset.mem_image.mpr (Exists.intro (ParallelClass F a)
           (And.intro hsrc hD'.symm))
  · intro hD
    -- 右→左：D = C.erase u, C ∈ classSet F
    obtain ⟨C, hC, hDdef⟩ :
        ∃ C, C ∈ classSet F ∧  C.erase u = D :=
      Finset.mem_image.mp hD
    -- C = class F a
    obtain ⟨a, ha, hCdef⟩ :
        ∃ a, a ∈ F.ground ∧ ParallelClass F a = C:=
      Finset.mem_image.mp hC
    -- 場合分け a = u / a ≠ u
    by_cases hau : a = u
    · -- a = u の場合：`u‖v` なので `class(trace) v = (class F u).erase u`
      -- D = C.erase u = (class F u).erase u = (class F v).erase u
      have hCv : C = ParallelClass F v := by
        -- C = class F a = class F u = class F v
        have h1 : C = ParallelClass F u := by
          exact Eq.trans hCdef.symm (by exact congrArg F.ParallelClass hau)  -- 安定化：型合わせだけ
        have h2 : ParallelClass F u = ParallelClass F v :=
          by
            -- u‖v よりクラス同一
            --have := parallel_trans (F := F)-- (parallel_symm' (F := F) hp) hp
            -- 直接クラス等式
            -- （簡潔に）クラスの定義から `ParallelClass_eq_of_parallel` 相当
            -- ここでは `Finset.ext` を使う：
            apply Finset.ext
            intro x
            -- 左右の会員判定を `mem_ParallelClass_iff` で開いてから、平行の推移
            have L : x ∈ ParallelClass F u ↔ (x ∈ F.ground ∧ Parallel F u x) :=
              (mem_ParallelClass_iff F u x)
            have R : x ∈ ParallelClass F v ↔ (x ∈ F.ground ∧ Parallel F v x) :=
              (mem_ParallelClass_iff F v x)
            constructor
            · intro hx
              have hx' := (Iff.mp L) hx
              -- Parallel F v x は u‖v から
              have hvx : Parallel F v x := by
                subst h1 hau hDdef
                simp_all only [mem_ParallelClass_iff, Parallel, true_and, ne_eq, true_iff, and_self, and_true, Finset.mem_image]
              exact (Iff.mpr R) (And.intro hx'.1 hvx)
            · intro hx
              have hx' := (Iff.mp R) hx
              have hux : Parallel F u x :=
                parallel_trans (F := F) hp hx'.2
              exact (Iff.mpr L) (And.intro hx'.1 hux)
        -- h1 : C = class F u, h2 : class F u = class F v
        exact Eq.trans h1 h2
      -- v は ground.erase u に入る
      have hv' : v ∈ F.ground.erase u :=
        Finset.mem_erase.mpr (And.intro (ne_comm.mp hne) hv)
      -- したがって D は左辺の元：D = class(trace) v
      have : D = ParallelClass (traceAt u F) v := by
        -- D = C.erase u = (ParallelClass F v).erase u = class(trace) v
        have h3 : D = (ParallelClass F v).erase u :=
          Eq.trans hDdef.symm (by exact congrArg (fun t => t) (congrFun (congrArg Finset.erase hCv) u))
        -- 対称形にしてから `ParallelClass_trace_eq_erase`
        have h4 :=
          ParallelClass_trace_eq_erase (F := F) (u := u) (a := v) hv'
        -- h4 : class(trace) v = (class F v).erase u
        -- よって (class F v).erase u = class(trace) v
        have h4' : (ParallelClass F v).erase u = ParallelClass (traceAt u F) v :=
          Eq.symm h4
        exact Eq.trans h3 h4'
      -- membership に戻す
      apply Finset.mem_image.mpr
      apply Exists.intro v
      · constructor
        · exact hv'
        · exact id (Eq.symm this)

    · -- a ≠ u の場合は、`a` を代表にしてそのまま戻す
      -- D = (class F a).erase u = class(trace) a
      have : D = ParallelClass (traceAt u F) a := by
        -- ParallelClass_trace_eq_erase の逆向き
        have h := ParallelClass_trace_eq_erase
                   (F := F) (u := u) (a := a)
                   (Finset.mem_erase.mpr (And.intro hau ha))
        -- h : class(trace) a = (class F a).erase u
        -- 逆向きにする
        have h' : (ParallelClass F a).erase u = ParallelClass (traceAt u F) a :=
          Eq.symm h
        -- D = C.erase u = (class F a).erase u = class(trace) a
        exact Eq.trans hDdef.symm (Eq.trans (by rw [hCdef]) h')
      -- membership
      apply Finset.mem_image.mpr
      apply Exists.intro a
      · constructor
        · subst this hCdef
          simp_all only [ne_eq, Parallel, Finset.mem_image, traceAt_ground, Finset.mem_erase, not_false_eq_true, and_self]
        · exact id (Eq.symm this)

/-- `erase u` は `classSet F` 上で単射（`u‖v` のとき）。 -/
lemma erase_on_classSet_injective_of_parallel
  (F : SetFamily α) (hasU: F.sets F.ground) {u v : α}
  (hu : u ∈ F.ground) --(hv : v ∈ F.ground)
  (hne : u ≠ v) (hp : Parallel F u v) :
  Function.Injective
    (fun (C : {C // C ∈ classSet F}) => (C.1).erase u) := by
  classical
  intro C D hEq
  -- `C.1` と `D.1` をそれぞれ `Cset`, `Dset` と名付けて扱う
  let Cset := C.1
  let Dset := D.1
  have hCmem : Cset ∈ classSet F := C.2
  have hDmem : Dset ∈ classSet F := D.2
  -- 目標：Cset = Dset
  -- Finset.ext で任意の x に対して同値を示す
  apply Subtype.ext
  apply Finset.ext
  intro x
  by_cases hx : x = u
  · -- x = u：`u ∈ Cset ↔ v ∈ Cset ↔ v ∈ Dset ↔ u ∈ Dset`
    -- v ≠ u
    have hvne : v ≠ u := ne_comm.mp hne
    -- `v ∈ Cset.erase u ↔ v ∈ Dset.erase u` は hEq から
    have hveq : (v ∈ Cset.erase u) ↔ (v ∈ Dset.erase u) := by
      -- 等式の両辺でメンバ判定を移す
      -- `congrArg` を使わず、明示に両方向を与える
      constructor
      · intro hvC
        -- hEq : Cset.erase u = Dset.erase u
        -- 置換
        have : v ∈ Dset.erase u := by
          -- cast を用いた置換（安定）
          subst hx
          simp_all only [Finset.coe_mem, ne_eq, Parallel, Finset.mem_erase, not_false_eq_true, true_and, and_self, Cset, Dset]

        exact this
      · intro hvD
        have : v ∈ Cset.erase u := by
          subst hx
          simp_all only [Finset.coe_mem, ne_eq, Parallel, Finset.mem_erase, not_false_eq_true, true_and, and_self, Cset, Dset]


        exact this
    -- `v ≠ u` なので、`v ∈ S.erase u ↔ v ∈ S`
    have hvC_iff : (v ∈ Cset.erase u) ↔ (v ∈ Cset) := by
      constructor
      · intro hvC
        exact (Finset.mem_erase.mp hvC).2
      · intro hvC
        exact Finset.mem_erase.mpr (And.intro hvne hvC)
    have hvD_iff : (v ∈ Dset.erase u) ↔ (v ∈ Dset) := by
      constructor
      · intro hvD
        exact (Finset.mem_erase.mp hvD).2
      · intro hvD
        exact Finset.mem_erase.mpr (And.intro hvne hvD)
    -- 連結：u∈Cset ↔ v∈Cset（同値）↔ v∈Dset ↔ u∈Dset
    have h1 : (u ∈ Cset) ↔ (v ∈ Cset) := by
      apply mem_u_iff_mem_v_of_class F
      subst hx
      simp_all only [Finset.coe_mem, ne_eq, Parallel, Finset.mem_erase, not_false_eq_true, true_and, Cset, Dset]
      exact hp
      exact hCmem
    have h2 : (u ∈ Dset) ↔ (v ∈ Dset) := by
      apply mem_u_iff_mem_v_of_class F hasU hp hDmem
    -- まとめ
    constructor
    · intro huC
      have hvC : v ∈ Cset := by
        subst hx
        simp_all only [Finset.coe_mem, ne_eq, Parallel, Finset.mem_erase, not_false_eq_true,
          true_and, iff_true, Cset, Dset]

      have hvD : v ∈ Dset := by
        have : v ∈ Cset.erase u := (Iff.mpr hvC_iff) hvC
        have : v ∈ Dset.erase u := (Iff.mp hveq) this
        exact (Iff.mp hvD_iff) this
      subst hx
      simp_all only [Finset.coe_mem, ne_eq, Parallel, Finset.mem_erase, not_false_eq_true, and_self, iff_true, Cset, Dset]

    · intro huD
      have hvD : v ∈ Dset := by
        subst hx
        simp_all only [Finset.coe_mem, ne_eq, Parallel, Finset.mem_erase, not_false_eq_true, true_and, true_iff, Cset, Dset]

      have hvC : v ∈ Cset := by
        have : v ∈ Dset.erase u := (Iff.mpr hvD_iff) hvD
        have : v ∈ Cset.erase u := (Iff.mpr hveq) this
        exact (Iff.mp hvC_iff) this
      subst hx
      simp_all only [Finset.coe_mem, ne_eq, Parallel, Finset.mem_erase, not_false_eq_true, and_self, iff_true, Cset, Dset]

  · -- x ≠ u：`x ∈ S` ↔ `x ∈ S.erase u` で両辺の等式から移す
    have hxC_iff : (x ∈ Cset) ↔ (x ∈ Cset.erase u) := by
      constructor
      · intro hxC; exact Finset.mem_erase.mpr (And.intro hx hxC)
      · intro hxC; exact (Finset.mem_erase.mp hxC).2
    have hxD_iff : (x ∈ Dset) ↔ (x ∈ Dset.erase u) := by
      constructor
      · intro hxD; exact Finset.mem_erase.mpr (And.intro hx hxD)
      · intro hxD; exact (Finset.mem_erase.mp hxD).2
    -- 等式 hEq を介して `x ∈ Cset.erase u ↔ x ∈ Dset.erase u`
    have heq_x :
        (x ∈ Cset.erase u) ↔ (x ∈ Dset.erase u) := by
      constructor
      · intro hxC
        simp [Dset]
        constructor
        · exact hx
        · simp_all [Cset]
      · intro hxD
        simp_all only [ne_eq, Parallel, Finset.coe_mem, Finset.mem_erase, not_false_eq_true, and_self, Cset, Dset]

    -- まとめ
    constructor
    · intro hxC
      have : x ∈ Cset.erase u := (Iff.mp hxC_iff) hxC
      have : x ∈ Dset.erase u := (Iff.mp heq_x) this
      exact Finset.mem_of_mem_erase this
    · intro hxD
      have : x ∈ Dset.erase u := (Iff.mp hxD_iff) hxD
      have : x ∈ Cset.erase u := (Iff.mpr heq_x) this
      exact Finset.mem_of_mem_erase this


@[simp] lemma ground_card_trace_of_mem
    (F : SetFamily α) {u : α} (hu : u ∈ F.ground) :
    (traceAt u F).ground.card = F.ground.card - 1 := by
  classical
  -- `traceAt` の ground 定義が `F.ground.erase u` であることを使用
  simp [traceAt, hu]

/-- ★ 最終目標：`excess` は 1 減る。 -/
lemma excess_trace
  (F : SetFamily α) (hasU: F.sets F.ground)(Nonemp:F.ground.card ≥ 1) (u v : α)
  (hu : u ∈ F.ground) (hv : v ∈ F.ground)
  (huv : u ≠ v) (hp : Parallel F u v) :
  excess (traceAt u F) = excess F - 1 := by
  classical
  -- 台集合サイズは 1 減る
  have hground :
      (traceAt u F).ground.card = F.ground.card - 1 := by
    apply ground_card_trace_of_mem (F := F) (hu := hu)
  -- クラス集合は `erase u` の像と一致
  have hclassSet :
      classSet (traceAt u F) = (classSet F).image (fun C => C.erase u) :=
    classSet_trace_eq_image_erase_of_parallel
      (F := F) (hu := hu) (hv := hv) (hne := huv) (hp := hp)
  -- 像の濃度 = 元集合の濃度（単射）
  have hinj :
      Function.Injective
        (fun (C : {C // C ∈ classSet F}) => (C.1).erase u) := by
    apply erase_on_classSet_injective_of_parallel hasU
      (F := F) (hu := hu) (hne := huv) (hp := hp)
  -- `card (image f S) = card S` を得る
  have hcard_image :
      ((classSet F).image (fun C => C.erase u)).card
      = (classSet F).card := by
    -- Finset.card_image は「≤」しか出さないので、単射版を組み立て
    -- 付随する Subtype 版の injective から結論
    -- 既存補題：card_image_iff.mpr 形式がない場合は、標準の `card_image` + `le_antisymm`
    -- だがここは inj を供給できるので、`Finset.card_image_...` 同値版を使う
    -- 安定のため明示に書く：
    apply Finset.card_image_of_injOn

    exact Set.injOn_iff_injective.mpr hinj -- ← もし手元の mathlib で card=card の直接補題名が違う場合、ここを差し替えて下さい。
  -- クラス個数は等しい
  have hnum :
      numClasses (traceAt u F) = numClasses F := by
    -- 定義展開と `hclassSet`、`hcard_image`
    unfold numClasses
    have : (classSet (traceAt u F)).card
           = ((classSet F).image (fun C => C.erase u)).card :=
      congrArg Finset.card hclassSet
    -- これで card = card
    have : (classSet (traceAt u F)).card = (classSet F).card :=
      Eq.trans this hcard_image
    -- そのまま戻す
    exact this
  -- あとは算術
  -- LHS = (a - 1) - b, RHS = (a - b) - 1 をともに a - (b + 1) に落とす
  unfold excess
  -- 左辺 使わなかったのか？
  have L :
      (traceAt u F).ground.card - numClasses (traceAt u F)
      = (F.ground.card:Int) - (1 + numClasses F) := by
    -- ground.card = a - 1, classes = b
    -- (a - 1) - b = a - (1 + b)
    have : (traceAt u F).ground.card = F.ground.card - 1 := hground
    have : (F.ground.card - 1) - numClasses (traceAt u F)
           = F.ground.card - (1 + numClasses (traceAt u F)) :=
      Nat.sub_sub _ _ _
    -- 書き換え
    -- numClasses(trace) = numClasses F
    have : F.ground.card - (1 + numClasses (traceAt u F))
           = F.ground.card - (1 + numClasses F) := by
      -- 加法の第2引数を書き換え
      exact congrArg (fun t => F.ground.card - (1 + t)) hnum
    -- まとめ
    -- まず ground を置換
    have : (traceAt u F).ground.card - numClasses (traceAt u F)
           = (F.ground.card:Int) - (1 + numClasses (traceAt u F)) := by
      -- (a' - b) 形に合わせるため、一旦 (a - 1) に差し替え
      simp
      simp at this
      simp_all
      omega

    -- 安定のため、直接等式連鎖を書かず、ゴールで使う形だけ残す
    -- ここは上の等式連鎖で十分置換できている前提です
    -- 最終形を返す
    -- （もし上の補助がビルド環境で合わなければ、`rw [hground, hnum, Nat.sub_sub]` の列を書いてください）
    rw [this]
    simp_all only [ge_iff_le, Finset.one_le_card, ne_eq, Parallel, traceAt_ground, Finset.card_erase_of_mem, Nat.cast_sub,
    Nat.cast_one]

  -- 右辺
  have R :
      F.ground.card - numClasses F - 1
      = F.ground.card - (numClasses F + 1) := by
    exact Nat.sub_sub _ _ _
  -- 仕上げ
  -- LHS: (a - (1 + b)) - 0 みたいな形に合わせ、最後に `Nat.add_comm`
  -- まず左辺の `excess (traceAt u F)` を L に、右辺 `excess F - 1` を R に置換
  -- その後、`1 + b = b + 1` で一致
  have : (traceAt u F).ground.card - numClasses (traceAt u F)
          = F.ground.card - (numClasses F + 1) := by
    -- L と加法可換律
    have : F.ground.card - (1 + numClasses F)
           = F.ground.card - (numClasses F + 1) :=
      by
        -- `a - (1 + b) = a - (b + 1)`
        -- 右辺の引数を書き換えるだけ
        exact congrArg (fun t => F.ground.card - t) (Nat.add_comm 1 (numClasses F))
    -- L を流し込む
    -- 注意：ここは `calc` で安全に
    have L' :
        (traceAt u F).ground.card - numClasses (traceAt u F)
        = F.ground.card - (1 + numClasses F) := by
      rw [←hnum]
      rw [hground]
      omega

    exact Eq.trans L' this
  -- 最後に excess の定義に戻す
  -- (a - b) - 1 = a - (b + 1)
  calc
    excess (traceAt u F)
        = (traceAt u F).ground.card - numClasses (traceAt u F) := rfl
    _   = F.ground.card - (numClasses F + 1) := this
    _   = (F.ground.card - numClasses F) - 1 := by
            -- 逆向きに `Nat.sub_sub` を使う
            exact Eq.symm (Nat.sub_sub _ _ _)
    _   = excess F - 1 := rfl

/-
/-以下を示す必要はあったのか？-/
lemma ParallelClass_card_trace
  (F : SetFamily α) (u a : α) (ha : a ≠ u) :
  (ParallelClass (traceAt u F) a).card =
    if u ∈ ParallelClass F a then (ParallelClass F a).card - 1
    else (ParallelClass F a).card := by
    sorry
-/

/-同内容の補題あり。
lemma ParallelClass_trace_eq_erase
  (F : SetFamily α) (u w : α) (hw : w ≠ u) :
  ParallelClass (traceAt u F) w
  = (ParallelClass F w).erase u := by
  classical
  -- ext b; それぞれ mem_filter をほどき、(3) と b≠u を使って同値に落とすだけ
  sorry
-/








/-
--条件が弱いかも。uは大きさ2以上の同値類に含まれないといけない。
--上で別の補題を証明できたので消す。
lemma parallel_off_u_preserved_by_trace
  (F : SetFamily α) (u w z : α) (hw : w ≠ u) (hz : z ≠ u) :
  Parallel_edge (traceAt u F) w z ↔ Parallel_edge F w z := by
  classical
  -- どちら側も `trace_filter_eq_image_filter_of_ne` による像の等式に還元
  have Hw :=
    trace_filter_eq_image_filter_of_ne (F := F) (u := u) (w := w) hw
  have Hz :=
    trace_filter_eq_image_filter_of_ne (F := F) (u := u) (w := z) hz
  -- すると、両辺が「同じ像（erase u）」になっているので、
  -- 元のフィルタが等しいことと同値です（Finset.image の両辺へ congrArg）。
  constructor <;> intro h
  · -- → 方向
    -- filter(trace,w) = filter(trace,z) を、両辺を上の補題で書き換え
    -- → image(filter(F,w)) = image(filter(F,z)) → filter(F,w) = filter(F,z)
    --   （`Finset.image` での等式から source が一致することは一般には要りませんが、
    --    ここは両辺とも全く同じ `image (erase u)` への像なので `by cases Hw; cases Hz; simpa` で済みます）
    -- 下は “同じものに書き換えてから等式の両辺を見比べる” だけにしています
    -- （`simp [Parallel_edge]` でも通るはず）
    have := by simpa [Parallel_edge] using h
    -- 書き換え
    simp [Parallel_edge, Hw, Hz]
    ext A
    --ここでAがuを含むかで場合分けしても良いかも。
    rw [Finset.ext_iff] at this
    specialize this A
    simp at this
    constructor
    · intro hA
      rw [@Finset.mem_filter] at hA
      rw [@Finset.mem_filter]
      simp at hA
      have :A ⊆ F.ground.erase u := by exact?
      constructor
      · simp_all only [ne_eq, mem_edgeFinset, and_self]
      ·

      exact hA
    · intro hA
      rw [@Finset.mem_filter] at hA
      rw [@Finset.mem_filter] at hA
      simp at hA
      exact hA
  · -- ← 方向（同様）
    have := by simpa [Parallel_edge] using h
    simpa [Parallel_edge, Hw, Hz] using this

-/
/- excessの方向転換によりコメントアウト
lemma Parallel_trace_iff_of_ne
  {α : Type*} [DecidableEq α]
  (F : SetFamily α) {u a b : α}
  (ha : a ≠ u) (hb : b ≠ u) :
  Parallel (traceAt u F) a b ↔ Parallel F a b := by
  classical
  -- 既存補題を使用
  have himg := edgeFinset_traceAt_eq_image_erase F u
  -- Parallel = sets での集合族一致
  constructor
  · intro h
    ext A
    constructor
    · intro ⟨hAF, haA⟩
      -- trace 側での条件に持ち込むため A.erase を利用
      have : A.erase u ∈ (traceAt u F).edgeFinset := by
        have : A ∈ F.edgeFinset := by
          dsimp [SetFamily.edgeFinset]
          rw [@Finset.mem_filter]
          constructor
          · rw [Finset.mem_powerset]
            exact F.inc_ground hAF
          · exact decide_eq_true hAF

        let fm := Finset.mem_image_of_mem (fun B => B.erase u) this
        simp_all only [ne_eq, Parallel, fm]
      -- Parallel on trace で a↔b が保存
      have := congrArg (fun S => A ∈ S) h
      simp only [Set.mem_setOf_eq] at this
      -- ここを整理して A 側に戻す
      sorry
    · intro ⟨hBF, hbB⟩
      sorry
  · intro h
    -- 逆向きも同様
    sorry

noncomputable def ParallelClass (F : SetFamily α) (a : α) : Finset α :=
  F.ground.filter (fun b => Parallel F a b)

@[simp] lemma mem_ParallelClass
  {α} [DecidableEq α] (F : SetFamily α) (a b : α) :
  b ∈ ParallelClass F a ↔ b ∈ F.ground ∧ Parallel F a b := by
  classical
  -- filter の基本事実
  simp [ParallelClass]

lemma ParallelClass_trace_eq_erase
  {α : Type*} [DecidableEq α]
  (F : SetFamily α) {u a : α} (ha : a ≠ u) :
  ParallelClass (traceAt u F) a = (ParallelClass F a).erase u := by
  classical
  ext b
  constructor
  · intro hb
    rcases Finset.mem_filter.mp hb with ⟨hbG, hpar⟩
    -- ground: traceAt の ground は erase
    have hbIn : b ∈ F.ground.erase u := by simpa [traceAt] using hbG
    rcases Finset.mem_erase.mp hbIn with ⟨hbne, hbG'⟩
    -- 並行性を元の F へ
    have hparF : Parallel F a b :=
      (Parallel_trace_iff_of_ne F ha hbne).1 hpar
    exact Finset.mem_erase.mpr ⟨hbne, Finset.mem_filter.mpr ⟨hbG', hparF⟩⟩
  · intro hb
    rcases Finset.mem_erase.mp hb with ⟨hbne, hbIn⟩
    rcases Finset.mem_filter.mp hbIn with ⟨hbG, hparF⟩
    -- trace 側の ground
    have hbG' : b ∈ (traceAt u F).ground := by
      simpa [traceAt] using Finset.mem_erase.mpr ⟨hbne, hbG⟩
    -- 並行性を trace 側へ
    have hparT : Parallel (traceAt u F) a b :=
      (Parallel_trace_iff_of_ne F ha hbne).2 hparF
    exact Finset.mem_filter.mpr ⟨hbG', hparT⟩
-/

-- 以下の部分は、idealsTraceと融合する必要があり。多分、全部コメントアウト
/-
--FuncSetupを使わない部分
/-- （言明のみ）Lemma 3.5 に対応：
`u` と `v` が Parallel なら，`A ↦ A.erase u` はエッジ集合上で単射。 -/
lemma trace_injective_of_parallel
    (F : SetFamily α) {u v : α} (h : F.Parallel u v) :
    Function.Injective (eraseMap F u) := by
  -- 詳細証明は IdealsTrace で（`mem_edgeFinset_iff` などと併用）
  intro A1 A2 hEq
  -- 将来の証明埋め込みで `simp_all` を活かせるように温存
  sorry

/-- Parallel なら `image (erase u)` に重複が出ない。 -/
--uとvが一致しないという条件がない。Nontrivの条件に統一する方向。
lemma card_image_erase_of_parallel
    (F : SetFamily α) {u v : α} (h : F.Parallel u v) :
    (F.edgeFinset.image (fun A => A.erase u)).card = F.edgeFinset.card := by
  classical
  -- `trace_injective_of_parallel` と `Finset.card_image_iff` で
  sorry

lemma NDS_traceAt_rewrite
    (F : SetFamily α) (u : α)
    (hEdgeImage : (Trace.traceAt u F).edgeFinset = F.edgeFinset.image (fun A => A.erase u))
    (hCardPres : (Trace.traceAt u F).numHyperedges = F.numHyperedges)
    (hGround   : (Trace.traceAt u F).ground = F.ground) :
    (Trace.traceAt u F).NDS
      = 2 * (∑ A ∈ F.edgeFinset, (A.erase u).card : Int)
        - (F.numHyperedges : Int) * (F.ground.card : Int) := by
  -- unfold NDS; rewrite 3つの仮定; `sum_image` の書き換えで完成（詳細は後で）
  sorry
-/

--------


/-ChatGPTの3番-/
lemma erase_on_edges_injective_of_parallel
    (F : SetFamily α) {u v : α}
    (huv : F.Parallel u v) (hne : u ≠ v) :
    Function.Injective
      (fun (A : {A // A ∈ F.edgeFinset}) => (A.1).erase u) := by
  classical
  intro A B h
  -- 目標は A = B（Subype.ext で値の一致を示せば十分）
  apply Subtype.ext
  -- Finset extensionality で要素ごとに同値を示す
  apply Finset.ext
  intro x
  by_cases hx : x = u
  · -- ケース1: x = u のとき，u の所属を比較したい

    -- A,B がエッジであることから sets 証拠を回収
    have hAsets : F.sets A.1 := by
      simp_all only [SetFamily.Parallel, ne_eq]
      obtain ⟨val, property⟩ := A
      obtain ⟨val_1, property_1⟩ := B
      simp_all only
      simp_all only [SetFamily.mem_edgeFinset]

    have hBsets : F.sets B.1 := by
      simp_all only [SetFamily.Parallel, ne_eq]
      obtain ⟨val, property⟩ := A
      obtain ⟨val_1, property_1⟩ := B
      simp_all only
      simp_all only [SetFamily.mem_edgeFinset, and_true]

    -- `A.erase u = B.erase u` から v の所属は一致
    have hv_on_erases :
        (v ∈ A.1.erase u) ↔ (v ∈ B.1.erase u) := by
      constructor <;> intro hv' <;> simpa [h] using hv'
    -- v ≠ u なので，`erase u` で v の所属は不変
    have hvAB : (v ∈ A.1) ↔ (v ∈ B.1) := by
      have hvne : v ≠ u := (ne_comm).1 hne
      simpa [Finset.mem_erase, hvne] using hv_on_erases
    -- Parallel: (u ∈ X) ↔ (v ∈ X) を A,B それぞれで使用し合成
    rw [hx]
    calc
      u ∈ A.1 ↔ v ∈ A.1 := by
        dsimp [SetFamily.Parallel] at huv
        constructor
        · intro hu
          have : A.1 ∈ {A : Finset α | F.sets A ∧ u ∈ A} := by
            exact Set.mem_sep hAsets hu
          subst hx
          simp_all only [ne_eq, Finset.mem_erase, Set.mem_setOf_eq, true_and]
        · intro hv
          have : A.1 ∈ {A : Finset α | F.sets A ∧ v ∈ A} := by
            exact Set.mem_sep hAsets hv
          --subst hx
          have : A.1 ∈ {A : Finset α | F.sets A ∧ u ∈ A} := by
            rw [←huv] at this
            exact this
          rw [Set.mem_setOf_eq] at this
          exact this.2
      _       ↔ v ∈ B.1 := hvAB
      _       ↔ u ∈ B.1 := by
        dsimp [SetFamily.Parallel] at huv
        constructor
        · intro hu
          have : B.1 ∈ {A : Finset α | F.sets A ∧ v ∈ A} := by
            exact Set.mem_sep hBsets hu
          have : B.1 ∈ {A : Finset α | F.sets A ∧ u ∈ A} := by
            rw [←huv] at this
            exact this
          rw [Set.mem_setOf_eq] at this
          exact this.2
        · intro hv
          have : B.1 ∈ {A : Finset α | F.sets A ∧ u ∈ A} := by
            exact Set.mem_sep hBsets hv
          --subst hx
          have : B.1 ∈ {A : Finset α | F.sets A ∧ v ∈ A} := by
            rw [huv] at this
            exact this
          rw [Set.mem_setOf_eq] at this
          exact this.2
  · -- ケース2: x ≠ u のとき，erase の等式からそのまま同値
    have hx_on_erases :
        (x ∈ A.1.erase u) ↔ (x ∈ B.1.erase u) := by
      constructor <;> intro hx' <;> simpa [h] using hx'
    -- x ≠ u なので，`erase u` で x の所属はそのまま
    simpa [Finset.mem_erase, hx] using hx_on_erases

--4番
@[simp] lemma sets_traceAt_iff (F : SetFamily α) (u : α) {B : Finset α} : (traceAt u F).sets B ↔ ∃ A, F.sets A ∧ B = A.erase u := by
  rfl

/-- トレース後のエッジ集合は，元のエッジ集合に `erase u` を施した像と一致。
`parallel` はここでは不要（像集合の同一性）。 -/
lemma edgeFinset_trace_eq_image_erase_of_parallel
    (F : SetFamily α) {u v : α}
    (_ : F.Parallel u v) (_ : u ≠ v) :
    (traceAt u F).edgeFinset = F.edgeFinset.image (fun A => A.erase u) := by
  classical
  -- メンバーシップ同値で両包含を示す
  apply Finset.ext
  intro B
  constructor
  · -- 「→」: B がトレース側のエッジなら，元の何か A の erase になっている
    intro hB
    have hBsets : (traceAt u F).sets B :=
      (mem_edgeFinset_iff_sets (F := traceAt u F) (A := B)).1 hB
    -- トレースの特徴付け：B = A.erase u
    rcases (sets_traceAt_iff (F := F) (u := u) (B := B)).1 hBsets with ⟨A, hA, rfl⟩
    -- 画像の元として書き換え
    exact Finset.mem_image.mpr
      ⟨A, (mem_edgeFinset_iff_sets (F := F) (A := A)).2 hA, rfl⟩
  · -- 「←」: 右辺の像の元なら，トレース側のエッジ
    intro hB
    rcases Finset.mem_image.mp hB with ⟨A, hAedge, hBdef⟩
    have hAsets : F.sets A :=
      (mem_edgeFinset_iff_sets (F := F) (A := A)).1 hAedge
    -- A ∈ F.sets なら (A.erase u) はトレース側のエッジ
    have : (traceAt u F).sets (A.erase u) :=
      (sets_traceAt_iff (F := F) (u := u) (B := A.erase u)).2 ⟨A, hAsets, rfl⟩
    -- edgeFinset への持ち上げ
    simpa [hBdef] using
      (mem_edgeFinset_iff_sets (F := traceAt u F) (A := A.erase u)).2 this

--ChatGPTの5番 どうも証明には必要なかった。
/- 上の二つから，全単射（存在）を明示しておく版。 -/
/-
lemma edges_bijection_exists_of_parallel
    (F : SetFamily α) {u v : α}
    (huv : F.Parallel u v) (hne : u ≠ v) :
    ∃ e : {A // A ∈ F.edgeFinset} ≃ {B // B ∈ (traceAt u F).edgeFinset},
      ∀ A, (e A).1 = (A.1.erase u) := by
  sorry
-/

--ChatGPTの6番
lemma numHyperedges_preserved_of_parallel
    (F : SetFamily α) {u v : α}
    (huv : F.Parallel u v) (hne : u ≠ v) :
    (traceAt u F).numHyperedges = F.numHyperedges := by
  classical
  -- ④: トレース後のエッジは `erase u` の像
  have himg :
      (traceAt u F).edgeFinset
        = F.edgeFinset.image (fun A => A.erase u) :=
    edgeFinset_trace_eq_image_erase_of_parallel (F := F) (u := u) (v := v) huv hne

  -- ③: `A ↦ A.erase u` は `F.edgeFinset` 上で単射
  have hinj_on :
      ∀ A ∈ F.edgeFinset, ∀ B ∈ F.edgeFinset,
        (A.erase u) = (B.erase u) → A = B := by
    intro A hA B hB hEq
    -- サブタイプ版の単射から引き戻す
    have hsub_inj :=
      @erase_on_edges_injective_of_parallel α _ F u v huv hne
    unfold Function.Injective at hsub_inj
    simp_all only [Parallel, ne_eq, mem_edgeFinset, Subtype.forall, Subtype.mk.injEq, and_imp, subset_refl]
    apply hsub_inj
    · simp_all only [subset_refl]
    · simp_all only [subset_refl]
    · simp_all only [subset_refl]
    · simp_all only [subset_refl]
    · simp_all only [subset_refl]

  -- `image` のカードは InjOn なら元と等しい
  have hcard_image :
      (F.edgeFinset.image (fun A => A.erase u)).card
        = F.edgeFinset.card := by
    -- お手元の補題名に応じて差し替えてください：
    -- 例: `Finset.card_image_iff.mpr hinj_on`
    --     または `Finset.card_image_eq_iff.mpr hinj_on`
    --     あるいは `by
    --        refine Finset.card_image_of_injOn ?_;
    --        exact hinj_on`
    -- ここでは `card_image_iff` 風の名前を仮定します。
    simpa using Finset.card_image_iff.mpr hinj_on

  -- 仕上げ：カード等式に書き換え
  simp [numHyperedges, himg, hcard_image]

lemma sum_edge_sizes_split_by_u
    (F : SetFamily α) (u : α) :
    (∑ A ∈ F.edgeFinset, A.card)
      = (∑ A ∈ F.edgeFinset, (A.erase u).card) + F.degree u := by
  classical
  have hpt :
      ∀ A : Finset α,
        A.card = (A.erase u).card + (if u ∈ A then 1 else 0) := by
    intro A; by_cases huA : u ∈ A
    · -- u を含むとき
      -- (A.erase u).card = A.card - 1 を使えば OK
      have : (A.erase u).card = A.card - 1 := by
        simp [huA]

      -- 自然数なので `A.card - 1 + 1 = A.card`
      have hpos : 0 < A.card := by
        exact Finset.card_pos.mpr ⟨u, huA⟩
      -- `Nat.succ_pred_eq_of_pos` を使う形に整える
      -- ここは `simp` で流せることが多いです
      simpa [this, huA] using by
        have := this
        -- 同値変形：A.card = (A.card - 1) + 1
        exact (by
          have := Nat.succ_pred_eq_of_pos hpos
          -- `A.card = Nat.succ (A.card - 1)`
          -- よって `(A.card - 1) + 1 = A.card`
          simpa [Nat.succ_eq_add_one, Nat.add_comm] using this.symm)
    · -- u を含まないとき
      -- (A.erase u).card = A.card, indicator は 0
      simp [huA]
  -- 点ごとの恒等式を和に移す
  have hsum :
      (∑ A ∈ F.edgeFinset, A.card)
        = ∑ A ∈ F.edgeFinset, ((A.erase u).card + (if u ∈ A then 1 else 0)) := by
    refine Finset.sum_congr rfl ?_
    intro A hA; simp [hpt A]
  -- 右辺を分配
  rw [hsum]

  simp [Finset.sum_add_distrib]
  exact Eq.symm (SetFamily.degree_eq_card_filter F u)

/-- 上をトレースのエッジ集合で書き直した版（parallel を使って像に置換）。 -/
lemma sum_edge_sizes_trace_version_of_parallel
    (F : SetFamily α) {u v : α}
    (huv : F.Parallel u v) (hne : u ≠ v) :
    (∑ A ∈ F.edgeFinset, A.card)
      = (∑ B ∈ (traceAt u F).edgeFinset, B.card) + F.degree u := by
  classical
  -- まず、parallel 不要の分解補題
  have hsplit := sum_edge_sizes_split_by_u (F := F) u
  -- ④: トレース後のエッジは `erase u` の像
  have himg :
      (traceAt u F).edgeFinset
        = F.edgeFinset.image (fun A => A.erase u) :=
    edgeFinset_trace_eq_image_erase_of_parallel (F := F) (u := u) (v := v) huv hne
  -- ③ から：`A ↦ A.erase u` が `F.edgeFinset` 上で InjOn
  have hinj_on :
      ∀ A ∈ F.edgeFinset, ∀ B ∈ F.edgeFinset,
        (A.erase u) = (B.erase u) → A = B := by
    intro A hA B hB hEq
    have hsub_inj :=
      @erase_on_edges_injective_of_parallel α _ F u v huv hne
    unfold Function.Injective at hsub_inj
    simp_all only [Parallel, ne_eq, mem_edgeFinset, Subtype.forall, Subtype.mk.injEq, and_imp, subset_refl]
    apply hsub_inj
    · simp_all only [subset_refl]
    · simp_all only [subset_refl]
    · simp_all only [subset_refl]
    · simp_all only [subset_refl]
    · simp_all only [subset_refl]

  -- `sum_image` で `∑ (A.erase u).card` を像側の和へ
  have hsum_image :
      (∑ A ∈ F.edgeFinset, (A.erase u).card)
        = (∑ B ∈ (F.edgeFinset.image (fun A => A.erase u)), B.card) := by
    -- `sum_image` は像側=元側 の向きなので `symm` を付けない形で書く
    -- sum_image : (InjOn f s) → ∑ x in s.image f, g x = ∑ x in s, g (f x)
    -- ここでは g := Finset.card
    exact Eq.symm (Finset.sum_image hinj_on)

  -- 仕上げ：置換して等式完成
  calc
    (∑ A ∈ F.edgeFinset, A.card)
        = (∑ A ∈ F.edgeFinset, (A.erase u).card) + F.degree u := hsplit
    _   = (∑ B ∈ (F.edgeFinset.image (fun A => A.erase u)), B.card) + F.degree u := by
            simp [hsum_image]
    _   = (∑ B ∈ (traceAt u F).edgeFinset, B.card) + F.degree u := by
            simp [himg]


/-- 目標：NDS の等式（版B）。
  `NDS(F) = 2 * Σ|A| - |E(F)| * |ground|` を使う。
  仮定：`u` は ground に属し，`v` は `u` の parallel パートナー。 -/
lemma NDS_eq_of_parallel
    (F : SetFamily α) {u v : α}
    (huv : F.Parallel u v) (hne : u ≠ v) (hu : u ∈ F.ground):
    F.NDS = (traceAt u F).NDS + 2 * (F.degree u : Int) - (F.numHyperedges : Int) := by
classical
  -- ⑧（Nat）を Int に持ち上げる：
  have hsum_nat :
      (∑ A ∈ F.edgeFinset, A.card)
        = (∑ B ∈ (traceAt u F).edgeFinset, B.card) + F.degree u :=
    sum_edge_sizes_trace_version_of_parallel (F := F) (u := u) (v := v) huv hne
  have hsum_int :
      (∑ A ∈ F.edgeFinset, (A.card : Int))
        = (∑ B ∈ (traceAt u F).edgeFinset, (B.card : Int))
          + (F.degree u : Int) := by
    -- Nat 等式を Int にキャスト
    have := congrArg (fun n : ℕ => (n : Int)) hsum_nat
    -- 和・加法の `Nat.cast` を展開
    simpa [Nat.cast_sum, Nat.cast_add] using this

  -- ⑥：辺数保存（Nat → Int）
  have hE_nat :
      (traceAt u F).numHyperedges = F.numHyperedges :=
    numHyperedges_preserved_of_parallel (F := F) (u := u) (v := v) huv hne
  have hE_int :
      ((traceAt u F).numHyperedges : Int) = (F.numHyperedges : Int) := by
    simpa using congrArg (fun n : ℕ => (n : Int)) hE_nat

  -- ground のサイズ：`u ∈ ground` より `|V(trace)| = |V| - 1`
  have hV_nat :
      (traceAt u F).ground.card = F.ground.card - 1 :=
    ground_card_trace_of_mem (F := F) hu
  -- そこから `|V| - |V(trace)| = 1` の Int 版を作る
  have hV_pos : 0 < F.ground.card := Finset.card_pos.mpr ⟨u, hu⟩
  have hsucc :
      (traceAt u F).ground.card + 1 = F.ground.card := by
    -- `Nat.succ (F.ground.card - 1) = F.ground.card`
    -- と `hV_nat` からの置換
    simp
    let nc := (Nat.succ_pred_eq_of_pos hV_pos)
    simp_all only [Parallel, ne_eq, traceAt_ground, Finset.card_erase_of_mem]
    exact nc


  have hV_int_eq :
      (F.ground.card : Int) = ((traceAt u F).ground.card : Int) + 1 := by
    have := congrArg (fun n : ℕ => (n : Int)) hsucc
    simp
    exact id (Eq.symm this)


  -- 本体計算
  -- 版Bの定義で `NDS(F)` と `NDS(trace)` を展開してから整理
  calc
    F.NDS
        = 2 * (∑ A ∈ F.edgeFinset, (A.card : Int))
            - (F.numHyperedges : Int) * (F.ground.card : Int) := by
            let nd := NDS_def F
            rw [nd]
            dsimp [SetFamily.totalHyperedgeSize]
            simp_all only [Parallel, ne_eq, traceAt_ground, Finset.card_erase_of_mem, Finset.card_pos, Finset.one_le_card,
               Nat.sub_add_cancel, Nat.cast_sub, Nat.cast_one, sub_add_cancel, Nat.cast_add, Nat.cast_sum]
    _   = 2 * ( (∑ B ∈ (traceAt u F).edgeFinset, (B.card : Int))
                + (F.degree u : Int))
            - ((traceAt u F).numHyperedges : Int) * (((traceAt u F).ground.card : Int) + 1) := by
            -- sums を ⑧ で置換、|E| と |V| を ⑥ と hV_int_eq で置換
            simp [hsum_int, hE_int, hV_int_eq]

    _   = (2 * (∑ B ∈ (traceAt u F).edgeFinset, (B.card : Int))
            - ((traceAt u F).numHyperedges : Int) * ((traceAt u F).ground.card : Int))
          + (2 * (F.degree u : Int) - ((traceAt u F).numHyperedges : Int)) := by
            -- 分配して `(a+b) - (c*(d+1)) = (2a - c*d) + (2b - c)`
            -- 詳細：`2*(X+D) = 2X + 2D`、`E*(G+1) = E*G + E`
            -- その後 `(x + y) - (p + q) = (x - p) + (y - q)`
            have : 2 * ((∑ B ∈ (traceAt u F).edgeFinset, (B.card : Int))
                        + (F.degree u : Int))
                    = 2 * (∑ B ∈ (traceAt u F).edgeFinset, (B.card : Int))
                      + 2 * (F.degree u : Int) := by
              simp [two_mul, mul_add, add_comm, add_assoc]
            have : ((traceAt u F).numHyperedges : Int)
                      * (((traceAt u F).ground.card : Int) + 1)
                    = ((traceAt u F).numHyperedges : Int)
                        * ((traceAt u F).ground.card : Int)
                      + ((traceAt u F).numHyperedges : Int) := by
              simp [mul_add, add_comm]
            -- まとめて変形
            -- `simp` で `sub_eq_add_neg` を使って並べ替える
            simp [two_mul, mul_add, add_comm, add_left_comm, add_assoc,
                   sub_eq_add_neg]
    _   = (traceAt u F).NDS + (2 * (F.degree u : Int) - (F.numHyperedges : Int)) := by
            -- 版Bの `trace` 定義へ戻す＋辺数は ⑥ で置換
            simp [ hE_int]
            dsimp [SetFamily.totalHyperedgeSize]
            exact Eq.symm (Nat.cast_sum (traceAt u F).edgeFinset Finset.card)
  exact add_sub_assoc' (traceAt u F).NDS (2 * ↑(F.degree u)) ↑F.numHyperedges

end Trace

end AvgRare

/- トレース後の「`B` がトレース族のメンバである」ことの便利な再表現。 -/
--lemma mem_traceAt_iff {x : α} {F : SetFamily α} {B : Finset α} :
--    (traceAt x F).sets B ↔ ∃ A, F.sets A ∧ B ⊆ A.erase x ∧ B ⊆ F.ground.erase x := by

/- 1点トレースの ground 包含（再掲）。 -/
/-
lemma subset_ground_of_mem_trace {x : α} {F : SetFamily α} {B : Finset α}
    (hB : (traceAt x F).sets B) :
    B ⊆ (traceAt x F).ground := by
  classical
  rcases (mem_traceAt_iff).1 hB with ⟨A, hA, hBsub, hBsubU⟩
  -- 定義どおり
  simpa using hBsubU
-/

/- 小補助：`A ⊆ F.ground` なら `A.erase x ⊆ F.ground.erase x`。 -/
/-
lemma erase_subset_erase_of_subset {x : α} {F : SetFamily α} {A : Finset α}
    (hA : A ⊆ F.ground) :
    A.erase x ⊆ F.ground.erase x := by
  intro a ha
  have : a ∈ A ∧ a ≠ x := by
    -- `Finset.mem_erase` の逆向き
    simp_all only [Finset.mem_erase, ne_eq, not_false_eq_true, and_self]
  have haA : a ∈ A := this.1
  have hne : a ≠ x := this.2
  have haU : a ∈ F.ground := hA haA
  -- `mem_erase` の順向き
  exact by
    -- a ∈ ground ∧ a ≠ x から a ∈ ground.erase x
    have : a ∈ F.ground.erase x := by
      -- `Finset.mem_erase` ⇔ (a ≠ x ∧ a ∈ ground)
      have := (show a ≠ x ∧ a ∈ F.ground from And.intro hne haU)
      -- 書き換え
      simpa [Finset.mem_erase, And.comm] using this
    exact this
-/

/-
noncomputable def traceErase (x : α) (F : SetFamily α) : SetFamily α := by
  classical
  refine
  { ground := F.ground.erase x
    , sets := fun B => ∃ A, F.sets A ∧ B = A.erase x
    , decSets := Classical.decPred _
    , inc_ground := ?_ }
  intro B hB
  rcases hB with ⟨A, hA, rfl⟩
  -- A ⊆ ground → A.erase x ⊆ ground.erase x
  exact (erase_subset_erase_of_subset (F := F) (A := A) (F.inc_ground hA))
-/

/- 像だけ版の edge 列挙：`edgeFinset = image (erase x)`。 -/
/-
lemma edgeFinset_traceErase (x : α) (F : SetFamily α) :
    (traceErase x F).edgeFinset
      = F.edgeFinset.image (fun A => A.erase x) := by
  classical
  -- ここは後で埋める（`mem_edgeFinset_iff` と `Finset.image` の往復）
  sorry
-/


/-
必要になったときに拡張しやすいよう、Trace とは独立の小道具をここに置いておけます
（例えば Equiv による ground の付け替え等）。現状は最小限に留めています。
-/


/-
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import AvgRare.Basics.SetFamily
import AvgRare.SPO.FuncSetup

universe u

namespace AvgRare
namespace Basics
namespace Trace
open scoped BigOperators

variable {α : Type u} [DecidableEq α]

/-- `A : Finset α` を同値関係 `E` の商に写した像。 -/
noncomputable def imageQuot (E : Setoid α) (A : Finset α) : Finset (Quot E) := by
  classical
  exact A.image (fun a => Quot.mk _ a)

@[simp]
lemma mem_imageQuot {E : Setoid α} {A : Finset α} {q : Quot E} :
    q ∈ imageQuot E A ↔ ∃ a ∈ A, Quot.mk _ a = q := by
  classical
  simp [imageQuot]

lemma imageQuot_mono {E : Setoid α} {A B : Finset α} (h : A ⊆ B) :
    imageQuot E A ⊆ imageQuot E B := by
  classical
  intro q hq
  rcases (mem_imageQuot (E:=E) (A:=A)).1 hq with ⟨a, haA, rfl⟩
  exact (mem_imageQuot (E:=E) (A:=B)).2 ⟨a, h haA, rfl⟩

--section
variable (E : Setoid α)
-- ★ ここで型レベルにインスタンスを用意しておく
noncomputable local instance : DecidableEq (Quot E) := Classical.decEq _

/-- `trace E F`：各超辺の商像を取り、その **下閉包** で得た集合族。 -/
noncomputable def trace (E : Setoid α) (F : SetFamily α) : SetFamily (Quot E) := by
  classical
  refine
  { ground := imageQuot E F.ground
    sets   := fun B => ∃ A : Finset α, F.sets A ∧ B ⊆ imageQuot E A
    decSets := Classical.decPred _
    inc_ground := ?_ }

  intro B hB
  rcases hB with ⟨A, hA, hsub⟩
  have hAg : A ⊆ F.ground := F.inc_ground hA
  have him : imageQuot E A ⊆ imageQuot E F.ground :=
    imageQuot_mono (E:=E) hAg
  exact hsub.trans him

/-- E ≤ E' ：E が E' より細かい（E の同値は E' の同値でもある） -/
def refines (E E' : Setoid α) : Prop :=
  ∀ ⦃a b : α⦄, E.r a b → E'.r a b

/-- refinement から商への写像 `Quot E → Quot E'` -/
noncomputable def liftQuot {E E' : Setoid α} (h : refines E E') :
  Quot E → Quot E' :=
  Quot.map (fun x => x) (by intro a b hab; exact h hab)

@[simp] lemma liftQuot_mk {E E' : Setoid α} (h : refines E E') (a : α) :
  liftQuot (E:=E) (E':=E') h (Quot.mk _ a) = Quot.mk _ a := rfl

/-- `imageQuot` を粗い同値に取り直すと、持ち上げ写像で包含が成り立つ。 -/
lemma imageQuot_mono_under_refines
  {E E' : Setoid α} (h : refines E E') (A : Finset α) :
  (A.image (fun a => Quot.mk E a)).image (liftQuot (E:=E) (E':=E') h)
    ⊆ A.image (fun a => Quot.mk E' a) := by
  classical
  intro q hq
  rcases Finset.mem_image.1 hq with ⟨q0, hq0, rfl⟩
  rcases Finset.mem_image.1 hq0 with ⟨a, haA, rfl⟩
  -- 右辺に同じ代表 a で入る
  exact Finset.mem_image.2 ⟨a, haA, rfl⟩

/-- **trace の単調性（Setoid を粗くすると大きくなる）**
`E ≤ E'`（E が細かい）なら、`trace E F` の各超辺像を `Quot E → Quot E'` に移せば `trace E' F` の超辺に含まれる。 -/
lemma trace_mono_in_setoid
  (E E' : Setoid α) (F : SetFamily α) (h : refines E E') :
  ∀ {B : Finset (Quot E)},
    (trace E F).sets B →
    ∃ B' : Finset (Quot E'),
      (trace E' F).sets B' ∧
      B.image (liftQuot (E:=E) (E':=E') h) ⊆ B' := by
  classical
  intro B hB
  -- 定義展開：B ⊆ imageQuot E A
  rcases hB with ⟨A, hAsets, hBsub⟩
  refine ⟨A.image (fun a => Quot.mk E' a), ?_, ?_⟩
  · -- `trace E' F` のメンバー
    refine ⟨A, hAsets, ?_⟩
    -- `imageQuot E' A` に対しては自明な包含
    intro q hq
    exact hq
  · -- B を `liftQuot` で写すと、`imageQuot E' A` に入る
    -- すなわち B.image (liftQuot h) ⊆ (imageQuot E' A)
    -- まず B ⊆ imageQuot E A を使って、像に押し出す
    intro q hq
    rcases Finset.mem_image.1 hq with ⟨q0, hq0, rfl⟩
    have : q0 ∈ A.image (fun a => Quot.mk E a) := hBsub hq0
    -- ここで `imageQuot_mono_under_refines` で E→E' に移す
    have step :=
      imageQuot_mono_under_refines (E:=E) (E':=E') h (A := A)
    -- step : (imageQuot E A).image (liftQuot h) ⊆ imageQuot E' A
    exact step (by
      -- q0 を像に入れてから lift して得る要素は右辺に含まれる
      exact Finset.mem_image.2 ⟨q0, this, rfl⟩)


noncomputable def restrict {α} [DecidableEq α]
    (F : SetFamily α) (U : Finset α) : SetFamily α := by
  classical
  refine
  { ground := U
    , sets := fun B => ∃ A : Finset α, F.sets A ∧ B ⊆ A ∧ B ⊆ U
    , decSets := Classical.decPred _
    , inc_ground := ?_ }
  intro B hB
  rcases hB with ⟨A, hA, hBsubA, hBsubU⟩
  exact hBsubU

@[simp] lemma mem_restrict_iff {α} [DecidableEq α]
    {F : SetFamily α} {U B : Finset α} :
    (restrict F U).sets B ↔ ∃ A, F.sets A ∧ B ⊆ A ∧ B ⊆ U := Iff.rfl

lemma isOrderIdeal_erase_on_restrict
  {α} [DecidableEq α] (S : FuncSetup α)
  (A : Finset S.Elem) (hA : S.isOrderIdeal A) (u : S.Elem) :
  (S.restrict (S.V.erase u)).isOrderIdeal (A.erase u) := by
  intro x y hy hx
  -- `x y : (S.restrict ...).Elem` だと思って使えるように、必要なら `Subtype` の `val` 展開
  -- `hy : y ≤ x` は制限順序の比較。基の順序の比較に戻してから `hA` に投げる。
  rcases Finset.mem_erase.mp hx with ⟨hx_ne, hxA⟩
  have hyA : (y : S.Elem) ∈ A := hA (by simpa using hy) hxA
  -- 結論は `x ∈ A.erase u`：
  apply Finset.mem_erase.mpr
  constructor
  · -- x ≠ u
    -- x = u なら u ≤ y だが y は `A` に居るので、`A.erase u` の仮定と矛盾、の形で弾く
    intro hxu; subst hxu
    -- `u ≤ y` だが `y ∈ A` なので `u ∈ A`（下方閉）。しかし `hx` は x≠u を言っていた…という整理。
    -- ここは環境の順序補題（反射・推移）に合わせて書き分け。
    have : (u : S.Elem) ∈ A := hA (by simpa using hy) hxA
    exact hx_ne this.symm
  · -- x ∈ A
    exact hA (by simpa using hy) hxA


/-- 記法：`𝓕 ↘ U` を `restrict 𝓕 U` の糖衣として定義。 -/
notation:90 F "↘" U => AvgRare.Basics.Trace.restrict F U

@[simp] lemma imageQuot_eq_image {E : Setoid α} (A : Finset α) :
  imageQuot E A = A.image (fun a => Quot.mk _ a) := rfl

@[simp] lemma mem_imageQuot_iff {E : Setoid α} {A : Finset α} {q : Quot E} :
  q ∈ imageQuot E A ↔ ∃ a ∈ A, Quot.mk _ a = q :=
by classical simp [imageQuot]

/-- 画像の画像：`imageQuot E A` の各要素を恒等的に lift する形の `image` は `imageQuot` の交換で吸収できる -/
lemma image_imageQuot_lift {E E' : Setoid α} (h : refines E E') (A : Finset α) :
  (imageQuot E A).image (liftQuot (E:=E) (E':=E') h)
    ⊆ imageQuot E' A := by
  classical
  -- 既存の `imageQuot_mono_under_refines` の言い換え
  have := imageQuot_mono_under_refines (E:=E) (E':=E') h (A:=A)
  -- 使っている定義の向きを合わせるだけ
  simpa [imageQuot_eq_image] using this

end Trace
end Basics
end AvgRare


-/
