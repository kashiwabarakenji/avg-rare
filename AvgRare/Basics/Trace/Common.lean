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

@[simp] lemma sets_traceAt_iff (F : SetFamily α) (u : α) {B : Finset α} : (traceAt u F).sets B ↔ ∃ A, F.sets A ∧ B = A.erase u := by
  rfl
--traceした時のhyperedgeがどうなるかの補題。数が減らないこともこれでわかるのかも。
--uにパラレルな要素を仮定してない。両辺一致はするが、両方とも数が減っているかもしれないということか。
--使っていたところをコメントアウトしたので現状使ってない。
--traceしても同値類の大きさが変わらないというところに使うので、Common.leanに移動。
lemma edgeFinset_traceAt_eq_image_erase (F : SetFamily α) (u : α) :
  (traceAt u F).edgeFinset = F.edgeFinset.image (fun A => A.erase u) := by
  classical
  ext B; constructor
  · intro hB
    have hSets : (traceAt u F).sets B :=
      (SetFamily.mem_edgeFinset_iff_sets (F := traceAt u F) (A := B)).1 hB
    rcases (sets_traceAt_iff (F := F) (u := u) (B := B)).1 hSets with ⟨A, hA, rfl⟩
    exact Finset.mem_image.mpr
      ⟨A, (SetFamily.mem_edgeFinset_iff_sets (F := F) (A := A)).2 hA, rfl⟩
  · intro hB
    rcases Finset.mem_image.mp hB with ⟨A, hAedge, rfl⟩
    have hAsets : F.sets A :=
      (SetFamily.mem_edgeFinset_iff_sets (F := F) (A := A)).1 hAedge
    have hTrace : (traceAt u F).sets (A.erase u) :=
      (sets_traceAt_iff (F := F) (u := u) (B := A.erase u)).2 ⟨A, hAsets, rfl⟩
    exact (SetFamily.mem_edgeFinset_iff_sets (F := traceAt u F) (A := A.erase u)).2 hTrace

/-オリジナル証明
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
-/

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



--trace関係あり
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

--Intで定義した方が計算が楽？
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
