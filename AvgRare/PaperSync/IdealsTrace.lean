import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.Order.GroupWithZero.Unbundled.Defs
import AvgRare.Basics.SetFamily
import AvgRare.Basics.Ideals
import AvgRare.SPO.FuncSetup
import AvgRare.SPO.TraceFunctional
import AvgRare.Basics.Trace.Common   -- Trace.traceAt / Trace.Parallel / Trace.eraseMap
import LeanCopilot

/-
IdealsTrace.lean — 「functional preorder × ideals × trace」の結合層（論文 §3）

このファイルは、SPO.FuncSetup で与えた機能的前順序 S の上で
- S から ground 上の二項関係 `leOn` を作る
- その order-ideal family を `idealFamily S` として `SetFamily α` に落とす
- 論文 §3 の Lemma 3.1（maximal ⇒ rare）, 3.3（∼ ⇔ parallel）, 3.5（trace 単射）,
  3.6（trace 後も functional, NDS は増えない）の**言明**を置く

重い証明は `sorry` のまま残し、他ファイルから参照可能な API を確定させます。
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

--variable (S : FuncSetup α) (x y : S.Elem)
--variable (S : FuncSetup α) [DecidableRel (S.le)]
noncomputable def Iy (S : FuncSetup α) (y : S.Elem) : Finset S.Elem :=
  S.ground.attach.filter (fun z : S.Elem => S.le z y)

-- 目標： hb : b ∈ S.ground, hleOn : S.leOn b a, haGround : a ∈ S.coeFinset Iy
--       から b ∈ S.coeFinset Iy を出す
--xとyに大小関係があれば、yを含むidealは、xも含む。重要補題。
--基礎補題を集めたファイルを作って分離してもよい。
lemma le_iff_forall_ideal_mem
  (S : FuncSetup α) (x y : S.Elem) :
  S.le x y ↔
    (∀ I : Finset S.Elem,
      (S.idealFamily).sets (S.coeFinset I) → y ∈ I → x ∈ I) := by
  constructor
  · -- (→) : `x ≤ y` なら、任意のイデアル I で `y ∈ I → x ∈ I`
    intro hxy I hI hyI
    -- イデアルの定義は α 上の order-ideal なので、`coeFinset I` に持ち上げる
    have hIdeal :
        isOrderIdealOn (S.leOn) S.ground (S.coeFinset I) :=
      (S.sets_iff_isOrderIdeal).1 hI
    -- y ∈ I から y.1 ∈ coeFinset I
    have hy' : (y.1 : α) ∈ S.coeFinset I := by

      exact (S.mem_coeFinset_iff (I:=I) (a:=y.1) (ha:=y.2)).2 hyI
    -- order-ideal のダウンワード閉包で x.1 ∈ coeFinset I を得る
    have hx' : (x.1 : α) ∈ S.coeFinset I := by
      -- `S.leOn` は α 上の関係。`x y : S.Elem` からは `S.leOn x.1 y.1`
      have hleOn : S.leOn x.1 y.1 := by exact (S.le_iff_leOn_val x y).mp hxy--S.le_to_leOn hxy
      simp_all only [ FuncSetup.mem_coeFinset, Subtype.exists, exists_and_right,
         exists_eq_right, Subtype.coe_eta, Finset.coe_mem, exists_const]
      exact S.mem_of_le_of_mem_inIdeal hIdeal hleOn  hyI

    -- もう一度 subtype に戻す
    simp_all only [FuncSetup.mem_coeFinset, Subtype.exists, exists_and_right,
    exists_eq_right, Subtype.coe_eta, Finset.coe_mem, exists_const]

  · -- (←) : 逆向き。`Iy` を y 以下の元の集合として取る
    intro hAll
    -- `Iy := { z ∈ ground | z ≤ y }` を Finset S.Elem で
    let Iy : Finset S.Elem :=
      S.ground.attach.filter (fun z => S.le z y)
    have hyIy : y ∈ Iy := by
      -- y は ground にあり、かつ y ≤ y
      have hy₀ : y ∈ S.ground.attach := by
        exact Finset.mem_attach S.ground y
      have : S.le y y := S.le_refl y
      simpa [Iy] using Finset.mem_filter.mpr ⟨hy₀, this⟩
    -- `S.coeFinset Iy` は α 上のイデアルであることを示す
    have hIy_sets : (S.idealFamily).sets (S.coeFinset Iy) := by
      -- isOrderIdealOn へ落とす（あなたの `sets_iff_isOrderIdeal` を利用）
      have : isOrderIdealOn (S.leOn) S.ground (S.coeFinset Iy) := by
        -- ⟨downward_closed, subset_ground⟩ を And で与える
        refine And.intro ?dc ?subset
        · -- ?dc : downward closed
          -- 目標: ∀ a ∈ ground, ∀ b, S.leOn b a → a ∈ S.coeFinset Iy → b ∈ S.coeFinset Iy
          simp_all only [Finset.mem_filter, Finset.mem_attach, true_and, Iy]
          intro z hz
          simp_all only [FuncSetup.mem_coeFinset, Finset.mem_filter, Finset.mem_attach, true_and, Subtype.exists,
            ]
          simp_all only [FuncSetup.le_iff_leOn_val, FuncSetup.sets_iff_isOrderIdeal, exists_and_left, exists_prop,
            exists_eq_right_right]
        · -- ?subset : S.coeFinset Iy ⊆ S.ground
          intro a haIn
          -- a ∈ coeFinset Iy から代表元 z を取り出す
          rcases (S.mem_coeFinset_val_iff).1 haIn with ⟨z, hzIy, hz⟩
          -- フィルタ左成分から z ∈ ground.attach
          have hzInAttach : z ∈ S.ground.attach :=
            (Finset.mem_filter).1 hzIy |>.left
          -- attach から ground へ
          have hzGround : z.1 ∈ S.ground := by
            subst hz
            simp_all only [ Finset.mem_filter, Finset.mem_attach, true_and,
              FuncSetup.mem_coeFinset, Subtype.exists, Finset.coe_mem, Iy]

          -- ので a ∈ ground
          -- `rw [hz]` を使わず等式で置換してもOK
          have : a ∈ S.ground := by
            -- a = z.1
            -- `subst` でも良い
            -- `convert hzGround using 1; exact hz.symm`
            exact Eq.ndrec hzGround hz

          intro y_1 a_1 a_2
          subst hz
          simp_all only [Finset.mem_attach, FuncSetup.mem_coeFinset, Subtype.exists, Finset.coe_mem,Iy]
          simp_all
          apply S.leOn_trans
          exact a_2
          exact hzIy
          -- 目標は b ∈ S.coeFinset Iy なので、存在証明で入れる
      simp_all only [Finset.mem_filter, Finset.mem_attach, true_and, Iy]
      exact this

    -- 仮定 `hAll` を Iy に適用すると x ∈ Iy
    have hxIy : x ∈ Iy := hAll Iy hIy_sets hyIy
    -- 以上より `x ≤ y` が従う
    have hxLe : S.le x y := (Finset.mem_filter.mp hxIy).2
    exact hxLe


/-- 論文 Lemma 3.3：
`u, v` が同じ同値類（S.sim）であることと，`idealFamily S` における parallel が同値。 -/
--この関係はfunctionalでなくても成り立つはずであるがここではfunctionalなものに対して証明している。
lemma parallel_iff_sim
  (S : FuncSetup α) (u v : S.Elem) :
  (S.idealFamily).Parallel u v ↔ FuncSetup.sim S u v := by
  constructor
  · intro hPar
    -- (∀ I, sets (coeFinset I) → (u∈I ↔ v∈I)) に言い換える

    have hUV :
      ∀ I : Finset S.Elem,
        (S.idealFamily).sets (S.coeFinset I) →
        (u ∈ I ↔ v ∈ I) := by
      dsimp [SetFamily.Parallel, FuncSetup.coeFinset] at *
      intro I hI
      constructor
      · intro hu
        have : (Finset.image (fun x => ↑x) I) ∈ {A | S.idealFamily.sets A ∧ ↑u ∈ A} :=
        by
          rw [@Set.mem_setOf_eq]
          constructor
          · exact hI
          · simp_all only [ Finset.mem_image, Subtype.exists, exists_and_right, exists_eq_right,
            Subtype.coe_eta, Finset.coe_mem, exists_const]
        simp_all only [ Set.mem_setOf_eq, Finset.mem_image, Subtype.exists, exists_and_right,
          exists_eq_right, Subtype.coe_eta, Finset.coe_mem, exists_const, true_and]
      · intro hv
        have : (Finset.image (fun x => ↑x) I) ∈ {A | S.idealFamily.sets A ∧ ↑v ∈ A} :=
        by
          rw [@Set.mem_setOf_eq]
          constructor
          · exact hI
          · simp_all only [Finset.mem_image, Subtype.exists, exists_and_right, exists_eq_right,
            Subtype.coe_eta, Finset.coe_mem, exists_const]
        rw [←hPar] at this
        rw [Set.mem_setOf_eq] at this
        simp_all only [Finset.mem_image, Subtype.exists, exists_and_right, exists_eq_right,
          Subtype.coe_eta, Finset.coe_mem, exists_const]

    -- 右向きに le_iff を使って S.le u v

    have huv : S.le u v := by
      let lifim := (le_iff_forall_ideal_mem S u v).mpr
      apply lifim
      intro I a a_1
      simp_all only [SetFamily.Parallel]

    -- 左向きに le_iff を使って S.le v u
    have hvu : S.le v u := by
      let lifim := (le_iff_forall_ideal_mem S v u).mpr
      apply lifim
      intro I a a_1
      simp_all only [SetFamily.Parallel]
    dsimp [FuncSetup.sim]
    exact ⟨huv, hvu⟩

  · intro hSim
    -- `le_iff_forall_ideal_mem` を左右に使って各 ideal での会員同値を出す
    rcases hSim with ⟨huv, hvu⟩
    dsimp [SetFamily.Parallel] at *
    ext J

    constructor
    swap
    · intro hu

      rw [@Set.mem_setOf_eq]
      rw [@Set.mem_setOf_eq] at hu
      constructor
      · exact hu.1
      · have : J ⊆ S.ground := by
          exact S.idealFamily.inc_ground hu.1

        let lifim := (le_iff_forall_ideal_mem S u v).mp huv (S.liftFinset J this)
        rw [S.coeFinset_liftFinset] at lifim
        specialize lifim hu.1
        simp_all only [FuncSetup.le_iff_leOn_val, FuncSetup.sets_iff_isOrderIdeal, FuncSetup.mem_liftFinset_iff, forall_const]

    · intro hv
      -- 対称に同様
      rw [@Set.mem_setOf_eq]
      rw [@Set.mem_setOf_eq] at hv
      constructor
      · exact hv.1
      · have : J ⊆ S.ground := by
          exact S.idealFamily.inc_ground hv.1

        let lifim := (le_iff_forall_ideal_mem S v u).mp hvu (S.liftFinset J this)
        rw [S.coeFinset_liftFinset] at lifim
        specialize lifim hv.1
        simp_all only [FuncSetup.le_iff_leOn_val, FuncSetup.sets_iff_isOrderIdeal, FuncSetup.mem_liftFinset_iff, forall_const]

--パラレルな元であれば、uからxにいければxからuにいける。
--極大性は使ってない。parallel_iff_simは使う立場。
--nontrivialClassの仮定を使って書き換えられそう。
--nds_monotone_under_traceで利用されている。
--この言明には、functionalという仮定が必要。
lemma maximal_of_parallel_nontrivial
    (S : SPO.FuncSetup α) {u v : α}
    (hu : u ∈ S.ground) (hv : v ∈ S.ground)
    (hpar : (S.idealFamily).Parallel u v)
    (hneq : u ≠ v) :
    ∀ x : S.Elem,
      Relation.ReflTransGen (stepRel S.f) (S.toElem! hu) x →
      Relation.ReflTransGen (stepRel S.f) x (S.toElem! hu) := by
  -- ① parallel ⇒ sim
  have hsim : SPO.FuncSetup.sim S (S.toElem! hu) (S.toElem! hv) := by
    -- `parallel_iff_sim` の → 方向
    have hiff := parallel_iff_sim (S:=S) (u:=S.toElem! hu) (v:=S.toElem! hv)
    exact (parallel_iff_sim S (S.toElem! hu) (S.toElem! hv)).mp hpar

  -- ② sim ⇒ 互いに到達可能（= `S.le` が両向き）
  --    ここはあなたの sim の定義／補題に合わせて置換してください。
  --    例：`sim_iff` や `le_of_sim_left/right` 等。
  have hle_uv : S.le (S.toElem! hu) (S.toElem! hv) ∧ S.le (S.toElem! hv) (S.toElem! hu) := by
    -- 代表例：`sim_iff` がある場合
    -- exact (SPO.FuncSetup.sim_iff (S:=S) (a:=S.toElem! hu) (b:=S.toElem! hv)).1 hsim
    -- もしくは片側ずつ取り出す補題があるならそれで OK
    simp_all only [SetFamily.Parallel, ne_eq]
    exact hsim

  -- ③ `S.le` を `ReflTransGen (stepRel S.fV)` に落とす
  --    （`S.le` の定義が「被覆の反射推移閉包」なら `Iff.rfl`/既存のブリッジ補題で変換できます）
  have huv :
      Relation.ReflTransGen (stepRel S.f) (S.toElem! hu) (S.toElem! hv) ∧
      Relation.ReflTransGen (stepRel S.f) (S.toElem! hv) (S.toElem! hu) := by
    -- 代表例：`S.le` の定義が `Relation.ReflTransGen S.cover` で `S.cover = stepRel S.fV`
    -- ならそれぞれ定義展開で終わりです。環境のブリッジ補題名に置換してください。
    -- 例：`(reach_eq_reflTrans (S:=S) _ _).1/2` など
    -- 左向き
    have h1 := hle_uv.1
    -- 右向き
    have h2 := hle_uv.2
    -- ここで h1, h2 を `ReflTransGen (stepRel S.fV)` へ移す
    -- 置換例：
    -- exact ⟨(by exact h1), (by exact h2)⟩
    simp_all only [SetFamily.Parallel, ne_eq, and_self]
    exact hsim

  -- ④ `u ≠ v` をサブタイプでも非自明に
  have hneq' : (S.toElem! hu) ≠ (S.toElem! hv) := by
    intro h
    -- 値写像で矛盾
    have : u = v := congrArg Subtype.val h
    exact hneq this

  -- ⑤ あなたの補題を適用（`α := S.Elem, f := S.fV`）
  have hmax :=
    maximal_of_nontrivialClass_lemma
      (α := S.Elem) (f := S.f)
      (u := S.toElem! hu) (v := S.toElem! hv)
      huv hneq'

  -- ⑥ 仕上げ：任意の x に対して戻す
  intro x hx
  exact hmax x hx
------------------------




/- =====================================================
   2) sim ↔ Parallel（既存）を α レベルに渡すための型合わせ
   ===================================================== -/

-- 既存: parallel_iff_sim (S : FuncSetup α) (u v : S.Elem)
-- をそのまま使い、必要なら underlying へ落とすだけ。
lemma parallel_of_sim_coe (S : FuncSetup α) {x y : S.Elem}
    (h : FuncSetup.sim S x y) :
    (S.idealFamily).Parallel (x : α) (y : α) := by
  -- `Parallel` の引数が α のとき、`x y : S.Elem` は自動で coercion されます。
  -- 既存の `parallel_iff_sim` を使うだけで OK。
  have hxy : (S.idealFamily).Parallel x y :=
    (parallel_iff_sim S x y).2 h
  -- ここで `x y` は自動 coercion され、目標型に一致します。
  exact hxy

--Lemma 2.4（カードを使わない形）：
-- 目標：非自明同値類 ⇒ 極大
--ここも{α}が必要。
lemma maximal_of_nontrivialClass
    (S : SPO.FuncSetup α) {x : S.Elem}
    (hx : S.nontrivialClass x) : S.maximal x := by
  -- 非自明同値類 ⇒ パラレル相手 y と x≠y を取る
  rcases hx with ⟨y, hneq, hsim⟩
  -- parallel on α が欲しいので、型合わせ補題で作る
  have hpar : (S.idealFamily).Parallel (x : α) (y : α) :=
    parallel_of_sim_coe S hsim
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

------

--NDSの証明で使っている。
lemma exists_parallel_partner_from_nontrivial
    (S : SPO.FuncSetup α) {u : S.Elem}
    (hx : S.nontrivialClass u) :
    ∃ v : α, v ≠ u.1 ∧ v ∈ S.ground ∧ (S.idealFamily).Parallel u.1 v := by
  classical
  rcases hx with ⟨y, hneq, hsim⟩
  refine ⟨(y : α), ?hne, y.property, ?hpar⟩
  · -- y ≠ u から値の不等号へ
    intro h
    apply hneq
    apply Subtype.ext
    exact h
  · -- sim ⇒ parallel
    exact parallel_of_sim_coe (S := S) hsim

--すぐ下で使っている。
lemma two_deg_le_num_int_of_Rare
    (F : SetFamily α) (x : α) (hR : F.Rare x) :
    (2 * (F.degree x : Int) ≤ (F.numHyperedges : Int)) := by
  -- Nat の不等式を Int に持ち上げる
  -- Int.ofNat_le.mpr : m ≤ n → (m : ℤ) ≤ (n : ℤ)
  have : Int.ofNat (2 * F.degree x) ≤ Int.ofNat F.numHyperedges :=
    Int.ofNat_le.mpr hR
  -- 表記を (· : Int) に戻す
  exact this

--NDSの証明で使っている。
lemma diff_term_nonpos_of_Rare
    (F : SetFamily α) (x : α) (hR : F.Rare x) :
    2 * (F.degree x : Int) - (F.numHyperedges : Int) ≤ 0 := by
  -- a - b ≤ 0 ↔ a ≤ b
  have hx : (2 * (F.degree x : Int) ≤ (F.numHyperedges : Int)) :=
    two_deg_le_num_int_of_Rare (F := F) (x := x) hR
  -- `sub_nonpos.mpr` は「a ≤ b」を「a - b ≤ 0」にする
  exact Int.sub_nonpos_of_le hx

--   C) 等式＋非正 ⇒ 片側の ≤ へ

--一般的な補題なので移動してもいい。TraceFunctionalとか。
lemma le_of_eq_add_of_nonpos {a b t : Int}
    (h : a = b + t) (ht : t ≤ 0) : a ≤ b := by
  -- 目標を h で書き換え
  rw [h]
  -- b + t ≤ b + 0
  have h1 : b + t ≤ b + 0 := add_le_add_left ht b
  -- 右の 0 を消す
  -- `rw [add_zero]` で十分
  -- （tactic スタイルを用いて `simpa` は使わない）
  have h2 := h1
  -- 書き換え
  -- ここは tactic ブロックで簡潔に
  have : b + t ≤ b := by
    -- 右辺の `+ 0` を消す
    -- `rw` は許容されている想定（`simpa using` を避けるため）
    -- 直接 h1 を上書きして使う
    -- 以降、この小ブロックでのみ tactic を使います
    -- (Lean では `by` ブロック内で `rw` を使えます)
    -- 変数 h1 を上書きしてもよいのですが、ここではローカルコピー h2 を書換えます
    have h2' := h2
    -- `rw [add_zero] at h2'`
    -- tactic:
    -- (ここで実際のコードでは `rw [add_zero] at h2'` と一行書きます)
    -- 仕上げとして h2' を返す想定です
    -- ただしこの大域ブロックでは term モードのため、最終形を直接返します：
    -- 手短に：`by have h := h1; rwa [add_zero] at h` でもOK
    exact (add_le_iff_nonpos_right b).mpr ht

  exact this


-------------------------------------
/-! ## 3) Lemma 3.1：maximal ⇒ rare -/

lemma sim_of_maximal_above_class
    (S : SPO.FuncSetup α) {u x y : S.Elem}
    (hmax : S.maximal u)
    (hyU : S.sim y u) (hyx : S.le y x) :
    S.sim x u := by
  -- `u ≤ x` と `x ≤ u` の両方を示せば良い
  constructor
  · -- まず `u ≤ x`
    have hux : S.le u x := S.le_trans hyU.2 hyx
    -- 最大性：`u ≤ x → x ≤ u`
    exact hmax hux
  · -- つぎに `u ≤ x` は上で得た `hux`
    exact S.le_trans hyU.2 hyx

lemma ideal_diff_simClass_is_ideal
    (S : SPO.FuncSetup α)
    {u : S.Elem} {I : Finset α}
    (hmax : S.maximal u)
    (hI : (S.idealFamily).sets I) (huI : u.1 ∈ I) :
    (S.idealFamily).sets (I \ S.simClass u) ∧ u.1 ∉ (I \ S.simClass u) := by
  classical
  -- isOrderIdealOn に展開
  have hIdeal : isOrderIdealOn (S.leOn) S.ground I := by
    change isOrderIdealOn (S.leOn) S.ground I
    exact (S.sets_iff_isOrderIdeal).1 hI
  -- (1) 包含 I\U ⊆ ground は I ⊆ ground から従う
  have hSub : (I \ S.simClass u) ⊆ S.ground := by
    intro x hx
    have hxI_and_hxNotU := (Finset.mem_sdiff).1 hx
    have hxI : x ∈ I := hxI_and_hxNotU.1
    have hI_sub : I ⊆ S.ground := hIdeal.1
    exact hI_sub hxI
  -- (2) 下方閉：x∈I\U, y∈ground, leOn y x ⇒ y∈I\U
  have hDown :
      ∀ ⦃x⦄, x ∈ (I \ S.simClass u) →
      ∀ ⦃y⦄, y ∈ S.ground →
      S.leOn y x → y ∈ (I \ S.simClass u) := by
    intro x hx y hy h_yx
    -- x ∈ I, x ∉ U を取り出す
    have hxI_and_hxNotU := (Finset.mem_sdiff).1 hx
    have hxI    : x ∈ I := hxI_and_hxNotU.1
    have hxNotU : x ∉ S.simClass u := hxI_and_hxNotU.2
    -- まず isOrderIdealOn の下方閉で y ∈ I
    have hyI : y ∈ I := by
      have hyx : S.leOn y x := h_yx
      exact hIdeal.2 (x := x) hxI (y := y) hy hyx
    -- つぎに y ∉ U を示す（y ∈ U なら x ∈ U になって矛盾）
    have hyNotU : y ∉ S.simClass u := by
      intro hyU
      -- y ∈ U の展開：∃hyV, sim ⟨y,hyV⟩ u （ただし hyV = hy でOK）
      have hySim : S.sim ⟨y, hy⟩ u := by
        rcases (S.mem_simClass_iff u).1 hyU with ⟨hyV, hsim⟩
        -- ここで hyV = hy だが、`leOn` の仮定にあるのは hy なので hy に差し替えたい。
        -- 同値性の本体だけ使うので、hy をそのまま使って良い。
        -- hsim : S.sim ⟨y, hyV⟩ u だが、`y` の値は同じなので
        -- `Subtype.ext rfl` で置換してよい（値は一致、証明部だけ差）
        -- 具体的には S.sim の定義は `le ∧ le` なので、`Subtype.ext`不要でそのまま使える。
        exact hsim
      -- leOn y x から `S.le ⟨y,hy⟩ ⟨x,hxV⟩` を得る
      have hxV : x ∈ S.ground := (hIdeal.1) hxI
      have hyx_le : S.le ⟨y, hy⟩ ⟨x, hxV⟩ := by
        have hx' : S.leOn y x ↔ S.le ⟨y, hy⟩ ⟨x, hxV⟩ :=
          S.leOn_iff_subtype (a := y) (b := x) hy hxV
        exact hx'.1 h_yx
      -- 最大性から x ∼ u を得る → x ∈ U、矛盾
      have hxu_sim : S.sim ⟨x, hxV⟩ u :=
        sim_of_maximal_above_class S (u := u) (x := ⟨x, hxV⟩) (y := ⟨y, hy⟩)
          hmax hySim hyx_le
      have hxU : x ∈ S.simClass u := by
        have : ∃ (hxg : x ∈ S.ground), S.sim ⟨x, hxg⟩ u := by
          exact ⟨hxV, hxu_sim⟩
        exact (S.mem_simClass_iff u).2 this
      exact hxNotU hxU
    -- まとめて y ∈ I \ U
    exact (Finset.mem_sdiff).2 ⟨hyI, hyNotU⟩
  -- 以上から I\U は isOrderIdealOn
  have hSet : (S.idealFamily).sets (I \ S.simClass u) := by
    change isOrderIdealOn (S.leOn) S.ground (I \ S.simClass u)
    exact And.intro hSub (by intro x hx; exact hDown hx)
  -- u は U に属するので u ∉ I\U
  have huNot : u.1 ∉ (I \ S.simClass u) := by
    have huU : u.1 ∈ S.simClass u := by
      have : S.sim u u := S.sim_refl u
      have : ∃ (hu' : u.1 ∈ S.ground), S.sim ⟨u.1, hu'⟩ u := by
        exact ⟨u.property, this⟩
      exact (S.mem_simClass_iff u).2 this
    intro huIn
    have hu_pair := (Finset.mem_sdiff).1 huIn
    exact hu_pair.2 huU
  exact And.intro hSet huNot

/- ===========================================================
   4)  単射 Φ : {I | イデアル ∧ u∈I} → {J | イデアル ∧ u∉J}
       （I ↦ I \ U）が単射
   =========================================================== -/

noncomputable def Phi
    (S : SPO.FuncSetup α) (u : S.Elem) (hmax : S.maximal u) :
    {I // I ∈ (S.idealFamily).edgeFinset ∧ u.1 ∈ I} →
    {J // J ∈ (S.idealFamily).edgeFinset ∧ u.1 ∉ J} :=
  fun ⟨I, hIedge, huI⟩ =>
    let hI_sets : (S.idealFamily).sets I :=
      (SetFamily.mem_edgeFinset_iff_sets (F := S.idealFamily) (A := I)).1 hIedge
    let h := ideal_diff_simClass_is_ideal (S := S) (u := u) hmax hI_sets huI
    let hJedge : (I \ S.simClass u) ∈ (S.idealFamily).edgeFinset :=
      (SetFamily.mem_edgeFinset_iff_sets (F := S.idealFamily) (A := I \ S.simClass u)).2 h.1
    ⟨ I \ S.simClass u, hJedge, h.2 ⟩

lemma Phi_injective
    (S : SPO.FuncSetup α) {u : S.Elem} (hmax : S.maximal u) :
    Function.Injective (Phi S u hmax) := by
  classical
  intro a b hEq
  -- 展開
  cases a with
  | mk I hI =>
    cases b with
    | mk J hJ =>
      cases hI with
      | intro hIedge huI =>
        cases hJ with
        | intro hJedge huJ =>
          -- Φ の定義で基底集合の等式へ
          dsimp [Phi] at hEq
          -- 使う補題：U ⊆ I, U ⊆ J
          have hI_sets : (S.idealFamily).sets I :=
            (SetFamily.mem_edgeFinset_iff_sets (F := S.idealFamily) (A := I)).1 hIedge
          have hJ_sets : (S.idealFamily).sets J :=
            (SetFamily.mem_edgeFinset_iff_sets (F := S.idealFamily) (A := J)).1 hJedge
          have UsubI : S.simClass u ⊆ I :=
            S.simClass_subset_of_contains (u := u) (I := I) hI_sets huI
          have UsubJ : S.simClass u ⊆ J :=
            S.simClass_subset_of_contains (u := u) (I := J) hJ_sets huJ
          -- まず基底の Finset 同士の等式を取り出す
          --   I \ U = J \ U
          have hDiff :
              I \ S.simClass u = J \ S.simClass u := by
            -- hEq は Subtype の等式なので、値部分を取り出す
            exact congrArg Subtype.val hEq
          -- I ⊆ J
          have hIJ : I ⊆ J := by
            intro x hxI
            by_cases hxU : x ∈ S.simClass u
            · -- U ⊆ J より
              exact UsubJ hxU
            · -- x ∈ I\U なので等式から x ∈ J\U、したがって x ∈ J
              have hxInDiff : x ∈ I \ S.simClass u :=
                (Finset.mem_sdiff).2 ⟨hxI, hxU⟩
              have hxInDiff' : x ∈ J \ S.simClass u := by
                -- hDiff の両辺に属するので書き換え
                -- `rw [hDiff] at hxInDiff` を避けて等価性で移送
                -- 等式から右辺への移送
                have : (I \ S.simClass u) ⊆ (J \ S.simClass u) := by
                  intro t ht; exact by
                    -- `rw [hDiff]` で十分だが、`rw` を使ってよい
                    -- ここは素直に置換します
                    rw [hDiff] at ht
                    exact ht
                exact this hxInDiff
              have hxJ_and_notU := (Finset.mem_sdiff).1 hxInDiff'
              exact hxJ_and_notU.1
          -- J ⊆ I も同様
          have hJI : J ⊆ I := by
            intro x hxJ
            by_cases hxU : x ∈ S.simClass u
            · exact UsubI hxU
            ·
              have hxInDiff : x ∈ J \ S.simClass u :=
                (Finset.mem_sdiff).2 ⟨hxJ, hxU⟩
              have hxInDiff' : x ∈ I \ S.simClass u := by
                have : (J \ S.simClass u) ⊆ (I \ S.simClass u) := by
                  intro t ht
                  -- 反対向きの包含は hDiff⁻¹
                  -- `rw [← hDiff]` で移送
                  rw [← hDiff] at ht
                  exact ht
                exact this hxInDiff
              have hxI_and_notU := (Finset.mem_sdiff).1 hxInDiff'
              exact hxI_and_notU.1
          -- 以上で I = J
          have hIJ_eq : I = J := Finset.Subset.antisymm hIJ hJI
          -- サブタイプまで持ち上げ
          apply Subtype.ext
          exact hIJ_eq



section RareByInjection

variable {α : Type*} [DecidableEq α]

/-- 単射 `Φ : {A | A∈E ∧ x∈A} → {B | B∈E ∧ x∉B}` があれば `Rare x`。 -/
lemma rare_of_injection_between_filters
  (F : SetFamily α) (x : α)
  (Φ : {A // A ∈ F.edgeFinset ∧ x ∈ A} →
       {B // B ∈ F.edgeFinset ∧ x ∉ B})
  (hΦ : Function.Injective Φ) :
  F.Rare x := by
  classical
  -- `S_in := {A | A∈E ∧ x∈A}` と `S_out := {A | A∈E ∧ x∉A}`
  -- の Fintype.card 比較から、filter の card 比較へ移す
  -- まず、`{A // A ∈ E ∧ x ∈ A}` と `Subtype (A ∈ E.filter (x ∈ ·))` の同値
  let s := F.edgeFinset
  let pin : Finset (Finset α) := s.filter (fun A => x ∈ A)
  let pout : Finset (Finset α) := s.filter (fun A => x ∉ A)

  -- subtype 同値（in）
  let eIn :
    {A // A ∈ s ∧ x ∈ A} ≃ {A // A ∈ pin} :=
  { toFun := fun a =>
      ⟨a.1, by
        -- a.2 : A ∈ s ∧ x ∈ A
        have h := a.2
        have : a.1 ∈ pin := by
          exact (Finset.mem_filter).2 ⟨h.1, h.2⟩
        exact this⟩
    , invFun := fun b =>
      ⟨b.1, by
        -- b.2 : A ∈ s.filter (x∈A)
        -- そこから `A ∈ s ∧ x∈A`
        have hb := (Finset.mem_filter).1 b.2
        exact ⟨hb.1, hb.2⟩⟩
    , left_inv := by
        intro a; cases a with
        | mk A hA =>
          rfl
    , right_inv := by
        intro b; cases b with
        | mk B hB =>
          rfl }

  -- subtype 同値（out）
  let eOut :
    {A // A ∈ s ∧ x ∉ A} ≃ {A // A ∈ pout} :=
  { toFun := fun a =>
      ⟨a.1, by
        have h := a.2
        have : a.1 ∈ pout := by
          exact (Finset.mem_filter).2 ⟨h.1, h.2⟩
        exact this⟩
    , invFun := fun b =>
      ⟨b.1, by
        have hb := (Finset.mem_filter).1 b.2
        exact ⟨hb.1, hb.2⟩⟩
    , left_inv := by
        intro a; cases a with
        | mk A hA => rfl
    , right_inv := by
        intro b; cases b with
        | mk B hB => rfl }

  -- Φ を同値で両側に移送して得た単射から card 比較
  have hΦ' :
    Function.Injective (fun a : {A // A ∈ pin} =>
      eOut (Φ (eIn.symm a))) := by
    intro a b h
    -- `eIn.symm` と `eOut` は同値なので injective
    have : eIn.symm a = eIn.symm b := by
      -- `Φ` の単射から
      apply hΦ
      -- 値部分に `eOut` の injective（同値）を外す
      -- `Equiv.injective` を使わず、同値の両辺に `left_inv/right_inv`
      -- をかけて取り出す
      -- 具体的には `congrArg Subtype.val` 等でも可だが、ここは素直に：
      have := congrArg Subtype.val h
      -- ただし Subtype.val の等式だけでは不足するので、`eOut` の左右逆性で戻す
      -- より簡潔には「同値は injective」を使う：
      -- `have hinj := eOut.injective` が使える
      have hinj := eOut.injective
      -- `h` から `eIn.symm a = eIn.symm b` を導く：
      -- 実際には `eOut (Φ (eIn.symm a)) = eOut (Φ (eIn.symm b))` なので
      -- `hinj` を適用して `Φ (eIn.symm a) = Φ (eIn.symm b)`
      have h₁ : Φ (eIn.symm a) = Φ (eIn.symm b) := by
        exact hinj h
      -- ここで `hΦ` に injective を適用すれば `eIn.symm a = eIn.symm b`
      exact hinj h

    -- 同値の injective から `a = b`
    -- `eIn.injective` を用いる
    simp_all only [Equiv.coe_fn_symm_mk, Equiv.coe_fn_mk, Subtype.mk.injEq, pout, s, eOut, pin, eIn]
    obtain ⟨val_1, property_1⟩ := b
    subst this
    simp_all only [pin, s]


  -- 以上から |pin| ≤ |pout|
  have hCard_le :
      pin.card ≤ pout.card := by
    -- 有限型の単射から Fintype.card の比較
    have hfin :
        Fintype.card {A // A ∈ pin}
        ≤ Fintype.card {A // A ∈ pout} :=
      Fintype.card_le_of_injective _ hΦ'
    -- それぞれ card = filter.card
    -- `Fintype.card {A // A ∈ t} = t.card` は標準
    -- `Fintype.card_subtype` 相当の事実
    -- `Fintype.card_coe` 的に扱えるので `by classical; exact ...`
    -- ここは既知の等式：`Fintype.card {a // a ∈ t} = t.card`
    -- 置換して終了
    -- 明示に書く：
    -- `Fintype.card {A // A ∈ pin} = pin.card`
    -- `Fintype.card {A // A ∈ pout} = pout.card`
    -- これらは `Fintype.card_coe` で出ます。
    -- ただし `Subtype` の `Fintype` は `DecidablePred` から自動で入る。
    -- 置換：
    simpa using hfin

  -- `degree x = |pin|`、`numHyperedges = s.card`
  have hDeg : F.degree x = pin.card :=
    (SetFamily.degree_eq_card_filter (F := F) (x := x))
  have hNum : F.numHyperedges = s.card := by
    exact rfl

  -- さらに `|pin| + |pout| = |s|`
  have hSplit :
      pin.card + pout.card = s.card := by
    exact SetFamily.card_filter_add_card_filter_not s fun A => x ∈ A

  -- 目標：2 * degree ≤ numHyperedges
  -- `2*|pin| ≤ |s|` を示せばよい
  -- `|pin| ≤ |pout|` と `|pin|+|pout|=|s|` から従う
  have h2 :
      2 * pin.card ≤ s.card := by
    -- `|pin| ≤ |pout|`
    -- 加えて両辺に `|pin|` を足すと：
    -- `|pin| + |pin| ≤ |pout| + |pin|`
    -- 右辺は分割等式より `= |s|`
    have := Nat.add_le_add_left hCard_le pin.card
    -- 左辺：`|pin| + |pin| = 2*|pin|`
    -- 右辺：`|pout| + |pin| = |s|`
    -- 書換え
    have : 2 * pin.card ≤ pin.card + pout.card := by
      -- `Nat.add_comm` で順序を合わせる
      -- `pin.card + pin.card = 2 * pin.card`
      -- これは `two_mul` か `Nat.two_mul`？
      -- Nat では `Nat.mul_comm 2 _` 等で整える
      -- まず左辺：
      --   2 * pin.card = pin.card + pin.card
      -- という等式を使って置換
      -- `Nat.succ_eq_add_one` のように `two_mul` は整数側だが Nat にも `two_mul` あり
      -- ここは手作業で書換え
      have hL : 2 * pin.card = pin.card + pin.card := by
        -- 2 * n = n + n
        -- `Nat.mul_comm` と `Nat.add_comm` は等式
        -- `Nat.succ` で書くより、この等式は標準
        -- 直接 `Nat.two_mul` は `2 * n = n + n`
        exact Nat.two_mul pin.card
      -- 右辺 `pin + pout` へは `Nat.add_comm` を使って
      have hR : pout.card + pin.card = pin.card + pout.card :=
        Nat.add_comm _ _
      -- 変形
      -- もともとの `Nat.add_le_add_left hCard_le pin.card` は：
      --   pin + pin ≤ pin + pout
      -- を与えるので、そこから置換
      have base := (Nat.add_le_add_left hCard_le pin.card)
      -- `pin + pin ≤ pin + pout`
      -- 左右を置換
      simpa [hL, hR] using base
    -- 右辺を |s| に置換
    -- `pin.card + pout.card = s.card`
    simpa [hSplit] using this

  -- 仕上げ：等式で置換
  -- `2 * F.degree x ≤ F.numHyperedges`
  -- = `2 * pin.card ≤ s.card`
  -- よって Rare
  -- Rare の定義に沿って直接示す
  -- `def Rare (F) (x) : Prop := 2 * F.degree x ≤ F.numHyperedges`
  -- 置換して `h2`
  -- `by` ブロックで書換え
  change 2 * F.degree x ≤ F.numHyperedges
  -- 置換
  -- `hDeg` と `hNum`
  -- `rw` で逐次書換え
  rw [hDeg, hNum]
  exact h2

end RareByInjection

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
  (hx : S.nontrivialClass u)
  (hNDSDef :
    (S.idealFamily).NDS
      = 2 * (∑ A ∈ (S.idealFamily).edgeFinset, (A.card : Int))
        - ((S.idealFamily).numHyperedges : Int) * ((S.idealFamily).ground.card : Int))
  (hNDSDefTrace :
    (traceAt u.1 (S.idealFamily)).NDS
      = 2 * (∑ B ∈ (traceAt u.1 (S.idealFamily)).edgeFinset, (B.card : Int))
        - ((traceAt u.1 (S.idealFamily)).numHyperedges : Int)
          * ((traceAt u.1 (S.idealFamily)).ground.card : Int)) :
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
      (hNDSDef := hNDSDef) (hNDSDefTrace := hNDSDefTrace)
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
--現状ではどこからも使ってないが、後半使うかも。
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
