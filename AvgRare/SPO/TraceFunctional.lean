import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.Order.GroupWithZero.Unbundled.Defs
import AvgRare.Basics.SetFamily
import AvgRare.Basics.Ideals
import AvgRare.SPO.FuncSetup
import AvgRare.Basics.Trace.Common

universe u
open Classical

open scoped BigOperators

namespace AvgRare
open Trace
open SPO
open FuncSetup
open SetFamily

variable {α : Type u} [DecidableEq α] (S : FuncSetup α)

namespace SPO



/- ==========================================
   1) 反射推移閉包 (RTG) と iterate の橋渡し
   ========================================== -/

-- 「k 回反復＝到達可能」の片向き（必要最小限）
lemma rtg_of_iter (S : FuncSetup α) (x : S.Elem) (k : ℕ) :
    Relation.ReflTransGen (stepRel S.f) x (S.iter k x) := by
  -- 既存: IterateRTG の
  --   reflTransGen_iff_exists_iterate (f : β → β)
  -- を β := S.Elem, f := (fun z => S.iter 1 z) に相当する定義で使えるように
  -- 定義が一致している前提で次の 1 行が通ります：
  -- （もし名前や定義が少し違っていたら、手元の IterateRTG 節に合わせて置換してください）
  have h : Relation.ReflTransGen (stepRel S.f) x (S.iter k x) :=
    (reflTransGen_iff_exists_iterate (S.f)).2 ⟨k, rfl⟩
  exact h

-- le ↔ ∃k.iter の既存補題を使って、le → RTG にするだけの最小版
--なぜか{α}が必要。ないとle_iff_exists_iter S x zでエラー。
--新しい証明で不要に？
lemma rtg_of_le {α : Type u} [DecidableEq α] (S : FuncSetup α) {x z : S.Elem} (hxz : S.le x z) :
    Relation.ReflTransGen (stepRel S.f) x z := by
  --#check le_iff_exists_iter S x z-- hxz
  rcases (le_iff_exists_iter S x z).1 hxz with ⟨k, hk⟩
  -- x ⟶* iter k x かつ iter k x = z
  have hxiter : Relation.ReflTransGen (stepRel S.f) x (S.iter k x) :=
    rtg_of_iter S x k
  -- 置換で z へ
  have := congrArg (fun t => Relation.ReflTransGen (stepRel S.f) x t) hk
  -- 上の `congrArg` は命題の等式には直接使えないので、ここは書き直し。
  -- `hk` による単純な書き換えで十分です：
  -- （Mathlib の `simp [hk]` でも可ですが、明示の書換えにします）
  cases hk
  exact hxiter

-- 逆向き RTG → le は、今回のゴールでは「最後に le を回収」する時に使います。
-- 新しい証明でも必要
lemma le_of_rtg {α} [DecidableEq α] (S : FuncSetup α) {x z : S.Elem}
  (h : Relation.ReflTransGen (stepRel S.f) x z) : S.le x z := by
  rcases (reflTransGen_iff_exists_iterate (S.f)).1 h with ⟨k, hk⟩
  exact (le_iff_exists_iter S x z).2 ⟨k, hk⟩

--必要。付け替え関数。
noncomputable def eraseOneMap
    (u v : {a // a ∈ S.ground}) (hvne : v ≠ u) :
    {x // x ∈ S.ground.erase u.1} → {y // y ∈ S.ground.erase u.1} :=
  fun x => by
    classical
    -- x : {x // x ∈ S.ground.erase u} から ground への包含をほどく
    have hx_in_ground : x.1 ∈ S.ground := (Finset.mem_erase.mp x.2).2
    -- 元の写像で 1 歩進める
    let y : {a // a ∈ S.ground} := S.f ⟨x.1, hx_in_ground⟩
    -- 場合分け：y = u なら v に付け替え，そうでなければ y のまま
    by_cases hyu : y = u
    · -- 出力は v。v が `ground.erase u` に入ることを示す。
      have hv_val_ne : v.1 ≠ u.1 := by
        intro hval
        apply hvne
        apply Subtype.ext
        exact hval
      have hv_in_erase : v.1 ∈ S.ground.erase u.1 := by
        -- mem_erase ↔ (≠ ∧ ∈)
        exact Finset.mem_erase.mpr ⟨hv_val_ne, v.2⟩
      exact ⟨v.1, hv_in_erase⟩
    · -- 出力は y。y が `ground.erase u` に入ることを示す。
      have hy_val_ne : y.1 ≠ u.1 := by
        intro hval
        apply hyu
        apply Subtype.ext
        exact hval
      have hy_in_erase : y.1 ∈ S.ground.erase u.1 := by
        exact Finset.mem_erase.mpr ⟨hy_val_ne, y.2⟩
      exact ⟨y.1, hy_in_erase⟩

/-- ground.erase u → ground の包含 。使われている。これもFuncSetup.leanに移動してもよい。-/
noncomputable def inclErase (S : FuncSetup α) (u : S.Elem) :
  {x // x ∈ S.ground.erase u.1} → S.Elem :=
fun x => ⟨x.1, (Finset.mem_erase.mp x.2).2⟩

--少し使われている。
@[simp] lemma inclErase_val (S : FuncSetup α) (u : S.Elem) (x) :
  (inclErase S u x).1 = x.1 := rfl

/-- `inclErase` の像は明らかに `ground` 上。値で十分なときに便利。でも使われてない。-/
@[simp] lemma inclErase_property (S : FuncSetup α) (u : S.Elem) (x : {x // x ∈ S.ground.erase u.1}) :
  (inclErase S u x).2 = (Finset.mem_erase.mp x.2).2 := rfl

/-- `eraseOneMap` の分岐仕様（値） -/
--必要性不明。必要性不明の補題で使われているだけ。
lemma eraseOneMap_spec
  (S : FuncSetup α) (u v : S.Elem) (hvne : v ≠ u)
  (x : {x // x ∈ S.ground.erase u.1}) :
  let y := S.f (inclErase S u x)
  if _ : y = u
  then (eraseOneMap S u v hvne x).1 = v.1
  else (eraseOneMap S u v hvne x).1 = y.1 := by
  classical
  dsimp [eraseOneMap, inclErase]
  by_cases hyu : S.f ⟨x.1, (Finset.mem_erase.mp x.2).2⟩ = u
  · -- then 分岐：出力は v
    -- 定義は `⟨v.1, _⟩` を返すので .1 は v.1
    simp_all only [↓reduceIte, ↓reduceDIte]
  · -- else 分岐：出力は y
    simp_all only [↓reduceIte, ↓reduceDIte]

/-! ## 3) 1 歩の橋渡し：S′ → S は `v = S.f u` の下で 1/2 歩に復元 -/

/-- `v = S.f u` のもとで，S′ の 1 ステップは S で 1 または 2 ステップに復元できる。 -/
--使われているよう。
lemma step_S'_to_S_usingSucc
  (S : FuncSetup α) (u v : S.Elem) (hvne : v ≠ u) (hv : v = S.f u)
  {x y : {a // a ∈ S.ground.erase u.1}}
  (h : stepRel (eraseOneMap S u v hvne) x y) :
  Relation.ReflTransGen (stepRel (fun z : S.Elem => S.f z))
      (inclErase S u x) (inclErase S u y) := by
  classical
  -- `h` は `S.eraseOneMap u v hvne x = y`
  -- 場合分け：`S.f (inclErase x) = u` or そうでない
  by_cases hyu : S.f (inclErase S u x) = u
  · -- then：S 側で `incl x → u → v`，かつ `y` は値として v に等しい
    -- まず `incl x ⟶ u`
    have h1 : stepRel (fun z : S.Elem => S.f z) (inclErase S u x) u := by
      exact hyu
    -- 次に `u ⟶ v`（仮定 hv）
    have h2 : stepRel (fun z : S.Elem => S.f z) u v := by
      -- `S.f u = v`
      exact Eq.symm hv
    -- `y` の値が v.1 であることを確認
    have hval_y :
      y.1 = v.1 := by
        -- `h : eraseOneMap ... x = y` を値に落とす
        have hval : (eraseOneMap S u v hvne x).1 = y.1 :=
          congrArg Subtype.val h
        -- `hyu` なら eraseOneMap の値は v.1（定義/補題で分岐）
        -- （ここはあなたが既に示したやり方と同じでOK）
        -- 例：eraseOneMap_spec を使うか，定義を開いて then 分岐に入れる
        -- 簡潔に書くなら：
        have : (eraseOneMap S u v hvne x).1 = v.1 := by
          -- 定義 or spec を使って `hyu` ケースに落とす
          -- （あなたの環境で通ったやり方でOK）
          -- ここでは短く：
          --   dsimp [eraseOneMap, inclErase] at *
          --   ... （hyu 側の分岐へ）
          -- という手順になります
          dsimp [eraseOneMap]
          split
          next h_1 => simp_all only
          next h_1 =>
            simp_all only
            contradiction
        exact Eq.trans (Eq.symm hval) this

    -- 値が等しいので `inclErase S u y = v`
    have hv_y : inclErase S u y = v := by
      apply Subtype.ext
      exact hval_y

    -- 2 ステップ連結：`incl x ⟶ u ⟶ v`
    have hx_to_u :
      Relation.ReflTransGen (stepRel (fun z : S.Elem => S.f z))
        (inclErase S u x) u := by
        apply Relation.ReflTransGen.tail
        exact Relation.ReflTransGen.refl
        exact hyu
    have hx_to_v :
      Relation.ReflTransGen (stepRel (fun z : S.Elem => S.f z))
        (inclErase S u x) v :=
      hx_to_u.tail h2

    -- `v = incl y` に置換してゴールを得る
    cases hv_y
    exact hx_to_v
  · -- else：`S.f (incl x) = incl y` なので S で 1 ステップ
    have hval :
        (S.f (inclErase S u x)).1 = (inclErase S u y).1 := by
      -- `h` を値へ
      have h' : (eraseOneMap S u v hvne x).1 = y.1 :=
        congrArg Subtype.val h
      -- else 分岐の値は `(S.f (incl x)).1`
      have hspec :=
        eraseOneMap_spec (S := S) (u := u) (v := v) (hvne := hvne) x
      -- else ケース
      -- ここで `hyu = false` を使う
      -- すると `(S.eraseOneMap ... x).1 = (S.f (incl x)).1`
      -- よって `(S.f (incl x)).1 = y.1` が従う
      exact Eq.trans (by subst hv;simp_all only [↓reduceDIte]) h'
    -- 値が等しいサブタイプは等しい
    have hstep : stepRel (fun z : S.Elem => S.f z)
        (inclErase S u x) (inclErase S u y) := by
      -- サブタイプの等式へ
      -- `S.f (incl x) = incl y`
      apply Subtype.ext
      exact hval
    apply Relation.ReflTransGen.tail
    · exact Relation.ReflTransGen.refl
    · exact hstep

-- `eraseOneMap` の定義を使って `f` を付け替える。必要。eraseOneMapは写像だけに対し、これはFuncSetupの対応。
noncomputable def eraseOne (u v : {a // a ∈ S.ground}) (hvne : v ≠ u) : FuncSetup α :=
{ ground := S.ground.erase u.1
, f      := eraseOneMap S u v hvne }

--パラレルパートナーを持つものに限定した、FuncSetupのほうのtraceの対応。
noncomputable def eraseOneUsingSucc (u : S.Elem)
    (hNontriv : S.nontrivialClass u) : FuncSetup α :=
  eraseOne S u (S.f u)
    (FuncSetup.f_ne_of_nontrivialClass (S := S) hNontriv)

/-- `foldMap S u hvne z`：
  `z = u` なら `S.f u` に，そうでなければ `z` 自身を `ground.erase u` 上に埋め込む。 -/
--必要な定義。他の場面でも使えるかも。他で使えることが判明すればFuncSetup.leanに移す。
noncomputable def foldMap
  (S : FuncSetup α) (u : S.Elem) (hvne : S.f u ≠ u)
  (z : S.Elem) : {a // a ∈ S.ground.erase u.1} :=
by
  classical
  by_cases hz : z = u
  · -- z = u → S.f u に送る
    refine ⟨(S.f u).1, ?_⟩
    -- (S.f u).1 ∈ ground.erase u.1
    have hval_ne : (S.f u).1 ≠ u.1 := by
      intro h
      apply hvne
      apply Subtype.ext
      exact h
    exact Finset.mem_erase.mpr ⟨hval_ne, (S.f u).2⟩
  · -- z ≠ u → 値 z.1 をそのまま erase へ
    refine ⟨z.1, ?_⟩
    have hval_ne : z.1 ≠ u.1 := by
      -- z ≠ u ⇒ 値も異なる
      have : (z : α) ≠ (u : α) := S.coe_ne_of_ne hz
      exact this
    exact Finset.mem_erase.mpr ⟨hval_ne, z.2⟩

/-- `foldMap` を戻すと：
    `z ≠ u` なら `inclErase (foldMap z) = z`，
    `z = u` なら `inclErase (foldMap z) = S.f u`。 -/
--必要な補題
lemma inclErase_foldMap
  (S : FuncSetup α) (u : S.Elem) (hvne : S.f u ≠ u) (z : S.Elem) :
  (inclErase S u (foldMap (S := S) (u := u) (hvne := hvne) z))
    = (if  z = u then S.f u else z) := by
  classical
  by_cases hz : z = u
  · -- then
    subst hz
    -- 定義からそのまま
    exact
      apply_dite (inclErase S z) (z = z) (fun hz => ⟨↑(S.f z), foldMap._proof_1 S z hvne⟩) fun hz =>
        ⟨↑z, foldMap._proof_2 S z z hz⟩
  · -- else
    -- 値が z.1，ground 証明は (mem_erase).2 の右成分が ground 証明
    -- `inclErase` は値保持の埋め込みなので z に戻る
    -- 右辺の if_false に一致
    have : (inclErase S u (foldMap (S := S) (u := u) (hvne := hvne) z)).1 = z.1 := by
      simp_all only [inclErase_val]
      simp [foldMap, hz]
    exact
      apply_dite (inclErase S u) (z = u) (fun hz => ⟨↑(S.f u), foldMap._proof_1 S u hvne⟩) fun hz =>
        ⟨↑z, foldMap._proof_2 S u z hz⟩

/-- `x : ground.erase u` に対しては常に `foldMap (inclErase x) = x`。 -/
--必要な補題。後ろで使われている。
@[simp] lemma foldMap_inclErase
  (S : FuncSetup α) (u : S.Elem) (hvne : S.f u ≠ u)
  (x : {a // a ∈ S.ground.erase u.1}) :
  foldMap (S := S) (u := u) (hvne := hvne) (inclErase S u x) = x := by
  classical
  -- `inclErase x ≠ u`（値が erase により u.1 と異なる）
  have hne : (inclErase S u x) ≠ u := by
    intro h
    have : x.1 = u.1 := congrArg Subtype.val h
    exact (Finset.mem_erase.mp x.2).1 this
  -- `inclErase_foldMap` の else 分岐で `inclErase (foldMap ...) = inclErase x`
  have hback :
      inclErase S u (foldMap (S := S) (u := u) (hvne := hvne) (inclErase S u x))
        = inclErase S u x := by
    -- if_false
    have := inclErase_foldMap (S := S) (u := u) (hvne := hvne) (z := inclErase S u x)
    -- else なので右辺は z
    -- 目標は `= z` と同じ
    -- そのまま使える
    simp_all only [ne_eq]
    exact rfl
  -- `inclErase` が単射（Subtype.ext with 値 rfl）：
  -- 具体的には値が等しいのでサブタイプも等しい
  apply Subtype.ext
  simp_all only [ne_eq]
  obtain ⟨val_1, property_1⟩ := x
  simp_all only
  exact congr_arg Subtype.val hback

/-! ## S の 1 歩を S′（`v = S.f u`）で 0/1 歩に移送 -/

/-- 1 歩版（`v = S.f u`）：`S.f p = q` から
    `foldMap p ⟶* foldMap q`（S′ の `eraseOneMap`） -/
--必要な補題
lemma step_map_S_to_S'_usingSucc
  (S : FuncSetup α) (u : S.Elem) (hvne : S.f u ≠ u)
  {p q : S.Elem} (hpq : stepRel (fun z : S.Elem => S.f z) p q) :
  Relation.ReflTransGen (stepRel (eraseOneMap S u (S.f u)
    (by intro h; exact hvne h)))
      (foldMap (S := S) (u := u) (hvne := hvne) p)
      (foldMap (S := S) (u := u) (hvne := hvne) q) := by
  classical
  -- 場合分け：p = u か否か
  by_cases hpu : p = u
  · -- p = u → q = S.f u。foldMap p = foldMap q なので refl
    have hq : q = S.f u := by
      -- hpq : S.f p = q
      -- p = u
      -- よって q = S.f u
      apply Eq.trans (Eq.symm hpq)
      exact congrArg S.f hpu
    -- 目標の両端が等しいことを示し，置換して refl
    have hEq :
        foldMap (S := S) (u := u) (hvne := hvne) p
      = foldMap (S := S) (u := u) (hvne := hvne) q := by
      -- p = u, q = S.f u
      cases hpu
      cases hq
      -- どちらも `(S.f u).1` を値に持つ
      apply Subtype.ext
      dsimp [foldMap]
      simp_all only [↓reduceDIte]

    subst hq hpu
    simp_all only
    obtain ⟨val, property⟩ := p
    simp_all only
    rfl

  · -- p ≠ u → 1 歩で移送できる
    -- `inclErase (foldMap p) = p`
    have hincl_p :
        inclErase S u (foldMap (S := S) (u := u) (hvne := hvne) p) = p :=
      by
        -- `inclErase_foldMap` の else 分岐
        have := inclErase_foldMap (S := S) (u := u) (hvne := hvne) (z := p)
        -- if_false → 右辺 = p
        -- そのまま使う
        simp_all only
        exact rfl
    -- `S.f p = q`
    have hfp : S.f p = q := hpq
    -- `eraseOneMap` の値を計算して q に一致することを示す
    have hstep :
      stepRel (eraseOneMap S u (S.f u)
          (by intro h; exact hvne h))
        (foldMap (S := S) (u := u) (hvne := hvne) p)
        (foldMap (S := S) (u := u) (hvne := hvne) q) := by
      -- 値成分で示す：`S.eraseOneMap ... (foldMap p) = foldMap q`
      apply Subtype.ext
      -- `eraseOneMap` の分岐は `S.f (inclErase (foldMap p))` が `u` かどうか
      -- いま `inclErase (foldMap p) = p` なので判定は `S.f p = q` と `q = u` で分岐
      have h_incl : inclErase S u (foldMap (S := S) (u := u) (hvne := hvne) p) = p := hincl_p
      -- 場合分け：q = u か否か
      by_cases hqu : q = u
      · -- then：`eraseOneMap` は v = S.f u を返す
        -- 左辺値 = (S.f u).1，右辺 `foldMap q` も q = u の分岐で (S.f u).1
        -- よって値は一致
        -- 値の等式を示せば十分
        -- 左：定義から (S.f u).1
        -- 右：foldMap の then 分岐で (S.f u).1
        -- そのまま rfl で潰せる（定義形）
        -- ここでは簡潔に：
        --   書換えにより両辺 (S.f u).1 へ
        -- ※ 詳細に展開する必要があればここを分解して書いてください
        --   （simpa using は使わない方針）
        -- 値の等式
        have : (eraseOneMap S u (S.f u)
                  (by intro h; exact hvne h)
                (foldMap (S := S) (u := u) (hvne := hvne) p)).1
              = (S.f u).1 := by
          -- 定義の then 分岐
          -- ここでは `S.f (inclErase (foldMap p)) = S.f p = q = u`
          -- なので then
          -- 出力値は v.1 = (S.f u).1
          dsimp [eraseOneMap]
          subst hqu hfp
          simp_all only
          obtain ⟨val, property⟩ := p
          split
          next h => simp_all only
          next h =>
            simp_all only
            congr 1
            ext : 1
            tauto
        have : (foldMap (S := S) (u := u) (hvne := hvne) q).1 = (S.f u).1 := by
          -- q = u の場合の foldMap は (S.f u)
          cases hqu
          dsimp [foldMap]
          subst hfp
          simp_all only [↓reduceDIte]
        -- 以上を合わせて
        apply Eq.trans
        · (expose_names; exact this_1)
        · exact id (Eq.symm this)

      · -- else：`eraseOneMap` は y = q を返す
        -- 左：値 q.1，右：foldMap の else 分岐で q.1
        -- 値が一致
        -- 簡潔に rfl
        dsimp [eraseOneMap]
        dsimp [foldMap]
        simp_all only [↓reduceDIte]

    -- 1 歩を RTG に
    apply Relation.ReflTransGen.tail
    · --show Relation.ReflTransGen (stepRel (eraseOneMap S u (S.f u) ⋯)) (foldMap S u hvne p) ?neg.b✝
      exact Relation.ReflTransGen.refl
    · dsimp [stepRel]
      exact hstep

--必要な補題
lemma map_rtg_foldMap_usingSucc
  (S : FuncSetup α) (u : S.Elem) (hvne : S.f u ≠ u)
  {p q : S.Elem}
  (h : Relation.ReflTransGen (stepRel (fun z : S.Elem => S.f z)) p q) :
  Relation.ReflTransGen (stepRel (eraseOneMap S u (S.f u)
    (by intro h; exact hvne h)))
    (foldMap (S := S) (u := u) (hvne := hvne) p)
    (foldMap (S := S) (u := u) (hvne := hvne) q) := by
  induction h with
  | @refl =>
      exact Relation.ReflTransGen.refl
  | @tail a b hab hbc ih =>
      -- 1歩を new 側に移す
      have step :=
        step_map_S_to_S'_usingSucc (S := S) (u := u) (hvne := hvne)
          (p := a) (q := b)
          (by simpa [stepRel] using hbc)
      -- 合成
      apply Relation.ReflTransGen.trans ih step

/-- (B) 目的の補題：`inclErase x ⟶* inclErase y` を新世界で `x ⟶* y` に移送 -/
--必要な補題。
lemma rtg_S_to_S'_usingSucc
  (S : FuncSetup α) (u : S.Elem) (hvne : S.f u ≠ u)
  {x y : {a // a ∈ S.ground.erase u.1}}
  (h : Relation.ReflTransGen (stepRel (fun z : S.Elem => S.f z))
        (inclErase S u x) (inclErase S u y)) :
  Relation.ReflTransGen (stepRel (eraseOneMap S u (S.f u)
    (by intro h; exact hvne h))) x y := by
  classical
  -- `inclErase x ⟶* inclErase y` を foldMap で移送
  have mapped :
    Relation.ReflTransGen (stepRel (eraseOneMap S u (S.f u)
      (by intro h; exact hvne h)))
      (foldMap (S := S) (u := u) (hvne := hvne) (inclErase S u x))
      (foldMap (S := S) (u := u) (hvne := hvne) (inclErase S u y)) :=
    map_rtg_foldMap_usingSucc (S := S) (u := u) (hvne := hvne) h
  -- 両端を `foldMap_inclErase` で潰す
  have hx := foldMap_inclErase (S := S) (u := u) (hvne := hvne) x
  have hy := foldMap_inclErase (S := S) (u := u) (hvne := hvne) y
  -- 端点書換え後ちょうど目標
  simpa [hx, hy] using mapped

/-- (a) usingSucc 版：S′ の RTG を S の RTG に持ち上げる。使われている -/
lemma map_rtg_S'_to_S_usingSucc
  (S : FuncSetup α) (u : S.Elem) (hvne : S.f u ≠ u)
  {x y : {a // a ∈ S.ground.erase u.1}}
  (h : Relation.ReflTransGen
        (stepRel (eraseOneMap S u (S.f u) (by intro h; exact hvne h)))
        x y) :
  Relation.ReflTransGen (stepRel (fun z : S.Elem => S.f z))
    (inclErase S u x) (inclErase S u y) := by
  classical
  refine Relation.ReflTransGen.head_induction_on h ?h0 ?hstep
  · exact Relation.ReflTransGen.refl
  · intro p q hpq hrest ih
    -- 1歩補題で `inclErase p ⟶* inclErase q`
    have one :
      Relation.ReflTransGen (stepRel (fun z : S.Elem => S.f z))
        (inclErase S u p) (inclErase S u q) :=
      step_S'_to_S_usingSucc
        (S := S) (u := u) (v := S.f u)
        (hvne := by intro h; exact hvne h) (hv := rfl) hpq
    exact Relation.ReflTransGen.trans one ih

/-- (b) usingSucc 版：`S'.leOn a b → S.leOn a b`。 使われている-/
lemma leOn_lift_S'_to_S_usingSucc {α : Type u} [DecidableEq α]
  (S : FuncSetup α) (u : S.Elem) (hvne : S.f u ≠ u)
  {a b : α} (ha : a ∈ S.ground.erase u.1) (hb : b ∈ S.ground.erase u.1) :
  (eraseOne S u (S.f u) (by intro h; exact hvne h)).leOn a b → S.leOn a b := by
  intro h'
  -- subtype 化して S′ の `le` を得る
  have hS'le :
      (eraseOne S u (S.f u) (by intro h; exact hvne h)).le ⟨a, ha⟩ ⟨b, hb⟩ :=
    (leOn_iff_subtype
      (S := eraseOne S u (S.f u) (by intro h; exact hvne h))
      (a := a) (b := b) (ha := ha) (hb := hb)).1 h'

  -- S′: le → RTG
  have hrtg_S' :
      Relation.ReflTransGen
        (stepRel (eraseOneMap S u (S.f u) (by intro h; exact hvne h)))
        ⟨a, ha⟩ ⟨b, hb⟩ :=
    rtg_of_le (S := eraseOne S u (S.f u) (by intro h; exact hvne h)) hS'le

  -- RTG を S に持ち上げ（端点は `inclErase` で ground に戻すだけ）
  have hrtg_S :
      Relation.ReflTransGen (stepRel S.f)
        (inclErase S u ⟨a, ha⟩) (inclErase S u ⟨b, hb⟩) :=
    map_rtg_S'_to_S_usingSucc (S := S) (u := u) (hvne := hvne) hrtg_S'

  -- 端点の値は一致している（`inclErase` はただの埋め込み）
  have haG : a ∈ S.ground := (Finset.mem_erase.mp ha).2
  have hbG : b ∈ S.ground := (Finset.mem_erase.mp hb).2
  have : Relation.ReflTransGen (stepRel S.f) ⟨a, haG⟩ ⟨b, hbG⟩ := by
    simpa [inclErase] using hrtg_S

  -- RTG → le → leOn
  have hle : S.le ⟨a, haG⟩ ⟨b, hbG⟩ := le_of_rtg (S := S) this
  exact (leOn_iff_subtype (S := S) (a := a) (b := b) (ha := haG) (hb := hbG)).2 hle


--使われている。
lemma leOn_restrict_S_to_S'_usingSucc {α : Type u} [DecidableEq α]
  (S : FuncSetup α) (u : S.Elem) (hvne : S.f u ≠ u)
  {a b : α} (ha : a ∈ S.ground.erase u.1) (hb : b ∈ S.ground.erase u.1) :
  S.leOn a b →
  (eraseOne S u (S.f u) (by intro h; exact hvne h)).leOn a b := by
  intro hab
  -- S 側の le
  have haG : a ∈ S.ground := (Finset.mem_erase.mp ha).2
  have hbG : b ∈ S.ground := (Finset.mem_erase.mp hb).2
  have hSle : S.le ⟨a,haG⟩ ⟨b,hbG⟩ :=
    (leOn_iff_subtype (S:=S) (a:=a) (b:=b) (ha:=haG) (hb:=hbG)).1 hab
  -- S の RTG
  have hrtg_S : Relation.ReflTransGen (stepRel S.f) ⟨a,haG⟩ ⟨b,hbG⟩ :=
    rtg_of_le (S:=S) hSle
  -- 端点を inclErase 形にそろえる
  have h' :
    Relation.ReflTransGen (stepRel (fun z : S.Elem => S.f z))
      (inclErase S u ⟨a,ha⟩) (inclErase S u ⟨b,hb⟩) := by
    -- inclErase の定義で値が同じなので書き換えだけでOK
    simpa [inclErase] using hrtg_S
  -- S′ の RTG（usingSucc）
  have hrtg_S' :
    Relation.ReflTransGen
      (stepRel (eraseOneMap S u (S.f u) (by intro h; exact hvne h)))
      ⟨a,ha⟩ ⟨b,hb⟩ :=
    rtg_S_to_S'_usingSucc (S:=S) (u:=u) (hvne:=hvne) h'
  -- RTG → le（S′）
  have hS'le :
    (eraseOne S u (S.f u) (by intro h; exact hvne h)).le ⟨a,ha⟩ ⟨b,hb⟩ :=
    le_of_rtg (S:=eraseOne S u (S.f u) (by intro h; exact hvne h)) hrtg_S'
  -- subtype から leOn へ
  exact (leOn_iff_subtype
    (S:=eraseOne S u (S.f u) (by intro h; exact hvne h))
    (a:=a) (b:=b) (ha:=ha) (hb:=hb)).2 hS'le

/-- S 側のイデアル `A` は，`u` を消去した S′（usingSucc 版）でも
    `A.erase u` がイデアル。 使われている。-/
lemma isOrderIdealOn.erase_usingSucc {α : Type u} [DecidableEq α]
  (S : FuncSetup α) (u : S.Elem) (hvne : S.f u ≠ u)
  {A : Finset α}
  (hA : isOrderIdealOn (S.leOn) S.ground A)
  (hNontriv : S.nontrivialClass u) :
  isOrderIdealOn ((eraseOneUsingSucc S u hNontriv).leOn)
                 (eraseOneUsingSucc S u hNontriv).ground
                 (A.erase u.1) := by
  classical
  -- ground 同定
  have : (eraseOneUsingSucc (S := S) u ?_).ground = S.ground.erase u.1 := rfl
  -- 2 条件を分けて示す
  dsimp [isOrderIdealOn]
  rw [this]
  constructor
  · -- subset
    intro a ha
    have aG : a ∈ S.ground := hA.1 ((Finset.mem_erase.mp ha).2)
    have : a ∈ S.ground.erase u.1 :=
      (Finset.mem_erase).2 ⟨(Finset.mem_erase.mp ha).1, aG⟩
    simp [this]  -- `simp` で `S'` の ground へ
  · -- downward closed on S′
    intro x hx y hy h_yx'
    -- それぞれの情報を展開
    have hx_ne : x ≠ u.1 := (Finset.mem_erase.mp hx).1
    have hxA   : x ∈ A   := (Finset.mem_erase.mp hx).2
    -- S′ の ground を S 側へ
    have hyE : y ∈ S.ground.erase u.1 := by
      simpa [this] using hy
    have hyG : y ∈ S.ground := (Finset.mem_erase.mp hyE).2
    have hxG : x ∈ S.ground := hA.1 hxA
    -- S′.leOn → S.leOn（lift）
    have h_yx : S.leOn y x := by
      apply leOn_lift_S'_to_S_usingSucc (S := S) (u := u) (hvne := hvne)
        (a := y) (b := x)
        (ha := by simpa [this] using hy)
        (hb := by
          have : x ∈ S.ground.erase u.1 :=
            (Finset.mem_erase).2 ⟨hx_ne, hxG⟩
          simp [this] )
      exact h_yx'

    -- S 側の下方閉包で y∈A
    have hyA : y ∈ A := hA.2 (x := x) hxA (y := y) hyG h_yx
    -- かつ y ≠ u
    have hy_ne : y ≠ u.1 := (Finset.mem_erase.mp hyE).1
    -- したがって y ∈ A.erase u
    exact (Finset.mem_erase).2 ⟨hy_ne, hyA⟩
  · exact hNontriv

-- 核心：trace の idealFamily と一致

lemma idealFamily_traceAt_eq_eraseOne {α : Type u} [DecidableEq α]
  (S : FuncSetup α) (u : S.Elem) (hNontriv : S.nontrivialClass u) :
  (eraseOneUsingSucc S u hNontriv).idealFamily
    = Trace.traceAt u.1 (S.idealFamily) := by
  classical
  -- 記号の短縮
  set S' := eraseOneUsingSucc (S := S) u hNontriv
  have hvne : S.f u ≠ u := FuncSetup.f_ne_of_nontrivialClass (S := S) hNontriv

  -- ground は定義計算で一致
  have hground :
      S'.ground = (traceAt u.1 (S.idealFamily)).ground := by
    -- S' の ground は `S.ground.erase u`
    -- traceAt の ground も `F.ground.erase u`
    simp [S', eraseOneUsingSucc, eraseOne, traceAt]
    exact rfl

  -- `sets` の同値を両方向で用意
  have hsets :
    ∀ B : Finset α,
      (S'.idealFamily).sets B ↔ (traceAt u.1 (S.idealFamily)).sets B := by
    intro B
    constructor
    ----------------------------------------------------------------
    -- (→)  S'.idealFamily.sets B → traceAt の定義形へ（∃A, ...）
    ----------------------------------------------------------------
    · -- B が S' のイデアル族なら，A を S のダウンワード閉包で作ると B = A.erase u
      intro hB
      -- S' 側の isOrderIdealOn へ展開
      have hBideal' :
          isOrderIdealOn (S'.leOn) S'.ground B := by
        simpa [S'.sets_iff_isOrderIdeal] using hB
      -- A := { a∈S.ground | ∃ b∈B, S.leOn a b } を構成
      let A : Finset α :=
        S.ground.filter (fun a => ∃ b, b ∈ B ∧ S.leOn a b)
      -- A が S 側の isOrderIdealOn になっていることを示す
      have hAideal :
          isOrderIdealOn (S.leOn) S.ground A := by
        refine And.intro ?Asub ?Adown
        · -- ⊆ ground は filter の定理
          exact Finset.filter_subset _ _
        · -- downward closed
          -- 目標: x∈A → y∈ground → S.leOn y x → y∈A
          intro x hx y hy h_yx
          -- x∈A の意味をほどく
          have hx' : x ∈ S.ground ∧ ∃ b, b ∈ B ∧ S.leOn x b := by
            -- filter の会員判定
            have := (Finset.mem_filter).1 hx
            -- ⟨x∈ground, ∃b...⟩
            simpa using this
          rcases hx' with ⟨hxG, ⟨b, hbB, hxb⟩⟩
          -- S.leOn の推移律
          have hyb : S.leOn y b := by
            exact leOn_trans S h_yx hxb
          -- y を A の定義に入れる（ground は hy）
          -- filter の会員判定を戻す
          have : y ∈ S.ground ∧ ∃ b, b ∈ B ∧ S.leOn y b := ⟨hy, ⟨b, hbB, hyb⟩⟩
          exact (Finset.mem_filter).2 this

      -- A は S の ideal
      have hAsets : (S.idealFamily).sets A := by
        simpa [S.sets_iff_isOrderIdeal] using hAideal

      -- A.erase u = B を示す
      have hAerase_eq_B : A.erase u.1 = B := by
        -- ⊆ と ⊇ の二方向
        ext a
        --apply Finset.Subset.antisymm_iff
        constructor
        · -- ⊆ : a∈A.erase u → a∈B
          intro ha
          -- `a ≠ u ∧ a ∈ A`
          have ha' := (Finset.mem_erase).1 ha
          have hane : a ≠ u.1 := ha'.1
          have haA : a ∈ A := ha'.2
          -- A の定義から b∈B で S.leOn a b がある
          have ha_def :
              a ∈ S.ground ∧ ∃ b, b ∈ B ∧ S.leOn a b :=
            (Finset.mem_filter).1 haA
          rcases ha_def with ⟨haG, ⟨b, hbB, hab⟩⟩
          -- ここから B のダウンワード閉包を使うために，
          -- `S.leOn a b` を S' に移送（a,b は erase-ground 上）
          have ha_in_erase : a ∈ S'.ground := by
            -- S'.ground = S.ground.erase u
            -- `a ≠ u` と `a∈ground` から従う
            have : a ∈ S.ground := haG
            have : a ∈ S.ground.erase u.1 :=
              (Finset.mem_erase).2 ⟨hane, this⟩
            simpa [S', eraseOneUsingSucc, eraseOne]
              using this
          have hb_in_erase : b ∈ S'.ground := by
            -- B ⊆ S'.ground から
            have hBsub : B ⊆ S'.ground :=
              (S'.idealFamily.inc_ground) hB
            exact hBsub hbB
          -- S'.leOn a b （S.leOn → S'.leOn の向き）
          have hab' : S'.leOn a b :=
            leOn_restrict_S_to_S'_usingSucc
              (S := S) (u := u) (hvne := hvne)
              (a := a) (b := b)
              (ha := by
                simpa [S', eraseOneUsingSucc, eraseOne]
                  using ha_in_erase)
              (hb := by
                simpa [S', eraseOneUsingSucc, eraseOne]
                  using hb_in_erase)
              (by exact hab)
          -- B は S' で downward closed
          have hBideal' :
            isOrderIdealOn (S'.leOn) S'.ground B := by
            simpa [S'.sets_iff_isOrderIdeal] using hB
          -- したがって a∈B
          exact hBideal'.2
            (x := b) (y := a)
            (by exact hbB)
            (by exact ha_in_erase)
            (by exact hab')
        · -- ⊇ : b∈B → b∈A.erase u
          intro hbB
          -- B ⊆ S'.ground より b∈ ground.erase
          have hb_in_erase : a ∈ S'.ground :=
            (S'.idealFamily.inc_ground hB) hbB
          -- b ≠ u かつ b∈ground
          have hb_ne_u : a ≠ u.1 := (Finset.mem_erase).1
            (by
              simpa [S', eraseOneUsingSucc, eraseOne]
                using hb_in_erase
            ) |>.1
          have hbG   : a ∈ S.ground := (Finset.mem_erase).1
            (by
              simpa [S', eraseOneUsingSucc, eraseOne]
                using hb_in_erase
            ) |>.2
          -- b∈A：反射律で S.leOn b b
          have hbb : S.leOn a a :=
            S.leOn_refl (x := a) hbG
          have hbA : a ∈ A := by
            -- filter の条件に合う
            apply (Finset.mem_filter).2
            exact ⟨hbG, ⟨a, hbB, hbb⟩⟩
          -- よって b ∈ A.erase u
          exact (Finset.mem_erase).2 ⟨hb_ne_u, hbA⟩

      -- 以上まとめ：traceAt の定義にする
      refine ⟨A, hAsets, ?_⟩
      -- B = A.erase u なので書換え
      exact hAerase_eq_B.symm

    ----------------------------------------------------------------
    -- (←)  traceAt の定義（∃A, ...）から S' 側の ideal を作る
    ----------------------------------------------------------------
    · rintro ⟨A, hAsets, rfl⟩
      -- A.erase u が S' の isOrderIdealOn であることを示す
      -- S 側 ideal へ展開
      have hAideal :
          isOrderIdealOn (S.leOn) S.ground A := by
        simpa [S.sets_iff_isOrderIdeal] using hAsets

      -- 目標：isOrderIdealOn (S'.leOn) S'.ground (A.erase u.1)
      have hIdeal' :
          isOrderIdealOn (S'.leOn) S'.ground (A.erase u.1) := by
        exact isOrderIdealOn.erase_usingSucc S u hvne hAsets hNontriv

      -- S' 側の sets に戻す
      simpa [S'.sets_iff_isOrderIdeal] using hIdeal'

  -- ここまでで `ground` と `sets` の「外延的一致」は得られた。
  -- 残りは構造の等式へまとめる（decSets/inc_ground は証明項なので自動で一致させられる）。
  -- もし `SetFamily.ext`（ground と sets の一致から等しい）があればそれを使って終わりです。
  -- なければ，下の一行を `sorry` から置き換えてください：
  --   `refine SetFamily.ext ?_ ?_`
  --   あるいは両辺を `cases` してフィールドごとに `simp`/`funext`/`propext` で埋めます。
  --
  -- ground：`hground`， sets：`funext (λ B => propext (hsets B))`
  -- で閉じます。
  apply SetFamily.ext hground (funext (λ B => propext (hsets B)))
  show S'.idealFamily.decSets ≍ (traceAt (↑u) S.idealFamily).decSets
  have h_sets : S'.idealFamily.sets = (traceAt (↑u) S.idealFamily).sets := funext (λ B => propext (hsets B))
  exact
    Subsingleton.helim (congrArg DecidablePred h_sets) S'.idealFamily.decSets
      (traceAt (↑u) S.idealFamily).decSets

--上の補題の書き換え。
/-- 使い勝手の良い “存在形” の再掲（既存の `traced_is_functional_family` を置換）。 -/
--定理名に反して、functionalまで示せてなくて、traceが単にidealFamilyであることを示している。
lemma traced_is_functional_family {α : Type u} [DecidableEq α]
    (S : SPO.FuncSetup α) (u : S.Elem)
    (hNontriv : SPO.FuncSetup.nontrivialClass S u) :
    ∃ S' : SPO.FuncSetup α,
      S'.idealFamily = Trace.traceAt u.1 (S.idealFamily) := by
  let eous := eraseOneUsingSucc (α := α) (S := S) u hNontriv
  let iftee := idealFamily_traceAt_eq_eraseOne (S := S) (u := u) (hNontriv := hNontriv)
  use eous

-----ここから不要-----

---使われてないっぽい。
lemma rtg_inclErase_to_foldMap_usingSucc
  (S : FuncSetup α) (u : S.Elem) (hvne : S.f u ≠ u)
  (x : {a // a ∈ S.ground.erase u.1}) :
  Relation.ReflTransGen
    (stepRel (eraseOneMap S u (S.f u) (by intro h; exact hvne h)))
    x (foldMap (S := S) (u := u) (hvne := hvne) (inclErase S u x)) := by
  -- foldMap (inclErase x) = x を取り出してゴールを書き換え
  have hx : foldMap (S := S) (u := u) (hvne := hvne) (inclErase S u x) = x :=
    foldMap_inclErase (S := S) (u := u) (hvne := hvne) x
  -- 右辺を書き換え
  -- これでゴールは `x ⟶* x` になり，`refl` で終了
  -- （`cases hx` だと依存パターンで怒られることがあるので `rw` を使う）
  -- ただしゴールは命題なので `rw` が素直に効く
  -- 右辺を x に置換
  simp_all only [foldMap_inclErase]
  rfl

/-
-- 必要と思ったが使ってないみたい。証明もできてないしコメントアウト。
lemma leOn_restrict_S_to_S'
  (S : FuncSetup α) (u v : S.Elem) (hvne : v ≠ u)
  {a b : α} (ha : a ∈ S.ground.erase u.1) (hb : b ∈ S.ground.erase u.1) :
  S.leOn a b → (eraseOne S u v hvne).leOn a b := by
  intro hab
  -- ground 側に戻す
  have haG : a ∈ S.ground := (Finset.mem_erase.mp ha).2
  have hbG : b ∈ S.ground := (Finset.mem_erase.mp hb).2
  -- S での le
  have hSle : S.le ⟨a, haG⟩ ⟨b, hbG⟩ :=
    (leOn_iff_subtype (S := S) (a := a) (b := b) (ha := haG) (hb := hbG)).1 hab
  -- S の RTG
  have hrtg_S : Relation.ReflTransGen (stepRel S.f) ⟨a, haG⟩ ⟨b, hbG⟩ :=
    rtg_of_le (S := S) hSle
  -- S′ の RTG（usingSucc）
  have hrtg_S' :
      Relation.ReflTransGen (stepRel (eraseOneMap S u v hvne))
        ⟨a, ha⟩ ⟨b, hb⟩ :=
    by
      -- 端点を inclErase で揃えてから持ち上げ
      -- `inclErase S u ⟨a,ha⟩ = ⟨a,haG⟩`，`inclErase S u ⟨b,hb⟩ = ⟨b,hbG⟩`
      -- を使って `rtg_S_to_S'_usingSucc` へ
      -- まず usingSucc 版の補題を適用するために形を合わせる：
      let rsts :=  rtg_S_to_S'_usingSucc (S := S) (u := u)
      sorry

          -- `hvne : v ≠ u` が必要だが usingSucc では v = S.f u を入れるので，
          -- この行の `rtg_S_to_S'_usingSucc` は「v = S.f u」版を使うのが自然。
          -- もし v を S.f u に特化するなら，上で (eraseOne S u (S.f u) …) にして使ってください。
          -- ここでは抽象 v 版を使う別補題があるならそれを使ってください。
          -- （プロジェクト側の定義に合わせて置換を。）
          -- 便宜上ここは usingSucc 版を使う想定で、v = S.f u に specialize するのが一番楽です。
          -- したがって、上の lemmata 群は usingSucc 版で統一することをお勧めします。

        --  (x := ⟨a, ha⟩) (y := ⟨b, hb⟩) ?_
  -- ↑ 上の `admit` は「usingSucc 版」に寄せれば不要になります：
  --   つまりこの補題自体を (eraseOne S u (S.f u) …) 版に書き換えるのが素直です。
  --   その場合、直前の hrtg_S' の行はそのまま `rtg_S_to_S'_usingSucc … hrtg_S` で OK です。
  -- RTG → le（S′）
  have hS'le : (eraseOne S u v hvne).le ⟨a, ha⟩ ⟨b, hb⟩ :=
    le_of_rtg (S := eraseOne S u v hvne) hrtg_S'
  -- subtype から leOn へ
  exact (leOn_iff_subtype (S := eraseOne S u v hvne)
          (a := a) (b := b) (ha := ha) (hb := hb)).2 hS'le
-/


/-- **RTG 版**：S′ の到達可能性は，S に落ちる（`v = S.f u`） -/
--多分いらないと思ったけど、leOn_restrict_S'_to_S_usingSuccで使っている。
lemma rtg_S'_to_S_usingSucc
  (S : FuncSetup α) (u v : S.Elem) (hvne : v ≠ u) (hv : v = S.f u)
  {x y : {a // a ∈ S.ground.erase u.1}}
  (h : Relation.ReflTransGen (stepRel (eraseOneMap S u v hvne)) x y) :
  Relation.ReflTransGen (stepRel (fun z : S.Elem => S.f z))
      (inclErase S u x) (inclErase S u y) := by
  -- `head_induction_on` で 1 歩補題を繰り返すだけ
  refine Relation.ReflTransGen.head_induction_on h ?base ?step
  · -- refl
    exact Relation.ReflTransGen.refl
  · intro p q hpq hqr ih
    -- p ⟶ q（S′ の 1 歩）を S に落とす
    have h1 :
      Relation.ReflTransGen (stepRel (fun z : S.Elem => S.f z))
        (inclErase S u p) (inclErase S u q) :=
      step_S'_to_S_usingSucc (S := S) (u := u) (v := v) (hvne := hvne) (hv := hv) hpq
    -- 連結
    exact Relation.ReflTransGen.trans h1 ih

--不要か必要か微妙なもの。

/-! ## C) `leOn` の S′→S 移送（`eraseOneUsingSucc` 用） -/

/-- `eraseOneUsingSucc` を使った S′ の `leOn` は S の `leOn` へ（端点が `ground.erase u` のとき） -/
--多分いらないtと思ったけど必要な可能性が出てきた。でも必要なものは、S'_to_Sでなくて、S_to_S'かも。
lemma leOn_restrict_S'_to_S_usingSucc {α : Type u}
  (S : FuncSetup α) (u : S.Elem) (hNontriv : S.nontrivialClass u)
  {a b : α} (ha : a ∈ S.ground.erase u.1) (hb : b ∈ S.ground.erase u.1) :
  (eraseOneUsingSucc (S := S) u hNontriv).leOn a b → S.leOn a b := by
  intro h'
  -- 記号短縮
  set S' := eraseOneUsingSucc (S := S) u hNontriv
  -- a,b の ground 証明（S 側）
  have haG : a ∈ S.ground := (Finset.mem_erase.mp ha).2
  have hbG : b ∈ S.ground := (Finset.mem_erase.mp hb).2
  -- S′ 側の ground 証明（`erase` 側）
  have haE : a ∈ S'.ground := by
    -- S'.ground = S.ground.erase u.1
    -- 定義から rfl のはずですが，明示に置換
    change a ∈ S.ground.erase u.1
    exact ha
  have hbE : b ∈ S'.ground := by
    change b ∈ S.ground.erase u.1
    exact hb

  -- `leOn_iff_subtype` で S′.le を取り出す
  have hS'le : S'.le ⟨a, haE⟩ ⟨b, hbE⟩ :=
    (leOn_iff_subtype (S := S') (a := a) (b := b) (ha := haE) (hb := hbE)).1 h'

  -- S′.le → S′ の RTG
  have hrtg_S' :
      Relation.ReflTransGen (stepRel S'.f) ⟨a, haE⟩ ⟨b, hbE⟩ :=
    rtg_of_le (S := S') hS'le

  -- S′.f は `eraseOneMap S u (S.f u)` なので，先の RTG 落としを使う
  have hvne : (S.f u) ≠ u :=
    FuncSetup.f_ne_of_nontrivialClass (S := S) hNontriv
  have hdrop :
      Relation.ReflTransGen (stepRel (fun z : S.Elem => S.f z))
        (inclErase S u ⟨a, ha⟩) (inclErase S u ⟨b, hb⟩) :=
    rtg_S'_to_S_usingSucc (S := S) (u := u) (v := S.f u)
      (hvne := by
        intro h;
        exact hvne h
        )
      (hv := rfl)
      (x := ⟨a, ha⟩) (y := ⟨b, hb⟩) hrtg_S'

  -- `inclErase` は just サブタイプ化なので，値で潰す
  have hdrop' :
      Relation.ReflTransGen (stepRel (fun z : S.Elem => S.f z))
        ⟨a, haG⟩ ⟨b, hbG⟩ := by
    -- `inclErase S u ⟨a,ha⟩ = ⟨a,haG⟩`（値は同じ）
    -- 同様に b も
    -- 直接置換で十分
    exact hdrop

  -- RTG → S.le，そして `leOn` に戻す
  have hSle : S.le ⟨a, haG⟩ ⟨b, hbG⟩ := by
    exact hdrop
  exact (leOn_iff_subtype (S := S) (a := a) (b := b) (ha := haG) (hb := hbG)).2 hSle


/-- `eraseOneMap` の値は常に `u.1` と異なる（出力は `ground.erase u`） -/
--必要性不明。多分いらない。使われてない。
lemma eraseOneMap_ne_u
  (S : FuncSetup α) (u v : S.Elem) (hvne : v ≠ u)
  (x : {x // x ∈ S.ground.erase u.1}) :
  (eraseOneMap S u v hvne x).1 ≠ u.1 := by
  classical
  dsimp [eraseOneMap, inclErase]
  by_cases hyu : S.f ⟨x.1, (Finset.mem_erase.mp x.2).2⟩ = u
  · -- then：値は v.1。v ≠ u より v.1 ≠ u.1
    intro hval
    have hvval : v.1 ≠ u.1 := by
      intro h'
      apply hvne
      apply Subtype.ext
      exact h'
    apply hvval
    simp_all only [↓reduceDIte]
  · -- else：値は y.1。y ≠ u だから y.1 ≠ u.1
    intro hval
    apply hyu
    -- 値の等式からサブタイプの等式へ
    apply Subtype.ext
    simp_all only [↓reduceDIte]

--多分いらない。不要なもので使われているだけ。
lemma step_S_to_S'
  (S : FuncSetup α) (u v : S.Elem) (hvne : v ≠ u)
  {x y : {a // a ∈ S.ground.erase u.1}}
  (h : stepRel (fun z : S.Elem => S.f z) (inclErase S u x) (inclErase S u y)) :
  Relation.ReflTransGen (stepRel (eraseOneMap S u v hvne)) x y := by
  classical
  -- stepRel の定義は「=」なので、値の等式を得る
  -- h : S.f (inclErase x) = inclErase y
  -- このとき `S.f (inclErase x) = u` は矛盾（右辺は y で、y ∈ erase）
  have hyu_false : S.f (inclErase S u x) ≠ u := by
    intro h'
    -- h とあわせると `inclErase y = u`
    have : inclErase S u y = u := by
      -- `h` は等式なので直接
      -- `h'.trans ?` の形で良いが、書き下しで
      -- S.f (inclErase x) = incl y かつ S.f (inclErase x) = u
      -- よって `incl y = u`
      -- 値に写す
      have := congrArg (fun z : S.Elem => z) h
      -- 同型的に扱ってよいので
      simp_all only [ne_eq]

    -- しかし y は erase に属するので値が違う
    have : y.1 = u.1 := congrArg Subtype.val this
    have hy_ne : y.1 ≠ u.1 := (Finset.mem_erase.mp y.2).1
    exact hy_ne this
  -- よって `eraseOneMap` は else 分岐で y へ送る
  -- すなわち 1 ステップで `x ⟶ y`
  have hstep : stepRel (eraseOneMap S u v hvne) x y := by
    -- 値成分で示す：`S.eraseOneMap u v hvne x = y`
    -- 先に値を計算
    -- `eraseOneMap_spec` の else ケース
    have : (eraseOneMap S u v hvne x).1 = (inclErase S u y).1 := by
      -- `h` から `(S.f (inclErase x)).1 = (inclErase y).1`
      have hval : (S.f (inclErase S u x)).1 = (inclErase S u y).1 :=
        congrArg Subtype.val h
      -- spec（else）
      have hspec :=
        eraseOneMap_spec (S := S) (u := u) (v := v) (hvne := hvne) x
      -- else ケースを取り出す
      -- `let y := ...` を書換え
      change
        (if _ then (eraseOneMap S u v hvne x).1 = v.1
         else (eraseOneMap S u v hvne x).1 = (S.f (inclErase S u x)).1) at hspec
      -- else に落ちる（`hyu_false`）
      have hspec' :
        (eraseOneMap S u v hvne x).1 = (S.f (inclErase S u x)).1 := by
        -- if_false で潰す
        simp_all only [ne_eq, inclErase_val, ↓reduceIte]

      -- 合成
      exact Eq.trans hspec' hval
    -- 値が等しいのでサブタイプとして等しい
    apply Subtype.ext
    -- `inclErase_val`
    have : (inclErase S u y).1 = y.1 := rfl
    apply Eq.trans
    · (expose_names; exact this_1)
    · exact this

  -- 1 歩の RTG
  apply Relation.ReflTransGen.tail
  · exact Relation.ReflTransGen.refl
  · exact hstep




/- **RTG 版**：S の到達可能性は S′ に持ち上がる（hvne のみ必要）。 -/
/-多分いらない
lemma rtg_S_to_S'
  (S : FuncSetup α) (u v : S.Elem) (hvne : v ≠ u)
  {x y : {a // a ∈ S.ground.erase u.1}}
  (h : Relation.ReflTransGen (stepRel (fun z : S.Elem => S.f z))
        (inclErase S u x) (inclErase S u y)) :
  Relation.ReflTransGen (stepRel (eraseOneMap S u v hvne)) x y := by
  -- RTG を 1 歩補題で伸ばすだけ
  refine Relation.ReflTransGen.head_induction_on h ?base ?step
  · show Relation.ReflTransGen (stepRel (eraseOneMap S u v hvne)) x y
    --#check stepRel (eraseOneMap S u v hvne)
    --stepRel (eraseOneMap S u v hvne) : { x // x ∈ S.ground.erase ↑u } → { x // x ∈ S.ground.erase ↑u } → Prop
    refine step_S_to_S' S u v hvne ?_
    dsimp [stepRel]
    revert h
    show Relation.ReflTransGen (stepRel fun z => S.f z) (inclErase S u x) (inclErase S u y) →
  S.f (inclErase S u x) = inclErase S u y
    intro h
    --h:Relation.ReflTransGen (stepRel fun z => S.f z) (inclErase S u x) (inclErase S u y)
    -- `inclErase S u x` の値を使って `S.f` の値を取り出す

    have hval : S.f (inclErase S u x) = inclErase S u y := by
      -- `h` は stepRel の定義なので、値の等式を得る
      sorry

    -- したがって else 分岐で y へ送る
    exact hval

  · intro p q hpq hqr ih
    simp_all only
-/

/-
/-! ## 2) `leOn` の両方向：eraseOneUsingSucc では同値（restricted で一致） -/
/-- 1歩補題：S′ で `x ⟶ foldMap (inclErase x)` が成り立つ（usingSucc 版）。 -/
-- 新しい証明で不要に？証明も未完。
lemma step_inclErase_to_foldMap_usingSucc
  (S : FuncSetup α) (u : S.Elem) (hvne : S.f u ≠ u)
  (x : {a // a ∈ S.ground.erase u.1}) :
  stepRel (eraseOneMap S u (S.f u) (by intro h; exact hvne h))
    x (foldMap (S := S) (u := u) (hvne := hvne) (inclErase S u x)) := by
  classical
  -- 定義展開して場合分け
  dsimp [stepRel, eraseOneMap, foldMap]
  -- `h : S.f (inclErase S u x) = u` か否か
  by_cases hxu : S.f (inclErase S u x) = u
  · -- then 分岐：両方とも (S.f u) を返す
    -- 値成分は一致（証明部は `mem_erase` で供給）
    apply Subtype.ext -- 値の等式で十分
    -- hxu : S.f (inclErase S u x) = u
    --show ↑(if hyu : S.f ⟨↑x, ⋯⟩ = u then ⟨↑(S.f u), ⋯⟩ else ⟨↑(S.f ⟨↑x, ⋯⟩), ⋯⟩) =↑(if hz : inclErase S u x = u then ⟨↑(S.f u), ⋯⟩ else ⟨↑x, ⋯⟩)
    sorry

  · -- else 分岐：両方とも `S.f (inclErase x)` を返す
    apply Subtype.ext
    simp

    --show ↑(if hyu : S.f ⟨↑x, ⋯⟩ = u then ⟨↑(S.f u), ⋯⟩ else ⟨↑(S.f ⟨↑x, ⋯⟩), ⋯⟩) = ↑(if inclErase S u x = u then ⟨↑(S.f u), ⋯⟩ else x)
    sorry
-/

/-
/-- **同値版**：`eraseOneUsingSucc` では `ground.erase u` 上で `leOn` が一致。 -/
--tukawanaikamo.
lemma leOn_restrict_eq_usingSucc
  (S : FuncSetup α) (u : S.Elem) (hNontriv : S.nontrivialClass u)
  {a b : α} (ha : a ∈ S.ground.erase u.1) (hb : b ∈ S.ground.erase u.1) :
  (eraseOneUsingSucc (S := S) u hNontriv).leOn a b ↔ S.leOn a b := by
  constructor
  · -- S′ → S （既出の補題）
    intro h
    exact leOn_restrict_S'_to_S_usingSucc (S := S) (u := u) (hNontriv := hNontriv) ha hb h
  · -- S → S′ （一般の持ち上げを `v = S.f u` に適用）
    intro h
    -- 記号短縮
    set S' := eraseOneUsingSucc (S := S) u hNontriv
    have hvne : (S.f u) ≠ u :=
      FuncSetup.f_ne_of_nontrivialClass (S := S) hNontriv
    -- 上の一般補題を v := S.f u に適用
    have : (eraseOne S u (S.f u)
              (by intro h; exact hvne h)).leOn a b :=
      leOn_restrict_S_to_S' (S := S) (u := u) (v := S.f u)
        (hvne := by intro h; exact hvne h) ha hb h
    -- S' と一致なのでそのまま
    exact this
-/





end AvgRare.SPO
