import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.Order.GroupWithZero.Unbundled.Defs
import AvgRare.Basics.SetFamily
import AvgRare.Basics.SetTrace
import AvgRare.Functional.FuncSetup


universe u
open Classical

open scoped BigOperators

namespace AvgRare
namespace FuncSetup

variable {α : Type u} [DecidableEq α] (S : FuncSetup α)


--functionalのtraceは、functionalというもの
--theorem  traced_is_functional_family
--The only theorem is cited from that.

-- One direction of "k iteration = reachable"
private lemma rtg_of_iter (S : FuncSetup α) (x : S.Elem) (k : ℕ) :
    Relation.ReflTransGen (stepRel S.f) x (S.iter k x) := by

  have h : Relation.ReflTransGen (stepRel S.f) x (S.iter k x) :=
    (reflTransGen_iff_exists_iterate (S.f)).2 ⟨k, rfl⟩
  exact h

-- A minimum version that simply uses the existing lema of le ↔ ∃k.iter to le → RTG
--For some reason, {α} is required.If not, le_iff_exists_iter error in S x z.
--It is used.
private lemma rtg_of_le {α : Type u} [DecidableEq α] (S : FuncSetup α) {x z : S.Elem} (hxz : S.le x z) :
    Relation.ReflTransGen (stepRel S.f) x z := by
  rcases (le_iff_exists_iter S x z).1 hxz with ⟨k, hk⟩
  have hxiter : Relation.ReflTransGen (stepRel S.f) x (S.iter k x) :=
    rtg_of_iter S x k
  have := congrArg (fun t => Relation.ReflTransGen (stepRel S.f) x t) hk
  cases hk
  exact hxiter

private lemma le_of_rtg {α} [DecidableEq α] (S : FuncSetup α) {x z : S.Elem}
  (h : Relation.ReflTransGen (stepRel S.f) x z) : S.le x z := by
  rcases (reflTransGen_iff_exists_iterate (S.f)).1 h with ⟨k, hk⟩
  exact (le_iff_exists_iter S x z).2 ⟨k, hk⟩

noncomputable def eraseOneMap
    (u v : {a // a ∈ S.ground}) (hvne : v ≠ u) :
    {x // x ∈ S.ground.erase u.1} → {y // y ∈ S.ground.erase u.1} :=
  fun x => by
    classical
    have hx_in_ground : x.1 ∈ S.ground := (Finset.mem_erase.mp x.2).2
    let y : {a // a ∈ S.ground} := S.f ⟨x.1, hx_in_ground⟩
    by_cases hyu : y = u
    ·
      have hv_val_ne : v.1 ≠ u.1 := by
        intro hval
        apply hvne
        apply Subtype.ext
        exact hval
      have hv_in_erase : v.1 ∈ S.ground.erase u.1 := by
        -- mem_erase ↔ (≠ ∧ ∈)
        exact Finset.mem_erase.mpr ⟨hv_val_ne, v.2⟩
      exact ⟨v.1, hv_in_erase⟩
    · have hy_val_ne : y.1 ≠ u.1 := by
        intro hval
        apply hyu
        apply Subtype.ext
        exact hval
      have hy_in_erase : y.1 ∈ S.ground.erase u.1 := by
        exact Finset.mem_erase.mpr ⟨hy_val_ne, y.2⟩
      exact ⟨y.1, hy_in_erase⟩

/-- ground.erase u → ground の包含 。使われている。-/
noncomputable def inclErase (S : FuncSetup α) (u : S.Elem) :
  {x // x ∈ S.ground.erase u.1} → S.Elem :=
fun x => ⟨x.1, (Finset.mem_erase.mp x.2).2⟩

--少し使われている。
@[simp] lemma inclErase_val (S : FuncSetup α) (u : S.Elem) (x) :
  (inclErase S u x).1 = x.1 := rfl

/-- `inclErase` の像は明らかに `ground` 上。値で十分なときに便利。でも結果的に使われてない。-/
--@[simp] lemma inclErase_property (S : FuncSetup α) (u : S.Elem) (x : {x // x ∈ S.ground.erase u.1}) :
--  (inclErase S u x).2 = (Finset.mem_erase.mp x.2).2 := rfl

/- `eraseOneMap` の分岐仕様 -/
--使われている。
private lemma eraseOneMap_spec
  (S : FuncSetup α) (u v : S.Elem) (hvne : v ≠ u)
  (x : {x // x ∈ S.ground.erase u.1}) :
  let y := S.f (inclErase S u x)
  if _ : y = u
  then (eraseOneMap S u v hvne x).1 = v.1
  else (eraseOneMap S u v hvne x).1 = y.1 := by
  classical
  dsimp [eraseOneMap, inclErase]
  by_cases hyu : S.f ⟨x.1, (Finset.mem_erase.mp x.2).2⟩ = u
  ·
    simp_all only [↓reduceIte, ↓reduceDIte]
  ·
    simp_all only [↓reduceIte, ↓reduceDIte]

/-- Under `v = S.f u`, one step of S' can be restored to one or two steps in S. -/
private lemma step_S'_to_S_usingSucc
  (S : FuncSetup α) (u v : S.Elem) (hvne : v ≠ u) (hv : v = S.f u)
  {x y : {a // a ∈ S.ground.erase u.1}}
  (h : stepRel (eraseOneMap S u v hvne) x y) :
  Relation.ReflTransGen (stepRel (fun z : S.Elem => S.f z))
      (inclErase S u x) (inclErase S u y) := by
  classical
  by_cases hyu : S.f (inclErase S u x) = u
  ·
    have h1 : stepRel (fun z : S.Elem => S.f z) (inclErase S u x) u := by
      exact hyu
    have h2 : stepRel (fun z : S.Elem => S.f z) u v := by
      -- `S.f u = v`
      exact Eq.symm hv
    have hval_y :
      y.1 = v.1 := by
        have hval : (eraseOneMap S u v hvne x).1 = y.1 :=
          congrArg Subtype.val h

        have : (eraseOneMap S u v hvne x).1 = v.1 := by

          dsimp [eraseOneMap]
          split
          next h_1 => simp_all only
          next h_1 =>
            simp_all only
            contradiction
        exact Eq.trans (Eq.symm hval) this

    have hv_y : inclErase S u y = v := by
      apply Subtype.ext
      exact hval_y

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

    cases hv_y
    exact hx_to_v
  ·
    have hval :
        (S.f (inclErase S u x)).1 = (inclErase S u y).1 := by
      have h' : (eraseOneMap S u v hvne x).1 = y.1 :=
        congrArg Subtype.val h
      have hspec :=
        eraseOneMap_spec (S := S) (u := u) (v := v) (hvne := hvne) x
      exact Eq.trans (by subst hv;simp_all only [↓reduceDIte]) h'
    have hstep : stepRel (fun z : S.Elem => S.f z)
        (inclErase S u x) (inclErase S u y) := by
      apply Subtype.ext
      exact hval
    apply Relation.ReflTransGen.tail
    · exact Relation.ReflTransGen.refl
    · exact hstep

-- Replace `f` using the `eraseOneMap` definition.eraseOneMap only supports mapping, but this is FuncSetup.
--Not used outside of this file.
noncomputable def eraseOne (u v : {a // a ∈ S.ground}) (hvne : v ≠ u) : FuncSetup α :=
{ ground := S.ground.erase u.1
  nonempty := by
        have : v.1 ∈ S.ground.erase u.1 := by
          apply Finset.mem_erase.mpr
          simp_all only [ne_eq, Finset.coe_mem, and_true]
          exact Subtype.coe_ne_coe.mpr hvne
        exact ⟨v, this⟩
  f      := eraseOneMap S u v hvne }

--FuncSetup's trace support is limited to those with parallel partners.
noncomputable def eraseOneUsingSucc (u : S.Elem)
    (hNontriv : S.nontrivialClass u) : FuncSetup α :=
  eraseOne S u (S.f u)
    (FuncSetup.f_ne_of_nontrivialClass (S := S) hNontriv)

/-- `foldMap S u hvne z`：
  `z = u` なら `S.f u` に，そうでなければ `z` 自身を `ground.erase u` 上に埋め込む。 -/
noncomputable def foldMap
  (S : FuncSetup α) (u : S.Elem) (hvne : S.f u ≠ u)
  (z : S.Elem) : {a // a ∈ S.ground.erase u.1} :=
by
  classical
  by_cases hz : z = u
  ·
    refine ⟨(S.f u).1, ?_⟩
    -- (S.f u).1 ∈ ground.erase u.1
    have hval_ne : (S.f u).1 ≠ u.1 := by
      intro h
      apply hvne
      apply Subtype.ext
      exact h
    exact Finset.mem_erase.mpr ⟨hval_ne, (S.f u).2⟩
  ·
    refine ⟨z.1, ?_⟩
    have hval_ne : z.1 ≠ u.1 := by

      have : (z : α) ≠ (u : α) := S.coe_ne_of_ne hz
      exact this
    exact Finset.mem_erase.mpr ⟨hval_ne, z.2⟩

/-- `foldMap` を戻すと：
    `z ≠ u` なら `inclErase (foldMap z) = z`，
    `z = u` なら `inclErase (foldMap z) = S.f u`。 -/
private lemma inclErase_foldMap
  (S : FuncSetup α) (u : S.Elem) (hvne : S.f u ≠ u) (z : S.Elem) :
  (inclErase S u (foldMap (S := S) (u := u) (hvne := hvne) z))
    = (if  z = u then S.f u else z) := by
  classical
  by_cases hz : z = u
  · -- then
    subst hz
    exact
      apply_dite (inclErase S z) (z = z) (fun hz => ⟨↑(S.f z), foldMap._proof_1 S z hvne⟩) fun hz =>
        ⟨↑z, foldMap._proof_2 S z z hz⟩
  ·
    have : (inclErase S u (foldMap (S := S) (u := u) (hvne := hvne) z)).1 = z.1 := by
      simp_all only [inclErase_val]
      simp [foldMap, hz]
    exact
      apply_dite (inclErase S u) (z = u) (fun hz => ⟨↑(S.f u), foldMap._proof_1 S u hvne⟩) fun hz =>
        ⟨↑z, foldMap._proof_2 S u z hz⟩

/-- `x : ground.erase u` に対しては常に `foldMap (inclErase x) = x`。 -/
@[simp] lemma foldMap_inclErase
  (S : FuncSetup α) (u : S.Elem) (hvne : S.f u ≠ u)
  (x : {a // a ∈ S.ground.erase u.1}) :
  foldMap (S := S) (u := u) (hvne := hvne) (inclErase S u x) = x := by
  classical
  have hne : (inclErase S u x) ≠ u := by
    intro h
    have : x.1 = u.1 := congrArg Subtype.val h
    exact (Finset.mem_erase.mp x.2).1 this
  have hback :
      inclErase S u (foldMap (S := S) (u := u) (hvne := hvne) (inclErase S u x))
        = inclErase S u x := by
    -- if_false
    have := inclErase_foldMap (S := S) (u := u) (hvne := hvne) (z := inclErase S u x)
    simp_all only [ne_eq]
    exact rfl
  apply Subtype.ext
  simp_all only [ne_eq]
  obtain ⟨val_1, property_1⟩ := x
  simp_all only
  exact congr_arg Subtype.val hback

/-- 1 歩版（`v = S.f u`）：`S.f p = q` から
    `foldMap p ⟶* foldMap q`（S′ の `eraseOneMap`） -/
private lemma step_map_S_to_S'_usingSucc
  (S : FuncSetup α) (u : S.Elem) (hvne : S.f u ≠ u)
  {p q : S.Elem} (hpq : stepRel (fun z : S.Elem => S.f z) p q) :
  Relation.ReflTransGen (stepRel (eraseOneMap S u (S.f u)
    (by intro h; exact hvne h)))
      (foldMap (S := S) (u := u) (hvne := hvne) p)
      (foldMap (S := S) (u := u) (hvne := hvne) q) := by
  classical
  by_cases hpu : p = u
  ·
    have hq : q = S.f u := by
      apply Eq.trans (Eq.symm hpq)
      exact congrArg S.f hpu
    have hEq :
        foldMap (S := S) (u := u) (hvne := hvne) p
      = foldMap (S := S) (u := u) (hvne := hvne) q := by
      cases hpu
      cases hq
      apply Subtype.ext
      dsimp [foldMap]
      simp_all only [↓reduceDIte]

    subst hq hpu
    simp_all only
    obtain ⟨val, property⟩ := p
    simp_all only
    rfl

  ·
    have hincl_p :
        inclErase S u (foldMap (S := S) (u := u) (hvne := hvne) p) = p :=
      by
        have := inclErase_foldMap (S := S) (u := u) (hvne := hvne) (z := p)
        simp_all only
        exact rfl
    have hfp : S.f p = q := hpq
    have hstep :
      stepRel (eraseOneMap S u (S.f u)
          (by intro h; exact hvne h))
        (foldMap (S := S) (u := u) (hvne := hvne) p)
        (foldMap (S := S) (u := u) (hvne := hvne) q) := by
      apply Subtype.ext
      have h_incl : inclErase S u (foldMap (S := S) (u := u) (hvne := hvne) p) = p := hincl_p
      by_cases hqu : q = u
      ·
        have : (eraseOneMap S u (S.f u)
                  (by intro h; exact hvne h)
                (foldMap (S := S) (u := u) (hvne := hvne) p)).1
              = (S.f u).1 := by

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
          cases hqu
          dsimp [foldMap]
          subst hfp
          simp_all only [↓reduceDIte]
        apply Eq.trans
        · (expose_names; exact this_1)
        · exact id (Eq.symm this)

      ·
        dsimp [eraseOneMap]
        dsimp [foldMap]
        simp_all only [↓reduceDIte]

    apply Relation.ReflTransGen.tail
    · --show Relation.ReflTransGen (stepRel (eraseOneMap S u (S.f u) ⋯)) (foldMap S u hvne p) ?neg.b✝
      exact Relation.ReflTransGen.refl
    · dsimp [stepRel]
      exact hstep

--必要な補題
private lemma map_rtg_foldMap_usingSucc
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

/--  目的の補題：`inclErase x ⟶* inclErase y` を新世界で `x ⟶* y` に移送 -/
private lemma rtg_S_to_S'_usingSucc
  (S : FuncSetup α) (u : S.Elem) (hvne : S.f u ≠ u)
  {x y : {a // a ∈ S.ground.erase u.1}}
  (h : Relation.ReflTransGen (stepRel (fun z : S.Elem => S.f z))
        (inclErase S u x) (inclErase S u y)) :
  Relation.ReflTransGen (stepRel (eraseOneMap S u (S.f u)
    (by intro h; exact hvne h))) x y := by
  classical
  have mapped :
    Relation.ReflTransGen (stepRel (eraseOneMap S u (S.f u)
      (by intro h; exact hvne h)))
      (foldMap (S := S) (u := u) (hvne := hvne) (inclErase S u x))
      (foldMap (S := S) (u := u) (hvne := hvne) (inclErase S u y)) :=
    map_rtg_foldMap_usingSucc (S := S) (u := u) (hvne := hvne) h
  have hx := foldMap_inclErase (S := S) (u := u) (hvne := hvne) x
  have hy := foldMap_inclErase (S := S) (u := u) (hvne := hvne) y
  simpa [hx, hy] using mapped

/-- (a) usingSucc 版：S′ の RTG を S の RTG に持ち上げる。使われている -/
private lemma map_rtg_S'_to_S_usingSucc
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
    have one :
      Relation.ReflTransGen (stepRel (fun z : S.Elem => S.f z))
        (inclErase S u p) (inclErase S u q) :=
      step_S'_to_S_usingSucc
        (S := S) (u := u) (v := S.f u)
        (hvne := by intro h; exact hvne h) (hv := rfl) hpq
    exact Relation.ReflTransGen.trans one ih

/-- (b) usingSucc 版：`S'.leOn a b → S.leOn a b`。 使われている-/
private lemma leOn_lift_S'_to_S_usingSucc {α : Type u} [DecidableEq α]
  (S : FuncSetup α) (u : S.Elem) (hvne : S.f u ≠ u)
  {a b : α} (ha : a ∈ S.ground.erase u.1) (hb : b ∈ S.ground.erase u.1) :
  (eraseOne S u (S.f u) (by intro h; exact hvne h)).leOn a b → S.leOn a b := by
  intro h'
  have hS'le :
      (eraseOne S u (S.f u) (by intro h; exact hvne h)).le ⟨a, ha⟩ ⟨b, hb⟩ :=
    (leOn_iff_subtype
      (S := eraseOne S u (S.f u) (by intro h; exact hvne h))
      (a := a) (b := b) (ha := ha) (hb := hb)).1 h'

  have hrtg_S' :
      Relation.ReflTransGen
        (stepRel (eraseOneMap S u (S.f u) (by intro h; exact hvne h)))
        ⟨a, ha⟩ ⟨b, hb⟩ :=
    rtg_of_le (S := eraseOne S u (S.f u) (by intro h; exact hvne h)) hS'le

  have hrtg_S :
      Relation.ReflTransGen (stepRel S.f)
        (inclErase S u ⟨a, ha⟩) (inclErase S u ⟨b, hb⟩) :=
    map_rtg_S'_to_S_usingSucc (S := S) (u := u) (hvne := hvne) hrtg_S'

  have haG : a ∈ S.ground := (Finset.mem_erase.mp ha).2
  have hbG : b ∈ S.ground := (Finset.mem_erase.mp hb).2
  have : Relation.ReflTransGen (stepRel S.f) ⟨a, haG⟩ ⟨b, hbG⟩ := by
    simpa [inclErase] using hrtg_S

  -- RTG → le → leOn
  have hle : S.le ⟨a, haG⟩ ⟨b, hbG⟩ := le_of_rtg (S := S) this
  exact (leOn_iff_subtype (S := S) (a := a) (b := b) (ha := haG) (hb := hbG)).2 hle


--使われている。
private lemma leOn_restrict_S_to_S'_usingSucc {α : Type u} [DecidableEq α]
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
  have h' :
    Relation.ReflTransGen (stepRel (fun z : S.Elem => S.f z))
      (inclErase S u ⟨a,ha⟩) (inclErase S u ⟨b,hb⟩) := by
    simpa [inclErase] using hrtg_S
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
private lemma isOrderIdealOn.erase_usingSucc {α : Type u} [DecidableEq α]
  (S : FuncSetup α) (u : S.Elem) (hvne : S.f u ≠ u)
  {A : Finset α}
  (hA : SetFamily.isOrderIdealOn (S.leOn) S.ground A)
  (hNontriv : S.nontrivialClass u) :
  SetFamily.isOrderIdealOn ((eraseOneUsingSucc S u hNontriv).leOn)
                 (eraseOneUsingSucc S u hNontriv).ground
                 (A.erase u.1) := by
  classical
  have : (eraseOneUsingSucc (S := S) u ?_).ground = S.ground.erase u.1 := rfl
  dsimp [SetFamily.isOrderIdealOn]
  rw [this]
  constructor
  · -- subset
    intro a ha
    have aG : a ∈ S.ground := hA.1 ((Finset.mem_erase.mp ha).2)
    have : a ∈ S.ground.erase u.1 :=
      (Finset.mem_erase).2 ⟨(Finset.mem_erase.mp ha).1, aG⟩
    simp [this]
  · -- downward closed on S′
    intro x hx y hy h_yx'
    have hx_ne : x ≠ u.1 := (Finset.mem_erase.mp hx).1
    have hxA   : x ∈ A   := (Finset.mem_erase.mp hx).2
    have hyE : y ∈ S.ground.erase u.1 := by
      simpa [this] using hy
    have hyG : y ∈ S.ground := (Finset.mem_erase.mp hyE).2
    have hxG : x ∈ S.ground := hA.1 hxA
    have h_yx : S.leOn y x := by
      apply leOn_lift_S'_to_S_usingSucc (S := S) (u := u) (hvne := hvne)
        (a := y) (b := x)
        (ha := by simpa [this] using hy)
        (hb := by
          have : x ∈ S.ground.erase u.1 :=
            (Finset.mem_erase).2 ⟨hx_ne, hxG⟩
          simp [this] )
      exact h_yx'

    have hyA : y ∈ A := hA.2 (x := x) hxA (y := y) hyG h_yx
    have hy_ne : y ≠ u.1 := (Finset.mem_erase.mp hyE).1
    exact (Finset.mem_erase).2 ⟨hy_ne, hyA⟩
  · exact hNontriv

-- 核心：trace の idealFamily と一致
private lemma idealFamily_traceAt_eq_eraseOne {α : Type u} [DecidableEq α]
  (S : FuncSetup α) (u : S.Elem) (hNontriv : S.nontrivialClass u) :
  (eraseOneUsingSucc S u hNontriv).idealFamily
    = SetFamily.traceAt u.1 (S.idealFamily) := by
  classical
  set S' := eraseOneUsingSucc (S := S) u hNontriv
  have hvne : S.f u ≠ u := FuncSetup.f_ne_of_nontrivialClass (S := S) hNontriv

  have hground :
      S'.ground = (SetFamily.traceAt u.1 (S.idealFamily)).ground := by
    simp [S', eraseOneUsingSucc, eraseOne, SetFamily.traceAt]
    exact rfl

  have hsets :
    ∀ B : Finset α,
      (S'.idealFamily).sets B ↔ (SetFamily.traceAt u.1 (S.idealFamily)).sets B := by
    intro B
    constructor
    ·
      intro hB
      have hBideal' :
          SetFamily.isOrderIdealOn (S'.leOn) S'.ground B := by
        simpa [S'.sets_iff_isOrderIdeal] using hB
      let A : Finset α :=
        S.ground.filter (fun a => ∃ b, b ∈ B ∧ S.leOn a b)
      have hAideal :
          SetFamily.isOrderIdealOn (S.leOn) S.ground A := by
        refine And.intro ?Asub ?Adown
        ·
          exact Finset.filter_subset _ _
        ·
          intro x hx y hy h_yx

          have hx' : x ∈ S.ground ∧ ∃ b, b ∈ B ∧ S.leOn x b := by

            have := (Finset.mem_filter).1 hx

            simpa using this
          rcases hx' with ⟨hxG, ⟨b, hbB, hxb⟩⟩
          have hyb : S.leOn y b := by
            exact leOn_trans S h_yx hxb
          have : y ∈ S.ground ∧ ∃ b, b ∈ B ∧ S.leOn y b := ⟨hy, ⟨b, hbB, hyb⟩⟩
          exact (Finset.mem_filter).2 this

      have hAsets : (S.idealFamily).sets A := by
        simpa [S.sets_iff_isOrderIdeal] using hAideal

      have hAerase_eq_B : A.erase u.1 = B := by
        ext a
        constructor
        ·
          intro ha

          have ha' := (Finset.mem_erase).1 ha
          have hane : a ≠ u.1 := ha'.1
          have haA : a ∈ A := ha'.2

          have ha_def :
              a ∈ S.ground ∧ ∃ b, b ∈ B ∧ S.leOn a b :=
            (Finset.mem_filter).1 haA
          rcases ha_def with ⟨haG, ⟨b, hbB, hab⟩⟩
          have ha_in_erase : a ∈ S'.ground := by
            have : a ∈ S.ground := haG
            have : a ∈ S.ground.erase u.1 :=
              (Finset.mem_erase).2 ⟨hane, this⟩
            simpa [S', eraseOneUsingSucc, eraseOne]
              using this
          have hb_in_erase : b ∈ S'.ground := by
            have hBsub : B ⊆ S'.ground :=
              (S'.idealFamily.inc_ground) hB
            exact hBsub hbB
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
          have hBideal' :
            SetFamily.isOrderIdealOn (S'.leOn) S'.ground B := by
            simpa [S'.sets_iff_isOrderIdeal] using hB
          exact hBideal'.2
            (x := b) (y := a)
            (by exact hbB)
            (by exact ha_in_erase)
            (by exact hab')
        ·
          intro hbB

          have hb_in_erase : a ∈ S'.ground :=
            (S'.idealFamily.inc_ground hB) hbB

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
          have hbb : S.leOn a a :=
            S.leOn_refl (x := a) hbG
          have hbA : a ∈ A := by
            apply (Finset.mem_filter).2
            exact ⟨hbG, ⟨a, hbB, hbb⟩⟩
          exact (Finset.mem_erase).2 ⟨hb_ne_u, hbA⟩

      refine ⟨A, hAsets, ?_⟩
      exact hAerase_eq_B.symm

    · rintro ⟨A, hAsets, rfl⟩
      have hAideal :
          SetFamily.isOrderIdealOn (S.leOn) S.ground A := by
        simpa [S.sets_iff_isOrderIdeal] using hAsets

      have hIdeal' :
          SetFamily.isOrderIdealOn (S'.leOn) S'.ground (A.erase u.1) := by
        exact isOrderIdealOn.erase_usingSucc S u hvne hAsets hNontriv

      simpa [S'.sets_iff_isOrderIdeal] using hIdeal'

  apply SetFamily.ext hground (funext (λ B => propext (hsets B)))
  show S'.idealFamily.decSets ≍ (SetFamily.traceAt (↑u) S.idealFamily).decSets
  have h_sets : S'.idealFamily.sets = (SetFamily.traceAt (↑u) S.idealFamily).sets := funext (λ B => propext (hsets B))
  exact
    Subsingleton.helim (congrArg DecidablePred h_sets) S'.idealFamily.decSets
      (SetFamily.traceAt (↑u) S.idealFamily).decSets

--上の補題の書き換え。
--functionalのtraceがまたfunctionalになる。このファイルのメインの結果。そとから使われている。
theorem  traced_is_functional_family {α : Type u} [DecidableEq α]
    (S : FuncSetup α) (u : S.Elem)
    (hNontriv : FuncSetup.nontrivialClass S u) :
    ∃ S' : FuncSetup α,
      S'.idealFamily = SetFamily.traceAt u.1 (S.idealFamily) := by
  let eous := eraseOneUsingSucc (α := α) (S := S) u hNontriv
  let iftee := idealFamily_traceAt_eq_eraseOne (S := S) (u := u) (hNontriv := hNontriv)
  use eous

end AvgRare.FuncSetup
