import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import AvgRare.Basics.SetFamily
import AvgRare.Basics.Trace.Common
import AvgRare.SPO.FuncSetup

universe u

namespace AvgRare
namespace Trace
open scoped BigOperators
open Classical

variable {α : Type u} [DecidableEq α]


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
    exact S.parallel_of_sim_coe hsim

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


lemma ideal_diff_simClass_is_ideal
    (S : SPO.FuncSetup α)
    {u : S.Elem} {I : Finset α}
    (hmax : S.maximal u)
    (hI : (S.idealFamily).sets I) --(huI : u.1 ∈ I)
    :
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
        S.sim_of_maximal_above_class (u := u) (x := ⟨x, hxV⟩) (y := ⟨y, hy⟩)
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
  fun ⟨I, hIedge, _⟩ =>
    let hI_sets : (S.idealFamily).sets I :=
      (SetFamily.mem_edgeFinset_iff_sets (F := S.idealFamily) (A := I)).1 hIedge
    let h := ideal_diff_simClass_is_ideal (S := S) (u := u) hmax hI_sets
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
