import Mathlib.Data.Finset.Basic
import AvgRare.Basics.SetFamily
import AvgRare.Basics.Trace.Common
import AvgRare.SPO.FuncSetup
import AvgRare.Basics.Ideals

universe u

namespace AvgRare
namespace PaperSync

open Classical
open Basics SetFamily Trace
open FuncSetup

variable {α : Type u} [DecidableEq α]

/-! ### 前提メモ
`SetFamily α` は構造体版：
  * `ground : Finset α`
  * `sets : Finset α → Prop`
  * `inc_ground : sets A → A ⊆ ground`
`↘` は Common 側で `restrict : SetFamily α → Finset α → SetFamily α` として定義済みとする。
-/

/-- サブタイプ化（`Elem S = {x // x ∈ S.V}`）。他所にあるなら import に切替可。 -/
abbrev Elem (S : FuncSetup α) := {x : α // x ∈ S.V}

/-- `proj : S.Elem → Quot S.ker`（SCC 商への射影） -/
@[simp] def proj (S : FuncSetup α) (x : Elem S) : Quot S.ker :=
  Quot.mk _ x

/-- Finset 版の商像。Common の `imageQuot` をそのまま使う別名。 -/
noncomputable def imQuot (S : FuncSetup α)
    (A : Finset (Elem S)) : Finset (Quot S.ker) :=
  AvgRare.Basics.Trace.imageQuot (S.ker) A


/-- 商像の単調性：`A ⊆ B → imQuot A ⊆ imQuot B` -/
lemma imQuot_mono (S : FuncSetup α)
    {A B : Finset (Elem S)} (hAB : A ⊆ B) :
    imQuot S A ⊆ imQuot S B := by
  classical
  -- Common 側の一般補題を流用
  simpa [imQuot] using
    (AvgRare.Basics.Trace.imageQuot_mono (E:=S.ker) (A:=A) (B:=B) hAB)

/-- 集合族の SCC 商への像：各 `A ∈ 𝓕` を `imQuot S A` に写す。 -/
noncomputable def mapFamilyToQuot (S : FuncSetup α)
    (𝓕 : SetFamily (Elem S)) : SetFamily (Quot S.ker) :=
{ ground := 𝓕.ground.image (fun a => proj S a)
, sets  := fun B : Finset (Quot S.ker) =>
    ∃ A : Finset (Elem S), 𝓕.sets A ∧ B ⊆ imQuot S A
, decSets := by infer_instance
, inc_ground := by
    intro B hB
    rcases hB with ⟨A, hA, hBsub⟩
    -- `A ⊆ ground` を像に押す
    have hAsub : A ⊆ 𝓕.ground := 𝓕.inc_ground hA
    have hImg : imQuot S A ⊆ 𝓕.ground.image (fun a => proj S a) := by
      intro q hq
      rcases Finset.mem_image.mp (by
        -- `imQuot S A = A.image (proj S)` と同値
        change q ∈ (A.image (fun a => proj S a)) at hq
        exact hq) with ⟨a, haA, rfl⟩
      exact Finset.mem_image.mpr ⟨a, hAsub haA, rfl⟩
    exact hBsub.trans hImg }

@[simp] lemma imQuot_def (S : FuncSetup α) (A : Finset (Elem S)) :
  imQuot S A = A.image (fun a => proj S a) := rfl

@[simp] lemma mem_imQuot_iff (S : FuncSetup α) {A : Finset (Elem S)} {q : Quot S.ker} :
  q ∈ imQuot S A ↔ ∃ a ∈ A, proj S a = q := by
  classical
  simp [imQuot_def, proj, Finset.mem_image]

-- 画像の単調性、`simp` で使いたいので `@[simp]` にもしておく（任意）
@[simp] lemma imQuot_mono' (S : FuncSetup α)
    {A B : Finset (Elem S)} (hAB : A ⊆ B) :
    imQuot S A ⊆ imQuot S B :=
  imQuot_mono (S:=S) hAB

/-- `mapFamilyToQuot` の単調性（述語の含意として記述） -/
lemma mapFamilyToQuot_mono (S : FuncSetup α)
  {𝓕 𝓖 : SetFamily (Elem S)}
  (hFG : ∀ {A : Finset (Elem S)}, 𝓕.sets A → 𝓖.sets A) :
  ∀ {B : Finset (Quot S.ker)},
    (mapFamilyToQuot S 𝓕).sets B → (mapFamilyToQuot S 𝓖).sets B := by
  intro B hB
  rcases hB with ⟨A, hA, hBsub⟩
  exact ⟨A, hFG hA, hBsub⟩



/-- idealFamily の像（商側の family）。 -/
noncomputable def idealFamilyQuot (S : FuncSetup α) :
    SetFamily (Quot S.ker) :=
  mapFamilyToQuot S (idealFamily S)

lemma trace_map_commute_subset (S : FuncSetup α)
    (𝓕 : SetFamily (Elem S)) (U : Finset (Elem S)) :
    ∀ {B : Finset (Quot S.ker)},
      (mapFamilyToQuot S (𝓕 ↘ U)).sets B →
      ∃ C : Finset (Quot S.ker),
        (mapFamilyToQuot S 𝓕).sets C ∧ B ⊆ imQuot S U := by
  classical
  intro B hB
  rcases hB with ⟨A', hA'rest, hBsub⟩
  rcases hA'rest with ⟨C, hCmem, hA'subC, hA'subU⟩
  refine ⟨imQuot S C, ?_, ?_⟩
  · exact ⟨C, hCmem, by intro q hq; exact hq⟩
  · exact fun q hq =>
      (imQuot_mono (S:=S) hA'subU) (hBsub hq)

/-- 橋渡し（包含版）。 -/
lemma ideal_trace_bridge_subset_ideal (S : FuncSetup α)
    (U : Finset (Elem S)) :
    ∀ {B : Finset (Quot S.ker)},
      (mapFamilyToQuot S ((idealFamily S) ↘ U)).sets B →
      ∃ C : Finset (Quot S.ker), (idealFamilyQuot S).sets C ∧ B ⊆ imQuot S U := by
  classical
  intro B hB
  rcases trace_map_commute_subset (S:=S) (𝓕:=(idealFamily S)) (U:=U) (B:=B) hB with ⟨C, hC, hsub⟩
  exact ⟨C, hC, hsub⟩

lemma ideal_trace_bridge_subset (S : FuncSetup α)
    (U : Finset (Elem S)) :
    ∀ {B : Finset (Quot S.ker)},
      (mapFamilyToQuot S ((idealFamily S) ↘ U)).sets B →
      ∃ C : Finset (Quot S.ker), (idealFamilyQuot S).sets C ∧ B ⊆ imQuot S U := by
  classical
  intro B hB
  rcases trace_map_commute_subset (S:=S) (𝓕:=idealFamily S) (U:=U) (B:=B) hB with ⟨C, hC, hsub⟩
  exact ⟨C, hC, hsub⟩

/-- 安定性: U が f に関して閉じている -/
def stable (S : FuncSetup α) (U : Finset (Elem S)) : Prop :=
  ∀ x ∈ U, S.fV x ∈ U

/-- Ideal 的性質（構造体版 SetFamily 用の簡易定義） -/
def IsIdeal {β} [DecidableEq β] (F : SetFamily β) : Prop :=
  ∀ ⦃A B⦄, F.sets B → A ⊆ B → F.sets A

/-- U が S(Elem) に関して安定（例：f-前像で閉、など望ましい条件へ差し替え） -/
-- 主定理の証明には関係ない？
def StableUnder (S : FuncSetup α) (U : Finset (Elem S)) : Prop :=
  ∀ {x}, x ∈ U → S.fV x ∈ U

/-- 逆向き：商側で `B ⊆ C` かつ `B ⊆ imQuot S U` が言え、かつ 𝓕 の元が
`ker` に関して **飽和（saturated）** しているなら、`B ∈ mapFamilyToQuot S (𝓕 ↘ U)`。
ここで飽和とは `x ~ y` かつ `x ∈ A` なら `y ∈ A` が成り立つこと。 -/
lemma trace_map_commute_superset_of_ker_saturated (S : FuncSetup α)
    (𝓕 : SetFamily (Elem S))
    (U : Finset (Elem S))
    (hSat : ∀ {A : Finset (Elem S)}, 𝓕.sets A →
              ∀ {x y : Elem S}, S.ker.r x y → x ∈ A → y ∈ A) :
    ∀ {B : Finset (Quot S.ker)},
      (∃ C : Finset (Quot S.ker), (mapFamilyToQuot S 𝓕).sets C ∧ B ⊆ C ∧ B ⊆ imQuot S U) →
      (mapFamilyToQuot S (𝓕 ↘ U)).sets B := by
  classical
  intro B h
  rcases h with ⟨C, hCsets, hBC, hBU⟩
  rcases hCsets with ⟨A, hAmem, hCsub⟩
  -- 各 q ∈ B について U 内代表を選ぶ
  have h1 : ∀ q, q ∈ B → ∃ x : Elem S, x ∈ U ∧ proj S x = q := by
    intro q hq
    exact (mem_imQuot_iff (S:=S)).1 (hBU hq)
  choose rep hrepU hrepProj using h1
  -- A' を B の各要素の代表の集合として作る
  let A' : Finset (Elem S) := B.attach.image (fun q => rep q.1 q.2)
  have hA'subU : A' ⊆ U := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨q, hqB, rfl⟩
    exact hrepU q.1 q.2
  -- A' が A に含まれることを示す（飽和性を使う）
  have hA'subA : A' ⊆ A := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨q, hqB, rfl⟩
    -- `q.1 ∈ B` かつ `B ⊆ C` より `q.1 ∈ C`
    have hqC : q.1 ∈ C := hBC q.2
    -- `C ⊆ imQuot S A` より、`q.1 ∈ imQuot S A`
    have hq_imA : q.1 ∈ imQuot S A := hCsub hqC
    -- ある y ∈ A で proj y = q.1
    rcases (mem_imQuot_iff (S:=S)).1 hq_imA with ⟨y, hyA, hyProj⟩
    -- 代表の等値から kernel 関係を得る
    have hEq : Quot.mk (S.ker) (rep q.1 q.2) = Quot.mk (S.ker) y := by
      have : proj S (rep q.1 q.2) = proj S y := by
        have : proj S (rep q.1 q.2) = q.1 := hrepProj q.1 q.2
        exact this.trans (by simp_all only [Subtype.forall, imQuot_def, proj, Finset.mem_attach, Finset.mem_image, true_and, exists_apply_eq_apply,
    Subtype.exists, A'])
      simpa [proj] using this
    have hRel0 : S.ker.r (rep q.1 q.2) y := Quotient.eq''.mp hEq
    -- 飽和性は向きを `y → rep` に使う
    have hRel1 : S.ker.r y (rep q.1 q.2) := (S.ker.iseqv.symm) hRel0
    exact hSat hAmem hRel1 hyA
  -- B ⊆ imQuot S A'
  have hBsubA' : B ⊆ imQuot S A' := by
    intro q hq
    -- `⟨q,hq⟩ : {q // q ∈ B}` は `B.attach` の元
    have hqa : ⟨q, hq⟩ ∈ B.attach := by exact Finset.mem_attach _ _
    have hx_mem : rep q hq ∈ A' := by
      exact Finset.mem_image.mpr ⟨⟨q, hq⟩, hqa, rfl⟩
    have hproj : proj S (rep q hq) = q := hrepProj q hq
    exact (mem_imQuot_iff (S:=S)).2 ⟨_, hx_mem, hproj⟩
  -- まとめ：`A' ⊆ A` かつ `A' ⊆ U`、そして `B ⊆ imQuot S A'`
  exact ⟨A', ⟨A, hAmem, hA'subA, hA'subU⟩, hBsubA'⟩


/-- `trace`（制限）と商への像の交換：包含版（restrict 風）。
`B ∈ mapFamilyToQuot S (𝓕 ↘ U)` なら、ある `C ∈ mapFamilyToQuot S 𝓕` があり、
`B ⊆ C` かつ `B ⊆ imQuot S U` が成り立つ。 -/
lemma trace_map_commute_subset_restrict (S : FuncSetup α)
    (𝓕 : SetFamily (Elem S)) (U : Finset (Elem S)) :
    ∀ {B : Finset (Quot S.ker)},
      (mapFamilyToQuot S (𝓕 ↘ U)).sets B →
      ∃ C : Finset (Quot S.ker),
        (mapFamilyToQuot S 𝓕).sets C ∧ B ⊆ C ∧ B ⊆ imQuot S U := by
  classical
  intro B hB
  rcases hB with ⟨A', hA'rest, hBsub⟩
  rcases hA'rest with ⟨C, hCmem, hA'subC, hA'subU⟩
  refine ⟨imQuot S C, ?_, ?_, ?_⟩
  · exact ⟨C, hCmem, by intro q hq; exact hq⟩
  · exact fun q hq => (imQuot_mono (S:=S) hA'subC) (hBsub hq)
  · exact fun q hq => (imQuot_mono (S:=S) hA'subU) (hBsub hq)

@[simp] lemma idealFamily_sets_iff (S : FuncSetup α)
  {A : Finset (Elem S)} :
  (idealFamily S).sets A ↔ S.isOrderIdeal A := Iff.rfl

/-- 等式版（核に関する飽和性から）。
`I.carrier` の各元が kernel に関して飽和（=順序イデアル）であるとき、
`trace` と商像は制限レベルで可換。 -/
lemma ideal_trace_bridge_eq_of_ker_saturated
  (S : FuncSetup α) (U : Finset (Elem S)) :
  ∀ {B : Finset (Quot S.ker)},
    (mapFamilyToQuot S ((idealFamily S) ↘ U)).sets B ↔
    (∃ C : Finset (Quot S.ker), (idealFamilyQuot S).sets C ∧ B ⊆ C ∧ B ⊆ imQuot S U) := by
  classical
  intro B; constructor
  · -- → 方向：制限→商像への包含をそのまま使う
    intro h
    rcases trace_map_commute_subset_restrict
            (S:=S) (𝓕:=(idealFamily S)) (U:=U) (B:=B) h with
      ⟨C, hC, hBC, hBU⟩
    exact ⟨C, hC, hBC, hBU⟩
  · -- ← 方向：kernel 飽和性を使って元へ戻す
    intro h
    -- idealFamily の各元は isOrderIdeal なので ker 飽和
    have hSat :
      ∀ {A : Finset (Elem S)}, (idealFamily S).sets A →
        ∀ {x y : Elem S}, S.ker.r x y → x ∈ A → y ∈ A := by
      intro A hA x y hxy hx
      -- `ideal_saturated_under_ker` を適用
      exact (FuncSetup.ideal_saturated_under_ker
              (S:=S) (hA := (idealFamily_sets_iff (S:=S)).1 hA)) hxy hx
    -- 逆向き補題で終了
    exact trace_map_commute_superset_of_ker_saturated
            (S:=S) (𝓕:=(idealFamily S)) (U:=U) (hSat:=hSat) (B:=B) h

lemma ideal_trace_bridge_eq_of_ker_saturated_ideal (S : FuncSetup α)
    (U : Finset (Elem S)) :
    ∀ {B : Finset (Quot S.ker)},
      (mapFamilyToQuot S ((idealFamily S) ↘ U)).sets B ↔
      (∃ C : Finset (Quot S.ker), (idealFamilyQuot S).sets C ∧ B ⊆ C ∧ B ⊆ imQuot S U) := by
  classical
  intro B; constructor
  · intro h
    rcases trace_map_commute_subset_restrict (S:=S) (𝓕:=(idealFamily S)) (U:=U) (B:=B) h with
      ⟨C, hC, hBC, hBU⟩
    exact ⟨C, hC, hBC, hBU⟩
  · intro h
    -- idealFamily の各元は isOrderIdeal なので ker 飽和
    have hSat : ∀ {A : Finset (Elem S)}, (idealFamily S).sets A →
        ∀ {x y : Elem S}, S.ker.r x y → x ∈ A → y ∈ A := by
      intro A hA x y hxy hx
      exact (FuncSetup.ideal_saturated_under_ker (S:=S)
              (hA := (idealFamily_sets_iff (S:=S)).1 hA)) hxy hx
    exact trace_map_commute_superset_of_ker_saturated (S:=S)
      (𝓕:=(idealFamily S)) (U:=U) (hSat:=hSat) (B:=B) h

lemma ideal_trace_bridge_eq (S : FuncSetup α)
    (U : Finset (Elem S)) :
    (mapFamilyToQuot S ((idealFamily S) ↘ U)).sets =
    (fun B : Finset (Quot S.ker) =>
      ∃ C : Finset (Quot S.ker),
        (idealFamilyQuot S).sets C ∧ B ⊆ C ∧ B ⊆ imQuot S U) := by
  -- すでにこの等式の両向きを証明した補題があり，それは「述語の同値」です。
  -- ここでは述語の等式にしたいので，点ごとの `propext` で仕上げます。
  funext B
  exact propext
    (ideal_trace_bridge_eq_of_ker_saturated_ideal (S:=S) (U:=U) (B:=B))

lemma idealFamily_sets_to_isOrderIdeal (S : FuncSetup α)
  {A : Finset (Elem S)} (h : (idealFamily S).sets A) :
  S.isOrderIdeal A := by simp_all only [idealFamily_sets_iff]

lemma isOrderIdeal_to_idealFamily_sets (S : FuncSetup α)
  {A : Finset (Elem S)} (h : S.isOrderIdeal A) :
  (idealFamily S).sets A := by simp_all only [idealFamily_sets_iff]

end PaperSync
end AvgRare


/- 論文の「ideal family 𝓘(S)」の外形：functional preorder `S` から生成される
ダウンワードクローズ集合族（まずは外形のみ）。 -/
/-idealsにうつした。
noncomputable def idealFamily (S : FuncSetup α) : SetFamily (Elem S) :=
{ ground := S.V.attach,
  sets   := fun A : Finset (Elem S) => S.isOrderIdeal A,
  decSets := by infer_instance,   -- `isOrderIdeal` は既に DecidablePred
  inc_ground := by
    intro A hA x hx
    -- 要素 `x : S.Elem` は常に `attach` に入る
    exact Finset.mem_attach S.V x }
    -/

/-
lemma ideal_trace_bridge_subset' (S : FuncSetup α)
  (I : IdealFamily S) (U : Finset (Elem S)) :
  ∀ {B : Finset (Quot S.ker)},
    (mapFamilyToQuot S (I.carrier ↘ U)).sets B →
    ∃ C : Finset (Quot S.ker), (idealFamilyQUot S I).sets C ∧ B ⊆ imQuot S U := by
  classical
  intro B hB
  rcases trace_map_commute_subset (S:=S) (𝓕:=I.carrier) (U:=U) (B:=B) hB with ⟨C, hC, hsub⟩
  exact ⟨C, hC, hsub⟩
-/


/- 等式版（占位定理）：適切な仮定のもとで交換は等式になる -/
/-
lemma ideal_trace_bridge_eq'
  (S : FuncSetup α) (I : IdealFamily S) (U : Finset (Elem S))
  (hI : IsIdeal I.carrier) (hU : StableUnder S U) :
  -- 集合族（述語）としての同値（相互包含）
  (mapFamilyToQuot S (I.carrier ↘ U)).sets =
  (fun B => ∃ C, (mapFamilyToQuot S I.carrier).sets C ∧ B ⊆ imQuot S U) := by
  -- → 向き：既に `trace_map_commute_subset` で示している
  -- ← 向き：`I` の理想性と `U` の安定性を使って、C を U で切って A' にし、B ⊆ imQuot S A' ⊆ imQuot S U から
  --         A' が `I.carrier ↘ U` の元といえることを示す
  funext B; apply propext; constructor
  · intro hB; exact trace_map_commute_subset S I.carrier U hB  -- 既存補題で出す
  · intro h; sorry   -- ここを後で詰める

/-- 等式版（占位）。仮定（`U` の安定性・`I` の性質）を整備したら強化予定。 -/
lemma ideal_trace_bridge_eq (S : FuncSetup α)
    (I : IdealFamily S) (U : Finset (Elem S)) : True := by
  trivial
-/

--theorem nds_ideal_family_eq_on_quot (S : FuncSetup α) :
--  (idealFamily S).normalized_degree_sum
--  = (idealFamilyQuot S).normalized_degree_sum := by
--  -- TODO: 代表選択と像の計数一致で証明する
--  sorry

--小文字と大文字で別？
--structure IdealFamily (S : FuncSetup α) where
--  carrier : SetFamily (Elem S)

--notation3:80 "𝓘(" S ")" => IdealFamily S
