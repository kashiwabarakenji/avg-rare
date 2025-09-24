# Avg-Rare Theorem Formalization (Lean 4)

This repository contains a Lean 4 formalization of functional preorders and Average-Rare (Frankl-type) results. Lean 4 code follows the paper's mathematical development with formal verification.

This formalization explores the combinatorial structure of set families and functional preorders, inspired by the Average-Rare (Frankl-type) phenomenon in extremal combinatorics. The results provide a rigorous, computer-verified foundation for understanding how certain algebraic and combinatorial properties interact.

**Background:**
The Average-Rare phenomenon describes how, in large families of sets or functions, most elements behave "typically" (average), while a few are "rare" and have special structural properties. This formalization captures these ideas using Lean 4, making the arguments precise and verifiable. For terminology and notation, please refer to the original paper.

**Intuitive Significance:**
The main theorem shows that, no matter how complicated the functional structure, the normalized degree sum (NDS) cannot be positive. This reflects a deep balance in the system: the "average" behavior dominates, and the "rare" configurations are tightly controlled by the structure of the ideals and maximal elements.

**Applications:**
- Understanding the structure of posets and set families in extremal combinatorics
- Formalizing proofs in discrete mathematics and theoretical computer science
- Providing a template for further formalization of combinatorial theorems


These results formalize and generalize combinatorial phenomena related to set families and functional structures, providing a rigorous foundation for further mathematical exploration.

## Structure
- `AvgRare/Basics/` — Core definitions (`SetFamily`, `SetTrace`, general lemmas).
- `AvgRare/Functional/` — Functional preorder and partial order structures (`FuncSetup`, `FuncPoset`, `TraceFunctional`).
- `AvgRare/Reductions/` — Reduction the Main theorem to Secondary Main Theorem (`Rare`, `Reduction`).
- `AvgRare/Secondary/` — proof of Secondary Main Theorem (`MainStatement`, `SumProduct`, `UniqueMax`).
- `AvgRare/Old/` — Legacy code (not part of the proof of  main theorem).

## Build
```bash
lake update
lake build
```

## Main Theorem

- **Main Theorem**  
  - **Paper: Theorem 2.8**  
    For any functional preorder, the normalized degree sum (NDS) is non-positive.  

    ```lean
    main_nds_nonpos (S : FuncSetup α) : NDS (idealFamily S) ≤ 0
    ```  

    The formalization of the Main Theorem appears in  
    `AvgRare/Secondary/MainStatement.lean` as  
    **`main_nds_nonpos_of_secondary`**.  

    *Proof Sketch:*  
    The proof reduces the general case to the Secondary Theorem (`secondary_main_theorem`).  
    Key steps include:

    - **Trace lemmas**:  
      - `NDS_le_trace_of_nontrivialClass` (Paper: Lemma 3.4)  
      - `NDS_eq_of_parallel` (Paper: Lemma 3.2)  
    - **Maximality lemmas**:  
      - `rare_of_maximal` (Paper: Lemma 3.1)  
    - **Equivalence lemmas**:  
      - `simClass_eq_parallelClass` (Paper: Lemma 3.3)  

    These reductions allow us to move from general functional preorders to rooted forests,
    which are handled by the Secondary Main Theorem.  


- **Secondary Main Theorem**  
  - **Paper: Theorem 2.9**  
    For any finite functional poset, the normalized degree sum (NDS) is non-positive.  

    ```lean
    secondary_main_theorem (S : FuncSetup α) 
      (hpos : isPoset S) : NDS (idealFamily S) ≤ 0
    ```  

    *Proof Sketch:*  
    The proof proceeds by induction on the size of the ground set.  

    - If the poset is **disconnected**, apply the **product formula**:  
      `NDS_restrict_sumProd_split` (Paper: Lemma 5.1).  
    - If the poset is **connected with a unique maximal**, use:  
      - `nds_diff_eq_root_delete_identity_uniqueMax` (Paper: Lemma 5.2)  
      - `ideals_card_ge_ground_card_succ` (Paper: Lemma 5.3)  
      - `nds_trace_nondecreasing_uniqueMax` (Paper: Lemma 5.4)  
    - The **base case** and **reachability** are handled by:  
      - `le_iff_exists_iter` (Paper: Lemma 2.2)  

    Together these results establish that the normalized degree sum cannot be positive
    for any functional poset.  



# Key Definitions and Theorems

## AvgRare/Basics/SetFamily.lean

### SetFamily
Basic structure for finite set families.
**[Paper: Definition 1.1]**
```lean
structure SetFamily (α : Type u) [DecidableEq α] where
	ground     : Finset α
	sets       : Finset α → Prop
	decSets    : DecidablePred sets
	inc_ground : ∀ {A : Finset α}, sets A → A ⊆ ground
```

### numHyperedges
Number of hyperedges (elements of the set family).
```lean
def numHyperedges : Nat := F.edgeFinset.card
```

### totalHyperedgeSize
Total size (number of elements) of all hyperedges.
```lean
def totalHyperedgeSize : Nat := ∑ A ∈ F.edgeFinset, A.card
```

### NDS (Normalized Degree Sum)
Normalized degree sum.
**[Paper: Definition 1.2]**
```lean
def NDS (F : SetFamily α) : Int :=
	2 * (F.totalHyperedgeSize : Int) - (F.numHyperedges : Int) * (F.ground.card : Int)
```

### Parallel
Parallel relation in set families.
**[Paper: Definition 1.3]**
```lean
def Parallel (F : SetFamily α) (u v : α) : Prop :=
	{A : Finset α | F.sets A ∧ u ∈ A} = {A : Finset α | F.sets A ∧ v ∈ A}
```

### isOrderIdealOn
Order ideal predicate.
**[Paper: Definition 1.4]**
```lean
def isOrderIdealOn (le : α → α → Prop) (V I : Finset α) : Prop :=
	I ⊆ V ∧ ∀ ⦃x⦄, x ∈ I → ∀ ⦃y⦄, y ∈ V → le y x → y ∈ I
```

### Related Theorems (Statements Only)
- `degree_eq_card_filter`: The degree equals the number of edges containing x.
- `mem_edgeFinset`: An element of edgeFinset is a subset of ground and a member of sets.
- `Parallel_edge_iff_Parallel`: Parallel and Parallel_edge are equivalent.
- `ground_eq_biUnion_classSet`: ground is the union of all classes in classSet.
- `card_ground_eq_sum_card_classes`: The cardinality of ground equals the sum of the cardinalities of all classes in classSet.

---

## AvgRare/Functional/FuncSetup.lean

```lean
structure FuncSetup (α : Type u) [DecidableEq α] where
	nonempty : Nonempty ground
	f      : {x // x ∈ ground} → {y // y ∈ ground}
**[Paper : Definition 2.1]**
```

### cover
Direct cover relation (edge of the functional graph).
**[Paper : Definition 2.2]**
```lean
def cover (x y : S.Elem) : Prop := S.f x = y
```

### le
Reachability via repeated application of f (preorder).
**[Paper : Definition 2.3]**
```lean
def le (x y : S.Elem) : Prop := Relation.ReflTransGen S.cover x y
```

### has_le_antisymm
Antisymmetry property for the preorder.
**[Paper : Definition 2.4]**
```lean
def has_le_antisymm : Prop := ∀ {x y : S.Elem}, S.le x y → S.le y x → x = y
```

### sim
Equivalence relation: mutual reachability.
**[Paper : Definition 2.5]**
```lean
def sim (x y : S.Elem) : Prop := S.le x y ∧ S.le y x
```

### maximal
Maximal element: every reachable element returns to x.
**[Paper : Definition 2.6]**
```lean
def maximal (x : S.Elem) : Prop := ∀ ⦃y⦄, S.le x y → S.le y x
```

### idealFamily
Order ideal family induced from the functional preorder.
**[Paper : Definition 2.7]**
```lean
noncomputable def idealFamily (S : FuncSetup α) : SetFamily α :=
	SetFamily.orderIdealFamily (le := leOn S) (V := S.ground)
```

### parallel_iff_sim
Parallel in idealFamily is equivalent to sim in FuncSetup.
**[Paper : Lemma 2.1]**
```lean
theorem parallel_iff_sim (S : FuncSetup α) (u v : S.Elem) :
	(S.idealFamily).Parallel u v ↔ FuncSetup.sim S u v
```

### le_iff_exists_iter
Reachability is equivalent to existence of an iterate.
**[Paper : Lemma 2.2]**
```lean
lemma le_iff_exists_iter (S : FuncSetup α) (x y : S.Elem) :
	S.le x y ↔ ∃ k : Nat, S.iter k x = y
```

### maximal_of_parallel_nontrivial
If two elements are parallel and distinct, then the class is maximal in the preorder.
**[Paper : Lemma 2.3]**
```lean
theorem maximal_of_parallel_nontrivial
	(S : FuncSetup α) {u v : α}
	(hu : u ∈ S.ground) (hv : v ∈ S.ground)
	(hpar : (S.idealFamily).Parallel u v)
	(hneq : u ≠ v) :
	∀ x : S.Elem,
		Relation.ReflTransGen (stepRel S.f) (S.toElem! hu) x →
		Relation.ReflTransGen (stepRel S.f) x (S.toElem! hu)
```

### Other Key Lemmas (Statements Only)
- `maximal_of_fixpoint`: If f u = u, then u is maximal.
- `simClass_eq_parallelClass`: The equivalence class in FuncSetup matches the parallel class in idealFamily.
- `le_iff_forall_ideal_mem`: Reachability is equivalent to membership in all ideals containing the target.

---

## AvgRare/Basics/SetTrace.lean
...existing code...

### traceAt
Trace operation: removes a point from every hyperedge and from the ground set.
**[Paper : Definition 3.1]**
```lean
noncomputable def traceAt (x : α) (F : SetFamily α) : SetFamily α
```

### excess
Excess parameter: ground size minus number of equivalence classes.
**[Paper : Definition 3.2]**
```lean
noncomputable def excess (F : SetFamily α) : ℕ :=
	F.ground.card - numClasses F
```

### excess_trace
Tracing a parallel element reduces excess by 1.
**[Paper : Lemma 3.1]**
```lean
theorem excess_trace
	(F : SetFamily α) (hasU: F.sets F.ground) (Nonemp: F.ground.card ≥ 1)
	(u v : α) (hu : u ∈ F.ground) (hv : v ∈ F.ground)
	(huv : u ≠ v) (hp : Parallel F u v) :
	excess (traceAt u F) = excess F - 1
```

### NDS_eq_of_parallel
Explicit formula for NDS after tracing a parallel element.
**[Paper : Lemma 3.2]**
```lean
theorem NDS_eq_of_parallel
	(F : SetFamily α) {u v : α}
	(huv : F.Parallel u v) (hne : u ≠ v) (hu : u ∈ F.ground):
	F.NDS = (traceAt u F).NDS + 2 * (F.degree u : Int) - (F.numHyperedges : Int)
```

---

## AvgRare/Functional/TraceFunctional.lean

### traced_is_functional_family
The trace of a functional family is again functional (preserves the functional structure).
**[Paper : Lemma 3.3]**
```lean
theorem traced_is_functional_family {α : Type u} [DecidableEq α]
	(S : FuncSetup α) (u : S.Elem)
	(hNontriv : FuncSetup.nontrivialClass S u) :
	∃ S' : FuncSetup α,
		S'.idealFamily = SetFamily.traceAt u.1 (S.idealFamily)
```




---

## AvgRare/Reductions/Reduction.lean

### maximal_of_nontrivialClass
If the equivalence class of x has size at least 2, then x is maximal.
**[Paper : Lemma 2.3]**
```lean
theorem maximal_of_nontrivialClass {α : Type u} [DecidableEq α]
	(S : FuncSetup α) {x : S.Elem}
	(hx : S.nontrivialClass x) : S.maximal x
```

### NDS_le_trace_of_nontrivialClass
Tracing a parallel partner does not increase NDS.
**[Paper : Lemma 3.4]**
```lean
theorem NDS_le_trace_of_nontrivialClass {α : Type u} [DecidableEq α]
	(S : FuncSetup α) {u : S.Elem}
	(hx : S.nontrivialClass u) :
	(S.idealFamily).NDS ≤ (traceAt u.1 (S.idealFamily)).NDS
```

### main_nds_nonpos_of_secondary
The main theorem: if the secondary statement holds, then NDS ≤ 0 for any functional family.
**[Paper : Theorem 1 (Main)]**
```lean
theorem main_nds_nonpos_of_secondary {α : Type u} [DecidableEq α]
	(secondary_nds_nonpos :
		∀ (T : FuncSetup α), FuncSetup.isPoset_excess T → (T.idealFamily).NDS ≤ 0)
	(S : FuncSetup α) :
	(S.idealFamily).NDS ≤ 0
```

### Rare

Rare element predicate: degree is at most half the number of hyperedges.
**[Paper : Definition 4.1]**
```lean
def Rare (F : SetFamily α) (x : α) : Prop :=
	2 * F.degree x ≤ F.numHyperedges
```

### rare_of_maximal
Maximal elements are rare in the ideal family.
**[Paper : Lemma 4.1]**
```lean
theorem rare_of_maximal {α : Type u} [DecidableEq α]
	(S : FuncSetup α) {u : S.Elem} (hmax : S.maximal u) :
	Rare (S.idealFamily) u.1
```

### NDS_le_trace_of_nontrivialClass
Tracing a parallel partner does not increase NDS.
**[Paper : Lemma 3.4]**
```lean
theorem NDS_le_trace_of_nontrivialClass {α : Type u} [DecidableEq α]
	(S : FuncSetup α) {u : S.Elem}
	(hx : S.nontrivialClass u) :
	(S.idealFamily).NDS ≤ (traceAt u.1 (S.idealFamily)).NDS
```

---

## AvgRare/Functional/FuncPoset.lean

### isPoset
Poset property: the preorder is antisymmetric.
**[Paper : Definition 2.4]**
```lean
def isPoset (S : FuncSetup α) : Prop :=
	has_le_antisymm S
```

---

## AvgRare/Secondary/SumProduct.lean

### NDS_restrict_sumProd_split
Decomposition formula for NDS when splitting by principal and co-principal ideals at a maximal element.
**[Paper : Lemma 5.1]**
```lean
theorem NDS_restrict_sumProd_split
	(S : FuncSetup α) (m : S.Elem) (hm : S.maximal m)
	(hpos : isPoset S) (notuniq : ¬ (∃! mm : S.Elem, S.maximal mm)) :
	let F₁ := (restrictToIdeal S m hm).idealFamily
	let F₂ := (restrictToCoIdeal S m hpos notuniq).idealFamily
	(SetFamily.sumProd F₁ F₂).NDS
		=
	(F₂.numHyperedges : Int) * F₁.NDS
	+ (F₁.numHyperedges : Int) * F₂.NDS
```

---

## AvgRare/Secondary/UniqueMax.lean

### nds_diff_eq_root_delete_identity_uniqueMax
Equality for NDS after tracing the unique maximal element.
**[Paper : Lemma 5.2]**
```lean
theorem nds_diff_eq_root_delete_identity_uniqueMax
	(S : FuncSetup α) [Fintype S.Elem] (geq2: S.ground.card ≥ 2)
	(hpos : isPoset S) (hexu : ∃! m : S.Elem, S.maximal m) :
	let S' := posetTraceOfUnique S geq2 hexu
	(S.idealFamily).NDS
		= (S'.idealFamily).NDS
			+ (S.ground.card - (S.idealFamily).numHyperedges + 1 : Int)
```

### ideals_card_ge_ground_card_succ
The number of ideals is at least ground size plus one.
**[Paper : Lemma 5.3]**
```lean
theorem ideals_card_ge_ground_card_succ
	(S : FuncSetup α) (hpos : isPoset S) :
	(S.idealFamily).numHyperedges ≥ S.ground.card + 1
```

### nds_trace_nondecreasing_uniqueMax
Tracing the unique maximal element does not decrease NDS.
**[Paper : Lemma 5.4]**
```lean
theorem nds_trace_nondecreasing_uniqueMax
	(S : FuncSetup α) [Fintype S.Elem] (geq2 : S.ground.card ≥ 2)
	(hpos : isPoset S) (hexu : ∃! m : S.Elem, S.maximal m) :
	let S' := posetTraceOfUnique S geq2 hexu
	(S.idealFamily).NDS ≤ (S'.idealFamily).NDS
```

## AvgRare/Secondary/MainStatement.lean

**[Paper : Theorem 2.9 (Secondary Main)]
```lean
theorem secondary_main_theorem
  (S : FuncSetup α) [Fintype S.Elem]
  (hpos : isPoset S) :
  (S.idealFamily).NDS ≤ 0 
```


### main_nds_nonpos
The main theorem: For any functional preorder, the normalized degree sum (NDS) is non-positive.
**[Paper : Theorem 2.8 (Main)]**
```lean
theorem main_nds_nonpos {α : Type u} [DecidableEq α]
	(S : FuncSetup α) :
	(S.idealFamily).NDS ≤ 0 := by
	apply Reduction.main_nds_nonpos_of_secondary
	intro T hT
	have hT' : isPoset T := by
		dsimp [isPoset]
		dsimp [has_le_antisymm]
		exact T.antisymm_of_isPoset hT
	exact secondary_main_theorem T hT'
```

