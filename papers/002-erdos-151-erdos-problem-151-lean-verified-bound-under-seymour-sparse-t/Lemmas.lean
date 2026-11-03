/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

public import FormalConjecturesUtil

/-!
# Erdős Problem 151

*References:*
- [erdosproblems.com/151](https://www.erdosproblems.com/151)
- [Er88] Erdős, P., *Problems and results in combinatorial analysis and graph theory*.
  Discrete Math. (1988), 81-92.
- [EGT92] Erdős, P. and Gallai, T. and Tuza, Zs., *Covering the cliques of a graph with
  vertices*. Discrete Math. (1992), 279-289.
-/

@[expose] public section

namespace Erdos151

open SimpleGraph

variable {V : Type*}

/-- `s` is a maximal clique of `G` with at least two vertices. -/
def IsBigMaximalClique (G : SimpleGraph V) (s : Finset V) : Prop :=
  Maximal (fun t : Finset V ↦ G.IsClique (t : Set V)) s ∧ 2 ≤ s.card

/-- `T` meets every maximal clique of `G` with at least two vertices. -/
def IsCliqueTransversal (G : SimpleGraph V) (T : Finset V) : Prop :=
  ∀ s, IsBigMaximalClique G s → ∃ v ∈ s, v ∈ T

/-- The clique transversal number $\tau(G)$: the minimal number of vertices that meet every
maximal clique of `G` with at least two vertices. -/
noncomputable def cliqueTransversalNumber (G : SimpleGraph V) : ℕ :=
  sInf {k | ∃ T : Finset V, IsCliqueTransversal G T ∧ T.card = k}

/-- $H(n)$: the largest `k` such that every triangle-free graph on `n` vertices contains an
independent set on `k` vertices. -/
noncomputable def H (n : ℕ) : ℕ :=
  sSup {k | ∀ G : SimpleGraph (Fin n), G.CliqueFree 3 → ∃ s, G.IsNIndepSet k s}

-- [item 3] H(n) is attained: every triangle-free graph has an independent set of size H(n)
theorem aux_H_mem (n : ℕ) : ∀ G : SimpleGraph (Fin n), G.CliqueFree 3 → ∃ s, G.IsNIndepSet (H n) s := by
  let S : Set ℕ := {k | ∀ G : SimpleGraph (Fin n), G.CliqueFree 3 → ∃ s, G.IsNIndepSet k s}
  have hne : S.Nonempty := by
    refine ⟨0, ?_⟩
    intro G hG
    exact ⟨∅, by simp [SimpleGraph.isNIndepSet_iff, SimpleGraph.IsIndepSet]⟩
  have hbd : BddAbove S := by
    refine ⟨n, ?_⟩
    intro k hk
    obtain ⟨s, hs⟩ := hk ⊥ (SimpleGraph.cliqueFree_bot (by omega))
    simpa [hs.card_eq] using s.card_le_univ
  exact Nat.sSup_mem hne hbd

-- [item 5] Complement of a set containing no big maximal clique gives a transversal bound
theorem aux_tau_le_of_free {n : ℕ} (G : SimpleGraph (Fin n)) (U : Finset (Fin n))
    (hU : ∀ s, IsBigMaximalClique G s → ¬ s ⊆ U) :
    cliqueTransversalNumber G ≤ n - U.card := by
  classical
  unfold cliqueTransversalNumber
  apply Nat.sInf_le
  refine ⟨Finset.univ \ U, ?_, ?_⟩
  · intro s hs
    have hex : ∃ v ∈ s, v ∉ U := by
      by_contra h
      apply hU s hs
      intro v hv
      by_contra hvU
      exact h ⟨v, hv, hvU⟩
    obtain ⟨v, hv, hvU⟩ := hex
    exact ⟨v, hv, by simp [hvU]⟩
  · rw [Finset.card_sdiff_of_subset (Finset.subset_univ U)]
    simp

-- [item 6] Reduction to a triangle-free graph whose edges hit all big maximal cliques
theorem aux_reduction {n : ℕ} (G G' : SimpleGraph (Fin n)) (h3 : G'.CliqueFree 3)
    (hcov : ∀ s, IsBigMaximalClique G s → ∃ a ∈ s, ∃ b ∈ s, G'.Adj a b) :
    cliqueTransversalNumber G ≤ n - H n := by
  obtain ⟨U, hU⟩ := aux_H_mem n G' h3
  rw [← hU.card_eq]
  apply aux_tau_le_of_free G U
  intro s hs hsub
  obtain ⟨a, ha, b, hb, hab⟩ := hcov s hs
  exact hU.isIndepSet (hsub ha) (hsub hb) hab.ne hab

-- [item 8] Triangle-free case: τ(G) ≤ n − H(n) when G is K3-free
theorem aux_triangle_free {n : ℕ} (G : SimpleGraph (Fin n)) (hG : G.CliqueFree 3) :
    cliqueTransversalNumber G ≤ n - H n := by
  apply aux_reduction G G hG
  intro s hs
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hs.2
  exact ⟨a, ha, b, hb, hs.1.1 ha hb hab⟩

-- [item 11] Clique transversal number is at most n minus any vertex degree
theorem aux_tau_le_neighbor {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (v : Fin n) : cliqueTransversalNumber G ≤ n - (G.neighborFinset v).card := by
  classical
  apply aux_tau_le_of_free G (G.neighborFinset v)
  intro s hs hsub
  have hinsert : G.IsClique ((insert v s : Finset (Fin n)) : Set (Fin n)) := by
    rw [Finset.coe_insert]
    apply hs.1.1.insert
    intro b hb hne
    exact (G.mem_neighborFinset v b).mp (hsub hb)
  have hv : v ∈ s := hs.1.2 hinsert (Finset.subset_insert v s) (Finset.mem_insert_self v s)
  exact ((G.mem_neighborFinset v v).mp (hsub hv)).ne rfl

-- [item 21] Bounded degree gives an independent set U with n ≤ |U| k
theorem aux_independent_card_mul_degree_bound {n k : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hd : ∀ v, (G.neighborFinset v).card < k) :
    ∃ U : Finset (Fin n), G.IsIndepSet (U : Set (Fin n)) ∧ n ≤ U.card * k := by
  classical
  obtain ⟨U, hU⟩ := G.maximumIndepSet_exists
  have hcover : Finset.univ ⊆ U.biUnion (fun v ↦ insert v (G.neighborFinset v)) := by
    intro v hv
    by_contra hn
    have hvU : v ∉ U := by
      intro hvU
      exact hn (Finset.mem_biUnion.mpr ⟨v, hvU, Finset.mem_insert_self _ _⟩)
    have hno : ∀ u ∈ U, ¬ G.Adj u v := by
      intro u hu hadj
      exact hn (Finset.mem_biUnion.mpr ⟨u, hu, Finset.mem_insert_of_mem ((G.mem_neighborFinset u v).mpr hadj)⟩)
    have hins : G.IsIndepSet ((insert v U : Finset (Fin n)) : Set (Fin n)) := by
      rw [← SimpleGraph.isClique_compl, Finset.coe_insert]
      apply ((SimpleGraph.isClique_compl G).mpr hU.isIndepSet).insert
      intro u hu hne
      exact ⟨hne, fun hadj ↦ hno u hu hadj.symm⟩
    have hh := hU.maximum (insert v U) hins
    rw [Finset.card_insert_of_notMem hvU] at hh
    omega
  refine ⟨U, hU.isIndepSet, ?_⟩
  calc
    n = (Finset.univ : Finset (Fin n)).card := by simp
    _ ≤ (U.biUnion (fun v ↦ insert v (G.neighborFinset v))).card := Finset.card_le_card hcover
    _ ≤ ∑ v ∈ U, (insert v (G.neighborFinset v)).card := Finset.card_biUnion_le
    _ ≤ ∑ v ∈ U, k := Finset.sum_le_sum (fun v hv ↦ (Finset.card_insert_le v _).trans (by have := hd v; omega))
    _ = U.card * k := by simp

-- [item 23] Independent-set complement bounds clique transversal number
theorem aux_tau_le_of_independent {n : ℕ} (G : SimpleGraph (Fin n))
    (U : Finset (Fin n)) (hU : G.IsIndepSet (U : Set (Fin n))) :
    cliqueTransversalNumber G ≤ n - U.card := by
  apply aux_tau_le_of_free G U
  intro s hs hsub
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hs.2
  exact hU (hsub ha) (hsub hb) hab (hs.1.1 ha hb hab)

-- [item 24] Square-root bound: τ(G) ≤ n − Nat.sqrt n
theorem aux_sqrt_bound (n : ℕ) (G : SimpleGraph (Fin n)) :
    cliqueTransversalNumber G ≤ n - Nat.sqrt n := by
  classical
  by_cases hd : ∃ v, Nat.sqrt n ≤ (G.neighborFinset v).card
  · obtain ⟨v, hv⟩ := hd
    exact (aux_tau_le_neighbor G v).trans (Nat.sub_le_sub_left hv n)
  · have hdeg : ∀ v, (G.neighborFinset v).card < Nat.sqrt n := by
      intro v
      have : ¬ Nat.sqrt n ≤ (G.neighborFinset v).card := fun hv ↦ hd ⟨v, hv⟩
      omega
    obtain ⟨U, hU, hcard⟩ := aux_independent_card_mul_degree_bound G hdeg
    have hs : Nat.sqrt n ≤ U.card := by
      have hsq := Nat.sqrt_le n
      by_contra hh
      have hlt : U.card < Nat.sqrt n := by omega
      have hpos : 0 < Nat.sqrt n := by omega
      have := Nat.mul_lt_mul_of_pos_right hlt hpos
      omega
    exact (aux_tau_le_of_independent G U hU).trans (Nat.sub_le_sub_left hs n)

-- [item 27] Case C structural bound: every clique has at most four vertices
theorem aux_caseC_clique_card {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h : ∀ a b, G.Adj a b → (Finset.univ.filter (fun c => G.Adj a c ∧ G.Adj b c)).card ≤ 2)
    (s : Finset (Fin n)) (hs : G.IsClique (s : Set (Fin n))) : s.card ≤ 4 := by
  classical
  by_cases hsmall : s.card ≤ 1
  · omega
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < s.card)
  have hsub : (s.erase a).erase b ⊆ Finset.univ.filter (fun c => G.Adj a c ∧ G.Adj b c) := by
    intro c hc
    obtain ⟨hcb, hca, hc⟩ := Finset.mem_erase.mp hc |>.imp_right Finset.mem_erase.mp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hs ha hc hca.symm, hs hb hc hcb.symm⟩
  have hcard := (Finset.card_le_card hsub).trans (h a b (hs ha hb hab))
  rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hab.symm, hb⟩), Finset.card_erase_of_mem ha] at hcard
  omega

-- [item 29] Case C: K5-free, and a K4 edge has exactly its two internal common neighbors
theorem aux_caseC_common_neighbors {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h : ∀ a b, G.Adj a b → (Finset.univ.filter (fun c => G.Adj a c ∧ G.Adj b c)).card ≤ 2)
    (s : Finset (Fin n)) (hs : G.IsClique (s : Set (Fin n))) (hcard : s.card = 4)
    {a b : Fin n} (ha : a ∈ s) (hb : b ∈ s) (hab : a ≠ b) :
    Finset.univ.filter (fun c => G.Adj a c ∧ G.Adj b c) = (s.erase a).erase b := by
  classical
  apply Eq.symm
  apply Finset.eq_of_subset_of_card_le
  · intro c hc
    obtain ⟨hcb, hca, hc⟩ := Finset.mem_erase.mp hc |>.imp_right Finset.mem_erase.mp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hs ha hc hca.symm, hs hb hc hcb.symm⟩
  · rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hab.symm, hb⟩), Finset.card_erase_of_mem ha, hcard]
    exact h a b (hs ha hb hab)

theorem aux_caseC_cliqueFree_five {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h : ∀ a b, G.Adj a b → (Finset.univ.filter (fun c => G.Adj a c ∧ G.Adj b c)).card ≤ 2) : G.CliqueFree 5 := by
  intro s hs
  have := aux_caseC_clique_card G h s hs.isClique
  have := hs.card_eq
  omega

-- [item 30] Case C: a clique sharing a K4 edge lies inside it; distinct K4s are edge-disjoint
theorem aux_caseC_clique_absorbed {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h : ∀ a b, G.Adj a b → (Finset.univ.filter (fun c => G.Adj a c ∧ G.Adj b c)).card ≤ 2)
    (s t : Finset (Fin n)) (hs : G.IsClique (s : Set (Fin n))) (hcard : s.card = 4)
    (ht : G.IsClique (t : Set (Fin n))) {a b : Fin n}
    (ha : a ∈ s) (hb : b ∈ s) (hat : a ∈ t) (hbt : b ∈ t) (hab : a ≠ b) : t ⊆ s := by
  classical
  intro c hc
  by_cases hca : c = a
  · simpa [hca] using ha
  by_cases hcb : c = b
  · simpa [hcb] using hb
  have hm : c ∈ Finset.univ.filter (fun c => G.Adj a c ∧ G.Adj b c) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨ht hat hc (Ne.symm hca), ht hbt hc (Ne.symm hcb)⟩
  rw [aux_caseC_common_neighbors G h s hs hcard ha hb hab] at hm
  exact Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hm)

theorem aux_caseC_four_cliques_equal {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h : ∀ a b, G.Adj a b → (Finset.univ.filter (fun c => G.Adj a c ∧ G.Adj b c)).card ≤ 2)
    (s t : Finset (Fin n)) (hs : G.IsClique (s : Set (Fin n))) (hcard : s.card = 4)
    (ht : G.IsClique (t : Set (Fin n))) (htcard : t.card = 4) {a b : Fin n}
    (ha : a ∈ s) (hb : b ∈ s) (hat : a ∈ t) (hbt : b ∈ t) (hab : a ≠ b) : t = s := by
  apply Finset.eq_of_subset_of_card_le (aux_caseC_clique_absorbed G h s t hs hcard ht ha hb hat hbt hab)
  omega

-- [item 66] Double counting for triple systems of maximum vertex degree two
theorem aux_degree_two_incidence_bound {α : Type*} [DecidableEq α]
    (F : Finset (Finset α))
    (hsize : ∀ e ∈ F, e.card = 3)
    (hdeg : ∀ v, (F.filter (v ∈ ·)).card ≤ 2) :
    3 * F.card ≤ 2 * (F.biUnion id).card := by
  classical
  have hcount : (∑ e ∈ F, e.card) = ∑ v ∈ F.biUnion id, (F.filter (v ∈ ·)).card := by
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro e he
    rw [← Finset.sum_filter]
    congr 1
    ext v
    simp only [Finset.mem_filter, Finset.mem_biUnion, id_eq]
    exact ⟨fun hv => ⟨⟨e, he, hv⟩, hv⟩, fun hv => hv.2⟩
  calc
    3 * F.card = ∑ e ∈ F, e.card := by
      rw [Finset.sum_congr rfl hsize]
      simp [Nat.mul_comm]
    _ = ∑ v ∈ F.biUnion id, (F.filter (v ∈ ·)).card := hcount
    _ ≤ ∑ v ∈ F.biUnion id, 2 := Finset.sum_le_sum (fun v _ => hdeg v)
    _ = 2 * (F.biUnion id).card := by simp [Nat.mul_comm]

-- [item 73] A permutation of incident hyperedges yields a valid two-colouring
theorem aux_coloring_of_incidence_permutation {α ι : Type*} [DecidableEq α]
    (E : ι → Finset α) (p : ι → ι) (hp : Function.Bijective p)
    (r : ι → α) (hr : ∀ i, r i ∈ E i)
    (hsize : ∀ i, 3 ≤ (E i).card)
    (hinc : ∀ i j, r i ∈ E j → j = i ∨ j = p i) :
    ∃ c : α → Bool, ∀ i, ∃ x ∈ E i, ∃ y ∈ E i, c x ≠ c y := by
  classical
  let c : α → Bool := fun x => decide (x ∈ Set.range r)
  refine ⟨c, ?_⟩
  intro i
  obtain ⟨q, hq⟩ := hp.surjective i
  have hex : ∃ y ∈ E i, y ∉ ({r i, r q} : Finset α) := by
    by_contra hh
    have hsub : E i ⊆ {r i, r q} := by
      intro y hy
      by_contra hyn
      exact hh ⟨y, hy, hyn⟩
    have hc := (Finset.card_le_card hsub).trans Finset.card_le_two
    have := hsize i
    omega
  obtain ⟨y, hy, hyn⟩ := hex
  have hnot : y ∉ Set.range r := by
    rintro ⟨j, rfl⟩
    rcases hinc j i hy with hij | hij
    · exact hyn (by simp [hij])
    · have hjq : j = q := hp.injective (hij.symm.trans hq.symm)
      subst j
      exact hyn (by simp)
  refine ⟨r i, hr i, y, hy, ?_⟩
  have hc1 : c (r i) = true := by simp only [c, decide_eq_true_eq]; exact ⟨i, rfl⟩
  have hc2 : c y = false := by simp only [c, decide_eq_false_iff_not]; exact hnot
  rw [hc1, hc2]
  decide

-- [item 74] Regular symmetric nonnegative integer matrices admit a supported permutation (Hall proof)
theorem aux_regular_symmetric_matrix_permutation {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : ι → ι → ℕ) (d : ℕ) (hd : 0 < d)
    (hsym : ∀ i j, w i j = w j i) (hrow : ∀ i, ∑ j, w i j = d) :
    ∃ p : ι → ι, Function.Bijective p ∧ ∀ i, 0 < w i (p i) := by
  classical
  let t : ι → Finset ι := fun i => Finset.univ.filter (fun j => 0 < w i j)
  have hhall : ∀ s : Finset ι, s.card ≤ (s.biUnion t).card := by
    intro s
    let N := s.biUnion t
    have heq : ∀ i ∈ s, ∑ j ∈ N, w i j = d := by
      intro i hi
      rw [← hrow i]
      apply Finset.sum_subset (Finset.subset_univ N)
      intro j hj hjN
      have : ¬ 0 < w i j := by
        intro hp
        exact hjN (Finset.mem_biUnion.mpr ⟨i, hi, by simp [t, hp]⟩)
      omega
    have hle : s.card * d ≤ N.card * d := calc
      s.card * d = ∑ i ∈ s, ∑ j ∈ N, w i j := by
        rw [Finset.sum_congr rfl heq]
        simp
      _ = ∑ j ∈ N, ∑ i ∈ s, w i j := Finset.sum_comm
      _ ≤ ∑ j ∈ N, d := by
        apply Finset.sum_le_sum
        intro j hj
        calc
          ∑ i ∈ s, w i j ≤ ∑ i, w i j := Finset.sum_le_univ_sum_of_nonneg (fun _ => Nat.zero_le _)
          _ = d := by simp_rw [hsym]; exact hrow j
      _ = N.card * d := by simp
    exact Nat.le_of_mul_le_mul_right hle hd
  obtain ⟨p, hp, hpm⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective t).mp hhall
  refine ⟨p, (Fintype.bijective_iff_injective_and_card p).mpr ⟨hp, rfl⟩, ?_⟩
  intro i
  simpa [t] using hpm i

-- [item 76] Euler-free full colouring core in multigraph incidence form via Hall's theorem
theorem aux_multigraph_incidence_coloring {α ι : Type*} [DecidableEq α]
    [Fintype ι] [DecidableEq ι] (E : ι → Finset α)
    (hsize : ∀ i, (E i).card = 3) (other : α → ι → ι)
    (hother : ∀ i x, x ∈ E i → x ∈ E (other x i))
    (hinv : ∀ i x, x ∈ E i → other x (other x i) = i)
    (hinc : ∀ i j x, x ∈ E i → x ∈ E j → j = i ∨ j = other x i) :
    ∃ c : α → Bool, ∀ i, ∃ x ∈ E i, ∃ y ∈ E i, c x ≠ c y := by
  classical
  let w : ι → ι → ℕ := fun i j => ((E i).filter (fun x => other x i = j)).card
  have hsym : ∀ i j, w i j = w j i := by
    intro i j
    dsimp [w]
    congr 1
    ext x
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hx, h⟩
      subst j
      exact ⟨hother i x hx, hinv i x hx⟩
    · rintro ⟨hx, h⟩
      subst i
      exact ⟨hother j x hx, hinv j x hx⟩
  have hrow : ∀ i, ∑ j, w i j = 3 := by
    intro i
    dsimp [w]
    rw [Finset.sum_card_fiberwise_eq_card_filter]
    simpa using hsize i
  obtain ⟨p, hp, hpos⟩ := aux_regular_symmetric_matrix_permutation w 3 (by omega) hsym hrow
  have hex : ∀ i, ∃ x ∈ E i, other x i = p i := by
    intro i
    obtain ⟨x, hx⟩ := Finset.card_pos.mp (hpos i)
    exact ⟨x, (Finset.mem_filter.mp hx).1, (Finset.mem_filter.mp hx).2⟩
  choose r hr hpr using hex
  apply aux_coloring_of_incidence_permutation E p hp r hr (fun i => by rw [hsize])
  intro i j hij
  rcases hinc i j (r i) (hr i) hij with h | h
  · exact Or.inl h
  · exact Or.inr (h.trans (hpr i))

-- [item 80] Every finite 3-uniform hypergraph of maximum vertex degree two has a nonmonochromatic two-colouring
theorem aux_degree_two_hypergraph_coloring {α : Type*} [DecidableEq α]
    (F : Finset (Finset α))
    (hsize : ∀ e ∈ F, e.card = 3)
    (hdeg : ∀ v, (F.filter (v ∈ ·)).card ≤ 2) :
    ∃ c : α → Bool, ∀ e ∈ F, ∃ x ∈ e, ∃ y ∈ e, c x ≠ c y := by
  classical
  let I := {e // e ∈ F}
  have uniq : ∀ (x : α) (i j k : I), x ∈ i.val → x ∈ j.val → x ∈ k.val →
      j ≠ i → k ≠ i → j = k := by
    intro x i j k hi hj hk hji hki
    have him : i.val ∈ F.filter (x ∈ ·) := Finset.mem_filter.mpr ⟨i.property, hi⟩
    have hc : ((F.filter (x ∈ ·)).erase i.val).card ≤ 1 := by
      rw [Finset.card_erase_of_mem him]
      have := hdeg x
      omega
    apply Subtype.ext
    apply Finset.card_le_one.mp hc j.val _ k.val _
    · exact Finset.mem_erase.mpr ⟨fun he => hji (Subtype.ext he), Finset.mem_filter.mpr ⟨j.property, hj⟩⟩
    · exact Finset.mem_erase.mpr ⟨fun he => hki (Subtype.ext he), Finset.mem_filter.mpr ⟨k.property, hk⟩⟩
  let other : α → I → I := fun x i =>
    if h : ∃ j : I, j ≠ i ∧ x ∈ j.val then h.choose else i
  have step : ∀ (x : α) (i j : I), x ∈ i.val → x ∈ j.val → j ≠ i → other x i = j := by
    intro x i j hi hj hji
    have hex : ∃ k : I, k ≠ i ∧ x ∈ k.val := ⟨j, hji, hj⟩
    simp only [other, dif_pos hex]
    exact uniq x i hex.choose j hi hex.choose_spec.2 hj hex.choose_spec.1 hji
  have hother : ∀ (i : I) x, x ∈ i.val → x ∈ (other x i).val := by
    intro i x hi
    dsimp [other]
    split
    · exact (Classical.choose_spec ‹∃ j : I, j ≠ i ∧ x ∈ j.val›).2
    · exact hi
  have hinv : ∀ (i : I) x, x ∈ i.val → other x (other x i) = i := by
    intro i x hi
    by_cases he : other x i = i
    · rw [he, he]
    · exact step x (other x i) i (hother i x hi) hi (Ne.symm he)
  have hinc : ∀ (i j : I) x, x ∈ i.val → x ∈ j.val → j = i ∨ j = other x i := by
    intro i j x hi hj
    by_cases he : j = i
    · exact Or.inl he
    · exact Or.inr (step x i j hi hj he).symm
  obtain ⟨c, hc⟩ := aux_multigraph_incidence_coloring (fun i : I => i.val)
    (fun i => hsize i.val i.property) other hother hinv hinc
  exact ⟨c, fun e he => hc ⟨e, he⟩⟩

-- [item 82] Case C incidence adapter: every edge belongs to at most two triangle finsets
theorem aux_caseC_triangles_through_edge {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h : ∀ a b, G.Adj a b → (Finset.univ.filter (fun c => G.Adj a c ∧ G.Adj b c)).card ≤ 2)
    {a b : Fin n} (hab : G.Adj a b) :
    ((G.cliqueFinset 3).filter (fun t => a ∈ t ∧ b ∈ t)).card ≤ 2 := by
  classical
  let C := Finset.univ.filter (fun c => G.Adj a c ∧ G.Adj b c)
  have hsub : (G.cliqueFinset 3).filter (fun t => a ∈ t ∧ b ∈ t) ⊆
      C.image (fun c => ({a, b, c} : Finset (Fin n))) := by
    intro t ht
    obtain ⟨ht, ha, hb⟩ := Finset.mem_filter.mp ht
    have hcl := SimpleGraph.mem_cliqueFinset_iff.mp ht
    have hc : ((t.erase a).erase b).card = 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hab.ne.symm, hb⟩),
        Finset.card_erase_of_mem ha, hcl.card_eq]
    obtain ⟨c, he⟩ := Finset.card_eq_one.mp hc
    have hcm : c ∈ (t.erase a).erase b := by rw [he]; simp
    obtain ⟨hcb, hca, hct⟩ := Finset.mem_erase.mp hcm |>.imp_right Finset.mem_erase.mp
    apply Finset.mem_image.mpr
    refine ⟨c, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcl.isClique ha hct hca.symm,
      hcl.isClique hb hct hcb.symm⟩, ?_⟩
    have hrestore : insert a (insert b ((t.erase a).erase b)) = t := by
      rw [Finset.insert_erase (Finset.mem_erase.mpr ⟨hab.ne.symm, hb⟩), Finset.insert_erase ha]
    simpa [he] using hrestore
  exact (Finset.card_le_card hsub).trans (Finset.card_image_le.trans (h a b hab))

-- [item 84] Case C: all triangle edge-triples admit a nonmonochromatic two-colouring
theorem aux_caseC_triangle_edge_coloring {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h : ∀ a b, G.Adj a b → (Finset.univ.filter (fun c => G.Adj a c ∧ G.Adj b c)).card ≤ 2) :
    ∃ c : Finset (Fin n) → Bool, ∀ t ∈ G.cliqueFinset 3,
      ∃ e ∈ t.powersetCard 2, ∃ f ∈ t.powersetCard 2, c e ≠ c f := by
  classical
  let F := (G.cliqueFinset 3).image (Finset.powersetCard 2)
  have hs : ∀ e ∈ F, e.card = 3 := by
    intro e he
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp he
    rw [Finset.card_powersetCard, (SimpleGraph.mem_cliqueFinset_iff.mp ht).card_eq]
    decide
  have hd : ∀ e, (F.filter (e ∈ ·)).card ≤ 2 := by
    intro e
    rw [show F = (G.cliqueFinset 3).image (Finset.powersetCard 2) from rfl,
      Finset.filter_image]
    apply Finset.card_image_le.trans
    by_cases he : e.card = 2
    · obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp he
      by_cases hadj : G.Adj a b
      · have heq : ((G.cliqueFinset 3).filter (fun t => {a, b} ∈ t.powersetCard 2)) =
            ((G.cliqueFinset 3).filter (fun t => a ∈ t ∧ b ∈ t)) := by
          ext t
          simp [Finset.mem_powersetCard, Finset.card_pair hab, Finset.insert_subset_iff,
            Finset.singleton_subset_iff]
        rw [heq]
        exact aux_caseC_triangles_through_edge G h hadj
      · have heq : ((G.cliqueFinset 3).filter (fun t => {a, b} ∈ t.powersetCard 2)) = ∅ := by
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro t ht
          obtain ⟨ht, hp⟩ := Finset.mem_filter.mp ht
          have hsub := (Finset.mem_powersetCard.mp hp).1
          exact hadj ((SimpleGraph.mem_cliqueFinset_iff.mp ht).isClique
            (hsub (by simp)) (hsub (by simp)) hab)
        rw [heq]
        simp
    · have heq : ((G.cliqueFinset 3).filter (fun t => e ∈ t.powersetCard 2)) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro t ht
        exact he (Finset.mem_powersetCard.mp (Finset.mem_filter.mp ht).2).2
      rw [heq]
      simp
  obtain ⟨c, hc⟩ := aux_degree_two_hypergraph_coloring F hs hd
  exact ⟨c, fun t ht => hc _ (Finset.mem_image.mpr ⟨t, ht, rfl⟩)⟩

-- [item 95] A nonmonochromatic triangle-edge colouring implies the Erdős 151 bound
theorem aux_edge_coloring_certificate {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (c : Finset (Fin n) → Bool)
    (hc : ∀ t ∈ G.cliqueFinset 3, ∃ e ∈ t.powersetCard 2, ∃ f ∈ t.powersetCard 2, c e ≠ c f) :
    cliqueTransversalNumber G ≤ n - H n := by
  classical
  let G' : SimpleGraph (Fin n) := {
    Adj := fun a b => G.Adj a b ∧ (c {a,b} = true ∨ ∀ x, ¬ (G.Adj a x ∧ G.Adj b x))
    symm := ⟨by
      intro a b hab
      refine ⟨hab.1.symm, ?_⟩
      rcases hab.2 with hh | hh
      · exact Or.inl (by simpa [Finset.pair_comm] using hh)
      · exact Or.inr (fun x hx => hh x ⟨hx.2, hx.1⟩)⟩
    loopless := ⟨fun _ ha => G.irrefl ha.1⟩ }
  apply aux_reduction G G'
  · intro t ht
    have htG : t ∈ G.cliqueFinset 3 := by
      apply SimpleGraph.mem_cliqueFinset_iff.mpr
      exact ⟨fun a ha b hb hab => (ht.isClique ha hb hab).1, ht.card_eq⟩
    have hall : ∀ e ∈ t.powersetCard 2, c e = true := by
      intro e he
      obtain ⟨hesub, hecard⟩ := Finset.mem_powersetCard.mp he
      obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hecard
      have ha : a ∈ t := hesub (by simp)
      have hb : b ∈ t := hesub (by simp)
      have hrem : ((t.erase a).erase b).Nonempty := by
        apply Finset.card_pos.mp
        rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hab.symm, hb⟩),
          Finset.card_erase_of_mem ha, ht.card_eq]
        decide
      obtain ⟨x, hx⟩ := hrem
      obtain ⟨hxb, hxa, hxt⟩ := Finset.mem_erase.mp hx |>.imp_right Finset.mem_erase.mp
      rcases (ht.isClique ha hb hab).2 with hh | hh
      · exact hh
      · exact False.elim (hh x ⟨(ht.isClique ha hxt hxa.symm).1, (ht.isClique hb hxt hxb.symm).1⟩)
    obtain ⟨e, he, f, hf, hef⟩ := hc t htG
    exact hef ((hall e he).trans (hall f hf).symm)
  · intro s hs
    by_cases htwo : s.card = 2
    · obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp htwo
      refine ⟨a, by simp, b, by simp, hs.1.1 (by simp) (by simp) hab, Or.inr ?_⟩
      intro x hx
      have hins : G.IsClique ((insert x ({a,b} : Finset (Fin n)) : Finset (Fin n)) : Set (Fin n)) := by
        rw [Finset.coe_insert]
        exact hs.1.1.insert (by
          intro y hy hxy
          simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hy
          rcases hy with rfl | rfl
          · exact hx.1.symm
          · exact hx.2.symm)
      have hxm := hs.1.2 hins (Finset.subset_insert x _) (Finset.mem_insert_self x _)
      simp only [Finset.mem_insert, Finset.mem_singleton] at hxm
      rcases hxm with rfl | rfl
      · exact G.irrefl hx.1
      · exact G.irrefl hx.2
    · have hbig := hs.2
      obtain ⟨t, hts, htcard⟩ := Finset.exists_subset_card_eq (show 3 ≤ s.card by omega)
      have htG : t ∈ G.cliqueFinset 3 := by
        apply SimpleGraph.mem_cliqueFinset_iff.mpr
        exact ⟨fun a ha b hb hab => hs.1.1 (hts ha) (hts hb) hab, htcard⟩
      obtain ⟨e, he, f, hf, hef⟩ := hc t htG
      have hex : ∃ e ∈ t.powersetCard 2, c e = true := by
        cases hce : c e with
        | true => exact ⟨e, he, hce⟩
        | false =>
          refine ⟨f, hf, ?_⟩
          cases hcf : c f with
          | true => rfl
          | false => exact False.elim (hef (hce.trans hcf.symm))
      obtain ⟨e, he, hce⟩ := hex
      obtain ⟨hesub, hecard⟩ := Finset.mem_powersetCard.mp he
      obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hecard
      have ha : a ∈ s := hts (hesub (by simp))
      have hb : b ∈ s := hts (hesub (by simp))
      exact ⟨a, ha, b, hb, hs.1.1 ha hb hab, Or.inl hce⟩

-- [item 96] Case C fully verified: each edge in at most two triangles implies the Erdős 151 bound
theorem aux_caseC {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h : ∀ a b, G.Adj a b → (Finset.univ.filter (fun c => G.Adj a c ∧ G.Adj b c)).card ≤ 2) :
    cliqueTransversalNumber G ≤ n - H n := by
  obtain ⟨c, hc⟩ := aux_caseC_triangle_edge_coloring G h
  exact aux_edge_coloring_certificate G c hc

-- [item 106] An edge intersecting all three edges of a triangle is one of those edges (Fano-realizability obstruction)
theorem aux_triangle_intersecting_edge {α : Type*} [DecidableEq α]
    (a b c : α) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (e : Finset α) (he : e.card = 2)
    (h1 : (e ∩ {a,b}).Nonempty) (h2 : (e ∩ {a,c}).Nonempty)
    (h3 : (e ∩ {b,c}).Nonempty) : e = {a,b} ∨ e = {a,c} ∨ e = {b,c} := by
  obtain ⟨x,y,hxy,rfl⟩ := Finset.card_eq_two.mp he
  simp only [Finset.nonempty_iff_ne_empty] at *
  have h1' : x = a ∨ x = b ∨ y = a ∨ y = b := by
    obtain ⟨z,hz⟩ := Finset.nonempty_iff_ne_empty.mpr h1
    simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hz
    aesop
  have h2' : x = a ∨ x = c ∨ y = a ∨ y = c := by
    obtain ⟨z,hz⟩ := Finset.nonempty_iff_ne_empty.mpr h2
    simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hz
    aesop
  have h3' : x = b ∨ x = c ∨ y = b ∨ y = c := by
    obtain ⟨z,hz⟩ := Finset.nonempty_iff_ne_empty.mpr h3
    simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hz
    aesop
  rcases h1' with h|h|h|h <;> subst_vars <;>
    rcases h2' with h|h|h|h <;> subst_vars <;>
    rcases h3' with h|h|h|h <;> subst_vars <;> simp_all [Finset.pair_comm]

-- [item 115] Triangle-edge realizations forbid a point outside a line incident with all three of its points (sail obstruction)
theorem aux_edge_meeting_triangle_edges {α : Type*} [DecidableEq α] (t e : Finset α)
    (ht : t.card = 3) (he : e.card = 2)
    (h : ∀ f ∈ t.powersetCard 2, (e ∩ f).Nonempty) : e ∈ t.powersetCard 2 := by
  obtain ⟨a,b,c,hab,hac,hbc,rfl⟩ := Finset.card_eq_three.mp ht
  have h1 := h {a,b} (by simp [Finset.mem_powersetCard, hab])
  have h2 := h {a,c} (by simp [Finset.mem_powersetCard, hac])
  have h3 := h {b,c} (by simp [Finset.mem_powersetCard, hbc])
  rcases aux_triangle_intersecting_edge a b c hab hac hbc e he h1 h2 h3 with rfl|rfl|rfl <;>
    simp [Finset.mem_powersetCard, hab, hac, hbc]

theorem aux_no_sail_realization {ι α : Type*} [DecidableEq ι] [DecidableEq α]
    (E : ι → Finset α) (hinj : Function.Injective E)
    (S : Finset ι) (t : Finset α) (ht : t.card = 3)
    (him : S.image E = t.powersetCard 2)
    (p : ι) (hp : p ∉ S) (he : (E p).card = 2)
    (h : ∀ q ∈ S, (E p ∩ E q).Nonempty) : False := by
  have hm : E p ∈ t.powersetCard 2 := aux_edge_meeting_triangle_edges t (E p) ht he (by
    intro f hf
    rw [← him] at hf
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hf
    exact h q hq)
  rw [← him] at hm
  obtain ⟨q,hq,heq⟩ := Finset.mem_image.mp hm
  exact hp (hinj heq ▸ hq)

-- [item 153] Square triple systems of maximum degree three are cubic (conditional counting step of locally cubic reduction)
theorem aux_square_triples_cubic {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (hsize : ∀ e ∈ F, e.card = 3)
    (hdeg : ∀ v, (F.filter (v ∈ ·)).card ≤ 3)
    (hsquare : (F.biUnion id).card ≤ F.card) :
    ∀ v ∈ F.biUnion id, (F.filter (v ∈ ·)).card = 3 := by
  classical
  have hcount : (∑ e ∈ F, e.card) = ∑ v ∈ F.biUnion id, (F.filter (v ∈ ·)).card := by
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro e he
    rw [← Finset.sum_filter]
    congr 1
    ext v
    simp only [Finset.mem_filter, Finset.mem_biUnion, id_eq]
    exact ⟨fun hv => ⟨⟨e, he, hv⟩, hv⟩, fun hv => hv.2⟩
  have heq : (∑ v ∈ F.biUnion id, (F.filter (v ∈ ·)).card) =
      ∑ _v ∈ F.biUnion id, 3 := by
    apply Nat.le_antisymm
    · exact Finset.sum_le_sum (fun v _ => hdeg v)
    · rw [← hcount, Finset.sum_congr rfl hsize]
      simpa using Nat.mul_le_mul_right 3 hsquare
  exact (Finset.sum_eq_sum_iff_of_le (fun v _ => hdeg v)).mp heq

-- [item 167] Every five-colorable graph satisfies the Erdős 151 bound via the Ramsey K5 edge template
theorem aux_five_color_triangle_template (a b c : Fin 5) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
  let R : Finset (Finset (Fin 5)) := {{0,1},{1,2},{2,3},{3,4},{4,0}}
  decide ({a,b} ∈ R) ≠ decide ({a,c} ∈ R) ∨
  decide ({a,b} ∈ R) ≠ decide ({b,c} ∈ R) := by
  revert a b c
  decide +kernel

theorem aux_five_colorable_bound {n : ℕ} (G : SimpleGraph (Fin n)) (h : G.Colorable 5) :
    cliqueTransversalNumber G ≤ n - H n := by
  classical
  obtain ⟨f⟩ := h
  let R : Finset (Finset (Fin 5)) := {{0,1},{1,2},{2,3},{3,4},{4,0}}
  let c : Finset (Fin n) → Bool := fun e => decide (e.image f ∈ R)
  apply aux_edge_coloring_certificate G c
  intro t ht
  have hcl := SimpleGraph.mem_cliqueFinset_iff.mp ht
  obtain ⟨a,b,d,hab,had,hbd,heq⟩ := Finset.card_eq_three.mp hcl.card_eq
  subst t
  have hab' := f.valid (hcl.isClique (by simp) (by simp) hab)
  have had' := f.valid (hcl.isClique (by simp) (by simp) had)
  have hbd' := f.valid (hcl.isClique (by simp) (by simp) hbd)
  rcases aux_five_color_triangle_template (f a) (f b) (f d) hab' had' hbd' with hh | hh
  · refine ⟨{a,b}, ?_, {a,d}, ?_, ?_⟩
    · simp [Finset.mem_powersetCard, hab]
    · simp [Finset.mem_powersetCard, had]
    · simpa [c, R] using hh
  · refine ⟨{a,b}, ?_, {b,d}, ?_, ?_⟩
    · simp [Finset.mem_powersetCard, hab]
    · simp [Finset.mem_powersetCard, hbd]
    · simpa [c, R] using hh

-- [item 168] K5 refutes the proposed universal triangle-free vertex-bipartition for locally cubic graphs
theorem aux_K5_locally_cubic : ∀ a b : Fin 5, a ≠ b →
    (Finset.univ.filter (fun c : Fin 5 => a ≠ c ∧ b ≠ c)).card = 3 := by
  decide +kernel

theorem aux_K5_no_triangle_free_bipartition :
    ¬ ∃ f : Fin 5 → Bool, ∀ a b c : Fin 5,
      a ≠ b → a ≠ c → b ≠ c → ¬ (f a = f b ∧ f b = f c) := by
  decide +kernel

-- [item 169] Single-edge-flip descent for monochromatic triangles can stall already on K5
theorem aux_K5_edge_flip_local_minimum :
  let E := (Finset.univ : Finset (Fin 5)).powersetCard 2
  let T := (Finset.univ : Finset (Fin 5)).powersetCard 3
  let R : Finset (Finset (Fin 5)) := {{0,2},{0,3},{0,4},{1,2},{1,3}}
  let bad := fun S : Finset (Finset (Fin 5)) =>
    (T.filter (fun t => (∀ e ∈ t.powersetCard 2, e ∈ S) ∨ (∀ e ∈ t.powersetCard 2, e ∉ S))).card
  bad R = 1 ∧ ∀ e ∈ E, 1 ≤ bad (if e ∈ R then R.erase e else insert e R) := by
  decide +kernel

-- [item 170] Locally cubic K5 has no partition into two triangle-free induced subgraphs
theorem aux_K5_vertex_partition_obstruction :
    (∀ a b : Fin 5, (⊤ : SimpleGraph (Fin 5)).Adj a b →
      (Finset.univ.filter (fun c => (⊤ : SimpleGraph (Fin 5)).Adj a c ∧
        (⊤ : SimpleGraph (Fin 5)).Adj b c)).card = 3) ∧
    (∀ c : Fin 5 → Bool, ∃ a b d : Fin 5,
      a ≠ b ∧ a ≠ d ∧ b ≠ d ∧ c a = c b ∧ c b = c d) := by
  decide

-- [item 175] Explicit nonmonochromatic triangle-edge colouring for every five-colorable graph
theorem aux_five_colorable_edge_coloring {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (h : G.Colorable 5) :
    ∃ c : Finset (Fin n) → Bool, ∀ t ∈ G.cliqueFinset 3,
      ∃ e ∈ t.powersetCard 2, ∃ f ∈ t.powersetCard 2, c e ≠ c f := by
  classical
  obtain ⟨f⟩ := h
  let R : Finset (Finset (Fin 5)) := {{0,1},{1,2},{2,3},{3,4},{4,0}}
  let c : Finset (Fin n) → Bool := fun e => decide (e.image f ∈ R)
  refine ⟨c, ?_⟩
  intro t ht
  have hcl := SimpleGraph.mem_cliqueFinset_iff.mp ht
  obtain ⟨a,b,d,hab,had,hbd,heq⟩ := Finset.card_eq_three.mp hcl.card_eq
  subst t
  have hab' := f.valid (hcl.isClique (by simp) (by simp) hab)
  have had' := f.valid (hcl.isClique (by simp) (by simp) had)
  have hbd' := f.valid (hcl.isClique (by simp) (by simp) hbd)
  rcases aux_five_color_triangle_template (f a) (f b) (f d) hab' had' hbd' with hh | hh
  · refine ⟨{a,b}, ?_, {a,d}, ?_, ?_⟩
    · simp [Finset.mem_powersetCard, hab]
    · simp [Finset.mem_powersetCard, had]
    · simpa [c, R] using hh
  · refine ⟨{a,b}, ?_, {b,d}, ?_, ?_⟩
    · simp [Finset.mem_powersetCard, hab]
    · simp [Finset.mem_powersetCard, hbd]
    · simpa [c, R] using hh

-- [item 181] Homomorphism pullback of a triangle-edge template implies Erdős 151
theorem aux_hom_template_bound {n m : ℕ} (G : SimpleGraph (Fin n)) (K : SimpleGraph (Fin m))
    (f : G →g K) (c : Finset (Fin m) → Bool)
    (hc : ∀ a b d, K.Adj a b → K.Adj a d → K.Adj b d →
      c {a,b} ≠ c {a,d} ∨ c {a,b} ≠ c {b,d}) :
    cliqueTransversalNumber G ≤ n - H n := by
  classical
  apply aux_edge_coloring_certificate G (fun e => c (e.image f))
  intro t ht
  have hcl := SimpleGraph.mem_cliqueFinset_iff.mp ht
  obtain ⟨a,b,d,hab,had,hbd,heq⟩ := Finset.card_eq_three.mp hcl.card_eq
  subst t
  have hab' := f.map_adj (hcl.isClique (by simp) (by simp) hab)
  have had' := f.map_adj (hcl.isClique (by simp) (by simp) had)
  have hbd' := f.map_adj (hcl.isClique (by simp) (by simp) hbd)
  rcases hc (f a) (f b) (f d) hab' had' hbd' with hh | hh
  · refine ⟨{a,b}, ?_, {a,d}, ?_, ?_⟩
    · simp [Finset.mem_powersetCard, hab]
    · simp [Finset.mem_powersetCard, had]
    · simpa using hh
  · refine ⟨{a,b}, ?_, {b,d}, ?_, ?_⟩
    · simp [Finset.mem_powersetCard, hab]
    · simp [Finset.mem_powersetCard, hbd]
    · simpa using hh

-- [item 182] A ten-vertex six-chromatic template: the join of two pentagons has a nonmonochromatic triangle-edge colouring, and its homomorphic preimages satisfy E
theorem aux_two_pentagons_edge_template :
    let K := SimpleGraph.fromRel (fun a b : Fin 10 => a.val % 2 ≠ b.val % 2 ∨ (a.val + 2) % 10 = b.val)
    let R : Finset (Finset (Fin 10)) := {{0,1},{0,8},{0,2},{0,5},{1,9},{1,3},{1,4},{2,3},{2,4},{2,7},{3,5},{3,6},{4,5},{4,6},{5,7},{6,7},{6,8},{7,9}}
    ∀ a b d, K.Adj a b → K.Adj a d → K.Adj b d →
      decide ({a,b} ∈ R) ≠ decide ({a,d} ∈ R) ∨
      decide ({a,b} ∈ R) ≠ decide ({b,d} ∈ R) := by
  decide +kernel

theorem aux_two_pentagons_hom_bound {n : ℕ} (G : SimpleGraph (Fin n))
    (f : G →g SimpleGraph.fromRel (fun a b : Fin 10 => a.val % 2 ≠ b.val % 2 ∨ (a.val + 2) % 10 = b.val)) :
    cliqueTransversalNumber G ≤ n - H n := by
  classical
  let R : Finset (Finset (Fin 10)) := {{0,1},{0,8},{0,2},{0,5},{1,9},{1,3},{1,4},{2,3},{2,4},{2,7},{3,5},{3,6},{4,5},{4,6},{5,7},{6,7},{6,8},{7,9}}
  exact aux_hom_template_bound G _ f (fun e => decide (e ∈ R)) aux_two_pentagons_edge_template

-- [item 187] Fano sail incidences survive deletion of any one line or replacement of any one point
theorem aux_fano_sail_survives_one_sum :
  let F : Finset (Finset (Fin 7)) :=
    {{0,1,2},{0,3,4},{0,5,6},{1,3,5},{1,4,6},{2,3,6},{2,4,5}}
  (∀ z : Fin 7, ∃ t ∈ F, ∃ p : Fin 7, p ∉ t ∧ p ≠ z ∧ z ∉ t ∧
    ∀ a ∈ t, ∃ s ∈ F, p ∈ s ∧ a ∈ s) ∧
  (∀ d ∈ F, ∃ t ∈ F.erase d, ∃ p : Fin 7, p ∉ t ∧
    ∀ a ∈ t, ∃ s ∈ F.erase d, p ∈ s ∧ a ∈ s) := by
  decide +kernel

-- [item 188] The join of two pentagons is not five-colorable (strict extension of the five-colorable result)
theorem aux_pentagon_three_colors (f : Fin 5 → Fin 5)
    (h : ∀ a : Fin 5, f a ≠ f ⟨(a.val + 1) % 5, Nat.mod_lt _ (by decide)⟩) :
    3 ≤ (Finset.univ.image f).card := by
  revert f
  decide +kernel

theorem aux_two_pentagons_not_five_colorable :
    ¬ (SimpleGraph.fromRel (fun a b : Fin 10 => a.val % 2 ≠ b.val % 2 ∨
      (a.val + 2) % 10 = b.val)).Colorable 5 := by
  rintro ⟨f⟩
  let e : Fin 5 → Fin 10 := fun a => ⟨2*a.val, by omega⟩
  let o : Fin 5 → Fin 10 := fun a => ⟨2*a.val+1, by omega⟩
  have he : ∀ a : Fin 5, (SimpleGraph.fromRel (fun a b : Fin 10 => a.val % 2 ≠ b.val % 2 ∨
      (a.val + 2) % 10 = b.val)).Adj (e a) (e ⟨(a.val+1)%5, Nat.mod_lt _ (by decide)⟩) := by decide +kernel
  have ho : ∀ a : Fin 5, (SimpleGraph.fromRel (fun a b : Fin 10 => a.val % 2 ≠ b.val % 2 ∨
      (a.val + 2) % 10 = b.val)).Adj (o a) (o ⟨(a.val+1)%5, Nat.mod_lt _ (by decide)⟩) := by decide +kernel
  have heo : ∀ a b : Fin 5, (SimpleGraph.fromRel (fun a b : Fin 10 => a.val % 2 ≠ b.val % 2 ∨
      (a.val + 2) % 10 = b.val)).Adj (e a) (o b) := by decide +kernel
  have hc1 := aux_pentagon_three_colors (fun a => f (e a)) (fun a => f.valid (he a))
  have hc2 := aux_pentagon_three_colors (fun a => f (o a)) (fun a => f.valid (ho a))
  have hd : Disjoint (Finset.univ.image (fun a => f (e a)))
      (Finset.univ.image (fun a => f (o a))) := by
    rw [Finset.disjoint_left]
    intro c hc hd
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hc
    obtain ⟨b, _, hb⟩ := Finset.mem_image.mp hd
    exact f.valid (heo a b) hb.symm
  have hu := (Finset.univ.image (fun a => f (e a)) ∪
    Finset.univ.image (fun a => f (o a))).card_le_univ
  rw [Finset.card_union_of_disjoint hd] at hu
  simp only [Fintype.card_fin] at hu
  omega

-- [item 189] The two-pentagon template is six-colorable, hence with the previous obstruction has chromatic number exactly six
theorem aux_two_pentagons_six_colorable :
    (SimpleGraph.fromRel (fun a b : Fin 10 => a.val % 2 ≠ b.val % 2 ∨
      (a.val + 2) % 10 = b.val)).Colorable 6 := by
  let f : Fin 10 → Fin 6 := ![0,1,2,3,0,1,2,3,4,5]
  exact ⟨⟨f, by decide +kernel⟩⟩

-- [item 216] Fano sail witnesses survive any two point attachments
theorem aux_fano_sail_survives_two_points :
  let F : Finset (Finset (Fin 7)) :=
    {{0,1,2},{0,3,4},{0,5,6},{1,3,5},{1,4,6},{2,3,6},{2,4,5}}
  ∀ z w : Fin 7, ∃ t ∈ F, ∃ p : Fin 7,
    p ∉ t ∧ p ≠ z ∧ p ≠ w ∧ z ∉ t ∧ w ∉ t ∧
    ∀ a ∈ t, ∃ s ∈ F, p ∈ s ∧ a ∈ s := by
  decide +kernel

-- [item 217] Fano sail witnesses survive two deleted lines or a mixed point/line attachment
theorem aux_fano_sail_survives_two_lines_or_mixed :
  let L : Fin 7 → Finset (Fin 7) :=
    ![{0,1,2},{0,3,4},{0,5,6},{1,3,5},{1,4,6},{2,3,6},{2,4,5}]
  (∀ d e : Fin 7, ∃ j : Fin 7, j ≠ d ∧ j ≠ e ∧ ∃ p : Fin 7,
    p ∉ L j ∧ ∀ a ∈ L j, ∃ k : Fin 7, k ≠ d ∧ k ≠ e ∧ p ∈ L k ∧ a ∈ L k) ∧
  (∀ z d : Fin 7, ∃ j : Fin 7, j ≠ d ∧ ∃ p : Fin 7,
    p ∉ L j ∧ p ≠ z ∧ z ∉ L j ∧
    ∀ a ∈ L j, ∃ k : Fin 7, k ≠ d ∧ p ∈ L k ∧ a ∈ L k) := by
  dsimp only
  constructor <;> decide +kernel

-- [item 237] Increasing-parent certificate: every maximal clique containing a forward parent edge implies Erdős 151
theorem aux_increasing_parent_bound {n : ℕ} (G : SimpleGraph (Fin n)) (p : Fin n → Fin n)
    (hcov : ∀ s, IsBigMaximalClique G s → ∃ a ∈ s, p a ∈ s ∧ a < p a) :
    cliqueTransversalNumber G ≤ n - H n := by
  let F : SimpleGraph (Fin n) := {
    Adj := fun a b => (a < b ∧ p a = b) ∨ (b < a ∧ p b = a)
    symm := ⟨fun _ _ h => h.symm⟩
    loopless := ⟨by intro a h; rcases h with h|h <;> exact (lt_irrefl a h.1)⟩ }
  apply aux_reduction G F
  · intro s hs
    obtain ⟨a,b,c,hab,hac,hbc,heq⟩ := Finset.card_eq_three.mp hs.card_eq
    subst s
    have h1 := hs.isClique (by simp : a ∈ ({a,b,c} : Finset (Fin n))) (by simp : b ∈ ({a,b,c} : Finset (Fin n))) hab
    have h2 := hs.isClique (by simp : a ∈ ({a,b,c} : Finset (Fin n))) (by simp : c ∈ ({a,b,c} : Finset (Fin n))) hac
    have h3 := hs.isClique (by simp : b ∈ ({a,b,c} : Finset (Fin n))) (by simp : c ∈ ({a,b,c} : Finset (Fin n))) hbc
    change (_ ∧ _) ∨ (_ ∧ _) at h1 h2 h3
    rcases h1 with ⟨h1,e1⟩|⟨h1,e1⟩ <;>
      rcases h2 with ⟨h2,e2⟩|⟨h2,e2⟩ <;>
      rcases h3 with ⟨h3,e3⟩|⟨h3,e3⟩ <;> omega
  · intro s hs
    obtain ⟨a,ha,hp,halt⟩ := hcov s hs
    exact ⟨a,ha,p a,hp,Or.inl ⟨halt,rfl⟩⟩

-- [item 238] Perfect elimination ordering implies the Erdős 151 bound (chordal-graph ordering formulation)
theorem aux_perfect_elimination_bound {n : ℕ} (G : SimpleGraph (Fin n))
    (hPEO : ∀ a b c, a < b → a < c → G.Adj a b → G.Adj a c → b ≠ c → G.Adj b c) :
    cliqueTransversalNumber G ≤ n - H n := by
  classical
  let p : Fin n → Fin n := fun a => if h : ∃ b, a < b ∧ G.Adj a b then h.choose else a
  have hp : ∀ a, (∃ b, a < b ∧ G.Adj a b) → a < p a ∧ G.Adj a (p a) := by
    intro a ha
    simpa only [p, dif_pos ha] using ha.choose_spec
  apply aux_increasing_parent_bound G p
  intro s hs
  have hne : s.Nonempty := Finset.card_pos.mp (by have := hs.2; omega)
  let a := s.min' hne
  have ha : a ∈ s := s.min'_mem hne
  have hmin : ∀ b ∈ s, a ≤ b := fun b hb => s.min'_le b hb
  have hrem : (s.erase a).Nonempty := by
    apply Finset.card_pos.mp
    rw [Finset.card_erase_of_mem ha]
    have := hs.2
    omega
  obtain ⟨b,hb⟩ := hrem
  obtain ⟨hba,hbs⟩ := Finset.mem_erase.mp hb
  have hab : a < b := lt_of_le_of_ne (hmin b hbs) hba.symm
  have hpa := hp a ⟨b,hab,hs.1.1 ha hbs hba.symm⟩
  have hins : G.IsClique ((insert (p a) s : Finset (Fin n)) : Set (Fin n)) := by
    rw [Finset.coe_insert]
    apply hs.1.1.insert
    intro c hc hpc
    by_cases hca : c = a
    · subst c; exact hpa.2.symm
    · exact hPEO a (p a) c hpa.1 (lt_of_le_of_ne (hmin c hc) (Ne.symm hca)) hpa.2
        (hs.1.1 ha hc (Ne.symm hca)) hpc
  exact ⟨a,ha,hs.1.2 hins (Finset.subset_insert _ _) (Finset.mem_insert_self _ _),hpa.1⟩

-- [item 242] Any two-clique-colorable graph satisfies Erdős 151 (only maximal cliques need be bichromatic)
theorem aux_maximal_clique_bipartition_bound {n : ℕ} (G : SimpleGraph (Fin n))
    (c : Fin n → Bool)
    (hc : ∀ s, IsBigMaximalClique G s → ∃ a ∈ s, ∃ b ∈ s, c a ≠ c b) :
    cliqueTransversalNumber G ≤ n - H n := by
  let R : SimpleGraph (Fin n) := {
    Adj := fun a b => G.Adj a b ∧ c a ≠ c b
    symm := ⟨fun a b h => ⟨h.1.symm, h.2.symm⟩⟩
    loopless := ⟨fun a h => h.2 rfl⟩ }
  apply aux_reduction G R
  · intro t ht
    obtain ⟨a,b,d,hab,had,hbd,heq⟩ := Finset.card_eq_three.mp ht.card_eq
    subst t
    have h1 := (ht.isClique (by simp) (by simp) hab).2
    have h2 := (ht.isClique (by simp) (by simp) had).2
    have h3 := (ht.isClique (by simp) (by simp) hbd).2
    cases hca : c a <;> cases hcb : c b <;> cases hcd : c d <;> simp_all
  · intro s hs
    obtain ⟨a,ha,b,hb,hab⟩ := hc s hs
    exact ⟨a,ha,b,hb, hs.1.1 ha hb (fun h => hab (congrArg c h)), hab⟩

-- [item 243] Increasing-parent certificate with an arbitrary injective ranking
theorem aux_ranked_parent_bound {n : ℕ} (G : SimpleGraph (Fin n))
    (r : Fin n → ℕ) (hr : Function.Injective r) (p : Fin n → Fin n)
    (hcov : ∀ s, IsBigMaximalClique G s → ∃ a ∈ s, p a ∈ s ∧ r a < r (p a)) :
    cliqueTransversalNumber G ≤ n - H n := by
  let F : SimpleGraph (Fin n) := {
    Adj := fun a b => (r a < r b ∧ p a = b) ∨ (r b < r a ∧ p b = a)
    symm := ⟨fun _ _ h => h.symm⟩
    loopless := ⟨by intro a h; rcases h with h|h <;> exact (lt_irrefl (r a) h.1)⟩ }
  apply aux_reduction G F
  · intro s hs
    obtain ⟨a,b,c,hab,hac,hbc,heq⟩ := Finset.card_eq_three.mp hs.card_eq
    subst s
    have h1 := hs.isClique (by simp : a ∈ ({a,b,c} : Finset (Fin n))) (by simp : b ∈ ({a,b,c} : Finset (Fin n))) hab
    have h2 := hs.isClique (by simp : a ∈ ({a,b,c} : Finset (Fin n))) (by simp : c ∈ ({a,b,c} : Finset (Fin n))) hac
    have h3 := hs.isClique (by simp : b ∈ ({a,b,c} : Finset (Fin n))) (by simp : c ∈ ({a,b,c} : Finset (Fin n))) hbc
    change (_ ∧ _) ∨ (_ ∧ _) at h1 h2 h3
    have hab' : r a ≠ r b := fun h => hab (hr h)
    have hac' : r a ≠ r c := fun h => hac (hr h)
    have hbc' : r b ≠ r c := fun h => hbc (hr h)
    rcases h1 with ⟨h1,e1⟩|⟨h1,e1⟩ <;>
      rcases h2 with ⟨h2,e2⟩|⟨h2,e2⟩ <;>
      rcases h3 with ⟨h3,e3⟩|⟨h3,e3⟩ <;>
      first | exact hab (e2.symm.trans e3) | exact hac (e1.symm.trans e3) |
        exact hbc (e1.symm.trans e2) | omega
  · intro s hs
    obtain ⟨a,ha,hp,halt⟩ := hcov s hs
    exact ⟨a,ha,p a,hp,Or.inl ⟨halt,rfl⟩⟩

-- [item 244] Erdős 151 for any graph with a perfect elimination ordering expressed by an injective rank
theorem aux_ranked_perfect_elimination_bound {n : ℕ} (G : SimpleGraph (Fin n))
    (r : Fin n → ℕ) (hr : Function.Injective r)
    (hPEO : ∀ a b c, r a < r b → r a < r c → G.Adj a b → G.Adj a c → b ≠ c → G.Adj b c) :
    cliqueTransversalNumber G ≤ n - H n := by
  classical
  let p : Fin n → Fin n := fun a => if h : ∃ b, r a < r b ∧ G.Adj a b then h.choose else a
  have hp : ∀ a, (∃ b, r a < r b ∧ G.Adj a b) → r a < r (p a) ∧ G.Adj a (p a) := by
    intro a ha
    simpa only [p, dif_pos ha] using ha.choose_spec
  apply aux_ranked_parent_bound G r hr p
  intro s hs
  have hne : s.Nonempty := Finset.card_pos.mp (by have := hs.2; omega)
  obtain ⟨a,ha,hmin⟩ := s.exists_min_image r hne
  have hrem : (s.erase a).Nonempty := by
    apply Finset.card_pos.mp
    rw [Finset.card_erase_of_mem ha]
    have := hs.2
    omega
  obtain ⟨b,hb⟩ := hrem
  obtain ⟨hba,hbs⟩ := Finset.mem_erase.mp hb
  have hab : r a < r b := lt_of_le_of_ne (hmin b hbs) (fun h => hba (hr h).symm)
  have hpa := hp a ⟨b,hab,hs.1.1 ha hbs hba.symm⟩
  have hins : G.IsClique ((insert (p a) s : Finset (Fin n)) : Set (Fin n)) := by
    rw [Finset.coe_insert]
    apply hs.1.1.insert
    intro c hc hpc
    by_cases hca : c = a
    · subst c; exact hpa.2.symm
    · exact hPEO a (p a) c hpa.1
        (lt_of_le_of_ne (hmin c hc) (fun h => hca (hr h).symm)) hpa.2
        (hs.1.1 ha hc (Ne.symm hca)) hpc
  exact ⟨a,ha,hs.1.2 hins (Finset.subset_insert _ _) (Finset.mem_insert_self _ _),hpa.1⟩

-- [item 252] Pairwise intersecting two-element sets form a star or lie in a triangle
theorem aux_pairwise_edges_star_or_triangle {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (hne : F.Nonempty)
    (hs : ∀ e ∈ F, e.card = 2)
    (hi : ∀ e ∈ F, ∀ f ∈ F, (e ∩ f).Nonempty) :
    (∃ v, ∀ e ∈ F, v ∈ e) ∨
      ∃ t : Finset α, t.card = 3 ∧ F ⊆ t.powersetCard 2 := by
  classical
  obtain ⟨e,he⟩ := hne
  obtain ⟨x,y,hxy,rfl⟩ := Finset.card_eq_two.mp (hs e he)
  by_cases hx : ∀ e ∈ F, x ∈ e
  · exact Or.inl ⟨x,hx⟩
  push Not at hx
  obtain ⟨f,hf,hxf⟩ := hx
  have hyf : y ∈ f := by
    obtain ⟨v,hv⟩ := hi {x,y} he f hf
    simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv.1 with rfl|rfl
    · exact False.elim (hxf hv.2)
    · exact hv.2
  obtain ⟨u,v,huv,hfe⟩ := Finset.card_eq_two.mp (hs f hf)
  have hex : ∃ z, y ≠ z ∧ x ≠ z ∧ f = {y,z} := by
    rw [hfe] at hyf hxf
    simp only [Finset.mem_insert, Finset.mem_singleton] at hyf hxf
    rcases hyf with rfl|rfl
    · exact ⟨v,huv,fun h => hxf (Or.inr h),hfe⟩
    · exact ⟨u,huv.symm,fun h => hxf (Or.inl h),hfe.trans (Finset.pair_comm _ _)⟩
  obtain ⟨z,hyz,hxz,rfl⟩ := hex
  by_cases hy : ∀ e ∈ F, y ∈ e
  · exact Or.inl ⟨y,hy⟩
  push Not at hy
  obtain ⟨g,hg,hyg⟩ := hy
  have hxg : x ∈ g := by
    obtain ⟨v,hv⟩ := hi {x,y} he g hg
    simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv.1 with rfl|rfl
    · exact hv.2
    · exact False.elim (hyg hv.2)
  have hzg : z ∈ g := by
    obtain ⟨v,hv⟩ := hi {y,z} hf g hg
    simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv.1 with rfl|rfl
    · exact False.elim (hyg hv.2)
    · exact hv.2
  have hge : g = {x,z} := by
    apply Finset.eq_of_subset_of_card_le
    · intro v hv
      by_contra hvn
      have hsub : {x,z,v} ⊆ g := by simp [Finset.insert_subset_iff, hxg,hzg,hv]
      have hcard := Finset.card_le_card hsub
      have hnvx : v ≠ x := by intro h; subst v; simp at hvn
      have hnvz : v ≠ z := by intro h; subst v; simp at hvn
      simp [Finset.card_insert_of_notMem,hxz,hnvx.symm,hnvz.symm,hs g hg] at hcard
    · simp [hs g hg,hxz]
  subst g
  refine Or.inr ⟨{x,y,z}, by simp [hxy,hxz,hyz], ?_⟩
  intro e he'
  rcases aux_triangle_intersecting_edge x y z hxy hxz hyz e (hs e he')
    (hi e he' {x,y} he) (hi e he' {x,z} hg) (hi e he' {y,z} hf) with rfl|rfl|rfl <;>
    simp [Finset.mem_powersetCard,hxy,hxz,hyz]

-- [item 253] Every nontrivial complete join has a bipartite maximal-clique certificate and satisfies Erdős 151
theorem aux_complete_join_bound {n : ℕ} (G : SimpleGraph (Fin n))
    (c : Fin n → Bool) (h0 : ∃ v, c v = false) (h1 : ∃ v, c v = true)
    (hcross : ∀ a b, c a ≠ c b → G.Adj a b) :
    cliqueTransversalNumber G ≤ n - H n := by
  apply aux_maximal_clique_bipartition_bound G c
  intro s hs
  obtain ⟨a, ha⟩ := Finset.card_pos.mp (show 0 < s.card by have := hs.2; omega)
  have hv : ∃ v, c v ≠ c a := by
    cases hca : c a with
    | false => obtain ⟨v,hv⟩ := h1; exact ⟨v, by simp [hv]⟩
    | true => obtain ⟨v,hv⟩ := h0; exact ⟨v, by simp [hv]⟩
  by_contra h
  obtain ⟨v,hv⟩ := hv
  have hmono : ∀ b ∈ s, c b = c a := by
    intro b hb
    by_contra hb'
    exact h ⟨b,hb,a,ha,hb'⟩
  have hins : G.IsClique ((insert v s : Finset (Fin n)) : Set (Fin n)) := by
    rw [Finset.coe_insert]
    apply hs.1.1.insert
    intro b hb _
    apply hcross
    simpa [hmono b hb] using hv
  have hvs : v ∈ s := hs.1.2 hins (Finset.subset_insert _ _) (Finset.mem_insert_self _ _)
  exact hv (hmono v hvs)

-- [item 258] Line graph cliques are stars or root triangles; maximal stars contain every incident edge
theorem aux_line_clique_classification {n : ℕ} {α : Type*} [DecidableEq α]
    (G : SimpleGraph (Fin n)) (E : Fin n → Finset α)
    (hE : ∀ a, (E a).card = 2) (hinj : Function.Injective E)
    (hadj : ∀ a b, G.Adj a b ↔ a ≠ b ∧ (E a ∩ E b).Nonempty)
    (s : Finset (Fin n)) (hs : G.IsClique (s : Set (Fin n))) (hbig : 3 ≤ s.card) :
    (∃ v, ∀ a ∈ s, v ∈ E a) ∨
      ∃ t : Finset α, t.card = 3 ∧ s.image E = t.powersetCard 2 := by
  classical
  have hne : (s.image E).Nonempty := (Finset.card_pos.mp (by omega : 0 < s.card)).image E
  obtain hstar|⟨t,ht,hsub⟩ := aux_pairwise_edges_star_or_triangle (s.image E) hne
    (by intro e he; obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp he; exact hE a)
    (by
      intro e he f hf
      obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp he
      obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hf
      by_cases hab : a = b
      · subst b; simpa using Finset.card_pos.mp (by rw [hE]; decide : 0 < (E a).card)
      · exact ((hadj a b).mp (hs ha hb hab)).2)
  · obtain ⟨v,hv⟩ := hstar
    exact Or.inl ⟨v,fun a ha => hv _ (Finset.mem_image.mpr ⟨a,ha,rfl⟩)⟩
  · refine Or.inr ⟨t,ht,Finset.eq_of_subset_of_card_le hsub ?_⟩
    rw [Finset.card_powersetCard,ht,Finset.card_image_of_injective _ hinj]
    exact hbig

theorem aux_line_maximal_star_full {n : ℕ} {α : Type*} [DecidableEq α]
    (G : SimpleGraph (Fin n)) (E : Fin n → Finset α)
    (hadj : ∀ a b, G.Adj a b ↔ a ≠ b ∧ (E a ∩ E b).Nonempty)
    (s : Finset (Fin n)) (hs : IsBigMaximalClique G s)
    (v : α) (hv : ∀ a ∈ s, v ∈ E a) :
    s = Finset.univ.filter (fun a => v ∈ E a) := by
  classical
  ext a
  simp only [Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · exact hv a
  · intro ha
    have hins : G.IsClique ((insert a s : Finset (Fin n)) : Set (Fin n)) := by
      rw [Finset.coe_insert]
      apply hs.1.1.insert
      intro b hb hab
      exact (hadj a b).mpr ⟨hab,⟨v,Finset.mem_inter.mpr ⟨ha,hv b hb⟩⟩⟩
    exact hs.1.2 hins (Finset.subset_insert a s) (Finset.mem_insert_self a s)

-- [item 259] Every big maximal line-graph clique is a full star or root triangle; ordered-pair encoding adapter
theorem aux_line_big_maximal_classification {n : ℕ} {α : Type*} [DecidableEq α]
    (G : SimpleGraph (Fin n)) (E : Fin n → Finset α)
    (hE : ∀ a, (E a).card = 2) (hinj : Function.Injective E)
    (hadj : ∀ a b, G.Adj a b ↔ a ≠ b ∧ (E a ∩ E b).Nonempty)
    (s : Finset (Fin n)) (hs : IsBigMaximalClique G s) :
    (∃ v, s = Finset.univ.filter (fun a => v ∈ E a)) ∨
      ∃ t : Finset α, t.card = 3 ∧ s.image E = t.powersetCard 2 := by
  classical
  by_cases hc : 3 ≤ s.card
  · rcases aux_line_clique_classification G E hE hinj hadj s hs.1.1 hc with ⟨v,hv⟩|ht
    · exact Or.inl ⟨v,aux_line_maximal_star_full G E hadj s hs v hv⟩
    · exact Or.inr ht
  · have htwo : s.card = 2 := by have := hs.2; omega
    obtain ⟨a,b,hab,rfl⟩ := Finset.card_eq_two.mp htwo
    obtain ⟨v,hv⟩ := ((hadj a b).mp (hs.1.1 (by simp) (by simp) hab)).2
    refine Or.inl ⟨v,aux_line_maximal_star_full G E hadj _ hs v ?_⟩
    intro c hc
    simp only [Finset.mem_insert,Finset.mem_singleton] at hc
    rcases hc with rfl|rfl
    · exact (Finset.mem_inter.mp hv).1
    · exact (Finset.mem_inter.mp hv).2

theorem aux_ordered_edge_encoding {n m : ℕ} (φ : Fin n → Fin m × Fin m)
    (hφ : ∀ a, (φ a).1 < (φ a).2) (hinj : Function.Injective φ) :
    Function.Injective (fun a => ({(φ a).1,(φ a).2} : Finset (Fin m))) ∧
    (∀ a b, (({(φ a).1,(φ a).2} : Finset (Fin m)) ∩ {(φ b).1,(φ b).2}).Nonempty ↔
      (φ a).1 = (φ b).1 ∨ (φ a).1 = (φ b).2 ∨ (φ a).2 = (φ b).1 ∨ (φ a).2 = (φ b).2) := by
  constructor
  · intro a b hab
    dsimp only at hab
    apply hinj
    have h1 : (φ a).1 = (φ b).1 ∨ (φ a).1 = (φ b).2 := by
      have : (φ a).1 ∈ ({(φ b).1,(φ b).2} : Finset (Fin m)) := by rw [← hab]; simp
      simpa using this
    have h2 : (φ a).2 = (φ b).1 ∨ (φ a).2 = (φ b).2 := by
      have : (φ a).2 ∈ ({(φ b).1,(φ b).2} : Finset (Fin m)) := by rw [← hab]; simp
      simpa using this
    have ha := hφ a
    have hb := hφ b
    apply Prod.ext <;> rcases h1 with h1|h1 <;> rcases h2 with h2|h2 <;> omega
  · intro a b
    simp only [Finset.Nonempty,Finset.mem_inter,Finset.mem_insert,Finset.mem_singleton]
    aesop

-- [item 264] Root triangles and full stars of degree at least three are maximal line-graph cliques
theorem aux_line_root_triangle_maximal {n : ℕ} {α : Type*} [DecidableEq α]
    (G : SimpleGraph (Fin n)) (E : Fin n → Finset α)
    (hE : ∀ a, (E a).card = 2) (hinj : Function.Injective E)
    (hadj : ∀ a b, G.Adj a b ↔ a ≠ b ∧ (E a ∩ E b).Nonempty)
    (s : Finset (Fin n)) (hs : G.IsClique (s : Set (Fin n)))
    (t : Finset α) (ht : t.card = 3) (him : s.image E = t.powersetCard 2) :
    IsBigMaximalClique G s := by
  classical
  have hcard : s.card = 3 := by
    have hh := congrArg Finset.card him
    rw [Finset.card_image_of_injective _ hinj,Finset.card_powersetCard,ht] at hh
    exact hh
  refine ⟨⟨hs,?_⟩,by omega⟩
  intro u hu hsu a hau
  have hm : E a ∈ t.powersetCard 2 := by
    apply aux_edge_meeting_triangle_edges t (E a) ht (hE a)
    intro f hf
    rw [← him] at hf
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hf
    by_cases hab : a = b
    · subst b; simpa using Finset.card_pos.mp (by rw [hE]; decide : 0 < (E a).card)
    · exact ((hadj a b).mp (hu hau (hsu hb) hab)).2
  rw [← him] at hm
  obtain ⟨b,hb,heq⟩ := Finset.mem_image.mp hm
  exact hinj heq ▸ hb

theorem aux_line_star_of_degree_three_maximal {n : ℕ} {α : Type*} [DecidableEq α]
    (G : SimpleGraph (Fin n)) (E : Fin n → Finset α)
    (hE : ∀ a, (E a).card = 2) (hinj : Function.Injective E)
    (hadj : ∀ a b, G.Adj a b ↔ a ≠ b ∧ (E a ∩ E b).Nonempty)
    (v : α) (s : Finset (Fin n))
    (hs : s = Finset.univ.filter (fun a => v ∈ E a)) (hcard : 3 ≤ s.card) :
    IsBigMaximalClique G s := by
  classical
  have hv : ∀ a, a ∈ s ↔ v ∈ E a := by intro a; simp [hs]
  have hcl : G.IsClique (s : Set (Fin n)) := by
    intro a ha b hb hab
    exact (hadj a b).mpr ⟨hab,⟨v,Finset.mem_inter.mpr ⟨(hv a).mp ha,(hv b).mp hb⟩⟩⟩
  refine ⟨⟨hcl,?_⟩,by omega⟩
  intro u hu hsu a hau
  by_contra han
  have hav : v ∉ E a := fun h => han ((hv a).mpr h)
  have hcover : s.image E ⊆ (E a).image (fun w => ({v,w} : Finset α)) := by
    intro e he
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp he
    have hab : a ≠ b := by intro h; subst b; exact han hb
    obtain ⟨w,hw⟩ := ((hadj a b).mp (hu hau (hsu hb) hab)).2
    obtain ⟨hwa,hwb⟩ := Finset.mem_inter.mp hw
    have hvb := (hv b).mp hb
    have hvw : v ≠ w := by intro h; exact hav (h.symm ▸ hwa)
    refine Finset.mem_image.mpr ⟨w,hwa,?_⟩
    apply Finset.eq_of_subset_of_card_le
    · simp [Finset.insert_subset_iff,hvb,hwb]
    · simp [hE b,hvw]
  have hh := (Finset.card_le_card hcover).trans Finset.card_image_le
  rw [Finset.card_image_of_injective _ hinj,hE a] at hh
  omega

-- [item 265] Line graph bound reduces to triangle-free certificate hitting full maximal stars and root triangles
theorem aux_line_local_certificate_bound {n : ℕ} {α : Type*} [DecidableEq α]
    (G R : SimpleGraph (Fin n)) (E : Fin n → Finset α)
    (hE : ∀ a, (E a).card = 2) (hinj : Function.Injective E)
    (hadj : ∀ a b, G.Adj a b ↔ a ≠ b ∧ (E a ∩ E b).Nonempty)
    (hR : R.CliqueFree 3)
    (hstar : ∀ (v : α) (s : Finset (Fin n)), IsBigMaximalClique G s →
      s = Finset.univ.filter (fun a => v ∈ E a) →
      ∃ a ∈ s, ∃ b ∈ s, R.Adj a b)
    (htri : ∀ (t : Finset α) (s : Finset (Fin n)), t.card = 3 →
      s.image E = t.powersetCard 2 → ∃ a ∈ s, ∃ b ∈ s, R.Adj a b) :
    cliqueTransversalNumber G ≤ n - H n := by
  apply aux_reduction G R hR
  intro s hs
  rcases aux_line_big_maximal_classification G E hE hinj hadj s hs with ⟨v,hv⟩|⟨t,ht,him⟩
  · exact hstar v s hs hv
  · exact htri t s ht him

-- [item 284] Line-graph certificate: no triangle containing a through pair
theorem aux_line_through_no_triangle {n : ℕ} (L H : Fin n → ℕ) (hlt : ∀ a, L a < H a)
    (hinj : ∀ a b, L a = L b → H a = H b → a = b)
    (sel : ℕ → Option (Fin n × Fin n))
    (hsel : ∀ v a b, sel v = some (a,b) →
      a ≠ b ∧ (L a = v ∨ H a = v) ∧ (L b = v ∨ H b = v) ∧
      ((∀ d, L d ≠ v) ∨ ((∀ d, H d ≠ v) ∧
      ((∀ c, ¬(L c = min (H a) (H b) ∧ H c = max (H a) (H b))) ∨ ∃ d, L d = max (H a) (H b)))))
    (a b c : Fin n) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (h1 : H a = L b)
    (h2 : (H a = L c ∨ ∃ v, sel v = some (a,c)) ∨ (H c = L a ∨ ∃ v, sel v = some (c,a)))
    (h3 : (H b = L c ∨ ∃ v, sel v = some (b,c)) ∨ (H c = L b ∨ ∃ v, sel v = some (c,b))) :
    False := by
  have la := hlt a; have lb := hlt b; have lc := hlt c
  have iab := fun h h' => hab (hinj a b h h')
  have iac := fun h h' => hac (hinj a c h h')
  have ibc := fun h h' => hbc (hinj b c h h')
  rcases h2 with (h2|⟨v2,e2⟩)|(h2|⟨v2,e2⟩) <;>
    rcases h3 with (h3|⟨v3,e3⟩)|(h3|⟨v3,e3⟩) <;>
    (try have g2 := hsel _ _ _ e2) <;>
    (try have g3 := hsel _ _ _ e3) <;> clear hsel <;>
    (try have q23 : v2 ≠ v3 := by rintro rfl; rw [e2] at e3; cases e3 <;> simp_all) <;>
    (try clear e2) <;> (try clear e3) <;> clear hinj sel <;>
    grind

theorem aux_line_pair_eq {m : ℕ} (p q x y : Fin m) (hpq : p < q) (hxy : x ≠ y)
    (h : ({p,q} : Finset (Fin m)) = {x,y}) :
    (p.val = x.val ∧ q.val = y.val) ∨ (p.val = y.val ∧ q.val = x.val) := by
  have h1 : p ∈ ({x,y} : Finset (Fin m)) := h ▸ by simp
  have h2 : q ∈ ({x,y} : Finset (Fin m)) := h ▸ by simp
  have h3 : x ∈ ({p,q} : Finset (Fin m)) := h.symm ▸ by simp
  simp at h1 h2 h3
  rcases h1 with rfl|rfl <;> rcases h2 with rfl|rfl <;> simp_all [Fin.ext_iff]

-- [item 286] Complete line-certificate triangle-freeness from the verified through-pair core
theorem aux_line_selected_no_triangle {n : ℕ} (L H : Fin n → ℕ) (hlt : ∀ a, L a < H a)
    (hinj : ∀ a b, L a = L b → H a = H b → a = b)
    (sel : ℕ → Option (Fin n × Fin n))
    (hsel : ∀ v a b, sel v = some (a,b) →
      a ≠ b ∧ (L a = v ∨ H a = v) ∧ (L b = v ∨ H b = v) ∧
      ((∀ d, L d ≠ v) ∨ ((∀ d, H d ≠ v) ∧
      ((∀ c, ¬(L c = min (H a) (H b) ∧ H c = max (H a) (H b))) ∨ ∃ d, L d = max (H a) (H b)))))
    (a b c : Fin n) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (h1 : (H a = L b ∨ ∃ v, sel v = some (a,b)) ∨ (H b = L a ∨ ∃ v, sel v = some (b,a)))
    (h2 : (H a = L c ∨ ∃ v, sel v = some (a,c)) ∨ (H c = L a ∨ ∃ v, sel v = some (c,a)))
    (h3 : (H b = L c ∨ ∃ v, sel v = some (b,c)) ∨ (H c = L b ∨ ∃ v, sel v = some (c,b))) : False := by
  by_cases ht1 : H a = L b ∨ H b = L a
  · rcases ht1 with h|h
    · exact aux_line_through_no_triangle L H hlt hinj sel hsel a b c hab hac hbc h h2 h3
    · exact aux_line_through_no_triangle L H hlt hinj sel hsel b a c hab.symm hbc hac h h3 h2
  by_cases ht2 : H a = L c ∨ H c = L a
  · rcases ht2 with h|h
    · exact aux_line_through_no_triangle L H hlt hinj sel hsel a c b hac hab hbc.symm h h1 h3.symm
    · exact aux_line_through_no_triangle L H hlt hinj sel hsel c a b hac.symm hbc.symm hab h h3.symm h1
  by_cases ht3 : H b = L c ∨ H c = L b
  · rcases ht3 with h|h
    · exact aux_line_through_no_triangle L H hlt hinj sel hsel b c a hbc hab.symm hac.symm h h1.symm h2.symm
    · exact aux_line_through_no_triangle L H hlt hinj sel hsel c b a hbc.symm hac.symm hab.symm h h2.symm h1.symm
  have weak : ∀ v a b, sel v = some (a,b) → (L a = v ∧ L b = v) ∨ (H a = v ∧ H b = v) := by
    intro v a b h
    obtain ⟨_, ha, hb, hg⟩ := hsel v a b h
    rcases hg with hg|⟨hg,_⟩
    · exact Or.inr ⟨ha.resolve_left (hg a), hb.resolve_left (hg b)⟩
    · exact Or.inl ⟨ha.resolve_right (hg a), hb.resolve_right (hg b)⟩
  have extract : ∀ (P Q R S : Prop), ¬ (P ∨ R) → (P ∨ Q) ∨ (R ∨ S) → Q ∨ S := by
    intros P Q R S hn hh
    rcases hh with (h|h)|(h|h)
    · exact False.elim (hn (Or.inl h))
    · exact Or.inl h
    · exact False.elim (hn (Or.inr h))
    · exact Or.inr h
  have s1 := extract _ _ _ _ ht1 h1
  have s2 := extract _ _ _ _ ht2 h2
  have s3 := extract _ _ _ _ ht3 h3
  clear h1 h2 h3 ht1 ht2 ht3 hsel hinj extract
  rcases s1 with ⟨v1,e1⟩|⟨v1,e1⟩ <;>
    rcases s2 with ⟨v2,e2⟩|⟨v2,e2⟩ <;>
    rcases s3 with ⟨v3,e3⟩|⟨v3,e3⟩ <;>
    have g1 := weak _ _ _ e1 <;> have g2 := weak _ _ _ e2 <;>
    have g3 := weak _ _ _ e3 <;> clear weak
  all_goals
    have q12 : v1 ≠ v2 := by rintro rfl; rw [e1] at e2; cases e2 <;> simp_all
    have q13 : v1 ≠ v3 := by rintro rfl; rw [e1] at e3; cases e3 <;> simp_all
    have q23 : v2 ≠ v3 := by rintro rfl; rw [e2] at e3; cases e3 <;> simp_all
    clear e1 e2 e3 sel
    rcases g1 with ⟨h,h'⟩|⟨h,h'⟩ <;> rcases g2 with ⟨j,j'⟩|⟨j,j'⟩ <;> rcases g3 with ⟨k,k'⟩|⟨k,k'⟩ <;> omega

-- [item 287] Ordered triple min-max overlap needed for source repair
theorem aux_three_min_max_overlap (x y z : ℕ) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    max x y = min x z ∨ max x y = min y z ∨
    max x z = min x y ∨ max x z = min y z ∨
    max y z = min x y ∨ max y z = min x z := by omega

-- [item 294] Every finite simple line graph satisfies Erdős 151 (edge-intersection encoding)
theorem aux_line_graph_intersection_bound {n m : ℕ} (G : SimpleGraph (Fin n)) (φ : Fin n → Fin m × Fin m)
    (hφ : ∀ a, (φ a).1 < (φ a).2) (hinj : Function.Injective φ)
    (hadj : ∀ a b, G.Adj a b ↔ a ≠ b ∧
      (({(φ a).1,(φ a).2} : Finset (Fin m)) ∩ {(φ b).1,(φ b).2}).Nonempty) :
    cliqueTransversalNumber G ≤ n - H n := by
  classical
  let Good := fun (L H : Fin n → ℕ) (v : ℕ) (a b : Fin n) =>
    a ≠ b ∧ (L a = v ∨ H a = v) ∧ (L b = v ∨ H b = v) ∧
    ((∀ d, L d ≠ v) ∨ ((∀ d, H d ≠ v) ∧
      ((∀ c, ¬(L c = min (H a) (H b) ∧ H c = max (H a) (H b))) ∨ ∃ d, L d = max (H a) (H b))))
  obtain ⟨hEinj, hint⟩ := aux_ordered_edge_encoding φ hφ hinj
  let L : Fin n → ℕ := fun a => ((φ a).1 : ℕ)
  let Hh : Fin n → ℕ := fun a => ((φ a).2 : ℕ)
  have hlt : ∀ a, L a < Hh a := fun a => hφ a
  have hLH : ∀ a b, L a = L b → Hh a = Hh b → a = b := by
    intro a b h1 h2; apply hinj; exact Prod.ext (Fin.ext h1) (Fin.ext h2)
  have hadjN : ∀ a b, G.Adj a b ↔ a ≠ b ∧
      (L a = L b ∨ L a = Hh b ∨ Hh a = L b ∨ Hh a = Hh b) := by
    intro a b; rw [hadj, hint]; simp only [L, Hh, Fin.ext_iff]
  have hmem : ∀ (v : Fin m) a, v ∈ ({(φ a).1,(φ a).2} : Finset (Fin m)) ↔
      (L a = v.val ∨ Hh a = v.val) := by
    intro v a; simp only [Finset.mem_insert, Finset.mem_singleton, L, Hh, Fin.ext_iff]; tauto
  let sel : ℕ → Option (Fin n × Fin n) := fun v =>
    if h : ∃ p : Fin n × Fin n, Good L Hh v p.1 p.2 then some h.choose else none
  have hsel : ∀ v a b, sel v = some (a,b) → Good L Hh v a b := by
    intro v a b h
    simp only [sel] at h
    split at h
    · rename_i hh; have := hh.choose_spec; rw [Option.some.inj h] at this; exact this
    · cases h
  have hselex : ∀ v a b, Good L Hh v a b → ∃ p q, sel v = some (p,q) ∧ Good L Hh v p q := by
    intro v a b hg
    have hh : ∃ p : Fin n × Fin n, Good L Hh v p.1 p.2 := ⟨(a,b), hg⟩
    refine ⟨hh.choose.1, hh.choose.2, ?_, hh.choose_spec⟩
    simp only [sel, dif_pos hh]
  let R : SimpleGraph (Fin n) :=
    SimpleGraph.fromRel (fun a b => Hh a = L b ∨ ∃ v, sel v = some (a,b))
  have hRadj : ∀ a b, a ≠ b → (Hh a = L b ∨ ∃ v, sel v = some (a,b)) → R.Adj a b := by
    intro a b hab h; exact (SimpleGraph.fromRel_adj _ a b).mpr ⟨hab, Or.inl h⟩
  apply aux_line_local_certificate_bound G R (fun a => ({(φ a).1,(φ a).2} : Finset (Fin m)))
    (fun a => Finset.card_pair (ne_of_lt (hφ a))) hEinj hadj
  · intro s hs
    obtain ⟨a,b,c,hab,hac,hbc,rfl⟩ := Finset.card_eq_three.mp hs.card_eq
    have h1 := hs.isClique (by simp : a ∈ ({a,b,c} : Finset (Fin n))) (by simp : b ∈ ({a,b,c} : Finset (Fin n))) hab
    have h2 := hs.isClique (by simp : a ∈ ({a,b,c} : Finset (Fin n))) (by simp : c ∈ ({a,b,c} : Finset (Fin n))) hac
    have h3 := hs.isClique (by simp : b ∈ ({a,b,c} : Finset (Fin n))) (by simp : c ∈ ({a,b,c} : Finset (Fin n))) hbc
    rw [SimpleGraph.fromRel_adj] at h1 h2 h3
    exact aux_line_selected_no_triangle L Hh hlt hLH sel hsel a b c hab hac hbc h1.2 h2.2 h3.2
  · intro v s hs hsv
    have hin : ∀ a, a ∈ s ↔ (L a = v.val ∨ Hh a = v.val) := by
      intro a; rw [hsv]; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hmem v a
    obtain ⟨a,ha,b,hb,hab⟩ := Finset.one_lt_card.mp (by have := hs.2; omega : 1 < s.card)
    have viaGood : (∃ a b, Good L Hh v.val a b) → ∃ a ∈ s, ∃ b ∈ s, R.Adj a b := by
      rintro ⟨a',b',hg⟩
      obtain ⟨p,q,hpq,hg⟩ := hselex _ a' b' hg
      exact ⟨p, (hin p).mpr hg.2.1, q, (hin q).mpr hg.2.2.1, hRadj p q hg.1 (Or.inr ⟨_, hpq⟩)⟩
    by_cases c1 : ∃ d, L d = v.val
    · by_cases c2 : ∃ d, Hh d = v.val
      · obtain ⟨d,hd⟩ := c1; obtain ⟨e,he⟩ := c2
        have hde : e ≠ d := by intro h; subst h; have := hlt e; omega
        exact ⟨e, (hin e).mpr (Or.inr he), d, (hin d).mpr (Or.inl hd), hRadj e d hde (Or.inl (by omega))⟩
      · push Not at c2
        apply viaGood
        by_contra hng
        push Not at hng
        have hLa : L a = v.val := ((hin a).mp ha).resolve_right (c2 a)
        have hLb : L b = v.val := ((hin b).mp hb).resolve_right (c2 b)
        have ng := hng a b
        simp only [Good, not_and, not_or, not_forall, not_exists] at ng
        have gg := (ng hab (Or.inl hLa) (Or.inl hLb)).2 c2
        simp only [not_not] at gg
        obtain ⟨⟨c, hc1, hc2⟩, hsink⟩ := gg
        have hHab : Hh a ≠ Hh b := fun h => hab (hLH a b (by omega) h)
        have la := hlt a; have lb := hlt b
        by_cases h3 : ∃ e ∈ s, e ≠ a ∧ e ≠ b
        · obtain ⟨e,he,hea,heb⟩ := h3
          have hLe : L e = v.val := ((hin e).mp he).resolve_right (c2 e)
          have le := hlt e
          have hHae : Hh a ≠ Hh e := fun h => hea (hLH e a (by omega) h.symm)
          have hHbe : Hh b ≠ Hh e := fun h => heb (hLH e b (by omega) h.symm)
          have ng2 := hng a e
          simp only [Good, not_and, not_or, not_forall, not_exists] at ng2
          have gg := (ng2 (Ne.symm hea) (Or.inl hLa) (Or.inl hLe)).2 c2
          simp only [not_not] at gg
          obtain ⟨⟨c', hc1', hc2'⟩, hsink'⟩ := gg
          have ng3 := hng b e
          simp only [Good, not_and, not_or, not_forall, not_exists] at ng3
          have gg := (ng3 (Ne.symm heb) (Or.inl hLb) (Or.inl hLe)).2 c2
          simp only [not_not] at gg
          obtain ⟨⟨c'', hc1'', hc2''⟩, hsink''⟩ := gg
          rcases aux_three_min_max_overlap (Hh a) (Hh b) (Hh e) hHab hHae hHbe with h|h|h|h|h|h
          · exact hsink c' (hc1'.trans h.symm)
          · exact hsink c'' (hc1''.trans h.symm)
          · exact hsink' c (hc1.trans h.symm)
          · exact hsink' c'' (hc1''.trans h.symm)
          · exact hsink'' c (hc1.trans h.symm)
          · exact hsink'' c' (hc1'.trans h.symm)
        · push Not at h3
          have hcs : c ∉ s := by
            intro h; rcases (hin c).mp h with h|h <;> omega
          have hins : G.IsClique ((insert c s : Finset (Fin n)) : Set (Fin n)) := by
            rw [Finset.coe_insert]
            apply hs.1.1.insert
            intro x hx hcx
            have hx' : x = a ∨ x = b := by
              by_contra hh; push Not at hh; exact hh.2 (h3 x hx hh.1)
            rw [hadjN]; refine ⟨hcx, ?_⟩
            rcases hx' with rfl|rfl <;> omega
          exact absurd (hs.1.2 hins (Finset.subset_insert c s) (Finset.mem_insert_self c s)) hcs
    · push Not at c1
      apply viaGood
      exact ⟨a, b, hab, (hin a).mp ha, (hin b).mp hb, Or.inl c1⟩
  · intro t s ht him
    obtain ⟨x,y,z,hxy,hxz,hyz,rfl⟩ := Finset.card_eq_three.mp ht
    have get : ∀ u w : Fin m, u ≠ w → u ∈ ({x,y,z} : Finset (Fin m)) →
        w ∈ ({x,y,z} : Finset (Fin m)) → ∃ a ∈ s,
        (L a = u.val ∧ Hh a = w.val) ∨ (L a = w.val ∧ Hh a = u.val) := by
      intro u w huw hu hw
      have : ({u,w} : Finset (Fin m)) ∈ s.image (fun a => ({(φ a).1,(φ a).2} : Finset (Fin m))) := by
        rw [him, Finset.mem_powersetCard]
        refine ⟨?_, Finset.card_pair huw⟩
        intro q hq; simp at hq; rcases hq with rfl|rfl <;> assumption
      obtain ⟨a,ha,he⟩ := Finset.mem_image.mp this
      exact ⟨a, ha, aux_line_pair_eq _ _ u w (hφ a) huw he⟩
    obtain ⟨a,ha,hA⟩ := get x y hxy (by simp) (by simp)
    obtain ⟨b,hb,hB⟩ := get x z hxz (by simp) (by simp)
    obtain ⟨c,hc,hC⟩ := get y z hyz (by simp) (by simp)
    have vxy : x.val ≠ y.val := fun h => hxy (Fin.ext h)
    have vxz : x.val ≠ z.val := fun h => hxz (Fin.ext h)
    have vyz : y.val ≠ z.val := fun h => hyz (Fin.ext h)
    have la := hlt a; have lb := hlt b; have lc := hlt c
    have hab : a ≠ b := by rintro rfl; omega
    have hac : a ≠ c := by rintro rfl; omega
    have hbc : b ≠ c := by rintro rfl; omega
    have key : (Hh a = L b ∨ Hh b = L a) ∨ (Hh a = L c ∨ Hh c = L a) ∨
        (Hh b = L c ∨ Hh c = L b) := by omega
    rcases key with (h|h)|(h|h)|(h|h)
    · exact ⟨a,ha,b,hb,hRadj a b hab (Or.inl h)⟩
    · exact ⟨b,hb,a,ha,hRadj b a (Ne.symm hab) (Or.inl h)⟩
    · exact ⟨a,ha,c,hc,hRadj a c hac (Or.inl h)⟩
    · exact ⟨c,hc,a,ha,hRadj c a (Ne.symm hac) (Or.inl h)⟩
    · exact ⟨b,hb,c,hc,hRadj b c hbc (Or.inl h)⟩
    · exact ⟨c,hc,b,hb,hRadj c b (Ne.symm hbc) (Or.inl h)⟩

-- [item 295] Erdős 151 for every line graph with an injective ordered endpoint encoding
theorem aux_line_graph_bound {n m : ℕ} (G : SimpleGraph (Fin n))
    (φ : Fin n → Fin m × Fin m)
    (hφ : ∀ a, (φ a).1 < (φ a).2) (hinj : Function.Injective φ)
    (hadj : ∀ a b, G.Adj a b ↔ a ≠ b ∧
      ((φ a).1 = (φ b).1 ∨ (φ a).1 = (φ b).2 ∨
       (φ a).2 = (φ b).1 ∨ (φ a).2 = (φ b).2)) :
    cliqueTransversalNumber G ≤ n - H n := by
  apply aux_line_graph_intersection_bound G φ hφ hinj
  intro a b
  rw [hadj, (aux_ordered_edge_encoding φ hφ hinj).2 a b]

-- [item 303] Erdős 151 holds for complements of triangle-free graphs (independence number ≤ 2)
theorem aux_compl_triangle_free_bound {n : ℕ} (G : SimpleGraph (Fin n)) (hT : Gᶜ.CliqueFree 3) :
    cliqueTransversalNumber G ≤ n - H n := by
  classical
  obtain ⟨I, hI⟩ := aux_H_mem n Gᶜ hT
  have hin : ∀ a ∈ I, ∀ b ∈ I, a ≠ b → G.Adj a b := by
    intro a ha b hb hab
    by_contra h
    exact hI.isIndepSet ha hb hab ⟨hab, h⟩
  by_cases hc : ∃ v ∈ I, ∃ w ∉ I, ¬ Gᶜ.Adj v w
  · rw [← hI.card_eq]
    obtain ⟨v, hv, w, hw, hvw⟩ := hc
    have hne : v ≠ w := fun h => hw (h ▸ hv)
    have hGvw : G.Adj v w := by
      by_contra h; exact hvw ⟨hne, h⟩
    have hsub : insert w (I.erase v) ⊆ G.neighborFinset v := by
      intro x hx
      rw [SimpleGraph.mem_neighborFinset]
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hGvw
      · obtain ⟨hxv, hxI⟩ := Finset.mem_erase.mp hx
        exact hin v hv x hxI (Ne.symm hxv)
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem (fun h => hw (Finset.mem_of_mem_erase h)),
      Finset.card_erase_of_mem hv] at hcard
    have hpos : 0 < I.card := Finset.card_pos.mpr ⟨v, hv⟩
    exact (aux_tau_le_neighbor G v).trans (by omega)
  · push Not at hc
    rcases I.eq_empty_or_nonempty with hE | ⟨v0, hv0⟩
    · rw [← hI.card_eq]
      subst hE
      have := aux_tau_le_of_free G ∅ (by
        intro s hs hsub
        have h1 := Finset.card_le_card hsub
        have h2 := hs.2
        rw [Finset.card_empty] at h1
        omega)
      simpa using this
    have hpart : ∀ a b, G.Adj a b → (a ∈ I ↔ b ∈ I) := by
      intro a b hab
      constructor
      · intro ha; by_contra hb; exact (hc a ha b hb).2 hab
      · intro hb; by_contra ha; exact (hc b hb a ha).2 hab.symm
    apply aux_perfect_elimination_bound G
    intro a b c _ _ hab hac hbc
    by_cases ha : a ∈ I
    · exact hin b ((hpart a b hab).mp ha) c ((hpart a c hac).mp ha) hbc
    · have hb : b ∉ I := fun h => ha ((hpart a b hab).mpr h)
      have hcI : c ∉ I := fun h => ha ((hpart a c hac).mpr h)
      by_contra hn
      have h1 := hc v0 hv0 b hb
      have h2 := hc v0 hv0 c hcI
      apply hT {v0, b, c}
      rw [SimpleGraph.is3Clique_triple_iff]
      exact ⟨h1, h2, ⟨hbc, hn⟩⟩

-- [item 324] Consecutive-pair maximal clique condition on a cyclic vertex ordering implies Erdős 151
theorem aux_circular_consecutive_bound {n : ℕ} (hn : 4 ≤ n) (G : SimpleGraph (Fin n))
    (hcov : ∀ s, IsBigMaximalClique G s → ∃ a ∈ s, ∃ b ∈ s,
      a.val + 1 = b.val ∨ (a.val + 1 = n ∧ b.val = 0)) :
    cliqueTransversalNumber G ≤ n - H n := by
  let R := SimpleGraph.fromRel (fun a b : Fin n => a.val + 1 = b.val ∨ (a.val + 1 = n ∧ b.val = 0))
  apply aux_reduction G R
  · intro s hs
    obtain ⟨a,b,c,hab,hac,hbc,rfl⟩ := Finset.card_eq_three.mp hs.card_eq
    have h1 := hs.isClique (by simp : a ∈ ({a,b,c} : Finset (Fin n))) (by simp : b ∈ ({a,b,c} : Finset (Fin n))) hab
    have h2 := hs.isClique (by simp : a ∈ ({a,b,c} : Finset (Fin n))) (by simp : c ∈ ({a,b,c} : Finset (Fin n))) hac
    have h3 := hs.isClique (by simp : b ∈ ({a,b,c} : Finset (Fin n))) (by simp : c ∈ ({a,b,c} : Finset (Fin n))) hbc
    simp only [R, SimpleGraph.fromRel_adj] at h1 h2 h3
    have ha := a.isLt; have hb := b.isLt; have hc := c.isLt
    have hab' : a.val ≠ b.val := fun h => hab (Fin.ext h)
    have hac' : a.val ≠ c.val := fun h => hac (Fin.ext h)
    have hbc' : b.val ≠ c.val := fun h => hbc (Fin.ext h)
    omega
  · intro s hs
    obtain ⟨a,ha,b,hb,hab⟩ := hcov s hs
    refine ⟨a,ha,b,hb,?_⟩
    apply (SimpleGraph.fromRel_adj _ a b).mpr
    refine ⟨?_,Or.inl hab⟩
    intro he; subst b
    have := a.isLt
    omega

-- [item 325] Exact free-set criterion for K4-free graphs: triangle-free induced set with no globally naked edge
theorem aux_K4_free_set_criterion {n : ℕ} (G : SimpleGraph (Fin n))
    (hG : G.CliqueFree 4) (U : Finset (Fin n)) :
    (∀ s, IsBigMaximalClique G s → ¬ s ⊆ U) ↔
    (∀ a ∈ U, ∀ b ∈ U, ∀ c ∈ U, G.Adj a b → G.Adj a c → ¬ G.Adj b c) ∧
    (∀ a ∈ U, ∀ b ∈ U, G.Adj a b → ∃ c, G.Adj a c ∧ G.Adj b c) := by
  classical
  constructor
  · intro hf
    constructor
    · intro a ha b hb c hc hab hac hbc
      have hcl : G.IsClique (({a,b,c} : Finset (Fin n)) : Set (Fin n)) :=
        (SimpleGraph.is3Clique_triple_iff.mpr ⟨hab,hac,hbc⟩).isClique
      have hmax : IsBigMaximalClique G {a,b,c} := by
        refine ⟨⟨hcl, ?_⟩, by simp [hab.ne,hac.ne,hbc.ne]⟩
        intro t ht hsub x hx
        by_contra hn
        have h4 : G.IsNClique 4 {x,a,b,c} := by
          refine ⟨?_, ?_⟩
          · intro y hy z hz hyz
            apply ht _ _ hyz <;> simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at * <;> aesop
          · simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hn
            simp [hn.1,hn.2.1,hn.2.2,hab.ne,hac.ne,hbc.ne]
        exact hG _ h4
      exact hf _ hmax (by simp [Finset.insert_subset_iff,ha,hb,hc])
    · intro a ha b hb hab
      by_contra hn
      push Not at hn
      apply hf {a,b} ?_ (by simp [Finset.insert_subset_iff,ha,hb])
      refine ⟨⟨?_, ?_⟩, by simp [hab.ne]⟩
      · intro x hx y hy hxy
        simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hx hy
        rcases hx with rfl|rfl <;> rcases hy with rfl|rfl <;> simp_all [hab.symm]
      · intro t ht hsub x hx
        by_cases hxa : x = a
        · simp [hxa]
        by_cases hxb : x = b
        · simp [hxb]
        exact False.elim (hn x (ht (hsub (by simp)) hx (Ne.symm hxa))
          (ht (hsub (by simp)) hx (Ne.symm hxb)))
  · rintro ⟨htri,hedge⟩ s hs hsub
    obtain ⟨a,ha,b,hb,hab⟩ := Finset.one_lt_card.mp hs.2
    have hadj := hs.1.1 ha hb hab
    obtain ⟨c,hac,hbc⟩ := hedge a (hsub ha) b (hsub hb) hadj
    have hsmall : s ⊆ {a,b} := by
      intro x hx
      by_cases hxa : x = a
      · simp [hxa]
      by_cases hxb : x = b
      · simp [hxb]
      exact False.elim (htri a (hsub ha) b (hsub hb) x (hsub hx) hadj
        (hs.1.1 ha hx (Ne.symm hxa)) (hs.1.1 hb hx (Ne.symm hxb)))
    have hins : G.IsClique ((insert c s : Finset (Fin n)) : Set (Fin n)) := by
      rw [Finset.coe_insert]
      apply hs.1.1.insert
      intro x hx _
      have hx' := hsmall hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx'
      rcases hx' with rfl|rfl
      · exact hac.symm
      · exact hbc.symm
    have hc := hs.1.2 hins (Finset.subset_insert c s) (Finset.mem_insert_self c s)
    exact htri a (hsub ha) b (hsub hb) c (hsub hc) hadj hac hbc

-- [item 326] Erdős 151 when all big maximal cliques are cyclic intervals in a fixed vertex ordering
theorem aux_circular_arc_maximal_cliques_bound {n : ℕ} (hn : 4 ≤ n) (G : SimpleGraph (Fin n))
    (harc : ∀ s, IsBigMaximalClique G s → ∃ (a : Fin n) (k : ℕ),
      s = (Finset.range k).image (fun i => (⟨(a.val+i)%n, Nat.mod_lt _ (by omega)⟩ : Fin n))) :
    cliqueTransversalNumber G ≤ n - H n := by
  apply aux_circular_consecutive_bound hn G
  intro s hs
  obtain ⟨a,k,hk⟩ := harc s hs
  have hcard : 2 ≤ k := by
    have := hs.2
    have hh : s.card ≤ k := by rw [hk]; exact Finset.card_image_le.trans (by simp)
    omega
  let b : Fin n := ⟨(a.val+1)%n,Nat.mod_lt _ (by omega)⟩
  refine ⟨a,?_,b,?_,?_⟩
  · rw [hk]; exact Finset.mem_image.mpr ⟨0,by simp; omega, by simp [Nat.mod_eq_of_lt a.isLt]⟩
  · rw [hk]; exact Finset.mem_image.mpr ⟨1,by simp; omega,rfl⟩
  · dsimp [b]
    have ha := a.isLt
    by_cases h : a.val+1 < n
    · left; rw [Nat.mod_eq_of_lt h]
    · right; have he : a.val+1=n := by omega
      simp [he]

-- [item 327] Neighborhood plus an independent set with no cross edges improves the degree bound by its cardinality
theorem aux_neighborhood_independent_extension {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (v : Fin n) (I : Finset (Fin n))
    (hI : G.IsIndepSet (I : Set (Fin n)))
    (hdis : ∀ i ∈ I, ¬ G.Adj v i)
    (hcross : ∀ i ∈ I, ∀ x, G.Adj v x → ¬ G.Adj i x) :
    cliqueTransversalNumber G ≤ n - ((G.neighborFinset v).card + I.card) := by
  classical
  have hd : Disjoint (G.neighborFinset v) I := by
    rw [Finset.disjoint_left]
    intro i hi hiI
    exact hdis i hiI ((G.mem_neighborFinset v i).mp hi)
  rw [← Finset.card_union_of_disjoint hd]
  apply aux_tau_le_of_free G
  intro s hs hsub
  have hsN : s ⊆ G.neighborFinset v := by
    intro i hi
    rcases Finset.mem_union.mp (hsub hi) with hiN|hiI
    · exact hiN
    · have hrem : (s.erase i).Nonempty := by
        apply Finset.card_pos.mp
        rw [Finset.card_erase_of_mem hi]
        have := hs.2
        omega
      obtain ⟨x,hx⟩ := hrem
      obtain ⟨hxi,hxs⟩ := Finset.mem_erase.mp hx
      have hix := hs.1.1 hi hxs (Ne.symm hxi)
      rcases Finset.mem_union.mp (hsub hxs) with hxN|hxI
      · exact False.elim (hcross i hiI x ((G.mem_neighborFinset v x).mp hxN) hix)
      · exact False.elim (hI hiI hxI (Ne.symm hxi) hix)
  have hins : G.IsClique ((insert v s : Finset (Fin n)) : Set (Fin n)) := by
    rw [Finset.coe_insert]
    apply hs.1.1.insert
    intro x hx _
    exact (G.mem_neighborFinset v x).mp (hsN hx)
  have hv := hs.1.2 hins (Finset.subset_insert v s) (Finset.mem_insert_self v s)
  exact G.irrefl ((G.mem_neighborFinset v v).mp (hsN hv))

-- [item 343] The undirected cover relation of a strict partial order has no triangles
theorem aux_comparability_cover_triangle {α : Type*} (lt : α → α → Prop)
    (hirr : ∀ a, ¬ lt a a)
    (htrans : ∀ a b c, lt a b → lt b c → lt a c)
    (a b c : α)
    (h1 : (lt a b ∧ ¬ ∃ x, lt a x ∧ lt x b) ∨ (lt b a ∧ ¬ ∃ x, lt b x ∧ lt x a))
    (h2 : (lt a c ∧ ¬ ∃ x, lt a x ∧ lt x c) ∨ (lt c a ∧ ¬ ∃ x, lt c x ∧ lt x a))
    (h3 : (lt b c ∧ ¬ ∃ x, lt b x ∧ lt x c) ∨ (lt c b ∧ ¬ ∃ x, lt c x ∧ lt x b)) : False := by
  rcases h1 with h1|h1 <;> rcases h2 with h2|h2 <;> rcases h3 with h3|h3 <;> grind

-- [item 344] Locally constant dominating-center labels certify a free set and a clique-transversal bound
theorem aux_component_center_free_bound {n : ℕ} (G : SimpleGraph (Fin n))
    (U : Finset (Fin n)) (center : Fin n → Fin n)
    (hcenter : ∀ a ∈ U, ∀ b ∈ U, G.Adj a b → center a = center b)
    (hdom : ∀ a ∈ U, ∀ b ∈ U, G.Adj a b → G.Adj (center a) a) :
    cliqueTransversalNumber G ≤ n - U.card := by
  apply aux_tau_le_of_free G U
  intro s hs hsub
  obtain ⟨a,ha,b,hb,hab⟩ := Finset.one_lt_card.mp hs.2
  have hadj := hs.1.1 ha hb hab
  have hca : G.Adj (center a) a := hdom a (hsub ha) b (hsub hb) hadj
  have hins : G.IsClique ((insert (center a) s : Finset (Fin n)) : Set (Fin n)) := by
    rw [Finset.coe_insert]
    apply hs.1.1.insert
    intro x hx _
    by_cases hxa : x = a
    · simpa [hxa] using hca
    · have hax := hs.1.1 ha hx (Ne.symm hxa)
      rw [hcenter a (hsub ha) x (hsub hx) hax]
      exact hdom x (hsub hx) a (hsub ha) hax.symm
  have hc := hs.1.2 hins (Finset.subset_insert _ _) (Finset.mem_insert_self _ _)
  by_cases he : center a = a
  · exact G.irrefl (he ▸ hca)
  · have had := hs.1.1 ha hc (Ne.symm he)
    have heq := hcenter a (hsub ha) (center a) (hsub hc) had
    have hh := hdom (center a) (hsub hc) a (hsub ha) had.symm
    rw [← heq] at hh
    exact G.irrefl hh

-- [item 345] Every comparability graph satisfies the Erdős 151 bound via its triangle-free cover graph
theorem aux_comparability_bound {n : ℕ} (G : SimpleGraph (Fin n)) (lt : Fin n → Fin n → Prop)
    (hirr : ∀ a, ¬ lt a a)
    (htrans : ∀ a b c, lt a b → lt b c → lt a c)
    (hadj : ∀ a b, G.Adj a b ↔ lt a b ∨ lt b a) :
    cliqueTransversalNumber G ≤ n - H n := by
  classical
  letI : IsTrans (Fin n) lt := ⟨htrans⟩
  letI : Std.Irrefl lt := ⟨hirr⟩
  have wf := Finite.wellFounded_of_trans_of_irrefl lt
  let cov := fun a b => lt a b ∧ ¬ ∃ c, lt a c ∧ lt c b
  let R : SimpleGraph (Fin n) := {
    Adj := fun a b => cov a b ∨ cov b a
    symm := ⟨fun _ _ h => h.symm⟩
    loopless := ⟨by intro a h; rcases h with h|h <;> exact hirr a h.1⟩ }
  apply aux_reduction G R
  · intro s hs
    obtain ⟨a,b,c,hab,hac,hbc,rfl⟩ := Finset.card_eq_three.mp hs.card_eq
    exact aux_comparability_cover_triangle lt hirr htrans a b c
      (hs.isClique (by simp) (by simp) hab)
      (hs.isClique (by simp) (by simp) hac)
      (hs.isClique (by simp) (by simp) hbc)
  · intro s hs
    have hne : (s : Set (Fin n)).Nonempty := by
      exact Finset.card_pos.mp (by have := hs.2; omega)
    obtain ⟨a,ha,hmina⟩ := wf.has_min (s : Set (Fin n)) hne
    have hrem : ((s.erase a : Finset (Fin n)) : Set (Fin n)).Nonempty := by
      apply Finset.card_pos.mp
      rw [Finset.card_erase_of_mem ha]
      have := hs.2
      omega
    obtain ⟨b,hb,hminb⟩ := wf.has_min ((s.erase a : Finset (Fin n)) : Set (Fin n)) hrem
    obtain ⟨hba,hbs⟩ := Finset.mem_erase.mp hb
    have hab : lt a b := ((hadj a b).mp (hs.1.1 ha hbs hba.symm)).resolve_right (hmina b hbs)
    refine ⟨a,ha,b,hbs,Or.inl ⟨hab,?_⟩⟩
    rintro ⟨c,hac,hcb⟩
    have hca : c ≠ a := by rintro rfl; exact hirr _ hac
    have hins : G.IsClique ((insert c s : Finset (Fin n)) : Set (Fin n)) := by
      rw [Finset.coe_insert]
      apply hs.1.1.insert
      intro x hx hcx
      apply (hadj c x).mpr
      by_cases hxa : x = a
      · subst x; exact Or.inr hac
      by_cases hxb : x = b
      · subst x; exact Or.inl hcb
      have hbx : lt b x := ((hadj b x).mp (hs.1.1 hbs hx (Ne.symm hxb))).resolve_right
        (hminb x (Finset.mem_erase.mpr ⟨hxa,hx⟩))
      exact Or.inl (htrans c b x hcb hbx)
    have hcs : c ∈ s := hs.1.2 hins (Finset.subset_insert _ _) (Finset.mem_insert_self _ _)
    exact hminb c (Finset.mem_erase.mpr ⟨hca,hcs⟩) hcb

-- [item 362] The four edges of K2,2 cannot all be ranked parent edges
theorem aux_C4_no_ranked_parent (r : Fin 4 → ℕ) (p : Fin 4 → Fin 4)
    (h : ∀ a b : Fin 4, a.val / 2 ≠ b.val / 2 →
      (r a < r b ∧ p a = b) ∨ (r b < r a ∧ p b = a)) : False := by
  have h02 := h 0 2 (by decide)
  have h03 := h 0 3 (by decide)
  have h12 := h 1 2 (by decide)
  have h13 := h 1 3 (by decide)
  clear h
  rcases h02 with ⟨a,b⟩|⟨a,b⟩ <;>
    rcases h03 with ⟨c,d⟩|⟨c,d⟩ <;>
    rcases h12 with ⟨e,f⟩|⟨e,f⟩ <;>
    rcases h13 with ⟨g,i⟩|⟨g,i⟩ <;> (try simp_all) <;> omega

-- [item 380] Finite free-set certificate for the eight-vertex SED-strong obstruction's maximal-clique family
theorem aux_sed_strong_obstruction_free_sets :
    let C : Finset (Finset (Fin 8)) :=
      {{0,1,4},{0,5},{1,2,3},{1,3,4},{2,6},{3,4,7},{5,7},{6,7}}
    (∀ U : Finset (Fin 8), (∀ s ∈ C, ¬ s ⊆ U) → U.card ≤ 4) ∧
    (∀ s ∈ C, ¬ s ⊆ ({0,2,3,4} : Finset (Fin 8))) ∧
    (∀ s ∈ C.erase {1,3,4}, ¬ s ⊆ ({1,3,4,5,6} : Finset (Fin 8))) := by
  decide +kernel

-- [item 385] Peeling generalization of Case C: if every triangle subfamily has codegree ≤2 or a triangle with a private edge, a nonmonochromatic triangle-edge colo
theorem aux_peel_triangle_coloring {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hpeel : ∀ S ⊆ G.cliqueFinset 3,
      (∀ e : Finset (Fin n), (S.filter (fun t => e ∈ t.powersetCard 2)).card ≤ 2) ∨
      ∃ t ∈ S, ∃ e ∈ t.powersetCard 2, ∀ t' ∈ S, e ∈ t'.powersetCard 2 → t' = t) :
    ∃ c : Finset (Fin n) → Bool, ∀ t ∈ G.cliqueFinset 3,
      ∃ e ∈ t.powersetCard 2, ∃ f ∈ t.powersetCard 2, c e ≠ c f := by
  classical
  suffices key : ∀ S, S ⊆ G.cliqueFinset 3 → ∃ c : Finset (Fin n) → Bool, ∀ t ∈ S,
      ∃ e ∈ t.powersetCard 2, ∃ f ∈ t.powersetCard 2, c e ≠ c f from key _ subset_rfl
  intro S
  induction S using Finset.strongInduction with
  | H S ih =>
    intro hS
    rcases hpeel S hS with hd | ⟨t, ht, e, he, hpriv⟩
    · have hs : ∀ x ∈ S.image (Finset.powersetCard 2), x.card = 3 := by
        intro x hx
        obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hx
        rw [Finset.card_powersetCard, (SimpleGraph.mem_cliqueFinset_iff.mp (hS ht)).card_eq]
        decide
      have hdd : ∀ e, ((S.image (Finset.powersetCard 2)).filter (e ∈ ·)).card ≤ 2 := by
        intro e
        rw [Finset.filter_image]
        exact Finset.card_image_le.trans (hd e)
      obtain ⟨c, hc⟩ := aux_degree_two_hypergraph_coloring _ hs hdd
      exact ⟨c, fun t ht => hc _ (Finset.mem_image.mpr ⟨t, ht, rfl⟩)⟩
    · obtain ⟨c, hc⟩ := ih (S.erase t) (Finset.erase_ssubset ht)
        ((Finset.erase_subset _ _).trans hS)
      have hne : ((t.powersetCard 2).erase e).Nonempty := by
        apply Finset.card_pos.mp
        rw [Finset.card_erase_of_mem he, Finset.card_powersetCard,
          (SimpleGraph.mem_cliqueFinset_iff.mp (hS ht)).card_eq]
        decide
      obtain ⟨f, hf⟩ := hne
      obtain ⟨hfe, hf⟩ := Finset.mem_erase.mp hf
      refine ⟨Function.update c e (!c f), ?_⟩
      intro t' ht'
      by_cases htt : t' = t
      · subst htt
        refine ⟨e, he, f, hf, ?_⟩
        rw [Function.update_self, Function.update_of_ne hfe]
        cases c f <;> simp
      · obtain ⟨e1, he1, f1, hf1, hne1⟩ := hc t' (Finset.mem_erase.mpr ⟨htt, ht'⟩)
        have hnot : e ∉ t'.powersetCard 2 := fun h => htt (hpriv t' ht' h)
        have h1 : e1 ≠ e := by rintro rfl; exact hnot he1
        have h2 : f1 ≠ e := by rintro rfl; exact hnot hf1
        refine ⟨e1, he1, f1, hf1, ?_⟩
        rw [Function.update_of_ne h1, Function.update_of_ne h2]
        exact hne1

theorem aux_peel_bound {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hpeel : ∀ S ⊆ G.cliqueFinset 3,
      (∀ e : Finset (Fin n), (S.filter (fun t => e ∈ t.powersetCard 2)).card ≤ 2) ∨
      ∃ t ∈ S, ∃ e ∈ t.powersetCard 2, ∀ t' ∈ S, e ∈ t'.powersetCard 2 → t' = t) :
    cliqueTransversalNumber G ≤ n - H n := by
  obtain ⟨c, hc⟩ := aux_peel_triangle_coloring G hpeel
  exact aux_edge_coloring_certificate G c hc

-- [item 386] K4-free deletion: the only free-set obstruction is a restored triangle; private surviving triangle sides certify free-set transfer
theorem aux_triangle_edge_deletion_obstruction {n : ℕ} (G F : SimpleGraph (Fin n))
    (hG : G.CliqueFree 4) (hF : F.CliqueFree 4) (hsub : F ≤ G)
    (hsupported : ∀ a b, G.Adj a b → ¬ F.Adj a b → ∃ c, G.Adj a c ∧ G.Adj b c)
    (U : Finset (Fin n)) (hU : ∀ s, IsBigMaximalClique F s → ¬ s ⊆ U) :
    (∀ s, IsBigMaximalClique G s → ¬ s ⊆ U) ↔
      (∀ a ∈ U, ∀ b ∈ U, ∀ c ∈ U, G.Adj a b → G.Adj a c → ¬ G.Adj b c) := by
  have hUF := (aux_K4_free_set_criterion F hF U).mp hU
  rw [aux_K4_free_set_criterion G hG U]
  constructor
  · exact And.left
  · intro htri
    refine ⟨htri, ?_⟩
    intro a ha b hb hab
    by_cases hf : F.Adj a b
    · obtain ⟨c, hac, hbc⟩ := hUF.2 a ha b hb hf
      exact ⟨c, hsub hac, hsub hbc⟩
    · exact hsupported a b hab hf

theorem aux_private_side_free_transfer {n : ℕ} (G F : SimpleGraph (Fin n))
    (hG : G.CliqueFree 4) (hF : F.CliqueFree 4) (hsub : F ≤ G)
    (hsupported : ∀ a b, G.Adj a b → ¬ F.Adj a b → ∃ c, G.Adj a c ∧ G.Adj b c)
    (hblock : ∀ a b c, G.Adj a b → G.Adj a c → G.Adj b c →
      ¬ F.Adj a b →
      (F.Adj a c ∧ ∀ d, ¬ (F.Adj a d ∧ F.Adj c d)) ∨
      (F.Adj b c ∧ ∀ d, ¬ (F.Adj b d ∧ F.Adj c d)))
    (U : Finset (Fin n)) (hU : ∀ s, IsBigMaximalClique F s → ¬ s ⊆ U) :
    ∀ s, IsBigMaximalClique G s → ¬ s ⊆ U := by
  apply (aux_triangle_edge_deletion_obstruction G F hG hF hsub hsupported U hU).mpr
  have hUF := (aux_K4_free_set_criterion F hF U).mp hU
  have edge : ∀ a ∈ U, ∀ b ∈ U, ∀ c ∈ U,
      G.Adj a b → G.Adj a c → G.Adj b c → F.Adj a b := by
    intro a ha b hb c hc hab hac hbc
    by_contra hn
    rcases hblock a b c hab hac hbc hn with ⟨he, hn⟩ | ⟨he, hn⟩
    · obtain ⟨d, hd⟩ := hUF.2 a ha c hc he
      exact hn d hd
    · obtain ⟨d, hd⟩ := hUF.2 b hb c hc he
      exact hn d hd
  intro a ha b hb c hc hab hac hbc
  exact hUF.1 a ha b hb c hc
    (edge a ha b hb c hc hab hac hbc)
    (edge a ha c hc b hb hac hab hbc.symm)
    (edge b hb c hc a ha hbc hab.symm hac.symm)

-- [item 401] Seymour-type colouring: if every subfamily S of edges has |S| < |⋃S|, the hypergraph has a nonmonochromatic 2-colouring; degree-3 corollary
theorem aux_seymour_coloring {α : Type*} [DecidableEq α]
    (F : Finset (Finset α))
    (hS : ∀ S ⊆ F, S.Nonempty → S.card < (S.biUnion id).card) :
    ∃ c : α → Bool, ∀ e ∈ F, ∃ x ∈ e, ∃ y ∈ e, c x ≠ c y := by
  classical
  suffices key : ∀ S, S ⊆ F → ∃ c : α → Bool, ∀ e ∈ S, ∃ x ∈ e, ∃ y ∈ e, c x ≠ c y from
    key F subset_rfl
  intro S
  induction S using Finset.strongInduction with
  | H S ih =>
    intro hSF
    rcases S.eq_empty_or_nonempty with h0 | hne
    · exact ⟨fun _ => true, by simp [h0]⟩
    have hlt := hS S hSF hne
    set P := S.biUnion id with hP
    let M : Matrix {t // t ∈ S} {x // x ∈ P} ℚ := fun t x => if x.val ∈ t.val then 1 else 0
    have hker : LinearMap.ker (M.mulVecLin) ≠ ⊥ := by
      apply LinearMap.ker_ne_bot_of_finrank_lt
      simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_coe]
      exact hlt
    obtain ⟨y, hyk, hy0⟩ := (Submodule.ne_bot_iff _).mp hker
    have hyk' : ∀ t : {t // t ∈ S}, ∑ x, (if x.val ∈ t.val then y x else 0) = 0 := by
      intro t
      have := congrFun (LinearMap.mem_ker.mp hyk) t
      rw [Matrix.mulVecLin_apply] at this
      simpa [Matrix.mulVec, dotProduct, M] using this
    obtain ⟨x0, hx0⟩ : ∃ x0, y x0 ≠ 0 := by
      by_contra h; push Not at h; exact hy0 (funext h)
    let S' := S.filter (fun e => ∀ x : {x // x ∈ P}, x.val ∈ e → y x = 0)
    have hss : S' ⊂ S := by
      refine (Finset.filter_ssubset).mpr ?_
      obtain ⟨e, he, hxe⟩ := Finset.mem_biUnion.mp x0.property
      exact ⟨e, he, fun h => hx0 (h x0 hxe)⟩
    obtain ⟨c', hc'⟩ := ih S' hss ((Finset.filter_subset _ _).trans hSF)
    let c : α → Bool := fun a => if h : a ∈ P then
      (if y ⟨a,h⟩ ≠ 0 then decide (0 < y ⟨a,h⟩) else c' a) else c' a
    refine ⟨c, ?_⟩
    intro e he
    by_cases he' : e ∈ S'
    · obtain ⟨x, hx, z, hz, hxz⟩ := hc' e he'
      have hfix : ∀ a ∈ e, c a = c' a := by
        intro a ha
        have haP : a ∈ P := Finset.mem_biUnion.mpr ⟨e, he, ha⟩
        have := (Finset.mem_filter.mp he').2 ⟨a, haP⟩ ha
        simp [c, haP, this]
      exact ⟨x, hx, z, hz, by rw [hfix x hx, hfix z hz]; exact hxz⟩
    · have hbad : ∃ x : {x // x ∈ P}, x.val ∈ e ∧ y x ≠ 0 := by
        by_contra h; push Not at h
        exact he' (Finset.mem_filter.mpr ⟨he, fun x hx => h x hx⟩)
      obtain ⟨x1, hx1e, hx1⟩ := hbad
      have hsum := hyk' ⟨e, he⟩
      have hpos : ∃ x : {x // x ∈ P}, x.val ∈ e ∧ 0 < y x := by
        by_contra h; push Not at h
        have hnp : ∀ x ∈ (Finset.univ : Finset {x // x ∈ P}),
            0 ≤ -(if x.val ∈ e then y x else 0) := by
          intro x _; split_ifs with hx
          · linarith [h x hx]
          · simp
        have := (Finset.sum_eq_zero_iff_of_nonneg hnp).mp (by rw [Finset.sum_neg_distrib, hsum]; simp) x1 (Finset.mem_univ _)
        simp [hx1e] at this; exact hx1 this
      have hneg : ∃ x : {x // x ∈ P}, x.val ∈ e ∧ y x < 0 := by
        by_contra h; push Not at h
        have hnp : ∀ x ∈ (Finset.univ : Finset {x // x ∈ P}),
            0 ≤ (if x.val ∈ e then y x else 0) := by
          intro x _; split_ifs with hx
          · exact h x hx
          · simp
        have := (Finset.sum_eq_zero_iff_of_nonneg hnp).mp hsum x1 (Finset.mem_univ _)
        simp [hx1e] at this; exact hx1 this
      obtain ⟨p, hpe, hp⟩ := hpos
      obtain ⟨q, hqe, hq⟩ := hneg
      refine ⟨p.val, hpe, q.val, hqe, ?_⟩
      have h1 : c p.val = true := by simp [c, p.property, hp.ne', hp]
      have h2 : c q.val = false := by simp [c, q.property, hq.ne, not_lt.mpr hq.le]
      rw [h1, h2]; decide

theorem aux_degree_three_hypergraph_coloring {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (hsize : ∀ e ∈ F, e.card = 3)
    (hdeg : ∀ v, (F.filter (v ∈ ·)).card ≤ 3)
    (hlow : ∀ S ⊆ F, S.Nonempty → ∃ v ∈ S.biUnion id, (S.filter (v ∈ ·)).card ≤ 2) :
    ∃ c : α → Bool, ∀ e ∈ F, ∃ x ∈ e, ∃ y ∈ e, c x ≠ c y := by
  classical
  apply aux_seymour_coloring F
  intro S hSF hne
  obtain ⟨v0, hv0, hv0d⟩ := hlow S hSF hne
  have hcount : (∑ e ∈ S, e.card) = ∑ v ∈ S.biUnion id, (S.filter (v ∈ ·)).card := by
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro e he
    rw [← Finset.sum_filter]
    congr 1
    ext v
    simp only [Finset.mem_filter, Finset.mem_biUnion, id_eq]
    exact ⟨fun hv => ⟨⟨e, he, hv⟩, hv⟩, fun hv => hv.2⟩
  have hdS : ∀ v, (S.filter (v ∈ ·)).card ≤ 3 := fun v =>
    (Finset.card_le_card (Finset.filter_subset_filter _ hSF)).trans (hdeg v)
  have hlt : (∑ v ∈ S.biUnion id, (S.filter (v ∈ ·)).card) < ∑ _v ∈ S.biUnion id, 3 :=
    Finset.sum_lt_sum (fun v _ => hdS v) ⟨v0, hv0, by omega⟩
  have h3 : (∑ e ∈ S, e.card) = 3 * S.card := by
    rw [Finset.sum_congr rfl (fun e he => hsize e (hSF he))]; simp [Nat.mul_comm]
  rw [hcount] at h3
  simp at hlt
  omega

-- [item 424] Triangle-family edge incidence is bounded by the common-neighbor count, with no fixed codegree bound
theorem aux_triangles_through_edge_le_codeg {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {a b : Fin n} (hab : G.Adj a b) :
    ((G.cliqueFinset 3).filter (fun t => a ∈ t ∧ b ∈ t)).card ≤
      (Finset.univ.filter (fun c => G.Adj a c ∧ G.Adj b c)).card := by
  classical
  let C := Finset.univ.filter (fun c => G.Adj a c ∧ G.Adj b c)
  have hsub : (G.cliqueFinset 3).filter (fun t => a ∈ t ∧ b ∈ t) ⊆
      C.image (fun c => ({a, b, c} : Finset (Fin n))) := by
    intro t ht
    obtain ⟨ht, ha, hb⟩ := Finset.mem_filter.mp ht
    have hcl := SimpleGraph.mem_cliqueFinset_iff.mp ht
    have hc : ((t.erase a).erase b).card = 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hab.ne.symm, hb⟩),
        Finset.card_erase_of_mem ha, hcl.card_eq]
    obtain ⟨c, he⟩ := Finset.card_eq_one.mp hc
    have hcm : c ∈ (t.erase a).erase b := by rw [he]; simp
    obtain ⟨hcb, hca, hct⟩ := Finset.mem_erase.mp hcm |>.imp_right Finset.mem_erase.mp
    apply Finset.mem_image.mpr
    refine ⟨c, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcl.isClique ha hct hca.symm,
      hcl.isClique hb hct hcb.symm⟩, ?_⟩
    have hrestore : insert a (insert b ((t.erase a).erase b)) = t := by
      rw [Finset.insert_erase (Finset.mem_erase.mpr ⟨hab.ne.symm, hb⟩), Finset.insert_erase ha]
    simpa [he] using hrestore
  exact (Finset.card_le_card hsub).trans Finset.card_image_le

theorem aux_edge_triangle_degree_le {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (S : Finset (Finset (Fin n))) (hS : S ⊆ G.cliqueFinset 3) (a b : Fin n) (hab : a ≠ b) :
    (S.filter (fun t => ({a,b} : Finset (Fin n)) ∈ t.powersetCard 2)).card ≤
      (Finset.univ.filter (fun c => G.Adj a c ∧ G.Adj b c)).card := by
  classical
  by_cases hadj : G.Adj a b
  · refine le_trans (Finset.card_le_card ?_) (aux_triangles_through_edge_le_codeg G hadj)
    intro t ht
    obtain ⟨htS, hp⟩ := Finset.mem_filter.mp ht
    have hsub := (Finset.mem_powersetCard.mp hp).1
    exact Finset.mem_filter.mpr ⟨hS htS, hsub (by simp), hsub (by simp)⟩
  · have : S.filter (fun t => ({a,b} : Finset (Fin n)) ∈ t.powersetCard 2) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro t ht
      obtain ⟨htS, hp⟩ := Finset.mem_filter.mp ht
      have hsub := (Finset.mem_powersetCard.mp hp).1
      exact hadj ((SimpleGraph.mem_cliqueFinset_iff.mp (hS htS)).isClique
        (hsub (by simp)) (hsub (by simp)) hab)
    rw [this]; simp

-- [item 428] Erdős 151 for codegree at most three when each triangle contains an edge of codegree at most two
theorem aux_codeg3_triangle_low_edge_bound {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h3 : ∀ a b, G.Adj a b → (Finset.univ.filter (fun c => G.Adj a c ∧ G.Adj b c)).card ≤ 3)
    (hlow : ∀ t ∈ G.cliqueFinset 3, ∃ a ∈ t, ∃ b ∈ t, a ≠ b ∧
      (Finset.univ.filter (fun c => G.Adj a c ∧ G.Adj b c)).card ≤ 2) :
    cliqueTransversalNumber G ≤ n - H n := by
  classical
  let T := G.cliqueFinset 3
  let F := T.image (Finset.powersetCard 2)
  have hs : ∀ e ∈ F, e.card = 3 := by
    intro e he
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp he
    rw [Finset.card_powersetCard, (SimpleGraph.mem_cliqueFinset_iff.mp ht).card_eq]
    decide
  have hd : ∀ a b, a ≠ b →
      (F.filter (fun E => ({a,b} : Finset (Fin n)) ∈ E)).card ≤
      (Finset.univ.filter (fun c => G.Adj a c ∧ G.Adj b c)).card := by
    intro a b hab
    dsimp [F]
    rw [Finset.filter_image]
    exact Finset.card_image_le.trans (aux_edge_triangle_degree_le G T subset_rfl a b hab)
  obtain ⟨c, hc⟩ := aux_degree_three_hypergraph_coloring F hs
    (by
      intro e
      by_cases he : ∃ E ∈ F, e ∈ E
      · obtain ⟨E, hE, he⟩ := he
        obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hE
        obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp he
        obtain ⟨a,b,hab,rfl⟩ := Finset.card_eq_two.mp hcard
        exact (hd a b hab).trans (h3 a b
          ((SimpleGraph.mem_cliqueFinset_iff.mp ht).isClique
            (hsub (by simp)) (hsub (by simp)) hab))
      · push Not at he
        rw [Finset.filter_false_of_mem he]
        simp)
    (by
      intro S hSF hne
      obtain ⟨E,hE⟩ := hne
      obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp (hSF hE)
      obtain ⟨a,ha,b,hb,hab,hle⟩ := hlow t ht
      refine ⟨{a,b}, Finset.mem_biUnion.mpr ⟨t.powersetCard 2,hE,?_⟩, ?_⟩
      · simp [Finset.mem_powersetCard, Finset.insert_subset_iff, ha, hb, hab]
      · exact (Finset.card_le_card (Finset.filter_subset_filter _ hSF)).trans
          ((hd a b hab).trans hle))
  exact aux_edge_coloring_certificate G c (fun t ht => hc _ (Finset.mem_image.mpr ⟨t,ht,rfl⟩))

-- [item 435] Seymour sparse triangle-family criterion implies Erdős 151; no codegree bound needed
theorem aux_triangle_sparse_bound {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hS : ∀ S ⊆ G.cliqueFinset 3, S.Nonempty →
      S.card < (S.biUnion (Finset.powersetCard 2)).card) :
    cliqueTransversalNumber G ≤ n - H n := by
  classical
  let F := (G.cliqueFinset 3).image (Finset.powersetCard 2)
  obtain ⟨c,hc⟩ := aux_seymour_coloring F (by
    intro U hUF hne
    let S := (G.cliqueFinset 3).filter (fun t => t.powersetCard 2 ∈ U)
    have him : S.image (Finset.powersetCard 2) = U := by
      ext E
      constructor
      · intro hE
        obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hE
        exact (Finset.mem_filter.mp ht).2
      · intro hE
        obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp (hUF hE)
        exact Finset.mem_image.mpr ⟨t,Finset.mem_filter.mpr ⟨ht,hE⟩,rfl⟩
    have hsne : S.Nonempty := by
      obtain ⟨E,hE⟩ := hne
      rw [← him] at hE
      obtain ⟨t,ht,_⟩ := Finset.mem_image.mp hE
      exact ⟨t,ht⟩
    have hlt := hS S (Finset.filter_subset _ _) hsne
    have hcard : U.card ≤ S.card := by rw [← him]; exact Finset.card_image_le
    have hu : U.biUnion id = S.biUnion (Finset.powersetCard 2) := by
      rw [← him]
      ext e
      simp
    rw [hu]
    exact hcard.trans_lt hlt)
  exact aux_edge_coloring_certificate G c (fun t ht => hc _ (Finset.mem_image.mpr ⟨t,ht,rfl⟩))

-- [item 441] K₂,₃,₆ has 36 triangles covering 36 edges, although every triangle has a codegree-two edge
theorem aux_K236_triangle_sparse_obstruction :
    let G := SimpleGraph.fromRel (fun a b : Fin 11 =>
      (if a.val < 2 then 0 else if a.val < 5 then 1 else 2) ≠
      (if b.val < 2 then 0 else if b.val < 5 then 1 else 2))
    let T := G.cliqueFinset 3
    T.card = 36 ∧ (T.biUnion (Finset.powersetCard 2)).card = 36 ∧
      (∀ t ∈ T, ∃ a ∈ t, ∃ b ∈ t, a ≠ b ∧
        (Finset.univ.filter (fun c => G.Adj a c ∧ G.Adj b c)).card ≤ 2) := by
  decide +kernel

-- [item 442] K₂,₂,₃ satisfies the new codegree-three low-edge hypothesis, but has codegree-three edges and no private triangle edge
theorem aux_K223_low_edge_not_caseC :
    let G := SimpleGraph.fromRel (fun a b : Fin 7 =>
      (if a.val < 2 then 0 else if a.val < 4 then 1 else 2) ≠
      (if b.val < 2 then 0 else if b.val < 4 then 1 else 2))
    (∀ a b, G.Adj a b →
      (Finset.univ.filter (fun c => G.Adj a c ∧ G.Adj b c)).card ≤ 3) ∧
    (∀ t ∈ G.cliqueFinset 3, ∃ a ∈ t, ∃ b ∈ t, a ≠ b ∧
      (Finset.univ.filter (fun c => G.Adj a c ∧ G.Adj b c)).card ≤ 2) ∧
    (∃ a b, G.Adj a b ∧
      (Finset.univ.filter (fun c => G.Adj a c ∧ G.Adj b c)).card = 3) ∧
    (∀ t ∈ G.cliqueFinset 3, ∀ e ∈ t.powersetCard 2,
      2 ≤ ((G.cliqueFinset 3).filter (fun u => e ∈ u.powersetCard 2)).card) := by
  decide +kernel

#print axioms aux_H_mem
#print axioms aux_tau_le_of_free
#print axioms aux_reduction
#print axioms aux_triangle_free
#print axioms aux_tau_le_neighbor
#print axioms aux_independent_card_mul_degree_bound
#print axioms aux_tau_le_of_independent
#print axioms aux_sqrt_bound
#print axioms aux_caseC_clique_card
#print axioms aux_caseC_common_neighbors
#print axioms aux_caseC_cliqueFree_five
#print axioms aux_caseC_clique_absorbed
#print axioms aux_caseC_four_cliques_equal
#print axioms aux_degree_two_incidence_bound
#print axioms aux_coloring_of_incidence_permutation
#print axioms aux_regular_symmetric_matrix_permutation
#print axioms aux_multigraph_incidence_coloring
#print axioms aux_degree_two_hypergraph_coloring
#print axioms aux_caseC_triangles_through_edge
#print axioms aux_caseC_triangle_edge_coloring
#print axioms aux_edge_coloring_certificate
#print axioms aux_caseC
#print axioms aux_triangle_intersecting_edge
#print axioms aux_edge_meeting_triangle_edges
#print axioms aux_no_sail_realization
#print axioms aux_square_triples_cubic
#print axioms aux_five_color_triangle_template
#print axioms aux_five_colorable_bound
#print axioms aux_K5_locally_cubic
#print axioms aux_K5_no_triangle_free_bipartition
#print axioms aux_K5_edge_flip_local_minimum
#print axioms aux_K5_vertex_partition_obstruction
#print axioms aux_five_colorable_edge_coloring
#print axioms aux_hom_template_bound
#print axioms aux_two_pentagons_edge_template
#print axioms aux_two_pentagons_hom_bound
#print axioms aux_fano_sail_survives_one_sum
#print axioms aux_pentagon_three_colors
#print axioms aux_two_pentagons_not_five_colorable
#print axioms aux_two_pentagons_six_colorable
#print axioms aux_fano_sail_survives_two_points
#print axioms aux_fano_sail_survives_two_lines_or_mixed
#print axioms aux_increasing_parent_bound
#print axioms aux_perfect_elimination_bound
#print axioms aux_maximal_clique_bipartition_bound
#print axioms aux_ranked_parent_bound
#print axioms aux_ranked_perfect_elimination_bound
#print axioms aux_pairwise_edges_star_or_triangle
#print axioms aux_complete_join_bound
#print axioms aux_line_clique_classification
#print axioms aux_line_maximal_star_full
#print axioms aux_line_big_maximal_classification
#print axioms aux_ordered_edge_encoding
#print axioms aux_line_root_triangle_maximal
#print axioms aux_line_star_of_degree_three_maximal
#print axioms aux_line_local_certificate_bound
#print axioms aux_line_through_no_triangle
#print axioms aux_line_pair_eq
#print axioms aux_line_selected_no_triangle
#print axioms aux_three_min_max_overlap
#print axioms aux_line_graph_intersection_bound
#print axioms aux_line_graph_bound
#print axioms aux_compl_triangle_free_bound
#print axioms aux_circular_consecutive_bound
#print axioms aux_K4_free_set_criterion
#print axioms aux_circular_arc_maximal_cliques_bound
#print axioms aux_neighborhood_independent_extension
#print axioms aux_comparability_cover_triangle
#print axioms aux_component_center_free_bound
#print axioms aux_comparability_bound
#print axioms aux_C4_no_ranked_parent
#print axioms aux_sed_strong_obstruction_free_sets
#print axioms aux_peel_triangle_coloring
#print axioms aux_peel_bound
#print axioms aux_triangle_edge_deletion_obstruction
#print axioms aux_private_side_free_transfer
#print axioms aux_seymour_coloring
#print axioms aux_degree_three_hypergraph_coloring
#print axioms aux_triangles_through_edge_le_codeg
#print axioms aux_edge_triangle_degree_le
#print axioms aux_codeg3_triangle_low_edge_bound
#print axioms aux_triangle_sparse_bound
#print axioms aux_K236_triangle_sparse_obstruction
#print axioms aux_K223_low_edge_not_caseC

/--
Erdős and Gallai made no progress on the question even when $G$ is $K_4$-free [Er88].
-/
@[category research open, question, AMS 5]
theorem erdos_151.variants.cliqueFree_four :
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)), G.CliqueFree 4 →
      cliqueTransversalNumber G ≤ n - H n := by
  sorry

/--
If $G$ is triangle-free, then $\tau(G)\leq n-H(n)$: the complement of an independent set meets
every edge.
-/
@[category research solved, AMS 5]
theorem erdos_151.variants.cliqueFree_three (n : ℕ) (G : SimpleGraph (Fin n))
    (hG : G.CliqueFree 3) : cliqueTransversalNumber G ≤ n - H n := by
  sorry

/--
It is easy to see that $\tau(G)\leq n-\sqrt{n}$. We state this with $\lfloor\sqrt{n}\rfloor$:
with the real square root the bound fails for a single edge ($n = 2$, $\tau = 1$).
-/
@[category research solved, AMS 5]
theorem erdos_151.variants.sqrt_bound (n : ℕ) (G : SimpleGraph (Fin n)) :
    cliqueTransversalNumber G ≤ n - Nat.sqrt n := by
  sorry

end Erdos151
