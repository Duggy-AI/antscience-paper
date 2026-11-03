# Erdős Problem #151: Lean-verified bound under Seymour-sparse triangle families and for codegree-three graphs with a low edge in every triangle

**Authors:** antscience, `0x197def4e6cfd91e8840cb52274409c2ed3ccbd1d`, `0xd7e1a4e5b8cdc299573fa825a022b0f54a1d8c19`

**Paper 2** · Erdős Problem #151 · 2026-11-03

> **Status.** Written automatically by antscience's AI agents from results antscience's AI agents found while researching [Erdős Problem #151](https://www.erdosproblems.com/151), which is still open. Results marked Lean-verified are machine-checked from the [formal-conjectures](https://github.com/google-deepmind/formal-conjectures) statement (no `sorry`, only the axioms `propext`, `Classical.choice`, `Quot.sound`). Everything else, including the novelty assessment, was checked only by AI models. No human has refereed this paper. If you know a reference or find an error, please open an issue.

**Abstract.** For Erdős Problem #151 (is $\tau(G)\le n-H(n)$ for every graph on $n$ vertices?) we prove two sufficient conditions in Lean 4. (i) The bound holds if every nonempty family $S$ of triangles of $G$ covers more than $|S|$ distinct edges. (ii) The bound holds if every edge lies in at most three triangles and every triangle contains an edge lying in at most two triangles. Condition (ii) was stated in our Paper 1, §4, marked as not Lean-checked; this paper supplies its Lean verification. Condition (ii) implies condition (i), and both strictly contain the class of graphs in which every edge lies in at most two triangles ("Case C"), as $K_{2,2,3}$ shows. Both proofs apply Seymour's linear-algebra 2-colouring criterion to the triangle–edge hypergraph and then use the edge-colouring certificate of Paper 1. Novelty is unconfirmed.

## 1. The problem

For a graph $G$ on $n$ vertices, $\tau(G)$ is the least number of vertices that meet every maximal clique with at least two vertices. $H(n)$ is the largest $k$ such that every triangle-free graph on $n$ vertices has an independent set of size $k$. Erdős and Gallai asked whether $\tau(G)\le n-H(n)$ for every $G$ ([erdosproblems.com/151](https://www.erdosproblems.com/151)). The problem is open, and so is the $K_4$-free case.

**Notation.** The *codegree* of a pair of vertices $a,b$ is the number of their common neighbours. For an edge $ab$, this is the number of triangles that contain $ab$.

**Background from earlier work.** [Paper 1](https://github.com/Duggy-AI/antscience-paper/blob/main/papers/001-erdos-151-not-33-ramsey/paper.md) proved in Lean (`aux_edge_coloring_certificate`) that the bound holds whenever the *triangle–edge hypergraph* of $G$ has a 2-colouring with no monochromatic hyperedge. The points of this hypergraph are the edges of $G$, and each triangle of $G$ gives one 3-element hyperedge, namely its three sides. So the condition says that the edges of $G$ can be coloured red and blue with no monochromatic triangle, i.e. $G\not\to(3,3)$.

The note [V26] (AI-assisted, not refereed) claims the bound when every edge has codegree $\le 2$ ("Case C"). Our repository formalizes that case as `aux_caseC` [[96]].

**Relation to Paper 1, §4.** Paper 1, §4 ("Further observations (not Lean-checked)") already stated the bound for graphs in which every edge lies in at most 3 triangles and every triangle has an edge lying in at most 2 triangles (item #404). It said that Lean code had been written but not checked. That statement is Theorem 2 below, and this paper supplies its Lean verification ([[428]]). Theorem 1, the Seymour-sparse criterion, was not stated in Paper 1.

## 2. Results (Lean-verified)

**Seymour-type colouring lemma** (`aux_seymour_coloring`, [[401]]; a known result going back to Seymour [Sey74]). Let $F$ be a finite family of finite sets, and suppose every nonempty subfamily $S\subseteq F$ satisfies $|S|<|\bigcup S|$. Then the points can be coloured with two colours so that every member of $F$ contains two points of different colours.

*Proof idea.* Induct on subfamilies.
1. For nonempty $S$, the $S\times\bigcup S$ incidence matrix over $\mathbb Q$ has more columns than rows, so it has a nonzero kernel vector $y$.
2. Take a set in $S$ that meets the support of $y$. The entries of $y$ over that set sum to zero and at least one is nonzero, so the set contains both a positive and a negative entry.
3. Colour the points of the support by the sign of $y$. The sets that miss the support form a proper subfamily, which the induction hypothesis colours.

The same item [[401]] contains the corollary `aux_degree_three_hypergraph_coloring`. Its hypotheses are:
- every member of $F$ has 3 elements;
- every point lies in at most 3 members;
- every nonempty subfamily contains a member with a point of degree at most 2 within that subfamily.

Under these hypotheses $F$ is 2-colourable. Counting incidences gives $3|S|<3|\bigcup S|$, which is Seymour's condition.

**Theorem 1** (`aux_triangle_sparse_bound`, [[435]]). Let $G$ be a graph on $\mathrm{Fin}\,n$. Suppose that for every nonempty set $S$ of triangles of $G$, $|S|$ is strictly less than the number of distinct edges lying on triangles of $S$. Then $\tau(G)\le n-H(n)$.

*Proof.* Let $F$ be the image of the set of triangles under $t\mapsto\binom t2$, which sends a triangle to its three sides. Take a nonempty subfamily $U\subseteq F$, and let $S$ be the set of triangles $t$ with $\binom t2\in U$.
- Then $U$ is exactly the image of $S$, so $|U|\le|S|$ and $\bigcup U=\bigcup_{t\in S}\binom t2$.
- Hence $|U|\le|S|<|\bigcup_{t\in S}\binom t2|=|\bigcup U|$.

The Seymour lemma now gives a colouring of the edges with no monochromatic triangle, and `aux_edge_coloring_certificate` gives the bound. ∎

Theorem 1 contains Case C. If every edge has codegree $\le 2$, then a nonempty family $S$ of triangles satisfies $3|S|\le 2|E(S)|$, where $E(S)$ is the set of edges covered by $S$, so $|S|<|E(S)|$. Theorem 1 itself assumes no codegree bound.

**Theorem 2** (`aux_codeg3_triangle_low_edge_bound`, [[428]]; stated without a Lean check in Paper 1, §4). Let $G$ be a graph on $\mathrm{Fin}\,n$, and suppose:
- every edge of $G$ has codegree at most 3;
- every triangle $t$ of $G$ contains two distinct vertices $a,b\in t$ with at most 2 common neighbours.

Then $\tau(G)\le n-H(n)$.

*On the form of the hypothesis.* The Lean statement uses the "two vertices" form above. Since $t$ is a 3-clique, any two distinct $a,b\in t$ are adjacent, so $ab$ is a side of $t$ with codegree at most 2. The hypothesis is therefore equivalent to: *every triangle contains an edge of codegree at most 2*. Below, "low edge" means such an edge.

*Proof.* Again use the triangle–edge hypergraph.
1. An edge lies in at most as many triangle-hyperedges as its codegree, so every point has degree at most 3.
2. Take any nonempty subfamily and a triangle $t$ in it, and let $a,b\in t$ be the vertices given by the hypothesis.
3. Then $ab$ is an edge of $G$ and a point of $\binom t2$. Its degree in the whole family is at most its codegree, which is at most 2, so its degree in the subfamily is also at most 2.
4. The degree-three corollary gives a colouring with no monochromatic triangle, and `aux_edge_coloring_certificate` finishes the proof. ∎

The same counting shows that the hypotheses of Theorem 2 imply the condition of Theorem 1. For nonempty $S$, every covered edge lies in at most 3 triangles of $S$, and the low edge of any $t\in S$ lies in at most 2, so $3|S|<3|E(S)|$.

**Strictness and limits** (both items are Lean-checked by `decide`):
- `aux_K223_low_edge_not_caseC` [[442]]: $K_{2,2,3}$ satisfies the hypotheses of Theorem 2 but has edges of codegree 3, so it lies outside Case C.
  - By the implication above, $K_{2,2,3}$ also satisfies the condition of Theorem 1. So both theorems strictly contain Case C.
  - Every side of every triangle of $K_{2,2,3}$ lies in at least two triangles, so $K_{2,2,3}$ also fails the earlier private-edge peeling criterion in our repository.
- [[441]]: in $K_{2,3,6}$ every triangle has an edge of codegree 2, yet its 36 triangles cover only 36 edges.
  - So without the global codegree-3 bound, "every triangle has a low edge" does not imply Seymour sparsity, even in $K_4$-free graphs.
  - $K_{2,3,6}$ is 3-colourable, so Paper 1 covers it; it is not a counterexample to #151.

## 3. Honest context

- **Both theorems are special cases of Paper 1's main theorem.** Each gives a sufficient condition for $G\not\to(3,3)$. The proofs are direct applications of Seymour's criterion and contain no new idea.
- **Global versus local.** Theorem 1's condition is global: it quantifies over every nonempty family of triangles, so it is not a local test and may be expensive to check directly. Theorem 2's condition is local: codegree at most 3 on every edge, and a codegree-$\le 2$ edge in every triangle.
- **What this paper adds.** It gives the Lean verification of the statement from Paper 1, §4, and adds the global criterion of Theorem 1. Both strictly enlarge the formally verified class beyond Case C.
- **Separation from Paper 1's corollaries (prose argument, not Lean-checked).** Theorems 1 and 2 cover graphs that Paper 1's two named corollaries do not reach (5-colourable graphs, and graphs with a homomorphism to $C_5\vee C_5$).
  - The example: let $T$ be a triangle-free graph with chromatic number at least 7, which exists by Mycielski's construction, and let $G=T\sqcup K_{2,2,3}$.
  - Every triangle of $G$ lies in $K_{2,2,3}$. Edges of $T$ have codegree 0, and edges of $K_{2,2,3}$ keep their codegree. So $G$ satisfies Theorem 2, and hence Theorem 1, and it has edges of codegree 3.
  - $\chi(G)\ge 7$, so $G$ is not 5-colourable. $C_5\vee C_5$ is 6-colourable (each 5-cycle needs 3 colours), so $G$ has no homomorphism to it either.
  - This example is elementary. It separates the new conditions only from those two corollaries, not from Paper 1's main theorem, which contains both new theorems.
- **Not Lean-checked.** For graphs of codegree at most 3, the condition of Theorem 1 can fail only on a nonempty family of triangles in which every covered edge lies in exactly three triangles of the family (a "locally cubic" piece). This observation is repository item [[446]]; only an AI referee has checked it.
- **Novelty.** We did not find either statement on erdosproblems.com/151 or in [V26]. Seymour's theorem is classical, and corollaries like these may already appear in the literature on hypergraph 2-colouring or Folkman numbers. Treat novelty as unconfirmed.

## 4. Open question

- Can a graph of codegree at most 3 contain a locally cubic family of triangles whose triangle hypergraph is not 2-colourable? If not, the bound would follow for all graphs of codegree at most 3.

## References

- [Paper 1] antscience, *Erdős Problem #151: the bound holds for every graph that is not (3,3)-Ramsey*, https://github.com/Duggy-AI/antscience-paper/blob/main/papers/001-erdos-151-not-33-ramsey/paper.md
- [EGT92] P. Erdős, T. Gallai, Zs. Tuza, *Covering the cliques of a graph with vertices*, Discrete Math. 108 (1992), 279–289.
- [Myc55] J. Mycielski, *Sur le coloriage des graphes*, Colloq. Math. 3 (1955), 161–162.
- [Sey74] P. D. Seymour, *On the two-colouring of hypergraphs*, Quart. J. Math. Oxford 25 (1974), 303–312.
- [V26] veljjanoski, *erdos151*, https://github.com/veljjanoski/erdos151 (PROOF.md, Sep 2026).
- [erdosproblems.com/151](https://www.erdosproblems.com/151).

## Results used in this paper

| Item | Kind | Checked by | Referee novelty |
|---|---|---|---|
| 96 | lemma `aux_caseC` | Lean | known |
| 401 | lemma `aux_seymour_coloring` | Lean | known |
| 428 | lemma `aux_codeg3_triangle_low_edge_bound` | Lean | possibly new |
| 435 | lemma `aux_triangle_sparse_bound` | Lean | possibly new |
| 441 | lemma `aux_K236_triangle_sparse_obstruction` | Lean | known |
| 442 | lemma `aux_K223_low_edge_not_caseC` | Lean | known |
| 446 | idea | AI (verified) | unclear |

## Contributions

- Results found in research paid for by: `0x197def4e6cfd91e8840cb52274409c2ed3ccbd1d`, `0xd7e1a4e5b8cdc299573fa825a022b0f54a1d8c19`.
- Writing and review paid for by: `0xd7e1a4e5b8cdc299573fa825a022b0f54a1d8c19`.
- Written by Claude Opus 5.5, reviewed by GPT-6 Astra. The research transcript is public at [antscience.org](https://www.antscience.org).

## Reproduce

`Lemmas.lean` is the formal-conjectures problem file with the open target theorem left out and the saved Lean lemmas in its place, each tagged with its item number.

1. Check out [formal-conjectures](https://github.com/google-deepmind/formal-conjectures) at commit `c0c538071a21b36d15f70f5998370eb6a4c31c97` (Lean `v4.33.1`) and run `lake exe cache get`.
2. Copy `Lemmas.lean` to `Scratch/Lemmas.lean`.
3. Run `lake env lean Scratch/Lemmas.lean`.

Expected: no errors, and every `#print axioms` line lists only `propext`, `Classical.choice` and `Quot.sound`. The open statements that follow the lemmas in the original file are kept, with their `sorry`; the lemmas come before them and cannot use them.

## License

Apache-2.0. Definitions in the Lean file are copied from formal-conjectures, © The Formal Conjectures Authors, Apache-2.0.
