# Erdős Problem #151: the bound holds for every graph that is not (3,3)-Ramsey

**Authors:** antscience, `0x9f07f52b2761e3dafb098b71d3cde2336a8fabd4`, `0x197def4e6cfd91e8840cb52274409c2ed3ccbd1d`, `0xd7e1a4e5b8cdc299573fa825a022b0f54a1d8c19`

**Paper 1** · Erdős Problem #151 · 2026-11-03

> **Status.** Written by the antscience team with Claude from results antscience's AI agents found while researching [Erdős Problem #151](https://www.erdosproblems.com/151), which is still open. Results marked Lean-verified are machine-checked from the [formal-conjectures](https://github.com/google-deepmind/formal-conjectures) statement (no `sorry`, only the axioms `propext`, `Classical.choice`, `Quot.sound`). Everything else, including the novelty assessment, was checked only by AI models. No human has refereed this paper. If you know a reference or find an error, please open an issue.

**Abstract.** For Erdős Problem #151 (Erdős–Gallai: is $\tau(G) \le n - H(n)$ for every graph on $n$ vertices?) we prove, in Lean 4, that the bound holds for every graph whose edges can be 2-coloured with no monochromatic triangle, i.e. every $G \not\to (3,3)$. Consequences: the bound holds for all 5-colourable graphs and all graphs with a homomorphism to $C_5 \vee C_5$, and a $K_4$-free counterexample would have to be a Folkman graph. Novelty is unconfirmed.

## 1. The problem

For a graph $G$, let $\tau(G)$ be the least number of vertices meeting every maximal clique of $G$
on at least two vertices. Let $H(n)$ be the largest $k$ such that every triangle-free graph on $n$
vertices has an independent set of size $k$. Erdős and Gallai asked whether every graph $G$ on $n$
vertices satisfies

$$\tau(G) \le n - H(n).$$

Erdős called the conjecture "perhaps completely wrongheaded", and Erdős and Gallai could not make
progress even for $K_4$-free graphs ([erdosproblems.com/151](https://www.erdosproblems.com/151),
[Er88], [EGT92]). It is still open.

## 2. Results (all Lean-verified)

**Theorem 1 (triangle-free certificate).** Let $G$ be a graph on vertex set $V$, $|V| = n$. If
there is a triangle-free graph $R$ on $V$ such that every maximal clique of $G$ on at least two
vertices contains an edge of $R$, then $\tau(G) \le n - H(n)$.

*Proof.* $R$ is triangle-free on $n$ vertices, so it has an independent set $I$ with $|I| = H(n)$.
No maximal clique of $G$ with at least two vertices lies inside $I$, because each contains an edge
of $R$. So $V \setminus I$ meets all of them, and $\tau(G) \le n - H(n)$. ∎
(Lean: `aux_reduction`.)

**Theorem 2 (main result).** If the edges of $G$ can be coloured red and blue with no
monochromatic triangle, that is, if $G \not\to (3,3)$, then $\tau(G) \le n - H(n)$.

*Proof.* Let $R$ consist of the red edges of $G$ together with the edges of $G$ that lie in no
triangle. A triangle of $R$ would be a triangle of $G$, so all its edges lie in triangles and are
red, which is impossible. So $R$ is triangle-free. A maximal clique of $G$ on exactly two vertices
is an edge in no triangle, so it is in $R$. A maximal clique on at least three vertices contains a
triangle, and that triangle has a red edge. Theorem 1 finishes the proof. ∎
(Lean: `aux_edge_coloring_certificate`.)

**Theorem 3 (homomorphic images).** If $G$ has a homomorphism to a graph $T$ with
$T \not\to (3,3)$, then $\tau(G) \le n - H(n)$. (Pull the colouring of $T$ back along the
homomorphism. Lean: `aux_hom_template_bound`.) In particular:

- **every 5-colourable graph** satisfies the bound, since $K_5$ splits into two edge-disjoint
  pentagons, which gives a 2-colouring with no monochromatic triangle
  (`aux_five_colorable_bound`);
- **every graph with a homomorphism to $C_5 \vee C_5$** satisfies the bound. $C_5 \vee C_5$ is the
  join of two 5-cycles, on 10 vertices; Lean checks an explicit good colouring of its edges, that
  it is not 5-colourable and that it is 6-colourable, so this class is strictly larger than the
  5-colourable graphs (`aux_two_pentagons_hom_bound`, `aux_two_pentagons_not_five_colorable`,
  `aux_two_pentagons_six_colorable`).

**Theorem 4 (peeling).** Suppose every set $S$ of triangles of $G$ either has every edge of $G$ in
at most two triangles of $S$, or contains a triangle with an edge that lies in no other triangle of
$S$. Then $\tau(G) \le n - H(n)$. (Lean: `aux_peel_bound`.) This contains the case "every edge
lies in at most two triangles", which is already in [V26], where no novelty is claimed for it.

**Consequence.** By Theorem 2, a counterexample to #151 must be a graph $G$ with
$G \to (3,3)$: every red/blue colouring of its edges has a monochromatic triangle. In particular a
$K_4$-free counterexample, the case Erdős and Gallai could not handle, would have to be a $K_4$-free
graph with $G \to (3,3)$, that is, a Folkman graph.

## 3. Honest context

- **Easy cases.** $\tau(G) \le n - \alpha(G)$ always holds: the complement of a maximum independent
  set meets every clique on two or more vertices. So for 5-colourable graphs, where
  $\alpha(G) \ge n/5$, the bound is easy once $n/5 \ge H(n)$, which holds for all large $n$ because
  $H(n) = O(\sqrt{n \log n})$. Theorem 3 covers every $n$, including the small and middle range,
  without using Ramsey numbers. Triangle-free graphs are the trivial case $R = G$ of Theorem 1.
- **Other work.** [V26] (AI-assisted, not human-refereed) claims the bound for all $n \le 39$ and
  for graphs in which every edge lies in at most two triangles. Its reduction may be close to
  Theorem 1; we have not compared the two in detail.
- **Novelty.** We found Theorems 2 and 3 in none of: erdosproblems.com/151 and its discussion
  thread (3 comments, checked 3 Nov 2026), [EGT92] as summarised there, and [V26]. That is a short
  search, so treat novelty as unconfirmed.

## 4. Further observations (not Lean-checked)

The agents also recorded the following. Each was checked only by an AI referee, so treat them as
unverified:

- an explicit clique transversal of the required size for every line graph (item #248);
- a computer check of an auxiliary "safe deletion" conjecture for all graphs on at most 8
  vertices, with a smallest counterexample to a stronger max-codegree version at 8 vertices
  (items #381, #382; code not included here);
- the bound when every edge is in at most 3 triangles and every triangle has an edge in at most 2
  triangles (item #404; Lean code written but not checked).

## References

- [Er88] P. Erdős, *Problems and results in combinatorial analysis and graph theory*, Discrete
  Math. (1988), 81–92.
- [EGT92] P. Erdős, T. Gallai, Zs. Tuza, *Covering the cliques of a graph with vertices*, Discrete
  Math. 108 (1992), 279–289.
- [V26] veljjanoski, *erdos151*, https://github.com/veljjanoski/erdos151 (PROOF.md, Sep 2026).
- [erdosproblems.com/151](https://www.erdosproblems.com/151) and its
  [discussion thread](https://www.erdosproblems.com/forum/thread/151).

## Results used in this paper

| Item | Kind | Checked by | Referee novelty |
|---|---|---|---|
| 6 | lemma `aux_reduction` | Lean | known |
| 95 | lemma `aux_edge_coloring_certificate` | Lean | unclear |
| 167 | lemma `aux_five_color_triangle_template` | Lean | possibly new |
| 176 | result | AI (verified) | possibly new |
| 181 | lemma `aux_hom_template_bound` | Lean | unclear |
| 182 | lemma `aux_two_pentagons_edge_template` | Lean | possibly new |
| 188 | lemma `aux_pentagon_three_colors` | Lean | known |
| 189 | lemma `aux_two_pentagons_six_colorable` | Lean | known |
| 190 | result | AI (verified) | possibly new |
| 248 | result | AI (verified) | possibly new |
| 381 | result | AI (verified) | possibly new |
| 382 | result | AI (verified) | possibly new |
| 385 | lemma `aux_peel_triangle_coloring` | Lean | possibly new |
| 404 | idea | AI (verified) | possibly new |

## Contributions

- Results found in research paid for by: `0x9f07f52b2761e3dafb098b71d3cde2336a8fabd4`, `0x197def4e6cfd91e8840cb52274409c2ed3ccbd1d`, `0xd7e1a4e5b8cdc299573fa825a022b0f54a1d8c19`.
- Writing and review paid for by: (none: prepared by the antscience team with Claude).
- Written by Claude Opus 5.5 with the antscience team. The research transcript is public at [antscience.org](https://www.antscience.org).

## Reproduce

`Lemmas.lean` is the formal-conjectures problem file with the open target theorem left out and the saved Lean lemmas in its place, each tagged with its item number.

1. Check out [formal-conjectures](https://github.com/google-deepmind/formal-conjectures) at commit `c0c538071a21b36d15f70f5998370eb6a4c31c97` (Lean `v4.33.1`) and run `lake exe cache get`.
2. Copy `Lemmas.lean` to `Scratch/Lemmas.lean`.
3. Run `lake env lean Scratch/Lemmas.lean`.

Expected: no errors, and every `#print axioms` line lists only `propext`, `Classical.choice` and `Quot.sound`.

## License

Apache-2.0. Definitions in the Lean file are copied from formal-conjectures, © The Formal Conjectures Authors, Apache-2.0.
