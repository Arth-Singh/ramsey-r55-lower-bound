# R(5,5) ≥ 43 in Lean 4

A Lean 4 / Mathlib proof of Exoo's lower bound for the diagonal Ramsey number $R(5,5)$:

```lean
theorem RamseyR55.ramsey_number_five_five_lower_bound :
    ∃ G : SimpleGraph (Fin 42), G.CliqueFree 5 ∧ (Gᶜ).CliqueFree 5
```

There is a simple graph on 42 vertices with no clique of size 5 and no independent set of
size 5. So $R(5,5) > 42$. The value of $R(5,5)$ is open; the known bounds are
$43 \le R(5,5) \le 46$, and 43 has been the best lower bound since Exoo's paper of 1989.

This is the statement that the [Formal Conjectures](https://github.com/google-deepmind/formal-conjectures)
repository records, without a proof, as `RamseyNumbers.ramsey_number_five_five_lower_bound` in
`FormalConjectures/Wikipedia/RamseyNumbers.lean`.

## How the proof works

`RamseyR55/ExooGraph.lean` has four parts.

1. `cliqueScan`: a search for a clique of a given size in a graph that is given by one
   natural-number bit mask of neighbours for each vertex.
2. `cliqueFree_of_scan_false`: if the scan over all vertices returns `false`, the graph has no
   clique of that size. The proof is by induction on the clique size; it takes the smallest
   vertex of a clique first.
3. `exooRows` and `exooCoRows`: the bit masks of an explicit graph on 42 vertices (435 edges,
   degrees 19 to 22) and of its complement.
4. Four closed statements that the Lean kernel evaluates (`decide +kernel`): the two scans
   return `false`, each pair of distinct vertices is an edge of the graph or of the complement
   rows, and the start mask holds all 42 vertices.

No `native_decide` is used. The theorem depends only on the axioms `propext`,
`Classical.choice`, and `Quot.sound`.

## Check it

```
lake exe cache get
lake build
```

After the Mathlib cache is in place, the build takes a few seconds; most of it is the kernel
evaluation of the two scans.

## Layout

| File | Content |
|---|---|
| `Challenge.lean` | The statement, with `sorry`. Imports only Mathlib. |
| `Solution.lean` | The same statement, proved. |
| `RamseyR55/ExooGraph.lean` | The proof development. |
| `comparator.json` | Configuration for [Comparator](https://github.com/leanprover/comparator). |
| `formalization.yaml` | Sources, authorship, automation, and review, in the `formalization.yaml` v0.4 format. |

## Sources

- G. Exoo, *A lower bound for R(5,5)*, Journal of Graph Theory 13 (1989), 97–98.
  [doi:10.1002/jgt.3190130113](https://doi.org/10.1002/jgt.3190130113). The result.
- L. Ge, Y. Jayasooriya, A. Qiu, M. Sun, V. Yuan, *Study of Exoo's Lower Bound for Ramsey
  number R(5,5)*, [arXiv:2212.12630](https://arxiv.org/abs/2212.12630). The explicit description
  of the colouring from which the bit masks were built.

## How this proof was made

The Lean proof is machine-written.

- An AI agent (OpenAI `gpt-6-astra` in the Codex CLI), one of 25 agents in an automated run,
  wrote the clique scan, its correctness proof, and the final assembly. A verifier compiled its
  work with Lean and accepted only the three standard axioms.
- A second AI system (Anthropic Claude, in Claude Code) prepared the inputs of the run (the
  graph data and a probe of the kernel evaluation), operated the run, checked the result again,
  and ported it to this repository (Lean 4.35 module layout, neutral names, docstrings,
  metadata).
- The maintainer directed the work and is responsible for this repository. No human has read
  the proof line by line. The guarantee is the Lean kernel, not a human review.

The result is a formalization of a known theorem. This repository makes no claim of priority.

## Licence

Apache-2.0. See `LICENSE`.
