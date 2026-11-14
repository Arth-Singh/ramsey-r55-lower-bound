module

public import Mathlib.Combinatorics.SimpleGraph.Clique

public section

/-!
# The lower bound $R(5,5) \ge 43$

The Ramsey number $R(5,5)$ is the least $n$ such that every simple graph on $n$ vertices has
a clique of size $5$ or an independent set of size $5$. An independent set of a graph is a
clique of its complement. So a graph on $42$ vertices without a $5$-clique, whose complement
also has no $5$-clique, shows that $R(5,5) > 42$. Exoo found such a graph in 1989; $43$ is still
the best known lower bound.

The statement uses only Mathlib definitions: `SimpleGraph`, `SimpleGraph.CliqueFree`, and the
complement of a simple graph. It is the statement of
`RamseyNumbers.ramsey_number_five_five_lower_bound` in the Formal Conjectures repository.
-/

/--
The lower bound $43 \le R(5,5)$ (Exoo, 1989): there is a graph on $42$ vertices with no clique
of size $5$ and no independent set of size $5$.
-/
theorem RamseyR55.ramsey_number_five_five_lower_bound :
    ∃ G : SimpleGraph (Fin 42), G.CliqueFree 5 ∧ (Gᶜ).CliqueFree 5 := by
  sorry
