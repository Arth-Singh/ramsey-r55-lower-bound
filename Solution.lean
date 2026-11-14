module

public import RamseyR55

public section

/-!
# Proved solution

The statement of `Challenge.lean`, proved by the witness graph of `RamseyR55.ExooGraph`.
-/

/--
The lower bound $43 \le R(5,5)$ (Exoo, 1989): there is a graph on $42$ vertices with no clique
of size $5$ and no independent set of size $5$.
-/
theorem RamseyR55.ramsey_number_five_five_lower_bound :
    ∃ G : SimpleGraph (Fin 42), G.CliqueFree 5 ∧ (Gᶜ).CliqueFree 5 :=
  RamseyR55.exoo_lower_bound
