module

public import Mathlib.Combinatorics.SimpleGraph.Clique

@[expose] public section

/-!
# A graph on 42 vertices with no 5-clique and no independent 5-set

This file proves the lower bound $R(5,5) \ge 43$ of Exoo (1989). It defines a clique scan on
natural-number bit masks, proves that a scan with the result `false` excludes every clique, and
lets the Lean kernel evaluate the scan on an explicit graph and on its complement
(`decide +kernel`; no `native_decide`).
-/

namespace RamseyR55

/--
`cliqueScan n rows k lo cand` searches for `k` pairwise adjacent vertices among the vertices
`v` with `lo ≤ v < n` whose bit is set in `cand`. Row `v` of `rows` is the bit mask of the
neighbours of `v`. The scan picks the vertices of a clique in increasing order and keeps in
`cand` the common neighbours of the vertices picked so far. It returns `true` if it finds a
clique. Only natural-number bit operations occur, so the kernel can evaluate it.
-/
def cliqueScan (n : ℕ) (rows : List ℕ) : ℕ → ℕ → ℕ → Bool
  | 0, _, _ => true
  | k + 1, lo, cand => (List.range n).any fun v =>
      decide (lo ≤ v) && cand.testBit v &&
        cliqueScan n rows k (v + 1) (cand &&& rows.getD v 0)

/--
Completeness of the scan: if the rows contain every edge of `G`, then the scan finds every
`k`-clique of `G` whose vertices are at least `lo` and lie in `cand`.
-/
theorem clique_detected {n k : ℕ} (rows : List ℕ)
    (G : SimpleGraph (Fin n))
    (hrow : ∀ a b : Fin n, G.Adj a b → (rows.getD a.val 0).testBit b.val = true)
    (s : Finset (Fin n)) (hs : G.IsNClique k s) (lo cand : ℕ)
    (hlo : ∀ v ∈ s, lo ≤ v.val)
    (hbits : ∀ v ∈ s, cand.testBit v.val = true) :
    cliqueScan n rows k lo cand = true := by
  induction k generalizing s lo cand with
  | zero => rfl
  | succ k ih =>
      have hcard := hs.card_eq
      have hne : s.Nonempty := Finset.card_pos.mp (by omega)
      let v := s.min' hne
      have hv : v ∈ s := Finset.min'_mem s hne
      have hsub : G.IsNClique k (s.erase v) := by
        simpa using hs.erase_of_mem hv
      have hb : ∀ w ∈ s.erase v, (cand &&& rows.getD v.val 0).testBit w.val = true := by
        intro w hw
        obtain ⟨hne', hws⟩ := Finset.mem_erase.mp hw
        rw [Nat.testBit_and, hbits w hws, hrow v w (hs.isClique hv hws hne'.symm)]
        rfl
      have hl : ∀ w ∈ s.erase v, v.val + 1 ≤ w.val := by
        intro w hw
        obtain ⟨hwn, hws⟩ := Finset.mem_erase.mp hw
        have hle : v ≤ w := Finset.min'_le s w hws
        have hlt : v < w := lt_of_le_of_ne hle hwn.symm
        exact hlt
      have hrec := ih (s.erase v) hsub (v.val + 1) (cand &&& rows.getD v.val 0) hl hb
      simp only [cliqueScan, List.any_eq_true]
      refine ⟨v.val, List.mem_range.mpr v.isLt, ?_⟩
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨⟨hlo v hv, hbits v hv⟩, hrec⟩

/-- If the scan over all vertices returns `false`, then `G` has no `k`-clique. -/
theorem cliqueFree_of_scan_false {n k : ℕ} (rows : List ℕ)
    (G : SimpleGraph (Fin n))
    (hrow : ∀ a b : Fin n, G.Adj a b → (rows.getD a.val 0).testBit b.val = true)
    (cand : ℕ) (hall : ∀ v : Fin n, cand.testBit v.val = true)
    (hscan : cliqueScan n rows k 0 cand = false) : G.CliqueFree k := by
  intro s hs
  have h := clique_detected rows G hrow s hs 0 cand (by simp) (fun v _ => hall v)
  rw [hscan] at h
  contradiction

/-- The graph on `Fin n` in which `a` and `b` are adjacent when each row has the bit of the other. -/
def rowsGraph (n : ℕ) (rows : List ℕ) : SimpleGraph (Fin n) where
  Adj a b := a ≠ b ∧ (rows.getD a.val 0).testBit b.val = true ∧
    (rows.getD b.val 0).testBit a.val = true
  symm := by
    constructor
    intro a b h
    exact ⟨h.1.symm, h.2.2, h.2.1⟩
  loopless := by
    constructor
    intro a h
    exact h.1 rfl

/--
A graph without a `k`-clique and without an independent `l`-set, from two scans that return
`false`: one over the rows of the graph and one over rows `coRows` that contain every non-edge.
-/
theorem rows_witness {n k l : ℕ} (rows coRows : List ℕ) (cand : ℕ)
    (hall : ∀ v : Fin n, cand.testBit v.val = true)
    (hcover : ∀ a b : Fin n, a ≠ b →
      ((rows.getD a.val 0).testBit b.val = true ∧
        (rows.getD b.val 0).testBit a.val = true) ∨
      (coRows.getD a.val 0).testBit b.val = true)
    (hscan : cliqueScan n rows k 0 cand = false)
    (hcoscan : cliqueScan n coRows l 0 cand = false) :
    ∃ G : SimpleGraph (Fin n), G.CliqueFree k ∧ (Gᶜ).CliqueFree l := by
  refine ⟨rowsGraph n rows, ?_, ?_⟩
  · apply cliqueFree_of_scan_false rows _ _ cand hall hscan
    intro a b h
    exact h.2.1
  · apply cliqueFree_of_scan_false coRows _ _ cand hall hcoscan
    intro a b h
    obtain ⟨hne, hn⟩ := (SimpleGraph.compl_adj _ _ _).mp h
    rcases hcover a b hne with hp | hp
    · exact False.elim (hn ⟨hne, hp⟩)
    · exact hp

/--
The neighbour bit masks of a graph on 42 vertices: the two-colouring `Exoo(42)` of `K₄₂` as
described by Ge, Jayasooriya, Qiu, Sun and Yuan (arXiv:2212.12630), with one colour class taken
as the edge set. The graph has 435 edges and degrees 19 to 22.
-/
def exooRows : List ℕ := [2280274621574, 162502732045, 325005464091, 650010928166, 1300021856324, 2600043712648, 802040914192, 1604081828641, 3208163657410, 2018280803716, 4034414123785, 3675076703762, 2952106888229, 1506167261259, 3012334522519, 1626622533934, 3253245198941, 2108443952314, 4216887904629, 4035729298154, 3673412085205, 2948777659307, 1499500418903, 2998996643503, 1599980330334, 3199977437885, 2001908364666, 4003816729333, 3609586947562, 2820053642197, 1243671386027, 2488416512855, 570196582062, 1153278066013, 2315146066618, 232245622132, 464491244265, 928982488530, 1308209163172, 2341540419400, 285034327696, 570068655393]
/-- The neighbour bit masks of the complement of the graph of `exooRows`. -/
def exooCoRows : List ℕ := [2117771889528, 4235543779056, 4073041047008, 3748035582929, 3098024654763, 1798002798423, 3596005596847, 2793964682334, 1189882853437, 2379765706875, 363632386294, 722969805293, 1445939618778, 2891879241652, 1385711972200, 2771423944401, 1144801246626, 2289602427717, 181158344330, 362316688661, 724633377322, 1449266754644, 2898541897896, 1399041478992, 2798049403553, 1198035518786, 2396071037573, 394095564042, 788191128085, 1577455997994, 3153301383252, 1907482514600, 3823554961745, 3236178510498, 2065720575301, 4131441150603, 3864835790102, 3331625069101, 2814959440987, 1506750277815, 3013500555631, 1628954600158]

/-- The mask `2 ^ 42 - 1` holds every vertex. -/
theorem exoo_all_bits :
    ∀ v : Fin 42, (2 ^ 42 - 1 : ℕ).testBit v.val = true := by decide +kernel

/-- Each pair of distinct vertices is an edge of the rows or of the complement rows. -/
theorem exoo_rows_cover : ∀ a b : Fin 42, a ≠ b →
    ((exooRows.getD a.val 0).testBit b.val = true ∧
      (exooRows.getD b.val 0).testBit a.val = true) ∨
    (exooCoRows.getD a.val 0).testBit b.val = true := by decide +kernel

/-- The kernel evaluates the scan for a 5-clique in the graph: none. -/
theorem exoo_no_clique :
    cliqueScan 42 exooRows 5 0 (2 ^ 42 - 1) = false := by decide +kernel

/-- The kernel evaluates the scan for a 5-clique in the complement: none. -/
theorem exoo_no_coclique :
    cliqueScan 42 exooCoRows 5 0 (2 ^ 42 - 1) = false := by decide +kernel

/-- The lower bound $R(5,5) \ge 43$: a graph on 42 vertices with no 5-clique and no independent 5-set. -/
theorem exoo_lower_bound :
    ∃ G : SimpleGraph (Fin 42), G.CliqueFree 5 ∧ (Gᶜ).CliqueFree 5 := by
  exact rows_witness exooRows exooCoRows (2 ^ 42 - 1)
    exoo_all_bits exoo_rows_cover exoo_no_clique exoo_no_coclique

end RamseyR55
