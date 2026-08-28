import Tablet.GlobalMaximumTriple
import Tablet.Incident
import Tablet.MissingColors
import Tablet.ScheideExitVertices

open scoped Sym2

-- [TABLET NODE: ScheideStructuralConfiguration]
structure ScheideStructuralConfiguration {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0) where
-- BODY
  p : ℕ
  s : ℕ
  p_ge_two : 2 ≤ p
  gamma : Fin s → Fin k
  gamma_injective : Function.Injective gamma
  y : Fin p → V
  baseEdge : Fin (p - 1) → E
  blockVertex : Fin s → Fin 2 → V
  blockEdge : Fin s → Fin 2 → E
  length_eq : T.length + 1 = p + 2 * s
  base_vertex_position : ∀ i : Fin p,
    T.vertex ⟨i.val, by omega⟩ = y i
  block_vertex_position : ∀ (i : Fin s) (j : Fin 2),
    T.vertex ⟨p + 2 * i.val + j.val, by omega⟩ = blockVertex i j
  base_edge_position : ∀ i : Fin (p - 1),
    T.edge ⟨i.val, by omega⟩ = baseEdge i
  block_edge_position : ∀ (i : Fin s) (j : Fin 2),
    T.edge ⟨p - 1 + 2 * i.val + j.val, by omega⟩ = blockEdge i j
  block_attaches_to_base : ∀ (i : Fin s) (j : Fin 2),
    ∃ q : Fin p, G.ends (blockEdge i j) = s(y q, blockVertex i j)
  block_color : ∀ (i : Fin s) (j : Fin 2),
    phi (blockEdge i j) = some (gamma i)
  block_color_missing_on_base : ∀ i : Fin s,
    ∃ q : Fin p, gamma i ∈ MissingColors G phi (y q)
  initial_nonfirst_avoids_blocks : ∀ i : Fin (p - 1), 1 ≤ i.val →
    ∀ c : Fin k, phi (baseEdge i) = some c → ∀ r : Fin s, c ≠ gamma r
  exit_covered : ∀ v ∈ ScheideExitVertices T phi,
    ∃ i : Fin s, gamma i ∈ MissingColors G phi v
  no_isolated : ∀ v : V, ∃ e : E, Incident G v e
  globally_maximum : GlobalMaximumTriple G k e0 phi T
