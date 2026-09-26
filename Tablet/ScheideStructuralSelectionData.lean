import Tablet.MissingColors
import Tablet.ScheideExitVertices
import Tablet.ScheideStructuralConfiguration

-- [TABLET NODE: ScheideStructuralSelectionData]
structure ScheideStructuralSelectionData {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (C : ScheideStructuralConfiguration G k e0 phi T) where
-- BODY
  absorbedCount : ℕ
  retainedCount : ℕ
  exitEquiv : Fin retainedCount ≃
    {v : V // v ∈ ScheideExitVertices T phi}
  retained : Fin retainedCount → Fin C.s
  retained_injective : Function.Injective retained
  retained_missing : ∀ t : Fin retainedCount,
    C.gamma (retained t) ∈ MissingColors G phi (exitEquiv t).1
  selected_unique : ∀ (t t' : Fin retainedCount),
    C.gamma (retained t') ∈ MissingColors G phi (exitEquiv t).1 → t' = t
  absorbedEquiv : Fin absorbedCount ≃
    {i : Fin C.s // i ∉ Set.range retained}
  count_eq : C.s = absorbedCount + retainedCount
  exit_count_eq : retainedCount = (ScheideExitVertices T phi).card
  partition : ∀ i : Fin C.s,
    (∃! h : Fin absorbedCount, (absorbedEquiv h).1 = i) ∨
      (∃! t : Fin retainedCount, retained t = i)
