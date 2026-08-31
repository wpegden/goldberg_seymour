import Tablet.IncidentCoreEndpoints
import Tablet.IncidentCoreMissingColors
import Tablet.TashkinovTree
import Tablet.TreeSequenceVertexSet

-- [TABLET NODE: IncidentCoreTreeTransport]
theorem IncidentCoreTreeTransport {V E : Type*} [Fintype V] [Fintype E]
    (G : LooplessMultigraph V E) :
    (∀ (e0 : E) (k : ℕ) (phi : PartialEdgeColoring E k)
      (T : TreeSequence G e0),
      ∃ Tc : TreeSequence (IncidentCore G) e0,
        ∃ hlen : Tc.length = T.length,
          (∀ i : Fin (Tc.length + 1),
            (Tc.vertex i).1 = T.vertex (Fin.cast
              (congrArg (fun n => n + 1) hlen) i)) ∧
          (∀ j : Fin Tc.length,
            Tc.edge j = T.edge (Fin.cast hlen j)) ∧
          (TreeSequenceVertexSet Tc).card = (TreeSequenceVertexSet T).card ∧
          (TashkinovTree (IncidentCore G) e0 phi Tc ↔
            TashkinovTree G e0 phi T)) ∧
    (∀ (e0 : E) (k : ℕ) (phi : PartialEdgeColoring E k)
      (Tc : TreeSequence (IncidentCore G) e0),
      ∃ T : TreeSequence G e0,
        ∃ hlen : T.length = Tc.length,
          (∀ i : Fin (T.length + 1),
            T.vertex i = (Tc.vertex (Fin.cast
              (congrArg (fun n => n + 1) hlen) i)).1) ∧
          (∀ j : Fin T.length,
            T.edge j = Tc.edge (Fin.cast hlen j)) ∧
          (TreeSequenceVertexSet Tc).card = (TreeSequenceVertexSet T).card ∧
          (TashkinovTree G e0 phi T ↔
            TashkinovTree (IncidentCore G) e0 phi Tc)) := by
-- BODY
  sorry
