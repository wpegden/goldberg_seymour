import Tablet.CertifiedETTPredecessor
import Tablet.ExtendedTashkinovTree
import Tablet.MaximumProperty
import Tablet.TashkinovSeriesData
import Tablet.TashkinovSeriesStep
import Tablet.TashkinovStoredColors

-- [TABLET NODE: CertifiedETTRestriction]
theorem CertifiedETTRestriction {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (generating : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T generating)
    (hMP : MaximumProperty ett) (r : ℕ)
    (hrPositive : 1 ≤ r) (hrBefore : r < ett.rounds) :
    ∃ restricted : ExtendedTashkinovTree G k e0 input
        (ett.series.data.tree ⟨r + 1, by omega⟩)
        (ett.series.data.coloring ⟨r, by omega⟩),
      ∃ hr : restricted.rounds = r,
        MaximumProperty restricted ∧
        (∀ i : Fin (restricted.rounds + 2),
          restricted.series.data.tree i =
            ett.series.data.tree (Fin.castLE (by omega) i)) ∧
        (∀ i : Fin (restricted.rounds + 1),
          restricted.series.data.coloring i =
              ett.series.data.coloring (Fin.castLE (by omega) i) ∧
          restricted.series.data.stored i =
              ett.series.data.stored (Fin.castLE (by omega) i) ∧
          restricted.series.data.connectingEdges i =
              ett.series.data.connectingEdges (Fin.castLE (by omega) i) ∧
          restricted.series.data.kind i =
              ett.series.data.kind (Fin.castLE (by omega) i) ∧
          restricted.series.data.chosenVertex i =
              ett.series.data.chosenVertex (Fin.castLE (by omega) i) ∧
          restricted.series.data.outsideVertex i =
              ett.series.data.outsideVertex (Fin.castLE (by omega) i) ∧
          restricted.series.data.delta i =
              ett.series.data.delta (Fin.castLE (by omega) i) ∧
          restricted.series.data.gamma i =
              ett.series.data.gamma (Fin.castLE (by omega) i) ∧
          TashkinovStoredColors restricted.series.data i =
              TashkinovStoredColors ett.series.data
                (Fin.castLE (by omega) i) ∧
          HEq (restricted.series.certified i)
            (ett.series.certified (Fin.castLE (by omega) i))) := by
-- BODY
  sorry
