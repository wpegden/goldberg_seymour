import Tablet.ColoredVertexSetClosed
import Tablet.ColoredVertexSetElementary
import Tablet.IsOneEdgeUncolored
import Tablet.IsProperEdgeColoring
import Tablet.KTriple
import Tablet.StableColoring
import Tablet.TashkinovAugmentation
import Tablet.TashkinovAugmentationSequence
import Tablet.TashkinovAugmentationSequencePreservesTashkinovTree
import Tablet.TashkinovClosure
import Tablet.TashkinovSeries
import Tablet.TashkinovSeriesStep
import Tablet.TashkinovStoredColors
import Tablet.TashkinovTree
import Tablet.TreeIncidentEdge
import Tablet.TreeInterchangeable
import Tablet.TreeMissingColors
import Tablet.TreeSequenceInitialSegment
import Tablet.TreeSequenceVertexSet
import Tablet.TashTree
import Tablet.Tchange
import Tablet.sc1

-- [TABLET NODE: TechnicalTheoremBase]
theorem TechnicalTheoremBase {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] (G : LooplessMultigraph V E)
    (k rounds : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
    (series : TashkinovSeries G k rounds e0 input) :
    ColoredVertexSetElementary G (series.data.coloring 0)
        (TreeSequenceVertexSet (series.data.tree ⟨1, by omega⟩)) ∧
      (let i0 : Fin (rounds + 1) := 0
       let T1 : TreeSequence G e0 := series.data.tree ⟨1, by omega⟩
       ∀ sigma : PartialEdgeColoring E k,
         IsProperEdgeColoring G sigma → IsOneEdgeUncolored sigma e0 →
         StableColoring T1 (TashkinovStoredColors series.data i0)
           (series.data.coloring i0) sigma →
         ∀ alpha beta : Fin k,
           (alpha ∈ TreeMissingColors sigma T1 ∨
             beta ∈ TreeMissingColors sigma T1) →
           TreeInterchangeable G T1 sigma alpha beta) := by
-- BODY
  sorry
