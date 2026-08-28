import Tablet.ColoredVertexSetElementary
import Tablet.IsOneEdgeUncolored
import Tablet.IsProperEdgeColoring
import Tablet.StableColoring
import Tablet.TashkinovSeries
import Tablet.TashkinovStoredColors
import Tablet.TreeInterchangeable
import Tablet.TreeMissingColors
import Tablet.TreeSequenceVertexSet

-- [TABLET NODE: TechnicalTheoremBaseClaims]
structure TechnicalTheoremBaseClaims {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq E] {G : LooplessMultigraph V E} {k rounds : ℕ} {e0 : E}
    {input : PartialEdgeColoring E k}
    (series : TashkinovSeries G k rounds e0 input) : Prop where
-- BODY
  initialElementary :
    ColoredVertexSetElementary G (series.data.coloring 0)
      (TreeSequenceVertexSet (series.data.tree ⟨1, by omega⟩))
  initialInterchangeability :
    let i0 : Fin (rounds + 1) := 0
    let T1 : TreeSequence G e0 := series.data.tree ⟨1, by omega⟩
    ∀ sigma : PartialEdgeColoring E k,
      IsProperEdgeColoring G sigma → IsOneEdgeUncolored sigma e0 →
      StableColoring T1 (TashkinovStoredColors series.data i0)
        (series.data.coloring i0) sigma →
      ∀ alpha beta : Fin k,
        (alpha ∈ TreeMissingColors sigma T1 ∨
          beta ∈ TreeMissingColors sigma T1) →
        TreeInterchangeable G T1 sigma alpha beta
