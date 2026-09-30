import Tablet.ClosedColorExitPathBoundaryEdge
import Tablet.CorrespondingExtendedTashkinovTree
import Tablet.ElementaryClosedExitPairExtendsTriple
import Tablet.Step1ExitLegMinimum
import Tablet.Step1ExitLegPresentation
import Tablet.TreeExitPath
import Tablet.TreeSequence
import Tablet.TreeSequenceVertexSet
import Tablet.TreeVertexOrder

-- [TABLET NODE: Step1ExitLegMinimumExists]
theorem Step1ExitLegMinimumExists {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (n q : ℕ)
    (hfamily : Nonempty (Step1ExitLegPresentation G k e0 n q))
    (helementary : ∀ P : Step1ExitLegPresentation G k e0 n q,
      ColoredVertexSetElementary G P.phi (TreeSequenceVertexSet P.T)) :
    Nonempty (Step1ExitLegMinimum G k e0 n q) := by
-- BODY
  sorry
