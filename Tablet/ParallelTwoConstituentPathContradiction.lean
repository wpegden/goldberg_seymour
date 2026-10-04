import Tablet.ColoredVertexSetClosed
import Tablet.ColoredVertexSetElementary
import Tablet.MissingColors
import Tablet.OrderedTreeUnion
import Tablet.PresentColors
import Tablet.TreeInterchangeable
import Tablet.TreeMissingColors
import Tablet.TwoColorComponent
import Tablet.TwoColorComponentSpanningPath
import Tablet.TwoColorPathComponent

-- [TABLET NODE: ParallelTwoConstituentPathContradiction]
theorem ParallelTwoConstituentPathContradiction {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (sigma : PartialEdgeColoring E k)
    (left right union : TreeSequence G e0)
    (hunion : Nonempty (OrderedTreeUnion left right union))
    (hproper : IsProperEdgeColoring G sigma)
    (hleftElementary : ColoredVertexSetElementary G sigma
      (TreeSequenceVertexSet left))
    (hrightElementary : ColoredVertexSetElementary G sigma
      (TreeSequenceVertexSet right))
    (hrightClosed : ColoredVertexSetClosed G sigma
      (TreeSequenceVertexSet right))
    (support common : V) (gamma delta : Fin k)
    (hsupportLeft : support ∈ TreeSequenceVertexSet left)
    (hsupportRight : support ∈ TreeSequenceVertexSet right)
    (hcommonLeft : common ∈ TreeSequenceVertexSet left)
    (hcommonRight : common ∈ TreeSequenceVertexSet right)
    (hcommonNe : common ≠ support)
    (hdelta : delta ∈ MissingColors G sigma support)
    (hgamma : gamma ∉ TreeMissingColors sigma left)
    (hcommonMissing : (MissingColors G sigma common).Nonempty)
    (hleftInterchangeable : ∀ alpha beta : Fin k,
      alpha ∈ TreeMissingColors sigma left →
      beta ∈ TreeMissingColors sigma left →
      alpha ≠ gamma → alpha ≠ delta →
      beta ≠ gamma → beta ≠ delta →
      TreeInterchangeable G left sigma alpha beta)
    (hrightInterchangeable : ∀ alpha beta : Fin k,
      (alpha ∈ TreeMissingColors sigma right ∨
        beta ∈ TreeMissingColors sigma right) →
      TreeInterchangeable G right sigma alpha beta) :
    ColoredVertexSetElementary G sigma
      (TreeSequenceVertexSet union) := by
-- BODY
  sorry
