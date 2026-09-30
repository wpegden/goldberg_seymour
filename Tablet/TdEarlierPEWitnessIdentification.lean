import Tablet.MaximumDefectiveChoice
import Tablet.MissingColors

-- [TABLET NODE: TdEarlierPEWitnessIdentification]
theorem TdEarlierPEWitnessIdentification {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (T : TreeSequence G e0) (C Cstar : Finset (Fin k))
    (phi phiStar : PartialEdgeColoring E k)
    (choice : MaximumDefectiveChoice G e0 T C phi)
    (choiceStar : MaximumDefectiveChoice G e0 T Cstar phiStar)
    (gamma gammaStar : Fin k)
    (post postStar : PartialEdgeColoring E k)
    (hedges : ({choice.edge} : Finset E) = {choiceStar.edge})
    (hpairs : ({choice.color, gamma} : Finset (Fin k)) =
      {choiceStar.color, gammaStar})
    (hmissing : MissingColors G post choice.vertex =
      MissingColors G postStar choiceStar.vertex)
    (hdelta : choice.color ∈ MissingColors G post choice.vertex)
    (hgamma : gamma ∉ MissingColors G post choice.vertex)
    (hdeltaStar : choiceStar.color ∈
      MissingColors G postStar choiceStar.vertex)
    (hgammaStar : gammaStar ∉
      MissingColors G postStar choiceStar.vertex) :
    choiceStar.edge = choice.edge ∧
      choiceStar.vertex = choice.vertex ∧
      choiceStar.otherEndpoint = choice.otherEndpoint ∧
      choiceStar.color = choice.color ∧ gammaStar = gamma := by
-- BODY
  sorry

