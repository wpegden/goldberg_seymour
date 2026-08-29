import Tablet.BoundaryColorEdges
import Tablet.BoundaryEdges
import Tablet.Incident
import Tablet.LooplessMultigraph
import Tablet.TreeSequenceVertexSet
import Tablet.TwoColorComponent
import Tablet.TwoColorIncidenceGraph

-- [TABLET NODE: ExtensionBaseCaseTwoObservation21]
theorem ExtensionBaseCaseTwoObservation21 {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    (Tn TjPrime : TreeSequence G e0)
    (rho1 : PartialEdgeColoring E k) (gammaN deltaN : Fin k)
    (fN : E) (terminalSupport x : V)
    (p : (TwoColorIncidenceGraph G rho1 gammaN deltaN).Walk
      (Sum.inl terminalSupport) (Sum.inl x))
    (hpath : p.IsPath)
    (hcomponent : {y : Sum V E | y ∈ p.support} =
      TwoColorComponent G rho1 gammaN deltaN (Sum.inl terminalSupport))
    (hterminalN : terminalSupport ∈ TreeSequenceVertexSet Tn)
    (hterminalPrime : terminalSupport ∈ TreeSequenceVertexSet TjPrime)
    (hxOutside : x ∉
      TreeSequenceVertexSet Tn ∪ TreeSequenceVertexSet TjPrime)
    (htwoN : ∃ w ∈ TreeSequenceVertexSet Tn,
      w ≠ terminalSupport ∧ Sum.inl w ∈ p.support)
    (hgammaBoundary : BoundaryColorEdges G rho1
      (TreeSequenceVertexSet Tn) gammaN = {fN})
    (hdeltaBoundary : BoundaryColorEdges G rho1
      (TreeSequenceVertexSet Tn ∪ TreeSequenceVertexSet TjPrime) deltaN = ∅)
    (hfNterminal : Incident G terminalSupport fN) :
    ∃ (u : V)
      (exitPath : (TwoColorIncidenceGraph G rho1 gammaN deltaN).Walk
        (Sum.inl x) (Sum.inl u)),
      u ∈ TreeSequenceVertexSet TjPrime \ TreeSequenceVertexSet Tn ∧
        exitPath.IsPath ∧ 2 ≤ exitPath.length ∧
        (∀ y : Sum V E, y ∈ exitPath.support → y ∈ p.support) ∧
        (∀ w : V,
          w ∈ TreeSequenceVertexSet Tn ∪ TreeSequenceVertexSet TjPrime →
          (Sum.inl w ∈ exitPath.support ↔ w = u)) ∧
        (∃ g ∈ BoundaryColorEdges G rho1
            (TreeSequenceVertexSet Tn ∪ TreeSequenceVertexSet TjPrime) gammaN,
          Incident G u g ∧ Sum.inr g ∈ exitPath.support) ∧
        ¬ Incident G u fN := by
-- BODY
  sorry
