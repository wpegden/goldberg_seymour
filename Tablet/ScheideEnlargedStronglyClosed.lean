import Tablet.AdjacentEdges
import Tablet.BoundaryEdges
import Tablet.ColoredVertexSetClosed
import Tablet.ColoredVertexSetStronglyClosed
import Tablet.DefectiveColors
import Tablet.GlobalMaximumTriple
import Tablet.Incident
import Tablet.InternalEdges
import Tablet.IsOneEdgeUncolored
import Tablet.IsProperEdgeColoring
import Tablet.KTriple
import Tablet.LooplessMultigraph
import Tablet.MissingColors
import Tablet.PresentColors
import Tablet.ScheideDefectiveChainPath
import Tablet.ScheideDefectiveSetup
import Tablet.ScheideDefectiveSwitchEffect
import Tablet.ScheideEnlargedClosed
import Tablet.ScheideEnlargedStrictAugmentation
import Tablet.ScheideEnlargedSwitchTransport
import Tablet.ScheideEnlargedVertexSet
import Tablet.ScheideExitVertex
import Tablet.ScheideExitVertices
import Tablet.ScheideGlobalMaximumOrder
import Tablet.ScheideReducedConfiguration
import Tablet.ScheideReplacementData
import Tablet.ScheideReplacementMaximum
import Tablet.ScheideReplacementPairsLaminar
import Tablet.ScheideReplacementUnionClosed
import Tablet.ScheideSingleBoundaryCrossing
import Tablet.ScheideStructuralConfiguration
import Tablet.ScheideStructuralExitsInBase
import Tablet.ScheideSymmetricDefectiveInternal
import Tablet.TashkinovOrder
import Tablet.TashkinovTree
import Tablet.TreeSequence
import Tablet.TreeSequenceVertexSet
import Tablet.TwoColorComponent
import Tablet.TwoColorComponentSwap
import Tablet.TwoColorComponentSwapProper
import Tablet.TwoColorIncidenceGraph

-- [TABLET NODE: ScheideEnlargedStronglyClosed]
theorem ScheideEnlargedStronglyClosed {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (C : ScheideReducedConfiguration G k e0 phi T)
    (D : ScheideDefectiveSetup G k e0 phi T C)
    (R : ∀ d : {delta // delta ∈ DefectiveColors G phi
      (TreeSequenceVertexSet T)}, ScheideReplacementData G k e0 phi T C D d) :
    ColoredVertexSetStronglyClosed G phi (ScheideEnlargedVertexSet R) := by
-- BODY
  classical
  by_contra hnot
  have htransport := ScheideEnlargedSwitchTransport G k e0 phi T C D R hnot
  obtain ⟨psi, S, htriple, htree, hcard⟩ :=
    ScheideEnlargedStrictAugmentation G k e0 phi T C D R htransport
  have hchi : ChromaticIndex G = k + 1 := htriple.2.1
  have hk : ChromaticIndex G - 1 = k := by omega
  have hmem : (TreeSequenceVertexSet S).card ∈
      (Finset.range (Fintype.card V + 1)).filter (fun n =>
        ∃ (e : E) (p : PartialEdgeColoring E (ChromaticIndex G - 1))
          (U : TreeSequence G e),
          KTriple G (ChromaticIndex G - 1) e p ∧
            TashkinovTree G e p U ∧
              (TreeSequenceVertexSet U).card = n) := by
    rw [hk]
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · have hle : (TreeSequenceVertexSet S).card ≤ Fintype.card V :=
        Finset.card_le_card (Finset.subset_univ _)
      omega
    · exact ⟨e0, psi, S, htriple, htree, rfl⟩
  have hle : (TreeSequenceVertexSet S).card ≤ TashkinovOrder G := by
    unfold TashkinovOrder
    dsimp
    exact Finset.le_max' _ _ (Finset.mem_insert_of_mem hmem)
  omega
