import Tablet.AdjacentEdges
import Tablet.BalancedGlobalMaximumTriple
import Tablet.BoundaryEdges
import Tablet.ColoredVertexSetClosed
import Tablet.ColoredVertexSetElementary
import Tablet.Degree
import Tablet.GlobalMaximumTriple
import Tablet.GlobalMaximumTripleExists
import Tablet.Incident
import Tablet.IsOneEdgeUncolored
import Tablet.IsProperEdgeColoring
import Tablet.KTriple
import Tablet.LooplessMultigraph
import Tablet.MaximumDegree
import Tablet.MissingColors
import Tablet.NormalGlobalMaximumTriple
import Tablet.PresentColors
import Tablet.ScheideBalancedExists
import Tablet.ScheideExitNoFree
import Tablet.ScheideExitVertex
import Tablet.ScheideExitVertices
import Tablet.ScheideGlobalMaximumOrder
import Tablet.ScheideGraphHeightOdd
import Tablet.ScheideHeightFiveGammaEdges
import Tablet.ScheideHeightFiveOutsideLinks
import Tablet.ScheideKempePathHeightBound
import Tablet.ScheideLargeHeightElementary
import Tablet.ScheideOrderNineBlockStructure
import Tablet.ScheideOrderNineExitLocalization
import Tablet.ScheideOrderNineParameters
import Tablet.ScheideSmallHeightElementary
import Tablet.ScheideStructuralConfiguration
import Tablet.ScheideTrunkRotationPreserves
import Tablet.TashkinovTree
import Tablet.TreeFreeColors
import Tablet.TreeSequence
import Tablet.TreeSequenceVertexSet
import Tablet.TreeUsedColors
import Tablet.TrunkRotation
import Tablet.TwoColorComponent
import Tablet.TwoColorComponentSwap
import Tablet.TwoColorComponentSwapProper
import Tablet.TwoColorIncidenceDegreeAtMostTwo
import Tablet.TwoColorIncidenceGraph

-- [TABLET NODE: ScheideOrderNineStructuralConfiguration]
theorem ScheideOrderNineStructuralConfiguration {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ)
    (hcritical : Critical G) (hindex : ChromaticIndex G = k + 1)
    (hdegree : MaximumDegree G + 1 ≤ k)
    (hnoisolated : ∀ v : V, ∃ e : E, Incident G v e)
    (hnonelementary : ¬ Elementary G) (horder : TashkinovOrder G < 11) :
    ∃ (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence G e0),
      Nonempty (ScheideStructuralConfiguration G k e0 phi T) := by
-- BODY
  classical
  obtain ⟨e0, phi0, T0, hglobal0⟩ :=
    GlobalMaximumTripleExists G k hcritical hindex hdegree
  obtain ⟨e0, phi, T, N, hbalanced⟩ :=
    ScheideBalancedExists G k e0 phi0 T0 hglobal0
  obtain ⟨horder9, hgraphHeight, hlength0, hheight0⟩ :=
    ScheideOrderNineParameters G k hcritical hindex hdegree hnoisolated
      hnonelementary horder e0 phi T N hbalanced
  obtain ⟨e0, phi, T, N, hbalanced, hlength, hheight, gamma, hgamma,
      hattach, hblockColor, hblockMissing, hbaseAvoids⟩ :=
    ScheideOrderNineBlockStructure G k e0 phi T N hbalanced
      horder9 hgraphHeight
  have hexit := ScheideOrderNineExitLocalization G k e0 phi T N hbalanced
    hlength hheight gamma hgamma hblockColor hblockMissing hbaseAvoids
  refine ⟨e0, phi, T, ?_⟩
  refine ⟨{
    p := 5
    s := 2
    p_ge_two := by omega
    gamma := gamma
    gamma_injective := hgamma
    y := fun i => T.vertex ⟨i.val, by omega⟩
    baseEdge := fun i => T.edge ⟨i.val, by omega⟩
    blockVertex := fun i j => T.vertex ⟨5 + 2 * i.val + j.val, by omega⟩
    blockEdge := fun i j => T.edge ⟨4 + 2 * i.val + j.val, by omega⟩
    length_eq := by omega
    base_vertex_position := by
      intro i
      rfl
    block_vertex_position := by
      intro i j
      rfl
    base_edge_position := by
      intro i
      rfl
    block_edge_position := by
      intro i j
      rfl
    block_attaches_to_base := hattach
    block_color := hblockColor
    block_color_missing_on_base := hblockMissing
    initial_nonfirst_avoids_blocks := hbaseAvoids
    exit_covered := hexit
    no_isolated := hnoisolated
    globally_maximum := N.global }⟩
