import Tablet.BalancedGlobalMaximumTriple
import Tablet.AdjacentEdges
import Tablet.BoundaryEdges
import Tablet.ColoredVertexSetElementary
import Tablet.FixedPairMaximalTashkinovTree
import Tablet.GlobalMaximumTriple
import Tablet.Incident
import Tablet.IsProperEdgeColoring
import Tablet.KTriple
import Tablet.LooplessMultigraph
import Tablet.MissingColors
import Tablet.NormalGlobalMaximumTriple
import Tablet.NormalTripleTrunk
import Tablet.PresentColors
import Tablet.ScheideGlobalMaximumOrder
import Tablet.ScheideGraphHeightOdd
import Tablet.ScheideBalancedCandidateMaximumExists
import Tablet.ScheideBalancedCandidateMaximumOrder
import Tablet.ScheideBalancedCandidateNormalTransport
import Tablet.ScheideGlobalMaximumFixedPairMaximal
import Tablet.ScheideMaximalContainsEveryTree
import Tablet.TashTree
import Tablet.TashkinovOrder
import Tablet.TashkinovTree
import Tablet.TreeSequence
import Tablet.TreeSequenceVertexSet
import Tablet.TreeUsedColors

-- [TABLET NODE: ScheideBalancedFromMaxNormal]
theorem ScheideBalancedFromMaxNormal {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (N : NormalGlobalMaximumTriple G k e0 phi T)
    (hheight : N.height = ScheideGraphHeight G) :
    ∃ (T' : TreeSequence G e0)
      (N' : NormalGlobalMaximumTriple G k e0 phi T'),
      BalancedGlobalMaximumTriple N' ∧
        TreeSequenceVertexSet T' = TreeSequenceVertexSet T ∧
        TreeUsedColors phi T' ⊆ TreeUsedColors phi T := by
-- BODY
  classical
  obtain ⟨S, hS, hmax⟩ :=
    ScheideBalancedCandidateMaximumExists G k e0 phi T N hheight
  have horder : (TreeSequenceVertexSet S).card = TashkinovOrder G :=
    ScheideBalancedCandidateMaximumOrder G k e0 phi T S N hS hmax
  have hfixed : FixedPairMaximalTashkinovTree G e0 phi T :=
    ScheideGlobalMaximumFixedPairMaximal G k e0 phi T N.global
  have hsubset : TreeSequenceVertexSet S ⊆ TreeSequenceVertexSet T :=
    ScheideMaximalContainsEveryTree G k e0 phi T S N.global.1 hfixed
      hS.tashkinov
  have hcard : (TreeSequenceVertexSet T).card ≤
      (TreeSequenceVertexSet S).card := by
    rw [N.global.2.2, horder]
  have hvertices : TreeSequenceVertexSet S = TreeSequenceVertexSet T :=
    Finset.eq_of_subset_of_card_le hsubset hcard
  obtain ⟨N', hN'⟩ :=
    ScheideBalancedCandidateNormalTransport G k e0 phi T S N hS hvertices
  refine ⟨S, N', ?_, hvertices, hS.usedColors⟩
  constructor
  · exact hN'.trans hheight
  · intro j hlow hupp
    exact hS.paired j (by simpa [hN'] using hlow) hupp
