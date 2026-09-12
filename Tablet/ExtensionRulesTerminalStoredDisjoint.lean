import Tablet.ETTFirstAppearanceIndex
import Tablet.ColoredVertexSetClosed
import Tablet.ColoredVertexSetElementary
import Tablet.CertifiedETTRestriction
import Tablet.HkuMissingStoredMonotone
import Tablet.HkuParallelBoundaryStructure
import Tablet.InternalEdges
import Tablet.ExtendedTashkinovTree
import Tablet.IsOneEdgeUncolored
import Tablet.IsProperEdgeColoring
import Tablet.MaximumProperty
import Tablet.MaximumDefectiveChoice
import Tablet.MissingColors
import Tablet.ParallelExtensionColor
import Tablet.PresentColors
import Tablet.RevisitingExtensionCertificate
import Tablet.SameColorSeriesPreserved
import Tablet.StableColoring
import Tablet.TashkinovExtensionKind
import Tablet.TashkinovSeries
import Tablet.TashkinovSeriesStep
import Tablet.TashkinovStoredColors
import Tablet.TechnicalTheoremBase
import Tablet.TreeInterchangeable
import Tablet.TreeExit
import Tablet.TreeExitPath
import Tablet.TreeMissingColors
import Tablet.TreeSequence
import Tablet.TreeSequenceInitialSegment
import Tablet.TreeSequenceVertexSet
import Tablet.TwoColorComponent
import Tablet.TwoColorComponentSwap
import Tablet.TwoColorComponentsDisjoint
import Tablet.TwoColorIncidenceDegreeAtMostTwo
import Tablet.TwoColorIncidenceGraph
import Tablet.sc1

-- [TABLET NODE: ExtensionRulesTerminalStoredDisjoint]
theorem ExtensionRulesTerminalStoredDisjoint {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (generating : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T generating)
    (hMP : MaximumProperty ett) (hpositive : 0 < ett.rounds)
    (hLowerOne : ∀ {T' : TreeSequence G e0}
      {generating' : PartialEdgeColoring E k}
      (lower : ExtendedTashkinovTree G k e0 input T' generating'),
      0 < lower.rounds → lower.rounds < ett.rounds → MaximumProperty lower →
      ColoredVertexSetElementary G generating'
        (TreeSequenceVertexSet T'))
    (hLowerTwo : ∀ {T' : TreeSequence G e0}
      {generating' : PartialEdgeColoring E k}
      (lower : ExtendedTashkinovTree G k e0 input T' generating'),
      0 < lower.rounds → lower.rounds < ett.rounds → MaximumProperty lower →
      (let n : Fin (lower.rounds + 1) := Fin.last lower.rounds
       let Tnext : TreeSequence G e0 :=
         lower.series.data.tree (Fin.last (lower.rounds + 1))
       ∀ sigma : PartialEdgeColoring E k,
         IsProperEdgeColoring G sigma → IsOneEdgeUncolored sigma e0 →
         StableColoring Tnext
           (TashkinovStoredColors lower.series.data n)
           (lower.series.data.coloring n) sigma →
         ∀ alpha beta : Fin k,
           (alpha ∈ TreeMissingColors sigma Tnext ∨
             beta ∈ TreeMissingColors sigma Tnext) →
           TreeInterchangeable G Tnext sigma alpha beta))
    (r : Fin ett.rounds) (vn vr : V)
    (hrEarlier : r.succ ≠ Fin.last ett.rounds)
    (hvnvr : vn ≠ vr)
    (hkindn : ett.series.data.kind (Fin.last ett.rounds) =
      some TashkinovExtensionKind.PE)
    (hkindr : ett.series.data.kind r.succ = some TashkinovExtensionKind.PE)
    (hvertexn : ett.series.data.chosenVertex (Fin.last ett.rounds) = some vn)
    (hvertexr : ett.series.data.chosenVertex r.succ = some vr)
    (hvn : vn ∈ TreeSequenceVertexSet T) (hvr : vr ∈ TreeSequenceVertexSet T)
    (hfirst : ETTFirstAppearanceIndex ett vn hvn =
      ETTFirstAppearanceIndex ett vr hvr) :
    Disjoint (ett.series.data.stored (Fin.last ett.rounds))
      (ett.series.data.stored r.succ) := by
-- BODY
  sorry
