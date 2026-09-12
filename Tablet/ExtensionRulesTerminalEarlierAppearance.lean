import Tablet.BoundaryColorVertex
import Tablet.BoundaryColorEdges
import Tablet.BoundaryEdges
import Tablet.CertifiedETTRestriction
import Tablet.DefectiveEdge
import Tablet.DefectiveVertex
import Tablet.DefectiveColor
import Tablet.ETTFirstAppearanceIndex
import Tablet.ExtendedTashkinovTree
import Tablet.HkuMissingStoredMonotone
import Tablet.HkuUnsupportedVertexColors
import Tablet.IsOneEdgeUncolored
import Tablet.IsProperEdgeColoring
import Tablet.MaximumProperty
import Tablet.MaximumDefectiveChoice
import Tablet.SameColorSeriesPreserved
import Tablet.StableColoring
import Tablet.StableColoringBeforeVertex
import Tablet.TashkinovExtensionKind
import Tablet.TashkinovSeries
import Tablet.TashkinovSeriesStep
import Tablet.TashkinovStoredColors
import Tablet.TreeSequence
import Tablet.TreeIncidentEdge
import Tablet.TreeMissingColors
import Tablet.TreeSequenceInitialSegment
import Tablet.TreeSequenceVertexSet
import Tablet.TreeVertexOrder
import Tablet.TreeVerticesBefore
import Tablet.sc2

-- [TABLET NODE: ExtensionRulesTerminalEarlierAppearance]
theorem ExtensionRulesTerminalEarlierAppearance {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (generating : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T generating)
    (hMP : MaximumProperty ett) (hpositive : 0 < ett.rounds)
    (hLowerFive : ∀ {T' : TreeSequence G e0}
      {generating' : PartialEdgeColoring E k}
      (lower : ExtendedTashkinovTree G k e0 input T' generating'),
      0 < lower.rounds → lower.rounds < ett.rounds → MaximumProperty lower →
      (let n : Fin (lower.rounds + 1) := Fin.last lower.rounds
       let Tn : TreeSequence G e0 := lower.series.data.tree n.castSucc
       ∀ sigma : PartialEdgeColoring E k,
         IsProperEdgeColoring G sigma → IsOneEdgeUncolored sigma e0 →
         StableColoring Tn (TashkinovStoredColors lower.series.data n)
           (lower.series.data.coloring n) sigma →
         ∀ (delta : Fin k),
           DefectiveColor G sigma (TreeSequenceVertexSet Tn) delta →
           ∀ (v : V),
             BoundaryColorVertex G sigma (TreeSequenceVertexSet Tn) delta v →
             (∃ w, BoundaryColorVertex G sigma
                 (TreeSequenceVertexSet Tn) delta w ∧
               TreeVertexOrder Tn w v) →
             ∀ (hvFinal : v ∈ TreeSequenceVertexSet T')
               (q : Fin lower.rounds) (vi : V),
               (lower.series.data.kind q.succ =
                    some TashkinovExtensionKind.PE ∨
                  lower.series.data.kind q.succ =
                    some TashkinovExtensionKind.SE) →
               lower.series.data.chosenVertex q.succ = some vi →
               ETTFirstAppearanceIndex lower v hvFinal ≤ q.val + 1 →
               v = vi ∨ TreeVertexOrder T' v vi))
    (v : V)
    (hkind : ett.series.data.kind (Fin.last ett.rounds) =
      some TashkinovExtensionKind.PE)
    (hvertex : ett.series.data.chosenVertex (Fin.last ett.rounds) = some v)
    (hvFinal : v ∈ TreeSequenceVertexSet T)
    (j : Fin (ett.rounds + 1))
    (hfirst : ETTFirstAppearanceIndex ett v hvFinal = j.val + 1)
    (hj : j.val + 1 < ett.rounds)
    (sigma : PartialEdgeColoring E k)
    (hproper : IsProperEdgeColoring G sigma)
    (hone : IsOneEdgeUncolored sigma e0)
    (hstable : StableColoring
      (ett.series.data.tree (Fin.last ett.rounds).castSucc)
      (TashkinovStoredColors ett.series.data (Fin.last ett.rounds))
      (ett.series.data.coloring (Fin.last ett.rounds)) sigma) :
    StableColoringBeforeVertex T v hvFinal
        (TashkinovStoredColors ett.series.data j)
        (ett.series.data.coloring j) sigma ∧
      (0 < j.val →
        StableColoring (ett.series.data.tree j.castSucc)
          (TashkinovStoredColors ett.series.data j)
          (ett.series.data.coloring j) sigma) := by
-- BODY
  sorry
