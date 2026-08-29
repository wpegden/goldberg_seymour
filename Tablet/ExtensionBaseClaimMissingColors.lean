import Tablet.DefectiveVertex
import Tablet.ETTFirstAppearanceIndex
import Tablet.ExtendedTashkinovLadderStage
import Tablet.ExtendedTashkinovTree
import Tablet.ExtensionBaseActiveIndices
import Tablet.ExtensionBaseSupportClass
import Tablet.HkuUnsupportedVertexColors
import Tablet.MaximumDefectiveChoice
import Tablet.StableColoring
import Tablet.SupportingPEMissingTransport
import Tablet.SupportingPEStoredIntersection
import Tablet.TashkinovSeries
import Tablet.TashkinovSeriesStep
import Tablet.TreeSequenceInitialSegment
import Tablet.TreeSequenceVertexSet

-- [TABLET NODE: ExtensionBaseClaimMissingColors]
theorem ExtensionBaseClaimMissingColors {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    {input : PartialEdgeColoring E k} {T : TreeSequence G e0}
    {generating : PartialEdgeColoring E k}
    (ett : ExtendedTashkinovTree G k e0 input T generating)
    (terminalSupport : V)
    (hterminalSupport : terminalSupport ∈ TreeSequenceVertexSet T)
    (jSlot q : Fin ett.rounds) (hjle : jSlot.val ≤ q.val)
    (hqTerminal : q.val + 1 = ett.rounds)
    (hqKind : ett.series.data.kind q.succ =
      some TashkinovExtensionKind.PE)
    (hqVertex : ett.series.data.chosenVertex q.succ = some terminalSupport)
    (hjSlot : jSlot.val + 1 =
      ETTFirstAppearanceIndex ett terminalSupport hterminalSupport)
    (w : V)
    (hw : w ∈ TreeSequenceVertexSet
      (ett.series.data.tree q.succ.castSucc))
    (p : ℕ) (indices : Fin (p + 1) → Fin ett.rounds)
    (hincreasing : ∀ a b, a.val < b.val →
      (indices a).val < (indices b).val)
    (hclass : ∀ r : Fin ett.rounds,
      r ∈ ExtensionBaseSupportClass ett terminalSupport hterminalSupport w ↔
        ∃ a : Fin (p + 1), indices a = r)
    (henumerates : ∀ r : Fin ett.rounds,
      (r.val ≤ q.val ∧
        ett.series.data.kind r.succ = some TashkinovExtensionKind.PE ∧
        ett.series.data.chosenVertex r.succ = some w) ↔
      ∃ a : Fin (p + 1), indices a = r)
    (gammaFirst deltaLast : Fin k)
    (hgammaFirst : ett.series.data.gamma (indices 0).succ = some gammaFirst)
    (hdeltaLast : ett.series.data.delta
      (indices (Fin.last p)).succ = some deltaLast)
    (sigma : PartialEdgeColoring E k)
    (hsigmaProper : IsProperEdgeColoring G sigma)
    (hsigmaOne : IsOneEdgeUncolored sigma e0)
    (hsigmaStable : StableColoring
      (ett.series.data.tree q.succ.castSucc)
      (TashkinovStoredColors ett.series.data q.succ)
      (ett.series.data.coloring q.succ) sigma) :
    (∀ v : V,
      v ∈ TreeSequenceVertexSet
          (ett.series.data.tree jSlot.succ.castSucc) →
      (∀ r : Fin ett.rounds,
        r ∈ ExtensionBaseActiveIndices ett terminalSupport hterminalSupport →
        ett.series.data.chosenVertex r.succ ≠ some v) →
      MissingColors G sigma v =
        MissingColors G (ett.series.data.coloring jSlot.castSucc) v) ∧
    (let storedPairs := Finset.univ.biUnion fun a : Fin (p + 1) =>
      ett.series.data.stored (indices a).succ
     MissingColors G sigma w ∩ storedPairs = {deltaLast} ∧
       MissingColors G (ett.series.data.coloring jSlot.castSucc) w =
         (MissingColors G sigma w \ {deltaLast}) ∪ {gammaFirst}) := by
-- BODY
  sorry
