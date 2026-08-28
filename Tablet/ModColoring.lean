import Tablet.CorrespondingExtendedTashkinovTree
import Tablet.TashkinovAugmentationSequence
import Tablet.TreeSequenceAdjoinEdge
import Tablet.TreeSequenceInitialSegment

-- [TABLET NODE: ModColoring]
def ModColoring {V E : Type*} [Fintype V] [Fintype E] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    {input : PartialEdgeColoring E k} {T : TreeSequence G e0}
    {generating : PartialEdgeColoring E k}
    (base : ExtendedTashkinovTree G k e0 input T generating)
    (sigmaN : PartialEdgeColoring E k) : Prop :=
-- BODY
  let n : Fin (base.rounds + 1) := Fin.last base.rounds
  let Tn : TreeSequence G e0 := base.series.data.tree n.castSucc
  IsProperEdgeColoring G sigmaN ∧ IsOneEdgeUncolored sigmaN e0 ∧
    ∀ Tstar : TreeSequence G e0,
      TreeSequenceInitialSegment Tn Tstar →
      Tn.length < Tstar.length →
      ((base.series.data.kind n = some TashkinovExtensionKind.PE ∧
          TashkinovAugmentationSequence sigmaN Tn Tstar) ∨
        ((base.series.data.kind n = some TashkinovExtensionKind.SE ∨
            base.series.data.kind n = some TashkinovExtensionKind.RE) ∧
          ∃ (f : E) (seed : TreeSequence G e0),
            base.series.data.connectingEdges n = {f} ∧
              TreeSequenceAdjoinEdge Tn f seed ∧
              TashkinovAugmentationSequence sigmaN seed Tstar)) →
      Nonempty (CorrespondingExtendedTashkinovTree G k e0 base sigmaN Tstar)
