import Tablet.P2634_T1_PETerminalFacts
import Tablet.ColoredVertexSetElementary
import Tablet.ExtendedTashkinovTree
import Tablet.TashkinovClosure
import Tablet.TashkinovClosureVertexSetUnique
import Tablet.TreeSequenceInitialSegmentVertexSetSubset

-- [TABLET NODE: P2634_T1_ClosedCoreElementary]
theorem P2634_T1_ClosedCoreElementary
    {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : Nat} {e0 : E}
    {input : PartialEdgeColoring E k} {T : TreeSequence G e0}
    {phi : PartialEdgeColoring E k}
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (hPE : ett.series.data.kind (Fin.last ett.rounds) =
      some TashkinovExtensionKind.PE)
    (core : TreeSequence G e0)
    (hroute : TashkinovAugmentationSequence phi
      (ett.series.data.tree (Fin.last ett.rounds).castSucc) core)
    (helem : ColoredVertexSetElementary G phi (TreeSequenceVertexSet core))
    (hclosed : ColoredVertexSetClosed G phi (TreeSequenceVertexSet core)) :
    ColoredVertexSetElementary G phi (TreeSequenceVertexSet T) := by
-- BODY
  have hfinal := (P2634_T1_PETerminalFacts ett hPE).2.2
  have hvertices := TashkinovClosureVertexSetUnique phi
    (ett.series.data.tree (Fin.last ett.rounds).castSucc) core
    (ett.series.data.tree (Fin.last (ett.rounds + 1)))
    ⟨hroute, hclosed⟩ hfinal
  have hsubset := TreeSequenceInitialSegmentVertexSetSubset ett.belowFinal
  rw [← hvertices] at hsubset
  intro u hu v hv hne
  exact helem (hsubset hu) (hsubset hv) hne
