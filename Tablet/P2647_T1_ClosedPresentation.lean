import Tablet.CorrespondingExtendedTashkinovTree
import Tablet.ExtendedTashkinovTree
import Tablet.MaximumPropertyTransport
import Tablet.ModColoring
import Tablet.RutgersClosedPresentation
import Tablet.TashkinovClosure
import Tablet.TreeSequenceAdjoinEdge

-- [TABLET NODE: P2647_T1_ClosedPresentation]
theorem P2647_T1_ClosedPresentation
    {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : Nat) (e0 : E)
    {input : PartialEdgeColoring E k} {T : TreeSequence G e0}
    {generating : PartialEdgeColoring E k}
    (original : ExtendedTashkinovTree G k e0 input T generating)
    (hMP : MaximumProperty original)
    (sigma : PartialEdgeColoring E k) (F : TreeSequence G e0)
    (hmod : ModColoring original sigma)
    (hsegment : TreeSequenceInitialSegment
      (original.series.data.tree (Fin.last original.rounds).castSucc) F)
    (hstrict : (original.series.data.tree
      (Fin.last original.rounds).castSucc).length < F.length)
    (hroute :
      (original.series.data.kind (Fin.last original.rounds) =
          some TashkinovExtensionKind.PE ∧
        TashkinovClosure sigma
          (original.series.data.tree (Fin.last original.rounds).castSucc) F) ∨
      ((original.series.data.kind (Fin.last original.rounds) =
            some TashkinovExtensionKind.SE ∨
          original.series.data.kind (Fin.last original.rounds) =
            some TashkinovExtensionKind.RE) ∧
        ∃ (f : E) (seed : TreeSequence G e0),
          original.series.data.connectingEdges (Fin.last original.rounds) = {f} ∧
            TreeSequenceAdjoinEdge
              (original.series.data.tree (Fin.last original.rounds).castSucc) f seed ∧
            TashkinovClosure sigma seed F)) :
    ∃ presentation : RutgersClosedPresentation G k e0 original,
      presentation.sigma = sigma ∧ presentation.U = F := by
-- BODY
  classical
  have eligible :
      (original.series.data.kind (Fin.last original.rounds) =
          some TashkinovExtensionKind.PE ∧
        TashkinovAugmentationSequence sigma
          (original.series.data.tree (Fin.last original.rounds).castSucc) F) ∨
      ((original.series.data.kind (Fin.last original.rounds) =
            some TashkinovExtensionKind.SE ∨
          original.series.data.kind (Fin.last original.rounds) =
            some TashkinovExtensionKind.RE) ∧
        ∃ (f : E) (seed : TreeSequence G e0),
          original.series.data.connectingEdges (Fin.last original.rounds) = {f} ∧
            TreeSequenceAdjoinEdge
              (original.series.data.tree (Fin.last original.rounds).castSucc) f seed ∧
            TashkinovAugmentationSequence sigma seed F) := by
    rcases hroute with ⟨hkind, hclosure⟩ | ⟨hkind, f, seed, hedge, hadjoin, hclosure⟩
    · exact Or.inl ⟨hkind, hclosure.1⟩
    · exact Or.inr ⟨hkind, f, seed, hedge, hadjoin, hclosure.1⟩
  obtain ⟨corr⟩ := hmod.2.2 F hsegment hstrict eligible
  have hmaximum := MaximumPropertyTransport G k e0 original sigma hmod F corr hMP
  have replacementRoute :
      let replacement := corr.replacementETT
      let n := Fin.last replacement.rounds
      let Tn := replacement.series.data.tree n.castSucc
      (replacement.series.data.kind n = some TashkinovExtensionKind.PE ∧
          TashkinovClosure sigma Tn F) ∨
        ((replacement.series.data.kind n = some TashkinovExtensionKind.SE ∨
            replacement.series.data.kind n = some TashkinovExtensionKind.RE) ∧
          ∃ (f : E) (seed : TreeSequence G e0),
            replacement.series.data.connectingEdges n = {f} ∧
              TreeSequenceAdjoinEdge Tn f seed ∧
              TashkinovClosure sigma seed F) := by
    rcases corr with ⟨replacementInput, replacementSeries, replacementETT,
      rungAgreement, seriesPresentation, finalGeneratingColoring,
      ladderTreesAgree, storedColorsAgree, connectingEdgesAgree,
      extensionKindsAgree, replacementProper, replacementOneUncolored,
      replacementStable⟩
    cases replacementETT with
    | mk rounds roundsPositive replacementData above strict below generating =>
      cases rungAgreement
      have seriesSame : replacementData = replacementSeries := eq_of_heq seriesPresentation
      cases seriesSame
      let q : Fin original.rounds := ⟨original.rounds - 1, by
        have := original.roundsPositive
        omega⟩
      have hq : q.succ = Fin.last original.rounds := by
        apply Fin.ext
        dsimp [q]
        have := original.roundsPositive
        omega
      have ladderEq : replacementSeries.data.tree
          (Fin.last original.rounds).castSucc =
          original.series.data.tree (Fin.last original.rounds).castSucc := by
        rw [← hq]
        exact ladderTreesAgree q
      dsimp
      simpa only [ladderEq, extensionKindsAgree, connectingEdgesAgree] using hroute
  exact ⟨⟨sigma, F, corr, hmaximum, replacementRoute⟩, rfl, rfl⟩
