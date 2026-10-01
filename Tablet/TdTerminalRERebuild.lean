import Tablet.Basic2
import Tablet.TdEarlierPEWitnessIdentification
import Tablet.TdReplacementPrefixExact
import Tablet.BoundaryEdges
import Tablet.CertifiedETTRestriction
import Tablet.ColoredVertexSetClosed
import Tablet.ColoredVertexSetStronglyClosed
import Tablet.CorrespondingExtendedTashkinovTree
import Tablet.DefectiveColor
import Tablet.DefectiveEdge
import Tablet.DefectiveVertex
import Tablet.ExtendedTashkinovTree
import Tablet.ExtensionBase
import Tablet.ExtensionRules
import Tablet.HkuMissingStoredMonotone
import Tablet.HkuTreeColorsControlled
import Tablet.IsProperEdgeColoring
import Tablet.KTriple
import Tablet.MaximumDefectiveChoice
import Tablet.MaximumProperty
import Tablet.MaximumPropertyTransport
import Tablet.MissingColors
import Tablet.ModColoring
import Tablet.ParallelExtensionColor
import Tablet.ParallelExtensionUndoStable
import Tablet.PresentColors
import Tablet.RevisitingExtensionCertificate
import Tablet.StableColoring
import Tablet.TashkinovAugmentation
import Tablet.TashkinovAugmentationSequence
import Tablet.TashkinovClosure
import Tablet.TashkinovClosureExists
import Tablet.TashkinovSeries
import Tablet.TashkinovSeriesAppend
import Tablet.TashkinovSeriesStep
import Tablet.TashkinovStoredColors
import Tablet.TechnicalTheoremBase
import Tablet.TreeExit
import Tablet.TreeExitPath
import Tablet.TreeIncidentEdge
import Tablet.TreeInterchangeable
import Tablet.TreeMissingColors
import Tablet.TreeSequenceAdjoinEdge
import Tablet.TreeSequenceInitialSegment
import Tablet.TwoColorComponent
import Tablet.TwoColorComponentSpanningPath
import Tablet.TwoColorComponentSwap
import Tablet.TwoColorCycle
import Tablet.TwoColorIncidenceDegreeAtMostTwo
import Tablet.TwoColorPathComponent
import Tablet.TwoColorNontrivialPathComponent
import Tablet.sc1
import Tablet.sc2

set_option maxHeartbeats 1800000

-- [TABLET NODE: TdTerminalRERebuild]
theorem TdTerminalRERebuild {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] (G : LooplessMultigraph V E)
    (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
    (T : TreeSequence G e0) (generating : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T generating)
    (hMP : MaximumProperty ett)
    (hpositive : 0 < ett.rounds)
    (hlower : ∀ {input' : PartialEdgeColoring E k}
      {T' : TreeSequence G e0}
      {generating' : PartialEdgeColoring E k}
      (lower : ExtendedTashkinovTree G k e0 input' T' generating'),
      0 < lower.rounds → lower.rounds < ett.rounds → MaximumProperty lower →
      ColoredVertexSetElementary G generating'
          (TreeSequenceVertexSet T') ∧
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
             TreeInterchangeable G Tnext sigma alpha beta) ∧
        ((∀ (q : Fin lower.rounds) (v : V),
          lower.series.data.kind q.succ =
              some TashkinovExtensionKind.PE →
          lower.series.data.chosenVertex q.succ = some v →
          ∀ hvFinal : v ∈ TreeSequenceVertexSet T',
          ∀ j : Fin (lower.rounds + 1),
            ETTFirstAppearanceIndex lower v hvFinal = j.val + 1 →
            ∀ sigma : PartialEdgeColoring E k,
              IsProperEdgeColoring G sigma →
              IsOneEdgeUncolored sigma e0 →
              StableColoring
                (lower.series.data.tree q.succ.castSucc)
                (TashkinovStoredColors lower.series.data q.succ)
                (lower.series.data.coloring q.succ) sigma →
              StableColoringBeforeVertex T' v hvFinal
                  (TashkinovStoredColors lower.series.data j)
                  (lower.series.data.coloring j) sigma ∧
                (0 < j.val →
                  StableColoring (lower.series.data.tree j.castSucc)
                    (TashkinovStoredColors lower.series.data j)
                    (lower.series.data.coloring j) sigma)) ∧
          ∀ (q r : Fin lower.rounds) (vq vr : V),
            q ≠ r → vq ≠ vr →
            lower.series.data.kind q.succ =
                some TashkinovExtensionKind.PE →
            lower.series.data.kind r.succ =
                some TashkinovExtensionKind.PE →
            lower.series.data.chosenVertex q.succ = some vq →
            lower.series.data.chosenVertex r.succ = some vr →
            ∀ (hvq : vq ∈ TreeSequenceVertexSet T')
              (hvr : vr ∈ TreeSequenceVertexSet T'),
              ETTFirstAppearanceIndex lower vq hvq =
                  ETTFirstAppearanceIndex lower vr hvr →
              Disjoint (lower.series.data.stored q.succ)
                (lower.series.data.stored r.succ)) ∧
        (let n : Fin (lower.rounds + 1) := Fin.last lower.rounds
         let Tn : TreeSequence G e0 :=
           lower.series.data.tree n.castSucc
         ∀ (v : V) (gamma delta : Fin k),
           lower.series.data.kind n = some TashkinovExtensionKind.PE →
           lower.series.data.chosenVertex n = some v →
           lower.series.data.gamma n = some gamma →
           lower.series.data.delta n = some delta →
           ∀ sigma : PartialEdgeColoring E k,
             IsProperEdgeColoring G sigma →
             IsOneEdgeUncolored sigma e0 →
             StableColoring Tn
               (TashkinovStoredColors lower.series.data n)
               (lower.series.data.coloring n) sigma →
             ∀ w, w ∈ TreeSequenceVertexSet Tn →
               (Sum.inl w ∈ TwoColorComponent G sigma gamma delta
                   (Sum.inl v) ↔ w = v)) ∧
        (let n : Fin (lower.rounds + 1) := Fin.last lower.rounds
         let Tn : TreeSequence G e0 :=
           lower.series.data.tree n.castSucc
         ∀ sigma : PartialEdgeColoring E k,
           IsProperEdgeColoring G sigma → IsOneEdgeUncolored sigma e0 →
           StableColoring Tn
             (TashkinovStoredColors lower.series.data n)
             (lower.series.data.coloring n) sigma →
           ∀ (delta : Fin k),
             DefectiveColor G sigma (TreeSequenceVertexSet Tn) delta →
             ∀ (v : V),
               BoundaryColorVertex G sigma (TreeSequenceVertexSet Tn)
                   delta v →
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
                 v = vi ∨ TreeVertexOrder T' v vi) ∧
        (let n : Fin (lower.rounds + 1) := Fin.last lower.rounds
         let Tn : TreeSequence G e0 :=
           lower.series.data.tree n.castSucc
         ∀ sigma : PartialEdgeColoring E k,
           IsProperEdgeColoring G sigma → IsOneEdgeUncolored sigma e0 →
           StableColoring Tn
             (TashkinovStoredColors lower.series.data n)
             (lower.series.data.coloring n) sigma →
           ModColoring lower sigma)) :
    let n : Fin (ett.rounds + 1) := Fin.last ett.rounds
    ett.series.data.kind n = some TashkinovExtensionKind.RE →
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc
    ∀ sigma : PartialEdgeColoring E k,
      IsProperEdgeColoring G sigma → IsOneEdgeUncolored sigma e0 →
      StableColoring Tn
        (TashkinovStoredColors ett.series.data n)
        (ett.series.data.coloring n) sigma →
      ModColoring ett sigma := by
-- BODY
  classical
  dsimp
  intro hterminalRE sigma hsigmaProper hsigmaOne hsigmaStable
  refine ⟨hsigmaProper, hsigmaOne, ?_⟩
  intro Tstar hTnTstar hstrict heligible
  rcases heligible with hparallel | hre
  · rw [hterminalRE] at hparallel
    simp at hparallel
  rcases hre with ⟨hkind, fstar, seed, hfinalEdges, hadjoin, hroute⟩
  obtain ⟨closureTree, hclosure⟩ :=
    TashkinovClosureExists sigma Tstar
  have hrouteClosure : TashkinovAugmentationSequence sigma seed closureTree :=
    hroute.trans hclosure.1
  have hseedClosure : TashkinovClosure sigma seed closureTree :=
    ⟨hrouteClosure, hclosure.2⟩
  have hTstarClosure : TreeSequenceInitialSegment Tstar closureTree :=
    TashkinovAugmentationSequenceInitialSegment sigma Tstar closureTree hclosure.1
  have hTnClosure : TreeSequenceInitialSegment
      (ett.series.data.tree (Fin.last ett.rounds).castSucc) closureTree := by
    rcases hTnTstar with ⟨hlenAB, hvertexAB, hedgeAB⟩
    rcases hTstarClosure with ⟨hlenBC, hvertexBC, hedgeBC⟩
    refine ⟨Nat.le_trans hlenAB hlenBC, ?_, ?_⟩
    · intro j
      calc
        closureTree.vertex
              (Fin.castLE (Nat.succ_le_succ (Nat.le_trans hlenAB hlenBC)) j) =
            closureTree.vertex
              (Fin.castLE (Nat.succ_le_succ hlenBC)
                (Fin.castLE (Nat.succ_le_succ hlenAB) j)) := by congr 1
        _ = Tstar.vertex (Fin.castLE (Nat.succ_le_succ hlenAB) j) :=
          hvertexBC _
        _ = (ett.series.data.tree (Fin.last ett.rounds).castSucc).vertex j :=
          hvertexAB j
    · intro j
      calc
        closureTree.edge (Fin.castLE (Nat.le_trans hlenAB hlenBC) j) =
            closureTree.edge (Fin.castLE hlenBC (Fin.castLE hlenAB j)) := by
          congr 1
        _ = Tstar.edge (Fin.castLE hlenAB j) := hedgeBC _
        _ = (ett.series.data.tree (Fin.last ett.rounds).castSucc).edge j :=
          hedgeAB j
  let q : Fin ett.rounds :=
    ⟨ett.rounds - 1,
      Nat.sub_lt (Nat.zero_lt_of_lt hpositive) (by omega)⟩
  have hqSucc : q.succ = Fin.last ett.rounds := by
    apply Fin.ext
    simp [q]
    omega
  have hqCast : q.castSucc =
      (⟨ett.rounds - 1, by omega⟩ : Fin (ett.rounds + 1)) := by
    apply Fin.ext
    rfl
  have hfinalStep := ett.series.certified (Fin.last ett.rounds)
  generalize htarget : (Fin.last ett.rounds : Fin (ett.rounds + 1)) =
    target at hfinalStep
  cases hfinalStep with
  | initial triple seedLength initialColoring initialStored initialEdges
      initialKind initialVertex initialOutside initialDelta initialGamma
      initialClosure =>
      have hv := congrArg Fin.val htarget
      simp at hv
      omega
  | SE i previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternative
      currentColoring currentStored currentEdges currentKind currentVertex
      currentOutside currentDelta currentGamma adjoined adjoinedExactly
      closedExtension orderedExtension strictExtension =>
      have hbad := currentKind.symm.trans (by simpa [htarget] using hterminalRE)
      cases hbad
  | PE i previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternativeFails
      gamma gammaRule secondStable secondStableProper secondStableOneUncolored
      secondStableRelation exitWitness currentColoring currentProper
      currentOneUncolored currentStored currentEdges currentKind currentVertex
      currentOutside currentDelta currentGamma closedExtension orderedExtension
      strictExtension =>
      have hbad := currentKind.symm.trans (by simpa [htarget] using hterminalRE)
      cases hbad
  | RE i previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed available currentColoring currentStored
      currentEdges currentKind currentVertex currentOutside currentDelta
      currentGamma adjoined adjoinedExactly closedExtension orderedExtension
      strictExtension =>
      have hi : i = q := by
        apply Fin.ext
        have hv : ett.rounds = i.val + 1 := by
          simpa using congrArg Fin.val htarget
        change i.val = ett.rounds - 1
        omega
      subst i
      have hreKind : ett.series.data.kind q.succ =
          some TashkinovExtensionKind.RE := by
        simpa [htarget] using currentKind
      have hprefix := TdReplacementPrefixExact G k e0 input T generating ett
        hMP hpositive hlower sigma hsigmaProper hsigmaOne
        (by simpa [hqSucc] using hsigmaStable)
      obtain ⟨sigmaPrev, hsigmaPrevProper, hsigmaPrevOne,
          hsigmaPrevStable, hsigmaPrevEq, hparallelPrev, hprefixCases⟩ := hprefix
      have hsigmaPrevSigma : sigmaPrev = sigma :=
        hsigmaPrevEq (Or.inr (by simpa [hqSucc] using hreKind))
      subst sigmaPrev
      rcases hprefixCases with hzero | hpositivePrefix
      · rcases hzero with ⟨hroundOne, prefixInput, zeroPrefix,
            hzeroTree, hzeroColor⟩
        have : available.earlier.val ≤ 0 := by
          have hqzero : q.castSucc.val = 0 := by simp [q, hroundOne]
          have hle := available.earlierAtMost
          omega
        have hearlierPositive := available.earlierPositive
        omega
      · rcases hpositivePrefix with ⟨hroundLarge, originalPrefix, hr,
            hprefixMP, hprefixTrees, hprefixData, corr, hcorrFinalTree,
            hcorrFinalColor, hcorrMP⟩
        let earlierPrefix : Fin (originalPrefix.rounds + 1) :=
          ⟨available.earlier.val, by
            rw [hr]
            have hle := available.earlierAtMost
            change available.earlier.val ≤ q.castSucc.val at hle
            simp [q] at hle ⊢
            omega⟩
        have hearlierMap : Fin.castLE (by omega) earlierPrefix =
            available.earlier := by
          apply Fin.ext
          rfl
        have hearlierPositive : 0 < earlierPrefix.val :=
          available.earlierPositive
        have hprefixEarlierKind : originalPrefix.series.data.kind
            earlierPrefix = some TashkinovExtensionKind.PE := by
          rw [(hprefixData earlierPrefix).2.2.2.1, hearlierMap]
          exact available.earlierPE
        have hreplacementEarlierKind : corr.replacementSeries.data.kind
            earlierPrefix = some TashkinovExtensionKind.PE := by
          rw [corr.extensionKindsAgree earlierPrefix]
          exact hprefixEarlierKind
        have holdStep := ett.series.certified available.earlier
        generalize holdTarget : available.earlier = oldTarget at holdStep
        cases holdStep with
        | initial tripleOld seedLengthOld initialColoringOld initialStoredOld
            initialEdgesOld initialKindOld initialVertexOld initialOutsideOld
            initialDeltaOld initialGammaOld initialClosureOld =>
            have hbad := initialKindOld.symm.trans
              (by simpa [holdTarget] using available.earlierPE)
            simp at hbad
        | SE oldi oldPreviousProper oldPreviousOne oldPreviousClosed
            oldPreviousNotStrong oldNoRE oldChoice oldAlternative
            oldCurrentColoring oldCurrentStored oldCurrentEdges oldCurrentKind
            oldCurrentVertex oldCurrentOutside oldCurrentDelta oldCurrentGamma
            oldAdjoined oldAdjoinedExactly oldClosedExtension
            oldOrderedExtension oldStrictExtension =>
            have hbad := oldCurrentKind.symm.trans
              (by simpa [holdTarget] using available.earlierPE)
            cases hbad
        | RE oldi oldPreviousProper oldPreviousOne oldPreviousClosed
            oldPreviousNotStrong oldAvailable oldCurrentColoring
            oldCurrentStored oldCurrentEdges oldCurrentKind oldCurrentVertex
            oldCurrentOutside oldCurrentDelta oldCurrentGamma oldAdjoined
            oldAdjoinedExactly oldClosedExtension oldOrderedExtension
            oldStrictExtension =>
            have hbad := oldCurrentKind.symm.trans
              (by simpa [holdTarget] using available.earlierPE)
            cases hbad
        | PE oldi oldPreviousProper oldPreviousOne oldPreviousClosed
            oldPreviousNotStrong oldNoRE oldChoice oldAlternativeFails oldGamma
            oldGammaRule oldSecond oldSecondProper oldSecondOne
            oldSecondStable oldExit oldCurrentColoring oldCurrentProper
            oldCurrentOne oldCurrentStored oldCurrentEdges oldCurrentKind
            oldCurrentVertex oldCurrentOutside oldCurrentDelta oldCurrentGamma
            oldClosedExtension oldOrderedExtension oldStrictExtension =>
            have holdIndex : oldi.succ = available.earlier := by
              simpa using holdTarget.symm
            have hnewStep := corr.replacementSeries.certified earlierPrefix
            generalize hnewTarget : earlierPrefix = newTarget at hnewStep
            cases hnewStep with
            | initial tripleNew seedLengthNew initialColoringNew initialStoredNew
                initialEdgesNew initialKindNew initialVertexNew initialOutsideNew
                initialDeltaNew initialGammaNew initialClosureNew =>
                have hbad := initialKindNew.symm.trans
                  (by simpa [hnewTarget] using hreplacementEarlierKind)
                simp at hbad
            | SE newi newPreviousProper newPreviousOne newPreviousClosed
                newPreviousNotStrong newNoRE newChoice newAlternative
                newCurrentColoring newCurrentStored newCurrentEdges
                newCurrentKind newCurrentVertex newCurrentOutside
                newCurrentDelta newCurrentGamma newAdjoined
                newAdjoinedExactly newClosedExtension newOrderedExtension
                newStrictExtension =>
                have hbad := newCurrentKind.symm.trans
                  (by simpa [hnewTarget] using hreplacementEarlierKind)
                cases hbad
            | RE newi newPreviousProper newPreviousOne newPreviousClosed
                newPreviousNotStrong newAvailable newCurrentColoring
                newCurrentStored newCurrentEdges newCurrentKind
                newCurrentVertex newCurrentOutside newCurrentDelta
                newCurrentGamma newAdjoined newAdjoinedExactly
                newClosedExtension newOrderedExtension newStrictExtension =>
                have hbad := newCurrentKind.symm.trans
                  (by simpa [hnewTarget] using hreplacementEarlierKind)
                cases hbad
            | PE newi newPreviousProper newPreviousOne newPreviousClosed
                newPreviousNotStrong newNoRE newChoice newAlternativeFails
                newGamma newGammaRule newSecond newSecondProper newSecondOne
                newSecondStable newExit newCurrentColoring newCurrentProper
                newCurrentOne newCurrentStored newCurrentEdges newCurrentKind
                newCurrentVertex newCurrentOutside newCurrentDelta
                newCurrentGamma newClosedExtension newOrderedExtension
                newStrictExtension =>
                have hnewIndex : newi.succ = earlierPrefix := by
                  simpa using hnewTarget.symm
                have htree :
                    corr.replacementSeries.data.tree newi.succ.castSucc =
                      ett.series.data.tree oldi.succ.castSucc := by
                  calc
                    corr.replacementSeries.data.tree newi.succ.castSucc =
                        originalPrefix.series.data.tree newi.succ.castSucc :=
                      corr.ladderTreesAgree newi
                    _ = ett.series.data.tree
                          (Fin.castLE (by omega) newi.succ.castSucc) :=
                      hprefixTrees newi.succ.castSucc
                    _ = ett.series.data.tree oldi.succ.castSucc := by
                      congr 1
                      apply Fin.ext
                      have hvalsOld := congrArg Fin.val holdIndex
                      have hvalsNew := congrArg Fin.val hnewIndex
                      have hvalsMap := congrArg Fin.val hearlierMap
                      simp only [Fin.val_succ] at hvalsOld hvalsNew
                      simp only [Fin.val_castLE] at hvalsMap
                      simp only [Fin.val_castLE, Fin.val_castSucc]
                      omega
                let oldChoiceOnNew : MaximumDefectiveChoice G e0
                    (corr.replacementSeries.data.tree newi.succ.castSucc)
                    (TashkinovStoredColors ett.series.data oldi.castSucc)
                    (ett.series.data.coloring oldi.castSucc) :=
                  htree.symm ▸ oldChoice
                have transportChoiceFields : ∀
                    {A B : TreeSequence G e0} (hAB : A = B)
                    (C : Finset (Fin k)) (phi : PartialEdgeColoring E k)
                    (ch : MaximumDefectiveChoice G e0 A C phi),
                    (hAB ▸ ch).edge = ch.edge ∧
                      (hAB ▸ ch).vertex = ch.vertex ∧
                      (hAB ▸ ch).otherEndpoint = ch.otherEndpoint ∧
                      (hAB ▸ ch).color = ch.color := by
                  intro A B hAB C phi ch
                  subst B
                  exact ⟨rfl, rfl, rfl, rfl⟩
                have htransport := transportChoiceFields htree.symm
                  (TashkinovStoredColors ett.series.data oldi.castSucc)
                  (ett.series.data.coloring oldi.castSucc) oldChoice
                have holdEdgeCast : oldChoiceOnNew.edge = oldChoice.edge := by
                  exact htransport.1
                have holdVertexCast : oldChoiceOnNew.vertex = oldChoice.vertex := by
                  exact htransport.2.1
                have holdOtherCast : oldChoiceOnNew.otherEndpoint =
                    oldChoice.otherEndpoint := by
                  exact htransport.2.2.1
                have holdColorCast : oldChoiceOnNew.color = oldChoice.color := by
                  exact htransport.2.2.2
                have hdataEdges : corr.replacementSeries.data.connectingEdges
                    earlierPrefix =
                      ett.series.data.connectingEdges available.earlier := by
                  calc
                    corr.replacementSeries.data.connectingEdges earlierPrefix =
                        originalPrefix.series.data.connectingEdges earlierPrefix :=
                      corr.connectingEdgesAgree earlierPrefix
                    _ = ett.series.data.connectingEdges
                          (Fin.castLE (by omega) earlierPrefix) :=
                      (hprefixData earlierPrefix).2.2.1
                    _ = ett.series.data.connectingEdges available.earlier := by
                      rw [hearlierMap]
                have hdataStored : corr.replacementSeries.data.stored
                    earlierPrefix = ett.series.data.stored available.earlier := by
                  calc
                    corr.replacementSeries.data.stored earlierPrefix =
                        originalPrefix.series.data.stored earlierPrefix :=
                      corr.storedColorsAgree earlierPrefix
                    _ = ett.series.data.stored
                          (Fin.castLE (by omega) earlierPrefix) :=
                      (hprefixData earlierPrefix).2.1
                    _ = ett.series.data.stored available.earlier := by
                      rw [hearlierMap]
                have hedgePairs : ({oldChoiceOnNew.edge} : Finset E) =
                    {newChoice.edge} := by
                  have holdEdges : ett.series.data.connectingEdges
                      available.earlier = {oldChoice.edge} := by
                    simpa only [holdIndex] using oldCurrentEdges
                  have hnewEdges : corr.replacementSeries.data.connectingEdges
                      earlierPrefix = {newChoice.edge} := by
                    simpa only [hnewIndex] using newCurrentEdges
                  simpa only [holdEdgeCast] using
                    holdEdges.symm.trans (hdataEdges.symm.trans hnewEdges)
                have hcolorPairs :
                    ({oldChoiceOnNew.color, oldGamma} : Finset (Fin k)) =
                      {newChoice.color, newGamma} := by
                  have holdStored : ett.series.data.stored available.earlier =
                      {oldChoice.color, oldGamma} := by
                    simpa only [holdIndex] using oldCurrentStored
                  have hnewStored : corr.replacementSeries.data.stored
                      earlierPrefix = {newChoice.color, newGamma} := by
                    simpa only [hnewIndex] using newCurrentStored
                  simpa only [holdColorCast] using
                    holdStored.symm.trans (hdataStored.symm.trans hnewStored)
                have hedgeIdentity : newChoice.edge = oldChoiceOnNew.edge := by
                  apply Finset.mem_singleton.mp
                  rw [hedgePairs]
                  exact Finset.mem_singleton_self _
                have hends : s(oldChoiceOnNew.vertex,
                      oldChoiceOnNew.otherEndpoint) =
                    s(newChoice.vertex, newChoice.otherEndpoint) := by
                  calc
                    s(oldChoiceOnNew.vertex, oldChoiceOnNew.otherEndpoint) =
                        G.ends oldChoiceOnNew.edge := oldChoiceOnNew.edgeEnds.symm
                    _ = G.ends newChoice.edge := congrArg G.ends hedgeIdentity.symm
                    _ = s(newChoice.vertex, newChoice.otherEndpoint) :=
                      newChoice.edgeEnds
                have hvertexIdentity : newChoice.vertex =
                    oldChoiceOnNew.vertex := by
                  rcases Sym2.eq_iff.mp hends with hstraight | hcross
                  · exact hstraight.1.symm
                  · exfalso
                    exact newChoice.otherOutside
                      (hcross.1 ▸ oldChoiceOnNew.vertexDefective.1)
                have hotherIdentity : newChoice.otherEndpoint =
                    oldChoiceOnNew.otherEndpoint := by
                  rcases Sym2.eq_iff.mp hends with hstraight | hcross
                  · exact hstraight.2.symm
                  · exfalso
                    exact oldChoiceOnNew.otherOutside
                      (hcross.2 ▸ newChoice.vertexDefective.1)
                have pePostStatus : ∀
                    (X : TreeSequence G e0) (C : Finset (Fin k))
                    (phi : PartialEdgeColoring E k)
                    (ch : MaximumDefectiveChoice G e0 X C phi)
                    (g : Fin k) (second : PartialEdgeColoring E k),
                    IsProperEdgeColoring G second →
                    StableColoring X (insert ch.color C) ch.selected second →
                    g ∈ MissingColors G ch.selected ch.vertex →
                    let post := TwoColorComponentSwap G second g ch.color
                      (Sum.inl ch.vertex)
                    ch.color ∈ MissingColors G post ch.vertex ∧
                      g ∉ MissingColors G post ch.vertex ∧ g ≠ ch.color := by
                  intro X C phi ch g second hsecondProper hsecondStable
                    hgSelected
                  dsimp
                  have hgSecond : g ∈ MissingColors G second ch.vertex := by
                    rw [hsecondStable.2 ch.vertex ch.vertexDefective.1]
                    exact hgSelected
                  have hedgeSecond : second ch.edge = some ch.color := by
                    exact (hsecondStable.1 ch.edge
                      ⟨ch.vertex, ch.vertexDefective.1, ch.edgeIncident⟩
                      ⟨ch.color, Finset.mem_union_right _ (Finset.mem_insert_self _ _),
                        ch.edgeColor⟩).trans ch.edgeColor
                  have hne : g ≠ ch.color := by
                    intro heq
                    have hpresent : g ∈ PresentColors G second ch.vertex := by
                      simp only [PresentColors, Finset.mem_filter,
                        Finset.mem_univ, true_and]
                      exact ⟨ch.edge, ch.edgeIncident, by simpa [heq] using hedgeSecond⟩
                    have hnotPresent : g ∉ PresentColors G second ch.vertex := by
                      simpa [MissingColors] using hgSecond
                    exact hnotPresent hpresent
                  have hedgeComponent : Sum.inr ch.edge ∈
                      TwoColorComponent G second g ch.color
                        (Sum.inl ch.vertex) := by
                    apply SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
                    simp [TwoColorComponent, TwoColorIncidenceGraph,
                      ch.edgeIncident, hedgeSecond]
                  have hmissingDelta : ch.color ∈ MissingColors G
                      (TwoColorComponentSwap G second g ch.color
                        (Sum.inl ch.vertex)) ch.vertex := by
                    exact (TwoColorComponentSwapMissingBehavior G second g ch.color
                      hne hsecondProper (Sum.inl ch.vertex)).2.1 ch.vertex rfl
                        hgSecond
                  have hedgePost : TwoColorComponentSwap G second g ch.color
                      (Sum.inl ch.vertex) ch.edge = some g := by
                    simp [TwoColorComponentSwap, hedgeComponent, hedgeSecond,
                      hne, hne.symm]
                  have hgammaPresent : g ∈ PresentColors G
                      (TwoColorComponentSwap G second g ch.color
                        (Sum.inl ch.vertex)) ch.vertex := by
                    simp only [PresentColors, Finset.mem_filter,
                      Finset.mem_univ, true_and]
                    exact ⟨ch.edge, ch.edgeIncident, hedgePost⟩
                  exact ⟨hmissingDelta,
                    by simpa [MissingColors] using hgammaPresent, hne⟩
                obtain ⟨holdDeltaMissing, holdGammaNotMissing, holdColorNe⟩ :=
                  pePostStatus
                    (ett.series.data.tree oldi.succ.castSucc)
                    (TashkinovStoredColors ett.series.data oldi.castSucc)
                    (ett.series.data.coloring oldi.castSucc) oldChoice oldGamma
                    oldSecond oldSecondProper oldSecondStable oldGammaRule.1
                obtain ⟨hnewDeltaMissing, hnewGammaNotMissing, hnewColorNe⟩ :=
                  pePostStatus
                    (corr.replacementSeries.data.tree newi.succ.castSucc)
                    (TashkinovStoredColors corr.replacementSeries.data
                      newi.castSucc)
                    (corr.replacementSeries.data.coloring newi.castSucc)
                    newChoice newGamma newSecond newSecondProper
                    newSecondStable newGammaRule.1
                rw [← oldCurrentColoring] at holdDeltaMissing holdGammaNotMissing
                rw [← newCurrentColoring] at hnewDeltaMissing hnewGammaNotMissing
                have hbaseTree : originalPrefix.series.data.tree
                    newi.succ.castSucc =
                      ett.series.data.tree oldi.succ.castSucc := by
                  calc
                    originalPrefix.series.data.tree newi.succ.castSucc =
                        corr.replacementSeries.data.tree newi.succ.castSucc :=
                      (corr.ladderTreesAgree newi).symm
                    _ = ett.series.data.tree oldi.succ.castSucc := htree
                have hbaseColor : originalPrefix.series.data.coloring
                    newi.succ = ett.series.data.coloring oldi.succ := by
                  calc
                    originalPrefix.series.data.coloring newi.succ =
                        ett.series.data.coloring
                          (Fin.castLE (by omega) newi.succ) :=
                      (hprefixData newi.succ).1
                    _ = ett.series.data.coloring oldi.succ := by
                      congr 1
                      apply Fin.ext
                      have hvalsOld := congrArg Fin.val holdIndex
                      have hvalsNew := congrArg Fin.val hnewIndex
                      have hvalsMap := congrArg Fin.val hearlierMap
                      simp only [Fin.val_succ] at hvalsOld hvalsNew
                      simp only [Fin.val_castLE] at hvalsMap ⊢
                      omega
                have hmissingSameVertex : MissingColors G
                    (ett.series.data.coloring oldi.succ) oldChoice.vertex =
                      MissingColors G
                        (corr.replacementSeries.data.coloring newi.succ)
                        oldChoice.vertex := by
                  have hvBase : oldChoice.vertex ∈ TreeSequenceVertexSet
                      (originalPrefix.series.data.tree newi.succ.castSucc) := by
                    rw [hbaseTree]
                    exact oldChoice.vertexDefective.1
                  have hs := (corr.replacementStable newi).2 oldChoice.vertex hvBase
                  rw [hbaseColor] at hs
                  exact hs.symm
                have hmissingForIdentification : MissingColors G
                    (ett.series.data.coloring oldi.succ)
                      oldChoiceOnNew.vertex =
                    MissingColors G
                      (corr.replacementSeries.data.coloring newi.succ)
                      newChoice.vertex := by
                  calc
                    MissingColors G (ett.series.data.coloring oldi.succ)
                        oldChoiceOnNew.vertex =
                        MissingColors G (ett.series.data.coloring oldi.succ)
                          oldChoice.vertex := congrArg _ holdVertexCast
                    _ = MissingColors G
                          (corr.replacementSeries.data.coloring newi.succ)
                          oldChoice.vertex := hmissingSameVertex
                    _ = MissingColors G
                          (corr.replacementSeries.data.coloring newi.succ)
                          newChoice.vertex := congrArg _
                            (hvertexIdentity.trans holdVertexCast).symm
                have holdDeltaForIdentification : oldChoiceOnNew.color ∈
                    MissingColors G (ett.series.data.coloring oldi.succ)
                      oldChoiceOnNew.vertex := by
                  simpa only [holdColorCast, holdVertexCast] using
                    holdDeltaMissing
                have holdGammaForIdentification : oldGamma ∉
                    MissingColors G (ett.series.data.coloring oldi.succ)
                      oldChoiceOnNew.vertex := by
                  simpa only [holdVertexCast] using holdGammaNotMissing
                have hidentified := TdEarlierPEWitnessIdentification G k e0
                  (corr.replacementSeries.data.tree newi.succ.castSucc)
                  (TashkinovStoredColors ett.series.data oldi.castSucc)
                  (TashkinovStoredColors corr.replacementSeries.data
                    newi.castSucc)
                  (ett.series.data.coloring oldi.castSucc)
                  (corr.replacementSeries.data.coloring newi.castSucc)
                  oldChoiceOnNew newChoice oldGamma newGamma
                  (ett.series.data.coloring oldi.succ)
                  (corr.replacementSeries.data.coloring newi.succ)
                  hedgePairs hcolorPairs hmissingForIdentification
                  holdDeltaForIdentification holdGammaForIdentification
                  hnewDeltaMissing hnewGammaNotMissing
                rcases hidentified with ⟨hidentifiedEdge, hidentifiedVertex,
                  hidentifiedOther, hidentifiedDelta, hidentifiedGamma⟩
                have holdDeltaAvailable : oldChoice.color = available.delta := by
                  exact Option.some.inj (oldCurrentDelta.symm.trans
                    ((congrArg ett.series.data.delta holdIndex).trans
                      available.earlierDelta))
                have holdGammaAvailable : oldGamma = available.gamma := by
                  exact Option.some.inj (oldCurrentGamma.symm.trans
                    ((congrArg ett.series.data.gamma holdIndex).trans
                      available.earlierGamma))
                have hnewDeltaAvailable : newChoice.color = available.delta := by
                  exact hidentifiedDelta.trans
                    (holdColorCast.trans holdDeltaAvailable)
                have hnewGammaAvailable : newGamma = available.gamma := by
                  exact hidentifiedGamma.trans holdGammaAvailable
                have hnewVertexOld : newChoice.vertex = oldChoice.vertex :=
                  hidentifiedVertex.trans holdVertexCast
                have hnewOtherOld : newChoice.otherEndpoint =
                    oldChoice.otherEndpoint :=
                  hidentifiedOther.trans holdOtherCast
                have reStepColoring : ∀ {rounds' : ℕ}
                    {input' : PartialEdgeColoring E k}
                    (series : TashkinovSeries G k rounds' e0 input')
                    (j : Fin rounds'),
                    series.data.kind j.succ = some TashkinovExtensionKind.RE →
                    series.data.coloring j.succ =
                      series.data.coloring j.castSucc := by
                  intro rounds' input' series j hj
                  have hstep := series.certified j.succ
                  generalize hslot : j.succ = slot at hstep
                  cases hstep with
                  | initial triple seedLength initialColoring initialStored
                      initialEdges initialKind initialVertex initialOutside
                      initialDelta initialGamma initialClosure =>
                      exact (Fin.succ_ne_zero j hslot).elim
                  | SE i prevProper prevOne prevClosed prevNotStrong noRE choice
                      alternative coloring stored edges kind vertex outside delta
                      gamma adjoined adjoinedExactly closed ordered strict =>
                      have hbad := kind.symm.trans (by simpa [hslot] using hj)
                      cases hbad
                  | PE i prevProper prevOne prevClosed prevNotStrong noRE choice
                      alternativeFails gamma gammaRule second secondProper
                      secondOne secondStable exit coloring coloringProper
                      coloringOne stored edges kind vertex outside delta gammaValue
                      closed ordered strict =>
                      have hbad := kind.symm.trans (by simpa [hslot] using hj)
                      cases hbad
                  | RE i prevProper prevOne prevClosed prevNotStrong cert coloring
                      stored edges kind vertex outside delta gamma adjoined
                      adjoinedExactly closed ordered strict =>
                      have hi : i = j := by
                        apply Fin.ext
                        have hv := congrArg Fin.val hslot
                        simp only [Fin.val_succ] at hv
                        omega
                      subst i
                      simpa [hslot] using coloring
                have reIntervalColoring : ∀ {rounds' : ℕ}
                    {input' : PartialEdgeColoring E k}
                    (series : TashkinovSeries G k rounds' e0 input')
                    (a b : Fin (rounds' + 1)),
                    a.val ≤ b.val →
                    (∀ j : Fin (rounds' + 1), a.val < j.val →
                      j.val ≤ b.val →
                      series.data.kind j = some TashkinovExtensionKind.RE) →
                    series.data.coloring b = series.data.coloring a := by
                  intro rounds' input' series a b hab hbetween
                  have coloringAlong : ∀ m : ℕ, a.val ≤ m → m ≤ b.val →
                      ∀ x : Fin (rounds' + 1), x.val = m →
                        series.data.coloring x = series.data.coloring a := by
                    intro m ham
                    induction m, ham using Nat.le_induction with
                    | base =>
                        intro hmb x hx
                        have hxa : x = a := by
                          apply Fin.ext
                          omega
                        rw [hxa]
                    | succ m ham ih =>
                        intro hmb x hx
                        let j : Fin rounds' := ⟨m, by
                          have hbLt := b.isLt
                          omega⟩
                        have hjKind : series.data.kind j.succ =
                            some TashkinovExtensionKind.RE := by
                          apply hbetween j.succ
                          · simp [j]
                            omega
                          · simp [j]
                            omega
                        have hstep := reStepColoring series j hjKind
                        have hxj : x = j.succ := by
                          apply Fin.ext
                          simp [j, hx]
                        calc
                          series.data.coloring x =
                              series.data.coloring j.succ := by rw [hxj]
                          _ = series.data.coloring j.castSucc := hstep
                          _ = series.data.coloring a :=
                            ih (by omega) j.castSucc (by simp [j])
                  exact coloringAlong b.val hab le_rfl b rfl
                have holdColorConstant : ett.series.data.coloring q.castSucc =
                    ett.series.data.coloring oldi.succ := by
                  apply reIntervalColoring ett.series oldi.succ q.castSucc
                  · have hvals := congrArg Fin.val holdIndex
                    have hle := available.earlierAtMost
                    simp only [Fin.val_succ] at hvals
                    omega
                  · intro j hjLower hjUpper
                    apply available.interveningRevisiting j
                    · have holdPositive := available.earlierPositive
                      have hvals := congrArg Fin.val holdIndex
                      simp only [Fin.val_succ] at hvals
                      omega
                    · have hvals := congrArg Fin.val holdIndex
                      simp only [Fin.val_succ] at hvals
                      omega
                    · exact hjUpper
                let replacementLast : Fin (originalPrefix.rounds + 1) :=
                  Fin.last originalPrefix.rounds
                have hreplacementLastMap : Fin.castLE (by omega)
                    replacementLast = q.castSucc := by
                  apply Fin.ext
                  simp [replacementLast, q, hr]
                have hreplacementColorConstant :
                    corr.replacementSeries.data.coloring replacementLast =
                      corr.replacementSeries.data.coloring newi.succ := by
                  apply reIntervalColoring corr.replacementSeries newi.succ
                    replacementLast
                  · have hvals := congrArg Fin.val hnewIndex
                    simp [replacementLast] at hvals ⊢
                  · intro j hjLower hjUpper
                    rw [corr.extensionKindsAgree j,
                      (hprefixData j).2.2.2.1]
                    apply available.interveningRevisiting
                      (Fin.castLE (by omega) j)
                    · simp only [Fin.val_castLE]
                      omega
                    · have hvalsNew := congrArg Fin.val hnewIndex
                      have hvalsMap := congrArg Fin.val hearlierMap
                      simp only [Fin.val_succ] at hvalsNew
                      simp only [Fin.val_castLE] at hvalsMap ⊢
                      omega
                    · have hvalsLast := congrArg Fin.val hreplacementLastMap
                      simp only [Fin.val_castLE] at hvalsLast ⊢
                      omega
                have hnewPostSigma :
                    corr.replacementSeries.data.coloring newi.succ = sigma := by
                  exact hreplacementColorConstant.symm.trans
                    (by simpa [replacementLast] using hcorrFinalColor)
                have hnewDeltaSigma : available.delta ∈
                    MissingColors G sigma newChoice.vertex := by
                  have hm := hnewDeltaMissing
                  rw [hnewDeltaAvailable] at hm
                  exact Eq.mp (congrArg (fun phi => available.delta ∈
                    MissingColors G phi newChoice.vertex) hnewPostSigma) hm
                have hnewGammaSigmaNot : available.gamma ∉
                    MissingColors G sigma newChoice.vertex := by
                  have hm := hnewGammaNotMissing
                  rw [hnewGammaAvailable] at hm
                  exact Eq.mp (congrArg (fun phi => available.gamma ∉
                    MissingColors G phi newChoice.vertex) hnewPostSigma) hm
                have hgammaDeltaNe : available.gamma ≠ available.delta := by
                  intro heq
                  apply hnewColorNe
                  rw [hnewGammaAvailable, hnewDeltaAvailable, heq]
                have stepSegment : ∀ r : Fin originalPrefix.rounds,
                    TreeSequenceInitialSegment
                      (corr.replacementSeries.data.tree r.succ.castSucc)
                      (corr.replacementSeries.data.tree r.succ.succ) := by
                  intro r
                  have hstep := corr.replacementSeries.certified r.succ
                  generalize hslot : r.succ = slot at hstep
                  cases hstep with
                  | initial triple seedLength initialColoring initialStored
                      initialEdges initialKind initialVertex initialOutside
                      initialDelta initialGamma initialClosure =>
                      exact (Fin.succ_ne_zero r hslot).elim
                  | SE i prevProper prevOne prevClosed prevNotStrong noRE choice
                      alternative coloring stored edges kind vertex outside delta
                      gamma adjoined adjoinedExactly closed ordered strict =>
                      have hi : i = r := by
                        apply Fin.ext
                        have hv := congrArg Fin.val hslot
                        simp only [Fin.val_succ] at hv
                        omega
                      subst i
                      simpa [hslot] using ordered
                  | PE i prevProper prevOne prevClosed prevNotStrong noRE choice
                      alternativeFails gamma gammaRule second secondProper
                      secondOne secondStable exit coloring coloringProper
                      coloringOne stored edges kind vertex outside delta gammaValue
                      closed ordered strict =>
                      have hi : i = r := by
                        apply Fin.ext
                        have hv := congrArg Fin.val hslot
                        simp only [Fin.val_succ] at hv
                        omega
                      subst i
                      simpa [hslot] using ordered
                  | RE i prevProper prevOne prevClosed prevNotStrong cert coloring
                      stored edges kind vertex outside delta gamma adjoined
                      adjoinedExactly closed ordered strict =>
                      have hi : i = r := by
                        apply Fin.ext
                        have hv := congrArg Fin.val hslot
                        simp only [Fin.val_succ] at hv
                        omega
                      subst i
                      simpa [hslot] using ordered
                have segmentTrans : ∀ (A B C : TreeSequence G e0),
                    TreeSequenceInitialSegment A B →
                    TreeSequenceInitialSegment B C →
                    TreeSequenceInitialSegment A C := by
                  intro A B C hAB hBC
                  rcases hAB with ⟨hlenAB, hvertexAB, hedgeAB⟩
                  rcases hBC with ⟨hlenBC, hvertexBC, hedgeBC⟩
                  refine ⟨hlenAB.trans hlenBC, ?_, ?_⟩
                  · intro x
                    calc
                      C.vertex (Fin.castLE
                          (Nat.succ_le_succ (hlenAB.trans hlenBC)) x) =
                          C.vertex (Fin.castLE (Nat.succ_le_succ hlenBC)
                            (Fin.castLE (Nat.succ_le_succ hlenAB) x)) := by
                            congr 1
                      _ = B.vertex (Fin.castLE (Nat.succ_le_succ hlenAB) x) :=
                        hvertexBC _
                      _ = A.vertex x := hvertexAB x
                  · intro x
                    calc
                      C.edge (Fin.castLE (hlenAB.trans hlenBC) x) =
                          C.edge (Fin.castLE hlenBC (Fin.castLE hlenAB x)) := by
                            congr 1
                      _ = B.edge (Fin.castLE hlenAB x) := hedgeBC _
                      _ = A.edge x := hedgeAB x
                have treeToFinal : ∀ (d : ℕ)
                    (idx : Fin (originalPrefix.rounds + 2)),
                    idx.val + d = originalPrefix.rounds + 1 →
                    1 ≤ idx.val →
                    TreeSequenceInitialSegment
                      (corr.replacementSeries.data.tree idx)
                      (corr.replacementSeries.data.tree
                        (Fin.last (originalPrefix.rounds + 1))) := by
                  intro d
                  induction d with
                  | zero =>
                      intro idx hidx hpos
                      have hi : idx = Fin.last (originalPrefix.rounds + 1) := by
                        apply Fin.ext
                        simp
                        omega
                      rw [hi]
                      exact ⟨le_rfl, (fun _ => rfl), (fun _ => rfl)⟩
                  | succ d ih =>
                      intro idx hidx hpos
                      have hlt : idx.val < originalPrefix.rounds + 1 := by
                        omega
                      let r : Fin originalPrefix.rounds :=
                        ⟨idx.val - 1, by omega⟩
                      have hleft : idx = r.succ.castSucc := by
                        apply Fin.ext
                        simp [r]
                        omega
                      let next : Fin (originalPrefix.rounds + 2) :=
                        ⟨idx.val + 1, by omega⟩
                      have hright : next = r.succ.succ := by
                        apply Fin.ext
                        simp [next, r]
                        omega
                      have hfirst : TreeSequenceInitialSegment
                          (corr.replacementSeries.data.tree idx)
                          (corr.replacementSeries.data.tree next) := by
                        rw [hleft, hright]
                        exact stepSegment r
                      exact segmentTrans _ _ _ hfirst
                        (ih next (by simp [next]; omega) (by simp [next]))
                have hnewTreeFinal : TreeSequenceInitialSegment
                    (corr.replacementSeries.data.tree newi.succ.castSucc)
                    (corr.replacementSeries.data.tree
                      (Fin.last (originalPrefix.rounds + 1))) := by
                  apply treeToFinal (originalPrefix.rounds - newi.val)
                  · simp
                    omega
                  · simp
                have hnewVertexTn : newChoice.vertex ∈ TreeSequenceVertexSet
                    (ett.series.data.tree (Fin.last ett.rounds).castSucc) := by
                  have hvFinal : newChoice.vertex ∈ TreeSequenceVertexSet
                      (corr.replacementSeries.data.tree
                        (Fin.last (originalPrefix.rounds + 1))) :=
                    TreeSequenceInitialSegmentVertexSetSubset hnewTreeFinal
                      newChoice.vertexDefective.1
                  exact Eq.mp
                    (congrArg (fun X => newChoice.vertex ∈
                      TreeSequenceVertexSet X) hcorrFinalTree) hvFinal
                have hgammaPresentSigma : available.gamma ∈
                    PresentColors G sigma newChoice.vertex := by
                  simpa [MissingColors] using hnewGammaSigmaNot
                obtain ⟨pathEdge, hpathEdgeIncident, hpathEdgeColor⟩ := by
                  simpa only [PresentColors, Finset.mem_filter,
                    Finset.mem_univ, true_and] using hgammaPresentSigma
                have hpathEdgeComponent : Sum.inr pathEdge ∈
                    TwoColorComponent G sigma available.gamma available.delta
                      (Sum.inl newChoice.vertex) := by
                  apply SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
                  simp [TwoColorComponent, TwoColorIncidenceGraph,
                    hpathEdgeIncident, hpathEdgeColor]
                have hleafDegree : @SimpleGraph.degree _
                    (TwoColorIncidenceGraph G sigma available.gamma
                      available.delta) (Sum.inl newChoice.vertex)
                    (Fintype.ofFinite _) ≤ 1 := by
                  have hgraphSwapOrder :
                      TwoColorIncidenceGraph G sigma available.delta
                          available.gamma =
                        TwoColorIncidenceGraph G sigma available.gamma
                          available.delta := by
                    ext x y
                    cases x <;> cases y <;>
                      simp [TwoColorIncidenceGraph, or_comm]
                  rw [← hgraphSwapOrder]
                  exact MissingColorIncidenceEndpoint G sigma available.delta
                    available.gamma hgammaDeltaNe.symm hsigmaProper
                    newChoice.vertex hnewDeltaSigma
                have hleaf : Set.Subsingleton
                    ((TwoColorIncidenceGraph G sigma available.gamma
                      available.delta).neighborSet
                        (Sum.inl newChoice.vertex)) := by
                  letI : Fintype
                      ((TwoColorIncidenceGraph G sigma available.gamma
                        available.delta).neighborSet
                          (Sum.inl newChoice.vertex)) := Fintype.ofFinite _
                  rw [← SimpleGraph.card_neighborSet_eq_degree] at hleafDegree
                  have hsub := Fintype.card_le_one_iff.mp hleafDegree
                  intro a ha b hb
                  exact congrArg Subtype.val
                    (hsub ⟨a, ha⟩ ⟨b, hb⟩)
                have hpathComponent : TwoColorNontrivialPathComponent G sigma
                    available.gamma available.delta
                    (Sum.inl newChoice.vertex) := by
                  refine ⟨⟨hgammaDeltaNe, Sum.inl newChoice.vertex, rfl,
                    hleaf⟩, pathEdge, hpathEdgeComponent⟩
                have hpathMeetsTn : ∃ v ∈ TreeSequenceVertexSet
                    (ett.series.data.tree (Fin.last ett.rounds).castSucc),
                    Sum.inl v ∈ TwoColorComponent G sigma available.gamma
                      available.delta (Sum.inl newChoice.vertex) :=
                  ⟨newChoice.vertex, hnewVertexTn, rfl⟩
                have hsigmaPrevStableQ : StableColoring
                    (ett.series.data.tree q.succ.castSucc)
                    (TashkinovStoredColors ett.series.data q.castSucc)
                    (ett.series.data.coloring q.castSucc) sigma := by
                  rw [hqSucc]
                  simpa [q] using hsigmaPrevStable
                have hgammaEarlierStored : available.gamma ∈
                    ett.series.data.stored available.earlier := by
                  rw [← holdIndex, oldCurrentStored, ← holdGammaAvailable]
                  simp
                have hdeltaEarlierStored : available.delta ∈
                    ett.series.data.stored available.earlier := by
                  rw [← holdIndex, oldCurrentStored, ← holdDeltaAvailable]
                  simp
                let previousPrefixIndex : Fin (originalPrefix.rounds + 2) :=
                  ⟨originalPrefix.rounds, by omega⟩
                have hpreviousPrefixMap : Fin.castLE (by omega)
                    previousPrefixIndex = q.castSucc.castSucc := by
                  apply Fin.ext
                  simp [previousPrefixIndex, q, hr]
                have hpreviousToTn : TreeSequenceInitialSegment
                    (ett.series.data.tree q.castSucc.castSucc)
                    (ett.series.data.tree q.succ.castSucc) := by
                  have hseg := originalPrefix.abovePenultimate
                  rw [hprefixTrees previousPrefixIndex] at hseg
                  rw [hpreviousPrefixMap] at hseg
                  simpa [hqSucc] using hseg
                have missingPreviousToTn (c : Fin k)
                    (hc : c ∈ TreeMissingColors
                      (ett.series.data.coloring q.castSucc)
                      (ett.series.data.tree q.castSucc.castSucc)) :
                    c ∈ TreeMissingColors
                      (ett.series.data.coloring q.castSucc)
                      (ett.series.data.tree q.succ.castSucc) := by
                  simp only [TreeMissingColors, Finset.mem_biUnion] at hc ⊢
                  obtain ⟨v, hv, hvc⟩ := hc
                  exact ⟨v,
                    TreeSequenceInitialSegmentVertexSetSubset hpreviousToTn hv,
                    hvc⟩
                have colorControlAtQ (c : Fin k)
                    (hc : c ∈ ett.series.data.stored available.earlier) :
                    c ∈ TreeMissingColors (ett.series.data.coloring q.castSucc)
                          (ett.series.data.tree q.succ.castSucc) ∪
                        TashkinovStoredColors ett.series.data q.castSucc := by
                  by_cases hm : c ∈ TreeMissingColors
                      (ett.series.data.coloring q.castSucc)
                      (ett.series.data.tree q.castSucc.castSucc)
                  · exact Finset.mem_union_left _ (missingPreviousToTn c hm)
                  · apply Finset.mem_union_right
                    unfold TashkinovStoredColors
                    have hqne : q.castSucc.val ≠ 0 := by
                      change ett.rounds - 1 ≠ 0
                      omega
                    rw [if_neg hqne]
                    rw [Finset.mem_sdiff]
                    refine ⟨?_, hm⟩
                    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
                    refine ⟨available.earlier, ?_⟩
                    rw [if_pos]
                    · exact hc
                    · exact available.earlierAtMost
                have hreturnNotNil : ¬ available.returnPath.Nil := by
                  intro hnil
                  have hend := SimpleGraph.Walk.Nil.eq hnil
                  simp at hend
                have oldReturnEdgeData (f : E)
                    (hf : Sum.inr f ∈ available.returnPath.support) :
                    TreeIncidentEdge
                        (ett.series.data.tree q.succ.castSucc) f ∧
                      (ett.series.data.coloring q.castSucc f =
                          some available.gamma ∨
                        ett.series.data.coloring q.castSucc f =
                          some available.delta) := by
                  obtain ⟨node, hnode, hadj⟩ :=
                    SimpleGraph.adj_of_mem_walk_support available.returnPath
                      hreturnNotNil hf
                  cases node with
                  | inl v =>
                      have hdata : Incident G v f ∧
                          (ett.series.data.coloring q.castSucc f =
                              some available.gamma ∨
                            ett.series.data.coloring q.castSucc f =
                              some available.delta) := by
                        simpa [TwoColorIncidenceGraph] using hadj
                      exact ⟨⟨v, available.returnPathInternal v hnode,
                        hdata.1⟩, hdata.2⟩
                  | inr g =>
                      simpa [TwoColorIncidenceGraph] using hadj
                have copyReturnEdge (f : E)
                    (hf : Sum.inr f ∈ available.returnPath.support) :
                    sigma f = ett.series.data.coloring q.castSucc f := by
                  obtain ⟨hfIncident, hcolor⟩ := oldReturnEdgeData f hf
                  apply hsigmaPrevStableQ.1 f hfIncident
                  rcases hcolor with hgamma | hdelta
                  · exact ⟨available.gamma,
                      colorControlAtQ available.gamma hgammaEarlierStored,
                      hgamma⟩
                  · exact ⟨available.delta,
                      colorControlAtQ available.delta hdeltaEarlierStored,
                      hdelta⟩
                let oldReturnGraph := TwoColorIncidenceGraph G
                  (ett.series.data.coloring q.castSucc) available.gamma
                  available.delta
                let sigmaReturnGraph := TwoColorIncidenceGraph G sigma
                  available.gamma available.delta
                have returnEdgeTransfer : ∀ edge,
                    edge ∈ available.returnPath.edges →
                    edge ∈ sigmaReturnGraph.edgeSet := by
                  intro edge hedge
                  induction edge using Sym2.inductionOn with
                  | _ a b =>
                      have haSupport :=
                        available.returnPath.fst_mem_support_of_mem_edges hedge
                      have hbSupport :=
                        available.returnPath.snd_mem_support_of_mem_edges hedge
                      have habOld : oldReturnGraph.Adj a b := by
                        simpa [oldReturnGraph] using
                          available.returnPath.edges_subset_edgeSet hedge
                      cases a with
                      | inl v =>
                          cases b with
                          | inl w =>
                              simpa [oldReturnGraph, TwoColorIncidenceGraph]
                                using habOld
                          | inr f =>
                              have hdata : Incident G v f ∧
                                  (ett.series.data.coloring q.castSucc f =
                                      some available.gamma ∨
                                    ett.series.data.coloring q.castSucc f =
                                      some available.delta) := by
                                simpa [oldReturnGraph,
                                  TwoColorIncidenceGraph] using habOld
                              have hcopy := copyReturnEdge f hbSupport
                              simpa [sigmaReturnGraph, TwoColorIncidenceGraph,
                                hcopy] using hdata
                      | inr f =>
                          cases b with
                          | inl v =>
                              have hdata : Incident G v f ∧
                                  (ett.series.data.coloring q.castSucc f =
                                      some available.gamma ∨
                                    ett.series.data.coloring q.castSucc f =
                                      some available.delta) := by
                                simpa [oldReturnGraph,
                                  TwoColorIncidenceGraph] using habOld
                              have hcopy := copyReturnEdge f haSupport
                              simpa [sigmaReturnGraph, TwoColorIncidenceGraph,
                                hcopy] using hdata
                          | inr g =>
                              simpa [oldReturnGraph, TwoColorIncidenceGraph]
                                using habOld
                let sigmaReturnPath :=
                  available.returnPath.transfer sigmaReturnGraph
                    returnEdgeTransfer
                have hsigmaReturnIsPath : sigmaReturnPath.IsPath := by
                  exact available.returnPathIsPath.transfer returnEdgeTransfer
                have hsigmaReturnSupport : ∀ z,
                    z ∈ sigmaReturnPath.support ↔
                      z ∈ available.returnPath.support := by
                  intro z
                  simp [sigmaReturnPath]
                have hreturnInQ : Sum.inl available.returnVertex ∈
                    TwoColorComponent G sigma available.gamma available.delta
                      (Sum.inr available.edge) := by
                  change sigmaReturnGraph.connectedComponentMk
                      (Sum.inl available.returnVertex) =
                    sigmaReturnGraph.connectedComponentMk
                      (Sum.inr available.edge)
                  exact (SimpleGraph.ConnectedComponent.sound
                    sigmaReturnPath.reachable).symm
                have hedgeSigmaActive : sigma available.edge =
                      some available.gamma ∨
                    sigma available.edge = some available.delta := by
                  have hsupport : Sum.inr available.edge ∈
                      available.returnPath.support := by simp
                  have hold := (oldReturnEdgeData available.edge hsupport).2
                  rw [copyReturnEdge available.edge hsupport]
                  exact hold
                have houtsideInQ : Sum.inl available.outsideEndpoint ∈
                    TwoColorComponent G sigma available.gamma available.delta
                      (Sum.inr available.edge) := by
                  apply SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
                  have houtIncident : Incident G available.outsideEndpoint
                      available.edge := by
                    unfold Incident
                    rw [available.edgeEnds]
                    exact Sym2.mem_mk_right _ _
                  simp [TwoColorComponent, TwoColorIncidenceGraph,
                    houtIncident, hedgeSigmaActive]
                have hreturnInNewEarlier : available.returnVertex ∈
                    TreeSequenceVertexSet
                      (corr.replacementSeries.data.tree
                        earlierPrefix.castSucc) := by
                  rw [← hnewIndex, htree]
                  simpa only [holdIndex] using available.returnInEarlier
                have hreturnInTn : available.returnVertex ∈
                    TreeSequenceVertexSet
                      (ett.series.data.tree
                        (Fin.last ett.rounds).castSucc) := by
                  have hvFinal : available.returnVertex ∈
                      TreeSequenceVertexSet
                        (corr.replacementSeries.data.tree
                          (Fin.last (originalPrefix.rounds + 1))) :=
                    TreeSequenceInitialSegmentVertexSetSubset hnewTreeFinal
                      (by simpa only [hnewIndex] using hreturnInNewEarlier)
                  exact Eq.mp
                    (congrArg (fun X => available.returnVertex ∈
                      TreeSequenceVertexSet X) hcorrFinalTree) hvFinal
                have holdDeltaAtNewVertex : available.delta ∈ MissingColors G
                    (ett.series.data.coloring q.castSucc)
                    newChoice.vertex := by
                  have hm := holdDeltaMissing
                  rw [holdDeltaAvailable] at hm
                  have hm' : available.delta ∈ MissingColors G
                      (ett.series.data.coloring oldi.succ)
                      newChoice.vertex := by
                    simpa only [hnewVertexOld] using hm
                  exact Eq.mpr (congrArg (fun phi => available.delta ∈
                    MissingColors G phi newChoice.vertex) holdColorConstant) hm'
                have holdLeafDegree : @SimpleGraph.degree _
                    (TwoColorIncidenceGraph G
                      (ett.series.data.coloring q.castSucc)
                      available.gamma available.delta)
                    (Sum.inl newChoice.vertex) (Fintype.ofFinite _) ≤ 1 := by
                  have hgraphSwapOrder :
                      TwoColorIncidenceGraph G
                          (ett.series.data.coloring q.castSucc)
                          available.delta available.gamma =
                        TwoColorIncidenceGraph G
                          (ett.series.data.coloring q.castSucc)
                          available.gamma available.delta := by
                    ext x y
                    cases x <;> cases y <;>
                      simp [TwoColorIncidenceGraph, or_comm]
                  rw [← hgraphSwapOrder]
                  exact MissingColorIncidenceEndpoint G
                    (ett.series.data.coloring q.castSucc) available.delta
                    available.gamma hgammaDeltaNe.symm previousProper
                    newChoice.vertex holdDeltaAtNewVertex
                have holdLeaf : Set.Subsingleton
                    ((TwoColorIncidenceGraph G
                      (ett.series.data.coloring q.castSucc)
                      available.gamma available.delta).neighborSet
                        (Sum.inl newChoice.vertex)) := by
                  letI : Fintype
                      ((TwoColorIncidenceGraph G
                        (ett.series.data.coloring q.castSucc)
                        available.gamma available.delta).neighborSet
                          (Sum.inl newChoice.vertex)) := Fintype.ofFinite _
                  rw [← SimpleGraph.card_neighborSet_eq_degree] at holdLeafDegree
                  have hsub := Fintype.card_le_one_iff.mp holdLeafDegree
                  intro a ha b hb
                  exact congrArg Subtype.val (hsub ⟨a, ha⟩ ⟨b, hb⟩)
                have hreturnNeNew : available.returnVertex ≠
                    newChoice.vertex := by
                  intro heq
                  have hsupport : Sum.inl newChoice.vertex ∈
                      available.cycle.walk.support := by
                    rw [← heq]
                    apply available.returnPathOnCycle
                    simp
                  let rotated := available.cycle.walk.rotate
                    (Sum.inl newChoice.vertex) hsupport
                  have hrotated : rotated.IsCycle :=
                    available.cycle.isCycle.rotate hsupport
                  have hfirst : (TwoColorIncidenceGraph G
                      (ett.series.data.coloring q.castSucc)
                      available.gamma available.delta).Adj
                        (Sum.inl newChoice.vertex) rotated.snd :=
                    rotated.adj_snd hrotated.not_nil
                  have hlast : (TwoColorIncidenceGraph G
                      (ett.series.data.coloring q.castSucc)
                      available.gamma available.delta).Adj
                        (Sum.inl newChoice.vertex) rotated.penultimate :=
                    (rotated.adj_penultimate hrotated.not_nil).symm
                  exact hrotated.snd_ne_penultimate (holdLeaf hfirst hlast)
                have hswapGraph : TwoColorIncidenceGraph G
                      (TwoColorComponentSwap G newSecond newGamma
                        newChoice.color (Sum.inl newChoice.vertex))
                      newGamma newChoice.color =
                    TwoColorIncidenceGraph G newSecond newGamma
                      newChoice.color := by
                  ext x y
                  cases x with
                  | inl v =>
                      cases y with
                      | inl w => simp [TwoColorIncidenceGraph]
                      | inr f =>
                          by_cases hf : Sum.inr f ∈ TwoColorComponent G
                              newSecond newGamma newChoice.color
                              (Sum.inl newChoice.vertex)
                          · by_cases hfg : newSecond f = some newGamma
                            · simp [TwoColorIncidenceGraph,
                                TwoColorComponentSwap, hf, hfg]
                            · by_cases hfd : newSecond f = some newChoice.color
                              · simp [TwoColorIncidenceGraph,
                                  TwoColorComponentSwap, hf, hfg, hfd]
                              · simp [TwoColorIncidenceGraph,
                                  TwoColorComponentSwap, hf, hfg, hfd]
                          · simp [TwoColorIncidenceGraph,
                              TwoColorComponentSwap, hf]
                  | inr f =>
                      cases y with
                      | inl v =>
                          by_cases hf : Sum.inr f ∈ TwoColorComponent G
                              newSecond newGamma newChoice.color
                              (Sum.inl newChoice.vertex)
                          · by_cases hfg : newSecond f = some newGamma
                            · simp [TwoColorIncidenceGraph,
                                TwoColorComponentSwap, hf, hfg]
                            · by_cases hfd : newSecond f = some newChoice.color
                              · simp [TwoColorIncidenceGraph,
                                  TwoColorComponentSwap, hf, hfg, hfd]
                              · simp [TwoColorIncidenceGraph,
                                  TwoColorComponentSwap, hf, hfg, hfd]
                          · simp [TwoColorIncidenceGraph,
                              TwoColorComponentSwap, hf]
                      | inr g => simp [TwoColorIncidenceGraph]
                have hsigmaExitGraph : TwoColorIncidenceGraph G sigma
                      available.gamma available.delta =
                    TwoColorIncidenceGraph G newSecond newGamma
                      newChoice.color := by
                  calc
                    TwoColorIncidenceGraph G sigma available.gamma
                        available.delta =
                      TwoColorIncidenceGraph G
                        (corr.replacementSeries.data.coloring newi.succ)
                        available.gamma available.delta :=
                          congrArg (fun phi => TwoColorIncidenceGraph G phi
                            available.gamma available.delta)
                            hnewPostSigma.symm
                    _ = TwoColorIncidenceGraph G
                        (TwoColorComponentSwap G newSecond newGamma
                          newChoice.color (Sum.inl newChoice.vertex))
                        available.gamma available.delta :=
                          congrArg (fun phi => TwoColorIncidenceGraph G phi
                            available.gamma available.delta)
                            newCurrentColoring
                    _ = TwoColorIncidenceGraph G
                        (TwoColorComponentSwap G newSecond newGamma
                          newChoice.color (Sum.inl newChoice.vertex))
                        newGamma newChoice.color := by
                          rw [hnewGammaAvailable, hnewDeltaAvailable]
                    _ = TwoColorIncidenceGraph G newSecond newGamma
                        newChoice.color := hswapGraph
                have hnewGammaSecond : newGamma ∈ MissingColors G newSecond
                    newChoice.vertex := by
                  rw [newSecondStable.2 newChoice.vertex
                    newChoice.vertexDefective.1]
                  exact newGammaRule.1
                have hcomponentOnly := TreeExitComponentMeetsTreeOnlyAtExit
                  (corr.replacementSeries.data.tree newi.succ.castSucc)
                  newSecond newGamma newChoice.color newChoice.vertex
                  newSecondProper hnewGammaSecond newExit
                have hcomponentDistinct :
                    TwoColorComponent G sigma available.gamma available.delta
                        (Sum.inl newChoice.vertex) ≠
                      TwoColorComponent G sigma available.gamma available.delta
                        (Sum.inr available.edge) := by
                  intro heq
                  have hreturnExitSigma : Sum.inl available.returnVertex ∈
                      TwoColorComponent G sigma available.gamma
                        available.delta (Sum.inl newChoice.vertex) := by
                    rw [heq]
                    exact hreturnInQ
                  have hreturnExitSecond : Sum.inl available.returnVertex ∈
                      TwoColorComponent G newSecond newGamma newChoice.color
                        (Sum.inl newChoice.vertex) := by
                    unfold TwoColorComponent at hreturnExitSigma ⊢
                    rw [← hsigmaExitGraph]
                    exact hreturnExitSigma
                  exact hreturnNeNew
                    ((hcomponentOnly available.returnVertex
                      (by simpa only [hnewIndex] using hreturnInNewEarlier)).mp
                        hreturnExitSecond)
                have hQMeetsTn : ∃ v ∈ TreeSequenceVertexSet
                    (ett.series.data.tree (Fin.last ett.rounds).castSucc),
                    Sum.inl v ∈ TwoColorComponent G sigma available.gamma
                      available.delta (Sum.inr available.edge) :=
                  ⟨available.returnVertex, hreturnInTn, hreturnInQ⟩
                have hcorrRoundsPositive : 0 < corr.replacementETT.rounds :=
                  corr.replacementETT.roundsPositive
                have hcorrRoundsLess : corr.replacementETT.rounds <
                    ett.rounds := by
                  rw [corr.rungAgreement, hr]
                  omega
                have correspondingTerminalTree : ∀
                    (C : CorrespondingExtendedTashkinovTree G k e0
                      originalPrefix sigma
                        (ett.series.data.tree
                          (Fin.last ett.rounds).castSucc)),
                    C.replacementETT.series.data.tree
                        (Fin.last (C.replacementETT.rounds + 1)) =
                      C.replacementSeries.data.tree
                        (Fin.last (originalPrefix.rounds + 1)) := by
                  intro C
                  rcases C with ⟨replacementInput, replacementSeries,
                    replacementETT, rungAgreement, seriesPresentation,
                    finalGeneratingColoring, ladderTreesAgree,
                    storedColorsAgree, connectingEdgesAgree,
                    extensionKindsAgree, replacementProper,
                    replacementOneUncolored, replacementStable⟩
                  cases replacementETT with
                  | mk rounds roundsPositive replacementData above strict below
                      generatingColoring =>
                      cases rungAgreement
                      have hseries : replacementData = replacementSeries :=
                        eq_of_heq seriesPresentation
                      cases hseries
                      rfl
                have hseriesTree := correspondingTerminalTree corr
                have hlowerColor :
                    corr.replacementETT.series.data.coloring
                        (Fin.last corr.replacementETT.rounds) = sigma := by
                  exact corr.replacementETT.generatingColoring.symm
                have hstableLower : StableColoring
                    (corr.replacementETT.series.data.tree
                      (Fin.last (corr.replacementETT.rounds + 1)))
                    (TashkinovStoredColors corr.replacementETT.series.data
                      (Fin.last corr.replacementETT.rounds))
                    (corr.replacementETT.series.data.coloring
                      (Fin.last corr.replacementETT.rounds)) sigma := by
                  rw [hlowerColor]
                  exact ⟨(by intros; rfl), (by intros; rfl)⟩
                have hlowerTree : corr.replacementETT.series.data.tree
                      (Fin.last (corr.replacementETT.rounds + 1)) =
                    ett.series.data.tree
                      (Fin.last ett.rounds).castSucc :=
                  hseriesTree.trans hcorrFinalTree
                have hdeltaLower : available.delta ∈ TreeMissingColors sigma
                    (corr.replacementETT.series.data.tree
                      (Fin.last (corr.replacementETT.rounds + 1))) := by
                  simp only [TreeMissingColors, Finset.mem_biUnion]
                  refine ⟨newChoice.vertex, ?_, hnewDeltaSigma⟩
                  rw [hlowerTree]
                  exact hnewVertexTn
                have hlowerPackage := hlower corr.replacementETT
                  hcorrRoundsPositive hcorrRoundsLess hcorrMP
                have hinterchangeLower := hlowerPackage.2.1 sigma
                  hsigmaProper hsigmaOne hstableLower available.gamma
                  available.delta (Or.inr hdeltaLower)
                have hinterchangeTn : TreeInterchangeable G
                    (ett.series.data.tree (Fin.last ett.rounds).castSucc)
                    sigma available.gamma available.delta := by
                  rw [← hlowerTree]
                  exact hinterchangeLower
                have hcycleComponent :=
                  TwoColorInterchangeableDistinctComponentCycle G
                    (ett.series.data.tree (Fin.last ett.rounds).castSucc)
                    sigma available.gamma available.delta hsigmaProper
                    (Sum.inl newChoice.vertex) (Sum.inr available.edge)
                    hpathComponent.1 hinterchangeTn hpathMeetsTn hQMeetsTn
                    hcomponentDistinct
                obtain ⟨replacementCycle, hcycleFull⟩ := hcycleComponent
                have hclosedSigma : ColoredVertexSetClosed G sigma
                    (TreeSequenceVertexSet
                      (ett.series.data.tree q.succ.castSucc)) := by
                  intro f c v hf hv hsf
                  intro hcm
                  obtain ⟨x, hx, y, hy, hends⟩ := by
                    simpa [BoundaryEdges] using hf
                  have hxf : Incident G x f := by
                    unfold Incident
                    rw [hends]
                    exact Sym2.mem_mk_left _ _
                  have hmissingEq := hsigmaPrevStableQ.2 v hv
                  have hcTree : c ∈ TreeMissingColors
                      (ett.series.data.coloring q.castSucc)
                      (ett.series.data.tree q.succ.castSucc) := by
                    simp only [TreeMissingColors, Finset.mem_biUnion]
                    exact ⟨v, hv, hmissingEq ▸ hcm⟩
                  have hcriterion := (sc1 G e0
                    (ett.series.data.tree q.succ.castSucc)
                    (TashkinovStoredColors ett.series.data q.castSucc)
                    (ett.series.data.coloring q.castSucc) sigma
                    previousProper previousOneUncolored hsigmaProper
                    hsigmaOne).mp hsigmaPrevStableQ
                  have hcopy := hcriterion f ⟨x, hx, hxf⟩
                    (Or.inr ⟨c, Finset.mem_union_left _ hcTree, hsf⟩)
                  have holdf : ett.series.data.coloring q.castSucc f =
                      some c := hcopy.symm.trans hsf
                  have hnotOld := previousClosed hf hv holdf
                  exact hnotOld (hmissingEq ▸ hcm)
                have hclosedFinal : ColoredVertexSetClosed G sigma
                    (TreeSequenceVertexSet
                      (ett.series.data.tree
                        (Fin.last ett.rounds).castSucc)) := by
                  rw [← hqSucc]
                  exact hclosedSigma
                have hreplacementCurrentTree :
                    corr.replacementSeries.data.tree replacementLast.succ =
                      ett.series.data.tree
                        (Fin.last ett.rounds).castSucc := by
                  as_aux_lemma =>
                    calc
                      corr.replacementSeries.data.tree replacementLast.succ =
                          corr.replacementSeries.data.tree
                            (Fin.last (originalPrefix.rounds + 1)) := by
                              congr 1
                      _ = ett.series.data.tree
                            (Fin.last ett.rounds).castSucc := hcorrFinalTree
                have havailableCurrentIndex : q.castSucc.succ =
                    (Fin.last ett.rounds).castSucc := by
                  apply Fin.ext
                  have hvals := congrArg Fin.val hqSucc
                  simp only [Fin.val_succ, Fin.val_castSucc] at hvals ⊢
                  exact hvals
                have havailableCurrentTree :
                    ett.series.data.tree q.castSucc.succ =
                      ett.series.data.tree
                        (Fin.last ett.rounds).castSucc := by
                  rw [havailableCurrentIndex]
                let currentTree := TreeSequenceVertexSet
                  (ett.series.data.tree q.succ.castSucc)
                have hreturnCycle : Sum.inl available.returnVertex ∈
                    replacementCycle.walk.support :=
                  (hcycleFull _).2 hreturnInQ
                have houtsideCycle : Sum.inl available.outsideEndpoint ∈
                    replacementCycle.walk.support :=
                  (hcycleFull _).2 houtsideInQ
                have hreturnCurrent : available.returnVertex ∈ currentTree := by
                  simpa [currentTree, hqSucc] using hreturnInTn
                have houtsideNotCurrent : available.outsideEndpoint ∉
                    currentTree := by
                  simpa [currentTree] using available.outsideNotCurrent
                let rootedCycle := replacementCycle.walk.rotate
                  (Sum.inl available.returnVertex) hreturnCycle
                have rootedIsCycle : rootedCycle.IsCycle :=
                  replacementCycle.isCycle.rotate hreturnCycle
                have houtsideRooted : Sum.inl available.outsideEndpoint ∈
                    rootedCycle.support := by
                  apply (replacementCycle.walk.mem_support_rotate_iff
                    (Sum.inl available.returnVertex) hreturnCycle).mpr
                  exact houtsideCycle
                let outsideIndices : Finset
                    (Fin (rootedCycle.length + 1)) :=
                  Finset.univ.filter fun i => ∃ v : V,
                    rootedCycle.getVert i.val = Sum.inl v ∧
                      v ∉ currentTree
                have outsideIndicesNonempty : outsideIndices.Nonempty := by
                  obtain ⟨m, hm, hmle⟩ :=
                    SimpleGraph.Walk.mem_support_iff_exists_getVert.mp
                      houtsideRooted
                  let idx : Fin (rootedCycle.length + 1) := ⟨m, by omega⟩
                  refine ⟨idx, Finset.mem_filter.mpr
                    ⟨Finset.mem_univ _, ?_⟩⟩
                  exact ⟨available.outsideEndpoint,
                    by simpa [idx] using hm, houtsideNotCurrent⟩
                let firstOutside : Fin (rootedCycle.length + 1) :=
                  outsideIndices.min' outsideIndicesNonempty
                obtain ⟨outsideOne, houtsideOneAt, houtsideOneNot⟩ :=
                  (Finset.mem_filter.mp
                    (Finset.min'_mem outsideIndices
                      outsideIndicesNonempty)).2
                have beforeFirstOutside : ∀
                    (idx : Fin (rootedCycle.length + 1)),
                    idx.val < firstOutside.val → ∀ v : V,
                    rootedCycle.getVert idx.val = Sum.inl v →
                      v ∈ currentTree := by
                  intro idx hidx v hv
                  by_contra hvNot
                  have hmem : idx ∈ outsideIndices :=
                    Finset.mem_filter.mpr
                      ⟨Finset.mem_univ _, ⟨v, hv, hvNot⟩⟩
                  have hmin := Finset.min'_le outsideIndices idx hmem
                  omega
                have firstOutsidePositive : 0 < firstOutside.val := by
                  by_contra hnot
                  have hzero : firstOutside.val = 0 := by omega
                  have heq : outsideOne = available.returnVertex := by
                    apply Sum.inl.inj
                    calc
                      Sum.inl outsideOne = rootedCycle.getVert
                          firstOutside.val := houtsideOneAt.symm
                      _ = rootedCycle.getVert 0 := by rw [hzero]
                      _ = Sum.inl available.returnVertex :=
                        rootedCycle.getVert_zero
                  exact houtsideOneNot (heq.symm ▸ hreturnCurrent)
                have firstOutsideLt : firstOutside.val <
                    rootedCycle.length := by
                  by_contra hnot
                  have hlast : firstOutside.val = rootedCycle.length := by
                    have := firstOutside.isLt
                    omega
                  have heq : outsideOne = available.returnVertex := by
                    apply Sum.inl.inj
                    calc
                      Sum.inl outsideOne = rootedCycle.getVert
                          firstOutside.val := houtsideOneAt.symm
                      _ = rootedCycle.getVert rootedCycle.length := by rw [hlast]
                      _ = Sum.inl available.returnVertex :=
                        rootedCycle.getVert_length
                  exact houtsideOneNot (heq.symm ▸ hreturnCurrent)
                have firstOutsideNotOne : firstOutside.val ≠ 1 := by
                  intro hone
                  have hadj := rootedCycle.adj_getVert_succ
                    (i := 0) (by omega)
                  have hy : rootedCycle.getVert 1 = Sum.inl outsideOne := by
                    have hone' :
                        (outsideIndices.min' outsideIndicesNonempty).val = 1 :=
                      hone
                    rw [hone'] at houtsideOneAt
                    exact houtsideOneAt
                  rw [rootedCycle.getVert_zero, hy] at hadj
                  simpa [TwoColorIncidenceGraph] using hadj
                have firstOutsideAtLeastTwo : 2 ≤ firstOutside.val := by omega
                have firstCrossingAdj := rootedCycle.adj_getVert_succ
                  (i := firstOutside.val - 1) (by omega)
                have firstCrossingIndex : firstOutside.val - 1 + 1 =
                    firstOutside.val := by omega
                obtain ⟨firstEdge, hfirstEdgeAt⟩ : ∃ f : E,
                    rootedCycle.getVert (firstOutside.val - 1) =
                      Sum.inr f := by
                  cases hnode : rootedCycle.getVert
                      (firstOutside.val - 1) with
                  | inl v =>
                      exfalso
                      rw [firstCrossingIndex, houtsideOneAt, hnode] at firstCrossingAdj
                      simpa [TwoColorIncidenceGraph] using firstCrossingAdj
                  | inr f => exact ⟨f, rfl⟩
                have hfirstOutsideIncident : Incident G outsideOne firstEdge := by
                  rw [firstCrossingIndex, houtsideOneAt, hfirstEdgeAt] at firstCrossingAdj
                  simpa [TwoColorIncidenceGraph] using firstCrossingAdj.1
                have hfirstEdgeActive : sigma firstEdge =
                      some available.gamma ∨
                    sigma firstEdge = some available.delta := by
                  rw [firstCrossingIndex, houtsideOneAt, hfirstEdgeAt] at firstCrossingAdj
                  simpa [TwoColorIncidenceGraph] using firstCrossingAdj.2
                have beforeFirstCrossingAdj := rootedCycle.adj_getVert_succ
                  (i := firstOutside.val - 2) (by omega)
                have beforeFirstCrossingIndex : firstOutside.val - 2 + 1 =
                    firstOutside.val - 1 := by omega
                obtain ⟨insideOne, hinsideOneAt⟩ : ∃ x : V,
                    rootedCycle.getVert (firstOutside.val - 2) =
                      Sum.inl x := by
                  cases hnode : rootedCycle.getVert
                      (firstOutside.val - 2) with
                  | inl x => exact ⟨x, rfl⟩
                  | inr f =>
                      exfalso
                      rw [beforeFirstCrossingIndex, hfirstEdgeAt, hnode] at beforeFirstCrossingAdj
                      simpa [TwoColorIncidenceGraph] using
                        beforeFirstCrossingAdj
                have hinsideOneCurrent : insideOne ∈ currentTree := by
                  let idx : Fin (rootedCycle.length + 1) :=
                    ⟨firstOutside.val - 2,
                      lt_of_le_of_lt (Nat.sub_le _ _) firstOutside.isLt⟩
                  apply beforeFirstOutside idx (by
                    change firstOutside.val - 2 < firstOutside.val
                    omega) insideOne
                  simpa [idx] using hinsideOneAt
                have hinsideOneIncident : Incident G insideOne firstEdge := by
                  rw [beforeFirstCrossingIndex, hfirstEdgeAt, hinsideOneAt] at beforeFirstCrossingAdj
                  simpa [TwoColorIncidenceGraph] using
                    beforeFirstCrossingAdj.1
                have endpointIdentity : ∀ {f : E} {a b : V},
                    Incident G a f → Incident G b f → a ≠ b →
                      G.ends f = s(a, b) := by
                  intro f a b ha hb hab
                  have endsEq : ∀ {z : Sym2 V} {x y : V},
                      x ∈ z → y ∈ z → x ≠ y → z = s(x, y) := by
                    as_aux_lemma =>
                      intro z x y hx hy hxy
                      induction z using Sym2.inductionOn with
                      | _ u v =>
                          simp only [Sym2.mem_iff] at hx hy
                          rcases hx with rfl | rfl
                          · rcases hy with rfl | rfl
                            · exact (hxy rfl).elim
                            · rfl
                          · rcases hy with rfl | rfl
                            · exact Sym2.eq_swap
                            · exact (hxy rfl).elim
                  exact endsEq ha hb hab
                have hinsideOutsideOne : insideOne ≠ outsideOne := by
                  intro heq
                  exact houtsideOneNot (heq ▸ hinsideOneCurrent)
                have hfirstEnds : G.ends firstEdge =
                    s(insideOne, outsideOne) :=
                  endpointIdentity hinsideOneIncident hfirstOutsideIncident
                    hinsideOutsideOne
                have hfirstBoundary : firstEdge ∈ BoundaryEdges G currentTree := by
                  simp only [BoundaryEdges, Finset.mem_filter,
                    Finset.mem_univ, true_and]
                  exact ⟨insideOne, hinsideOneCurrent, outsideOne,
                    houtsideOneNot, hfirstEnds⟩
                let laterInsideIndices : Finset
                    (Fin (rootedCycle.length + 1)) :=
                  Finset.univ.filter fun idx => firstOutside.val < idx.val ∧
                    ∃ v : V, rootedCycle.getVert idx.val = Sum.inl v ∧
                      v ∈ currentTree
                have laterInsideNonempty : laterInsideIndices.Nonempty := by
                  let idx : Fin (rootedCycle.length + 1) :=
                    ⟨rootedCycle.length, by omega⟩
                  refine ⟨idx, Finset.mem_filter.mpr
                    ⟨Finset.mem_univ _, firstOutsideLt, ?_⟩⟩
                  exact ⟨available.returnVertex,
                    by simpa [idx] using rootedCycle.getVert_length,
                    hreturnCurrent⟩
                let firstReturn : Fin (rootedCycle.length + 1) :=
                  laterInsideIndices.min' laterInsideNonempty
                have hfirstReturnMem := Finset.min'_mem laterInsideIndices
                  laterInsideNonempty
                have hfirstReturnAfter : firstOutside.val < firstReturn.val :=
                  (Finset.mem_filter.mp hfirstReturnMem).2.1
                obtain ⟨insideTwo, hinsideTwoAt, hinsideTwoCurrent⟩ :=
                  (Finset.mem_filter.mp hfirstReturnMem).2.2
                have hreturnNotNext : firstReturn.val ≠
                    firstOutside.val + 1 := by
                  intro heq
                  have hadj := rootedCycle.adj_getVert_succ
                    (i := firstOutside.val) (by omega)
                  rw [houtsideOneAt] at hadj
                  have hnext : rootedCycle.getVert
                      (firstOutside.val + 1) = Sum.inl insideTwo := by
                    have heq' :
                        (laterInsideIndices.min' laterInsideNonempty).val =
                          firstOutside.val + 1 := heq
                    rw [heq'] at hinsideTwoAt
                    exact hinsideTwoAt
                  rw [hnext] at hadj
                  simpa [TwoColorIncidenceGraph] using hadj
                have hreturnGap : firstOutside.val + 2 ≤
                    firstReturn.val := by omega
                have returnCrossingAdj := rootedCycle.adj_getVert_succ
                  (i := firstReturn.val - 1) (by omega)
                have returnCrossingIndex : firstReturn.val - 1 + 1 =
                    firstReturn.val := by omega
                obtain ⟨secondEdge, hsecondEdgeAt⟩ : ∃ f : E,
                    rootedCycle.getVert (firstReturn.val - 1) =
                      Sum.inr f := by
                  cases hnode : rootedCycle.getVert
                      (firstReturn.val - 1) with
                  | inl v =>
                      exfalso
                      rw [returnCrossingIndex, hinsideTwoAt, hnode] at returnCrossingAdj
                      simpa [TwoColorIncidenceGraph] using returnCrossingAdj
                  | inr f => exact ⟨f, rfl⟩
                have hinsideTwoIncident : Incident G insideTwo secondEdge := by
                  rw [returnCrossingIndex, hinsideTwoAt, hsecondEdgeAt] at returnCrossingAdj
                  simpa [TwoColorIncidenceGraph] using returnCrossingAdj.1
                have hsecondEdgeActive : sigma secondEdge =
                      some available.gamma ∨
                    sigma secondEdge = some available.delta := by
                  rw [returnCrossingIndex, hinsideTwoAt, hsecondEdgeAt] at returnCrossingAdj
                  simpa [TwoColorIncidenceGraph] using returnCrossingAdj.2
                have beforeReturnCrossingAdj := rootedCycle.adj_getVert_succ
                  (i := firstReturn.val - 2) (by omega)
                have beforeReturnCrossingIndex : firstReturn.val - 2 + 1 =
                    firstReturn.val - 1 := by omega
                obtain ⟨outsideTwo, houtsideTwoAt⟩ : ∃ y : V,
                    rootedCycle.getVert (firstReturn.val - 2) =
                      Sum.inl y := by
                  cases hnode : rootedCycle.getVert
                      (firstReturn.val - 2) with
                  | inl y => exact ⟨y, rfl⟩
                  | inr f =>
                      exfalso
                      rw [beforeReturnCrossingIndex, hsecondEdgeAt, hnode] at beforeReturnCrossingAdj
                      simpa [TwoColorIncidenceGraph] using
                        beforeReturnCrossingAdj
                have houtsideTwoNot : outsideTwo ∉ currentTree := by
                  intro houtsideTwoCurrent
                  by_cases heq : firstReturn.val - 2 = firstOutside.val
                  · have hvertices : outsideTwo = outsideOne := by
                      apply Sum.inl.inj
                      calc
                        Sum.inl outsideTwo = rootedCycle.getVert
                            (firstReturn.val - 2) := houtsideTwoAt.symm
                        _ = rootedCycle.getVert firstOutside.val := by rw [heq]
                        _ = Sum.inl outsideOne := houtsideOneAt
                    exact houtsideOneNot
                      (hvertices.symm ▸ houtsideTwoCurrent)
                  · have hbetween : firstOutside.val <
                        firstReturn.val - 2 := by omega
                    let idx : Fin (rootedCycle.length + 1) :=
                      ⟨firstReturn.val - 2,
                        lt_of_le_of_lt (Nat.sub_le _ _) firstReturn.isLt⟩
                    have hmem : idx ∈ laterInsideIndices :=
                      Finset.mem_filter.mpr ⟨Finset.mem_univ _,
                        by simpa [idx], outsideTwo, by simpa [idx] using
                          houtsideTwoAt, houtsideTwoCurrent⟩
                    have hmin := Finset.min'_le laterInsideIndices idx hmem
                    have hmin' : firstReturn.val ≤ idx.val := by
                      simpa [firstReturn] using hmin
                    simp [idx] at hmin'
                    omega
                have houtsideTwoIncident : Incident G outsideTwo secondEdge := by
                  rw [beforeReturnCrossingIndex, hsecondEdgeAt,
                    houtsideTwoAt] at beforeReturnCrossingAdj
                  simpa [TwoColorIncidenceGraph] using
                    beforeReturnCrossingAdj.1
                have houtsideInsideTwo : outsideTwo ≠ insideTwo := by
                  intro heq
                  exact houtsideTwoNot (heq ▸ hinsideTwoCurrent)
                have hsecondEnds : G.ends secondEdge =
                    s(insideTwo, outsideTwo) := by
                  rw [Sym2.eq_swap]
                  exact endpointIdentity houtsideTwoIncident
                    hinsideTwoIncident houtsideInsideTwo
                have hsecondBoundary : secondEdge ∈
                    BoundaryEdges G currentTree := by
                  simp only [BoundaryEdges, Finset.mem_filter,
                    Finset.mem_univ, true_and]
                  exact ⟨insideTwo, hinsideTwoCurrent, outsideTwo,
                    houtsideTwoNot, hsecondEnds⟩
                have hcrossingEdgesNe : firstEdge ≠ secondEdge := by
                  intro heq
                  have hp1Positive : 0 < firstOutside.val - 1 := by omega
                  have hp1AtMost : firstOutside.val - 1 ≤
                      rootedCycle.length := by omega
                  have hp2Positive : 0 < firstReturn.val - 1 := by omega
                  have hreturnAtMost : firstReturn.val ≤
                      rootedCycle.length := by
                    exact Nat.lt_succ_iff.mp firstReturn.isLt
                  have hp2AtMost : firstReturn.val - 1 ≤
                      rootedCycle.length :=
                    (Nat.sub_le _ _).trans hreturnAtMost
                  have hindices := rootedIsCycle.getVert_injOn
                    (by
                      simp only [Set.mem_ofPred_eq]
                      exact ⟨hp1Positive, hp1AtMost⟩)
                    (by
                      simp only [Set.mem_ofPred_eq]
                      exact ⟨hp2Positive, hp2AtMost⟩)
                  have hvertices : rootedCycle.getVert
                        (firstOutside.val - 1) =
                      rootedCycle.getVert (firstReturn.val - 1) := by
                    rw [hfirstEdgeAt, hsecondEdgeAt, heq]
                  have := hindices hvertices
                  omega
                have hnewVertexCurrent : newChoice.vertex ∈ currentTree := by
                  simpa [currentTree, hqSucc] using hnewVertexTn
                have hfirstGamma : sigma firstEdge =
                    some available.gamma := by
                  rcases hfirstEdgeActive with hgamma | hdelta
                  · exact hgamma
                  · exfalso
                    exact (hclosedSigma hfirstBoundary hnewVertexCurrent
                      hdelta) hnewDeltaSigma
                have hsecondGamma : sigma secondEdge =
                    some available.gamma := by
                  rcases hsecondEdgeActive with hgamma | hdelta
                  · exact hgamma
                  · exfalso
                    exact (hclosedSigma hsecondBoundary hnewVertexCurrent
                      hdelta) hnewDeltaSigma
                have hnotStrongSigma : ¬ ColoredVertexSetStronglyClosed G sigma
                    currentTree := by
                  intro hstrong
                  exact (hstrong.2 hfirstBoundary hsecondBoundary
                    hcrossingEdgesNe hfirstGamma) hsecondGamma
                have hreplacementColor :
                    corr.replacementSeries.data.coloring replacementLast =
                      sigma := by
                  simpa [replacementLast] using hcorrFinalColor
                let castReturnWalk (phi psi : PartialEdgeColoring E k)
                    (hphi : phi = psi)
                    (P : (TwoColorIncidenceGraph G psi available.gamma
                      available.delta).Walk (Sum.inr available.edge)
                        (Sum.inl available.returnVertex)) :
                    (TwoColorIncidenceGraph G phi available.gamma
                      available.delta).Walk (Sum.inr available.edge)
                        (Sum.inl available.returnVertex) := by
                  subst psi
                  exact P
                have castReturnWalkIsPath : ∀
                    (phi psi : PartialEdgeColoring E k) (hphi : phi = psi)
                    (P : (TwoColorIncidenceGraph G psi available.gamma
                      available.delta).Walk (Sum.inr available.edge)
                        (Sum.inl available.returnVertex)),
                    P.IsPath → (castReturnWalk phi psi hphi P).IsPath := by
                  intro phi psi hphi P hP
                  subst psi
                  exact hP
                have castReturnWalkSupport : ∀
                    (phi psi : PartialEdgeColoring E k) (hphi : phi = psi)
                    (P : (TwoColorIncidenceGraph G psi available.gamma
                      available.delta).Walk (Sum.inr available.edge)
                        (Sum.inl available.returnVertex)) z,
                    z ∈ (castReturnWalk phi psi hphi P).support ↔
                      z ∈ P.support := by
                  intro phi psi hphi P z
                  subst psi
                  rfl
                let castCycle (phi psi : PartialEdgeColoring E k)
                    (hphi : phi = psi)
                    (C : TwoColorCycle G psi available.gamma available.delta) :
                    TwoColorCycle G phi available.gamma available.delta := by
                  subst psi
                  exact C
                have castCycleSupport : ∀
                    (phi psi : PartialEdgeColoring E k) (hphi : phi = psi)
                    (C : TwoColorCycle G psi available.gamma available.delta) z,
                    z ∈ (castCycle phi psi hphi C).walk.support ↔
                      z ∈ C.walk.support := by
                  intro phi psi hphi C z
                  subst psi
                  rfl
                let replacementCycleForPrefix := castCycle
                  (corr.replacementSeries.data.coloring replacementLast) sigma
                  hreplacementColor replacementCycle
                let replacementReturnPath := castReturnWalk
                  (corr.replacementSeries.data.coloring replacementLast) sigma
                  hreplacementColor sigmaReturnPath
                have hsigmaPathInQ : ∀ z,
                    z ∈ sigmaReturnPath.support →
                      z ∈ TwoColorComponent G sigma available.gamma
                        available.delta (Sum.inr available.edge) := by
                  intro z hz
                  obtain ⟨m, hm, hmle⟩ :=
                    SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hz
                  change sigmaReturnGraph.connectedComponentMk z =
                    sigmaReturnGraph.connectedComponentMk
                      (Sum.inr available.edge)
                  rw [← hm]
                  exact (SimpleGraph.ConnectedComponent.sound
                    (sigmaReturnPath.take m).reachable).symm
                have hsigmaPathOnCycle : ∀ z,
                    z ∈ sigmaReturnPath.support →
                      z ∈ replacementCycle.walk.support := by
                  intro z hz
                  exact (hcycleFull z).2 (hsigmaPathInQ z hz)
                let replacementCertificate : RevisitingExtensionCertificate
                    corr.replacementSeries.data replacementLast := {
                  earlier := earlierPrefix
                  earlierPositive := hearlierPositive
                  earlierAtMost := by
                    simp [earlierPrefix, replacementLast]
                    have hle := available.earlierAtMost
                    simp [q] at hle
                    omega
                  earlierPE := hreplacementEarlierKind
                  interveningRevisiting := by
                    intro j hjPositive hjLower hjUpper
                    rw [corr.extensionKindsAgree j,
                      (hprefixData j).2.2.2.1]
                    apply available.interveningRevisiting
                      (Fin.castLE (by omega) j)
                    · exact hjPositive
                    · have hvals := congrArg Fin.val hearlierMap
                      simp only [Fin.val_castLE] at hvals ⊢
                      omega
                    · simp only [Fin.val_castLE]
                      have hupper := hjUpper
                      simp [replacementLast] at hupper
                      have hqval : q.castSucc.val =
                          originalPrefix.rounds := by simp [q, hr]
                      omega
                  gamma := available.gamma
                  delta := available.delta
                  earlierGamma := by
                    rw [← hnewIndex, newCurrentGamma, hnewGammaAvailable]
                  earlierDelta := by
                    rw [← hnewIndex, newCurrentDelta, hnewDeltaAvailable]
                  cycle := replacementCycleForPrefix
                  meetsEarlier := by
                    refine ⟨available.returnVertex, hreturnInNewEarlier, ?_⟩
                    exact (castCycleSupport _ _ hreplacementColor
                      replacementCycle _).2 hreturnCycle
                  leavesCurrent := by
                    refine ⟨available.outsideEndpoint, ?_, ?_⟩
                    · rw [hreplacementCurrentTree, ← havailableCurrentTree]
                      exact available.outsideNotCurrent
                    · exact (castCycleSupport _ _ hreplacementColor
                        replacementCycle _).2 houtsideCycle
                  edge := available.edge
                  edgeOnCycle := (castCycleSupport _ _ hreplacementColor
                    replacementCycle _).2 ((hcycleFull _).2 rfl)
                  edgeBoundary := by
                    rw [hreplacementCurrentTree, ← havailableCurrentTree]
                    exact available.edgeBoundary
                  insideEndpoint := available.insideEndpoint
                  outsideEndpoint := available.outsideEndpoint
                  insideInCurrent := by
                    rw [hreplacementCurrentTree, ← havailableCurrentTree]
                    exact available.insideInCurrent
                  outsideNotCurrent := by
                    rw [hreplacementCurrentTree, ← havailableCurrentTree]
                    exact available.outsideNotCurrent
                  edgeEnds := available.edgeEnds
                  returnVertex := available.returnVertex
                  returnInEarlier := hreturnInNewEarlier
                  returnPath := replacementReturnPath
                  returnPathIsPath := castReturnWalkIsPath _ _
                    hreplacementColor sigmaReturnPath hsigmaReturnIsPath
                  returnPathOnCycle := by
                    intro z hz
                    apply (castCycleSupport _ _ hreplacementColor
                      replacementCycle _).2
                    apply hsigmaPathOnCycle
                    exact (castReturnWalkSupport _ _ hreplacementColor
                      sigmaReturnPath z).1 hz
                  returnPathInternal := by
                    intro v hv
                    have hvOld : Sum.inl v ∈
                        available.returnPath.support :=
                      (hsigmaReturnSupport (Sum.inl v)).mp
                        ((castReturnWalkSupport _ _ hreplacementColor
                          sigmaReturnPath _).1 hv)
                    rw [hreplacementCurrentTree, ← havailableCurrentTree]
                    exact available.returnPathInternal v hvOld
                }
                have hfstar : fstar = available.edge := by
                  have hcurrentEdgesFinal :
                      ett.series.data.connectingEdges (Fin.last ett.rounds) =
                        {available.edge} := by
                    rw [← hqSucc]
                    exact currentEdges
                  apply Finset.mem_singleton.mp
                  rw [← hcurrentEdgesFinal, hfinalEdges]
                  exact Finset.mem_singleton_self fstar
                let newStored : Finset (Fin k) :=
                  {available.delta, available.gamma}
                let newEdges : Finset E := {available.edge}
                let newKind : Option TashkinovExtensionKind :=
                  some TashkinovExtensionKind.RE
                let newVertex : Option V := some available.insideEndpoint
                let newOutside : Option V := some available.outsideEndpoint
                let newDelta : Option (Fin k) := some available.delta
                let newGamma : Option (Fin k) := some available.gamma
                let appendedData := TashkinovSeriesDataAppend
                  corr.replacementSeries.data closureTree sigma newStored
                  newEdges newKind newVertex newOutside newDelta newGamma
                obtain ⟨appendedCertificate, happGamma, happDelta, happEdge,
                    happInside, happOutside⟩ :=
                  (RevisitingExtensionCertificateAppend
                    corr.replacementSeries.data closureTree sigma newStored
                    newEdges newKind newVertex newOutside newDelta newGamma
                    replacementLast).2 replacementCertificate
                have hstrictClosure :
                    (ett.series.data.tree
                        (Fin.last ett.rounds).castSucc).length <
                      closureTree.length :=
                  lt_of_lt_of_le hstrict hTstarClosure.1
                have lastStep : TashkinovSeriesStep G k
                    (originalPrefix.rounds + 1) e0 corr.replacementInput
                    appendedData (Fin.last (originalPrefix.rounds + 1)) := by
                  have hlast : replacementLast.succ =
                      Fin.last (originalPrefix.rounds + 1) := by
                    apply Fin.ext
                    simp [replacementLast]
                  have hclosedReplacement : ColoredVertexSetClosed G sigma
                      (TreeSequenceVertexSet
                        (corr.replacementSeries.data.tree
                          (Fin.last (originalPrefix.rounds + 1)))) := by
                    rw [hcorrFinalTree]
                    exact hclosedFinal
                  rw [← hlast]
                  apply TashkinovSeriesStep.RE (i := replacementLast)
                    (available := appendedCertificate) (adjoined := seed)
                  · simpa [appendedData, TashkinovSeriesDataAppend,
                      hlast, replacementLast, hreplacementColor] using hsigmaProper
                  · simpa [appendedData, TashkinovSeriesDataAppend,
                      hlast, replacementLast, hreplacementColor] using hsigmaOne
                  · simp only [TashkinovSeriesDataAppend,
                      Fin.lastCases_castSucc]
                    change ColoredVertexSetClosed G
                      (corr.replacementSeries.data.coloring replacementLast)
                      (TreeSequenceVertexSet
                        (corr.replacementSeries.data.tree replacementLast.succ))
                    rw [hreplacementColor, hlast]
                    intro f c v hf hv hsf hcm
                    obtain ⟨x, hx, y, hy, hends⟩ := by
                      simpa [BoundaryEdges] using hf
                    have htreeEq : TreeSequenceVertexSet
                          (corr.replacementSeries.data.tree
                            (Fin.last (originalPrefix.rounds + 1))) =
                        TreeSequenceVertexSet
                          (ett.series.data.tree q.succ.castSucc) := by
                      rw [hcorrFinalTree, hqSucc]
                    have hxOld : x ∈ TreeSequenceVertexSet
                        (ett.series.data.tree q.succ.castSucc) := by
                      rw [← htreeEq]
                      exact hx
                    have hyOld : y ∉ TreeSequenceVertexSet
                        (ett.series.data.tree q.succ.castSucc) := by
                      rw [← htreeEq]
                      exact hy
                    have hfOld : f ∈ BoundaryEdges G
                        (TreeSequenceVertexSet
                          (ett.series.data.tree q.succ.castSucc)) := by
                      simp only [BoundaryEdges, Finset.mem_filter,
                        Finset.mem_univ, true_and]
                      exact ⟨x, hxOld, y, hyOld, hends⟩
                    have hvOld : v ∈ TreeSequenceVertexSet
                        (ett.series.data.tree q.succ.castSucc) := by
                      rw [← htreeEq]
                      exact hv
                    have hxf : Incident G x f := by
                      unfold Incident
                      rw [hends]
                      exact Sym2.mem_mk_left _ _
                    have hmissingEq := hsigmaPrevStableQ.2 v hvOld
                    have hcTree : c ∈ TreeMissingColors
                        (ett.series.data.coloring q.castSucc)
                        (ett.series.data.tree q.succ.castSucc) := by
                      simp only [TreeMissingColors, Finset.mem_biUnion]
                      exact ⟨v, hvOld, hmissingEq ▸ hcm⟩
                    have hcriterion := (sc1 G e0
                      (ett.series.data.tree q.succ.castSucc)
                      (TashkinovStoredColors ett.series.data q.castSucc)
                      (ett.series.data.coloring q.castSucc) sigma
                      previousProper previousOneUncolored hsigmaProper
                      hsigmaOne).mp hsigmaPrevStableQ
                    have hcopy := hcriterion f ⟨x, hxOld, hxf⟩
                      (Or.inr ⟨c, Finset.mem_union_left _ hcTree, hsf⟩)
                    have holdf : ett.series.data.coloring q.castSucc f =
                        some c := hcopy.symm.trans hsf
                    have hnotOld := previousClosed hfOld hvOld holdf
                    exact hnotOld (hmissingEq ▸ hcm)
                  · simpa [appendedData, TashkinovSeriesDataAppend,
                      hlast, replacementLast, hreplacementColor,
                      hcorrFinalTree, currentTree, hqSucc] using
                      hnotStrongSigma
                  · simp [appendedData, TashkinovSeriesDataAppend,
                      hlast, replacementLast, hreplacementColor]
                  · simp [appendedData, TashkinovSeriesDataAppend, newStored,
                      hlast, replacementCertificate, happDelta, happGamma]
                  · simp [appendedData, TashkinovSeriesDataAppend, newEdges,
                      hlast, replacementCertificate, happEdge]
                  · simp [appendedData, TashkinovSeriesDataAppend, hlast, newKind]
                  · simp [appendedData, TashkinovSeriesDataAppend, newVertex,
                      hlast, replacementCertificate, happInside]
                  · simp [appendedData, TashkinovSeriesDataAppend, newOutside,
                      hlast, replacementCertificate, happOutside]
                  · simp [appendedData, TashkinovSeriesDataAppend, newDelta,
                      hlast, replacementCertificate, happDelta]
                  · simp [appendedData, TashkinovSeriesDataAppend, newGamma,
                      hlast, replacementCertificate, happGamma]
                  · simpa [appendedData, TashkinovSeriesDataAppend,
                      hlast, replacementLast, hcorrFinalTree, hfstar,
                      replacementCertificate, happEdge] using hadjoin
                  · simpa [appendedData, TashkinovSeriesDataAppend, hlast] using
                      hseedClosure
                  · simpa [appendedData, TashkinovSeriesDataAppend,
                      hlast, replacementLast, hcorrFinalTree] using hTnClosure
                  · simpa [appendedData, TashkinovSeriesDataAppend,
                      hlast, replacementLast, hcorrFinalTree] using
                      hstrictClosure
                obtain ⟨extendedSeries, hextendedData⟩ :=
                  TashkinovSeriesAppend G k originalPrefix.rounds e0
                    corr.replacementInput corr.replacementSeries closureTree
                    sigma newStored newEdges newKind newVertex newOutside
                    newDelta newGamma lastStep
                have hroundsEq : originalPrefix.rounds + 1 = ett.rounds := by
                  rw [hr]
                  omega
                let castSeries {a b : ℕ} (h : a = b)
                    (S : TashkinovSeries G k a e0 corr.replacementInput) :
                    TashkinovSeries G k b e0 corr.replacementInput := by
                  subst b
                  exact S
                have castSeriesTree : ∀ {a b : ℕ} (h : a = b)
                    (S : TashkinovSeries G k a e0 corr.replacementInput)
                    (i : Fin (b + 2)),
                    (castSeries h S).data.tree i =
                      S.data.tree
                        (Fin.cast (congrArg (fun m : ℕ => m + 2) h.symm) i) := by
                  intro a b h S i
                  subst b
                  rfl
                have castSeriesColoring : ∀ {a b : ℕ} (h : a = b)
                    (S : TashkinovSeries G k a e0 corr.replacementInput)
                    (i : Fin (b + 1)),
                    (castSeries h S).data.coloring i =
                      S.data.coloring
                        (Fin.cast (congrArg (fun m : ℕ => m + 1) h.symm) i) := by
                  intro a b h S i
                  subst b
                  rfl
                have castSeriesStored : ∀ {a b : ℕ} (h : a = b)
                    (S : TashkinovSeries G k a e0 corr.replacementInput)
                    (i : Fin (b + 1)),
                    (castSeries h S).data.stored i =
                      S.data.stored
                        (Fin.cast (congrArg (fun m : ℕ => m + 1) h.symm) i) := by
                  intro a b h S i
                  subst b
                  rfl
                have castSeriesEdges : ∀ {a b : ℕ} (h : a = b)
                    (S : TashkinovSeries G k a e0 corr.replacementInput)
                    (i : Fin (b + 1)),
                    (castSeries h S).data.connectingEdges i =
                      S.data.connectingEdges
                        (Fin.cast (congrArg (fun m : ℕ => m + 1) h.symm) i) := by
                  intro a b h S i
                  subst b
                  rfl
                have castSeriesKind : ∀ {a b : ℕ} (h : a = b)
                    (S : TashkinovSeries G k a e0 corr.replacementInput)
                    (i : Fin (b + 1)),
                    (castSeries h S).data.kind i =
                      S.data.kind
                        (Fin.cast (congrArg (fun m : ℕ => m + 1) h.symm) i) := by
                  intro a b h S i
                  subst b
                  rfl
                let finalSeries : TashkinovSeries G k ett.rounds e0
                    corr.replacementInput :=
                  castSeries hroundsEq extendedSeries
                let rawPenultimate : Fin (originalPrefix.rounds + 3) :=
                  Fin.cast
                    (congrArg (fun m : ℕ => m + 2) hroundsEq.symm)
                    (⟨ett.rounds, by omega⟩ : Fin (ett.rounds + 2))
                have hrawPenultimate : rawPenultimate =
                    replacementLast.succ.castSucc := by
                  apply Fin.ext
                  simp [rawPenultimate, replacementLast]
                  omega
                have hfinalPenultimateTree : finalSeries.data.tree
                      (⟨ett.rounds, by omega⟩ : Fin (ett.rounds + 2)) =
                    ett.series.data.tree
                      (Fin.last ett.rounds).castSucc := by
                  calc
                    finalSeries.data.tree
                          (⟨ett.rounds, by omega⟩ : Fin (ett.rounds + 2)) =
                        extendedSeries.data.tree rawPenultimate := by
                          exact castSeriesTree hroundsEq extendedSeries _
                    _ = appendedData.tree rawPenultimate := by
                          rw [hextendedData]
                    _ = corr.replacementSeries.data.tree
                          replacementLast.succ := by
                          rw [hrawPenultimate]
                          simp only [appendedData,
                            TashkinovSeriesDataAppend]
                          exact Fin.lastCases_castSucc replacementLast.succ
                    _ = ett.series.data.tree
                          (Fin.last ett.rounds).castSucc :=
                      hreplacementCurrentTree
                let rawFinalTree : Fin (originalPrefix.rounds + 3) :=
                  Fin.cast
                    (congrArg (fun m : ℕ => m + 2) hroundsEq.symm)
                    (Fin.last (ett.rounds + 1))
                have hrawFinalTree : rawFinalTree =
                    Fin.last (originalPrefix.rounds + 2) := by
                  apply Fin.ext
                  simp [rawFinalTree]
                have hfinalTree : finalSeries.data.tree
                      (Fin.last (ett.rounds + 1)) = closureTree := by
                  calc
                    finalSeries.data.tree (Fin.last (ett.rounds + 1)) =
                        extendedSeries.data.tree rawFinalTree := by
                          exact castSeriesTree hroundsEq extendedSeries _
                    _ = appendedData.tree rawFinalTree := by rw [hextendedData]
                    _ = closureTree := by
                      rw [hrawFinalTree]
                      simp [appendedData, TashkinovSeriesDataAppend]
                let rawFinalColor : Fin (originalPrefix.rounds + 2) :=
                  Fin.cast
                    (congrArg (fun m : ℕ => m + 1) hroundsEq.symm)
                    (Fin.last ett.rounds)
                have hrawFinalColor : rawFinalColor =
                    Fin.last (originalPrefix.rounds + 1) := by
                  apply Fin.ext
                  simp [rawFinalColor]
                have hfinalColor : finalSeries.data.coloring
                      (Fin.last ett.rounds) = sigma := by
                  calc
                    finalSeries.data.coloring (Fin.last ett.rounds) =
                        extendedSeries.data.coloring rawFinalColor := by
                          exact castSeriesColoring hroundsEq extendedSeries _
                    _ = appendedData.coloring rawFinalColor := by
                      rw [hextendedData]
                    _ = sigma := by
                      rw [hrawFinalColor]
                      simp [appendedData, TashkinovSeriesDataAppend]
                let rawDataIndex (i : Fin (ett.rounds + 1)) :
                    Fin (originalPrefix.rounds + 2) :=
                  Fin.cast
                    (congrArg (fun m : ℕ => m + 1) hroundsEq.symm) i
                have hseriesDataAgree : ∀ i : Fin (ett.rounds + 1),
                    finalSeries.data.stored i = ett.series.data.stored i ∧
                    finalSeries.data.connectingEdges i =
                      ett.series.data.connectingEdges i ∧
                    finalSeries.data.kind i = ett.series.data.kind i := by
                  intro i
                  by_cases hi : i.val < ett.rounds
                  · let j : Fin (originalPrefix.rounds + 1) :=
                      ⟨i.val, by rw [hroundsEq]; exact hi⟩
                    have hraw : rawDataIndex i = j.castSucc := by
                      apply Fin.ext
                      rfl
                    have hmap : Fin.castLE (by omega) j = i := by
                      apply Fin.ext
                      rfl
                    constructor
                    · calc
                        finalSeries.data.stored i =
                            extendedSeries.data.stored (rawDataIndex i) := by
                              exact castSeriesStored hroundsEq extendedSeries i
                        _ = appendedData.stored (rawDataIndex i) := by
                              rw [hextendedData]
                        _ = corr.replacementSeries.data.stored j := by
                              rw [hraw]
                              simp [appendedData, TashkinovSeriesDataAppend]
                        _ = originalPrefix.series.data.stored j :=
                              corr.storedColorsAgree j
                        _ = ett.series.data.stored (Fin.castLE (by omega) j) :=
                              (hprefixData j).2.1
                        _ = ett.series.data.stored i := by rw [hmap]
                    · constructor
                      · calc
                          finalSeries.data.connectingEdges i =
                              extendedSeries.data.connectingEdges
                                (rawDataIndex i) := by
                                  exact castSeriesEdges hroundsEq
                                    extendedSeries i
                          _ = appendedData.connectingEdges
                                (rawDataIndex i) := by rw [hextendedData]
                          _ = corr.replacementSeries.data.connectingEdges j := by
                                rw [hraw]
                                simp [appendedData,
                                  TashkinovSeriesDataAppend]
                          _ = originalPrefix.series.data.connectingEdges j :=
                                corr.connectingEdgesAgree j
                          _ = ett.series.data.connectingEdges
                                (Fin.castLE (by omega) j) :=
                                (hprefixData j).2.2.1
                          _ = ett.series.data.connectingEdges i := by rw [hmap]
                      · calc
                          finalSeries.data.kind i =
                              extendedSeries.data.kind (rawDataIndex i) := by
                                exact castSeriesKind hroundsEq extendedSeries i
                          _ = appendedData.kind (rawDataIndex i) := by
                                rw [hextendedData]
                          _ = corr.replacementSeries.data.kind j := by
                                rw [hraw]
                                simp [appendedData,
                                  TashkinovSeriesDataAppend]
                          _ = originalPrefix.series.data.kind j :=
                                corr.extensionKindsAgree j
                          _ = ett.series.data.kind
                                (Fin.castLE (by omega) j) :=
                                (hprefixData j).2.2.2.1
                          _ = ett.series.data.kind i := by rw [hmap]
                  · have hilast : i = Fin.last ett.rounds := by
                      apply Fin.ext
                      simp
                      omega
                    subst i
                    have hraw : rawDataIndex (Fin.last ett.rounds) =
                        Fin.last (originalPrefix.rounds + 1) := by
                      apply Fin.ext
                      simp [rawDataIndex]
                    constructor
                    · calc
                        finalSeries.data.stored (Fin.last ett.rounds) =
                            extendedSeries.data.stored
                              (rawDataIndex (Fin.last ett.rounds)) := by
                              exact castSeriesStored hroundsEq extendedSeries _
                        _ = appendedData.stored
                              (rawDataIndex (Fin.last ett.rounds)) := by
                              rw [hextendedData]
                        _ = newStored := by
                              rw [hraw]
                              simp [appendedData, TashkinovSeriesDataAppend]
                        _ = {available.delta, available.gamma} := rfl
                        _ = ett.series.data.stored (Fin.last ett.rounds) := by
                              rw [← hqSucc]
                              exact currentStored.symm
                    · constructor
                      · calc
                          finalSeries.data.connectingEdges
                                (Fin.last ett.rounds) =
                              extendedSeries.data.connectingEdges
                                (rawDataIndex (Fin.last ett.rounds)) := by
                                  exact castSeriesEdges hroundsEq
                                    extendedSeries _
                          _ = appendedData.connectingEdges
                                (rawDataIndex (Fin.last ett.rounds)) := by
                                  rw [hextendedData]
                          _ = newEdges := by
                                  rw [hraw]
                                  simp [appendedData,
                                    TashkinovSeriesDataAppend]
                          _ = {available.edge} := rfl
                          _ = ett.series.data.connectingEdges
                                (Fin.last ett.rounds) := by
                                  rw [← hqSucc]
                                  exact currentEdges.symm
                      · calc
                          finalSeries.data.kind (Fin.last ett.rounds) =
                              extendedSeries.data.kind
                                (rawDataIndex (Fin.last ett.rounds)) := by
                                  exact castSeriesKind hroundsEq extendedSeries _
                          _ = appendedData.kind
                                (rawDataIndex (Fin.last ett.rounds)) := by
                                  rw [hextendedData]
                          _ = newKind := by
                                  rw [hraw]
                                  simp [appendedData,
                                    TashkinovSeriesDataAppend]
                          _ = some TashkinovExtensionKind.RE := rfl
                          _ = ett.series.data.kind
                                (Fin.last ett.rounds) := by
                                  rw [← hqSucc]
                                  exact currentKind.symm
                let rawTreeIndex (i : Fin (ett.rounds + 2)) :
                    Fin (originalPrefix.rounds + 3) :=
                  Fin.cast
                    (congrArg (fun m : ℕ => m + 2) hroundsEq.symm) i
                have hseriesTreeAgree : ∀ i : Fin ett.rounds,
                    finalSeries.data.tree i.succ.castSucc =
                      ett.series.data.tree i.succ.castSucc := by
                  intro i
                  by_cases hi : i.val < originalPrefix.rounds
                  · let j : Fin originalPrefix.rounds := ⟨i.val, hi⟩
                    have hraw : rawTreeIndex i.succ.castSucc =
                        j.succ.castSucc.castSucc := by
                      apply Fin.ext
                      rfl
                    have hmap : Fin.castLE (by omega) j.succ.castSucc =
                        i.succ.castSucc := by
                      apply Fin.ext
                      rfl
                    calc
                      finalSeries.data.tree i.succ.castSucc =
                          extendedSeries.data.tree
                            (rawTreeIndex i.succ.castSucc) := by
                            exact castSeriesTree hroundsEq extendedSeries _
                      _ = appendedData.tree
                            (rawTreeIndex i.succ.castSucc) := by
                            rw [hextendedData]
                      _ = corr.replacementSeries.data.tree
                            j.succ.castSucc := by
                            rw [hraw]
                            simp only [appendedData,
                              TashkinovSeriesDataAppend]
                            convert (Fin.lastCases_castSucc
                              j.succ.castSucc) using 1 <;>
                                apply Fin.ext <;> rfl
                      _ = originalPrefix.series.data.tree
                            j.succ.castSucc := corr.ladderTreesAgree j
                      _ = ett.series.data.tree
                            (Fin.castLE (by omega) j.succ.castSucc) :=
                            hprefixTrees j.succ.castSucc
                      _ = ett.series.data.tree i.succ.castSucc := by rw [hmap]
                  · let ilast : Fin ett.rounds :=
                      ⟨ett.rounds - 1, by omega⟩
                    have hilast : i = ilast := by
                      apply Fin.ext
                      have hiBound := i.isLt
                      have hprefixRounds := hr
                      simp [ilast]
                      omega
                    rw [hilast]
                    have hindex :
                        ilast.succ.castSucc =
                          (Fin.last ett.rounds).castSucc := by
                      apply Fin.ext
                      simp [ilast]
                      omega
                    rw [hindex]
                    exact hfinalPenultimateTree
                have hseriesColorProperties : ∀ i : Fin (ett.rounds + 1),
                    IsProperEdgeColoring G (finalSeries.data.coloring i) ∧
                      IsOneEdgeUncolored (finalSeries.data.coloring i) e0 := by
                  intro i
                  by_cases hi : i.val < ett.rounds
                  · let j : Fin (originalPrefix.rounds + 1) :=
                      ⟨i.val, by rw [hroundsEq]; exact hi⟩
                    have hraw : rawDataIndex i = j.castSucc := by
                      apply Fin.ext
                      rfl
                    have hcolor : finalSeries.data.coloring i =
                        corr.replacementSeries.data.coloring j := by
                      calc
                        finalSeries.data.coloring i =
                            extendedSeries.data.coloring (rawDataIndex i) := by
                              exact castSeriesColoring hroundsEq
                                extendedSeries i
                        _ = appendedData.coloring (rawDataIndex i) := by
                              rw [hextendedData]
                        _ = corr.replacementSeries.data.coloring j := by
                              rw [hraw]
                              simp [appendedData, TashkinovSeriesDataAppend]
                    rw [hcolor]
                    exact ⟨corr.replacementProper j,
                      corr.replacementOneUncolored j⟩
                  · have hilast : i = Fin.last ett.rounds := by
                      apply Fin.ext
                      simp
                      have hiBound := i.isLt
                      omega
                    rw [hilast, hfinalColor]
                    exact ⟨hsigmaProper, hsigmaOne⟩
                have hseriesStable : ∀ i : Fin ett.rounds,
                    StableColoring
                      (ett.series.data.tree i.succ.castSucc)
                      (TashkinovStoredColors ett.series.data i.succ)
                      (ett.series.data.coloring i.succ)
                      (finalSeries.data.coloring i.succ) := by
                  intro i
                  by_cases hi : i.val < originalPrefix.rounds
                  · let j : Fin originalPrefix.rounds := ⟨i.val, hi⟩
                    have hmap : Fin.castLE (by omega) j.succ = i.succ := by
                      apply Fin.ext
                      rfl
                    have htreeMap : Fin.castLE (by omega)
                        j.succ.castSucc = i.succ.castSucc := by
                      apply Fin.ext
                      rfl
                    have htreeEq : originalPrefix.series.data.tree
                          j.succ.castSucc =
                        ett.series.data.tree i.succ.castSucc := by
                      calc
                        originalPrefix.series.data.tree j.succ.castSucc =
                            ett.series.data.tree
                              (Fin.castLE (by omega) j.succ.castSucc) :=
                          hprefixTrees j.succ.castSucc
                        _ = ett.series.data.tree i.succ.castSucc := by
                          rw [htreeMap]
                    have hstoredEq : TashkinovStoredColors
                          originalPrefix.series.data j.succ =
                        TashkinovStoredColors ett.series.data i.succ := by
                      calc
                        TashkinovStoredColors originalPrefix.series.data
                            j.succ =
                            TashkinovStoredColors ett.series.data
                              (Fin.castLE (by omega) j.succ) :=
                          (hprefixData j.succ).2.2.2.2
                        _ = TashkinovStoredColors ett.series.data i.succ := by
                          rw [hmap]
                    have holdColorEq : originalPrefix.series.data.coloring
                          j.succ = ett.series.data.coloring i.succ := by
                      calc
                        originalPrefix.series.data.coloring j.succ =
                            ett.series.data.coloring
                              (Fin.castLE (by omega) j.succ) :=
                          (hprefixData j.succ).1
                        _ = ett.series.data.coloring i.succ := by rw [hmap]
                    have hraw : rawDataIndex i.succ =
                        j.succ.castSucc := by
                      apply Fin.ext
                      rfl
                    have hnewColorEq : finalSeries.data.coloring i.succ =
                        corr.replacementSeries.data.coloring j.succ := by
                      calc
                        finalSeries.data.coloring i.succ =
                            extendedSeries.data.coloring
                              (rawDataIndex i.succ) := by
                              exact castSeriesColoring hroundsEq
                                extendedSeries i.succ
                        _ = appendedData.coloring
                              (rawDataIndex i.succ) := by rw [hextendedData]
                        _ = corr.replacementSeries.data.coloring j.succ := by
                              rw [hraw]
                              simp only [appendedData,
                                TashkinovSeriesDataAppend]
                              exact Fin.lastCases_castSucc j.succ
                    have hstable := corr.replacementStable j
                    rw [htreeEq, hstoredEq, holdColorEq] at hstable
                    rw [hnewColorEq]
                    exact hstable
                  · let ilast : Fin ett.rounds :=
                      ⟨ett.rounds - 1, by omega⟩
                    have hilast : i = ilast := by
                      apply Fin.ext
                      have hiBound := i.isLt
                      have hprefixRounds := hr
                      simp [ilast]
                      omega
                    have hindex : ilast.succ = Fin.last ett.rounds := by
                      apply Fin.ext
                      simp [ilast]
                      omega
                    rw [hilast, hindex, hfinalColor]
                    exact hsigmaStable
                let replacementETT : ExtendedTashkinovTree G k e0
                    corr.replacementInput Tstar sigma := {
                  rounds := ett.rounds
                  roundsPositive := ett.roundsPositive
                  series := finalSeries
                  abovePenultimate := by
                    rw [hfinalPenultimateTree]
                    exact hTnTstar
                  strictAbovePenultimate := by
                    rw [hfinalPenultimateTree]
                    exact hstrict
                  belowFinal := by
                    rw [hfinalTree]
                    exact hTstarClosure
                  generatingColoring := hfinalColor.symm
                }
                refine ⟨{
                  replacementInput := corr.replacementInput
                  replacementSeries := finalSeries
                  replacementETT := replacementETT
                  rungAgreement := rfl
                  seriesPresentation := by dsimp [replacementETT]; rfl
                  finalGeneratingColoring := hfinalColor.symm
                  ladderTreesAgree := hseriesTreeAgree
                  storedColorsAgree := fun i => (hseriesDataAgree i).1
                  connectingEdgesAgree := fun i => (hseriesDataAgree i).2.1
                  extensionKindsAgree := fun i => (hseriesDataAgree i).2.2
                  replacementProper := fun i =>
                    (hseriesColorProperties i).1
                  replacementOneUncolored := fun i =>
                    (hseriesColorProperties i).2
                  replacementStable := hseriesStable
                }⟩
