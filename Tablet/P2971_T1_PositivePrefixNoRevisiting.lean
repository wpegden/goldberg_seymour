import Tablet.CertifiedETTRestriction
import Tablet.CorrespondingExtendedTashkinovTree
import Tablet.ExtendedTashkinovTree
import Tablet.MaximumDefectiveChoice
import Tablet.MaximumProperty
import Tablet.MissingColorIncidenceEndpoint
import Tablet.ParallelExtensionColor
import Tablet.PresentColors
import Tablet.RevisitingExtensionCertificate
import Tablet.StableColoring
import Tablet.TashkinovSeries
import Tablet.TashkinovSeriesStep
import Tablet.TashkinovStoredColors
import Tablet.TdEarlierPEWitnessIdentification
import Tablet.TreeInterchangeable
import Tablet.TreeMissingColors
import Tablet.TreeSequenceInitialSegment
import Tablet.TreeSequenceInitialSegmentVertexSetSubset
import Tablet.TwoColorComponent
import Tablet.TwoColorComponentSwap
import Tablet.TwoColorComponentSwapMissingBehavior
import Tablet.TwoColorCycle
import Tablet.TwoColorIncidenceDegreeAtMostTwo
import Tablet.TwoColorIncidenceGraph
import Tablet.TwoColorInterchangeableDistinctComponentCycle
import Tablet.TwoColorNontrivialPathComponent
import Tablet.TwoColorPathComponent
import Tablet.sc1

set_option maxHeartbeats 800000

-- [TABLET NODE: P2971_T1_PositivePrefixNoRevisiting]
theorem P2971_T1_PositivePrefixNoRevisiting {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (generating : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T generating)
    (hMP : MaximumProperty ett) (hroundLarge : 1 < ett.rounds)
    (hlower : ∀ {input' : PartialEdgeColoring E k}
      {T' : TreeSequence G e0} {generating' : PartialEdgeColoring E k}
      (lower : ExtendedTashkinovTree G k e0 input' T' generating'),
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
           TreeInterchangeable G Tnext sigma alpha beta) ∧
      (let n : Fin (lower.rounds + 1) := Fin.last lower.rounds
       let Tn : TreeSequence G e0 := lower.series.data.tree n.castSucc
       ∀ (v : V) (gamma delta : Fin k),
         lower.series.data.kind n = some TashkinovExtensionKind.PE →
         lower.series.data.chosenVertex n = some v →
         lower.series.data.gamma n = some gamma →
         lower.series.data.delta n = some delta →
         ∀ sigma : PartialEdgeColoring E k,
           IsProperEdgeColoring G sigma → IsOneEdgeUncolored sigma e0 →
           StableColoring Tn
             (TashkinovStoredColors lower.series.data n)
             (lower.series.data.coloring n) sigma →
           ∀ w, w ∈ TreeSequenceVertexSet Tn →
             (Sum.inl w ∈ TwoColorComponent G sigma gamma delta
                 (Sum.inl v) ↔ w = v))) :
    let q : Fin ett.rounds := ⟨ett.rounds - 1, by omega⟩
    let Tn : TreeSequence G e0 :=
      ett.series.data.tree (Fin.last ett.rounds).castSucc
    ∀ (sigmaPrev : PartialEdgeColoring E k),
      IsProperEdgeColoring G sigmaPrev → IsOneEdgeUncolored sigmaPrev e0 →
      IsProperEdgeColoring G (ett.series.data.coloring q.castSucc) →
      IsOneEdgeUncolored (ett.series.data.coloring q.castSucc) e0 →
      StableColoring (ett.series.data.tree q.succ.castSucc)
        (TashkinovStoredColors ett.series.data q.castSucc)
        (ett.series.data.coloring q.castSucc) sigmaPrev →
      ∀ (originalPrefix : ExtendedTashkinovTree G k e0 input Tn
          (ett.series.data.coloring q.castSucc))
        (hr : originalPrefix.rounds = ett.rounds - 1),
        MaximumProperty originalPrefix →
        (∀ i : Fin (originalPrefix.rounds + 2),
          originalPrefix.series.data.tree i =
            ett.series.data.tree (Fin.castLE (by omega) i)) →
        (∀ i : Fin (originalPrefix.rounds + 1),
          originalPrefix.series.data.coloring i =
              ett.series.data.coloring (Fin.castLE (by omega) i) ∧
          originalPrefix.series.data.stored i =
              ett.series.data.stored (Fin.castLE (by omega) i) ∧
          originalPrefix.series.data.connectingEdges i =
              ett.series.data.connectingEdges (Fin.castLE (by omega) i) ∧
          originalPrefix.series.data.kind i =
              ett.series.data.kind (Fin.castLE (by omega) i) ∧
          TashkinovStoredColors originalPrefix.series.data i =
              TashkinovStoredColors ett.series.data
                (Fin.castLE (by omega) i)) →
        ∀ (corr : CorrespondingExtendedTashkinovTree G k e0
            originalPrefix sigmaPrev Tn),
          corr.replacementSeries.data.tree
              (Fin.last (originalPrefix.rounds + 1)) = Tn →
          corr.replacementSeries.data.coloring
              (Fin.last originalPrefix.rounds) = sigmaPrev →
          MaximumProperty corr.replacementETT →
          (¬ Nonempty (RevisitingExtensionCertificate ett.series.data
            q.castSucc)) →
          ¬ Nonempty (RevisitingExtensionCertificate
            corr.replacementSeries.data (Fin.last originalPrefix.rounds)) := by
-- BODY
  classical
  let q : Fin ett.rounds := ⟨ett.rounds - 1, by omega⟩
  change ∀ sigmaPrev, _
  intro sigmaPrev hsigmaPrevProper hsigmaPrevOne previousProper
    previousOneUncolored hsigmaPrevStableQ originalPrefix hr hprefixMP
    hprefixTrees hprefixData corr hcorrFinalTree hcorrFinalColor hcorrMP
    noRevisiting
  have hqSucc : q.succ = Fin.last ett.rounds := by
    apply Fin.ext
    simp [q]
    omega
  let replacementLast : Fin (originalPrefix.rounds + 1) :=
    Fin.last originalPrefix.rounds
  have horiginalPositive : 0 < originalPrefix.rounds := by
    rw [hr]
    omega
  have hlastMap : Fin.castLE (by omega) replacementLast =
      q.castSucc := by
    apply Fin.ext
    simp [replacementLast, q, hr]
  have hreplacementCurrentTree :
      corr.replacementSeries.data.tree replacementLast.succ =
        ett.series.data.tree q.succ.castSucc := by
    have hlastTree : replacementLast.succ =
        Fin.last (originalPrefix.rounds + 1) := by
      apply Fin.ext
      simp [replacementLast]
    rw [hlastTree, hcorrFinalTree, hqSucc]
  have horiginalCurrentTree :
      originalPrefix.series.data.tree replacementLast.castSucc =
        ett.series.data.tree q.castSucc.castSucc := by
    calc
      originalPrefix.series.data.tree replacementLast.castSucc =
          ett.series.data.tree
            (Fin.castLE (by omega) replacementLast.castSucc) :=
        hprefixTrees replacementLast.castSucc
      _ = ett.series.data.tree q.castSucc.castSucc := by
        congr 1
        apply Fin.ext
        simp [replacementLast, q, hr]
  have peRootOnly : ∀ {input' : PartialEdgeColoring E k}
      {T' : TreeSequence G e0} {generating' : PartialEdgeColoring E k}
      (base : ExtendedTashkinovTree G k e0 input' T' generating'),
      0 < base.rounds → base.rounds < ett.rounds → MaximumProperty base →
      ∀ (r : ℕ) (series : TashkinovSeries G k r e0 input'),
        base.rounds = r → HEq base.series series →
        ∀ (a : Fin (r + 1)) (v : V) (gamma delta : Fin k),
          0 < a.val →
          series.data.kind a = some TashkinovExtensionKind.PE →
          series.data.chosenVertex a = some v →
          series.data.gamma a = some gamma →
          series.data.delta a = some delta →
          IsProperEdgeColoring G (series.data.coloring a) →
          IsOneEdgeUncolored (series.data.coloring a) e0 →
          ∀ w, w ∈ TreeSequenceVertexSet (series.data.tree a.castSucc) →
            (Sum.inl w ∈ TwoColorComponent G (series.data.coloring a)
                gamma delta (Sum.inl v) ↔ w = v) := by
    intro input' T' generating' base hp hl hm r series hrSeries hseries
    cases hrSeries
    cases hseries
    intro a v gamma delta ha hk hv hg hd hproper hone
    by_cases hlast : a.val = base.rounds
    · have haLast : a = Fin.last base.rounds := Fin.ext hlast
      subst a
      exact (hlower base hp hl hm).2 v gamma delta hk hv hg hd
        (base.series.data.coloring (Fin.last base.rounds)) hproper hone
        ⟨(by intros; rfl), (by intros; rfl)⟩
    · have habefore : a.val < base.rounds := by
        have habound := a.isLt
        omega
      obtain ⟨restricted, hrRestricted, hmaxRestricted, htrees, hdata⟩ :=
        CertifiedETTRestriction G k e0 input' T' generating' base hm
          a.val (by omega) habefore
      have hrestrictedPositive : 0 < restricted.rounds := by
        rw [hrRestricted]
        exact ha
      have hrestrictedLess : restricted.rounds < ett.rounds := by
        rw [hrRestricted]
        exact habefore.trans hl
      let lastRestricted : Fin (restricted.rounds + 1) :=
        Fin.last restricted.rounds
      have hmap : Fin.castLE (by omega) lastRestricted = a := by
        apply Fin.ext
        simp [lastRestricted, hrRestricted]
      have htree : restricted.series.data.tree lastRestricted.castSucc =
          base.series.data.tree a.castSucc := by
        calc
          restricted.series.data.tree lastRestricted.castSucc =
              base.series.data.tree
                (Fin.castLE (by omega) lastRestricted.castSucc) :=
            htrees lastRestricted.castSucc
          _ = base.series.data.tree a.castSucc := by
            congr 1
            apply Fin.ext
            simp [lastRestricted, hrRestricted]
      rcases hdata lastRestricted with
        ⟨hc, _, _, hkind, hvertex, _, hdelta, hgamma, _, _⟩
      rw [hmap] at hc hkind hvertex hdelta hgamma
      have hroot := (hlower restricted hrestrictedPositive hrestrictedLess
        hmaxRestricted).2 v gamma delta
        (by simpa only [← hkind] using hk)
        (by simpa only [← hvertex] using hv)
        (by simpa only [← hgamma] using hg)
        (by simpa only [← hdelta] using hd)
        (base.series.data.coloring a) hproper hone (by
          change StableColoring _ _
            (restricted.series.data.coloring lastRestricted) _
          rw [hc]
          exact ⟨(by intros; rfl), (by intros; rfl)⟩)
      intro w hw
      apply hroot w
      change w ∈ TreeSequenceVertexSet
        (restricted.series.data.tree lastRestricted.castSucc)
      rw [htree]
      exact hw
  rintro ⟨available⟩
  let earlierPrefix : Fin (originalPrefix.rounds + 1) :=
    available.earlier
  have hearlierPositive : 0 < earlierPrefix.val :=
    available.earlierPositive
  have hbaseEarlierKind : originalPrefix.series.data.kind
      earlierPrefix = some TashkinovExtensionKind.PE := by
    rw [← corr.extensionKindsAgree earlierPrefix]
    exact available.earlierPE
  have hbaseStep := originalPrefix.series.certified earlierPrefix
  generalize hbaseTarget : earlierPrefix = baseTarget at hbaseStep
  cases hbaseStep with
  | initial tripleBase seedLengthBase initialColoringBase
      initialStoredBase initialEdgesBase initialKindBase
      initialVertexBase initialOutsideBase initialDeltaBase
      initialGammaBase initialClosureBase =>
      have hbad := initialKindBase.symm.trans
        (by simpa [hbaseTarget] using hbaseEarlierKind)
      simp at hbad
  | SE oldi oldPreviousProper oldPreviousOne oldPreviousClosed
      oldPreviousNotStrong oldNoRE oldChoice oldAlternative
      oldCurrentColoring oldCurrentStored oldCurrentEdges
      oldCurrentKind oldCurrentVertex oldCurrentOutside
      oldCurrentDelta oldCurrentGamma oldAdjoined
      oldAdjoinedExactly oldClosedExtension oldOrderedExtension
      oldStrictExtension =>
      have hbad := oldCurrentKind.symm.trans
        (by simpa [hbaseTarget] using hbaseEarlierKind)
      cases hbad
  | RE oldi oldPreviousProper oldPreviousOne oldPreviousClosed
      oldPreviousNotStrong oldAvailable oldCurrentColoring
      oldCurrentStored oldCurrentEdges oldCurrentKind
      oldCurrentVertex oldCurrentOutside oldCurrentDelta
      oldCurrentGamma oldAdjoined oldAdjoinedExactly
      oldClosedExtension oldOrderedExtension oldStrictExtension =>
      have hbad := oldCurrentKind.symm.trans
        (by simpa [hbaseTarget] using hbaseEarlierKind)
      cases hbad
  | PE oldi oldPreviousProper oldPreviousOne oldPreviousClosed
      oldPreviousNotStrong oldNoRE oldChoice oldAlternativeFails
      oldGamma oldGammaRule oldSecond oldSecondProper oldSecondOne
      oldSecondStable oldExit oldCurrentColoring oldCurrentProper
      oldCurrentOne oldCurrentStored oldCurrentEdges oldCurrentKind
      oldCurrentVertex oldCurrentOutside oldCurrentDelta
      oldCurrentGamma oldClosedExtension oldOrderedExtension
      oldStrictExtension =>
      have holdIndex : oldi.succ = earlierPrefix := by
        simpa using hbaseTarget.symm
      have hnewStep :=
        corr.replacementSeries.certified earlierPrefix
      generalize hnewTarget : earlierPrefix = newTarget at hnewStep
      cases hnewStep with
      | initial tripleNew seedLengthNew initialColoringNew
          initialStoredNew initialEdgesNew initialKindNew
          initialVertexNew initialOutsideNew initialDeltaNew
          initialGammaNew initialClosureNew =>
          have hk : corr.replacementSeries.data.kind 0 =
              some TashkinovExtensionKind.PE := by
            rw [← hnewTarget]
            exact available.earlierPE
          have hbad := initialKindNew.symm.trans
            hk
          simp at hbad
      | SE newi newPreviousProper newPreviousOne newPreviousClosed
          newPreviousNotStrong newNoRE newChoicePE newAlternative
          newCurrentColoring newCurrentStored newCurrentEdges
          newCurrentKind newCurrentVertex newCurrentOutside
          newCurrentDelta newCurrentGamma newAdjoined
          newAdjoinedExactly newClosedExtension newOrderedExtension
          newStrictExtension =>
          have hk : corr.replacementSeries.data.kind newi.succ =
              some TashkinovExtensionKind.PE := by
            rw [← hnewTarget]
            exact available.earlierPE
          have hbad := newCurrentKind.symm.trans
            hk
          cases hbad
      | RE newi newPreviousProper newPreviousOne newPreviousClosed
          newPreviousNotStrong newAvailable newCurrentColoring
          newCurrentStored newCurrentEdges newCurrentKind
          newCurrentVertex newCurrentOutside newCurrentDelta
          newCurrentGamma newAdjoined newAdjoinedExactly
          newClosedExtension newOrderedExtension newStrictExtension =>
          have hk : corr.replacementSeries.data.kind newi.succ =
              some TashkinovExtensionKind.PE := by
            rw [← hnewTarget]
            exact available.earlierPE
          have hbad := newCurrentKind.symm.trans
            hk
          cases hbad
      | PE newi newPreviousProper newPreviousOne newPreviousClosed
          newPreviousNotStrong newNoRE newChoicePE
          newAlternativeFails newGamma newGammaRule newSecond
          newSecondProper newSecondOne newSecondStable newExit
          newCurrentColoring newCurrentProper newCurrentOne
          newCurrentStored newCurrentEdges newCurrentKind
          newCurrentVertex newCurrentOutside newCurrentDelta
          newCurrentGamma newClosedExtension newOrderedExtension
          newStrictExtension =>
          have hnewIndex : newi.succ = earlierPrefix := by
            simpa using hnewTarget.symm
          have hindices : oldi = newi := by
            apply Fin.ext
            have holdVals := congrArg Fin.val holdIndex
            have hnewVals := congrArg Fin.val hnewIndex
            simp only [Fin.val_succ] at holdVals hnewVals
            omega
          subst newi
          have hbaseTree :
              corr.replacementSeries.data.tree oldi.succ.castSucc =
                originalPrefix.series.data.tree oldi.succ.castSucc :=
            corr.ladderTreesAgree oldi
          let oldChoiceOnNew : MaximumDefectiveChoice G e0
              (corr.replacementSeries.data.tree oldi.succ.castSucc)
              (TashkinovStoredColors originalPrefix.series.data
                oldi.castSucc)
              (originalPrefix.series.data.coloring oldi.castSucc) :=
            hbaseTree.symm ▸ oldChoice
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
          have htransport := transportChoiceFields hbaseTree.symm
            (TashkinovStoredColors originalPrefix.series.data
              oldi.castSucc)
            (originalPrefix.series.data.coloring oldi.castSucc)
            oldChoice
          have holdEdgeCast : oldChoiceOnNew.edge = oldChoice.edge :=
            htransport.1
          have holdVertexCast : oldChoiceOnNew.vertex =
              oldChoice.vertex := htransport.2.1
          have holdOtherCast : oldChoiceOnNew.otherEndpoint =
              oldChoice.otherEndpoint := htransport.2.2.1
          have holdColorCast : oldChoiceOnNew.color =
              oldChoice.color := htransport.2.2.2
          have hedgePairs : ({oldChoiceOnNew.edge} : Finset E) =
              {newChoicePE.edge} := by
            have holdEdges : originalPrefix.series.data.connectingEdges
                earlierPrefix = {oldChoice.edge} := by
              simpa only [holdIndex] using oldCurrentEdges
            have hnewEdges :
                corr.replacementSeries.data.connectingEdges
                  earlierPrefix = {newChoicePE.edge} := by
              simpa only [hnewIndex] using newCurrentEdges
            simpa only [holdEdgeCast] using
              holdEdges.symm.trans
                ((corr.connectingEdgesAgree earlierPrefix).symm.trans
                  hnewEdges)
          have hcolorPairs :
              ({oldChoiceOnNew.color, oldGamma} : Finset (Fin k)) =
                {newChoicePE.color, newGamma} := by
            have holdStored : originalPrefix.series.data.stored
                earlierPrefix = {oldChoice.color, oldGamma} := by
              simpa only [holdIndex] using oldCurrentStored
            have hnewStored : corr.replacementSeries.data.stored
                earlierPrefix = {newChoicePE.color, newGamma} := by
              simpa only [hnewIndex] using newCurrentStored
            simpa only [holdColorCast] using
              holdStored.symm.trans
                ((corr.storedColorsAgree earlierPrefix).symm.trans
                  hnewStored)
          have hedgeIdentity : newChoicePE.edge =
              oldChoiceOnNew.edge := by
            apply Finset.mem_singleton.mp
            rw [hedgePairs]
            exact Finset.mem_singleton_self _
          have hends : s(oldChoiceOnNew.vertex,
                oldChoiceOnNew.otherEndpoint) =
              s(newChoicePE.vertex, newChoicePE.otherEndpoint) := by
            calc
              s(oldChoiceOnNew.vertex,
                  oldChoiceOnNew.otherEndpoint) =
                  G.ends oldChoiceOnNew.edge :=
                oldChoiceOnNew.edgeEnds.symm
              _ = G.ends newChoicePE.edge :=
                congrArg G.ends hedgeIdentity.symm
              _ = s(newChoicePE.vertex,
                  newChoicePE.otherEndpoint) := newChoicePE.edgeEnds
          have hvertexIdentity : newChoicePE.vertex =
              oldChoiceOnNew.vertex := by
            rcases Sym2.eq_iff.mp hends with hstraight | hcross
            · exact hstraight.1.symm
            · exfalso
              exact newChoicePE.otherOutside
                (hcross.1 ▸ oldChoiceOnNew.vertexDefective.1)
          have hotherIdentity : newChoicePE.otherEndpoint =
              oldChoiceOnNew.otherEndpoint := by
            rcases Sym2.eq_iff.mp hends with hstraight | hcross
            · exact hstraight.2.symm
            · exfalso
              exact oldChoiceOnNew.otherOutside
                (hcross.2 ▸ newChoicePE.vertexDefective.1)
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
                g ∉ MissingColors G post ch.vertex ∧
                g ≠ ch.color := by
            intro X C phi ch g second hsecondProper hsecondStable
              hgSelected
            dsimp
            have hgSecond : g ∈ MissingColors G second ch.vertex := by
              rw [hsecondStable.2 ch.vertex ch.vertexDefective.1]
              exact hgSelected
            have hedgeSecond : second ch.edge = some ch.color := by
              exact (hsecondStable.1 ch.edge
                ⟨ch.vertex, ch.vertexDefective.1, ch.edgeIncident⟩
                ⟨ch.color, Finset.mem_union_right _
                  (Finset.mem_insert_self _ _), ch.edgeColor⟩).trans
                    ch.edgeColor
            have hne : g ≠ ch.color := by
              intro heq
              have hpresent : g ∈ PresentColors G second ch.vertex := by
                simp only [PresentColors, Finset.mem_filter,
                  Finset.mem_univ, true_and]
                exact ⟨ch.edge, ch.edgeIncident,
                  by simpa [heq] using hedgeSecond⟩
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
              exact (TwoColorComponentSwapMissingBehavior G second g
                ch.color hne hsecondProper (Sum.inl ch.vertex)).2.1
                  ch.vertex rfl hgSecond
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
          obtain ⟨holdDeltaMissing, holdGammaNotMissing,
              holdColorNe⟩ := pePostStatus
            (originalPrefix.series.data.tree oldi.succ.castSucc)
            (TashkinovStoredColors originalPrefix.series.data
              oldi.castSucc)
            (originalPrefix.series.data.coloring oldi.castSucc)
            oldChoice oldGamma oldSecond oldSecondProper
            oldSecondStable oldGammaRule.1
          obtain ⟨hnewDeltaMissing, hnewGammaNotMissing,
              hnewColorNe⟩ := pePostStatus
            (corr.replacementSeries.data.tree oldi.succ.castSucc)
            (TashkinovStoredColors corr.replacementSeries.data
              oldi.castSucc)
            (corr.replacementSeries.data.coloring oldi.castSucc)
            newChoicePE newGamma newSecond newSecondProper
            newSecondStable newGammaRule.1
          rw [← oldCurrentColoring] at holdDeltaMissing holdGammaNotMissing
          rw [← newCurrentColoring] at hnewDeltaMissing hnewGammaNotMissing
          have hmissingSameVertex : MissingColors G
              (originalPrefix.series.data.coloring oldi.succ)
                oldChoice.vertex =
            MissingColors G
              (corr.replacementSeries.data.coloring oldi.succ)
                oldChoice.vertex := by
            have hs := (corr.replacementStable oldi).2
              oldChoice.vertex (by
                exact oldChoice.vertexDefective.1)
            exact hs.symm
          have hmissingForIdentification : MissingColors G
              (originalPrefix.series.data.coloring oldi.succ)
                oldChoiceOnNew.vertex =
            MissingColors G
              (corr.replacementSeries.data.coloring oldi.succ)
                newChoicePE.vertex := by
            calc
              MissingColors G
                  (originalPrefix.series.data.coloring oldi.succ)
                  oldChoiceOnNew.vertex =
                MissingColors G
                  (originalPrefix.series.data.coloring oldi.succ)
                  oldChoice.vertex := congrArg _ holdVertexCast
              _ = MissingColors G
                  (corr.replacementSeries.data.coloring oldi.succ)
                  oldChoice.vertex := hmissingSameVertex
              _ = MissingColors G
                  (corr.replacementSeries.data.coloring oldi.succ)
                  newChoicePE.vertex := by
                    exact congrArg _
                      (hvertexIdentity.trans holdVertexCast).symm
          have holdDeltaForIdentification : oldChoiceOnNew.color ∈
              MissingColors G
                (originalPrefix.series.data.coloring oldi.succ)
                oldChoiceOnNew.vertex := by
            simpa only [holdColorCast, holdVertexCast] using
              holdDeltaMissing
          have holdGammaForIdentification : oldGamma ∉
              MissingColors G
                (originalPrefix.series.data.coloring oldi.succ)
                oldChoiceOnNew.vertex := by
            simpa only [holdVertexCast] using holdGammaNotMissing
          have hidentified := TdEarlierPEWitnessIdentification G k e0
            (corr.replacementSeries.data.tree oldi.succ.castSucc)
            (TashkinovStoredColors originalPrefix.series.data
              oldi.castSucc)
            (TashkinovStoredColors corr.replacementSeries.data
              oldi.castSucc)
            (originalPrefix.series.data.coloring oldi.castSucc)
            (corr.replacementSeries.data.coloring oldi.castSucc)
            oldChoiceOnNew newChoicePE oldGamma newGamma
            (originalPrefix.series.data.coloring oldi.succ)
            (corr.replacementSeries.data.coloring oldi.succ)
            hedgePairs hcolorPairs hmissingForIdentification
            holdDeltaForIdentification holdGammaForIdentification
            hnewDeltaMissing hnewGammaNotMissing
          rcases hidentified with ⟨hidentifiedEdge,
            hidentifiedVertex, hidentifiedOther, hidentifiedDelta,
            hidentifiedGamma⟩
          have hnewDeltaAvailable : newChoicePE.color =
              available.delta := by
            exact Option.some.inj (newCurrentDelta.symm.trans
              ((congrArg corr.replacementSeries.data.delta
                hnewIndex).trans available.earlierDelta))
          have hnewGammaAvailable : newGamma = available.gamma := by
            exact Option.some.inj (newCurrentGamma.symm.trans
              ((congrArg corr.replacementSeries.data.gamma
                hnewIndex).trans available.earlierGamma))
          have holdDeltaAvailable : oldChoice.color =
              available.delta := by
            exact holdColorCast.symm.trans
              (hidentifiedDelta.symm.trans hnewDeltaAvailable)
          have holdGammaAvailable : oldGamma = available.gamma := by
            exact hidentifiedGamma.symm.trans hnewGammaAvailable
          have hnewVertexOld : newChoicePE.vertex = oldChoice.vertex :=
            hidentifiedVertex.trans holdVertexCast
          have hnewOtherOld : newChoicePE.otherEndpoint =
              oldChoice.otherEndpoint :=
            hidentifiedOther.trans holdOtherCast
          have reStepColoring : ∀ {rounds' : ℕ}
              {input' : PartialEdgeColoring E k}
              (series : TashkinovSeries G k rounds' e0 input')
              (j : Fin rounds'),
              series.data.kind j.succ =
                  some TashkinovExtensionKind.RE →
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
            | SE i prevProper prevOne prevClosed prevNotStrong noRE
                ch alternative coloring stored edges kind vertex
                outside delta gamma adjoined adjoinedExactly closed
                ordered strict =>
                have hbad := kind.symm.trans
                  (by simpa [hslot] using hj)
                cases hbad
            | PE i prevProper prevOne prevClosed prevNotStrong noRE
                ch alternativeFails gamma gammaRule second
                secondProper secondOne secondStable exit coloring
                coloringProper coloringOne stored edges kind vertex
                outside delta gammaValue closed ordered strict =>
                have hbad := kind.symm.trans
                  (by simpa [hslot] using hj)
                cases hbad
            | RE i prevProper prevOne prevClosed prevNotStrong cert
                coloring stored edges kind vertex outside delta gamma
                adjoined adjoinedExactly closed ordered strict =>
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
                series.data.kind j =
                  some TashkinovExtensionKind.RE) →
              series.data.coloring b = series.data.coloring a := by
            intro rounds' input' series a b hab hbetween
            have coloringAlong : ∀ m : ℕ, a.val ≤ m →
                m ≤ b.val → ∀ x : Fin (rounds' + 1),
                x.val = m →
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
          have hreplacementColorConstant :
              corr.replacementSeries.data.coloring replacementLast =
                corr.replacementSeries.data.coloring oldi.succ := by
            apply reIntervalColoring corr.replacementSeries
              oldi.succ replacementLast
            · have hvals := congrArg Fin.val hnewIndex
              simp [replacementLast] at hvals ⊢
              omega
            · intro j hjLower hjUpper
              apply available.interveningRevisiting j
              · omega
              · have hvals := congrArg Fin.val hnewIndex
                simp only [Fin.val_succ] at hvals
                omega
              · exact hjUpper
          have hbaseColorConstant :
              originalPrefix.series.data.coloring replacementLast =
                originalPrefix.series.data.coloring oldi.succ := by
            apply reIntervalColoring originalPrefix.series oldi.succ
              replacementLast
            · have hvals := congrArg Fin.val holdIndex
              simp [replacementLast] at hvals ⊢
              omega
            · intro j hjLower hjUpper
              rw [← corr.extensionKindsAgree j]
              apply available.interveningRevisiting j
              · omega
              · have hvals := congrArg Fin.val holdIndex
                simp only [Fin.val_succ] at hvals
                omega
              · exact hjUpper
          have hnewPostSigmaPrev :
              corr.replacementSeries.data.coloring oldi.succ =
                sigmaPrev :=
            hreplacementColorConstant.symm.trans
              (by simpa [replacementLast] using hcorrFinalColor)
          have hbaseFinalColor :
              originalPrefix.series.data.coloring replacementLast =
                ett.series.data.coloring q.castSucc := by
            calc
              originalPrefix.series.data.coloring replacementLast =
                  ett.series.data.coloring
                    (Fin.castLE (by omega) replacementLast) :=
                (hprefixData replacementLast).1
              _ = ett.series.data.coloring q.castSucc := by
                rw [hlastMap]
          have holdPostOriginal :
              originalPrefix.series.data.coloring oldi.succ =
                ett.series.data.coloring q.castSucc :=
            hbaseColorConstant.symm.trans hbaseFinalColor
          have hnewDeltaSigmaPrev : available.delta ∈
              MissingColors G sigmaPrev newChoicePE.vertex := by
            have hm := hnewDeltaMissing
            rw [hnewDeltaAvailable] at hm
            exact Eq.mp (congrArg (fun phi => available.delta ∈
              MissingColors G phi newChoicePE.vertex)
                hnewPostSigmaPrev) hm
          have hnewGammaSigmaPrevNot : available.gamma ∉
              MissingColors G sigmaPrev newChoicePE.vertex := by
            have hm := hnewGammaNotMissing
            rw [hnewGammaAvailable] at hm
            exact Eq.mp (congrArg (fun phi => available.gamma ∉
              MissingColors G phi newChoicePE.vertex)
                hnewPostSigmaPrev) hm
          have holdDeltaOriginal : available.delta ∈ MissingColors G
              (ett.series.data.coloring q.castSucc)
              oldChoice.vertex := by
            have hm := holdDeltaMissing
            rw [holdDeltaAvailable] at hm
            exact Eq.mp (congrArg (fun phi => available.delta ∈
              MissingColors G phi oldChoice.vertex)
                holdPostOriginal) hm
          have holdGammaOriginalNot : available.gamma ∉ MissingColors G
              (ett.series.data.coloring q.castSucc)
              oldChoice.vertex := by
            have hm := holdGammaNotMissing
            rw [holdGammaAvailable] at hm
            exact Eq.mp (congrArg (fun phi => available.gamma ∉
              MissingColors G phi oldChoice.vertex)
                holdPostOriginal) hm
          have hgammaDeltaNe : available.gamma ≠ available.delta := by
            intro heq
            apply hnewColorNe
            rw [hnewGammaAvailable, hnewDeltaAvailable, heq]
          have stepSegment : ∀ r : Fin originalPrefix.rounds,
              TreeSequenceInitialSegment
                (originalPrefix.series.data.tree r.succ.castSucc)
                (originalPrefix.series.data.tree r.succ.succ) := by
            intro r
            have hstep := originalPrefix.series.certified r.succ
            generalize hslot : r.succ = slot at hstep
            cases hstep with
            | initial triple seedLength initialColoring initialStored
                initialEdges initialKind initialVertex initialOutside
                initialDelta initialGamma initialClosure =>
                exact (Fin.succ_ne_zero r hslot).elim
            | SE i prevProper prevOne prevClosed prevNotStrong noRE ch
                alternative coloring stored edges kind vertex outside
                delta gamma adjoined adjoinedExactly closed ordered strict =>
                have hi : i = r := by
                  apply Fin.ext
                  have hv := congrArg Fin.val hslot
                  simp only [Fin.val_succ] at hv
                  omega
                subst i
                simpa [hslot] using ordered
            | PE i prevProper prevOne prevClosed prevNotStrong noRE ch
                alternativeFails gamma gammaRule second secondProper
                secondOne secondStable exit coloring coloringProper
                coloringOne stored edges kind vertex outside delta
                gammaValue closed ordered strict =>
                have hi : i = r := by
                  apply Fin.ext
                  have hv := congrArg Fin.val hslot
                  simp only [Fin.val_succ] at hv
                  omega
                subst i
                simpa [hslot] using ordered
            | RE i prevProper prevOne prevClosed prevNotStrong cert
                coloring stored edges kind vertex outside delta gamma
                adjoined adjoinedExactly closed ordered strict =>
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
                _ = B.vertex
                    (Fin.castLE (Nat.succ_le_succ hlenAB) x) :=
                  hvertexBC _
                _ = A.vertex x := hvertexAB x
            · intro x
              calc
                C.edge (Fin.castLE (hlenAB.trans hlenBC) x) =
                    C.edge (Fin.castLE hlenBC
                      (Fin.castLE hlenAB x)) := by congr 1
                _ = B.edge (Fin.castLE hlenAB x) := hedgeBC _
                _ = A.edge x := hedgeAB x
          have treeToFinal : ∀ (d : ℕ)
              (idx : Fin (originalPrefix.rounds + 2)),
              idx.val + d = originalPrefix.rounds + 1 →
              1 ≤ idx.val →
              TreeSequenceInitialSegment
                (originalPrefix.series.data.tree idx)
                (originalPrefix.series.data.tree
                  (Fin.last (originalPrefix.rounds + 1))) := by
            intro d
            induction d with
            | zero =>
                intro idx hidx hpos
                have hi : idx =
                    Fin.last (originalPrefix.rounds + 1) := by
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
                    (originalPrefix.series.data.tree idx)
                    (originalPrefix.series.data.tree next) := by
                  rw [hleft, hright]
                  exact stepSegment r
                exact segmentTrans _ _ _ hfirst
                  (ih next (by simp [next]; omega)
                    (by simp [next]))
          have holdTreeFinal : TreeSequenceInitialSegment
              (originalPrefix.series.data.tree oldi.succ.castSucc)
              (originalPrefix.series.data.tree
                (Fin.last (originalPrefix.rounds + 1))) := by
            apply treeToFinal (originalPrefix.rounds - oldi.val)
            · simp
              omega
            · simp
          have holdVertexFinal : oldChoice.vertex ∈
              TreeSequenceVertexSet
                (originalPrefix.series.data.tree
                  (Fin.last (originalPrefix.rounds + 1))) :=
            TreeSequenceInitialSegmentVertexSetSubset holdTreeFinal
              oldChoice.vertexDefective.1
          have hreturnInOldEarlier : available.returnVertex ∈
              TreeSequenceVertexSet
                (originalPrefix.series.data.tree
                  earlierPrefix.castSucc) := by
            have htreeEarlier : corr.replacementSeries.data.tree
                  earlierPrefix.castSucc =
                originalPrefix.series.data.tree
                  earlierPrefix.castSucc := by
              calc
                corr.replacementSeries.data.tree
                    earlierPrefix.castSucc =
                    corr.replacementSeries.data.tree
                      oldi.succ.castSucc := by
                        congr 1
                        exact congrArg Fin.castSucc hnewIndex.symm
                _ = originalPrefix.series.data.tree
                      oldi.succ.castSucc := hbaseTree
                _ = originalPrefix.series.data.tree
                      earlierPrefix.castSucc := by
                        congr 1
                        exact congrArg Fin.castSucc holdIndex
            rw [← htreeEarlier]
            simpa [earlierPrefix] using available.returnInEarlier
          have hreturnInFinal : available.returnVertex ∈
              TreeSequenceVertexSet
                (originalPrefix.series.data.tree
                  (Fin.last (originalPrefix.rounds + 1))) :=
            TreeSequenceInitialSegmentVertexSetSubset holdTreeFinal
              (by simpa only [holdIndex] using hreturnInOldEarlier)
          have hpreviousToTn : TreeSequenceInitialSegment
              (ett.series.data.tree q.castSucc.castSucc)
              (ett.series.data.tree q.succ.castSucc) := by
            rw [← horiginalCurrentTree, hqSucc]
            exact originalPrefix.abovePenultimate
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
              TreeSequenceInitialSegmentVertexSetSubset
                hpreviousToTn hv, hvc⟩
          have hgammaEarlierStored : available.gamma ∈
              originalPrefix.series.data.stored earlierPrefix := by
            rw [← holdIndex, oldCurrentStored,
              ← holdGammaAvailable]
            simp
          have hdeltaEarlierStored : available.delta ∈
              originalPrefix.series.data.stored earlierPrefix := by
            rw [← holdIndex, oldCurrentStored,
              ← holdDeltaAvailable]
            simp
          have hgammaEarlierStoredFull : available.gamma ∈
              ett.series.data.stored
                (Fin.castLE (by omega) earlierPrefix) := by
            rw [← (hprefixData earlierPrefix).2.1]
            exact hgammaEarlierStored
          have hdeltaEarlierStoredFull : available.delta ∈
              ett.series.data.stored
                (Fin.castLE (by omega) earlierPrefix) := by
            rw [← (hprefixData earlierPrefix).2.1]
            exact hdeltaEarlierStored
          have colorControlAtQ (c : Fin k)
              (hc : c ∈ ett.series.data.stored
                (Fin.castLE (by omega) earlierPrefix)) :
              c ∈ TreeMissingColors
                    (ett.series.data.coloring q.castSucc)
                    (ett.series.data.tree q.succ.castSucc) ∪
                  TashkinovStoredColors ett.series.data q.castSucc := by
            by_cases hm : c ∈ TreeMissingColors
                (ett.series.data.coloring q.castSucc)
                (ett.series.data.tree q.castSucc.castSucc)
            · exact Finset.mem_union_left _
                (missingPreviousToTn c hm)
            · apply Finset.mem_union_right
              unfold TashkinovStoredColors
              have hqne : q.castSucc.val ≠ 0 := by
                change ett.rounds - 1 ≠ 0
                omega
              rw [if_neg hqne, Finset.mem_sdiff]
              refine ⟨?_, hm⟩
              simp only [Finset.mem_biUnion, Finset.mem_univ,
                true_and]
              refine ⟨Fin.castLE (by omega) earlierPrefix, ?_⟩
              rw [if_pos]
              · exact hc
              · have hle := available.earlierAtMost
                have hlastVal : replacementLast.val = q.castSucc.val := by
                  exact congrArg Fin.val hlastMap
                simpa [earlierPrefix] using hle.trans_eq hlastVal
          have hreturnNotNil : ¬ available.returnPath.Nil := by
            intro hnil
            have hend := SimpleGraph.Walk.Nil.eq hnil
            simp at hend
          have replacementReturnEdgeData (f : E)
              (hf : Sum.inr f ∈ available.returnPath.support) :
              TreeIncidentEdge
                  (ett.series.data.tree q.succ.castSucc) f ∧
                (sigmaPrev f = some available.gamma ∨
                  sigmaPrev f = some available.delta) := by
            obtain ⟨node, hnode, hadj⟩ :=
              SimpleGraph.adj_of_mem_walk_support available.returnPath
                hreturnNotNil hf
            cases node with
            | inl v =>
                have hdataRaw : Incident G v f ∧
                    (corr.replacementSeries.data.coloring
                          replacementLast f = some available.gamma ∨
                      corr.replacementSeries.data.coloring
                          replacementLast f = some available.delta) := by
                  simpa [TwoColorIncidenceGraph] using hadj
                have hdata : Incident G v f ∧
                    (sigmaPrev f = some available.gamma ∨
                      sigmaPrev f = some available.delta) := by
                  simpa [replacementLast, hcorrFinalColor] using hdataRaw
                refine ⟨⟨v, ?_, hdata.1⟩, hdata.2⟩
                rw [← hreplacementCurrentTree]
                exact available.returnPathInternal v hnode
            | inr g =>
                simpa [TwoColorIncidenceGraph] using hadj
          have copyReturnEdge (f : E)
              (hf : Sum.inr f ∈ available.returnPath.support) :
              sigmaPrev f = ett.series.data.coloring q.castSucc f := by
            obtain ⟨hfIncident, hcolor⟩ :=
              replacementReturnEdgeData f hf
            have hcriterion := (sc1 G e0
              (ett.series.data.tree q.succ.castSucc)
              (TashkinovStoredColors ett.series.data q.castSucc)
              (ett.series.data.coloring q.castSucc) sigmaPrev
              previousProper previousOneUncolored hsigmaPrevProper
              hsigmaPrevOne).mp hsigmaPrevStableQ
            apply hcriterion f hfIncident
            rcases hcolor with hgamma | hdelta
            · exact Or.inr ⟨available.gamma,
                colorControlAtQ available.gamma
                  hgammaEarlierStoredFull, hgamma⟩
            · exact Or.inr ⟨available.delta,
                colorControlAtQ available.delta
                  hdeltaEarlierStoredFull, hdelta⟩
          let replacementReturnGraph := TwoColorIncidenceGraph G
            (corr.replacementSeries.data.coloring replacementLast)
            available.gamma available.delta
          let originalReturnGraph := TwoColorIncidenceGraph G
            (ett.series.data.coloring q.castSucc) available.gamma
            available.delta
          have returnEdgeTransfer : ∀ edge,
              edge ∈ available.returnPath.edges →
              edge ∈ originalReturnGraph.edgeSet := by
            intro edge hedge
            induction edge using Sym2.inductionOn with
            | _ a b =>
                have haSupport :=
                  available.returnPath.fst_mem_support_of_mem_edges
                    hedge
                have hbSupport :=
                  available.returnPath.snd_mem_support_of_mem_edges
                    hedge
                have habReplacement : replacementReturnGraph.Adj a b := by
                  simpa [replacementReturnGraph] using
                    available.returnPath.edges_subset_edgeSet hedge
                cases a with
                | inl v =>
                    cases b with
                    | inl w =>
                        simpa [replacementReturnGraph,
                          TwoColorIncidenceGraph] using habReplacement
                    | inr f =>
                        have hdata : Incident G v f ∧
                            (corr.replacementSeries.data.coloring
                                  replacementLast f =
                                some available.gamma ∨
                              corr.replacementSeries.data.coloring
                                  replacementLast f =
                                some available.delta) := by
                          simpa [replacementReturnGraph,
                            TwoColorIncidenceGraph] using habReplacement
                        have hcopy := copyReturnEdge f hbSupport
                        have hfinal :
                            corr.replacementSeries.data.coloring
                                replacementLast f = sigmaPrev f := by
                          simpa [replacementLast] using
                            congrFun hcorrFinalColor f
                        simpa [originalReturnGraph,
                          TwoColorIncidenceGraph, hfinal, hcopy] using hdata
                | inr f =>
                    cases b with
                    | inl v =>
                        have hdata : Incident G v f ∧
                            (corr.replacementSeries.data.coloring
                                  replacementLast f =
                                some available.gamma ∨
                              corr.replacementSeries.data.coloring
                                  replacementLast f =
                                some available.delta) := by
                          simpa [replacementReturnGraph,
                            TwoColorIncidenceGraph] using habReplacement
                        have hcopy := copyReturnEdge f haSupport
                        have hfinal :
                            corr.replacementSeries.data.coloring
                                replacementLast f = sigmaPrev f := by
                          simpa [replacementLast] using
                            congrFun hcorrFinalColor f
                        simpa [originalReturnGraph,
                          TwoColorIncidenceGraph, hfinal, hcopy] using hdata
                    | inr g =>
                        simpa [replacementReturnGraph,
                          TwoColorIncidenceGraph] using habReplacement
          let originalReturnPath :=
            available.returnPath.transfer originalReturnGraph
              returnEdgeTransfer
          have horiginalReturnIsPath : originalReturnPath.IsPath :=
            available.returnPathIsPath.transfer returnEdgeTransfer
          have horiginalReturnSupport : ∀ z,
              z ∈ originalReturnPath.support ↔
                z ∈ available.returnPath.support := by
            intro z
            simp [originalReturnPath]
          have hreturnInQ : Sum.inl available.returnVertex ∈
              TwoColorComponent G
                (ett.series.data.coloring q.castSucc)
                available.gamma available.delta
                (Sum.inr available.edge) := by
            change originalReturnGraph.connectedComponentMk
                (Sum.inl available.returnVertex) =
              originalReturnGraph.connectedComponentMk
                (Sum.inr available.edge)
            exact (SimpleGraph.ConnectedComponent.sound
              originalReturnPath.reachable).symm
          have hedgeOriginalActive :
              ett.series.data.coloring q.castSucc available.edge =
                  some available.gamma ∨
                ett.series.data.coloring q.castSucc available.edge =
                  some available.delta := by
            have hsupport : Sum.inr available.edge ∈
                available.returnPath.support := by simp
            have hdata :=
              (replacementReturnEdgeData available.edge hsupport).2
            have hcopy := copyReturnEdge available.edge hsupport
            rw [hcopy] at hdata
            exact hdata
          have houtsideInQ : Sum.inl available.outsideEndpoint ∈
              TwoColorComponent G
                (ett.series.data.coloring q.castSucc)
                available.gamma available.delta
                (Sum.inr available.edge) := by
            apply SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
            have houtIncident : Incident G available.outsideEndpoint
                available.edge := by
              unfold Incident
              rw [available.edgeEnds]
              exact Sym2.mem_mk_right _ _
            simp [TwoColorComponent, TwoColorIncidenceGraph,
              houtIncident, hedgeOriginalActive]
          have hgammaPresentOriginal : available.gamma ∈
              PresentColors G (ett.series.data.coloring q.castSucc)
                oldChoice.vertex := by
            simpa [MissingColors] using holdGammaOriginalNot
          obtain ⟨pathEdge, hpathEdgeIncident, hpathEdgeColor⟩ := by
            simpa only [PresentColors, Finset.mem_filter,
              Finset.mem_univ, true_and] using hgammaPresentOriginal
          have hpathEdgeComponent : Sum.inr pathEdge ∈
              TwoColorComponent G
                (ett.series.data.coloring q.castSucc)
                available.gamma available.delta
                (Sum.inl oldChoice.vertex) := by
            apply SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
            simp [TwoColorComponent, TwoColorIncidenceGraph,
              hpathEdgeIncident, hpathEdgeColor]
          have hleafDegree : @SimpleGraph.degree _
              (TwoColorIncidenceGraph G
                (ett.series.data.coloring q.castSucc)
                available.gamma available.delta)
              (Sum.inl oldChoice.vertex) (Fintype.ofFinite _) ≤ 1 := by
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
              oldChoice.vertex holdDeltaOriginal
          have hleaf : Set.Subsingleton
              ((TwoColorIncidenceGraph G
                (ett.series.data.coloring q.castSucc)
                available.gamma available.delta).neighborSet
                  (Sum.inl oldChoice.vertex)) := by
            letI : Fintype
                ((TwoColorIncidenceGraph G
                  (ett.series.data.coloring q.castSucc)
                  available.gamma available.delta).neighborSet
                    (Sum.inl oldChoice.vertex)) := Fintype.ofFinite _
            rw [← SimpleGraph.card_neighborSet_eq_degree] at hleafDegree
            have hsub := Fintype.card_le_one_iff.mp hleafDegree
            intro a ha b hb
            exact congrArg Subtype.val
              (hsub ⟨a, ha⟩ ⟨b, hb⟩)
          have hpathComponent : TwoColorNontrivialPathComponent G
              (ett.series.data.coloring q.castSucc)
              available.gamma available.delta
              (Sum.inl oldChoice.vertex) := by
            refine ⟨⟨hgammaDeltaNe, Sum.inl oldChoice.vertex,
              rfl, hleaf⟩, pathEdge, hpathEdgeComponent⟩
          have hpathMeetsFinal : ∃ v ∈ TreeSequenceVertexSet
              (originalPrefix.series.data.tree
                (Fin.last (originalPrefix.rounds + 1))),
              Sum.inl v ∈ TwoColorComponent G
                (ett.series.data.coloring q.castSucc)
                available.gamma available.delta
                (Sum.inl oldChoice.vertex) :=
            ⟨oldChoice.vertex, holdVertexFinal, rfl⟩
          have hreplacementLeafDegree : @SimpleGraph.degree _
              (TwoColorIncidenceGraph G
                (corr.replacementSeries.data.coloring replacementLast)
                available.gamma available.delta)
              (Sum.inl newChoicePE.vertex) (Fintype.ofFinite _) ≤ 1 := by
            have hgraphSwapOrder :
                TwoColorIncidenceGraph G sigmaPrev available.delta
                    available.gamma =
                  TwoColorIncidenceGraph G sigmaPrev available.gamma
                    available.delta := by
              ext x y
              cases x <;> cases y <;>
                simp [TwoColorIncidenceGraph, or_comm]
            have hdegree : @SimpleGraph.degree _
                (TwoColorIncidenceGraph G sigmaPrev available.gamma
                  available.delta) (Sum.inl newChoicePE.vertex)
                  (Fintype.ofFinite _) ≤ 1 := by
              rw [← hgraphSwapOrder]
              exact MissingColorIncidenceEndpoint G sigmaPrev
                available.delta available.gamma hgammaDeltaNe.symm
                hsigmaPrevProper newChoicePE.vertex hnewDeltaSigmaPrev
            have hcolorEq :
                corr.replacementSeries.data.coloring replacementLast =
                  sigmaPrev := by
              simpa [replacementLast] using hcorrFinalColor
            rw [hcolorEq]
            exact hdegree
          have hreplacementLeaf : Set.Subsingleton
              ((TwoColorIncidenceGraph G
                (corr.replacementSeries.data.coloring replacementLast)
                available.gamma available.delta).neighborSet
                  (Sum.inl newChoicePE.vertex)) := by
            letI : Fintype
                ((TwoColorIncidenceGraph G
                  (corr.replacementSeries.data.coloring replacementLast)
                  available.gamma available.delta).neighborSet
                    (Sum.inl newChoicePE.vertex)) := Fintype.ofFinite _
            rw [← SimpleGraph.card_neighborSet_eq_degree] at hreplacementLeafDegree
            have hsub := Fintype.card_le_one_iff.mp
              hreplacementLeafDegree
            intro a ha b hb
            exact congrArg Subtype.val
              (hsub ⟨a, ha⟩ ⟨b, hb⟩)
          have hreturnNeOld : available.returnVertex ≠
              oldChoice.vertex := by
            intro heq
            have hsupport : Sum.inl newChoicePE.vertex ∈
                available.cycle.walk.support := by
              rw [hnewVertexOld, ← heq]
              apply available.returnPathOnCycle
              simp
            let rotated := available.cycle.walk.rotate
              (Sum.inl newChoicePE.vertex) hsupport
            have hrotated : rotated.IsCycle :=
              available.cycle.isCycle.rotate hsupport
            have hfirst : (TwoColorIncidenceGraph G
                (corr.replacementSeries.data.coloring replacementLast)
                available.gamma available.delta).Adj
                  (Sum.inl newChoicePE.vertex) rotated.snd :=
              rotated.adj_snd hrotated.not_nil
            have hlast : (TwoColorIncidenceGraph G
                (corr.replacementSeries.data.coloring replacementLast)
                available.gamma available.delta).Adj
                  (Sum.inl newChoicePE.vertex) rotated.penultimate :=
              (rotated.adj_penultimate hrotated.not_nil).symm
            exact hrotated.snd_ne_penultimate
              (hreplacementLeaf hfirst hlast)
          have horiginalRoundsLess : originalPrefix.rounds < ett.rounds := by
            rw [hr]
            omega
          have holdRootOnly := peRootOnly originalPrefix horiginalPositive
            horiginalRoundsLess hprefixMP originalPrefix.rounds
            originalPrefix.series rfl HEq.rfl oldi.succ oldChoice.vertex
            oldGamma oldChoice.color (by simp) oldCurrentKind
            oldCurrentVertex oldCurrentGamma oldCurrentDelta
            oldCurrentProper oldCurrentOne
          have hreplacementPositive : 0 < corr.replacementETT.rounds := by
            rw [corr.rungAgreement]
            exact horiginalPositive
          have hreplacementLess : corr.replacementETT.rounds < ett.rounds := by
            rw [corr.rungAgreement]
            exact horiginalRoundsLess
          have hnewRootOnly := peRootOnly corr.replacementETT
            hreplacementPositive hreplacementLess hcorrMP originalPrefix.rounds
            corr.replacementSeries corr.rungAgreement corr.seriesPresentation
            oldi.succ newChoicePE.vertex newGamma newChoicePE.color
            (by simp) newCurrentKind newCurrentVertex newCurrentGamma
            newCurrentDelta newCurrentProper newCurrentOne
          have hcomponentOnly : ∀ w,
              w ∈ TreeSequenceVertexSet
                (originalPrefix.series.data.tree oldi.succ.castSucc) →
              (Sum.inl w ∈ TwoColorComponent G
                (ett.series.data.coloring q.castSucc)
                available.gamma available.delta (Sum.inl oldChoice.vertex) ↔
                w = oldChoice.vertex) := by
            simpa only [holdPostOriginal, holdGammaAvailable,
              holdDeltaAvailable] using holdRootOnly
          have hreplacementComponentOnly : ∀ w,
              w ∈ TreeSequenceVertexSet
                (corr.replacementSeries.data.tree oldi.succ.castSucc) →
              (Sum.inl w ∈ TwoColorComponent G sigmaPrev
                available.gamma available.delta (Sum.inl oldChoice.vertex) ↔
                w = oldChoice.vertex) := by
            simpa only [hnewPostSigmaPrev, hnewGammaAvailable,
              hnewDeltaAvailable, hnewVertexOld] using hnewRootOnly
          have hreplacementRootAvoidsReturn :
              Sum.inl available.returnVertex ∉ TwoColorComponent G sigmaPrev
                available.gamma available.delta (Sum.inl oldChoice.vertex) := by
            intro hreturn
            apply hreturnNeOld
            apply (hreplacementComponentOnly available.returnVertex ?_).1 hreturn
            rw [hbaseTree]
            simpa only [holdIndex] using hreturnInOldEarlier
          have hcomponentDistinct :
              TwoColorComponent G
                  (ett.series.data.coloring q.castSucc)
                  available.gamma available.delta
                  (Sum.inl oldChoice.vertex) ≠
                TwoColorComponent G
                  (ett.series.data.coloring q.castSucc)
                  available.gamma available.delta
                  (Sum.inr available.edge) := by
            intro heq
            have hreturnExitOriginal : Sum.inl available.returnVertex ∈
                TwoColorComponent G
                  (ett.series.data.coloring q.castSucc)
                  available.gamma available.delta
                  (Sum.inl oldChoice.vertex) := by
              rw [heq]
              exact hreturnInQ
            have hreturnExitSecond : Sum.inl available.returnVertex ∈
                TwoColorComponent G sigmaPrev available.gamma available.delta
                  (Sum.inl oldChoice.vertex) := by
              have hreturnEq := (hcomponentOnly available.returnVertex
                (by simpa only [holdIndex] using hreturnInOldEarlier)).1
                  hreturnExitOriginal
              rw [hreturnEq]
              rfl
            exact hreplacementRootAvoidsReturn hreturnExitSecond
          have hQMeetsFinal : ∃ v ∈ TreeSequenceVertexSet
              (originalPrefix.series.data.tree
                (Fin.last (originalPrefix.rounds + 1))),
              Sum.inl v ∈ TwoColorComponent G
                (ett.series.data.coloring q.castSucc)
                available.gamma available.delta
                (Sum.inr available.edge) :=
            ⟨available.returnVertex, hreturnInFinal, hreturnInQ⟩
          have hlowerColor : originalPrefix.series.data.coloring
                (Fin.last originalPrefix.rounds) =
              ett.series.data.coloring q.castSucc := by
            simpa [replacementLast] using hbaseFinalColor
          have hstableLower : StableColoring
              (originalPrefix.series.data.tree
                (Fin.last (originalPrefix.rounds + 1)))
              (TashkinovStoredColors originalPrefix.series.data
                (Fin.last originalPrefix.rounds))
              (originalPrefix.series.data.coloring
                (Fin.last originalPrefix.rounds))
              (ett.series.data.coloring q.castSucc) := by
            rw [hlowerColor]
            exact ⟨(by intros; rfl), (by intros; rfl)⟩
          have hdeltaLower : available.delta ∈ TreeMissingColors
              (ett.series.data.coloring q.castSucc)
              (originalPrefix.series.data.tree
                (Fin.last (originalPrefix.rounds + 1))) := by
            simp only [TreeMissingColors, Finset.mem_biUnion]
            exact ⟨oldChoice.vertex, holdVertexFinal,
              holdDeltaOriginal⟩
          have hlowerPackage := hlower originalPrefix
            horiginalPositive horiginalRoundsLess hprefixMP
          have hinterchangeLower := hlowerPackage.1
            (ett.series.data.coloring q.castSucc) previousProper
            previousOneUncolored hstableLower available.gamma
            available.delta (Or.inr hdeltaLower)
          have hcycleComponent :=
            TwoColorInterchangeableDistinctComponentCycle G
              (originalPrefix.series.data.tree
                (Fin.last (originalPrefix.rounds + 1)))
              (ett.series.data.coloring q.castSucc)
              available.gamma available.delta previousProper
              (Sum.inl oldChoice.vertex) (Sum.inr available.edge)
              hpathComponent.1 hinterchangeLower hpathMeetsFinal
              hQMeetsFinal hcomponentDistinct
          obtain ⟨originalCycle, hcycleFull⟩ := hcycleComponent
          let oldEarlier : Fin (ett.rounds + 1) :=
            Fin.castLE (by omega) earlierPrefix
          have holdEarlierMap : oldEarlier =
              Fin.castLE (by omega) earlierPrefix := rfl
          have hfullEarlierKind : ett.series.data.kind oldEarlier =
              some TashkinovExtensionKind.PE := by
            rw [holdEarlierMap, ← (hprefixData earlierPrefix).2.2.2.1]
            exact hbaseEarlierKind
          have hfullStep := ett.series.certified oldEarlier
          generalize hfullTarget : oldEarlier = fullTarget at hfullStep
          cases hfullStep with
          | initial tripleFull seedLengthFull initialColoringFull
              initialStoredFull initialEdgesFull initialKindFull
              initialVertexFull initialOutsideFull initialDeltaFull
              initialGammaFull initialClosureFull =>
              have hk : ett.series.data.kind 0 =
                  some TashkinovExtensionKind.PE := by
                rw [← hfullTarget]
                exact hfullEarlierKind
              have hbad := initialKindFull.symm.trans hk
              simp at hbad
          | SE fulli fullPreviousProper fullPreviousOne
              fullPreviousClosed fullPreviousNotStrong fullNoRE
              fullChoice fullAlternative fullCurrentColoring
              fullCurrentStored fullCurrentEdges fullCurrentKind
              fullCurrentVertex fullCurrentOutside fullCurrentDelta
              fullCurrentGamma fullAdjoined fullAdjoinedExactly
              fullClosedExtension fullOrderedExtension
              fullStrictExtension =>
              have hk : ett.series.data.kind fulli.succ =
                  some TashkinovExtensionKind.PE := by
                rw [← hfullTarget]
                exact hfullEarlierKind
              have hbad := fullCurrentKind.symm.trans hk
              cases hbad
          | RE fulli fullPreviousProper fullPreviousOne
              fullPreviousClosed fullPreviousNotStrong fullAvailable
              fullCurrentColoring fullCurrentStored fullCurrentEdges
              fullCurrentKind fullCurrentVertex fullCurrentOutside
              fullCurrentDelta fullCurrentGamma fullAdjoined
              fullAdjoinedExactly fullClosedExtension
              fullOrderedExtension fullStrictExtension =>
              have hk : ett.series.data.kind fulli.succ =
                  some TashkinovExtensionKind.PE := by
                rw [← hfullTarget]
                exact hfullEarlierKind
              have hbad := fullCurrentKind.symm.trans hk
              cases hbad
          | PE fulli fullPreviousProper fullPreviousOne
              fullPreviousClosed fullPreviousNotStrong fullNoRE
              fullChoice fullAlternativeFails fullGamma fullGammaRule
              fullSecond fullSecondProper fullSecondOne
              fullSecondStable fullExit fullCurrentColoring
              fullCurrentProper fullCurrentOne fullCurrentStored
              fullCurrentEdges fullCurrentKind fullCurrentVertex
              fullCurrentOutside fullCurrentDelta fullCurrentGamma
              fullClosedExtension fullOrderedExtension
              fullStrictExtension =>
              have hfullIndex : fulli.succ = oldEarlier := by
                simpa using hfullTarget.symm
              have htreePrefixFull :
                  originalPrefix.series.data.tree
                      oldi.succ.castSucc =
                    ett.series.data.tree fulli.succ.castSucc := by
                calc
                  originalPrefix.series.data.tree
                      oldi.succ.castSucc =
                      ett.series.data.tree
                        (Fin.castLE (by omega)
                          oldi.succ.castSucc) :=
                    hprefixTrees oldi.succ.castSucc
                  _ = ett.series.data.tree fulli.succ.castSucc := by
                    congr 1
                    apply Fin.ext
                    have holdVals := congrArg Fin.val holdIndex
                    have hfullVals := congrArg Fin.val hfullIndex
                    change oldi.val + 1 = earlierPrefix.val at holdVals
                    change fulli.val + 1 = earlierPrefix.val at hfullVals
                    simp only [Fin.val_castLE, Fin.val_castSucc,
                      Fin.val_succ]
                    omega
              let prefixChoiceOnFull : MaximumDefectiveChoice G e0
                  (ett.series.data.tree fulli.succ.castSucc)
                  (TashkinovStoredColors originalPrefix.series.data
                    oldi.castSucc)
                  (originalPrefix.series.data.coloring oldi.castSucc) :=
                htreePrefixFull ▸ oldChoice
              have htransportFull := transportChoiceFields
                htreePrefixFull
                (TashkinovStoredColors originalPrefix.series.data
                  oldi.castSucc)
                (originalPrefix.series.data.coloring oldi.castSucc)
                oldChoice
              have hprefEdgeCast : prefixChoiceOnFull.edge =
                  oldChoice.edge := htransportFull.1
              have hprefVertexCast : prefixChoiceOnFull.vertex =
                  oldChoice.vertex := htransportFull.2.1
              have hprefOtherCast : prefixChoiceOnFull.otherEndpoint =
                  oldChoice.otherEndpoint := htransportFull.2.2.1
              have hprefColorCast : prefixChoiceOnFull.color =
                  oldChoice.color := htransportFull.2.2.2
              have hfullMap : Fin.castLE (by omega) earlierPrefix =
                  oldEarlier := by rfl
              have hfullEdgePairs :
                  ({prefixChoiceOnFull.edge} : Finset E) =
                    {fullChoice.edge} := by
                have hprefEdges :
                    originalPrefix.series.data.connectingEdges
                        earlierPrefix = {oldChoice.edge} := by
                  simpa only [holdIndex] using oldCurrentEdges
                have hfullEdges : ett.series.data.connectingEdges
                    oldEarlier = {fullChoice.edge} := by
                  simpa only [hfullIndex] using fullCurrentEdges
                simpa only [hprefEdgeCast] using
                  hprefEdges.symm.trans
                    (((hprefixData earlierPrefix).2.2.1.trans
                      (by rw [hfullMap])).trans hfullEdges)
              have hfullColorPairs :
                  ({prefixChoiceOnFull.color, oldGamma} :
                      Finset (Fin k)) =
                    {fullChoice.color, fullGamma} := by
                have hprefStored : originalPrefix.series.data.stored
                    earlierPrefix = {oldChoice.color, oldGamma} := by
                  simpa only [holdIndex] using oldCurrentStored
                have hfullStored : ett.series.data.stored oldEarlier =
                    {fullChoice.color, fullGamma} := by
                  simpa only [hfullIndex] using fullCurrentStored
                simpa only [hprefColorCast] using
                  hprefStored.symm.trans
                    (((hprefixData earlierPrefix).2.1.trans
                      (by rw [hfullMap])).trans hfullStored)
              have hfullEdgeIdentity : fullChoice.edge =
                  prefixChoiceOnFull.edge := by
                apply Finset.mem_singleton.mp
                rw [hfullEdgePairs]
                exact Finset.mem_singleton_self _
              have hfullEnds : s(prefixChoiceOnFull.vertex,
                    prefixChoiceOnFull.otherEndpoint) =
                  s(fullChoice.vertex, fullChoice.otherEndpoint) := by
                calc
                  s(prefixChoiceOnFull.vertex,
                      prefixChoiceOnFull.otherEndpoint) =
                      G.ends prefixChoiceOnFull.edge :=
                    prefixChoiceOnFull.edgeEnds.symm
                  _ = G.ends fullChoice.edge :=
                    congrArg G.ends hfullEdgeIdentity.symm
                  _ = s(fullChoice.vertex,
                      fullChoice.otherEndpoint) := fullChoice.edgeEnds
              have hfullVertexIdentity : fullChoice.vertex =
                  prefixChoiceOnFull.vertex := by
                rcases Sym2.eq_iff.mp hfullEnds with
                    hstraight | hcross
                · exact hstraight.1.symm
                · exfalso
                  exact fullChoice.otherOutside
                    (hcross.1 ▸
                      prefixChoiceOnFull.vertexDefective.1)
              have hfullOtherIdentity : fullChoice.otherEndpoint =
                  prefixChoiceOnFull.otherEndpoint := by
                rcases Sym2.eq_iff.mp hfullEnds with
                    hstraight | hcross
                · exact hstraight.2.symm
                · exfalso
                  exact prefixChoiceOnFull.otherOutside
                    (hcross.2 ▸ fullChoice.vertexDefective.1)
              obtain ⟨hfullDeltaMissing, hfullGammaNotMissing,
                  hfullColorNe⟩ := pePostStatus
                (ett.series.data.tree fulli.succ.castSucc)
                (TashkinovStoredColors ett.series.data fulli.castSucc)
                (ett.series.data.coloring fulli.castSucc)
                fullChoice fullGamma fullSecond fullSecondProper
                fullSecondStable fullGammaRule.1
              rw [← fullCurrentColoring] at hfullDeltaMissing hfullGammaNotMissing
              have hpostColorPrefixFull :
                  originalPrefix.series.data.coloring oldi.succ =
                    ett.series.data.coloring fulli.succ := by
                calc
                  originalPrefix.series.data.coloring oldi.succ =
                      originalPrefix.series.data.coloring
                        earlierPrefix := by rw [holdIndex]
                  _ = ett.series.data.coloring
                        (Fin.castLE (by omega) earlierPrefix) :=
                    (hprefixData earlierPrefix).1
                  _ = ett.series.data.coloring fulli.succ := by
                    congr 1
              have hmissingPrefixFull : MissingColors G
                  (originalPrefix.series.data.coloring oldi.succ)
                    prefixChoiceOnFull.vertex =
                MissingColors G
                  (ett.series.data.coloring fulli.succ)
                    fullChoice.vertex := by
                rw [hpostColorPrefixFull, hfullVertexIdentity]
              have hprefDeltaForFull : prefixChoiceOnFull.color ∈
                  MissingColors G
                    (originalPrefix.series.data.coloring oldi.succ)
                    prefixChoiceOnFull.vertex := by
                simpa only [hprefColorCast, hprefVertexCast] using
                  holdDeltaMissing
              have hprefGammaForFull : oldGamma ∉ MissingColors G
                  (originalPrefix.series.data.coloring oldi.succ)
                  prefixChoiceOnFull.vertex := by
                simpa only [hprefVertexCast] using
                  holdGammaNotMissing
              have hfullIdentified := TdEarlierPEWitnessIdentification
                G k e0
                (ett.series.data.tree fulli.succ.castSucc)
                (TashkinovStoredColors originalPrefix.series.data
                  oldi.castSucc)
                (TashkinovStoredColors ett.series.data fulli.castSucc)
                (originalPrefix.series.data.coloring oldi.castSucc)
                (ett.series.data.coloring fulli.castSucc)
                prefixChoiceOnFull fullChoice oldGamma fullGamma
                (originalPrefix.series.data.coloring oldi.succ)
                (ett.series.data.coloring fulli.succ)
                hfullEdgePairs hfullColorPairs hmissingPrefixFull
                hprefDeltaForFull hprefGammaForFull
                hfullDeltaMissing hfullGammaNotMissing
              rcases hfullIdentified with ⟨hfullIdentifiedEdge,
                hfullIdentifiedVertex, hfullIdentifiedOther,
                hfullIdentifiedDelta, hfullIdentifiedGamma⟩
              have hfullDeltaAvailable : fullChoice.color =
                  available.delta :=
                hfullIdentifiedDelta.trans
                  (hprefColorCast.trans holdDeltaAvailable)
              have hfullGammaAvailable : fullGamma =
                  available.gamma :=
                hfullIdentifiedGamma.trans holdGammaAvailable
              have hcurrentIndex : q.castSucc.succ =
                  q.succ.castSucc := by
                apply Fin.ext
                rfl
              have hcertificateCurrentTree :
                  ett.series.data.tree q.castSucc.succ =
                    corr.replacementSeries.data.tree
                      replacementLast.succ := by
                rw [hcurrentIndex, hreplacementCurrentTree]
              have hprefixEarlierTree :
                  originalPrefix.series.data.tree
                      earlierPrefix.castSucc =
                    ett.series.data.tree oldEarlier.castSucc := by
                calc
                  originalPrefix.series.data.tree
                      earlierPrefix.castSucc =
                      ett.series.data.tree
                        (Fin.castLE (by omega)
                          earlierPrefix.castSucc) :=
                    hprefixTrees earlierPrefix.castSucc
                  _ = ett.series.data.tree oldEarlier.castSucc := by
                    congr 1
              have horiginalPathInQ : ∀ z,
                  z ∈ originalReturnPath.support →
                    z ∈ TwoColorComponent G
                      (ett.series.data.coloring q.castSucc)
                      available.gamma available.delta
                      (Sum.inr available.edge) := by
                intro z hz
                obtain ⟨m, hm, hmle⟩ :=
                  SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hz
                change originalReturnGraph.connectedComponentMk z =
                  originalReturnGraph.connectedComponentMk
                    (Sum.inr available.edge)
                rw [← hm]
                exact (SimpleGraph.ConnectedComponent.sound
                  (originalReturnPath.take m).reachable).symm
              let originalCertificate : RevisitingExtensionCertificate
                  ett.series.data q.castSucc := {
                earlier := oldEarlier
                earlierPositive := by
                  simpa [oldEarlier, earlierPrefix] using
                    available.earlierPositive
                earlierAtMost := by
                  have hle := available.earlierAtMost
                  have hlastVals := congrArg Fin.val hlastMap
                  simpa [oldEarlier, earlierPrefix] using
                    hle.trans_eq hlastVals
                earlierPE := hfullEarlierKind
                interveningRevisiting := by
                  intro j hjPositive hjLower hjUpper
                  let jPrefix : Fin (originalPrefix.rounds + 1) :=
                    ⟨j.val, by
                      have hjBound := j.isLt
                      simp [q, hr] at hjUpper ⊢
                      omega⟩
                  have hjMap : Fin.castLE (by omega) jPrefix = j := by
                    apply Fin.ext
                    rfl
                  calc
                    ett.series.data.kind j =
                        ett.series.data.kind
                          (Fin.castLE (by omega) jPrefix) := by
                      rw [hjMap]
                    _ = originalPrefix.series.data.kind jPrefix :=
                      (hprefixData jPrefix).2.2.2.1.symm
                    _ = corr.replacementSeries.data.kind jPrefix :=
                      (corr.extensionKindsAgree jPrefix).symm
                    _ = some TashkinovExtensionKind.RE := by
                      apply available.interveningRevisiting jPrefix
                      · exact hjPositive
                      · simpa [jPrefix, oldEarlier,
                          earlierPrefix] using hjLower
                      · have hlastVals :=
                            congrArg Fin.val hlastMap
                        simpa [jPrefix, replacementLast] using
                          hjUpper.trans_eq hlastVals.symm
                gamma := available.gamma
                delta := available.delta
                earlierGamma := by
                  rw [← hfullIndex, fullCurrentGamma,
                    hfullGammaAvailable]
                earlierDelta := by
                  rw [← hfullIndex, fullCurrentDelta,
                    hfullDeltaAvailable]
                cycle := originalCycle
                meetsEarlier := by
                  refine ⟨available.returnVertex, ?_, ?_⟩
                  · rw [← hprefixEarlierTree]
                    exact hreturnInOldEarlier
                  · exact (hcycleFull _).2 hreturnInQ
                leavesCurrent := by
                  refine ⟨available.outsideEndpoint, ?_, ?_⟩
                  · rw [hcertificateCurrentTree]
                    exact available.outsideNotCurrent
                  · exact (hcycleFull _).2 houtsideInQ
                edge := available.edge
                edgeOnCycle := (hcycleFull _).2 rfl
                edgeBoundary := by
                  rw [hcertificateCurrentTree]
                  exact available.edgeBoundary
                insideEndpoint := available.insideEndpoint
                outsideEndpoint := available.outsideEndpoint
                insideInCurrent := by
                  rw [hcertificateCurrentTree]
                  exact available.insideInCurrent
                outsideNotCurrent := by
                  rw [hcertificateCurrentTree]
                  exact available.outsideNotCurrent
                edgeEnds := available.edgeEnds
                returnVertex := available.returnVertex
                returnInEarlier := by
                  rw [← hprefixEarlierTree]
                  exact hreturnInOldEarlier
                returnPath := originalReturnPath
                returnPathIsPath := horiginalReturnIsPath
                returnPathOnCycle := by
                  intro z hz
                  exact (hcycleFull z).2 (horiginalPathInQ z hz)
                returnPathInternal := by
                  intro v hv
                  have hvAvailable : Sum.inl v ∈
                      available.returnPath.support :=
                    (horiginalReturnSupport (Sum.inl v)).mp hv
                  rw [hcertificateCurrentTree]
                  exact available.returnPathInternal v hvAvailable
              }
              exact noRevisiting ⟨originalCertificate⟩
