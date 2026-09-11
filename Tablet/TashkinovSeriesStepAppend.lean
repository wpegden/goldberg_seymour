import Tablet.ParallelExtensionColorAppend
import Tablet.RevisitingExtensionCertificateAppend
import Tablet.TashkinovSeriesDataAppendEquations
import Tablet.TashkinovSeriesStep
import Tablet.TashkinovStoredColorsAppend
set_option maxHeartbeats 1200000

-- [TABLET NODE: TashkinovSeriesStepAppend]
theorem TashkinovSeriesStepAppend {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq E] (G : LooplessMultigraph V E) (k rounds : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k)
    (data : TashkinovSeriesData G k rounds e0)
    (newTree : TreeSequence G e0)
    (newColoring : PartialEdgeColoring E k)
    (newStored : Finset (Fin k))
    (newConnectingEdges : Finset E)
    (newKind : Option TashkinovExtensionKind)
    (newChosenVertex newOutsideVertex : Option V)
    (newDelta newGamma : Option (Fin k))
    (j : Fin (rounds + 1))
    (step : TashkinovSeriesStep G k rounds e0 input data j) :
    TashkinovSeriesStep G k (rounds + 1) e0 input
      (TashkinovSeriesDataAppend data newTree newColoring newStored
        newConnectingEdges newKind newChosenVertex newOutsideVertex newDelta newGamma)
      j.castSucc := by
-- BODY
  let appended := TashkinovSeriesDataAppend data newTree newColoring
    newStored newConnectingEdges newKind newChosenVertex newOutsideVertex
    newDelta newGamma
  rcases TashkinovSeriesDataAppendEquations data newTree newColoring newStored newConnectingEdges
      newKind newChosenVertex newOutsideVertex newDelta newGamma with
    ⟨treeOld, treeLast, slotsOld, coloringLast, storedLast, edgesLast,
      kindLast, chosenLast, outsideLast, deltaLast, gammaLast⟩
  have treeZeroIndex : (0 : Fin ((rounds + 1) + 2)) =
      (0 : Fin (rounds + 2)).castSucc := by ext; rfl
  have treeOneIndex : (1 : Fin ((rounds + 1) + 2)) =
      (1 : Fin (rounds + 2)).castSucc := by ext; rfl
  have slotZeroIndex : (0 : Fin ((rounds + 1) + 1)) =
      (0 : Fin (rounds + 1)).castSucc := by ext; rfl
  cases step with
  | initial triple seedLength initialColoring initialStored initialEdges initialKind
      initialVertex initialOutside initialDelta initialGamma initialClosure =>
      apply TashkinovSeriesStep.initial triple
      · rw [treeZeroIndex, treeOld]
        exact seedLength
      · rw [slotZeroIndex, (slotsOld 0).1]
        exact initialColoring
      · rw [slotZeroIndex, (slotsOld 0).2.1]
        exact initialStored
      · rw [slotZeroIndex, (slotsOld 0).2.2.1]
        exact initialEdges
      · rw [slotZeroIndex, (slotsOld 0).2.2.2.1]
        exact initialKind
      · rw [slotZeroIndex, (slotsOld 0).2.2.2.2.1]
        exact initialVertex
      · rw [slotZeroIndex, (slotsOld 0).2.2.2.2.2.1]
        exact initialOutside
      · rw [slotZeroIndex, (slotsOld 0).2.2.2.2.2.2.1]
        exact initialDelta
      · rw [slotZeroIndex, (slotsOld 0).2.2.2.2.2.2.2]
        exact initialGamma
      · rw [treeZeroIndex, treeOneIndex, treeOld, treeOld,
          slotZeroIndex, (slotsOld 0).1]
        exact initialClosure
  | SE i previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternative
      currentColoring currentStored currentEdges currentKind currentVertex
      currentOutside currentDelta currentGamma adjoined adjoinedExactly
      closedExtension orderedExtension strictExtension =>
      have slotIndexEq : i.castSucc.succ = i.succ.castSucc := by ext; rfl
      have previousTreeIndexEq : i.castSucc.succ.castSucc =
          i.succ.castSucc.castSucc := by ext; rfl
      have outputTreeIndexEq : i.castSucc.succ.succ =
          i.succ.succ.castSucc := by ext; rfl
      have previousTreeEq : appended.tree i.castSucc.succ.castSucc =
          data.tree i.succ.castSucc := by
        calc
          appended.tree i.castSucc.succ.castSucc =
              appended.tree i.succ.castSucc.castSucc :=
            congrArg appended.tree previousTreeIndexEq
          _ = data.tree i.succ.castSucc := treeOld i.succ.castSucc
      have outputTreeEq : appended.tree i.castSucc.succ.succ =
          data.tree i.succ.succ := by
        calc
          appended.tree i.castSucc.succ.succ =
              appended.tree i.succ.succ.castSucc :=
            congrArg appended.tree outputTreeIndexEq
          _ = data.tree i.succ.succ := treeOld i.succ.succ
      have previousColoringEq : appended.coloring i.castSucc.castSucc =
          data.coloring i.castSucc := (slotsOld i.castSucc).1
      have storedColorsEq : TashkinovStoredColors appended i.castSucc.castSucc =
          TashkinovStoredColors data i.castSucc :=
        TashkinovStoredColorsAppend data newTree newColoring newStored newConnectingEdges
          newKind newChosenVertex newOutsideVertex newDelta newGamma i.castSucc
      have currentColoringEq : appended.coloring i.castSucc.succ =
          data.coloring i.succ := by
        calc
          appended.coloring i.castSucc.succ =
              appended.coloring i.succ.castSucc :=
            congrArg appended.coloring slotIndexEq
          _ = data.coloring i.succ := (slotsOld i.succ).1
      have currentStoredEq : appended.stored i.castSucc.succ =
          data.stored i.succ := by
        calc
          appended.stored i.castSucc.succ = appended.stored i.succ.castSucc :=
            congrArg appended.stored slotIndexEq
          _ = data.stored i.succ := (slotsOld i.succ).2.1
      have currentEdgesEq : appended.connectingEdges i.castSucc.succ =
          data.connectingEdges i.succ := by
        calc
          appended.connectingEdges i.castSucc.succ =
              appended.connectingEdges i.succ.castSucc :=
            congrArg appended.connectingEdges slotIndexEq
          _ = data.connectingEdges i.succ := (slotsOld i.succ).2.2.1
      have currentKindEq : appended.kind i.castSucc.succ = data.kind i.succ := by
        calc
          appended.kind i.castSucc.succ = appended.kind i.succ.castSucc :=
            congrArg appended.kind slotIndexEq
          _ = data.kind i.succ := (slotsOld i.succ).2.2.2.1
      have currentVertexEq : appended.chosenVertex i.castSucc.succ =
          data.chosenVertex i.succ := by
        calc
          appended.chosenVertex i.castSucc.succ =
              appended.chosenVertex i.succ.castSucc :=
            congrArg appended.chosenVertex slotIndexEq
          _ = data.chosenVertex i.succ := (slotsOld i.succ).2.2.2.2.1
      have currentOutsideEq : appended.outsideVertex i.castSucc.succ =
          data.outsideVertex i.succ := by
        calc
          appended.outsideVertex i.castSucc.succ =
              appended.outsideVertex i.succ.castSucc :=
            congrArg appended.outsideVertex slotIndexEq
          _ = data.outsideVertex i.succ := (slotsOld i.succ).2.2.2.2.2.1
      have currentDeltaEq : appended.delta i.castSucc.succ = data.delta i.succ := by
        calc
          appended.delta i.castSucc.succ = appended.delta i.succ.castSucc :=
            congrArg appended.delta slotIndexEq
          _ = data.delta i.succ := (slotsOld i.succ).2.2.2.2.2.2.1
      have currentGammaEq : appended.gamma i.castSucc.succ = data.gamma i.succ := by
        calc
          appended.gamma i.castSucc.succ = appended.gamma i.succ.castSucc :=
            congrArg appended.gamma slotIndexEq
          _ = data.gamma i.succ := (slotsOld i.succ).2.2.2.2.2.2.2
      let Package (previousColor currentColor : PartialEdgeColoring E k)
          (previousTree outputTree : TreeSequence G e0)
          (storedColors currentStoredValue : Finset (Fin k))
          (currentEdgesValue : Finset E)
          (currentKindValue : Option TashkinovExtensionKind)
          (currentVertexValue currentOutsideValue : Option V)
          (currentDeltaValue currentGammaValue : Option (Fin k)) : Prop :=
        ∃ selectedChoice : MaximumDefectiveChoice G e0 previousTree
            storedColors previousColor,
          (∀ pi : PartialEdgeColoring E k,
            IsProperEdgeColoring G pi → IsOneEdgeUncolored pi e0 →
              StableColoring previousTree (insert selectedChoice.color storedColors)
                selectedChoice.selected pi →
              Disjoint (MissingColors G pi selectedChoice.otherEndpoint)
                (TreeMissingColors pi previousTree)) ∧
          currentColor = selectedChoice.selected ∧
          currentStoredValue = {selectedChoice.color} ∧
          currentEdgesValue = {selectedChoice.edge} ∧
          currentKindValue = some TashkinovExtensionKind.SE ∧
          currentVertexValue = some selectedChoice.vertex ∧
          currentOutsideValue = some selectedChoice.otherEndpoint ∧
          currentDeltaValue = some selectedChoice.color ∧
          currentGammaValue = none ∧
          ∃ exactAdjoined : TreeSequence G e0,
            TreeSequenceAdjoinEdge previousTree selectedChoice.edge exactAdjoined ∧
            TashkinovClosure currentColor exactAdjoined outputTree ∧
            TreeSequenceInitialSegment previousTree outputTree ∧
            previousTree.length < outputTree.length
      have oldPackage : Package (data.coloring i.castSucc) (data.coloring i.succ)
          (data.tree i.succ.castSucc) (data.tree i.succ.succ)
          (TashkinovStoredColors data i.castSucc) (data.stored i.succ)
          (data.connectingEdges i.succ) (data.kind i.succ)
          (data.chosenVertex i.succ) (data.outsideVertex i.succ)
          (data.delta i.succ) (data.gamma i.succ) := by
        exact ⟨choice, seriesAlternative, currentColoring, currentStored,
          currentEdges, currentKind, currentVertex, currentOutside, currentDelta,
          currentGamma, adjoined, adjoinedExactly, closedExtension,
          orderedExtension, strictExtension⟩
      have newPackage : Package (appended.coloring i.castSucc.castSucc)
          (appended.coloring i.castSucc.succ)
          (appended.tree i.castSucc.succ.castSucc)
          (appended.tree i.castSucc.succ.succ)
          (TashkinovStoredColors appended i.castSucc.castSucc)
          (appended.stored i.castSucc.succ)
          (appended.connectingEdges i.castSucc.succ)
          (appended.kind i.castSucc.succ)
          (appended.chosenVertex i.castSucc.succ)
          (appended.outsideVertex i.castSucc.succ)
          (appended.delta i.castSucc.succ) (appended.gamma i.castSucc.succ) := by
        rw [previousColoringEq, currentColoringEq, previousTreeEq, outputTreeEq,
          storedColorsEq, currentStoredEq, currentEdgesEq, currentKindEq,
          currentVertexEq, currentOutsideEq, currentDeltaEq, currentGammaEq]
        exact oldPackage
      rcases newPackage with ⟨newChoice, newSeriesAlternative,
        newCurrentColoring, newCurrentStored, newCurrentEdges, newCurrentKind,
        newCurrentVertex, newCurrentOutside, newCurrentDelta, newCurrentGamma,
        newAdjoined, newAdjoinedExactly, newClosedExtension,
        newOrderedExtension, newStrictExtension⟩
      have newNoRevisiting : ¬ Nonempty
          (RevisitingExtensionCertificate appended i.castSucc.castSucc) := by
        rintro ⟨newCertificate⟩
        rcases (RevisitingExtensionCertificateAppend data newTree newColoring newStored
          newConnectingEdges newKind newChosenVertex newOutsideVertex
          newDelta newGamma i.castSucc).1 newCertificate with ⟨oldCertificate, -⟩
        exact noRevisiting ⟨oldCertificate⟩
      have lifted : TashkinovSeriesStep G k (rounds + 1) e0 input appended
          i.castSucc.succ := by
        apply TashkinovSeriesStep.SE (i := i.castSucc) (choice := newChoice)
          (adjoined := newAdjoined)
        · rw [previousColoringEq]
          exact previousProper
        · rw [previousColoringEq]
          exact previousOneUncolored
        · rw [previousColoringEq, previousTreeEq]
          exact previousClosed
        · rw [previousColoringEq, previousTreeEq]
          exact previousNotStronglyClosed
        · exact newNoRevisiting
        · exact newSeriesAlternative
        · exact newCurrentColoring
        · exact newCurrentStored
        · exact newCurrentEdges
        · exact newCurrentKind
        · exact newCurrentVertex
        · exact newCurrentOutside
        · exact newCurrentDelta
        · exact newCurrentGamma
        · exact newAdjoinedExactly
        · exact newClosedExtension
        · exact newOrderedExtension
        · exact newStrictExtension
      rw [← slotIndexEq]
      exact lifted

  | PE i previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternativeFails
      gamma gammaRule secondStable secondStableProper secondStableOneUncolored
      secondStableRelation exitWitness currentColoring currentProper
      currentOneUncolored currentStored currentEdges currentKind currentVertex
      currentOutside currentDelta currentGamma closedExtension orderedExtension
      strictExtension =>
      have slotIndexEq : i.castSucc.succ = i.succ.castSucc := by ext; rfl
      have previousTreeIndexEq : i.castSucc.succ.castSucc =
          i.succ.castSucc.castSucc := by ext; rfl
      have outputTreeIndexEq : i.castSucc.succ.succ =
          i.succ.succ.castSucc := by ext; rfl
      have previousTreeEq : appended.tree i.castSucc.succ.castSucc =
          data.tree i.succ.castSucc := by
        calc
          appended.tree i.castSucc.succ.castSucc =
              appended.tree i.succ.castSucc.castSucc :=
            congrArg appended.tree previousTreeIndexEq
          _ = data.tree i.succ.castSucc := treeOld i.succ.castSucc
      have outputTreeEq : appended.tree i.castSucc.succ.succ =
          data.tree i.succ.succ := by
        calc
          appended.tree i.castSucc.succ.succ =
              appended.tree i.succ.succ.castSucc :=
            congrArg appended.tree outputTreeIndexEq
          _ = data.tree i.succ.succ := treeOld i.succ.succ
      have previousColoringEq : appended.coloring i.castSucc.castSucc =
          data.coloring i.castSucc := (slotsOld i.castSucc).1
      have storedColorsEq : TashkinovStoredColors appended i.castSucc.castSucc =
          TashkinovStoredColors data i.castSucc :=
        TashkinovStoredColorsAppend data newTree newColoring newStored newConnectingEdges
          newKind newChosenVertex newOutsideVertex newDelta newGamma i.castSucc
      have currentColoringEq : appended.coloring i.castSucc.succ =
          data.coloring i.succ := by
        calc
          appended.coloring i.castSucc.succ =
              appended.coloring i.succ.castSucc :=
            congrArg appended.coloring slotIndexEq
          _ = data.coloring i.succ := (slotsOld i.succ).1
      have currentStoredEq : appended.stored i.castSucc.succ =
          data.stored i.succ := by
        calc
          appended.stored i.castSucc.succ = appended.stored i.succ.castSucc :=
            congrArg appended.stored slotIndexEq
          _ = data.stored i.succ := (slotsOld i.succ).2.1
      have currentEdgesEq : appended.connectingEdges i.castSucc.succ =
          data.connectingEdges i.succ := by
        calc
          appended.connectingEdges i.castSucc.succ =
              appended.connectingEdges i.succ.castSucc :=
            congrArg appended.connectingEdges slotIndexEq
          _ = data.connectingEdges i.succ := (slotsOld i.succ).2.2.1
      have currentKindEq : appended.kind i.castSucc.succ = data.kind i.succ := by
        calc
          appended.kind i.castSucc.succ = appended.kind i.succ.castSucc :=
            congrArg appended.kind slotIndexEq
          _ = data.kind i.succ := (slotsOld i.succ).2.2.2.1
      have currentVertexEq : appended.chosenVertex i.castSucc.succ =
          data.chosenVertex i.succ := by
        calc
          appended.chosenVertex i.castSucc.succ =
              appended.chosenVertex i.succ.castSucc :=
            congrArg appended.chosenVertex slotIndexEq
          _ = data.chosenVertex i.succ := (slotsOld i.succ).2.2.2.2.1
      have currentOutsideEq : appended.outsideVertex i.castSucc.succ =
          data.outsideVertex i.succ := by
        calc
          appended.outsideVertex i.castSucc.succ =
              appended.outsideVertex i.succ.castSucc :=
            congrArg appended.outsideVertex slotIndexEq
          _ = data.outsideVertex i.succ := (slotsOld i.succ).2.2.2.2.2.1
      have currentDeltaEq : appended.delta i.castSucc.succ = data.delta i.succ := by
        calc
          appended.delta i.castSucc.succ = appended.delta i.succ.castSucc :=
            congrArg appended.delta slotIndexEq
          _ = data.delta i.succ := (slotsOld i.succ).2.2.2.2.2.2.1
      have currentGammaEq : appended.gamma i.castSucc.succ = data.gamma i.succ := by
        calc
          appended.gamma i.castSucc.succ = appended.gamma i.succ.castSucc :=
            congrArg appended.gamma slotIndexEq
          _ = data.gamma i.succ := (slotsOld i.succ).2.2.2.2.2.2.2
      let oldRule := fun selected v gamma =>
        ParallelExtensionColor data i.castSucc selected v gamma
      let newRule := fun selected v gamma =>
        ParallelExtensionColor appended i.castSucc.castSucc selected v gamma
      have ruleEq : newRule = oldRule := by
        funext selected v gamma
        apply propext
        exact ParallelExtensionColorAppend data newTree newColoring newStored
          newConnectingEdges newKind newChosenVertex newOutsideVertex
          newDelta newGamma i.castSucc selected v gamma
      let Package (rule : PartialEdgeColoring E k → V → Fin k → Prop)
          (previousColor currentColor : PartialEdgeColoring E k)
          (previousTree outputTree : TreeSequence G e0)
          (storedColors currentStoredValue : Finset (Fin k))
          (currentEdgesValue : Finset E)
          (currentKindValue : Option TashkinovExtensionKind)
          (currentVertexValue currentOutsideValue : Option V)
          (currentDeltaValue currentGammaValue : Option (Fin k)) : Prop :=
        ∃ selectedChoice : MaximumDefectiveChoice G e0 previousTree
            storedColors previousColor,
          (∃ rho : PartialEdgeColoring E k,
            IsProperEdgeColoring G rho ∧ IsOneEdgeUncolored rho e0 ∧
              StableColoring previousTree (insert selectedChoice.color storedColors)
                selectedChoice.selected rho ∧
              ¬ Disjoint (MissingColors G rho selectedChoice.otherEndpoint)
                (TreeMissingColors rho previousTree)) ∧
          ∃ selectedGamma : Fin k,
            rule selectedChoice.selected selectedChoice.vertex selectedGamma ∧
            ∃ stableColoring : PartialEdgeColoring E k,
              IsProperEdgeColoring G stableColoring ∧
              IsOneEdgeUncolored stableColoring e0 ∧
              StableColoring previousTree (insert selectedChoice.color storedColors)
                selectedChoice.selected stableColoring ∧
              TreeExit previousTree stableColoring selectedGamma
                selectedChoice.color selectedChoice.vertex ∧
              currentColor = TwoColorComponentSwap G stableColoring selectedGamma
                selectedChoice.color (Sum.inl selectedChoice.vertex) ∧
              IsProperEdgeColoring G currentColor ∧
              IsOneEdgeUncolored currentColor e0 ∧
              currentStoredValue = {selectedChoice.color, selectedGamma} ∧
              currentEdgesValue = {selectedChoice.edge} ∧
              currentKindValue = some TashkinovExtensionKind.PE ∧
              currentVertexValue = some selectedChoice.vertex ∧
              currentOutsideValue = some selectedChoice.otherEndpoint ∧
              currentDeltaValue = some selectedChoice.color ∧
              currentGammaValue = some selectedGamma ∧
              TashkinovClosure currentColor previousTree outputTree ∧
              TreeSequenceInitialSegment previousTree outputTree ∧
              previousTree.length < outputTree.length
      have oldPackage : Package oldRule (data.coloring i.castSucc)
          (data.coloring i.succ) (data.tree i.succ.castSucc)
          (data.tree i.succ.succ) (TashkinovStoredColors data i.castSucc)
          (data.stored i.succ) (data.connectingEdges i.succ)
          (data.kind i.succ) (data.chosenVertex i.succ)
          (data.outsideVertex i.succ) (data.delta i.succ) (data.gamma i.succ) := by
        exact ⟨choice, seriesAlternativeFails, gamma, gammaRule, secondStable,
          secondStableProper, secondStableOneUncolored, secondStableRelation,
          exitWitness, currentColoring, currentProper, currentOneUncolored,
          currentStored, currentEdges, currentKind, currentVertex, currentOutside,
          currentDelta, currentGamma, closedExtension, orderedExtension,
          strictExtension⟩
      have newPackage : Package newRule (appended.coloring i.castSucc.castSucc)
          (appended.coloring i.castSucc.succ)
          (appended.tree i.castSucc.succ.castSucc)
          (appended.tree i.castSucc.succ.succ)
          (TashkinovStoredColors appended i.castSucc.castSucc)
          (appended.stored i.castSucc.succ)
          (appended.connectingEdges i.castSucc.succ)
          (appended.kind i.castSucc.succ)
          (appended.chosenVertex i.castSucc.succ)
          (appended.outsideVertex i.castSucc.succ)
          (appended.delta i.castSucc.succ) (appended.gamma i.castSucc.succ) := by
        rw [ruleEq, previousColoringEq, currentColoringEq, previousTreeEq,
          outputTreeEq, storedColorsEq, currentStoredEq, currentEdgesEq,
          currentKindEq, currentVertexEq, currentOutsideEq, currentDeltaEq,
          currentGammaEq]
        exact oldPackage
      rcases newPackage with ⟨newChoice, newSeriesAlternativeFails,
        newGammaValue, newGammaRule, newSecondStable, newSecondStableProper,
        newSecondStableOneUncolored, newSecondStableRelation, newExitWitness,
        newCurrentColoring, newCurrentProper, newCurrentOneUncolored,
        newCurrentStored, newCurrentEdges, newCurrentKind, newCurrentVertex,
        newCurrentOutside, newCurrentDelta, newCurrentGamma, newClosedExtension,
        newOrderedExtension, newStrictExtension⟩
      have newNoRevisiting : ¬ Nonempty
          (RevisitingExtensionCertificate appended i.castSucc.castSucc) := by
        rintro ⟨newCertificate⟩
        rcases (RevisitingExtensionCertificateAppend data newTree newColoring newStored
          newConnectingEdges newKind newChosenVertex newOutsideVertex
          newDelta newGamma i.castSucc).1 newCertificate with ⟨oldCertificate, -⟩
        exact noRevisiting ⟨oldCertificate⟩
      have lifted : TashkinovSeriesStep G k (rounds + 1) e0 input appended
          i.castSucc.succ := by
        apply TashkinovSeriesStep.PE (i := i.castSucc) (choice := newChoice)
          (gamma := newGammaValue) (secondStable := newSecondStable)
        · rw [previousColoringEq]
          exact previousProper
        · rw [previousColoringEq]
          exact previousOneUncolored
        · rw [previousColoringEq, previousTreeEq]
          exact previousClosed
        · rw [previousColoringEq, previousTreeEq]
          exact previousNotStronglyClosed
        · exact newNoRevisiting
        · exact newSeriesAlternativeFails
        · exact newGammaRule
        · exact newSecondStableProper
        · exact newSecondStableOneUncolored
        · exact newSecondStableRelation
        · exact newExitWitness
        · exact newCurrentColoring
        · exact newCurrentProper
        · exact newCurrentOneUncolored
        · exact newCurrentStored
        · exact newCurrentEdges
        · exact newCurrentKind
        · exact newCurrentVertex
        · exact newCurrentOutside
        · exact newCurrentDelta
        · exact newCurrentGamma
        · exact newClosedExtension
        · exact newOrderedExtension
        · exact newStrictExtension
      rw [← slotIndexEq]
      exact lifted

  | RE i previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed available currentColoring currentStored
      currentEdges currentKind currentVertex currentOutside currentDelta
      currentGamma adjoined adjoinedExactly closedExtension orderedExtension
      strictExtension =>
      have slotIndexEq : i.castSucc.succ = i.succ.castSucc := by ext; rfl
      have previousTreeIndexEq : i.castSucc.succ.castSucc =
          i.succ.castSucc.castSucc := by ext; rfl
      have outputTreeIndexEq : i.castSucc.succ.succ =
          i.succ.succ.castSucc := by ext; rfl
      have previousTreeEq : appended.tree i.castSucc.succ.castSucc =
          data.tree i.succ.castSucc := by
        calc
          appended.tree i.castSucc.succ.castSucc =
              appended.tree i.succ.castSucc.castSucc :=
            congrArg appended.tree previousTreeIndexEq
          _ = data.tree i.succ.castSucc := treeOld i.succ.castSucc
      have outputTreeEq : appended.tree i.castSucc.succ.succ =
          data.tree i.succ.succ := by
        calc
          appended.tree i.castSucc.succ.succ =
              appended.tree i.succ.succ.castSucc :=
            congrArg appended.tree outputTreeIndexEq
          _ = data.tree i.succ.succ := treeOld i.succ.succ
      have previousColoringEq : appended.coloring i.castSucc.castSucc =
          data.coloring i.castSucc := (slotsOld i.castSucc).1
      have currentColoringEq : appended.coloring i.castSucc.succ =
          data.coloring i.succ := by
        calc
          appended.coloring i.castSucc.succ =
              appended.coloring i.succ.castSucc :=
            congrArg appended.coloring slotIndexEq
          _ = data.coloring i.succ := (slotsOld i.succ).1
      have currentStoredEq : appended.stored i.castSucc.succ =
          data.stored i.succ := by
        calc
          appended.stored i.castSucc.succ = appended.stored i.succ.castSucc :=
            congrArg appended.stored slotIndexEq
          _ = data.stored i.succ := (slotsOld i.succ).2.1
      have currentEdgesEq : appended.connectingEdges i.castSucc.succ =
          data.connectingEdges i.succ := by
        calc
          appended.connectingEdges i.castSucc.succ =
              appended.connectingEdges i.succ.castSucc :=
            congrArg appended.connectingEdges slotIndexEq
          _ = data.connectingEdges i.succ := (slotsOld i.succ).2.2.1
      have currentKindEq : appended.kind i.castSucc.succ = data.kind i.succ := by
        calc
          appended.kind i.castSucc.succ = appended.kind i.succ.castSucc :=
            congrArg appended.kind slotIndexEq
          _ = data.kind i.succ := (slotsOld i.succ).2.2.2.1
      have currentVertexEq : appended.chosenVertex i.castSucc.succ =
          data.chosenVertex i.succ := by
        calc
          appended.chosenVertex i.castSucc.succ =
              appended.chosenVertex i.succ.castSucc :=
            congrArg appended.chosenVertex slotIndexEq
          _ = data.chosenVertex i.succ := (slotsOld i.succ).2.2.2.2.1
      have currentOutsideEq : appended.outsideVertex i.castSucc.succ =
          data.outsideVertex i.succ := by
        calc
          appended.outsideVertex i.castSucc.succ =
              appended.outsideVertex i.succ.castSucc :=
            congrArg appended.outsideVertex slotIndexEq
          _ = data.outsideVertex i.succ := (slotsOld i.succ).2.2.2.2.2.1
      have currentDeltaEq : appended.delta i.castSucc.succ = data.delta i.succ := by
        calc
          appended.delta i.castSucc.succ = appended.delta i.succ.castSucc :=
            congrArg appended.delta slotIndexEq
          _ = data.delta i.succ := (slotsOld i.succ).2.2.2.2.2.2.1
      have currentGammaEq : appended.gamma i.castSucc.succ = data.gamma i.succ := by
        calc
          appended.gamma i.castSucc.succ = appended.gamma i.succ.castSucc :=
            congrArg appended.gamma slotIndexEq
          _ = data.gamma i.succ := (slotsOld i.succ).2.2.2.2.2.2.2
      rcases (RevisitingExtensionCertificateAppend data newTree newColoring newStored
          newConnectingEdges newKind newChosenVertex newOutsideVertex
          newDelta newGamma i.castSucc).2 available with
        ⟨newAvailable, availableGamma, availableDelta, availableEdge,
          availableInside, availableOutside⟩
      have lifted : TashkinovSeriesStep G k (rounds + 1) e0 input appended
          i.castSucc.succ := by
        apply TashkinovSeriesStep.RE (i := i.castSucc)
          (available := newAvailable) (adjoined := adjoined)
        · rw [previousColoringEq]
          exact previousProper
        · rw [previousColoringEq]
          exact previousOneUncolored
        · rw [previousColoringEq, previousTreeEq]
          exact previousClosed
        · rw [previousColoringEq, previousTreeEq]
          exact previousNotStronglyClosed
        · rw [currentColoringEq, previousColoringEq]
          exact currentColoring
        · rw [currentStoredEq, availableDelta, availableGamma]
          exact currentStored
        · rw [currentEdgesEq, availableEdge]
          exact currentEdges
        · rw [currentKindEq]
          exact currentKind
        · rw [currentVertexEq, availableInside]
          exact currentVertex
        · rw [currentOutsideEq, availableOutside]
          exact currentOutside
        · rw [currentDeltaEq, availableDelta]
          exact currentDelta
        · rw [currentGammaEq, availableGamma]
          exact currentGamma
        · rw [previousTreeEq, availableEdge]
          exact adjoinedExactly
        · rw [currentColoringEq, outputTreeEq]
          exact closedExtension
        · rw [previousTreeEq, outputTreeEq]
          exact orderedExtension
        · rw [previousTreeEq, outputTreeEq]
          exact strictExtension
      rw [← slotIndexEq]
      exact lifted

