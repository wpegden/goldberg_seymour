import Tablet.CorrespondingExtendedTashkinovTree
import Tablet.HierarchyBase

-- [TABLET NODE: HierarchyBaseCorrespondingTransport]
lemma HierarchyBaseCorrespondingTransport
    {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : Nat) (e0 : E)
    (input : PartialEdgeColoring E k) (T U : TreeSequence G e0)
    (phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (corr : CorrespondingExtendedTashkinovTree G k e0 ett phi U)
    (base : HierarchyBase ett phi) :
    exists replacementBase : HierarchyBase corr.replacementETT phi,
      replacementBase.core = base.core /\
        replacementBase.closure = base.closure /\
        replacementBase.supportPosition.val = base.supportPosition.val := by
-- BODY
  classical
  rcases corr with ⟨replacementInput, replacementSeries, replacementETT,
    rungAgreement, seriesPresentation, finalGeneratingColoring,
    ladderTreesAgree, storedColorsAgree, connectingEdgesAgree,
    extensionKindsAgree, replacementProper, replacementOneUncolored,
    replacementStable⟩
  cases replacementETT with
  | mk rounds roundsPositive replacementData above strict below generating =>
    cases rungAgreement
    have seriesSame : replacementData = replacementSeries :=
      eq_of_heq seriesPresentation
    cases seriesSame
    let q : Fin ett.rounds :=
      ⟨ett.rounds - 1,
        Nat.sub_lt (Nat.zero_lt_of_lt ett.roundsPositive) (by omega)⟩
    have hq : q.succ = Fin.last ett.rounds := by
      apply Fin.ext
      exact Nat.sub_add_cancel ett.roundsPositive
    have hfinal : replacementSeries.data.tree
          (Fin.last ett.rounds).castSucc =
        ett.series.data.tree (Fin.last ett.rounds).castSucc := by
      rw [← hq]
      exact ladderTreesAgree q
    have hkindEq : replacementSeries.data.kind (Fin.last ett.rounds) =
        ett.series.data.kind (Fin.last ett.rounds) :=
      extensionKindsAgree (Fin.last ett.rounds)
    have insideUnique : ∀ (u v x y : V) (e : E),
        u ∈ TreeSequenceVertexSet
            (replacementSeries.data.tree (Fin.last ett.rounds).castSucc) →
        v ∈ TreeSequenceVertexSet
            (ett.series.data.tree (Fin.last ett.rounds).castSucc) →
        x ∉ TreeSequenceVertexSet
            (replacementSeries.data.tree (Fin.last ett.rounds).castSucc) →
        y ∉ TreeSequenceVertexSet
            (ett.series.data.tree (Fin.last ett.rounds).castSucc) →
        G.ends e = s(u, x) → G.ends e = s(v, y) → u = v := by
      intro u v x y e hu hv hx hy he₁ he₂
      rcases (Sym2.eq_iff.mp (he₁.symm.trans he₂)) with h | h
      · exact h.1
      · have hv' := hv
        rw [← hfinal] at hv'
        exact False.elim (hx (h.2 ▸ hv'))
    have chosenAgree :
        ett.series.data.kind (Fin.last ett.rounds) =
            some TashkinovExtensionKind.PE →
          replacementSeries.data.chosenVertex (Fin.last ett.rounds) =
            ett.series.data.chosenVertex (Fin.last ett.rounds) := by
      intro hPE
      have hkind : replacementSeries.data.kind (Fin.last ett.rounds) =
          some TashkinovExtensionKind.PE := hkindEq.trans hPE
      have oldStep := ett.series.certified (Fin.last ett.rounds)
      have newStep := replacementSeries.certified (Fin.last ett.rounds)
      generalize oldIndex : Fin.last ett.rounds = oldTarget at oldStep
      generalize newIndex : Fin.last ett.rounds = newTarget at newStep
      cases oldStep with
        | initial triple seedLength initialColoring initialStored initialEdges
            initialKind initialVertex initialOutside initialDelta initialGamma
            initialClosure =>
          rw [oldIndex] at hPE
          rw [initialKind] at hPE
          cases hPE
        | SE oi previousProper previousOneUncolored previousClosed
            previousNotStronglyClosed noRevisiting choice seriesAlternative
            currentColoring currentStored currentEdges currentKind currentVertex
            currentOutside currentDelta currentGamma adjoined adjoinedExactly
            closedExtension orderedExtension strictExtension =>
          rw [oldIndex] at hPE
          rw [currentKind] at hPE
          cases hPE
        | RE oi previousProper previousOneUncolored previousClosed
            previousNotStronglyClosed available currentColoring currentStored
            currentEdges currentKind currentVertex currentOutside currentDelta
            currentGamma adjoined adjoinedExactly closedExtension orderedExtension
            strictExtension =>
          rw [oldIndex] at hPE
          rw [currentKind] at hPE
          cases hPE
        | PE oi previousProper previousOneUncolored previousClosed
            previousNotStronglyClosed noRevisiting oldChoice seriesAlternativeFails
            oldGamma gammaRule secondStable secondStableProper
            secondStableOneUncolored secondStableRelation exitWitness oldColoring
            oldProper oldOneUncolored oldStored oldEdges oldKind oldVertex
            oldOutside oldDelta oldGamma2 closedExtension orderedExtension
            strictExtension =>
          have hio : oi = q := by
            apply Fin.ext
            have hv := congrArg Fin.val oldIndex
            simp [q] at hv ⊢
            omega
          subst oi
          cases newStep with
          | initial triple seedLength initialColoring initialStored initialEdges
              initialKind initialVertex initialOutside initialDelta initialGamma
              initialClosure =>
            rw [newIndex] at hkind
            rw [initialKind] at hkind
            cases hkind
          | SE ni previousProper previousOneUncolored previousClosed
              previousNotStronglyClosed noRevisiting choice seriesAlternative
              currentColoring currentStored currentEdges currentKind currentVertex
              currentOutside currentDelta currentGamma adjoined adjoinedExactly
              closedExtension orderedExtension strictExtension =>
            rw [newIndex] at hkind
            rw [currentKind] at hkind
            cases hkind
          | RE ni previousProper previousOneUncolored previousClosed
              previousNotStronglyClosed available currentColoring currentStored
              currentEdges currentKind currentVertex currentOutside currentDelta
              currentGamma adjoined adjoinedExactly closedExtension orderedExtension
              strictExtension =>
            rw [newIndex] at hkind
            rw [currentKind] at hkind
            cases hkind
          | PE ni previousProper previousOneUncolored previousClosed
              previousNotStronglyClosed noRevisiting newChoice seriesAlternativeFails
              newGamma gammaRule secondStable secondStableProper
              secondStableOneUncolored secondStableRelation exitWitness newColoring
              newProper newOneUncolored newStored newEdges newKind newVertex
              newOutside newDelta newGamma2 closedExtension orderedExtension
              strictExtension =>
            have hin : ni = q := by
              apply Fin.ext
              have hv := congrArg Fin.val newIndex
              simp [q] at hv ⊢
              omega
            subst ni
            have hedge : newChoice.edge = oldChoice.edge := by
              have he := connectingEdgesAgree (Fin.last ett.rounds)
              rw [← hq] at he
              rw [newEdges, oldEdges] at he
              simpa using he
            have hnew : newChoice.vertex ∈ TreeSequenceVertexSet
                (replacementSeries.data.tree
                  (Fin.last ett.rounds).castSucc) := by
              simpa [hq] using newChoice.vertexDefective.1
            have hold : oldChoice.vertex ∈ TreeSequenceVertexSet
                (ett.series.data.tree (Fin.last ett.rounds).castSucc) := by
              simpa [hq] using oldChoice.vertexDefective.1
            have hnewOutside : newChoice.otherEndpoint ∉ TreeSequenceVertexSet
                (replacementSeries.data.tree
                  (Fin.last ett.rounds).castSucc) := by
              simpa [hq] using newChoice.otherOutside
            have holdOutside : oldChoice.otherEndpoint ∉ TreeSequenceVertexSet
                (ett.series.data.tree (Fin.last ett.rounds).castSucc) := by
              simpa [hq] using oldChoice.otherOutside
            have hv := insideUnique newChoice.vertex oldChoice.vertex
              newChoice.otherEndpoint oldChoice.otherEndpoint newChoice.edge
              hnew hold hnewOutside holdOutside newChoice.edgeEnds
              (hedge ▸ oldChoice.edgeEnds)
            have hvertices :=
              newVertex.trans ((congrArg some hv).trans oldVertex.symm)
            simpa [hq] using hvertices
    have transportVertex : ∀ (A B : TreeSequence G e0), ∀ (h : A = B),
        ∀ i : Fin (B.length + 1),
        A.vertex (Fin.cast (congrArg
          (fun W : TreeSequence G e0 => W.length + 1) h.symm) i) =
          B.vertex i := by
      intro A B h i
      cases h
      rfl
    let pos : Fin ((replacementSeries.data.tree
        (Fin.last ett.rounds).castSucc).length + 1) :=
      Fin.cast (congrArg (fun W : TreeSequence G e0 => W.length + 1)
        hfinal.symm) base.supportPosition
    let replacementBase : HierarchyBase
        { rounds := ett.rounds
          roundsPositive := roundsPositive
          series := replacementSeries
          abovePenultimate := above
          strictAbovePenultimate := strict
          belowFinal := below
          generatingColoring := generating } phi :=
      { core := base.core
        closure := base.closure
        supportPosition := pos
        supportPositive := by simpa [pos] using base.supportPositive
        terminalMissingColors := by rfl
        parallel := by
          dsimp
          intro hp
          have hp' : ett.series.data.kind (Fin.last ett.rounds) =
              some TashkinovExtensionKind.PE := hkindEq.symm.trans hp
          have hb := base.parallel hp'
          refine ⟨?_, ?_, ?_⟩
          · have hvertex :
                (replacementSeries.data.tree
                    (Fin.last ett.rounds).castSucc).vertex pos =
                  (ett.series.data.tree
                    (Fin.last ett.rounds).castSucc).vertex
                    base.supportPosition := by
              exact transportVertex _ _ hfinal base.supportPosition
            rw [chosenAgree hp']
            rw [hvertex]
            exact hb.1
          · simpa [pos, hfinal] using hb.2.1
          · simpa [hfinal] using hb.2.2
        nonparallel := by
          dsimp
          intro hp
          have hp' : ett.series.data.kind (Fin.last ett.rounds) ≠
              some TashkinovExtensionKind.PE := by
            intro h
            exact hp (hkindEq.trans h)
          exact (base.nonparallel hp').trans hfinal.symm }
    exact ⟨replacementBase, rfl, rfl, by simp [replacementBase, pos]⟩
