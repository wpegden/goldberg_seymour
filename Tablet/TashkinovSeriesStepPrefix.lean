import Tablet.TashkinovSeriesDataPrefix
import Tablet.TashkinovSeriesStep
import Tablet.TashkinovStoredColorsPrefix

-- [TABLET NODE: TashkinovSeriesStepPrefix]
theorem TashkinovSeriesStepPrefix {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq E] {G : LooplessMultigraph V E} {k rounds : ℕ} {e0 : E}
    (input : PartialEdgeColoring E k)
    (data : TashkinovSeriesData G k rounds e0)
    (m : ℕ) (hm : m ≤ rounds) (i : Fin (m + 1))
    (cert : TashkinovSeriesStep G k rounds e0 input data
      (Fin.castLE (by omega) i)) :
    ∃ prefixCert : TashkinovSeriesStep G k m e0 input
        (TashkinovSeriesDataPrefix m hm data) i,
      HEq prefixCert cert := by
-- BODY
  have aux : ∀ (j : Fin (rounds + 1)) (hj : j.val ≤ m)
      (oldCert : TashkinovSeriesStep G k rounds e0 input data j),
      ∃ prefixCert : TashkinovSeriesStep G k m e0 input
          (TashkinovSeriesDataPrefix m hm data) ⟨j.val, by omega⟩,
        HEq prefixCert oldCert := by
    intro j hj oldCert
    cases oldCert with
    | initial triple seedLength initialColoring initialStored initialEdges
        initialKind initialVertex initialOutside initialDelta initialGamma
        initialClosure =>
      refine ⟨TashkinovSeriesStep.initial triple ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_,
        proof_irrel_heq _ _⟩
      · simpa [TashkinovSeriesDataPrefix] using seedLength
      · simpa [TashkinovSeriesDataPrefix] using initialColoring
      · simpa [TashkinovSeriesDataPrefix] using initialStored
      · simpa [TashkinovSeriesDataPrefix] using initialEdges
      · simpa [TashkinovSeriesDataPrefix] using initialKind
      · simpa [TashkinovSeriesDataPrefix] using initialVertex
      · simpa [TashkinovSeriesDataPrefix] using initialOutside
      · simpa [TashkinovSeriesDataPrefix] using initialDelta
      · simpa [TashkinovSeriesDataPrefix] using initialGamma
      · simpa only [TashkinovSeriesDataPrefix, Fin.castLE_zero]
    | SE idx previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed noRevisiting choice seriesAlternative
        currentColoring currentStored currentEdges currentKind currentVertex
        currentOutside currentDelta currentGamma adjoined adjoinedExactly
        closedExtension orderedExtension strictExtension =>
      have hidxSucc : idx.val + 1 ≤ m := by simpa using hj
      have hidx : idx.val < m := by omega
      let idx' : Fin m := ⟨idx.val, hidx⟩
      have hprev : (TashkinovSeriesDataPrefix m hm data).coloring idx'.castSucc =
          data.coloring idx.castSucc := by rfl
      have htree : (TashkinovSeriesDataPrefix m hm data).tree
          idx'.succ.castSucc = data.tree idx.succ.castSucc := by rfl
      have htreeCurrent : (TashkinovSeriesDataPrefix m hm data).tree
          idx'.castSucc.succ = data.tree idx.castSucc.succ := by rfl
      have hcur : (TashkinovSeriesDataPrefix m hm data).coloring idx'.succ =
          data.coloring idx.succ := by rfl
      have hcurStored : (TashkinovSeriesDataPrefix m hm data).stored idx'.succ =
          data.stored idx.succ := by rfl
      have hcurEdges : (TashkinovSeriesDataPrefix m hm data).connectingEdges
          idx'.succ = data.connectingEdges idx.succ := by rfl
      have hcurKind : (TashkinovSeriesDataPrefix m hm data).kind idx'.succ =
          data.kind idx.succ := by rfl
      have hcurVertex : (TashkinovSeriesDataPrefix m hm data).chosenVertex
          idx'.succ = data.chosenVertex idx.succ := by rfl
      have hcurOutside : (TashkinovSeriesDataPrefix m hm data).outsideVertex
          idx'.succ = data.outsideVertex idx.succ := by rfl
      have hcurDelta : (TashkinovSeriesDataPrefix m hm data).delta idx'.succ =
          data.delta idx.succ := by rfl
      have hcurGamma : (TashkinovSeriesDataPrefix m hm data).gamma idx'.succ =
          data.gamma idx.succ := by rfl
      have hnext : (TashkinovSeriesDataPrefix m hm data).tree idx'.succ.succ =
          data.tree idx.succ.succ := by rfl
      have hstored : TashkinovStoredColors
          (TashkinovSeriesDataPrefix m hm data) idx'.castSucc =
          TashkinovStoredColors data idx.castSucc := by
        exact TashkinovStoredColorsPrefix m hm data idx'.castSucc
      let choice' : MaximumDefectiveChoice G e0
          ((TashkinovSeriesDataPrefix m hm data).tree idx'.succ.castSucc)
          (TashkinovStoredColors (TashkinovSeriesDataPrefix m hm data)
            idx'.castSucc)
          ((TashkinovSeriesDataPrefix m hm data).coloring idx'.castSucc) := {
        selected := choice.selected
        selectedProper := choice.selectedProper
        selectedOneUncolored := choice.selectedOneUncolored
        selectedStable := by
          rw [htree, hstored, hprev]
          exact choice.selectedStable
        vertex := choice.vertex
        vertexDefective := by
          rw [htree]
          exact choice.vertexDefective
        maximal := by
          rw [htree, hstored, hprev]
          exact choice.maximal
        edge := choice.edge
        edgeDefective := by
          rw [htree]
          exact choice.edgeDefective
        edgeIncident := choice.edgeIncident
        otherEndpoint := choice.otherEndpoint
        otherOutside := by
          rw [htree]
          exact choice.otherOutside
        edgeEnds := choice.edgeEnds
        color := choice.color
        edgeColor := choice.edgeColor
      }
      have noRevisiting' : ¬ Nonempty (RevisitingExtensionCertificate
          (TashkinovSeriesDataPrefix m hm data) idx'.castSucc) := by
        rintro ⟨r⟩
        apply noRevisiting
        let earlier' : Fin (rounds + 1) := Fin.castLE (by omega) r.earlier
        have hkindEarlier : (TashkinovSeriesDataPrefix m hm data).kind
            r.earlier = data.kind earlier' := by rfl
        have hgammaEarlier : (TashkinovSeriesDataPrefix m hm data).gamma
            r.earlier = data.gamma earlier' := by rfl
        have hdeltaEarlier : (TashkinovSeriesDataPrefix m hm data).delta
            r.earlier = data.delta earlier' := by rfl
        have htreeEarlier : (TashkinovSeriesDataPrefix m hm data).tree
            r.earlier.castSucc = data.tree earlier'.castSucc := by rfl
        let cycle' : TwoColorCycle G (data.coloring idx.castSucc)
            r.gamma r.delta := {
          base := r.cycle.base
          walk := @Eq.ndrec (PartialEdgeColoring E k)
            ((TashkinovSeriesDataPrefix m hm data).coloring idx'.castSucc)
            (fun phi => (TwoColorIncidenceGraph G phi r.gamma r.delta).Walk
              r.cycle.base r.cycle.base)
            r.cycle.walk (data.coloring idx.castSucc) hprev
          isCycle := by
            dsimp
            cases hprev
            exact r.cycle.isCycle
        }
        let returnPath' : (TwoColorIncidenceGraph G (data.coloring idx.castSucc)
            r.gamma r.delta).Walk (Sum.inr r.edge) (Sum.inl r.returnVertex) :=
          @Eq.ndrec (PartialEdgeColoring E k)
            ((TashkinovSeriesDataPrefix m hm data).coloring idx'.castSucc)
            (fun phi => (TwoColorIncidenceGraph G phi r.gamma r.delta).Walk
              (Sum.inr r.edge) (Sum.inl r.returnVertex))
            r.returnPath (data.coloring idx.castSucc) hprev
        refine ⟨{
          earlier := earlier'
          earlierPositive := by simpa [earlier'] using r.earlierPositive
          earlierAtMost := by simpa [earlier', idx'] using r.earlierAtMost
          earlierPE := by
            simpa [hkindEarlier] using r.earlierPE
          interveningRevisiting := ?_
          gamma := r.gamma
          delta := r.delta
          earlierGamma := by
            simpa [hgammaEarlier] using r.earlierGamma
          earlierDelta := by
            simpa [hdeltaEarlier] using r.earlierDelta
          cycle := cycle'
          meetsEarlier := by
            rcases r.meetsEarlier with ⟨v, hv, hc⟩
            refine ⟨v, ?_, ?_⟩
            · rwa [htreeEarlier] at hv
            · dsimp [cycle']
              cases hprev
              exact hc
          leavesCurrent := by
            rcases r.leavesCurrent with ⟨v, hv, hc⟩
            refine ⟨v, ?_, ?_⟩
            · rwa [htreeCurrent] at hv
            · dsimp [cycle']
              cases hprev
              exact hc
          edge := r.edge
          edgeOnCycle := by
            dsimp [cycle']
            cases hprev
            exact r.edgeOnCycle
          edgeBoundary := by
            simpa only [htreeCurrent] using r.edgeBoundary
          insideEndpoint := r.insideEndpoint
          outsideEndpoint := r.outsideEndpoint
          insideInCurrent := by
            simpa only [htreeCurrent] using r.insideInCurrent
          outsideNotCurrent := by
            simpa only [htreeCurrent] using r.outsideNotCurrent
          edgeEnds := r.edgeEnds
          returnVertex := r.returnVertex
          returnInEarlier := by
            simpa [htreeEarlier] using r.returnInEarlier
          returnPath := returnPath'
          returnPathIsPath := by
            dsimp [returnPath']
            cases hprev
            exact r.returnPathIsPath
          returnPathOnCycle := by
            dsimp [returnPath', cycle']
            cases hprev
            exact r.returnPathOnCycle
          returnPathInternal := by
            intro v hv
            have hv' : Sum.inl v ∈ r.returnPath.support := by
              dsimp [returnPath'] at hv
              cases hprev
              exact hv
            simpa only [htreeCurrent] using r.returnPathInternal v hv'
        }⟩
        intro j hjpos hjafter hjatMost
        have hjle : j.val ≤ idx.val := by
          simpa [idx'] using hjatMost
        have hjm : j.val < m + 1 := by omega
        let j' : Fin (m + 1) := ⟨j.val, hjm⟩
        have hstep := r.interveningRevisiting j' (by simpa [j'] using hjpos)
          (by simpa [j', earlier'] using hjafter)
          (by simpa [j', idx'] using hjatMost)
        have hkindJ : (TashkinovSeriesDataPrefix m hm data).kind j' =
            data.kind j := by rfl
        simpa [hkindJ] using hstep
      have prefixCert : TashkinovSeriesStep G k m e0 input
          (TashkinovSeriesDataPrefix m hm data) idx'.succ := by
        apply TashkinovSeriesStep.SE (i := idx') (choice := choice')
          (adjoined := adjoined)
        · rw [hprev]
          exact previousProper
        · rw [hprev]
          exact previousOneUncolored
        · rw [hprev, htree]
          exact previousClosed
        · rw [hprev, htree]
          exact previousNotStronglyClosed
        · exact noRevisiting'
        · intro pi hp ho hs
          apply seriesAlternative pi hp ho
          change StableColoring
            ((TashkinovSeriesDataPrefix m hm data).tree idx'.succ.castSucc)
            (insert choice.color (TashkinovStoredColors
              (TashkinovSeriesDataPrefix m hm data) idx'.castSucc))
            choice.selected pi at hs
          rw [htree, hstored] at hs
          exact hs
        · change (TashkinovSeriesDataPrefix m hm data).coloring idx'.succ =
            choice.selected
          rw [hcur]
          exact currentColoring
        · change (TashkinovSeriesDataPrefix m hm data).stored idx'.succ =
            {choice.color}
          rw [hcurStored]
          exact currentStored
        · change (TashkinovSeriesDataPrefix m hm data).connectingEdges
            idx'.succ = {choice.edge}
          rw [hcurEdges]
          exact currentEdges
        · rw [hcurKind]
          exact currentKind
        · change (TashkinovSeriesDataPrefix m hm data).chosenVertex
            idx'.succ = some choice.vertex
          rw [hcurVertex]
          exact currentVertex
        · change (TashkinovSeriesDataPrefix m hm data).outsideVertex
            idx'.succ = some choice.otherEndpoint
          rw [hcurOutside]
          exact currentOutside
        · change (TashkinovSeriesDataPrefix m hm data).delta idx'.succ =
            some choice.color
          rw [hcurDelta]
          exact currentDelta
        · rw [hcurGamma]
          exact currentGamma
        · change TreeSequenceAdjoinEdge
            ((TashkinovSeriesDataPrefix m hm data).tree idx'.succ.castSucc)
            choice.edge adjoined
          rw [htree]
          exact adjoinedExactly
        · rw [hcur, hnext]
          exact closedExtension
        · rw [htree, hnext]
          exact orderedExtension
        · rw [htree, hnext]
          exact strictExtension
      have hresult : idx'.succ =
          (⟨idx.succ.val, by omega⟩ : Fin (m + 1)) := by
        apply Fin.ext
        rfl
      rw [← hresult]
      exact ⟨prefixCert, proof_irrel_heq _ _⟩
    | PE idx previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed noRevisiting choice seriesAlternativeFails
        gamma gammaRule secondStable secondStableProper
        secondStableOneUncolored secondStableRelation exitWitness
        currentColoring currentProper currentOneUncolored currentStored
        currentEdges currentKind currentVertex currentOutside currentDelta
        currentGamma closedExtension orderedExtension strictExtension =>
      have hidxSucc : idx.val + 1 ≤ m := by simpa using hj
      have hidx : idx.val < m := by omega
      let idx' : Fin m := ⟨idx.val, hidx⟩
      have hprev : (TashkinovSeriesDataPrefix m hm data).coloring idx'.castSucc =
          data.coloring idx.castSucc := by rfl
      have htree : (TashkinovSeriesDataPrefix m hm data).tree
          idx'.succ.castSucc = data.tree idx.succ.castSucc := by rfl
      have htreeCurrent : (TashkinovSeriesDataPrefix m hm data).tree
          idx'.castSucc.succ = data.tree idx.castSucc.succ := by rfl
      have hcur : (TashkinovSeriesDataPrefix m hm data).coloring idx'.succ =
          data.coloring idx.succ := by rfl
      have hcurStored : (TashkinovSeriesDataPrefix m hm data).stored idx'.succ =
          data.stored idx.succ := by rfl
      have hcurEdges : (TashkinovSeriesDataPrefix m hm data).connectingEdges
          idx'.succ = data.connectingEdges idx.succ := by rfl
      have hcurKind : (TashkinovSeriesDataPrefix m hm data).kind idx'.succ =
          data.kind idx.succ := by rfl
      have hcurVertex : (TashkinovSeriesDataPrefix m hm data).chosenVertex
          idx'.succ = data.chosenVertex idx.succ := by rfl
      have hcurOutside : (TashkinovSeriesDataPrefix m hm data).outsideVertex
          idx'.succ = data.outsideVertex idx.succ := by rfl
      have hcurDelta : (TashkinovSeriesDataPrefix m hm data).delta idx'.succ =
          data.delta idx.succ := by rfl
      have hcurGamma : (TashkinovSeriesDataPrefix m hm data).gamma idx'.succ =
          data.gamma idx.succ := by rfl
      have hnext : (TashkinovSeriesDataPrefix m hm data).tree idx'.succ.succ =
          data.tree idx.succ.succ := by rfl
      have hstored : TashkinovStoredColors
          (TashkinovSeriesDataPrefix m hm data) idx'.castSucc =
          TashkinovStoredColors data idx.castSucc := by
        exact TashkinovStoredColorsPrefix m hm data idx'.castSucc
      let choice' : MaximumDefectiveChoice G e0
          ((TashkinovSeriesDataPrefix m hm data).tree idx'.succ.castSucc)
          (TashkinovStoredColors (TashkinovSeriesDataPrefix m hm data)
            idx'.castSucc)
          ((TashkinovSeriesDataPrefix m hm data).coloring idx'.castSucc) := {
        selected := choice.selected
        selectedProper := choice.selectedProper
        selectedOneUncolored := choice.selectedOneUncolored
        selectedStable := by
          rw [htree, hstored, hprev]
          exact choice.selectedStable
        vertex := choice.vertex
        vertexDefective := by
          rw [htree]
          exact choice.vertexDefective
        maximal := by
          rw [htree, hstored, hprev]
          exact choice.maximal
        edge := choice.edge
        edgeDefective := by
          rw [htree]
          exact choice.edgeDefective
        edgeIncident := choice.edgeIncident
        otherEndpoint := choice.otherEndpoint
        otherOutside := by
          rw [htree]
          exact choice.otherOutside
        edgeEnds := choice.edgeEnds
        color := choice.color
        edgeColor := choice.edgeColor
      }
      have noRevisiting' : ¬ Nonempty (RevisitingExtensionCertificate
          (TashkinovSeriesDataPrefix m hm data) idx'.castSucc) := by
        rintro ⟨r⟩
        apply noRevisiting
        let earlier' : Fin (rounds + 1) := Fin.castLE (by omega) r.earlier
        have hkindEarlier : (TashkinovSeriesDataPrefix m hm data).kind
            r.earlier = data.kind earlier' := by rfl
        have hgammaEarlier : (TashkinovSeriesDataPrefix m hm data).gamma
            r.earlier = data.gamma earlier' := by rfl
        have hdeltaEarlier : (TashkinovSeriesDataPrefix m hm data).delta
            r.earlier = data.delta earlier' := by rfl
        have htreeEarlier : (TashkinovSeriesDataPrefix m hm data).tree
            r.earlier.castSucc = data.tree earlier'.castSucc := by rfl
        let cycle' : TwoColorCycle G (data.coloring idx.castSucc)
            r.gamma r.delta := {
          base := r.cycle.base
          walk := @Eq.ndrec (PartialEdgeColoring E k)
            ((TashkinovSeriesDataPrefix m hm data).coloring idx'.castSucc)
            (fun phi => (TwoColorIncidenceGraph G phi r.gamma r.delta).Walk
              r.cycle.base r.cycle.base)
            r.cycle.walk (data.coloring idx.castSucc) hprev
          isCycle := by
            dsimp
            cases hprev
            exact r.cycle.isCycle
        }
        let returnPath' : (TwoColorIncidenceGraph G (data.coloring idx.castSucc)
            r.gamma r.delta).Walk (Sum.inr r.edge) (Sum.inl r.returnVertex) :=
          @Eq.ndrec (PartialEdgeColoring E k)
            ((TashkinovSeriesDataPrefix m hm data).coloring idx'.castSucc)
            (fun phi => (TwoColorIncidenceGraph G phi r.gamma r.delta).Walk
              (Sum.inr r.edge) (Sum.inl r.returnVertex))
            r.returnPath (data.coloring idx.castSucc) hprev
        refine ⟨{
          earlier := earlier'
          earlierPositive := by simpa [earlier'] using r.earlierPositive
          earlierAtMost := by simpa [earlier', idx'] using r.earlierAtMost
          earlierPE := by simpa [hkindEarlier] using r.earlierPE
          interveningRevisiting := ?_
          gamma := r.gamma
          delta := r.delta
          earlierGamma := by simpa [hgammaEarlier] using r.earlierGamma
          earlierDelta := by simpa [hdeltaEarlier] using r.earlierDelta
          cycle := cycle'
          meetsEarlier := by
            rcases r.meetsEarlier with ⟨v, hv, hc⟩
            refine ⟨v, ?_, ?_⟩
            · rwa [htreeEarlier] at hv
            · dsimp [cycle']
              cases hprev
              exact hc
          leavesCurrent := by
            rcases r.leavesCurrent with ⟨v, hv, hc⟩
            refine ⟨v, ?_, ?_⟩
            · rwa [htreeCurrent] at hv
            · dsimp [cycle']
              cases hprev
              exact hc
          edge := r.edge
          edgeOnCycle := by
            dsimp [cycle']
            cases hprev
            exact r.edgeOnCycle
          edgeBoundary := by
            simpa only [htreeCurrent] using r.edgeBoundary
          insideEndpoint := r.insideEndpoint
          outsideEndpoint := r.outsideEndpoint
          insideInCurrent := by
            simpa only [htreeCurrent] using r.insideInCurrent
          outsideNotCurrent := by
            simpa only [htreeCurrent] using r.outsideNotCurrent
          edgeEnds := r.edgeEnds
          returnVertex := r.returnVertex
          returnInEarlier := by
            simpa [htreeEarlier] using r.returnInEarlier
          returnPath := returnPath'
          returnPathIsPath := by
            dsimp [returnPath']
            cases hprev
            exact r.returnPathIsPath
          returnPathOnCycle := by
            dsimp [returnPath', cycle']
            cases hprev
            exact r.returnPathOnCycle
          returnPathInternal := by
            intro v hv
            have hv' : Sum.inl v ∈ r.returnPath.support := by
              dsimp [returnPath'] at hv
              cases hprev
              exact hv
            simpa only [htreeCurrent] using r.returnPathInternal v hv'
        }⟩
        intro j hjpos hjafter hjatMost
        have hjle : j.val ≤ idx.val := by simpa [idx'] using hjatMost
        have hjm : j.val < m + 1 := by omega
        let j' : Fin (m + 1) := ⟨j.val, hjm⟩
        have hstep := r.interveningRevisiting j' (by simpa [j'] using hjpos)
          (by simpa [j', earlier'] using hjafter)
          (by simpa [j', idx'] using hjatMost)
        have hkindJ : (TashkinovSeriesDataPrefix m hm data).kind j' =
            data.kind j := by rfl
        simpa [hkindJ] using hstep
      have gammaRule' : ParallelExtensionColor
          (TashkinovSeriesDataPrefix m hm data) idx'.castSucc
          choice'.selected choice'.vertex gamma := by
        change ParallelExtensionColor (TashkinovSeriesDataPrefix m hm data)
          idx'.castSucc choice.selected choice.vertex gamma
        unfold ParallelExtensionColor at gammaRule ⊢
        refine ⟨gammaRule.1, ?_⟩
        rcases gammaRule.2 with existing | fresh
        · left
          rcases existing with
            ⟨h, hpos, hatMost, hkind, hvertex, hdelta, hlatest⟩
          have hle : h.val ≤ idx.val := by simpa using hatMost
          have hhm : h.val < m + 1 := by omega
          let h' : Fin (m + 1) := ⟨h.val, hhm⟩
          refine ⟨h', by simpa [h'] using hpos, by simpa [h', idx'] using hatMost,
            ?_, ?_, ?_, ?_⟩
          · simpa [h', TashkinovSeriesDataPrefix] using hkind
          · simpa [h', TashkinovSeriesDataPrefix] using hvertex
          · simpa [h', TashkinovSeriesDataPrefix] using hdelta
          · intro j jpos jatMost jkind jvertex
            let j' : Fin (rounds + 1) := Fin.castLE (by omega) j
            have latest := hlatest j' (by simpa [j'] using jpos)
              (by simpa [j', idx'] using jatMost)
              (by simpa [j', TashkinovSeriesDataPrefix] using jkind)
              (by simpa [j', TashkinovSeriesDataPrefix] using jvertex)
            simpa [j', h'] using latest
        · right
          intro h hpos hatMost hkind hvertex
          let h' : Fin (rounds + 1) := Fin.castLE (by omega) h
          apply fresh h' (by simpa [h'] using hpos)
            (by simpa [h', idx'] using hatMost)
          · simpa [h', TashkinovSeriesDataPrefix] using hkind
          · simpa [h', TashkinovSeriesDataPrefix] using hvertex
      have prefixCert : TashkinovSeriesStep G k m e0 input
          (TashkinovSeriesDataPrefix m hm data) idx'.succ := by
        apply TashkinovSeriesStep.PE (i := idx') (choice := choice')
          (gamma := gamma) (secondStable := secondStable)
        · rw [hprev]
          exact previousProper
        · rw [hprev]
          exact previousOneUncolored
        · rw [hprev, htree]
          exact previousClosed
        · rw [hprev, htree]
          exact previousNotStronglyClosed
        · exact noRevisiting'
        · rcases seriesAlternativeFails with ⟨rho, hp, ho, hs, hd⟩
          refine ⟨rho, hp, ho, ?_, ?_⟩
          · change StableColoring
              ((TashkinovSeriesDataPrefix m hm data).tree idx'.succ.castSucc)
              (insert choice.color (TashkinovStoredColors
                (TashkinovSeriesDataPrefix m hm data) idx'.castSucc))
              choice.selected rho
            rw [htree, hstored]
            exact hs
          · change ¬ Disjoint (MissingColors G rho choice.otherEndpoint)
              (TreeMissingColors rho
                ((TashkinovSeriesDataPrefix m hm data).tree idx'.succ.castSucc))
            rw [htree]
            exact hd
        · exact gammaRule'
        · exact secondStableProper
        · exact secondStableOneUncolored
        · change StableColoring
            ((TashkinovSeriesDataPrefix m hm data).tree idx'.succ.castSucc)
            (insert choice.color (TashkinovStoredColors
              (TashkinovSeriesDataPrefix m hm data) idx'.castSucc))
            choice.selected secondStable
          rw [htree, hstored]
          exact secondStableRelation
        · change TreeExit
            ((TashkinovSeriesDataPrefix m hm data).tree idx'.succ.castSucc)
            secondStable gamma choice.color choice.vertex
          rw [htree]
          exact exitWitness
        · change (TashkinovSeriesDataPrefix m hm data).coloring idx'.succ =
            TwoColorComponentSwap G secondStable gamma choice.color
              (Sum.inl choice.vertex)
          rw [hcur]
          exact currentColoring
        · rw [hcur]
          exact currentProper
        · rw [hcur]
          exact currentOneUncolored
        · change (TashkinovSeriesDataPrefix m hm data).stored idx'.succ =
            {choice.color, gamma}
          rw [hcurStored]
          exact currentStored
        · change (TashkinovSeriesDataPrefix m hm data).connectingEdges
            idx'.succ = {choice.edge}
          rw [hcurEdges]
          exact currentEdges
        · rw [hcurKind]
          exact currentKind
        · change (TashkinovSeriesDataPrefix m hm data).chosenVertex
            idx'.succ = some choice.vertex
          rw [hcurVertex]
          exact currentVertex
        · change (TashkinovSeriesDataPrefix m hm data).outsideVertex
            idx'.succ = some choice.otherEndpoint
          rw [hcurOutside]
          exact currentOutside
        · change (TashkinovSeriesDataPrefix m hm data).delta idx'.succ =
            some choice.color
          rw [hcurDelta]
          exact currentDelta
        · rw [hcurGamma]
          exact currentGamma
        · rw [hcur, htree, hnext]
          exact closedExtension
        · rw [htree, hnext]
          exact orderedExtension
        · rw [htree, hnext]
          exact strictExtension
      have hresult : idx'.succ =
          (⟨idx.succ.val, by omega⟩ : Fin (m + 1)) := by
        apply Fin.ext
        rfl
      rw [← hresult]
      exact ⟨prefixCert, proof_irrel_heq _ _⟩
    | RE idx previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed available currentColoring currentStored
        currentEdges currentKind currentVertex currentOutside currentDelta
        currentGamma adjoined adjoinedExactly closedExtension orderedExtension
        strictExtension =>
      have hidxSucc : idx.val + 1 ≤ m := by simpa using hj
      have hidx : idx.val < m := by omega
      let idx' : Fin m := ⟨idx.val, hidx⟩
      have hprev : (TashkinovSeriesDataPrefix m hm data).coloring idx'.castSucc =
          data.coloring idx.castSucc := by rfl
      have htree : (TashkinovSeriesDataPrefix m hm data).tree
          idx'.succ.castSucc = data.tree idx.succ.castSucc := by rfl
      have htreeCurrent : (TashkinovSeriesDataPrefix m hm data).tree
          idx'.castSucc.succ = data.tree idx.castSucc.succ := by rfl
      have hcur : (TashkinovSeriesDataPrefix m hm data).coloring idx'.succ =
          data.coloring idx.succ := by rfl
      have hcurStored : (TashkinovSeriesDataPrefix m hm data).stored idx'.succ =
          data.stored idx.succ := by rfl
      have hcurEdges : (TashkinovSeriesDataPrefix m hm data).connectingEdges
          idx'.succ = data.connectingEdges idx.succ := by rfl
      have hcurKind : (TashkinovSeriesDataPrefix m hm data).kind idx'.succ =
          data.kind idx.succ := by rfl
      have hcurVertex : (TashkinovSeriesDataPrefix m hm data).chosenVertex
          idx'.succ = data.chosenVertex idx.succ := by rfl
      have hcurOutside : (TashkinovSeriesDataPrefix m hm data).outsideVertex
          idx'.succ = data.outsideVertex idx.succ := by rfl
      have hcurDelta : (TashkinovSeriesDataPrefix m hm data).delta idx'.succ =
          data.delta idx.succ := by rfl
      have hcurGamma : (TashkinovSeriesDataPrefix m hm data).gamma idx'.succ =
          data.gamma idx.succ := by rfl
      have hnext : (TashkinovSeriesDataPrefix m hm data).tree idx'.succ.succ =
          data.tree idx.succ.succ := by rfl
      have haLe : available.earlier.val ≤ idx.val := by
        simpa using available.earlierAtMost
      have haBound : available.earlier.val < m + 1 := by omega
      let earlier' : Fin (m + 1) := ⟨available.earlier.val, haBound⟩
      have hkindEarlier : (TashkinovSeriesDataPrefix m hm data).kind
          earlier' = data.kind available.earlier := by rfl
      have hgammaEarlier : (TashkinovSeriesDataPrefix m hm data).gamma
          earlier' = data.gamma available.earlier := by rfl
      have hdeltaEarlier : (TashkinovSeriesDataPrefix m hm data).delta
          earlier' = data.delta available.earlier := by rfl
      have htreeEarlier : (TashkinovSeriesDataPrefix m hm data).tree
          earlier'.castSucc = data.tree available.earlier.castSucc := by rfl
      let cycle' : TwoColorCycle G
          ((TashkinovSeriesDataPrefix m hm data).coloring idx'.castSucc)
          available.gamma available.delta := {
        base := available.cycle.base
        walk := @Eq.ndrec (PartialEdgeColoring E k)
          (data.coloring idx.castSucc)
          (fun phi => (TwoColorIncidenceGraph G phi available.gamma
            available.delta).Walk available.cycle.base available.cycle.base)
          available.cycle.walk
          ((TashkinovSeriesDataPrefix m hm data).coloring idx'.castSucc)
          hprev.symm
        isCycle := by
          dsimp
          cases hprev
          exact available.cycle.isCycle
      }
      let returnPath' : (TwoColorIncidenceGraph G
          ((TashkinovSeriesDataPrefix m hm data).coloring idx'.castSucc)
          available.gamma available.delta).Walk (Sum.inr available.edge)
          (Sum.inl available.returnVertex) :=
        @Eq.ndrec (PartialEdgeColoring E k) (data.coloring idx.castSucc)
          (fun phi => (TwoColorIncidenceGraph G phi available.gamma
            available.delta).Walk (Sum.inr available.edge)
            (Sum.inl available.returnVertex))
          available.returnPath
          ((TashkinovSeriesDataPrefix m hm data).coloring idx'.castSucc)
          hprev.symm
      let available' : RevisitingExtensionCertificate
          (TashkinovSeriesDataPrefix m hm data) idx'.castSucc := {
        earlier := earlier'
        earlierPositive := by
          simpa [earlier'] using available.earlierPositive
        earlierAtMost := by
          simpa [earlier', idx'] using available.earlierAtMost
        earlierPE := by
          simpa [hkindEarlier] using available.earlierPE
        interveningRevisiting := by
          intro j hjpos hjafter hjatMost
          let j' : Fin (rounds + 1) := Fin.castLE (by omega) j
          have hstep := available.interveningRevisiting j'
            (by simpa [j'] using hjpos)
            (by simpa [j', earlier'] using hjafter)
            (by simpa [j', idx'] using hjatMost)
          have hkindJ : (TashkinovSeriesDataPrefix m hm data).kind j =
              data.kind j' := by rfl
          simpa [hkindJ] using hstep
        gamma := available.gamma
        delta := available.delta
        earlierGamma := by
          simpa [hgammaEarlier] using available.earlierGamma
        earlierDelta := by
          simpa [hdeltaEarlier] using available.earlierDelta
        cycle := cycle'
        meetsEarlier := by
          rcases available.meetsEarlier with ⟨v, hv, hc⟩
          refine ⟨v, ?_, ?_⟩
          · rwa [← htreeEarlier] at hv
          · dsimp [cycle']
            cases hprev
            exact hc
        leavesCurrent := by
          rcases available.leavesCurrent with ⟨v, hv, hc⟩
          refine ⟨v, ?_, ?_⟩
          · rwa [← htreeCurrent] at hv
          · dsimp [cycle']
            cases hprev
            exact hc
        edge := available.edge
        edgeOnCycle := by
          dsimp [cycle']
          cases hprev
          exact available.edgeOnCycle
        edgeBoundary := by
          simpa only [htreeCurrent] using available.edgeBoundary
        insideEndpoint := available.insideEndpoint
        outsideEndpoint := available.outsideEndpoint
        insideInCurrent := by
          simpa only [htreeCurrent] using available.insideInCurrent
        outsideNotCurrent := by
          simpa only [htreeCurrent] using available.outsideNotCurrent
        edgeEnds := available.edgeEnds
        returnVertex := available.returnVertex
        returnInEarlier := by
          simpa only [htreeEarlier] using available.returnInEarlier
        returnPath := returnPath'
        returnPathIsPath := by
          dsimp [returnPath']
          cases hprev
          exact available.returnPathIsPath
        returnPathOnCycle := by
          dsimp [returnPath', cycle']
          cases hprev
          exact available.returnPathOnCycle
        returnPathInternal := by
          intro v hv
          have hv' : Sum.inl v ∈ available.returnPath.support := by
            dsimp [returnPath'] at hv
            cases hprev
            exact hv
          simpa only [htreeCurrent] using available.returnPathInternal v hv'
      }
      have prefixCert : TashkinovSeriesStep G k m e0 input
          (TashkinovSeriesDataPrefix m hm data) idx'.succ := by
        apply TashkinovSeriesStep.RE (i := idx') (available := available')
          (adjoined := adjoined)
        · rw [hprev]
          exact previousProper
        · rw [hprev]
          exact previousOneUncolored
        · rw [hprev, htree]
          exact previousClosed
        · rw [hprev, htree]
          exact previousNotStronglyClosed
        · rw [hcur, hprev]
          exact currentColoring
        · change (TashkinovSeriesDataPrefix m hm data).stored idx'.succ =
            {available.delta, available.gamma}
          rw [hcurStored]
          exact currentStored
        · change (TashkinovSeriesDataPrefix m hm data).connectingEdges
            idx'.succ = {available.edge}
          rw [hcurEdges]
          exact currentEdges
        · rw [hcurKind]
          exact currentKind
        · change (TashkinovSeriesDataPrefix m hm data).chosenVertex
            idx'.succ = some available.insideEndpoint
          rw [hcurVertex]
          exact currentVertex
        · change (TashkinovSeriesDataPrefix m hm data).outsideVertex
            idx'.succ = some available.outsideEndpoint
          rw [hcurOutside]
          exact currentOutside
        · change (TashkinovSeriesDataPrefix m hm data).delta idx'.succ =
            some available.delta
          rw [hcurDelta]
          exact currentDelta
        · change (TashkinovSeriesDataPrefix m hm data).gamma idx'.succ =
            some available.gamma
          rw [hcurGamma]
          exact currentGamma
        · change TreeSequenceAdjoinEdge
            ((TashkinovSeriesDataPrefix m hm data).tree idx'.succ.castSucc)
            available.edge adjoined
          rw [htree]
          exact adjoinedExactly
        · rw [hcur, hnext]
          exact closedExtension
        · rw [htree, hnext]
          exact orderedExtension
        · rw [htree, hnext]
          exact strictExtension
      have hresult : idx'.succ =
          (⟨idx.succ.val, by omega⟩ : Fin (m + 1)) := by
        apply Fin.ext
        rfl
      rw [← hresult]
      exact ⟨prefixCert, proof_irrel_heq _ _⟩
  let included : Fin (rounds + 1) :=
    Fin.castLE (Nat.add_le_add_right hm 1) i
  have hibound : included.val ≤ m := by
    exact Nat.le_of_lt_succ i.isLt
  have hcertType : TashkinovSeriesStep G k rounds e0 input data included := by
    exact cert
  obtain ⟨prefixCert, hcert⟩ := aux included hibound hcertType
  have hi : (⟨included.val, by omega⟩ : Fin (m + 1)) = i := by
    apply Fin.ext
    rfl
  rw [hi] at prefixCert
  exact ⟨prefixCert, hcert⟩
