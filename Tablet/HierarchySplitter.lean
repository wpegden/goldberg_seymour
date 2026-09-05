import Tablet.CombinedStableClosurePreserved
import Tablet.CombinedStableColoring
import Tablet.CorrespondingExtendedTashkinovTree
import Tablet.MaximumPropertyTransport
import Tablet.ModColoring
import Tablet.SameHierarchyStages
import Tablet.TashkinovAugmentationSequence
import Tablet.Td

-- [TABLET NODE: HierarchySplitter]
theorem HierarchySplitter {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi sigma : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (hMP : MaximumProperty ett) (hpositive : 0 < ett.rounds)
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
           ModColoring lower sigma))
    (base : HierarchyBase ett phi) (H : TashkinovHierarchy ett base)
    (hPE : ett.series.data.kind (Fin.last ett.rounds) =
      some TashkinovExtensionKind.PE)
    (hproperPhi : IsProperEdgeColoring G phi)
    (honePhi : IsOneEdgeUncolored phi e0)
    (hproperSigma : IsProperEdgeColoring G sigma)
    (honeSigma : IsOneEdgeUncolored sigma e0)
    (hcombined : CombinedStableColoring
      (ett.series.data.tree (Fin.last ett.rounds).castSucc)
      base.closure
      (TashkinovStoredColors ett.series.data (Fin.last ett.rounds))
      phi sigma)
    (hbuilt : TashkinovAugmentationSequence sigma
      (ett.series.data.tree (Fin.last ett.rounds).castSucc) T) :
    ∃ corr : CorrespondingExtendedTashkinovTree G k e0 ett sigma T,
      MaximumProperty corr.replacementETT ∧
      ∃ baseSigma : HierarchyBase corr.replacementETT sigma,
        ∃ K : TashkinovHierarchy corr.replacementETT baseSigma,
          SameHierarchyStages H K := by
-- BODY
  classical
  have hstable : StableColoring
      (ett.series.data.tree (Fin.last ett.rounds).castSucc)
      (TashkinovStoredColors ett.series.data (Fin.last ett.rounds))
      (ett.series.data.coloring (Fin.last ett.rounds)) sigma := by
    simpa [ett.generatingColoring] using hcombined.1
  have hmod : ModColoring ett sigma := by
    exact Td G k e0 input T phi ett hMP hpositive hlower sigma
      hproperSigma honeSigma hstable
  rcases hmod with ⟨hsProper, hsOne, hmodProp⟩
  have hbase := CombinedStableClosurePreserved G k e0 input T phi phi sigma ett
    hpositive base ett.generatingColoring hPE hproperPhi honePhi hproperSigma honeSigma hcombined
  let n : Fin (ett.rounds + 1) := Fin.last ett.rounds
  let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc
  have hinitial : TreeSequenceInitialSegment Tn T := by
    have hi : (⟨ett.rounds, by omega⟩ : Fin (ett.rounds + 2)) =
        (Fin.last ett.rounds).castSucc := Fin.ext (by rfl)
    change TreeSequenceInitialSegment
      (ett.series.data.tree (Fin.last ett.rounds).castSucc) T
    rw [← hi]
    exact ett.abovePenultimate
  have hstrict : Tn.length < T.length := by
    have hi : (⟨ett.rounds, by omega⟩ : Fin (ett.rounds + 2)) =
        (Fin.last ett.rounds).castSucc := Fin.ext (by rfl)
    change (ett.series.data.tree (Fin.last ett.rounds).castSucc).length < T.length
    rw [← hi]
    exact ett.strictAbovePenultimate
  have hcorr : Nonempty (CorrespondingExtendedTashkinovTree G k e0 ett sigma T) := by
    exact hmodProp T hinitial hstrict (Or.inl ⟨hPE, hbuilt⟩)
  let corr : CorrespondingExtendedTashkinovTree G k e0 ett sigma T :=
    Classical.choice hcorr
  have hcorrMP : MaximumProperty corr.replacementETT := by
    exact MaximumPropertyTransport G k e0 ett sigma
      ⟨hsProper, hsOne, hmodProp⟩ T corr hMP
  refine ⟨corr, hcorrMP, ?_⟩
  have finish : ∀ (c : CorrespondingExtendedTashkinovTree G k e0 ett sigma T),
      MaximumProperty c.replacementETT →
      ∃ baseSigma : HierarchyBase c.replacementETT sigma,
        ∃ K : TashkinovHierarchy c.replacementETT baseSigma,
          SameHierarchyStages H K := by
    intro c hc
    rcases c with ⟨replacementInput, replacementSeries, replacementETT,
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
        ⟨ett.rounds - 1, Nat.sub_lt (Nat.zero_lt_of_lt hpositive) (by omega)⟩
      have hq : q.succ = Fin.last ett.rounds := by
        apply Fin.ext
        simp [q]
        omega
      have hfinal : replacementSeries.data.tree (Fin.last ett.rounds).castSucc =
          ett.series.data.tree (Fin.last ett.rounds).castSucc := by
        rw [← hq]
        exact ladderTreesAgree q
      have hkindEq : replacementSeries.data.kind (Fin.last ett.rounds) =
          ett.series.data.kind (Fin.last ett.rounds) := by
        have hk := extensionKindsAgree q.succ
        rw [hq] at hk
        exact hk
      have hkind : replacementSeries.data.kind (Fin.last ett.rounds) =
          some TashkinovExtensionKind.PE := hkindEq.trans hPE
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
      have chosenAgree : replacementSeries.data.chosenVertex
          (Fin.last ett.rounds) = ett.series.data.chosenVertex
          (Fin.last ett.rounds) := by
        have oldStep := ett.series.certified (Fin.last ett.rounds)
        have newStep := replacementSeries.certified (Fin.last ett.rounds)
        generalize oldIndex : Fin.last ett.rounds = oldTarget at oldStep
        generalize newIndex : Fin.last ett.rounds = newTarget at newStep
        cases oldStep with
        | initial triple seedLength initialColoring initialStored initialEdges
            initialKind initialVertex initialOutside initialDelta initialGamma initialClosure =>
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
            oldGamma gammaRule secondStable secondStableProper secondStableOneUncolored
            secondStableRelation exitWitness oldColoring oldProper oldOneUncolored
            oldStored oldEdges oldKind oldVertex oldOutside oldDelta oldGamma2
            closedExtension orderedExtension strictExtension =>
          have hio : oi = q := by
            apply Fin.ext
            have hv := congrArg Fin.val oldIndex
            simp [q] at hv ⊢
            omega
          subst oi
          cases newStep with
          | initial triple seedLength initialColoring initialStored initialEdges
              initialKind initialVertex initialOutside initialDelta initialGamma initialClosure =>
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
              newGamma gammaRule secondStable secondStableProper secondStableOneUncolored
              secondStableRelation exitWitness newColoring newProper newOneUncolored
              newStored newEdges newKind newVertex newOutside newDelta newGamma2
              closedExtension orderedExtension strictExtension =>
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
                (replacementSeries.data.tree (Fin.last ett.rounds).castSucc) := by
              simpa [hq] using newChoice.vertexDefective.1
            have hold : oldChoice.vertex ∈ TreeSequenceVertexSet
                (ett.series.data.tree (Fin.last ett.rounds).castSucc) := by
              simpa [hq] using oldChoice.vertexDefective.1
            have hnewOutside : newChoice.otherEndpoint ∉ TreeSequenceVertexSet
                (replacementSeries.data.tree (Fin.last ett.rounds).castSucc) := by
              simpa [hq] using newChoice.otherOutside
            have holdOutside : oldChoice.otherEndpoint ∉ TreeSequenceVertexSet
                (ett.series.data.tree (Fin.last ett.rounds).castSucc) := by
              simpa [hq] using oldChoice.otherOutside
            have hv := insideUnique newChoice.vertex oldChoice.vertex
              newChoice.otherEndpoint oldChoice.otherEndpoint newChoice.edge
              hnew hold hnewOutside holdOutside
              newChoice.edgeEnds (hedge ▸ oldChoice.edgeEnds)
            have hvertices := newVertex.trans ((congrArg some hv).trans oldVertex.symm)
            simpa [hq] using hvertices
      have transportVertex : ∀ (A B : TreeSequence G e0), ∀ (h : A = B),
          ∀ i : Fin (B.length + 1),
          A.vertex (Fin.cast (congrArg (fun W : TreeSequence G e0 => W.length + 1)
            h.symm) i) = B.vertex i := by
        intro A B h i
        cases h
        rfl
      let pos : Fin ((replacementSeries.data.tree
          (Fin.last ett.rounds).castSucc).length + 1) :=
        Fin.cast (congrArg (fun W : TreeSequence G e0 => W.length + 1)
          hfinal.symm) base.supportPosition
      let baseSigma : HierarchyBase
          { rounds := ett.rounds
            roundsPositive := by omega
            series := replacementSeries
            abovePenultimate := above
            strictAbovePenultimate := strict
            belowFinal := below
            generatingColoring := generating } sigma :=
        { core := base.core
          closure := base.closure
          supportPosition := pos
          supportPositive := by simpa [pos] using base.supportPositive
          terminalMissingColors := by rfl
          parallel := by
            dsimp
            intro hp
            have hp' : ett.series.data.kind (Fin.last ett.rounds) =
                some TashkinovExtensionKind.PE := by
              exact hkindEq ▸ hp
            have hb := base.parallel hp'
            refine ⟨?_, ?_, ?_⟩
            · have hvertex :
                  (replacementSeries.data.tree (Fin.last ett.rounds).castSucc).vertex pos =
              (ett.series.data.tree (Fin.last ett.rounds).castSucc).vertex
                      base.supportPosition := by
                exact transportVertex _ _ hfinal base.supportPosition
              rw [chosenAgree]
              rw [hvertex]
              simpa [hfinal] using hb.1
            · simpa [pos, hfinal] using hbase.2.2
            · simpa [hfinal] using hb.2.2
          nonparallel := by
            dsimp
            intro hp
            exact False.elim (hp hkind) }
      refine ⟨baseSigma, ?_⟩
      let K : TashkinovHierarchy _ baseSigma :=
        { dividerCount := H.dividerCount
          stage := H.stage
          baseStage := by simpa [hfinal] using H.baseStage
          terminalStage := H.terminalStage
          nested := H.nested
          strict := H.strict
          dividerPosition := H.dividerPosition
          dividerPositive := H.dividerPositive
          dividerIncreasing := H.dividerIncreasing
          dividerStage := H.dividerStage
          coreInsideFirst := H.coreInsideFirst }
      refine ⟨K, ?_⟩
      simp [SameHierarchyStages, baseSigma, K, hPE, hkind]
  exact finish corr hcorrMP
