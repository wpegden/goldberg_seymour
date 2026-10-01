import Tablet.Basic2
import Tablet.TdEarlierPEWitnessIdentification
import Tablet.TdReplacementPrefixExact
import Tablet.AdjacentEdges
import Tablet.BoundaryColorEdges
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
import Tablet.IsOneEdgeUncolored
import Tablet.IsProperEdgeColoring
import Tablet.KTriple
import Tablet.LooplessMultigraph
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
import Tablet.TashkinovSeriesFinalETTExists
import Tablet.TashkinovSeriesStep
import Tablet.TashkinovStoredColors
import Tablet.TashkinovStoredColorsAppend
import Tablet.TechnicalTheoremBase
import Tablet.TreeExit
import Tablet.TreeExitPath
import Tablet.TreeIncidentEdge
import Tablet.TreeInterchangeable
import Tablet.TreeMissingColors
import Tablet.TreeSequenceAdjoinEdge
import Tablet.TreeSequenceInitialSegment
import Tablet.TwoColorComponent
import Tablet.TwoColorIncidenceGraph
import Tablet.TwoColorComponentSpanningPath
import Tablet.TwoColorComponentSwap
import Tablet.TwoColorCycle
import Tablet.TwoColorIncidenceDegreeAtMostTwo
import Tablet.TwoColorPathComponent
import Tablet.TwoColorNontrivialPathComponent
import Tablet.RevisitingExtensionCertificateAppend
import Tablet.ParallelExtensionColorAppend
import Tablet.sc1
import Tablet.sc2

set_option maxHeartbeats 1800000

-- [TABLET NODE: TdTerminalSEPERebuild]
theorem TdTerminalSEPERebuild {V E : Type*} [Fintype V] [Fintype E]
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
    (ett.series.data.kind n = some TashkinovExtensionKind.SE ∨
      ett.series.data.kind n = some TashkinovExtensionKind.PE) →
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
  intro hterminal sigma hsigmaProper hsigmaOne hsigmaStable
  refine ⟨hsigmaProper, hsigmaOne, ?_⟩
  intro Tstar hTnTstar hstrict heligible
  obtain ⟨closureTree, hclosure⟩ := TashkinovClosureExists sigma Tstar
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
  have hsigmaStableQ : StableColoring
      (ett.series.data.tree q.succ.castSucc)
      (TashkinovStoredColors ett.series.data q.succ)
      (ett.series.data.coloring q.succ) sigma := by
    simpa [hqSucc] using hsigmaStable
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
  | RE i previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed available currentColoring currentStored
      currentEdges currentKind currentVertex currentOutside currentDelta
      currentGamma adjoined adjoinedExactly closedExtension orderedExtension
      strictExtension =>
      have hbad : some TashkinovExtensionKind.RE =
          some TashkinovExtensionKind.SE ∨
          some TashkinovExtensionKind.RE =
            some TashkinovExtensionKind.PE := by
        simpa [htarget, currentKind] using hterminal
      rcases hbad with hbad | hbad <;> cases hbad
  | SE i previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternative
      currentColoring currentStored currentEdges currentKind currentVertex
      currentOutside currentDelta currentGamma adjoined adjoinedExactly
      closedExtension orderedExtension strictExtension =>
      have hi : i = q := by
        apply Fin.ext
        have hv : ett.rounds = i.val + 1 := by
          simpa using congrArg Fin.val htarget
        change i.val = ett.rounds - 1
        omega
      subst i
      have hseKind : ett.series.data.kind q.succ =
          some TashkinovExtensionKind.SE := by
        simpa [htarget] using currentKind
      have hprefix := TdReplacementPrefixExact G k e0 input T generating ett
        hMP hpositive hlower sigma hsigmaProper hsigmaOne
        (by simpa [hqSucc] using hsigmaStable)
      obtain ⟨sigmaPrev, hsigmaPrevProper, hsigmaPrevOne,
          hsigmaPrevStable, hsigmaPrevEq, hparallelPrev, hprefixCases⟩ := hprefix
      have hsigmaPrevStableQ : StableColoring
          (ett.series.data.tree q.succ.castSucc)
          (TashkinovStoredColors ett.series.data q.castSucc)
          (ett.series.data.coloring q.castSucc) sigmaPrev := by
        simpa [hqSucc, hqCast] using hsigmaPrevStable
      have hsigmaPrevSigma : sigmaPrev = sigma :=
        hsigmaPrevEq (Or.inl (by simpa [hqSucc] using hseKind))
      have hpreviousControl :
          TreeMissingColors (ett.series.data.coloring q.castSucc)
                (ett.series.data.tree q.succ.castSucc) ∪
              TashkinovStoredColors ett.series.data q.castSucc ⊆
            TreeMissingColors (ett.series.data.coloring q.succ)
                (ett.series.data.tree q.succ.castSucc) ∪
              TashkinovStoredColors ett.series.data q.succ :=
        (HkuMissingStoredMonotone G k ett.rounds e0 input ett.series q).1
      have hdeltaCurrentControl : choice.color ∈
          TreeMissingColors (ett.series.data.coloring q.succ)
                (ett.series.data.tree q.succ.castSucc) ∪
              TashkinovStoredColors ett.series.data q.succ := by
        by_cases hm : choice.color ∈
            TreeMissingColors (ett.series.data.coloring q.succ)
              (ett.series.data.tree q.succ.castSucc)
        · exact Finset.mem_union_left _ hm
        · apply Finset.mem_union_right
          unfold TashkinovStoredColors
          have hqpos : q.succ.val ≠ 0 := by simp
          rw [if_neg hqpos, Finset.mem_sdiff]
          refine ⟨?_, hm⟩
          simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
          refine ⟨q.succ, ?_⟩
          rw [if_pos le_rfl]
          simpa [currentStored]
      have henlargedControl :
          TreeMissingColors choice.selected
                (ett.series.data.tree q.succ.castSucc) ∪
              insert choice.color
                (TashkinovStoredColors ett.series.data q.castSucc) ⊆
            TreeMissingColors (ett.series.data.coloring q.succ)
                (ett.series.data.tree q.succ.castSucc) ∪
              TashkinovStoredColors ett.series.data q.succ := by
        intro c hc
        rcases Finset.mem_union.mp hc with hc | hc
        · apply Finset.mem_union_left
          simpa [currentColoring] using hc
        · rw [Finset.mem_insert] at hc
          rcases hc with rfl | hc
          · exact hdeltaCurrentControl
          · exact hpreviousControl (Finset.mem_union_right _ hc)
      have hsigmaPrevEnlarged : StableColoring
          (ett.series.data.tree q.succ.castSucc)
          (insert choice.color
            (TashkinovStoredColors ett.series.data q.castSucc))
          choice.selected sigmaPrev := by
        constructor
        · intro f hf hcolor
          rcases hcolor with ⟨c, hc, hfc⟩
          have hcopy := hsigmaStableQ.1 f hf
            ⟨c, henlargedControl hc, by simpa [currentColoring] using hfc⟩
          simpa [currentColoring, hsigmaPrevSigma] using hcopy
        · intro v hv
          simpa [currentColoring, hsigmaPrevSigma] using hsigmaStableQ.2 v hv
      have hdeltaBoundary : BoundaryColorEdges G choice.selected
            (TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc))
            choice.color =
          BoundaryColorEdges G sigmaPrev
            (TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc))
            choice.color := by
        ext f
        simp only [BoundaryColorEdges, Finset.mem_filter]
        constructor
        · rintro ⟨hf, hfc⟩
          refine ⟨hf, ?_⟩
          obtain ⟨x, hx, y, hy, hends⟩ := by
            simpa [BoundaryEdges] using hf
          have hinc : TreeIncidentEdge
              (ett.series.data.tree q.succ.castSucc) f := by
            refine ⟨x, hx, ?_⟩
            unfold Incident
            rw [hends]
            exact Sym2.mem_mk_left _ _
          exact (hsigmaPrevEnlarged.1 f hinc
            ⟨choice.color, Finset.mem_union_right _
              (Finset.mem_insert_self _ _), hfc⟩).trans hfc
        · rintro ⟨hf, hfc⟩
          refine ⟨hf, ?_⟩
          obtain ⟨x, hx, y, hy, hends⟩ := by
            simpa [BoundaryEdges] using hf
          have hinc : TreeIncidentEdge
              (ett.series.data.tree q.succ.castSucc) f := by
            refine ⟨x, hx, ?_⟩
            unfold Incident
            rw [hends]
            exact Sym2.mem_mk_left _ _
          have hcriterion := (sc1 G e0
            (ett.series.data.tree q.succ.castSucc)
            (insert choice.color
              (TashkinovStoredColors ett.series.data q.castSucc))
            choice.selected sigmaPrev choice.selectedProper
            choice.selectedOneUncolored hsigmaPrevProper hsigmaPrevOne).mp
              hsigmaPrevEnlarged
          exact (hcriterion f hinc (Or.inr
            ⟨choice.color, Finset.mem_union_right _
              (Finset.mem_insert_self _ _), hfc⟩)).symm.trans hfc
      have hchoiceDefective : DefectiveColor G sigmaPrev
          (TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc))
          choice.color := by
        obtain ⟨oldColor, holdDefective, holdEdge⟩ := choice.edgeDefective
        have holdColor : oldColor = choice.color := by
          have holdEdgeColor := (Finset.mem_filter.mp holdEdge).2
          exact Option.some.inj (holdEdgeColor.symm.trans choice.edgeColor)
        subst oldColor
        unfold DefectiveColor
        rw [← hdeltaBoundary]
        exact holdDefective
      have hchoiceEdgeNew : choice.edge ∈ BoundaryColorEdges G sigmaPrev
          (TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc))
          choice.color := by
        rw [← hdeltaBoundary]
        obtain ⟨oldColor, holdDefective, holdEdge⟩ := choice.edgeDefective
        have holdColor : oldColor = choice.color := by
          have holdEdgeColor := (Finset.mem_filter.mp holdEdge).2
          exact Option.some.inj (holdEdgeColor.symm.trans choice.edgeColor)
        simpa [holdColor] using holdEdge
      have hsigmaPrevSelf : StableColoring
          (ett.series.data.tree q.succ.castSucc)
          (TashkinovStoredColors ett.series.data q.castSucc)
          sigmaPrev sigmaPrev := by
        exact (sc2 G e0 (ett.series.data.tree q.succ.castSucc)
          (TashkinovStoredColors ett.series.data q.castSucc)).refl
          ⟨sigmaPrev, hsigmaPrevProper, hsigmaPrevOne⟩
      let newChoice : MaximumDefectiveChoice G e0
          (ett.series.data.tree q.succ.castSucc)
          (TashkinovStoredColors ett.series.data q.castSucc) sigmaPrev := {
        selected := sigmaPrev
        selectedProper := hsigmaPrevProper
        selectedOneUncolored := hsigmaPrevOne
        selectedStable := hsigmaPrevSelf
        vertex := choice.vertex
        vertexDefective := ⟨choice.vertexDefective.1, choice.edge,
          ⟨choice.color, hchoiceDefective, hchoiceEdgeNew⟩,
          choice.edgeIncident⟩
        maximal := by
          intro pi w hpiProper hpiOne hpiStable hw
          have hpiOld : StableColoring
              (ett.series.data.tree q.succ.castSucc)
              (TashkinovStoredColors ett.series.data q.castSucc)
              (ett.series.data.coloring q.castSucc) pi := by
            exact (sc2 G e0 (ett.series.data.tree q.succ.castSucc)
              (TashkinovStoredColors ett.series.data q.castSucc)).trans
                (x := ⟨ett.series.data.coloring q.castSucc,
                  ⟨previousProper, previousOneUncolored⟩⟩)
                (y := ⟨sigmaPrev, ⟨hsigmaPrevProper, hsigmaPrevOne⟩⟩)
                (z := ⟨pi, ⟨hpiProper, hpiOne⟩⟩)
                hsigmaPrevStableQ hpiStable
          exact choice.maximal pi w hpiProper hpiOne hpiOld hw
        edge := choice.edge
        edgeDefective := ⟨choice.color, hchoiceDefective, hchoiceEdgeNew⟩
        edgeIncident := choice.edgeIncident
        otherEndpoint := choice.otherEndpoint
        otherOutside := choice.otherOutside
        edgeEnds := choice.edgeEnds
        color := choice.color
        edgeColor := (Finset.mem_filter.mp hchoiceEdgeNew).2 }
      have hclosedPrev : ColoredVertexSetClosed G sigmaPrev
          (TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc)) := by
        intro f c v hf hv hsf hcm
        obtain ⟨x, hx, y, hy, hends⟩ := by
          simpa [BoundaryEdges] using hf
        have hinc : TreeIncidentEdge
            (ett.series.data.tree q.succ.castSucc) f := by
          refine ⟨x, hx, ?_⟩
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
          (ett.series.data.coloring q.castSucc) sigmaPrev previousProper
          previousOneUncolored hsigmaPrevProper hsigmaPrevOne).mp
            hsigmaPrevStableQ
        have hcopy := hcriterion f hinc
          (Or.inr ⟨c, Finset.mem_union_left _ hcTree, hsf⟩)
        have holdf : ett.series.data.coloring q.castSucc f = some c :=
          hcopy.symm.trans hsf
        exact previousClosed hf hv holdf (hmissingEq ▸ hcm)
      have hnotStrongPrev : ¬ ColoredVertexSetStronglyClosed G sigmaPrev
          (TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc)) := by
        intro hstrong
        have hone : 1 < (BoundaryColorEdges G sigmaPrev
            (TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc))
            choice.color).card := by
          have htwo : 2 ≤ (BoundaryColorEdges G sigmaPrev
              (TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc))
              choice.color).card := hchoiceDefective
          omega
        obtain ⟨f, hf, g, hg, hfg⟩ := Finset.one_lt_card.mp hone
        have hfBoundary := (Finset.mem_filter.mp hf).1
        have hgBoundary := (Finset.mem_filter.mp hg).1
        have hfColor := (Finset.mem_filter.mp hf).2
        have hgColor := (Finset.mem_filter.mp hg).2
        exact (hstrong.2 hfBoundary hgBoundary hfg hfColor) hgColor
      have hnewAlternative : ∀ pi : PartialEdgeColoring E k,
          IsProperEdgeColoring G pi → IsOneEdgeUncolored pi e0 →
          StableColoring (ett.series.data.tree q.succ.castSucc)
            (insert newChoice.color
              (TashkinovStoredColors ett.series.data q.castSucc))
            newChoice.selected pi →
          Disjoint (MissingColors G pi newChoice.otherEndpoint)
            (TreeMissingColors pi
              (ett.series.data.tree q.succ.castSucc)) := by
        intro pi hpiProper hpiOne hpiStable
        have hpiOld : StableColoring
            (ett.series.data.tree q.succ.castSucc)
            (insert choice.color
              (TashkinovStoredColors ett.series.data q.castSucc))
            choice.selected pi := by
          exact (sc2 G e0 (ett.series.data.tree q.succ.castSucc)
            (insert choice.color
              (TashkinovStoredColors ett.series.data q.castSucc))).trans
              (x := ⟨choice.selected,
                ⟨choice.selectedProper, choice.selectedOneUncolored⟩⟩)
              (y := ⟨sigmaPrev, ⟨hsigmaPrevProper, hsigmaPrevOne⟩⟩)
              (z := ⟨pi, ⟨hpiProper, hpiOne⟩⟩)
              hsigmaPrevEnlarged (by simpa [newChoice] using hpiStable)
        simpa [newChoice] using
          seriesAlternative pi hpiProper hpiOne hpiOld
      rcases hprefixCases with hzero | hpositivePrefix
      · rcases hzero with ⟨hroundOne, prefixInput, zeroPrefix,
            hzeroTree, hzeroColor⟩
        rcases heligible with hparallel | hsimple
        · have hbad := hparallel.1.symm.trans
            (by simpa [hqSucc] using hseKind)
          cases hbad
        · rcases hsimple with ⟨hkind, fstar, seed, hfinalEdges,
              hadjoin, hroute⟩
          have hfstar : fstar = choice.edge := by
            apply Finset.mem_singleton.mp
            rw [← currentEdges, hqSucc, hfinalEdges]
            exact Finset.mem_singleton_self fstar
          have hrouteClosure : TashkinovAugmentationSequence sigma seed
              closureTree := hroute.trans hclosure.1
          have hseedClosure : TashkinovClosure sigma seed closureTree :=
            ⟨hrouteClosure, hclosure.2⟩
          let zeroLast : Fin (0 + 1) := Fin.last 0
          let newStored : Finset (Fin k) := {choice.color}
          let newEdges : Finset E := {choice.edge}
          let newKind : Option TashkinovExtensionKind :=
            some TashkinovExtensionKind.SE
          let newVertex : Option V := some choice.vertex
          let newOutside : Option V := some choice.otherEndpoint
          let newDelta : Option (Fin k) := some choice.color
          let newGamma : Option (Fin k) := none
          let appendedData := TashkinovSeriesDataAppend zeroPrefix.data
            closureTree sigma newStored newEdges newKind newVertex newOutside
            newDelta newGamma
          have happendLastTree : appendedData.tree (Fin.last 2) =
              closureTree := by
            simp only [appendedData, TashkinovSeriesDataAppend,
              Fin.lastCases_last]
          have happendLastColor : appendedData.coloring (Fin.last 1) =
              sigma := by
            simp only [appendedData, TashkinovSeriesDataAppend,
              Fin.lastCases_last]
          have happendLastStored : appendedData.stored (Fin.last 1) =
              newStored := by
            simp only [appendedData, TashkinovSeriesDataAppend,
              Fin.lastCases_last]
          have happendLastEdges : appendedData.connectingEdges (Fin.last 1) =
              newEdges := by
            simp only [appendedData, TashkinovSeriesDataAppend,
              Fin.lastCases_last]
          have happendLastKind : appendedData.kind (Fin.last 1) =
              newKind := by
            simp only [appendedData, TashkinovSeriesDataAppend,
              Fin.lastCases_last]
          have happendLastVertex : appendedData.chosenVertex (Fin.last 1) =
              newVertex := by
            simp only [appendedData, TashkinovSeriesDataAppend,
              Fin.lastCases_last]
          have happendLastOutside : appendedData.outsideVertex (Fin.last 1) =
              newOutside := by
            simp only [appendedData, TashkinovSeriesDataAppend,
              Fin.lastCases_last]
          have happendLastDelta : appendedData.delta (Fin.last 1) =
              newDelta := by
            simp only [appendedData, TashkinovSeriesDataAppend,
              Fin.lastCases_last]
          have happendLastGamma : appendedData.gamma (Fin.last 1) =
              newGamma := by
            simp only [appendedData, TashkinovSeriesDataAppend,
              Fin.lastCases_last]
          have hstoredZero : TashkinovStoredColors appendedData
              zeroLast.castSucc = TashkinovStoredColors zeroPrefix.data
                zeroLast := by
            exact TashkinovStoredColorsAppend zeroPrefix.data closureTree sigma
              newStored newEdges newKind newVertex newOutside newDelta newGamma
              zeroLast
          have happendTree : appendedData.tree zeroLast.succ.castSucc =
              ett.series.data.tree q.succ.castSucc := by
            calc
              appendedData.tree zeroLast.succ.castSucc =
                  zeroPrefix.data.tree (Fin.last 1) := by
                    simp only [appendedData, TashkinovSeriesDataAppend,
                      Fin.lastCases_castSucc]
                    congr 1
              _ = ett.series.data.tree (Fin.last ett.rounds).castSucc := hzeroTree
              _ = ett.series.data.tree q.succ.castSucc := by rw [hqSucc]
          have happendColor : appendedData.coloring zeroLast.castSucc =
              sigmaPrev := by
            calc
              appendedData.coloring zeroLast.castSucc =
                  zeroPrefix.data.coloring (Fin.last 0) := by
                    simp only [appendedData, TashkinovSeriesDataAppend,
                      Fin.lastCases_castSucc]
                    congr 1
              _ = sigmaPrev := hzeroColor
          have happendStored : TashkinovStoredColors appendedData
                zeroLast.castSucc =
              TashkinovStoredColors ett.series.data q.castSucc := by
            unfold TashkinovStoredColors
            simp [zeroLast, q, hroundOne]
          let appendedChoice : MaximumDefectiveChoice G e0
              (appendedData.tree zeroLast.succ.castSucc)
              (TashkinovStoredColors appendedData zeroLast.castSucc)
              (appendedData.coloring zeroLast.castSucc) := {
            selected := sigmaPrev
            selectedProper := hsigmaPrevProper
            selectedOneUncolored := hsigmaPrevOne
            selectedStable := by
              rw [happendTree, happendStored, happendColor]
              exact newChoice.selectedStable
            vertex := choice.vertex
            vertexDefective := by
              rw [happendTree]
              exact newChoice.vertexDefective
            maximal := by
              intro pi w hpiProper hpiOne hpiStable hw
              rw [happendTree, happendStored, happendColor] at hpiStable
              rw [happendTree] at hw ⊢
              exact newChoice.maximal pi w hpiProper hpiOne hpiStable hw
            edge := choice.edge
            edgeDefective := by
              rw [happendTree]
              exact newChoice.edgeDefective
            edgeIncident := choice.edgeIncident
            otherEndpoint := choice.otherEndpoint
            otherOutside := by
              rw [happendTree]
              exact newChoice.otherOutside
            edgeEnds := choice.edgeEnds
            color := choice.color
            edgeColor := newChoice.edgeColor }
          have hnoRevisitingZero : ¬ Nonempty
              (RevisitingExtensionCertificate appendedData
                zeroLast.castSucc) := by
            rintro ⟨cert⟩
            obtain ⟨oldCert, -, -, -, -, -⟩ :=
              (RevisitingExtensionCertificateAppend zeroPrefix.data
                closureTree sigma newStored newEdges newKind newVertex
                newOutside newDelta newGamma zeroLast).1 cert
            have hle := oldCert.earlierAtMost
            have hpos := oldCert.earlierPositive
            simp [zeroLast] at hle
            omega
          have hnewAlternativeZero : ∀ pi : PartialEdgeColoring E k,
              IsProperEdgeColoring G pi → IsOneEdgeUncolored pi e0 →
              StableColoring (appendedData.tree zeroLast.succ.castSucc)
                (insert appendedChoice.color
                  (TashkinovStoredColors appendedData zeroLast.castSucc))
                appendedChoice.selected pi →
              Disjoint (MissingColors G pi appendedChoice.otherEndpoint)
                (TreeMissingColors pi
                  (appendedData.tree zeroLast.succ.castSucc)) := by
            intro pi hpiProper hpiOne hpiStable
            have hpiStable' := hpiStable
            change StableColoring (appendedData.tree zeroLast.succ.castSucc)
              (insert choice.color
                (TashkinovStoredColors appendedData zeroLast.castSucc))
              sigmaPrev pi at hpiStable'
            rw [happendTree, happendStored] at hpiStable'
            have hresult := hnewAlternative pi hpiProper hpiOne
              (by simpa [appendedChoice, newChoice] using hpiStable')
            change Disjoint (MissingColors G pi choice.otherEndpoint)
              (TreeMissingColors pi
                (appendedData.tree zeroLast.succ.castSucc))
            rw [happendTree]
            simpa [appendedChoice, newChoice] using hresult
          have hstrictClosure :
              (ett.series.data.tree (Fin.last ett.rounds).castSucc).length <
                closureTree.length := lt_of_lt_of_le hstrict hTstarClosure.1
          have lastStep : TashkinovSeriesStep G k 1 e0 prefixInput
              appendedData (Fin.last 1) := by
            have hlast : zeroLast.succ = Fin.last 1 := by
              apply Fin.ext
              rfl
            rw [← hlast]
            apply TashkinovSeriesStep.SE (i := zeroLast)
              (choice := appendedChoice) (adjoined := seed)
            · rw [happendColor]; exact hsigmaPrevProper
            · rw [happendColor]; exact hsigmaPrevOne
            · rw [happendColor, happendTree]; exact hclosedPrev
            · rw [happendColor, happendTree]; exact hnotStrongPrev
            · exact hnoRevisitingZero
            · exact hnewAlternativeZero
            · exact happendLastColor.trans hsigmaPrevSigma.symm
            · exact happendLastStored.trans (by rfl)
            · exact happendLastEdges.trans (by rfl)
            · exact happendLastKind.trans (by rfl)
            · exact happendLastVertex.trans (by rfl)
            · exact happendLastOutside.trans (by rfl)
            · exact happendLastDelta.trans (by rfl)
            · exact happendLastGamma.trans (by rfl)
            · change TreeSequenceAdjoinEdge
                (appendedData.tree zeroLast.succ.castSucc) choice.edge seed
              rw [happendTree]
              simpa [hqSucc, hfstar] using hadjoin
            · change TashkinovClosure (appendedData.coloring (Fin.last 1))
                seed (appendedData.tree (Fin.last 2))
              rw [happendLastColor, happendLastTree]
              exact hseedClosure
            · change TreeSequenceInitialSegment
                (appendedData.tree zeroLast.succ.castSucc)
                (appendedData.tree (Fin.last 2))
              rw [happendTree]
              rw [happendLastTree]
              simpa [hqSucc] using hTnClosure
            · change (appendedData.tree zeroLast.succ.castSucc).length <
                (appendedData.tree (Fin.last 2)).length
              rw [happendTree]
              rw [happendLastTree]
              simpa [hqSucc] using hstrictClosure
          obtain ⟨extendedSeries, hextendedData⟩ :=
            TashkinovSeriesAppend G k 0 e0 prefixInput zeroPrefix closureTree
              sigma newStored newEdges newKind newVertex newOutside newDelta
              newGamma lastStep
          have hroundsEq : 0 + 1 = ett.rounds := by omega
          let castSeries {a b : ℕ} (h : a = b)
              (S : TashkinovSeries G k a e0 prefixInput) :
              TashkinovSeries G k b e0 prefixInput := by
            subst b
            exact S
          have castSeriesTree : ∀ {a b : ℕ} (h : a = b)
              (S : TashkinovSeries G k a e0 prefixInput)
              (i : Fin (b + 2)),
              (castSeries h S).data.tree i = S.data.tree
                (Fin.cast (congrArg (fun m : ℕ => m + 2) h.symm) i) := by
            intro a b h S i
            subst b
            rfl
          have castSeriesColoring : ∀ {a b : ℕ} (h : a = b)
              (S : TashkinovSeries G k a e0 prefixInput)
              (i : Fin (b + 1)),
              (castSeries h S).data.coloring i = S.data.coloring
                (Fin.cast (congrArg (fun m : ℕ => m + 1) h.symm) i) := by
            intro a b h S i
            subst b
            rfl
          have castSeriesStored : ∀ {a b : ℕ} (h : a = b)
              (S : TashkinovSeries G k a e0 prefixInput)
              (i : Fin (b + 1)),
              (castSeries h S).data.stored i = S.data.stored
                (Fin.cast (congrArg (fun m : ℕ => m + 1) h.symm) i) := by
            intro a b h S i
            subst b
            rfl
          have castSeriesEdges : ∀ {a b : ℕ} (h : a = b)
              (S : TashkinovSeries G k a e0 prefixInput)
              (i : Fin (b + 1)),
              (castSeries h S).data.connectingEdges i =
                S.data.connectingEdges
                  (Fin.cast (congrArg (fun m : ℕ => m + 1) h.symm) i) := by
            intro a b h S i
            subst b
            rfl
          have castSeriesKind : ∀ {a b : ℕ} (h : a = b)
              (S : TashkinovSeries G k a e0 prefixInput)
              (i : Fin (b + 1)),
              (castSeries h S).data.kind i = S.data.kind
                (Fin.cast (congrArg (fun m : ℕ => m + 1) h.symm) i) := by
            intro a b h S i
            subst b
            rfl
          let finalSeries : TashkinovSeries G k ett.rounds e0 prefixInput :=
            castSeries hroundsEq extendedSeries
          let rawTreeIndex (i : Fin (ett.rounds + 2)) : Fin 3 :=
            Fin.cast (congrArg (fun m : ℕ => m + 2) hroundsEq.symm) i
          let rawDataIndex (i : Fin (ett.rounds + 1)) : Fin 2 :=
            Fin.cast (congrArg (fun m : ℕ => m + 1) hroundsEq.symm) i
          have hrawPenultimate : rawTreeIndex
                (⟨ett.rounds, by omega⟩ : Fin (ett.rounds + 2)) =
              zeroLast.succ.castSucc := by
            apply Fin.ext
            simp [rawTreeIndex, zeroLast]
            omega
          have hrawFinalTree : rawTreeIndex (Fin.last (ett.rounds + 1)) =
              Fin.last 2 := by
            apply Fin.ext
            simp [rawTreeIndex]
          have hrawFinalData : rawDataIndex (Fin.last ett.rounds) =
              Fin.last 1 := by
            apply Fin.ext
            simp [rawDataIndex]
          have hfinalTree : finalSeries.data.tree
              (Fin.last (ett.rounds + 1)) = closureTree := by
            calc
              finalSeries.data.tree (Fin.last (ett.rounds + 1)) =
                  extendedSeries.data.tree
                    (rawTreeIndex (Fin.last (ett.rounds + 1))) := by
                    exact castSeriesTree hroundsEq extendedSeries _
              _ = appendedData.tree
                    (rawTreeIndex (Fin.last (ett.rounds + 1))) := by
                    rw [hextendedData]
              _ = appendedData.tree (Fin.last 2) := by rw [hrawFinalTree]
              _ = closureTree := happendLastTree
          have hpenultimateTree : finalSeries.data.tree
              (⟨ett.rounds, by omega⟩ : Fin (ett.rounds + 2)) =
                ett.series.data.tree (Fin.last ett.rounds).castSucc := by
            calc
              finalSeries.data.tree
                    (⟨ett.rounds, by omega⟩ : Fin (ett.rounds + 2)) =
                  extendedSeries.data.tree
                    (rawTreeIndex
                      (⟨ett.rounds, by omega⟩ : Fin (ett.rounds + 2))) := by
                    exact castSeriesTree hroundsEq extendedSeries _
              _ = appendedData.tree
                    (rawTreeIndex
                      (⟨ett.rounds, by omega⟩ : Fin (ett.rounds + 2))) := by
                    rw [hextendedData]
              _ = appendedData.tree zeroLast.succ.castSucc := by
                    rw [hrawPenultimate]
              _ = ett.series.data.tree q.succ.castSucc := happendTree
              _ = ett.series.data.tree (Fin.last ett.rounds).castSucc := by
                    rw [hqSucc]
          have hfinalColor : finalSeries.data.coloring
              (Fin.last ett.rounds) = sigma := by
            calc
              finalSeries.data.coloring (Fin.last ett.rounds) =
                  extendedSeries.data.coloring
                    (rawDataIndex (Fin.last ett.rounds)) := by
                    exact castSeriesColoring hroundsEq extendedSeries _
              _ = appendedData.coloring
                    (rawDataIndex (Fin.last ett.rounds)) := by
                    rw [hextendedData]
              _ = appendedData.coloring (Fin.last 1) := by rw [hrawFinalData]
              _ = sigma := happendLastColor
          have hprefixFields : ∀ (i : Fin (ett.rounds + 1)),
              i.val < ett.rounds →
              zeroPrefix.data.stored zeroLast = ett.series.data.stored i ∧
              zeroPrefix.data.connectingEdges zeroLast =
                ett.series.data.connectingEdges i ∧
              zeroPrefix.data.kind zeroLast = ett.series.data.kind i := by
            intro i hi
            have hiZero : i.val = 0 := by
              have hr := hroundOne
              omega
            have hiEq : i = 0 := Fin.ext hiZero
            subst i
            have hold := zeroPrefix.certified 0
            have hnew := ett.series.certified 0
            cases hold with
            | initial triple0 seedLength0 initialColoring0 initialStored0
                initialEdges0 initialKind0 initialVertex0 initialOutside0
                initialDelta0 initialGamma0 initialClosure0 =>
              cases hnew with
              | initial triple1 seedLength1 initialColoring1 initialStored1
                  initialEdges1 initialKind1 initialVertex1 initialOutside1
                  initialDelta1 initialGamma1 initialClosure1 =>
                exact ⟨by simpa [zeroLast] using
                    initialStored0.trans initialStored1.symm,
                  by simpa [zeroLast] using
                    initialEdges0.trans initialEdges1.symm,
                  by simpa [zeroLast] using
                    initialKind0.trans initialKind1.symm⟩
          have hseriesDataAgree : ∀ i : Fin (ett.rounds + 1),
              finalSeries.data.stored i = ett.series.data.stored i ∧
              finalSeries.data.connectingEdges i =
                ett.series.data.connectingEdges i ∧
              finalSeries.data.kind i = ett.series.data.kind i := by
            intro i
            by_cases hi : i.val < ett.rounds
            · have hraw : rawDataIndex i = zeroLast.castSucc := by
                apply Fin.ext
                have hiZero : i.val = 0 := by
                  have hr := hroundOne
                  omega
                exact hiZero
              have hp := hprefixFields i hi
              constructor
              · calc
                  finalSeries.data.stored i =
                      extendedSeries.data.stored (rawDataIndex i) := by
                        exact castSeriesStored hroundsEq extendedSeries i
                  _ = appendedData.stored (rawDataIndex i) := by
                        rw [hextendedData]
                  _ = zeroPrefix.data.stored zeroLast := by
                        rw [hraw]
                        simp only [appendedData, TashkinovSeriesDataAppend,
                          Fin.lastCases_castSucc]
                  _ = ett.series.data.stored i := hp.1
              · constructor
                · calc
                    finalSeries.data.connectingEdges i =
                        extendedSeries.data.connectingEdges
                          (rawDataIndex i) := by
                          exact castSeriesEdges hroundsEq extendedSeries i
                    _ = appendedData.connectingEdges (rawDataIndex i) := by
                          rw [hextendedData]
                    _ = zeroPrefix.data.connectingEdges zeroLast := by
                          rw [hraw]
                          simp only [appendedData, TashkinovSeriesDataAppend,
                            Fin.lastCases_castSucc]
                    _ = ett.series.data.connectingEdges i := hp.2.1
                · calc
                    finalSeries.data.kind i =
                        extendedSeries.data.kind (rawDataIndex i) := by
                          exact castSeriesKind hroundsEq extendedSeries i
                    _ = appendedData.kind (rawDataIndex i) := by
                          rw [hextendedData]
                    _ = zeroPrefix.data.kind zeroLast := by
                          rw [hraw]
                          simp only [appendedData, TashkinovSeriesDataAppend,
                            Fin.lastCases_castSucc]
                    _ = ett.series.data.kind i := hp.2.2
            · have hilast : i = Fin.last ett.rounds := by
                apply Fin.ext
                have hibound := i.isLt
                simp
                omega
              subst i
              constructor
              · calc
                  finalSeries.data.stored (Fin.last ett.rounds) =
                      extendedSeries.data.stored
                        (rawDataIndex (Fin.last ett.rounds)) := by
                        exact castSeriesStored hroundsEq extendedSeries _
                  _ = appendedData.stored
                        (rawDataIndex (Fin.last ett.rounds)) := by
                        rw [hextendedData]
                  _ = appendedData.stored (Fin.last 1) := by rw [hrawFinalData]
                  _ = newStored := happendLastStored
                  _ = {choice.color} := rfl
                  _ = ett.series.data.stored (Fin.last ett.rounds) := by
                        rw [← hqSucc]
                        exact currentStored.symm
              · constructor
                · calc
                    finalSeries.data.connectingEdges (Fin.last ett.rounds) =
                        extendedSeries.data.connectingEdges
                          (rawDataIndex (Fin.last ett.rounds)) := by
                          exact castSeriesEdges hroundsEq extendedSeries _
                    _ = appendedData.connectingEdges
                          (rawDataIndex (Fin.last ett.rounds)) := by
                          rw [hextendedData]
                    _ = appendedData.connectingEdges (Fin.last 1) := by
                          rw [hrawFinalData]
                    _ = newEdges := happendLastEdges
                    _ = {choice.edge} := rfl
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
                    _ = appendedData.kind (Fin.last 1) := by rw [hrawFinalData]
                    _ = newKind := happendLastKind
                    _ = some TashkinovExtensionKind.SE := rfl
                    _ = ett.series.data.kind (Fin.last ett.rounds) := by
                          rw [← hqSucc]
                          exact currentKind.symm
          have hseriesTreeAgree : ∀ j : Fin ett.rounds,
              finalSeries.data.tree j.succ.castSucc =
                ett.series.data.tree j.succ.castSucc := by
            intro j
            have hj : j.succ = Fin.last ett.rounds := by
              apply Fin.ext
              have hjbound := j.isLt
              simp
              have hr := hroundOne
              omega
            have htreeIndex : rawTreeIndex j.succ.castSucc =
                zeroLast.succ.castSucc := by
              apply Fin.ext
              simpa [rawTreeIndex, zeroLast] using congrArg Fin.val hj
            calc
              finalSeries.data.tree j.succ.castSucc =
                  extendedSeries.data.tree (rawTreeIndex j.succ.castSucc) := by
                    exact castSeriesTree hroundsEq extendedSeries _
              _ = appendedData.tree (rawTreeIndex j.succ.castSucc) := by
                    rw [hextendedData]
              _ = appendedData.tree zeroLast.succ.castSucc := by rw [htreeIndex]
              _ = ett.series.data.tree q.succ.castSucc := happendTree
              _ = ett.series.data.tree j.succ.castSucc := by
                    rw [hj, hqSucc]
          have hseriesColorProperties : ∀ i : Fin (ett.rounds + 1),
              IsProperEdgeColoring G (finalSeries.data.coloring i) ∧
                IsOneEdgeUncolored (finalSeries.data.coloring i) e0 := by
            intro i
            by_cases hi : i.val < ett.rounds
            · have hraw : rawDataIndex i = zeroLast.castSucc := by
                apply Fin.ext
                have hiZero : i.val = 0 := by
                  have hr := hroundOne
                  omega
                exact hiZero
              have hcolor : finalSeries.data.coloring i = sigmaPrev := by
                calc
                  finalSeries.data.coloring i =
                      extendedSeries.data.coloring (rawDataIndex i) := by
                        exact castSeriesColoring hroundsEq extendedSeries i
                  _ = appendedData.coloring (rawDataIndex i) := by
                        rw [hextendedData]
                  _ = appendedData.coloring zeroLast.castSucc := by rw [hraw]
                  _ = sigmaPrev := happendColor
              rw [hcolor]
              exact ⟨hsigmaPrevProper, hsigmaPrevOne⟩
            · have hilast : i = Fin.last ett.rounds := by
                apply Fin.ext
                have hibound := i.isLt
                simp
                omega
              subst i
              rw [hfinalColor]
              exact ⟨hsigmaProper, hsigmaOne⟩
          have hseriesStable : ∀ j : Fin ett.rounds,
              StableColoring (ett.series.data.tree j.succ.castSucc)
                (TashkinovStoredColors ett.series.data j.succ)
                (ett.series.data.coloring j.succ)
                (finalSeries.data.coloring j.succ) := by
            intro j
            have hj : j.succ = Fin.last ett.rounds := by
              apply Fin.ext
              have hjbound := j.isLt
              simp
              have hr := hroundOne
              omega
            rw [hj, hfinalColor]
            exact hsigmaStable
          let replacementETT : ExtendedTashkinovTree G k e0 prefixInput
              Tstar sigma := {
            rounds := ett.rounds
            roundsPositive := ett.roundsPositive
            series := finalSeries
            abovePenultimate := by rw [hpenultimateTree]; exact hTnTstar
            strictAbovePenultimate := by rw [hpenultimateTree]; exact hstrict
            belowFinal := by rw [hfinalTree]; exact hTstarClosure
            generatingColoring := hfinalColor.symm }
          refine ⟨{
            replacementInput := prefixInput
            replacementSeries := finalSeries
            replacementETT := replacementETT
            rungAgreement := rfl
            seriesPresentation := by dsimp [replacementETT]; rfl
            finalGeneratingColoring := hfinalColor.symm
            ladderTreesAgree := hseriesTreeAgree
            storedColorsAgree := fun i => (hseriesDataAgree i).1
            connectingEdgesAgree := fun i => (hseriesDataAgree i).2.1
            extensionKindsAgree := fun i => (hseriesDataAgree i).2.2
            replacementProper := fun i => (hseriesColorProperties i).1
            replacementOneUncolored := fun i => (hseriesColorProperties i).2
            replacementStable := hseriesStable }⟩
      · rcases hpositivePrefix with ⟨hroundLarge, originalPrefix, hr,
            hprefixMP, hprefixTrees, hprefixData, corr, hcorrFinalTree,
            hcorrFinalColor, hcorrMP⟩
        let replacementLast : Fin (originalPrefix.rounds + 1) :=
          Fin.last originalPrefix.rounds
        have horiginalPositive : 0 < originalPrefix.rounds := by
          rw [hr]
          omega
        let previousReplacement : Fin originalPrefix.rounds :=
          ⟨originalPrefix.rounds - 1,
            Nat.sub_lt horiginalPositive (by omega)⟩
        have hpreviousSucc : previousReplacement.succ = replacementLast := by
          apply Fin.ext
          simp [previousReplacement, replacementLast]
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
        have htreeMissingEq : TreeMissingColors
              (corr.replacementSeries.data.coloring replacementLast)
              (corr.replacementSeries.data.tree replacementLast.castSucc) =
            TreeMissingColors
              (originalPrefix.series.data.coloring replacementLast)
              (originalPrefix.series.data.tree replacementLast.castSucc) := by
          have hstable := corr.replacementStable previousReplacement
          rw [hpreviousSucc] at hstable
          have htree := corr.ladderTreesAgree previousReplacement
          rw [hpreviousSucc] at htree
          rw [htree]
          ext c
          simp only [TreeMissingColors, Finset.mem_biUnion]
          constructor
          · rintro ⟨v, hv, hc⟩
            exact ⟨v, hv, (hstable.2 v hv).symm ▸ hc⟩
          · rintro ⟨v, hv, hc⟩
            exact ⟨v, hv, hstable.2 v hv ▸ hc⟩
        have hreplacementStored : TashkinovStoredColors
              corr.replacementSeries.data replacementLast =
            TashkinovStoredColors ett.series.data q.castSucc := by
          have hcorrStored : TashkinovStoredColors
                corr.replacementSeries.data replacementLast =
              TashkinovStoredColors originalPrefix.series.data
                replacementLast := by
            unfold TashkinovStoredColors
            have hnonzero : replacementLast.val ≠ 0 := by
              simp [replacementLast]
              exact Nat.ne_of_gt horiginalPositive
            rw [if_neg hnonzero, if_neg hnonzero]
            ext c
            simp only [Finset.mem_sdiff, Finset.mem_biUnion]
            constructor
            · rintro ⟨⟨j, hj, hc⟩, hn⟩
              refine ⟨⟨j, hj, ?_⟩, ?_⟩
              · by_cases hle : j.val ≤ replacementLast.val
                · simp only [if_pos hle] at hc ⊢
                  simpa [corr.storedColorsAgree j] using hc
                · simp only [if_neg hle] at hc ⊢
                  exact hc
              · rw [htreeMissingEq] at hn
                exact hn
            · rintro ⟨⟨j, hj, hc⟩, hn⟩
              refine ⟨⟨j, hj, ?_⟩, ?_⟩
              · by_cases hle : j.val ≤ replacementLast.val
                · simp only [if_pos hle] at hc ⊢
                  simpa [corr.storedColorsAgree j] using hc
                · simp only [if_neg hle] at hc ⊢
                  exact hc
              · rw [← htreeMissingEq] at hn
                exact hn
          calc
            TashkinovStoredColors corr.replacementSeries.data replacementLast =
                TashkinovStoredColors originalPrefix.series.data
                  replacementLast := hcorrStored
            _ = TashkinovStoredColors ett.series.data
                  (Fin.castLE (by omega) replacementLast) :=
              (hprefixData replacementLast).2.2.2.2
            _ = TashkinovStoredColors ett.series.data q.castSucc := by
              rw [hlastMap]
        let replacementChoice : MaximumDefectiveChoice G e0
            (corr.replacementSeries.data.tree replacementLast.succ)
            (TashkinovStoredColors corr.replacementSeries.data replacementLast)
            (corr.replacementSeries.data.coloring replacementLast) := {
          selected := sigmaPrev
          selectedProper := hsigmaPrevProper
          selectedOneUncolored := hsigmaPrevOne
          selectedStable := by
            rw [hreplacementCurrentTree, hreplacementStored, hcorrFinalColor]
            exact newChoice.selectedStable
          vertex := choice.vertex
          vertexDefective := by
            rw [hreplacementCurrentTree]
            exact newChoice.vertexDefective
          maximal := by
            intro pi w hpiProper hpiOne hpiStable hw
            rw [hreplacementCurrentTree, hreplacementStored, hcorrFinalColor]
              at hpiStable
            rw [hreplacementCurrentTree] at hw ⊢
            exact newChoice.maximal pi w hpiProper hpiOne hpiStable hw
          edge := choice.edge
          edgeDefective := by
            rw [hreplacementCurrentTree]
            exact newChoice.edgeDefective
          edgeIncident := choice.edgeIncident
          otherEndpoint := choice.otherEndpoint
          otherOutside := by
            rw [hreplacementCurrentTree]
            exact newChoice.otherOutside
          edgeEnds := choice.edgeEnds
          color := choice.color
          edgeColor := newChoice.edgeColor }
        have hnoRevisitingReplacement : ¬ Nonempty
            (RevisitingExtensionCertificate corr.replacementSeries.data
              replacementLast) := by
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
                  have hswapGraph : TwoColorIncidenceGraph G
                        (TwoColorComponentSwap G oldSecond oldGamma
                          oldChoice.color (Sum.inl oldChoice.vertex))
                        oldGamma oldChoice.color =
                      TwoColorIncidenceGraph G oldSecond oldGamma
                        oldChoice.color := by
                    ext x y
                    cases x with
                    | inl v =>
                        cases y with
                        | inl w => simp [TwoColorIncidenceGraph]
                        | inr f =>
                            by_cases hf : Sum.inr f ∈ TwoColorComponent G
                                oldSecond oldGamma oldChoice.color
                                (Sum.inl oldChoice.vertex)
                            · by_cases hfg : oldSecond f = some oldGamma
                              · simp [TwoColorIncidenceGraph,
                                  TwoColorComponentSwap, hf, hfg]
                              · by_cases hfd : oldSecond f =
                                    some oldChoice.color
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
                                oldSecond oldGamma oldChoice.color
                                (Sum.inl oldChoice.vertex)
                            · by_cases hfg : oldSecond f = some oldGamma
                              · simp [TwoColorIncidenceGraph,
                                  TwoColorComponentSwap, hf, hfg]
                              · by_cases hfd : oldSecond f =
                                    some oldChoice.color
                                · simp [TwoColorIncidenceGraph,
                                    TwoColorComponentSwap, hf, hfg, hfd]
                                · simp [TwoColorIncidenceGraph,
                                    TwoColorComponentSwap, hf, hfg, hfd]
                            · simp [TwoColorIncidenceGraph,
                                TwoColorComponentSwap, hf]
                        | inr g => simp [TwoColorIncidenceGraph]
                  have horiginalExitGraph : TwoColorIncidenceGraph G
                        (ett.series.data.coloring q.castSucc)
                        available.gamma available.delta =
                      TwoColorIncidenceGraph G oldSecond oldGamma
                        oldChoice.color := by
                    calc
                      TwoColorIncidenceGraph G
                          (ett.series.data.coloring q.castSucc)
                          available.gamma available.delta =
                        TwoColorIncidenceGraph G
                          (originalPrefix.series.data.coloring oldi.succ)
                          available.gamma available.delta :=
                            congrArg (fun phi => TwoColorIncidenceGraph G phi
                              available.gamma available.delta)
                              holdPostOriginal.symm
                      _ = TwoColorIncidenceGraph G
                          (TwoColorComponentSwap G oldSecond oldGamma
                            oldChoice.color (Sum.inl oldChoice.vertex))
                          available.gamma available.delta :=
                            congrArg (fun phi => TwoColorIncidenceGraph G phi
                              available.gamma available.delta)
                              oldCurrentColoring
                      _ = TwoColorIncidenceGraph G
                          (TwoColorComponentSwap G oldSecond oldGamma
                            oldChoice.color (Sum.inl oldChoice.vertex))
                          oldGamma oldChoice.color := by
                            rw [holdGammaAvailable, holdDeltaAvailable]
                      _ = TwoColorIncidenceGraph G oldSecond oldGamma
                          oldChoice.color := hswapGraph
                  have holdGammaSecond : oldGamma ∈ MissingColors G oldSecond
                      oldChoice.vertex := by
                    rw [oldSecondStable.2 oldChoice.vertex
                      oldChoice.vertexDefective.1]
                    exact oldGammaRule.1
                  have hcomponentOnly := TreeExitComponentMeetsTreeOnlyAtExit
                    (originalPrefix.series.data.tree oldi.succ.castSucc)
                    oldSecond oldGamma oldChoice.color oldChoice.vertex
                    oldSecondProper holdGammaSecond oldExit
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
                        TwoColorComponent G oldSecond oldGamma oldChoice.color
                          (Sum.inl oldChoice.vertex) := by
                      unfold TwoColorComponent at hreturnExitOriginal ⊢
                      rw [← horiginalExitGraph]
                      exact hreturnExitOriginal
                    exact hreturnNeOld
                      ((hcomponentOnly available.returnVertex
                        (by simpa only [holdIndex] using
                          hreturnInOldEarlier)).mp hreturnExitSecond)
                  have hQMeetsFinal : ∃ v ∈ TreeSequenceVertexSet
                      (originalPrefix.series.data.tree
                        (Fin.last (originalPrefix.rounds + 1))),
                      Sum.inl v ∈ TwoColorComponent G
                        (ett.series.data.coloring q.castSucc)
                        available.gamma available.delta
                        (Sum.inr available.edge) :=
                    ⟨available.returnVertex, hreturnInFinal, hreturnInQ⟩
                  have horiginalRoundsLess : originalPrefix.rounds <
                      ett.rounds := by
                    rw [hr]
                    omega
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
                  have hinterchangeLower := hlowerPackage.2.1
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
        have hnewAlternativeReplacement : ∀ pi : PartialEdgeColoring E k,
            IsProperEdgeColoring G pi → IsOneEdgeUncolored pi e0 →
            StableColoring
              (corr.replacementSeries.data.tree replacementLast.succ)
              (insert replacementChoice.color
                (TashkinovStoredColors corr.replacementSeries.data
                  replacementLast)) replacementChoice.selected pi →
            Disjoint (MissingColors G pi replacementChoice.otherEndpoint)
              (TreeMissingColors pi
                (corr.replacementSeries.data.tree replacementLast.succ)) := by
          intro pi hpiProper hpiOne hpiStable
          have hpiStable' := hpiStable
          change StableColoring
            (corr.replacementSeries.data.tree replacementLast.succ)
            (insert choice.color
              (TashkinovStoredColors corr.replacementSeries.data
                replacementLast)) sigmaPrev pi at hpiStable'
          rw [hreplacementCurrentTree, hreplacementStored] at hpiStable'
          have hresult := hnewAlternative pi hpiProper hpiOne
            (by simpa [replacementChoice, newChoice] using hpiStable')
          change Disjoint (MissingColors G pi choice.otherEndpoint)
            (TreeMissingColors pi
              (corr.replacementSeries.data.tree replacementLast.succ))
          rw [hreplacementCurrentTree]
          simpa [replacementChoice, newChoice] using hresult
        rcases heligible with hparallel | hsimple
        · have hbad := hparallel.1.symm.trans
            (by simpa [hqSucc] using hseKind)
          cases hbad
        · rcases hsimple with ⟨hkind, fstar, seed, hfinalEdges,
              hadjoin, hroute⟩
          have hfstar : fstar = choice.edge := by
            apply Finset.mem_singleton.mp
            rw [← currentEdges, hqSucc, hfinalEdges]
            exact Finset.mem_singleton_self fstar
          have hrouteClosure : TashkinovAugmentationSequence sigma seed
              closureTree := hroute.trans hclosure.1
          have hseedClosure : TashkinovClosure sigma seed closureTree :=
            ⟨hrouteClosure, hclosure.2⟩
          let newStored : Finset (Fin k) := {choice.color}
          let newEdges : Finset E := {choice.edge}
          let newKind : Option TashkinovExtensionKind :=
            some TashkinovExtensionKind.SE
          let newVertex : Option V := some choice.vertex
          let newOutside : Option V := some choice.otherEndpoint
          let newDelta : Option (Fin k) := some choice.color
          let newGamma : Option (Fin k) := none
          let appendedData := TashkinovSeriesDataAppend
            corr.replacementSeries.data closureTree sigma newStored newEdges
            newKind newVertex newOutside newDelta newGamma
          have happendedTree :
              appendedData.tree replacementLast.succ.castSucc =
                corr.replacementSeries.data.tree replacementLast.succ := by
            simp only [appendedData, TashkinovSeriesDataAppend]
            exact Fin.lastCases_castSucc replacementLast.succ
          have happendedStored : TashkinovStoredColors appendedData
                replacementLast.castSucc =
              TashkinovStoredColors corr.replacementSeries.data
                replacementLast :=
            TashkinovStoredColorsAppend corr.replacementSeries.data
              closureTree sigma newStored newEdges newKind newVertex newOutside
              newDelta newGamma replacementLast
          have happendedColor : appendedData.coloring
                replacementLast.castSucc =
              corr.replacementSeries.data.coloring replacementLast := by
            simp [appendedData, TashkinovSeriesDataAppend]
          let appendedChoice : MaximumDefectiveChoice G e0
              (appendedData.tree replacementLast.succ.castSucc)
              (TashkinovStoredColors appendedData replacementLast.castSucc)
              (appendedData.coloring replacementLast.castSucc) := {
            selected := replacementChoice.selected
            selectedProper := replacementChoice.selectedProper
            selectedOneUncolored := replacementChoice.selectedOneUncolored
            selectedStable := by
              rw [happendedTree, happendedStored, happendedColor]
              exact replacementChoice.selectedStable
            vertex := replacementChoice.vertex
            vertexDefective := by
              rw [happendedTree]
              exact replacementChoice.vertexDefective
            maximal := by
              intro pi w hpiProper hpiOne hpiStable hw
              rw [happendedTree, happendedStored, happendedColor] at hpiStable
              rw [happendedTree] at hw ⊢
              exact replacementChoice.maximal pi w hpiProper hpiOne hpiStable hw
            edge := replacementChoice.edge
            edgeDefective := by
              rw [happendedTree]
              exact replacementChoice.edgeDefective
            edgeIncident := replacementChoice.edgeIncident
            otherEndpoint := replacementChoice.otherEndpoint
            otherOutside := by
              rw [happendedTree]
              exact replacementChoice.otherOutside
            edgeEnds := replacementChoice.edgeEnds
            color := replacementChoice.color
            edgeColor := replacementChoice.edgeColor }
          have hnoRevisitingAppended : ¬ Nonempty
              (RevisitingExtensionCertificate appendedData
                replacementLast.castSucc) := by
            rintro ⟨cert⟩
            obtain ⟨oldCert, -, -, -, -, -⟩ :=
              (RevisitingExtensionCertificateAppend
                corr.replacementSeries.data closureTree sigma newStored
                newEdges newKind newVertex newOutside newDelta newGamma
                replacementLast).1 cert
            exact hnoRevisitingReplacement ⟨oldCert⟩
          have hnewAlternativeAppended : ∀ pi : PartialEdgeColoring E k,
              IsProperEdgeColoring G pi → IsOneEdgeUncolored pi e0 →
              StableColoring
                (appendedData.tree replacementLast.succ.castSucc)
                (insert appendedChoice.color
                  (TashkinovStoredColors appendedData
                    replacementLast.castSucc)) appendedChoice.selected pi →
              Disjoint
                (MissingColors G pi appendedChoice.otherEndpoint)
                (TreeMissingColors pi
                  (appendedData.tree replacementLast.succ.castSucc)) := by
            intro pi hpiProper hpiOne hpiStable
            have hpiStable' := hpiStable
            change StableColoring
              (appendedData.tree replacementLast.succ.castSucc)
              (insert replacementChoice.color
                (TashkinovStoredColors appendedData
                  replacementLast.castSucc)) replacementChoice.selected pi
                at hpiStable'
            rw [happendedTree, happendedStored] at hpiStable'
            have hresult := hnewAlternativeReplacement pi hpiProper hpiOne
              hpiStable'
            change Disjoint
              (MissingColors G pi replacementChoice.otherEndpoint)
              (TreeMissingColors pi
                (appendedData.tree replacementLast.succ.castSucc))
            rw [happendedTree]
            exact hresult
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
            rw [← hlast]
            apply TashkinovSeriesStep.SE (i := replacementLast)
              (choice := appendedChoice) (adjoined := seed)
            · rw [happendedColor, hcorrFinalColor]
              exact hsigmaPrevProper
            · rw [happendedColor, hcorrFinalColor]
              exact hsigmaPrevOne
            · rw [happendedColor, happendedTree, hcorrFinalColor,
                hreplacementCurrentTree]
              exact hclosedPrev
            · rw [happendedColor, happendedTree, hcorrFinalColor,
                hreplacementCurrentTree]
              exact hnotStrongPrev
            · exact hnoRevisitingAppended
            · exact hnewAlternativeAppended
            · simp [appendedChoice, replacementChoice, appendedData,
                TashkinovSeriesDataAppend,
                hlast, hsigmaPrevSigma]
            · simp [appendedChoice, replacementChoice, appendedData,
                TashkinovSeriesDataAppend, newStored, hlast]
            · simp [appendedChoice, replacementChoice, appendedData,
                TashkinovSeriesDataAppend, newEdges, hlast]
            · simp [appendedData, TashkinovSeriesDataAppend, newKind, hlast]
            · simp [appendedChoice, replacementChoice, appendedData,
                TashkinovSeriesDataAppend, newVertex, hlast]
            · simp [appendedChoice, replacementChoice, appendedData,
                TashkinovSeriesDataAppend, newOutside, hlast]
            · simp [appendedChoice, replacementChoice, appendedData,
                TashkinovSeriesDataAppend, newDelta, hlast]
            · simp [appendedData, TashkinovSeriesDataAppend, newGamma, hlast]
            · change TreeSequenceAdjoinEdge
                (appendedData.tree replacementLast.succ.castSucc)
                choice.edge seed
              rw [happendedTree, hreplacementCurrentTree]
              simpa [appendedChoice, replacementChoice, hqSucc, hfstar] using
                hadjoin
            · simpa [appendedData, TashkinovSeriesDataAppend, hlast] using
                hseedClosure
            · change TreeSequenceInitialSegment
                (appendedData.tree replacementLast.succ.castSucc)
                (appendedData.tree (Fin.last (originalPrefix.rounds + 2)))
              rw [happendedTree, hreplacementCurrentTree]
              simpa [appendedData, TashkinovSeriesDataAppend, hqSucc] using
                hTnClosure
            · change (appendedData.tree replacementLast.succ.castSucc).length <
                (appendedData.tree
                  (Fin.last (originalPrefix.rounds + 2))).length
              rw [happendedTree, hreplacementCurrentTree]
              simpa [appendedData, TashkinovSeriesDataAppend, hqSucc] using
                hstrictClosure
          obtain ⟨extendedSeries, hextendedData⟩ :=
            TashkinovSeriesAppend G k originalPrefix.rounds e0
              corr.replacementInput corr.replacementSeries closureTree sigma
              newStored newEdges newKind newVertex newOutside newDelta newGamma
              lastStep
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
                    (Fin.last ett.rounds).castSucc := by
                exact hreplacementCurrentTree.trans
                  (congrArg ett.series.data.tree
                    (congrArg Fin.castSucc hqSucc))
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
                  _ = {choice.color} := rfl
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
                    _ = {choice.edge} := rfl
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
                    _ = some TashkinovExtensionKind.SE := rfl
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
  | PE i previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternativeFails
      gamma gammaRule secondStable secondStableProper secondStableOneUncolored
      secondStableRelation exitWitness currentColoring currentProper
      currentOneUncolored currentStored currentEdges currentKind currentVertex
      currentOutside currentDelta currentGamma closedExtension orderedExtension
      strictExtension =>
      have hi : i = q := by
        apply Fin.ext
        have hv : ett.rounds = i.val + 1 := by
          simpa using congrArg Fin.val htarget
        change i.val = ett.rounds - 1
        omega
      subst i
      have hpeKind : ett.series.data.kind q.succ =
          some TashkinovExtensionKind.PE := by
        simpa [htarget] using currentKind
      have hprefix := TdReplacementPrefixExact G k e0 input T generating ett
        hMP hpositive hlower sigma hsigmaProper hsigmaOne
        (by simpa [hqSucc] using hsigmaStable)
      obtain ⟨sigmaPrev, hsigmaPrevProper, hsigmaPrevOne,
          hsigmaPrevStable, hsigmaPrevEq, hparallelPrev, hprefixCases⟩ := hprefix
      have hsigmaPrevStableQ : StableColoring
          (ett.series.data.tree q.succ.castSucc)
          (TashkinovStoredColors ett.series.data q.castSucc)
          (ett.series.data.coloring q.castSucc) sigmaPrev := by
        simpa [hqSucc, hqCast] using hsigmaPrevStable
      have hchoiceVertex : choice.vertex ∈ TreeSequenceVertexSet
          (ett.series.data.tree q.succ.castSucc) :=
        choice.vertexDefective.1
      have hcomponent : ∀ w,
          w ∈ TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc) →
          (Sum.inl w ∈ TwoColorComponent G sigma gamma choice.color
              (Sum.inl choice.vertex) ↔ w = choice.vertex) := by
        have hbase := ExtensionBase G k e0 input T generating ett hMP hpositive
          hlower choice.vertex gamma choice.color
          (by simpa [hqSucc] using hpeKind)
          (by simpa [hqSucc] using currentVertex)
          (by simpa [hqSucc] using currentGamma)
          (by simpa [hqSucc] using currentDelta)
          sigma hsigmaProper hsigmaOne
          (by simpa [hqSucc] using hsigmaStable)
        simpa [hqSucc] using hbase
      obtain ⟨parallelVertex, parallelGamma, parallelDelta,
          hparallelVertex, hparallelGamma, hparallelDelta,
          hsigmaPrevSwitch⟩ := hparallelPrev (by simpa [hqSucc] using hpeKind)
      have hparallelVertexEq : parallelVertex = choice.vertex := by
        apply Option.some.inj
        exact hparallelVertex.symm.trans (by simpa [hqSucc] using currentVertex)
      have hparallelGammaEq : parallelGamma = gamma := by
        apply Option.some.inj
        exact hparallelGamma.symm.trans (by simpa [hqSucc] using currentGamma)
      have hparallelDeltaEq : parallelDelta = choice.color := by
        apply Option.some.inj
        exact hparallelDelta.symm.trans (by simpa [hqSucc] using currentDelta)
      subst parallelVertex
      subst parallelGamma
      subst parallelDelta
      have hsigmaPrevFormula : sigmaPrev =
          TwoColorComponentSwap G sigma gamma choice.color
            (Sum.inl choice.vertex) := hsigmaPrevSwitch
      have hsigmaPrevEnlarged : StableColoring
          (ett.series.data.tree q.succ.castSucc)
          (insert choice.color
            (TashkinovStoredColors ett.series.data q.castSucc))
          choice.selected sigmaPrev := by
        have hmissing : gamma ∈ MissingColors G secondStable choice.vertex := by
          exact (secondStableRelation.2 choice.vertex choice.vertexDefective.1).symm ▸ gammaRule.1
        have hdegree : ∀ w, gamma ∈ MissingColors G secondStable w ∨
            choice.color ∈ MissingColors G secondStable w →
            (TwoColorIncidenceGraph G secondStable gamma choice.color).degree
              (Sum.inl w) ≤ 1 := by
          intro w hw
          rw [← SimpleGraph.card_neighborFinset_eq_degree]
          apply Finset.card_le_one.mpr
          intro y hy z hz
          simp only [SimpleGraph.mem_neighborFinset] at hy hz
          cases y with
          | inl y => simp [TwoColorIncidenceGraph] at hy
          | inr e =>
            cases z with
            | inl z => simp [TwoColorIncidenceGraph] at hz
            | inr f =>
              simp only [TwoColorIncidenceGraph] at hy hz
              rcases hw with hw | hw
              · have he : secondStable e = some choice.color :=
                  hy.2.resolve_left (by
                    intro he
                    apply (by simpa [MissingColors] using hw)
                    simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
                    exact ⟨e, hy.1, he⟩)
                have hf : secondStable f = some choice.color :=
                  hz.2.resolve_left (by
                    intro hf
                    apply (by simpa [MissingColors] using hw)
                    simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
                    exact ⟨f, hz.1, hf⟩)
                by_cases h : e = f
                · exact congrArg Sum.inr h
                · exact (secondStableProper h ⟨w, hy.1, hz.1⟩ he hf).elim
              · have he : secondStable e = some gamma :=
                  hy.2.resolve_right (by
                    intro he
                    apply (by simpa [MissingColors] using hw)
                    simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
                    exact ⟨e, hy.1, he⟩)
                have hf : secondStable f = some gamma :=
                  hz.2.resolve_right (by
                    intro hf
                    apply (by simpa [MissingColors] using hw)
                    simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
                    exact ⟨f, hz.1, hf⟩)
                by_cases h : e = f
                · exact congrArg Sum.inr h
                · exact (secondStableProper h ⟨w, hy.1, hz.1⟩ he hf).elim
        rcases exitWitness with ⟨u, path, pathData⟩
        rcases pathData with ⟨pathIs, pathLen, uOut, endTree, endOnly⟩
        have hdegreeBound : ∀ x, @SimpleGraph.degree _
            (TwoColorIncidenceGraph G secondStable gamma choice.color) x
            (Fintype.ofFinite _) ≤ 2 := by
          intro x
          exact TwoColorIncidenceDegreeAtMostTwo G secondStable gamma choice.color
            secondStableProper x
        have huDegree := hdegree u endOnly.1
        have hclosed : ∀ x, x ∈ path.support → ∀ y,
            (TwoColorIncidenceGraph G secondStable gamma choice.color).Adj x y →
            y ∈ path.support := by
          intro x hx y hxy
          obtain ⟨n, hn, hnle⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hx
          by_cases hn0 : n = 0
          · subst n
            have hx0 : x = Sum.inl u := by simpa using hn.symm
            let graph := TwoColorIncidenceGraph G secondStable gamma choice.color
            letI : Fintype (graph.neighborSet x) := Fintype.ofFinite _
            have card : Fintype.card (graph.neighborSet x) ≤ 1 := by
              rw [SimpleGraph.card_neighborSet_eq_degree]
              convert huDegree using 1
              cases hx0
              exact congrArg (fun z => @SimpleGraph.degree _ graph (Sum.inl u) z)
                (Subsingleton.elim _ _)
            have hy' : y ∈ graph.neighborSet x := by simpa [graph, SimpleGraph.mem_neighborSet] using hxy
            have hn' : path.getVert 1 ∈ graph.neighborSet x := by
              simpa [graph, hx0, SimpleGraph.mem_neighborSet] using
                path.adj_getVert_succ (show 0 < path.length by omega)
            have heq := Fintype.card_le_one_iff.mp card ⟨y, hy'⟩ ⟨path.getVert 1, hn'⟩
            have hey : y = path.getVert 1 := congrArg Subtype.val heq
            rw [hey]
            exact path.getVert_mem_support 1
          by_cases hlast : n = path.length
          · have hx1 : x = Sum.inl choice.vertex := by
              rw [← hn, pathIs.getVert_eq_end_iff hnle]
              exact hlast
            let graph := TwoColorIncidenceGraph G secondStable gamma choice.color
            letI : Fintype (graph.neighborSet x) := Fintype.ofFinite _
            have card : Fintype.card (graph.neighborSet x) ≤ 1 := by
              rw [SimpleGraph.card_neighborSet_eq_degree]
              convert hdegree choice.vertex (Or.inl hmissing) using 1
              cases hx1
              exact congrArg (fun z => @SimpleGraph.degree _ graph (Sum.inl choice.vertex) z)
                (Subsingleton.elim _ _)
            have hy' : y ∈ graph.neighborSet x := by simpa [graph, SimpleGraph.mem_neighborSet] using hxy
            have hp : path.getVert (path.length - 1) ∈ graph.neighborSet x := by
              have ha : graph.Adj (Sum.inl choice.vertex) (path.getVert (path.length - 1)) := by
                simpa [graph, show path.length - 1 + 1 = path.length by omega] using
                  (path.adj_getVert_succ (show path.length - 1 < path.length by omega)).symm
              simpa [hx1, SimpleGraph.mem_neighborSet] using ha
            have heq := Fintype.card_le_one_iff.mp card ⟨y, hy'⟩ ⟨path.getVert (path.length - 1), hp⟩
            have hey : y = path.getVert (path.length - 1) := congrArg Subtype.val heq
            rw [hey]
            exact path.getVert_mem_support _
          have hl : (TwoColorIncidenceGraph G secondStable gamma choice.color).Adj
              (path.getVert n) (path.getVert (n - 1)) := by
            rw [← show n - 1 + 1 = n by omega]
            exact (path.adj_getVert_succ (by omega)).symm
          have hnlt : n < path.length := lt_of_le_of_ne hnle hlast
          have hr := path.adj_getVert_succ hnlt
          by_contra hyout
          rw [← hn] at hxy
          have hnl : path.getVert (n - 1) ≠ y := by
            intro h; apply hyout; rw [← h]; exact path.getVert_mem_support _
          have hnr : path.getVert (n + 1) ≠ y := by
            intro h; apply hyout; rw [← h]; exact path.getVert_mem_support _
          have hnp : path.getVert (n - 1) ≠ path.getVert (n + 1) := by
            intro h
            have hi := pathIs.getVert_injOn (show n - 1 ≤ path.length by omega)
              (show n + 1 ≤ path.length by omega) h
            omega
          let graph := TwoColorIncidenceGraph G secondStable gamma choice.color
          letI : Fintype (graph.neighborSet (path.getVert n)) := Fintype.ofFinite _
          have three : 3 ≤ graph.degree (path.getVert n) := by
            rw [← SimpleGraph.card_neighborFinset_eq_degree]
            let s : Finset _ := {y, path.getVert (n - 1), path.getVert (n + 1)}
            have hs : s ⊆ graph.neighborFinset (path.getVert n) := by
              intro t ht
              simp only [s, Finset.mem_insert, Finset.mem_singleton] at ht
              rcases ht with rfl | rfl | rfl
              · simpa [graph, SimpleGraph.mem_neighborFinset] using hxy
              · simpa [graph, SimpleGraph.mem_neighborFinset] using hl
              · simpa [graph, SimpleGraph.mem_neighborFinset] using hr
            have hc : 3 ≤ s.card := by simp [s, hnl, hnr, hnp, hnl.symm, hnr.symm, hnp.symm]
            exact hc.trans (Finset.card_le_card hs)
          have upper : graph.degree (path.getVert n) ≤ 2 := hdegreeBound (path.getVert n)
          omega
        have hpathComponent : ∀ y,
            y ∈ TwoColorComponent G secondStable gamma choice.color
              (Sum.inl choice.vertex) → y ∈ path.support := by
          intro y hy
          let graph := TwoColorIncidenceGraph G secondStable gamma choice.color
          have reach : graph.Reachable (Sum.inl choice.vertex) y := by
            change graph.connectedComponentMk y = graph.connectedComponentMk (Sum.inl choice.vertex) at hy
            exact SimpleGraph.ConnectedComponent.eq.mp hy |>.symm
          exact reach.mem_subgraphVerts (H := (⊤ : graph.Subgraph).induce {x | x ∈ path.support})
            (fun x hx z hadj => ⟨by simpa using hx, hclosed x (by simpa using hx) z hadj, hadj⟩)
            (by simpa using path.getVert_mem_support path.length)
        have hcompEdge : ∀ e,
            Sum.inr e ∈ TwoColorComponent G secondStable gamma choice.color
              (Sum.inl choice.vertex) →
            secondStable e = some gamma ∨ secondStable e = some choice.color := by
          intro e he
          have hs : Sum.inr e ∈
              (TwoColorIncidenceGraph G secondStable gamma choice.color).support := by
            apply SimpleGraph.mem_support_of_reachable
              (G := TwoColorIncidenceGraph G secondStable gamma choice.color)
              (u := Sum.inr e) (v := Sum.inl choice.vertex) (by simp)
            exact SimpleGraph.ConnectedComponent.eq.mp he
          obtain ⟨r, hr⟩ :=
            (TwoColorIncidenceGraph G secondStable gamma choice.color).mem_support.mp hs
          cases r with
          | inl x => exact hr.2
          | inr x => simpa [TwoColorIncidenceGraph] using hr
        have hchoiceSecond : secondStable choice.edge = some choice.color := by
          have heq := secondStableRelation.1 choice.edge
            ⟨choice.vertex, choice.vertexDefective.1, choice.edgeIncident⟩
            ⟨choice.color, Finset.mem_union.mpr (Or.inr (Finset.mem_insert_self _ _)),
              choice.edgeColor⟩
          exact heq.trans choice.edgeColor
        have hneq : gamma ≠ choice.color := by
          intro heq
          have hp : gamma ∈ PresentColors G secondStable choice.vertex := by
            simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨choice.edge, choice.edgeIncident, heq ▸ hchoiceSecond⟩
          have hpnot : gamma ∉ PresentColors G secondStable choice.vertex := by
            simpa [MissingColors] using hmissing
          exact hpnot hp
        have hfcomponent : Sum.inr choice.edge ∈
            TwoColorComponent G secondStable gamma choice.color
              (Sum.inl choice.vertex) := by
          apply SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
          simp [TwoColorIncidenceGraph, choice.edgeIncident, hchoiceSecond]
        have htreeEdge : ∀ e,
            TreeIncidentEdge (ett.series.data.tree q.succ.castSucc) e →
            Sum.inr e ∈ TwoColorComponent G secondStable gamma choice.color
              (Sum.inl choice.vertex) → e = choice.edge := by
          intro e heT heC
          rcases heT with ⟨w, hw, hwe⟩
          have hwC : Sum.inl w ∈ TwoColorComponent G secondStable gamma choice.color
              (Sum.inl choice.vertex) := by
            have hadj : (TwoColorIncidenceGraph G secondStable gamma choice.color).Adj
                (Sum.inl w) (Sum.inr e) := by
              simp [TwoColorIncidenceGraph, hwe, hcompEdge e heC]
            change (TwoColorIncidenceGraph G secondStable gamma choice.color).connectedComponentMk
                (Sum.inl w) = _
            exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj).trans heC
          have hwv : w = choice.vertex := (endOnly.2 w hw).mp (hpathComponent _ hwC)
          subst w
          rcases hcompEdge e heC with hec | hec
          · have hnot : secondStable e ≠ some gamma := by
              intro heq
              have hp : gamma ∈ PresentColors G secondStable choice.vertex := by
                simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
                exact ⟨e, hwe, heq⟩
              have hm : gamma ∉ PresentColors G secondStable choice.vertex := by
                simpa [MissingColors] using hmissing
              exact hm hp
            exact (hnot hec).elim
          · by_contra hne
            exact (secondStableProper hne ⟨choice.vertex, hwe, choice.edgeIncident⟩ hec
              hchoiceSecond).elim
        have hsigmaEdge : ∀ e,
            TreeIncidentEdge (ett.series.data.tree q.succ.castSucc) e →
            Sum.inr e ∈ TwoColorComponent G sigma gamma choice.color
              (Sum.inl choice.vertex) → e = choice.edge := by
          intro e heT heC
          rcases heT with ⟨w, hw, hwe⟩
          have hgamma : sigma choice.edge = some gamma := by
            have hsc := hsigmaStableQ.1 choice.edge
              ⟨choice.vertex, choice.vertexDefective.1, choice.edgeIncident⟩
            have hctrl : ∃ c ∈ TreeMissingColors (ett.series.data.coloring q.succ)
                (ett.series.data.tree q.succ.castSucc) ∪ TashkinovStoredColors ett.series.data q.succ,
                ett.series.data.coloring q.succ choice.edge = some c := by
              refine ⟨gamma, ?_, ?_⟩
              · by_cases hm : gamma ∈ TreeMissingColors (ett.series.data.coloring q.succ)
                    (ett.series.data.tree q.succ.castSucc)
                · exact Finset.mem_union.mpr (Or.inl hm)
                · apply Finset.mem_union.mpr
                  right
                  unfold TashkinovStoredColors
                  rw [if_neg (by simp)]
                  simp only [Finset.mem_sdiff, Finset.mem_biUnion]
                  constructor
                  · refine ⟨q.succ, ?_, ?_⟩
                    · simp
                    · simpa [currentStored]
                  · simpa using hm
              · rw [currentColoring]
                simp [TwoColorComponentSwap, hfcomponent, hchoiceSecond, hneq]
            exact (hsc hctrl).trans (by
              rw [currentColoring]
              simp [TwoColorComponentSwap, hfcomponent, hchoiceSecond, hneq])
          have hecol : sigma e = some gamma ∨ sigma e = some choice.color := by
            have hs : Sum.inr e ∈
                (TwoColorIncidenceGraph G sigma gamma choice.color).support := by
              apply SimpleGraph.mem_support_of_reachable
                (G := TwoColorIncidenceGraph G sigma gamma choice.color)
                (u := Sum.inr e) (v := Sum.inl choice.vertex) (by simp)
              exact SimpleGraph.ConnectedComponent.eq.mp heC
            obtain ⟨r, hr⟩ :=
              (TwoColorIncidenceGraph G sigma gamma choice.color).mem_support.mp hs
            cases r with
            | inl x => exact hr.2
            | inr x => simpa [TwoColorIncidenceGraph] using hr
          have hwC : Sum.inl w ∈ TwoColorComponent G sigma gamma choice.color
              (Sum.inl choice.vertex) := by
            have hadj : (TwoColorIncidenceGraph G sigma gamma choice.color).Adj
                (Sum.inl w) (Sum.inr e) := by
              simp [TwoColorIncidenceGraph, hwe, hecol]
            change (TwoColorIncidenceGraph G sigma gamma choice.color).connectedComponentMk
                (Sum.inl w) = _
            exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj).trans heC
          have hwv := (hcomponent w hw).mp hwC
          subst w
          rcases hecol with hec | hec
          · have hp : gamma ∈ PresentColors G sigma choice.vertex := by
              simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
              exact ⟨e, hwe, hec⟩
            by_contra hne
            exact (hsigmaProper hne ⟨choice.vertex, hwe, choice.edgeIncident⟩ hec hgamma).elim
          · by_contra hne
            have hcolor : sigma e = some choice.color := hec
            have hmissColor : choice.color ∈ MissingColors G sigma choice.vertex := by
              rw [hsigmaStableQ.2 choice.vertex hchoiceVertex]
              rw [MissingColors]
              simp only [Finset.mem_sdiff]
              refine ⟨?_, ?_⟩
              · exact Finset.mem_univ _
              · intro hp
                simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and] at hp
                rcases hp with ⟨a, hae, hac⟩
                by_cases ha : Sum.inr a ∈
                    TwoColorComponent G secondStable gamma choice.color
                      (Sum.inl choice.vertex)
                · rcases hcompEdge a ha with hag | hacs
                  · have hn : gamma ∉ PresentColors G secondStable choice.vertex := by
                      simpa [MissingColors] using hmissing
                    exact hn (by
                      simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
                      exact ⟨a, hae, hag⟩)
                  · rw [currentColoring] at hac
                    simp [TwoColorComponentSwap, ha, hacs, hneq, hneq.symm] at hac
                · rw [currentColoring] at hac
                  have hac' : secondStable a = some choice.color := by
                    simpa [TwoColorComponentSwap, ha] using hac
                  have hne : a ≠ choice.edge := by
                    intro heq
                    apply ha
                    exact heq ▸ hfcomponent
                  exact (secondStableProper hne ⟨choice.vertex, hae, choice.edgeIncident⟩
                    hac' hchoiceSecond).elim
            have hnot : choice.color ∉ PresentColors G sigma choice.vertex := by
              change choice.color ∈ Finset.univ \ PresentColors G sigma choice.vertex at hmissColor
              exact (Finset.mem_sdiff.mp hmissColor).2
            exact (hnot (by
              simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
              exact ⟨e, hwe, hcolor⟩)).elim
        let undone := TwoColorComponentSwap G sigma gamma choice.color
          (Sum.inl choice.vertex)
        have undoneProper : IsProperEdgeColoring G undone := by
          exact TwoColorComponentSwapProper G sigma gamma choice.color hneq
            hsigmaProper (Sum.inl choice.vertex)
        have undoneOne : IsOneEdgeUncolored undone e0 := by
          unfold IsOneEdgeUncolored
          constructor
          · by_cases he : Sum.inr e0 ∈
              TwoColorComponent G sigma gamma choice.color (Sum.inl choice.vertex)
            · simp [undone, TwoColorComponentSwap, he, hsigmaOne.1]
            · simp [undone, TwoColorComponentSwap, he, hsigmaOne.1]
          · intro e he
            obtain ⟨c, hc⟩ := hsigmaOne.2 e he
            by_cases hec : Sum.inr e ∈
                TwoColorComponent G sigma gamma choice.color (Sum.inl choice.vertex)
            · by_cases hcg : c = gamma
              · exact ⟨choice.color, by simp [undone, TwoColorComponentSwap, hec, hc, hcg]⟩
              · by_cases hcd : c = choice.color
                · exact ⟨gamma, by simp [undone, TwoColorComponentSwap, hec, hc, hcd,
                    hneq, hneq.symm]⟩
                · exact ⟨c, by simp [undone, TwoColorComponentSwap, hec, hc, hcg, hcd]⟩
            · exact ⟨c, by simp [undone, TwoColorComponentSwap, hec, hc]⟩
        have treeMissingTransport : ∀ (a b : PartialEdgeColoring E k),
            (∀ w, w ∈ TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc) →
              MissingColors G a w = MissingColors G b w) →
            TreeMissingColors a (ett.series.data.tree q.succ.castSucc) =
              TreeMissingColors b (ett.series.data.tree q.succ.castSucc) := by
          intro a b hab
          ext c
          unfold TreeMissingColors
          simp only [Finset.mem_biUnion]
          constructor
          · rintro ⟨w, hw, hc⟩
            exact ⟨w, hw, by rw [hab w hw] at hc; exact hc⟩
          · rintro ⟨w, hw, hc⟩
            exact ⟨w, hw, by rw [hab w hw]; exact hc⟩
        have treeSecondSelected :
            TreeMissingColors secondStable (ett.series.data.tree q.succ.castSucc) =
              TreeMissingColors choice.selected (ett.series.data.tree q.succ.castSucc) :=
          treeMissingTransport secondStable choice.selected (by
            intro w hw
            exact secondStableRelation.2 w hw)
        have sigmaComponentColor : ∀ e,
            Sum.inr e ∈ TwoColorComponent G sigma gamma choice.color
              (Sum.inl choice.vertex) →
            sigma e = some gamma ∨ sigma e = some choice.color := by
          intro e he
          have hs : Sum.inr e ∈
              (TwoColorIncidenceGraph G sigma gamma choice.color).support := by
            apply SimpleGraph.mem_support_of_reachable
              (G := TwoColorIncidenceGraph G sigma gamma choice.color)
              (u := Sum.inr e) (v := Sum.inl choice.vertex) (by simp)
            exact SimpleGraph.ConnectedComponent.eq.mp he
          obtain ⟨r, hr⟩ :=
            (TwoColorIncidenceGraph G sigma gamma choice.color).mem_support.mp hs
          cases r with
          | inl x => exact hr.2
          | inr x => simpa [TwoColorIncidenceGraph] using hr
        have currentColorMissing : choice.color ∈
            MissingColors G (ett.series.data.coloring q.succ) choice.vertex := by
          rw [MissingColors]
          simp only [Finset.mem_sdiff]
          refine ⟨Finset.mem_univ _, ?_⟩
          intro hp
          simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and] at hp
          rcases hp with ⟨e, he, hec⟩
          rw [currentColoring] at hec
          by_cases hecomp : Sum.inr e ∈
              TwoColorComponent G secondStable gamma choice.color (Sum.inl choice.vertex)
          · rcases hcompEdge e hecomp with hegamma | hecolor
            · have hm : gamma ∉ PresentColors G secondStable choice.vertex := by
                simpa [MissingColors] using hmissing
              apply hm
              simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
              exact ⟨e, he, hegamma⟩
            · simp [TwoColorComponentSwap, hecomp, hecolor, hneq, hneq.symm] at hec
          · have hecolor : secondStable e = some choice.color := by
              simpa [TwoColorComponentSwap, hecomp] using hec
            by_cases heq : e = choice.edge
            · subst e
              exact (hecomp hfcomponent).elim
            · exact (secondStableProper heq ⟨choice.vertex, he, choice.edgeIncident⟩
                hecolor hchoiceSecond).elim
        have sigmaColorMissing : choice.color ∈
            MissingColors G sigma choice.vertex := by
          rw [hsigmaStableQ.2 choice.vertex hchoiceVertex]
          exact currentColorMissing
        have treeSelectedPrevious :
            TreeMissingColors choice.selected (ett.series.data.tree q.succ.castSucc) =
              TreeMissingColors (ett.series.data.coloring q.castSucc)
                (ett.series.data.tree q.succ.castSucc) :=
          treeMissingTransport choice.selected (ett.series.data.coloring q.castSucc) (by
            intro w hw
            exact choice.selectedStable.2 w hw)
        have currentControl : ∀ c,
            c ∈ TreeMissingColors choice.selected (ett.series.data.tree q.succ.castSucc) ∪
                insert choice.color (TashkinovStoredColors ett.series.data q.castSucc) →
            c ∈ TreeMissingColors (ett.series.data.coloring q.succ)
                (ett.series.data.tree q.succ.castSucc) ∪
                TashkinovStoredColors ett.series.data q.succ := by
          intro c hc
          rcases Finset.mem_union.mp hc with hc | hc
          · apply (HkuMissingStoredMonotone G k ett.rounds e0 input ett.series q).1
            rw [treeSelectedPrevious] at hc
            exact Finset.mem_union.mpr (Or.inl hc)
          · rcases Finset.mem_insert.mp hc with rfl | hc
            · by_cases hm : choice.color ∈ TreeMissingColors
                  (ett.series.data.coloring q.succ) (ett.series.data.tree q.succ.castSucc)
              · exact Finset.mem_union.mpr (Or.inl hm)
              · apply Finset.mem_union.mpr
                right
                unfold TashkinovStoredColors
                rw [if_neg (by simp)]
                simp only [Finset.mem_sdiff, Finset.mem_biUnion]
                exact ⟨⟨q.succ, by simp, by simpa [currentStored]⟩, hm⟩
            · exact (HkuMissingStoredMonotone G k ett.rounds e0 input ett.series q).1
                (Finset.mem_union.mpr (Or.inr hc))
        have selectedStableFact := choice.selectedStable
        have sigmaStableFact := hsigmaStableQ
        have relationFact := secondStableRelation
        have gammaControl : gamma ∈
            TreeMissingColors choice.selected (ett.series.data.tree q.succ.castSucc) ∪
              insert choice.color (TashkinovStoredColors ett.series.data q.castSucc) := by
          apply Finset.mem_union.mpr
          left
          unfold TreeMissingColors
          simp only [Finset.mem_biUnion]
          refine ⟨choice.vertex, hchoiceVertex, ?_⟩
          rw [← secondStableRelation.2 choice.vertex
            choice.vertexDefective.1]
          exact hmissing
        have stableSecond : StableColoring
            (ett.series.data.tree q.succ.castSucc)
            (insert choice.color (TashkinovStoredColors ett.series.data q.castSucc))
            secondStable undone := by
          apply (sc1 G e0 (ett.series.data.tree q.succ.castSucc)
            (insert choice.color (TashkinovStoredColors ett.series.data q.castSucc))
            secondStable undone secondStableProper secondStableOneUncolored
            undoneProper undoneOne).2
          intro f hf h
          rcases h with h | h
          · rcases h with ⟨c, hc, hcf⟩
            rw [treeSecondSelected] at hc
            have h' := ((sc1 G e0 (ett.series.data.tree q.succ.castSucc)
              (insert choice.color (TashkinovStoredColors ett.series.data q.castSucc))
              choice.selected secondStable choice.selectedProper choice.selectedOneUncolored
              secondStableProper secondStableOneUncolored).mp secondStableRelation) f hf
              (Or.inr ⟨c, hc, hcf⟩)
            have hs := hsigmaStableQ.1 f hf
            by_cases hsf : Sum.inr f ∈
                TwoColorComponent G sigma gamma choice.color (Sum.inl choice.vertex)
            · have ef := hsigmaEdge f hf hsf
              subst f
              rcases sigmaComponentColor choice.edge hsf with hec | hec
              · simp [undone, TwoColorComponentSwap, hsf, hec, hchoiceSecond]
              · exfalso
                have hnot : choice.color ∉ PresentColors G sigma choice.vertex := by
                  simpa [MissingColors] using sigmaColorMissing
                apply hnot
                simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
                exact ⟨choice.edge, choice.edgeIncident, hec⟩
            · have hu : undone f = sigma f := by
                change (if Sum.inr f ∈
                  TwoColorComponent G sigma gamma choice.color (Sum.inl choice.vertex) then
                    (if sigma f = some gamma then some choice.color
                    else if sigma f = some choice.color then some gamma else sigma f)
                  else sigma f) = sigma f
                exact if_neg hsf
              rw [hu]
              clear hdegree hdegreeBound hclosed hpathComponent hcompEdge
                hsigmaEdge sigmaComponentColor
              by_cases ha : Sum.inr f ∈
                  TwoColorComponent G secondStable gamma choice.color
                    (Sum.inl choice.vertex)
              · have he := htreeEdge f hf ha
                subst f
                have hcGamma := currentControl gamma gammaControl
                have hsGamma := hsigmaStableQ.1 choice.edge
                  ⟨choice.vertex, choice.vertexDefective.1, choice.edgeIncident⟩
                  ⟨gamma, hcGamma, by
                    rw [currentColoring]
                    simp [TwoColorComponentSwap, ha, hneq, hchoiceSecond]⟩
                have hcurGamma : ett.series.data.coloring q.succ choice.edge =
                    some gamma := by
                  rw [currentColoring]
                  simp [TwoColorComponentSwap, ha, hneq, hchoiceSecond]
                have hsigGamma : sigma choice.edge = some gamma :=
                  hsGamma.trans hcurGamma
                have hmem : Sum.inr choice.edge ∈
                    TwoColorComponent G sigma gamma choice.color
                      (Sum.inl choice.vertex) := by
                  apply SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
                  simp [TwoColorIncidenceGraph, choice.edgeIncident, hsigGamma]
                exact (hsf hmem).elim
              · have hcur : ett.series.data.coloring q.succ f = some c := by
                  rw [currentColoring]
                  simp [TwoColorComponentSwap, ha, hcf, h', hneq]
                have hsig := hsigmaStableQ.1 f hf
                  ⟨c, currentControl c hc, hcur⟩
                exact hsig.trans (hcur.trans hcf.symm)
          · rcases h with ⟨c, hc, hcf⟩
            by_cases hsf : Sum.inr f ∈
                TwoColorComponent G sigma gamma choice.color (Sum.inl choice.vertex)
            · have ef := hsigmaEdge f hf hsf
              subst f
              rcases sigmaComponentColor choice.edge hsf with hec | hec
              · simp [undone, TwoColorComponentSwap, hsf, hec, hchoiceSecond]
              · exfalso
                have hnot : choice.color ∉ PresentColors G sigma choice.vertex := by
                  simpa [MissingColors] using sigmaColorMissing
                apply hnot
                simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
                exact ⟨choice.edge, choice.edgeIncident, hec⟩
            · have hu : undone f = sigma f := by
                change (if Sum.inr f ∈
                  TwoColorComponent G sigma gamma choice.color (Sum.inl choice.vertex) then
                    (if sigma f = some gamma then some choice.color
                    else if sigma f = some choice.color then some gamma else sigma f)
                  else sigma f) = sigma f
                exact if_neg hsf
              rw [hu]
              clear hdegree hdegreeBound hclosed hpathComponent hcompEdge
                hsigmaEdge sigmaComponentColor
              rw [treeSecondSelected] at hc
              by_cases ha : Sum.inr f ∈
                  TwoColorComponent G secondStable gamma choice.color
                    (Sum.inl choice.vertex)
              · have he := htreeEdge f hf ha
                subst f
                have hcGamma := currentControl gamma gammaControl
                have hsGamma := hsigmaStableQ.1 choice.edge
                  ⟨choice.vertex, choice.vertexDefective.1, choice.edgeIncident⟩
                  ⟨gamma, hcGamma, by
                    rw [currentColoring]
                    simp [TwoColorComponentSwap, ha, hneq, hchoiceSecond]⟩
                have hcurGamma : ett.series.data.coloring q.succ choice.edge =
                    some gamma := by
                  rw [currentColoring]
                  simp [TwoColorComponentSwap, ha, hneq, hchoiceSecond]
                have hsigGamma : sigma choice.edge = some gamma :=
                  hsGamma.trans hcurGamma
                have hmem : Sum.inr choice.edge ∈
                    TwoColorComponent G sigma gamma choice.color
                      (Sum.inl choice.vertex) := by
                  apply SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
                  simp [TwoColorIncidenceGraph, choice.edgeIncident, hsigGamma]
                exact (hsf hmem).elim
              · have hsigmaValue : sigma f = some c := hu.symm.trans hcf
                have hsig := ((sc1 G e0 (ett.series.data.tree q.succ.castSucc)
                  (TashkinovStoredColors ett.series.data q.succ)
                  (ett.series.data.coloring q.succ) sigma currentProper currentOneUncolored
                  hsigmaProper hsigmaOne).mp hsigmaStableQ) f hf
                  (Or.inr ⟨c, currentControl c hc, hsigmaValue⟩)
                have hcur : ett.series.data.coloring q.succ f = some c :=
                  (Eq.symm hsig).trans hsigmaValue
                have hsecond : secondStable f = some c := by
                  have hcs : ett.series.data.coloring q.succ f = secondStable f := by
                    rw [currentColoring]
                    simp [TwoColorComponentSwap, ha]
                  exact hcs.symm.trans hcur
                exact hsig.trans (hcur.trans hsecond.symm)
        have stableSelected : StableColoring
            (ett.series.data.tree q.succ.castSucc)
            (insert choice.color (TashkinovStoredColors ett.series.data q.castSucc))
            choice.selected undone := by
          apply (sc1 G e0 (ett.series.data.tree q.succ.castSucc)
            (insert choice.color (TashkinovStoredColors ett.series.data q.castSucc))
            choice.selected undone choice.selectedProper choice.selectedOneUncolored
            undoneProper undoneOne).2
          have stableSecondCriterion :=
            ((sc1 G e0 (ett.series.data.tree q.succ.castSucc)
              (insert choice.color (TashkinovStoredColors ett.series.data q.castSucc))
              secondStable undone secondStableProper secondStableOneUncolored
              undoneProper undoneOne).mp stableSecond)
          intro f hf h
          rcases h with h | h
          · rcases h with ⟨c, hc, hcf⟩
            have hrel := secondStableRelation.1 f hf
              ⟨c, hc, hcf⟩
            have hc2 := hc
            rw [← treeSecondSelected] at hc2
            have hstable := stableSecondCriterion f hf
              (Or.inl ⟨c, hc2, hrel.trans hcf⟩)
            exact hstable.trans hrel
          · rcases h with ⟨c, hc, hcf⟩
            have hc2 := hc
            rw [← treeSecondSelected] at hc2
            have hstable := stableSecondCriterion f hf
              (Or.inr ⟨c, hc2, hcf⟩)
            have hsecond : secondStable f = some c := hstable.symm.trans hcf
            have relationCriterion :=
              ((sc1 G e0 (ett.series.data.tree q.succ.castSucc)
                (insert choice.color (TashkinovStoredColors ett.series.data q.castSucc))
                choice.selected secondStable choice.selectedProper choice.selectedOneUncolored
                secondStableProper secondStableOneUncolored).mp secondStableRelation)
            have hrel := relationCriterion f hf (Or.inr ⟨c, hc, hsecond⟩)
            exact hstable.trans hrel
        rw [hsigmaPrevFormula]
        exact stableSelected
      have hdeltaBoundary : BoundaryColorEdges G choice.selected
            (TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc))
            choice.color =
          BoundaryColorEdges G sigmaPrev
            (TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc))
            choice.color := by
        ext f
        simp only [BoundaryColorEdges, Finset.mem_filter]
        constructor
        · rintro ⟨hf, hfc⟩
          refine ⟨hf, ?_⟩
          obtain ⟨x, hx, y, hy, hends⟩ := by
            simpa [BoundaryEdges] using hf
          have hinc : TreeIncidentEdge
              (ett.series.data.tree q.succ.castSucc) f := by
            refine ⟨x, hx, ?_⟩
            unfold Incident
            rw [hends]
            exact Sym2.mem_mk_left _ _
          exact (hsigmaPrevEnlarged.1 f hinc
            ⟨choice.color, Finset.mem_union_right _
              (Finset.mem_insert_self _ _), hfc⟩).trans hfc
        · rintro ⟨hf, hfc⟩
          refine ⟨hf, ?_⟩
          obtain ⟨x, hx, y, hy, hends⟩ := by
            simpa [BoundaryEdges] using hf
          have hinc : TreeIncidentEdge
              (ett.series.data.tree q.succ.castSucc) f := by
            refine ⟨x, hx, ?_⟩
            unfold Incident
            rw [hends]
            exact Sym2.mem_mk_left _ _
          have hcriterion := (sc1 G e0
            (ett.series.data.tree q.succ.castSucc)
            (insert choice.color
              (TashkinovStoredColors ett.series.data q.castSucc))
            choice.selected sigmaPrev choice.selectedProper
            choice.selectedOneUncolored hsigmaPrevProper hsigmaPrevOne).mp
              hsigmaPrevEnlarged
          exact (hcriterion f hinc (Or.inr
            ⟨choice.color, Finset.mem_union_right _
              (Finset.mem_insert_self _ _), hfc⟩)).symm.trans hfc
      have hchoiceDefective : DefectiveColor G sigmaPrev
          (TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc))
          choice.color := by
        obtain ⟨oldColor, holdDefective, holdEdge⟩ := choice.edgeDefective
        have holdColor : oldColor = choice.color := by
          have holdEdgeColor := (Finset.mem_filter.mp holdEdge).2
          exact Option.some.inj (holdEdgeColor.symm.trans choice.edgeColor)
        subst oldColor
        unfold DefectiveColor
        rw [← hdeltaBoundary]
        exact holdDefective
      have hchoiceEdgeNew : choice.edge ∈ BoundaryColorEdges G sigmaPrev
          (TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc))
          choice.color := by
        rw [← hdeltaBoundary]
        obtain ⟨oldColor, holdDefective, holdEdge⟩ := choice.edgeDefective
        have holdColor : oldColor = choice.color := by
          have holdEdgeColor := (Finset.mem_filter.mp holdEdge).2
          exact Option.some.inj (holdEdgeColor.symm.trans choice.edgeColor)
        simpa [holdColor] using holdEdge
      have hsigmaPrevSelf : StableColoring
          (ett.series.data.tree q.succ.castSucc)
          (TashkinovStoredColors ett.series.data q.castSucc)
          sigmaPrev sigmaPrev := by
        exact (sc2 G e0 (ett.series.data.tree q.succ.castSucc)
          (TashkinovStoredColors ett.series.data q.castSucc)).refl
          ⟨sigmaPrev, hsigmaPrevProper, hsigmaPrevOne⟩
      let newChoice : MaximumDefectiveChoice G e0
          (ett.series.data.tree q.succ.castSucc)
          (TashkinovStoredColors ett.series.data q.castSucc) sigmaPrev := {
        selected := sigmaPrev
        selectedProper := hsigmaPrevProper
        selectedOneUncolored := hsigmaPrevOne
        selectedStable := hsigmaPrevSelf
        vertex := choice.vertex
        vertexDefective := ⟨choice.vertexDefective.1, choice.edge,
          ⟨choice.color, hchoiceDefective, hchoiceEdgeNew⟩,
          choice.edgeIncident⟩
        maximal := by
          intro pi w hpiProper hpiOne hpiStable hw
          have hpiOld : StableColoring
              (ett.series.data.tree q.succ.castSucc)
              (TashkinovStoredColors ett.series.data q.castSucc)
              (ett.series.data.coloring q.castSucc) pi := by
            exact (sc2 G e0 (ett.series.data.tree q.succ.castSucc)
              (TashkinovStoredColors ett.series.data q.castSucc)).trans
                (x := ⟨ett.series.data.coloring q.castSucc,
                  ⟨previousProper, previousOneUncolored⟩⟩)
                (y := ⟨sigmaPrev, ⟨hsigmaPrevProper, hsigmaPrevOne⟩⟩)
                (z := ⟨pi, ⟨hpiProper, hpiOne⟩⟩)
                hsigmaPrevStableQ hpiStable
          exact choice.maximal pi w hpiProper hpiOne hpiOld hw
        edge := choice.edge
        edgeDefective := ⟨choice.color, hchoiceDefective, hchoiceEdgeNew⟩
        edgeIncident := choice.edgeIncident
        otherEndpoint := choice.otherEndpoint
        otherOutside := choice.otherOutside
        edgeEnds := choice.edgeEnds
        color := choice.color
        edgeColor := (Finset.mem_filter.mp hchoiceEdgeNew).2 }
      have hclosedPrev : ColoredVertexSetClosed G sigmaPrev
          (TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc)) := by
        intro f c v hf hv hsf hcm
        obtain ⟨x, hx, y, hy, hends⟩ := by
          simpa [BoundaryEdges] using hf
        have hinc : TreeIncidentEdge
            (ett.series.data.tree q.succ.castSucc) f := by
          refine ⟨x, hx, ?_⟩
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
          (ett.series.data.coloring q.castSucc) sigmaPrev previousProper
          previousOneUncolored hsigmaPrevProper hsigmaPrevOne).mp
            hsigmaPrevStableQ
        have hcopy := hcriterion f hinc
          (Or.inr ⟨c, Finset.mem_union_left _ hcTree, hsf⟩)
        have holdf : ett.series.data.coloring q.castSucc f = some c :=
          hcopy.symm.trans hsf
        exact previousClosed hf hv holdf (hmissingEq ▸ hcm)
      have hnotStrongPrev : ¬ ColoredVertexSetStronglyClosed G sigmaPrev
          (TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc)) := by
        intro hstrong
        have hone : 1 < (BoundaryColorEdges G sigmaPrev
            (TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc))
            choice.color).card := by
          have htwo : 2 ≤ (BoundaryColorEdges G sigmaPrev
              (TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc))
              choice.color).card := hchoiceDefective
          omega
        obtain ⟨f, hf, g, hg, hfg⟩ := Finset.one_lt_card.mp hone
        have hfBoundary := (Finset.mem_filter.mp hf).1
        have hgBoundary := (Finset.mem_filter.mp hg).1
        have hfColor := (Finset.mem_filter.mp hf).2
        have hgColor := (Finset.mem_filter.mp hg).2
        exact (hstrong.2 hfBoundary hgBoundary hfg hfColor) hgColor
      have hnewAlternativeFails : ∃ rho : PartialEdgeColoring E k,
          IsProperEdgeColoring G rho ∧ IsOneEdgeUncolored rho e0 ∧
            StableColoring (ett.series.data.tree q.succ.castSucc)
              (insert newChoice.color
                (TashkinovStoredColors ett.series.data q.castSucc))
              newChoice.selected rho ∧
            ¬ Disjoint (MissingColors G rho newChoice.otherEndpoint)
              (TreeMissingColors rho
                (ett.series.data.tree q.succ.castSucc)) := by
        rcases seriesAlternativeFails with
          ⟨rho, hrhoProper, hrhoOne, hrhoStable, hrhoIntersection⟩
        have hreverse : StableColoring
            (ett.series.data.tree q.succ.castSucc)
            (insert choice.color
              (TashkinovStoredColors ett.series.data q.castSucc))
            sigmaPrev choice.selected := by
          exact (sc2 G e0 (ett.series.data.tree q.succ.castSucc)
            (insert choice.color
              (TashkinovStoredColors ett.series.data q.castSucc))).symm
              (x := ⟨choice.selected,
                ⟨choice.selectedProper, choice.selectedOneUncolored⟩⟩)
              (y := ⟨sigmaPrev, ⟨hsigmaPrevProper, hsigmaPrevOne⟩⟩)
              hsigmaPrevEnlarged
        have hrhoNew : StableColoring
            (ett.series.data.tree q.succ.castSucc)
            (insert choice.color
              (TashkinovStoredColors ett.series.data q.castSucc))
            sigmaPrev rho := by
          exact (sc2 G e0 (ett.series.data.tree q.succ.castSucc)
            (insert choice.color
              (TashkinovStoredColors ett.series.data q.castSucc))).trans
              (x := ⟨sigmaPrev, ⟨hsigmaPrevProper, hsigmaPrevOne⟩⟩)
              (y := ⟨choice.selected,
                ⟨choice.selectedProper, choice.selectedOneUncolored⟩⟩)
              (z := ⟨rho, ⟨hrhoProper, hrhoOne⟩⟩)
              hreverse hrhoStable
        refine ⟨rho, hrhoProper, hrhoOne, ?_, ?_⟩
        · simpa [newChoice] using hrhoNew
        · simpa [newChoice] using hrhoIntersection
      have hgammaSecond : gamma ∈ MissingColors G secondStable
          choice.vertex := by
        rw [secondStableRelation.2 choice.vertex choice.vertexDefective.1]
        exact gammaRule.1
      have hchoiceSecond : secondStable choice.edge = some choice.color := by
        have hfix := secondStableRelation.1 choice.edge
          ⟨choice.vertex, choice.vertexDefective.1, choice.edgeIncident⟩
          ⟨choice.color, Finset.mem_union_right _
            (Finset.mem_insert_self _ _), choice.edgeColor⟩
        exact hfix.trans choice.edgeColor
      have hgammaDeltaNe : gamma ≠ choice.color := by
        intro heq
        have hpresent : gamma ∈ PresentColors G secondStable choice.vertex := by
          simp only [PresentColors, Finset.mem_filter, Finset.mem_univ,
            true_and]
          exact ⟨choice.edge, choice.edgeIncident, heq ▸ hchoiceSecond⟩
        have hnot : gamma ∉ PresentColors G secondStable choice.vertex := by
          simpa [MissingColors] using hgammaSecond
        exact hnot hpresent
      have hchoiceSecondComponent : Sum.inr choice.edge ∈
          TwoColorComponent G secondStable gamma choice.color
            (Sum.inl choice.vertex) := by
        apply SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
        simp [TwoColorIncidenceGraph, choice.edgeIncident, hchoiceSecond]
      have hdeltaCurrentMissing : choice.color ∈ MissingColors G
          (ett.series.data.coloring q.succ) choice.vertex := by
        rw [MissingColors]
        simp only [Finset.mem_sdiff]
        refine ⟨Finset.mem_univ _, ?_⟩
        intro hpresent
        simp only [PresentColors, Finset.mem_filter, Finset.mem_univ,
          true_and] at hpresent
        rcases hpresent with ⟨f, hfIncident, hfCurrent⟩
        rw [currentColoring] at hfCurrent
        by_cases hfComponent : Sum.inr f ∈
            TwoColorComponent G secondStable gamma choice.color
              (Sum.inl choice.vertex)
        · by_cases hfg : secondStable f = some gamma
          · have hp : gamma ∈ PresentColors G secondStable choice.vertex := by
              simp only [PresentColors, Finset.mem_filter, Finset.mem_univ,
                true_and]
              exact ⟨f, hfIncident, hfg⟩
            have hnot : gamma ∉ PresentColors G secondStable choice.vertex := by
              simpa [MissingColors] using hgammaSecond
            exact hnot hp
          · by_cases hfd : secondStable f = some choice.color
            · have heq : choice.color = gamma := by
                simpa [TwoColorComponentSwap, hfComponent, hfg, hfd,
                  hgammaDeltaNe] using hfCurrent
              exact hgammaDeltaNe heq.symm
            · simp [TwoColorComponentSwap, hfComponent, hfg, hfd] at hfCurrent
        · have hfd : secondStable f = some choice.color := by
            simpa [TwoColorComponentSwap, hfComponent] using hfCurrent
          by_cases hfeq : f = choice.edge
          · subst f
            exact hfComponent hchoiceSecondComponent
          · exact (secondStableProper hfeq
              ⟨choice.vertex, hfIncident, choice.edgeIncident⟩
              hfd hchoiceSecond).elim
      have hdeltaSigmaMissing : choice.color ∈ MissingColors G sigma
          choice.vertex := by
        rw [hsigmaStableQ.2 choice.vertex hchoiceVertex]
        exact hdeltaCurrentMissing
      have hsigmaComponentColor : ∀ f,
          Sum.inr f ∈ TwoColorComponent G sigma gamma choice.color
              (Sum.inl choice.vertex) →
            sigma f = some gamma ∨ sigma f = some choice.color := by
        intro f hf
        have hs : Sum.inr f ∈
            (TwoColorIncidenceGraph G sigma gamma choice.color).support := by
          apply SimpleGraph.mem_support_of_reachable
            (G := TwoColorIncidenceGraph G sigma gamma choice.color)
            (u := Sum.inr f) (v := Sum.inl choice.vertex) (by simp)
          exact SimpleGraph.ConnectedComponent.eq.mp hf
        obtain ⟨r, hr⟩ :=
          (TwoColorIncidenceGraph G sigma gamma choice.color).mem_support.mp hs
        cases r with
        | inl x => exact hr.2
        | inr x => simpa [TwoColorIncidenceGraph] using hr
      have hgammaPrevMissing : gamma ∈ MissingColors G sigmaPrev
          choice.vertex := by
        rw [MissingColors]
        simp only [Finset.mem_sdiff]
        refine ⟨Finset.mem_univ _, ?_⟩
        intro hpresent
        simp only [PresentColors, Finset.mem_filter, Finset.mem_univ,
          true_and] at hpresent
        rcases hpresent with ⟨f, hfIncident, hfPrev⟩
        rw [hsigmaPrevFormula] at hfPrev
        by_cases hfComponent : Sum.inr f ∈
            TwoColorComponent G sigma gamma choice.color
              (Sum.inl choice.vertex)
        · rcases hsigmaComponentColor f hfComponent with hfg | hfd
          · have heq : choice.color = gamma := by
              simpa [TwoColorComponentSwap, hfComponent, hfg,
                hgammaDeltaNe] using hfPrev
            exact hgammaDeltaNe heq.symm
          · have hp : choice.color ∈ PresentColors G sigma choice.vertex := by
              simp only [PresentColors, Finset.mem_filter, Finset.mem_univ,
                true_and]
              exact ⟨f, hfIncident, hfd⟩
            have hnot : choice.color ∉ PresentColors G sigma choice.vertex := by
              simpa [MissingColors] using hdeltaSigmaMissing
            exact hnot hp
        · have hfg : sigma f = some gamma := by
            simpa [TwoColorComponentSwap, hfComponent] using hfPrev
          apply hfComponent
          apply SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
          simp [TwoColorIncidenceGraph, hfIncident, hfg]
      have hswapGraph : TwoColorIncidenceGraph G sigmaPrev gamma choice.color =
          TwoColorIncidenceGraph G sigma gamma choice.color := by
        rw [hsigmaPrevFormula]
        ext x y
        cases x with
        | inl v =>
            cases y with
            | inl w => simp [TwoColorIncidenceGraph]
            | inr f =>
                by_cases hf : Sum.inr f ∈ TwoColorComponent G sigma gamma
                    choice.color (Sum.inl choice.vertex)
                · rcases hsigmaComponentColor f hf with hfg | hfd
                  · simp [TwoColorIncidenceGraph, TwoColorComponentSwap, hf,
                      hfg, hgammaDeltaNe]
                  · simp [TwoColorIncidenceGraph, TwoColorComponentSwap, hf,
                      hfd, hgammaDeltaNe]
                · simp [TwoColorIncidenceGraph, TwoColorComponentSwap, hf]
        | inr f =>
            cases y with
            | inl v =>
                by_cases hf : Sum.inr f ∈ TwoColorComponent G sigma gamma
                    choice.color (Sum.inl choice.vertex)
                · rcases hsigmaComponentColor f hf with hfg | hfd
                  · simp [TwoColorIncidenceGraph, TwoColorComponentSwap, hf,
                      hfg, hgammaDeltaNe]
                  · simp [TwoColorIncidenceGraph, TwoColorComponentSwap, hf,
                      hfd, hgammaDeltaNe]
                · simp [TwoColorIncidenceGraph, TwoColorComponentSwap, hf]
            | inr g => simp [TwoColorIncidenceGraph]
      have hcomponentPrev : ∀ w,
          w ∈ TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc) →
          (Sum.inl w ∈ TwoColorComponent G sigmaPrev gamma choice.color
              (Sum.inl choice.vertex) ↔ w = choice.vertex) := by
        intro w hw
        unfold TwoColorComponent
        rw [hswapGraph]
        exact hcomponent w hw
      have hsigmaRecovered : sigma =
          TwoColorComponentSwap G sigmaPrev gamma choice.color
            (Sum.inl choice.vertex) := by
        funext f
        have hcomponentEq :
            (Sum.inr f ∈ TwoColorComponent G sigmaPrev gamma choice.color
                (Sum.inl choice.vertex)) ↔
              Sum.inr f ∈ TwoColorComponent G sigma gamma choice.color
                (Sum.inl choice.vertex) := by
          unfold TwoColorComponent
          rw [hswapGraph]
        by_cases hf : Sum.inr f ∈ TwoColorComponent G sigma gamma
            choice.color (Sum.inl choice.vertex)
        · have hfPrev := hcomponentEq.mpr hf
          rcases hsigmaComponentColor f hf with hfg | hfd
          · have hprevValue : sigmaPrev f = some choice.color := by
              rw [hsigmaPrevFormula, TwoColorComponentSwap, if_pos hf]
              simp [hfg, hgammaDeltaNe]
            rw [TwoColorComponentSwap, if_pos hfPrev, hprevValue]
            simpa [hgammaDeltaNe, hgammaDeltaNe.symm] using hfg
          · have hprevValue : sigmaPrev f = some gamma := by
              rw [hsigmaPrevFormula, TwoColorComponentSwap, if_pos hf]
              simp [hfd, hgammaDeltaNe]
            rw [TwoColorComponentSwap, if_pos hfPrev, hprevValue]
            simpa [hgammaDeltaNe, hgammaDeltaNe.symm] using hfd
        · have hfPrev : Sum.inr f ∉ TwoColorComponent G sigmaPrev gamma
              choice.color (Sum.inl choice.vertex) := by
            simpa [hcomponentEq] using hf
          rw [TwoColorComponentSwap, if_neg hfPrev, hsigmaPrevFormula,
            TwoColorComponentSwap, if_neg hf]
      let H := TwoColorIncidenceGraph G sigmaPrev gamma choice.color
      have hrootLeaf : Set.Subsingleton
          (H.neighborSet (Sum.inl choice.vertex)) := by
        have hdegree : @SimpleGraph.degree _ H (Sum.inl choice.vertex)
            (Fintype.ofFinite _) ≤ 1 := by
          simpa [H] using MissingColorIncidenceEndpoint G sigmaPrev gamma
            choice.color hgammaDeltaNe hsigmaPrevProper choice.vertex
              hgammaPrevMissing
        letI : Fintype (H.neighborSet (Sum.inl choice.vertex)) :=
          Fintype.ofFinite _
        intro x hx y hy
        have hcard : Fintype.card (H.neighborSet (Sum.inl choice.vertex)) ≤ 1 := by
          rw [SimpleGraph.card_neighborSet_eq_degree]
          exact hdegree
        exact congrArg Subtype.val
          (Fintype.card_le_one_iff.mp hcard ⟨x, hx⟩ ⟨y, hy⟩)
      have hrootComponent : Sum.inl choice.vertex ∈
          TwoColorComponent G sigmaPrev gamma choice.color
            (Sum.inl choice.vertex) := by
        change H.connectedComponentMk (Sum.inl choice.vertex) =
          H.connectedComponentMk (Sum.inl choice.vertex)
        rfl
      have hedgeComponent : Sum.inr choice.edge ∈
          TwoColorComponent G sigmaPrev gamma choice.color
            (Sum.inl choice.vertex) := by
        apply SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
        simp [H, TwoColorIncidenceGraph, choice.edgeIncident,
          (Finset.mem_filter.mp hchoiceEdgeNew).2]
      obtain ⟨a, b, p, hp, hps⟩ :=
        TwoColorComponentSpanningPath G sigmaPrev gamma choice.color
          hsigmaPrevProper (Sum.inl choice.vertex)
      have hrootSupport : Sum.inl choice.vertex ∈ p.support := by
        change Sum.inl choice.vertex ∈ {z | z ∈ p.support}
        rw [hps]
        exact hrootComponent
      have hrootEnd : Sum.inl choice.vertex = a ∨
          Sum.inl choice.vertex = b := by
        by_contra hn
        push Not at hn
        exact (hp.isTrail.not_mem_support_of_subsingleton_neighborSet
          hn.1 hn.2 hrootLeaf) hrootSupport
      obtain ⟨b, p, hp, hps⟩ : ∃ (b : Sum V E)
          (p : H.Walk (Sum.inl choice.vertex) b),
          p.IsPath ∧ {z | z ∈ p.support} =
            TwoColorComponent G sigmaPrev gamma choice.color
              (Sum.inl choice.vertex) := by
        rcases hrootEnd with ha | hb
        · subst a
          exact ⟨b, p, hp, hps⟩
        · subst b
          refine ⟨a, p.reverse, hp.reverse, ?_⟩
          ext z
          change z ∈ p.reverse.support ↔ z ∈
            TwoColorComponent G sigmaPrev gamma choice.color
              (Sum.inl choice.vertex)
          rw [SimpleGraph.Walk.support_reverse, List.mem_reverse]
          exact Set.ext_iff.mp hps z
      have hpNotNil : ¬ p.Nil := by
        intro hnil
        have hedgeSupport : Sum.inr choice.edge ∈ p.support := by
          change Sum.inr choice.edge ∈ {z | z ∈ p.support}
          rw [hps]
          exact hedgeComponent
        rw [SimpleGraph.Walk.nil_iff_support_eq.mp hnil] at hedgeSupport
        simp at hedgeSupport
      have hendNeighbor : ∀ y, H.Adj b y →
          y = p.getVert (p.length - 1) := by
        intro y hby
        have hyComponent : y ∈ TwoColorComponent G sigmaPrev gamma
            choice.color (Sum.inl choice.vertex) := by
          have hbComponent : b ∈ TwoColorComponent G sigmaPrev gamma
              choice.color (Sum.inl choice.vertex) := by
            rw [← hps]
            change b ∈ p.support
            simpa only [p.getVert_length] using
              p.getVert_mem_support p.length
          change H.connectedComponentMk y =
            H.connectedComponentMk (Sum.inl choice.vertex)
          change H.connectedComponentMk b =
            H.connectedComponentMk (Sum.inl choice.vertex) at hbComponent
          exact
            (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
              hby).symm.trans hbComponent
        have hySupport : y ∈ p.support := by
          change y ∈ {z | z ∈ p.support}
          rw [hps]
          exact hyComponent
        obtain ⟨n, hn, hnle⟩ :=
          SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hySupport
        have hnlt : n < p.length := by
          have hnne : n ≠ p.length := by
            intro heq
            have hyb : y = b := by
              rw [← hn, heq, p.getVert_length]
            exact hby.ne hyb.symm
          omega
        by_cases hpen : n + 1 = p.length
        · rw [← hn]
          congr 1
          omega
        by_cases hn0 : n = 0
        · have hnext : H.Adj (Sum.inl choice.vertex) (p.getVert 1) := by
            simpa [hn0, p.getVert_zero] using
              p.adj_getVert_succ hnlt
          have hbstart : H.Adj (Sum.inl choice.vertex) b := by
            rw [← hn, hn0, p.getVert_zero] at hby
            exact hby.symm
          have hneNext : p.getVert 1 ≠ b := by
            intro heq
            have hindices := hp.getVert_injOn
              (show 1 ≤ p.length by omega)
              (show p.length ≤ p.length by rfl)
              (heq.trans p.getVert_length.symm)
            omega
          exact False.elim (hneNext (hrootLeaf hnext hbstart))
        · have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
          have hleft : H.Adj y (p.getVert (n - 1)) := by
            rw [← hn]
            have hadj := p.adj_getVert_succ (i := n - 1) (by omega)
            simpa only [Nat.sub_add_cancel (by omega : 1 ≤ n)] using
              hadj.symm
          have hright : H.Adj y (p.getVert (n + 1)) := by
            rw [← hn]
            exact p.adj_getVert_succ hnlt
          have hbneLeft : b ≠ p.getVert (n - 1) := by
            intro heq
            have hindices := hp.getVert_injOn
              (show p.length ≤ p.length by rfl)
              (show n - 1 ≤ p.length by omega)
              (p.getVert_length.trans heq)
            omega
          have hbneRight : b ≠ p.getVert (n + 1) := by
            intro heq
            have hindices := hp.getVert_injOn
              (show p.length ≤ p.length by rfl)
              (show n + 1 ≤ p.length by omega)
              (p.getVert_length.trans heq)
            omega
          have hlrne : p.getVert (n - 1) ≠ p.getVert (n + 1) := by
            intro heq
            have hindices := hp.getVert_injOn
              (show n - 1 ≤ p.length by omega)
              (show n + 1 ≤ p.length by omega) heq
            omega
          letI : Fintype (H.neighborSet y) := Fintype.ofFinite _
          have hthree : 3 ≤ @SimpleGraph.degree _ H y
              (Fintype.ofFinite _) := by
            rw [← SimpleGraph.card_neighborFinset_eq_degree]
            let ss : Finset (Sum V E) :=
              {b, p.getVert (n - 1), p.getVert (n + 1)}
            have hss : ss ⊆ H.neighborFinset y := by
              intro z hz
              simp only [ss, Finset.mem_insert, Finset.mem_singleton] at hz
              rcases hz with rfl | rfl | rfl
              · simpa [SimpleGraph.mem_neighborFinset] using hby.symm
              · simpa [SimpleGraph.mem_neighborFinset] using hleft
              · simpa [SimpleGraph.mem_neighborFinset] using hright
            have hc3 : 3 ≤ ss.card := by
              simp [ss, hbneLeft, hbneRight, hlrne]
            exact hc3.trans (Finset.card_le_card hss)
          have htwo : @SimpleGraph.degree _ H y
              (Fintype.ofFinite _) ≤ 2 := by
            simpa [H] using TwoColorIncidenceDegreeAtMostTwo G sigmaPrev
              gamma choice.color hsigmaPrevProper y
          omega
      have hendLeaf : Set.Subsingleton (H.neighborSet b) := by
        intro y hy z hz
        exact (hendNeighbor y hy).trans (hendNeighbor z hz).symm
      have hpPos : 0 < p.length :=
        SimpleGraph.Walk.not_nil_iff_lt_length.mp hpNotNil
      have hendVertex : ∃ u : V, b = Sum.inl u := by
        cases hb : b with
        | inl u => exact ⟨u, rfl⟩
        | inr e =>
            have hlastAdj : H.Adj (p.getVert (p.length - 1)) b := by
              simpa only [Nat.sub_add_cancel (by omega : 1 ≤ p.length),
                p.getVert_length] using
                p.adj_getVert_succ (i := p.length - 1) (by omega)
            have hecolor : sigmaPrev e = some gamma ∨
                sigmaPrev e = some choice.color := by
              cases hprev : p.getVert (p.length - 1) with
              | inl w =>
                  rw [hprev, hb] at hlastAdj
                  have hdata : Incident G w e ∧
                      (sigmaPrev e = some gamma ∨
                        sigmaPrev e = some choice.color) := by
                    simpa [H, TwoColorIncidenceGraph] using hlastAdj
                  exact hdata.2
              | inr f =>
                  rw [hprev, hb] at hlastAdj
                  have : False := by
                    simpa [H, TwoColorIncidenceGraph] using hlastAdj
                  exact this.elim
            induction hends : G.ends e using Sym2.inductionOn with
            | _ u v =>
                have huv : u ≠ v := by
                  intro huv
                  subst v
                  exact G.loopless e u hends
                have huAdj : H.Adj b (Sum.inl u) := by
                  rw [hb]
                  simpa [H, TwoColorIncidenceGraph, Incident, hends] using
                    (show Incident G u e ∧
                        (sigmaPrev e = some gamma ∨
                          sigmaPrev e = some choice.color) from
                      ⟨by simp [Incident, hends], hecolor⟩)
                have hvAdj : H.Adj b (Sum.inl v) := by
                  rw [hb]
                  simpa [H, TwoColorIncidenceGraph, Incident, hends] using
                    (show Incident G v e ∧
                        (sigmaPrev e = some gamma ∨
                          sigmaPrev e = some choice.color) from
                      ⟨by simp [Incident, hends], hecolor⟩)
                exact False.elim
                  (huv (Sum.inl.inj (hendLeaf huAdj hvAdj)))
      obtain ⟨u, hu⟩ := hendVertex
      subst b
      have hvu : choice.vertex ≠ u := by
        intro hvu
        apply hpNotNil
        exact hp.nil_iff_eq.mpr (by simpa [hvu])
      have hendMissing : gamma ∈ MissingColors G sigmaPrev u ∨
          choice.color ∈ MissingColors G sigmaPrev u := by
        by_cases hg : gamma ∈ MissingColors G sigmaPrev u
        · exact Or.inl hg
        · right
          have hgp : gamma ∈ PresentColors G sigmaPrev u := by
            simpa [MissingColors] using hg
          by_contra hd
          have hdp : choice.color ∈ PresentColors G sigmaPrev u := by
            simpa [MissingColors] using hd
          obtain ⟨eg, heg, hcg⟩ := by simpa [PresentColors] using hgp
          obtain ⟨ed, hed, hcd⟩ := by simpa [PresentColors] using hdp
          have hag : H.Adj (Sum.inl u) (Sum.inr eg) := by
            simpa [H, TwoColorIncidenceGraph] using
              (show Incident G u eg ∧
                  (sigmaPrev eg = some gamma ∨
                    sigmaPrev eg = some choice.color) from
                ⟨heg, Or.inl hcg⟩)
          have had : H.Adj (Sum.inl u) (Sum.inr ed) := by
            simpa [H, TwoColorIncidenceGraph] using
              (show Incident G u ed ∧
                  (sigmaPrev ed = some gamma ∨
                    sigmaPrev ed = some choice.color) from
                ⟨hed, Or.inr hcd⟩)
          have heq : eg = ed := Sum.inr.inj (hendLeaf hag had)
          subst ed
          exact hgammaDeltaNe (Option.some.inj (hcg.symm.trans hcd))
      have huComponent : Sum.inl u ∈
          TwoColorComponent G sigmaPrev gamma choice.color
            (Sum.inl choice.vertex) := by
        rw [← hps]
        change Sum.inl u ∈ p.support
        simpa only [p.getVert_length] using p.getVert_mem_support p.length
      have huOutside : u ∉ TreeSequenceVertexSet
          (ett.series.data.tree q.succ.castSucc) := by
        intro huTree
        exact hvu.symm ((hcomponentPrev u huTree).mp huComponent)
      have hpNotOne : p.length ≠ 1 := by
        intro hone
        have hadj := p.adj_getVert_succ (i := 0) (by omega)
        have hend := p.getVert_length
        rw [hone] at hend
        rw [p.getVert_zero, hend] at hadj
        simp [H, TwoColorIncidenceGraph] at hadj
      have hnewExit : TreeExit
          (ett.series.data.tree q.succ.castSucc) sigmaPrev gamma
            choice.color choice.vertex := by
        refine ⟨u, p.reverse, ?_⟩
        unfold TreeExitPath
        refine ⟨hp.reverse, ?_, huOutside, hchoiceVertex,
          hendMissing, ?_⟩
        · simpa using (show 2 ≤ p.length by omega)
        · intro w hw
          constructor
          · intro hmem
            have hmem' : Sum.inl w ∈ p.support := by
              simpa [SimpleGraph.Walk.support_reverse] using hmem
            have hmemComponent : Sum.inl w ∈
                TwoColorComponent G sigmaPrev gamma choice.color
                  (Sum.inl choice.vertex) := by
              rw [← hps]
              exact hmem'
            exact (hcomponentPrev w hw).mp hmemComponent
          · intro hwv
            subst w
            simpa [SimpleGraph.Walk.support_reverse] using
              p.start_mem_support
      rcases hprefixCases with hzero | hpositivePrefix
      · rcases hzero with ⟨hroundOne, prefixInput, zeroPrefix,
            hzeroTree, hzeroColor⟩
        rcases heligible with hparallel | hsimple
        · have hrouteClosure : TashkinovAugmentationSequence sigma
              (ett.series.data.tree (Fin.last ett.rounds).castSucc)
              closureTree := hparallel.2.trans hclosure.1
          have hterminalClosure : TashkinovClosure sigma
              (ett.series.data.tree (Fin.last ett.rounds).castSucc)
              closureTree := ⟨hrouteClosure, hclosure.2⟩
          let zeroLast : Fin (0 + 1) := Fin.last 0
          let newStored : Finset (Fin k) := {choice.color, gamma}
          let newEdges : Finset E := {choice.edge}
          let newKind : Option TashkinovExtensionKind :=
            some TashkinovExtensionKind.PE
          let newVertex : Option V := some choice.vertex
          let newOutside : Option V := some choice.otherEndpoint
          let newDelta : Option (Fin k) := some choice.color
          let newGamma : Option (Fin k) := some gamma
          let appendedData := TashkinovSeriesDataAppend zeroPrefix.data
            closureTree sigma newStored newEdges newKind newVertex newOutside
            newDelta newGamma
          have happendLastTree : appendedData.tree (Fin.last 2) =
              closureTree := by
            simp only [appendedData, TashkinovSeriesDataAppend,
              Fin.lastCases_last]
          have happendLastColor : appendedData.coloring (Fin.last 1) =
              sigma := by
            simp only [appendedData, TashkinovSeriesDataAppend,
              Fin.lastCases_last]
          have happendLastStored : appendedData.stored (Fin.last 1) =
              newStored := by
            simp only [appendedData, TashkinovSeriesDataAppend,
              Fin.lastCases_last]
          have happendLastEdges : appendedData.connectingEdges (Fin.last 1) =
              newEdges := by
            simp only [appendedData, TashkinovSeriesDataAppend,
              Fin.lastCases_last]
          have happendLastKind : appendedData.kind (Fin.last 1) =
              newKind := by
            simp only [appendedData, TashkinovSeriesDataAppend,
              Fin.lastCases_last]
          have happendLastVertex : appendedData.chosenVertex (Fin.last 1) =
              newVertex := by
            simp only [appendedData, TashkinovSeriesDataAppend,
              Fin.lastCases_last]
          have happendLastOutside : appendedData.outsideVertex (Fin.last 1) =
              newOutside := by
            simp only [appendedData, TashkinovSeriesDataAppend,
              Fin.lastCases_last]
          have happendLastDelta : appendedData.delta (Fin.last 1) =
              newDelta := by
            simp only [appendedData, TashkinovSeriesDataAppend,
              Fin.lastCases_last]
          have happendLastGamma : appendedData.gamma (Fin.last 1) =
              newGamma := by
            simp only [appendedData, TashkinovSeriesDataAppend,
              Fin.lastCases_last]
          have hstoredZero : TashkinovStoredColors appendedData
              zeroLast.castSucc = TashkinovStoredColors zeroPrefix.data
                zeroLast := by
            exact TashkinovStoredColorsAppend zeroPrefix.data closureTree sigma
              newStored newEdges newKind newVertex newOutside newDelta newGamma
              zeroLast
          have happendTree : appendedData.tree zeroLast.succ.castSucc =
              ett.series.data.tree q.succ.castSucc := by
            calc
              appendedData.tree zeroLast.succ.castSucc =
                  zeroPrefix.data.tree (Fin.last 1) := by
                    simp only [appendedData, TashkinovSeriesDataAppend,
                      Fin.lastCases_castSucc]
                    congr 1
              _ = ett.series.data.tree (Fin.last ett.rounds).castSucc := hzeroTree
              _ = ett.series.data.tree q.succ.castSucc := by rw [hqSucc]
          have happendColor : appendedData.coloring zeroLast.castSucc =
              sigmaPrev := by
            calc
              appendedData.coloring zeroLast.castSucc =
                  zeroPrefix.data.coloring (Fin.last 0) := by
                    simp only [appendedData, TashkinovSeriesDataAppend,
                      Fin.lastCases_castSucc]
                    congr 1
              _ = sigmaPrev := hzeroColor
          have happendStored : TashkinovStoredColors appendedData
                zeroLast.castSucc =
              TashkinovStoredColors ett.series.data q.castSucc := by
            unfold TashkinovStoredColors
            simp [zeroLast, q, hroundOne]
          let appendedChoice : MaximumDefectiveChoice G e0
              (appendedData.tree zeroLast.succ.castSucc)
              (TashkinovStoredColors appendedData zeroLast.castSucc)
              (appendedData.coloring zeroLast.castSucc) := {
            selected := sigmaPrev
            selectedProper := hsigmaPrevProper
            selectedOneUncolored := hsigmaPrevOne
            selectedStable := by
              rw [happendTree, happendStored, happendColor]
              exact newChoice.selectedStable
            vertex := choice.vertex
            vertexDefective := by
              rw [happendTree]
              exact newChoice.vertexDefective
            maximal := by
              intro pi w hpiProper hpiOne hpiStable hw
              rw [happendTree, happendStored, happendColor] at hpiStable
              rw [happendTree] at hw ⊢
              exact newChoice.maximal pi w hpiProper hpiOne hpiStable hw
            edge := choice.edge
            edgeDefective := by
              rw [happendTree]
              exact newChoice.edgeDefective
            edgeIncident := choice.edgeIncident
            otherEndpoint := choice.otherEndpoint
            otherOutside := by
              rw [happendTree]
              exact newChoice.otherOutside
            edgeEnds := choice.edgeEnds
            color := choice.color
            edgeColor := newChoice.edgeColor }
          have hpeNoRevisitingZero : ¬ Nonempty
              (RevisitingExtensionCertificate appendedData
                zeroLast.castSucc) := by
            rintro ⟨cert⟩
            obtain ⟨oldCert, -, -, -, -, -⟩ :=
              (RevisitingExtensionCertificateAppend zeroPrefix.data
                closureTree sigma newStored newEdges newKind newVertex
                newOutside newDelta newGamma zeroLast).1 cert
            have hle := oldCert.earlierAtMost
            have hpos := oldCert.earlierPositive
            simp [zeroLast] at hle
            omega
          have hpeAlternativeZero : ∃ rho : PartialEdgeColoring E k,
              IsProperEdgeColoring G rho ∧ IsOneEdgeUncolored rho e0 ∧
                StableColoring (appendedData.tree zeroLast.succ.castSucc)
                  (insert appendedChoice.color
                    (TashkinovStoredColors appendedData zeroLast.castSucc))
                  appendedChoice.selected rho ∧
                ¬ Disjoint (MissingColors G rho appendedChoice.otherEndpoint)
                  (TreeMissingColors rho
                    (appendedData.tree zeroLast.succ.castSucc)) := by
            rcases hnewAlternativeFails with
              ⟨rho, hrhoProper, hrhoOne, hrhoStable, hrhoNotDisjoint⟩
            refine ⟨rho, hrhoProper, hrhoOne, ?_, ?_⟩
            · change StableColoring
                (appendedData.tree zeroLast.succ.castSucc)
                (insert choice.color
                  (TashkinovStoredColors appendedData zeroLast.castSucc))
                sigmaPrev rho
              rw [happendTree, happendStored]
              simpa [appendedChoice, newChoice] using hrhoStable
            · change ¬ Disjoint (MissingColors G rho choice.otherEndpoint)
                (TreeMissingColors rho
                  (appendedData.tree zeroLast.succ.castSucc))
              rw [happendTree]
              simpa [appendedChoice, newChoice] using hrhoNotDisjoint
          have hpeGammaRuleZero : ParallelExtensionColor appendedData
              zeroLast.castSucc appendedChoice.selected appendedChoice.vertex
              gamma := by
            rw [ParallelExtensionColorAppend zeroPrefix.data closureTree sigma
              newStored newEdges newKind newVertex newOutside newDelta newGamma
              zeroLast appendedChoice.selected appendedChoice.vertex gamma]
            refine ⟨?_, Or.inr ?_⟩
            · simpa [appendedChoice, newChoice] using hgammaPrevMissing
            · intro h hhPositive hhAtMost hhPE
              simp [zeroLast] at hhAtMost
              omega
          have hstrictClosure :
              (ett.series.data.tree (Fin.last ett.rounds).castSucc).length <
                closureTree.length := lt_of_lt_of_le hstrict hTstarClosure.1
          have lastStep : TashkinovSeriesStep G k 1 e0 prefixInput
              appendedData (Fin.last 1) := by
            have hlast : zeroLast.succ = Fin.last 1 := by
              apply Fin.ext
              rfl
            rw [← hlast]
            apply TashkinovSeriesStep.PE (i := zeroLast)
              (choice := appendedChoice) (gamma := gamma)
              (secondStable := sigmaPrev)
            · rw [happendColor]; exact hsigmaPrevProper
            · rw [happendColor]; exact hsigmaPrevOne
            · rw [happendColor, happendTree]; exact hclosedPrev
            · rw [happendColor, happendTree]; exact hnotStrongPrev
            · exact hpeNoRevisitingZero
            · exact hpeAlternativeZero
            · exact hpeGammaRuleZero
            · exact hsigmaPrevProper
            · exact hsigmaPrevOne
            · exact (sc2 G e0
                (appendedData.tree zeroLast.succ.castSucc)
                (insert appendedChoice.color
                  (TashkinovStoredColors appendedData zeroLast.castSucc))).refl
                ⟨sigmaPrev, hsigmaPrevProper, hsigmaPrevOne⟩
            · change TreeExit (appendedData.tree zeroLast.succ.castSucc)
                sigmaPrev gamma choice.color choice.vertex
              rw [happendTree]
              exact hnewExit
            · exact happendLastColor.trans hsigmaRecovered
            · rw [hlast, happendLastColor]
              exact hsigmaProper
            · rw [hlast, happendLastColor]
              exact hsigmaOne
            · exact happendLastStored.trans (by rfl)
            · exact happendLastEdges.trans (by rfl)
            · exact happendLastKind.trans (by rfl)
            · exact happendLastVertex.trans (by rfl)
            · exact happendLastOutside.trans (by rfl)
            · exact happendLastDelta.trans (by rfl)
            · exact happendLastGamma.trans (by rfl)
            · change TashkinovClosure
                (appendedData.coloring (Fin.last 1))
                (appendedData.tree zeroLast.succ.castSucc)
                (appendedData.tree (Fin.last 2))
              rw [happendLastColor, happendTree, happendLastTree]
              simpa [hqSucc] using hterminalClosure
            · change TreeSequenceInitialSegment
                (appendedData.tree zeroLast.succ.castSucc)
                (appendedData.tree (Fin.last 2))
              rw [happendTree]
              rw [happendLastTree]
              simpa [hqSucc] using hTnClosure
            · change (appendedData.tree zeroLast.succ.castSucc).length <
                (appendedData.tree (Fin.last 2)).length
              rw [happendTree]
              rw [happendLastTree]
              simpa [hqSucc] using hstrictClosure
          obtain ⟨extendedSeries, hextendedData⟩ :=
            TashkinovSeriesAppend G k 0 e0 prefixInput zeroPrefix closureTree
              sigma newStored newEdges newKind newVertex newOutside newDelta
              newGamma lastStep
          have hroundsEq : 0 + 1 = ett.rounds := by omega
          let castSeries {a b : ℕ} (h : a = b)
              (S : TashkinovSeries G k a e0 prefixInput) :
              TashkinovSeries G k b e0 prefixInput := by
            subst b
            exact S
          have castSeriesTree : ∀ {a b : ℕ} (h : a = b)
              (S : TashkinovSeries G k a e0 prefixInput)
              (i : Fin (b + 2)),
              (castSeries h S).data.tree i = S.data.tree
                (Fin.cast (congrArg (fun m : ℕ => m + 2) h.symm) i) := by
            intro a b h S i
            subst b
            rfl
          have castSeriesColoring : ∀ {a b : ℕ} (h : a = b)
              (S : TashkinovSeries G k a e0 prefixInput)
              (i : Fin (b + 1)),
              (castSeries h S).data.coloring i = S.data.coloring
                (Fin.cast (congrArg (fun m : ℕ => m + 1) h.symm) i) := by
            intro a b h S i
            subst b
            rfl
          have castSeriesStored : ∀ {a b : ℕ} (h : a = b)
              (S : TashkinovSeries G k a e0 prefixInput)
              (i : Fin (b + 1)),
              (castSeries h S).data.stored i = S.data.stored
                (Fin.cast (congrArg (fun m : ℕ => m + 1) h.symm) i) := by
            intro a b h S i
            subst b
            rfl
          have castSeriesEdges : ∀ {a b : ℕ} (h : a = b)
              (S : TashkinovSeries G k a e0 prefixInput)
              (i : Fin (b + 1)),
              (castSeries h S).data.connectingEdges i =
                S.data.connectingEdges
                  (Fin.cast (congrArg (fun m : ℕ => m + 1) h.symm) i) := by
            intro a b h S i
            subst b
            rfl
          have castSeriesKind : ∀ {a b : ℕ} (h : a = b)
              (S : TashkinovSeries G k a e0 prefixInput)
              (i : Fin (b + 1)),
              (castSeries h S).data.kind i = S.data.kind
                (Fin.cast (congrArg (fun m : ℕ => m + 1) h.symm) i) := by
            intro a b h S i
            subst b
            rfl
          let finalSeries : TashkinovSeries G k ett.rounds e0 prefixInput :=
            castSeries hroundsEq extendedSeries
          let rawTreeIndex (i : Fin (ett.rounds + 2)) : Fin 3 :=
            Fin.cast (congrArg (fun m : ℕ => m + 2) hroundsEq.symm) i
          let rawDataIndex (i : Fin (ett.rounds + 1)) : Fin 2 :=
            Fin.cast (congrArg (fun m : ℕ => m + 1) hroundsEq.symm) i
          have hrawPenultimate : rawTreeIndex
                (⟨ett.rounds, by omega⟩ : Fin (ett.rounds + 2)) =
              zeroLast.succ.castSucc := by
            apply Fin.ext
            simp [rawTreeIndex, zeroLast]
            omega
          have hrawFinalTree : rawTreeIndex (Fin.last (ett.rounds + 1)) =
              Fin.last 2 := by
            apply Fin.ext
            simp [rawTreeIndex]
          have hrawFinalData : rawDataIndex (Fin.last ett.rounds) =
              Fin.last 1 := by
            apply Fin.ext
            simp [rawDataIndex]
          have hfinalTree : finalSeries.data.tree
              (Fin.last (ett.rounds + 1)) = closureTree := by
            calc
              finalSeries.data.tree (Fin.last (ett.rounds + 1)) =
                  extendedSeries.data.tree
                    (rawTreeIndex (Fin.last (ett.rounds + 1))) := by
                    exact castSeriesTree hroundsEq extendedSeries _
              _ = appendedData.tree
                    (rawTreeIndex (Fin.last (ett.rounds + 1))) := by
                    rw [hextendedData]
              _ = appendedData.tree (Fin.last 2) := by rw [hrawFinalTree]
              _ = closureTree := happendLastTree
          have hpenultimateTree : finalSeries.data.tree
              (⟨ett.rounds, by omega⟩ : Fin (ett.rounds + 2)) =
                ett.series.data.tree (Fin.last ett.rounds).castSucc := by
            calc
              finalSeries.data.tree
                    (⟨ett.rounds, by omega⟩ : Fin (ett.rounds + 2)) =
                  extendedSeries.data.tree
                    (rawTreeIndex
                      (⟨ett.rounds, by omega⟩ : Fin (ett.rounds + 2))) := by
                    exact castSeriesTree hroundsEq extendedSeries _
              _ = appendedData.tree
                    (rawTreeIndex
                      (⟨ett.rounds, by omega⟩ : Fin (ett.rounds + 2))) := by
                    rw [hextendedData]
              _ = appendedData.tree zeroLast.succ.castSucc := by
                    rw [hrawPenultimate]
              _ = ett.series.data.tree q.succ.castSucc := happendTree
              _ = ett.series.data.tree (Fin.last ett.rounds).castSucc := by
                    rw [hqSucc]
          have hfinalColor : finalSeries.data.coloring
              (Fin.last ett.rounds) = sigma := by
            calc
              finalSeries.data.coloring (Fin.last ett.rounds) =
                  extendedSeries.data.coloring
                    (rawDataIndex (Fin.last ett.rounds)) := by
                    exact castSeriesColoring hroundsEq extendedSeries _
              _ = appendedData.coloring
                    (rawDataIndex (Fin.last ett.rounds)) := by
                    rw [hextendedData]
              _ = appendedData.coloring (Fin.last 1) := by rw [hrawFinalData]
              _ = sigma := happendLastColor
          have hprefixFields : ∀ (i : Fin (ett.rounds + 1)),
              i.val < ett.rounds →
              zeroPrefix.data.stored zeroLast = ett.series.data.stored i ∧
              zeroPrefix.data.connectingEdges zeroLast =
                ett.series.data.connectingEdges i ∧
              zeroPrefix.data.kind zeroLast = ett.series.data.kind i := by
            intro i hi
            have hiZero : i.val = 0 := by
              have hr := hroundOne
              omega
            have hiEq : i = 0 := Fin.ext hiZero
            subst i
            have hold := zeroPrefix.certified 0
            have hnew := ett.series.certified 0
            cases hold with
            | initial triple0 seedLength0 initialColoring0 initialStored0
                initialEdges0 initialKind0 initialVertex0 initialOutside0
                initialDelta0 initialGamma0 initialClosure0 =>
              cases hnew with
              | initial triple1 seedLength1 initialColoring1 initialStored1
                  initialEdges1 initialKind1 initialVertex1 initialOutside1
                  initialDelta1 initialGamma1 initialClosure1 =>
                exact ⟨by simpa [zeroLast] using
                    initialStored0.trans initialStored1.symm,
                  by simpa [zeroLast] using
                    initialEdges0.trans initialEdges1.symm,
                  by simpa [zeroLast] using
                    initialKind0.trans initialKind1.symm⟩
          have hseriesDataAgree : ∀ i : Fin (ett.rounds + 1),
              finalSeries.data.stored i = ett.series.data.stored i ∧
              finalSeries.data.connectingEdges i =
                ett.series.data.connectingEdges i ∧
              finalSeries.data.kind i = ett.series.data.kind i := by
            intro i
            by_cases hi : i.val < ett.rounds
            · have hraw : rawDataIndex i = zeroLast.castSucc := by
                apply Fin.ext
                have hiZero : i.val = 0 := by
                  have hr := hroundOne
                  omega
                exact hiZero
              have hp := hprefixFields i hi
              constructor
              · calc
                  finalSeries.data.stored i =
                      extendedSeries.data.stored (rawDataIndex i) := by
                        exact castSeriesStored hroundsEq extendedSeries i
                  _ = appendedData.stored (rawDataIndex i) := by
                        rw [hextendedData]
                  _ = zeroPrefix.data.stored zeroLast := by
                        rw [hraw]
                        simp only [appendedData, TashkinovSeriesDataAppend,
                          Fin.lastCases_castSucc]
                  _ = ett.series.data.stored i := hp.1
              · constructor
                · calc
                    finalSeries.data.connectingEdges i =
                        extendedSeries.data.connectingEdges
                          (rawDataIndex i) := by
                          exact castSeriesEdges hroundsEq extendedSeries i
                    _ = appendedData.connectingEdges (rawDataIndex i) := by
                          rw [hextendedData]
                    _ = zeroPrefix.data.connectingEdges zeroLast := by
                          rw [hraw]
                          simp only [appendedData, TashkinovSeriesDataAppend,
                            Fin.lastCases_castSucc]
                    _ = ett.series.data.connectingEdges i := hp.2.1
                · calc
                    finalSeries.data.kind i =
                        extendedSeries.data.kind (rawDataIndex i) := by
                          exact castSeriesKind hroundsEq extendedSeries i
                    _ = appendedData.kind (rawDataIndex i) := by
                          rw [hextendedData]
                    _ = zeroPrefix.data.kind zeroLast := by
                          rw [hraw]
                          simp only [appendedData, TashkinovSeriesDataAppend,
                            Fin.lastCases_castSucc]
                    _ = ett.series.data.kind i := hp.2.2
            · have hilast : i = Fin.last ett.rounds := by
                apply Fin.ext
                have hibound := i.isLt
                simp
                omega
              subst i
              constructor
              · calc
                  finalSeries.data.stored (Fin.last ett.rounds) =
                      extendedSeries.data.stored
                        (rawDataIndex (Fin.last ett.rounds)) := by
                        exact castSeriesStored hroundsEq extendedSeries _
                  _ = appendedData.stored
                        (rawDataIndex (Fin.last ett.rounds)) := by
                        rw [hextendedData]
                  _ = appendedData.stored (Fin.last 1) := by rw [hrawFinalData]
                  _ = newStored := happendLastStored
                  _ = {choice.color, gamma} := rfl
                  _ = ett.series.data.stored (Fin.last ett.rounds) := by
                        rw [← hqSucc]
                        exact currentStored.symm
              · constructor
                · calc
                    finalSeries.data.connectingEdges (Fin.last ett.rounds) =
                        extendedSeries.data.connectingEdges
                          (rawDataIndex (Fin.last ett.rounds)) := by
                          exact castSeriesEdges hroundsEq extendedSeries _
                    _ = appendedData.connectingEdges
                          (rawDataIndex (Fin.last ett.rounds)) := by
                          rw [hextendedData]
                    _ = appendedData.connectingEdges (Fin.last 1) := by
                          rw [hrawFinalData]
                    _ = newEdges := happendLastEdges
                    _ = {choice.edge} := rfl
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
                    _ = appendedData.kind (Fin.last 1) := by rw [hrawFinalData]
                    _ = newKind := happendLastKind
                    _ = some TashkinovExtensionKind.PE := rfl
                    _ = ett.series.data.kind (Fin.last ett.rounds) := by
                          rw [← hqSucc]
                          exact currentKind.symm
          have hseriesTreeAgree : ∀ j : Fin ett.rounds,
              finalSeries.data.tree j.succ.castSucc =
                ett.series.data.tree j.succ.castSucc := by
            intro j
            have hj : j.succ = Fin.last ett.rounds := by
              apply Fin.ext
              have hjbound := j.isLt
              simp
              have hr := hroundOne
              omega
            have htreeIndex : rawTreeIndex j.succ.castSucc =
                zeroLast.succ.castSucc := by
              apply Fin.ext
              simpa [rawTreeIndex, zeroLast] using congrArg Fin.val hj
            calc
              finalSeries.data.tree j.succ.castSucc =
                  extendedSeries.data.tree (rawTreeIndex j.succ.castSucc) := by
                    exact castSeriesTree hroundsEq extendedSeries _
              _ = appendedData.tree (rawTreeIndex j.succ.castSucc) := by
                    rw [hextendedData]
              _ = appendedData.tree zeroLast.succ.castSucc := by rw [htreeIndex]
              _ = ett.series.data.tree q.succ.castSucc := happendTree
              _ = ett.series.data.tree j.succ.castSucc := by
                    rw [hj, hqSucc]
          have hseriesColorProperties : ∀ i : Fin (ett.rounds + 1),
              IsProperEdgeColoring G (finalSeries.data.coloring i) ∧
                IsOneEdgeUncolored (finalSeries.data.coloring i) e0 := by
            intro i
            by_cases hi : i.val < ett.rounds
            · have hraw : rawDataIndex i = zeroLast.castSucc := by
                apply Fin.ext
                have hiZero : i.val = 0 := by
                  have hr := hroundOne
                  omega
                exact hiZero
              have hcolor : finalSeries.data.coloring i = sigmaPrev := by
                calc
                  finalSeries.data.coloring i =
                      extendedSeries.data.coloring (rawDataIndex i) := by
                        exact castSeriesColoring hroundsEq extendedSeries i
                  _ = appendedData.coloring (rawDataIndex i) := by
                        rw [hextendedData]
                  _ = appendedData.coloring zeroLast.castSucc := by rw [hraw]
                  _ = sigmaPrev := happendColor
              rw [hcolor]
              exact ⟨hsigmaPrevProper, hsigmaPrevOne⟩
            · have hilast : i = Fin.last ett.rounds := by
                apply Fin.ext
                have hibound := i.isLt
                simp
                omega
              subst i
              rw [hfinalColor]
              exact ⟨hsigmaProper, hsigmaOne⟩
          have hseriesStable : ∀ j : Fin ett.rounds,
              StableColoring (ett.series.data.tree j.succ.castSucc)
                (TashkinovStoredColors ett.series.data j.succ)
                (ett.series.data.coloring j.succ)
                (finalSeries.data.coloring j.succ) := by
            intro j
            have hj : j.succ = Fin.last ett.rounds := by
              apply Fin.ext
              have hjbound := j.isLt
              simp
              have hr := hroundOne
              omega
            rw [hj, hfinalColor]
            exact hsigmaStable
          let replacementETT : ExtendedTashkinovTree G k e0 prefixInput
              Tstar sigma := {
            rounds := ett.rounds
            roundsPositive := ett.roundsPositive
            series := finalSeries
            abovePenultimate := by rw [hpenultimateTree]; exact hTnTstar
            strictAbovePenultimate := by rw [hpenultimateTree]; exact hstrict
            belowFinal := by rw [hfinalTree]; exact hTstarClosure
            generatingColoring := hfinalColor.symm }
          refine ⟨{
            replacementInput := prefixInput
            replacementSeries := finalSeries
            replacementETT := replacementETT
            rungAgreement := rfl
            seriesPresentation := by dsimp [replacementETT]; rfl
            finalGeneratingColoring := hfinalColor.symm
            ladderTreesAgree := hseriesTreeAgree
            storedColorsAgree := fun i => (hseriesDataAgree i).1
            connectingEdgesAgree := fun i => (hseriesDataAgree i).2.1
            extensionKindsAgree := fun i => (hseriesDataAgree i).2.2
            replacementProper := fun i => (hseriesColorProperties i).1
            replacementOneUncolored := fun i => (hseriesColorProperties i).2
            replacementStable := hseriesStable }⟩
        · rcases hsimple.1 with hse | hre
          · have hbad := hpeKind.symm.trans (by simpa [hqSucc] using hse)
            cases hbad
          · have hbad := hpeKind.symm.trans (by simpa [hqSucc] using hre)
            cases hbad
      · rcases hpositivePrefix with ⟨hroundLarge, originalPrefix, hr,
            hprefixMP, hprefixTrees, hprefixData, corr, hcorrFinalTree,
            hcorrFinalColor, hcorrMP⟩
        let replacementLast : Fin (originalPrefix.rounds + 1) :=
          Fin.last originalPrefix.rounds
        have horiginalPositive : 0 < originalPrefix.rounds := by
          rw [hr]
          omega
        let previousReplacement : Fin originalPrefix.rounds :=
          ⟨originalPrefix.rounds - 1,
            Nat.sub_lt horiginalPositive (by omega)⟩
        have hpreviousSucc : previousReplacement.succ = replacementLast := by
          apply Fin.ext
          simp [previousReplacement, replacementLast]
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
        have htreeMissingEq : TreeMissingColors
              (corr.replacementSeries.data.coloring replacementLast)
              (corr.replacementSeries.data.tree replacementLast.castSucc) =
            TreeMissingColors
              (originalPrefix.series.data.coloring replacementLast)
              (originalPrefix.series.data.tree replacementLast.castSucc) := by
          have hstable := corr.replacementStable previousReplacement
          rw [hpreviousSucc] at hstable
          have htree := corr.ladderTreesAgree previousReplacement
          rw [hpreviousSucc] at htree
          rw [htree]
          ext c
          simp only [TreeMissingColors, Finset.mem_biUnion]
          constructor
          · rintro ⟨v, hv, hc⟩
            exact ⟨v, hv, (hstable.2 v hv).symm ▸ hc⟩
          · rintro ⟨v, hv, hc⟩
            exact ⟨v, hv, hstable.2 v hv ▸ hc⟩
        have hreplacementStored : TashkinovStoredColors
              corr.replacementSeries.data replacementLast =
            TashkinovStoredColors ett.series.data q.castSucc := by
          have hcorrStored : TashkinovStoredColors
                corr.replacementSeries.data replacementLast =
              TashkinovStoredColors originalPrefix.series.data
                replacementLast := by
            unfold TashkinovStoredColors
            have hnonzero : replacementLast.val ≠ 0 := by
              simp [replacementLast]
              exact Nat.ne_of_gt horiginalPositive
            rw [if_neg hnonzero, if_neg hnonzero]
            ext c
            simp only [Finset.mem_sdiff, Finset.mem_biUnion]
            constructor
            · rintro ⟨⟨j, hj, hc⟩, hn⟩
              refine ⟨⟨j, hj, ?_⟩, ?_⟩
              · by_cases hle : j.val ≤ replacementLast.val
                · simp only [if_pos hle] at hc ⊢
                  simpa [corr.storedColorsAgree j] using hc
                · simp only [if_neg hle] at hc ⊢
                  exact hc
              · rw [htreeMissingEq] at hn
                exact hn
            · rintro ⟨⟨j, hj, hc⟩, hn⟩
              refine ⟨⟨j, hj, ?_⟩, ?_⟩
              · by_cases hle : j.val ≤ replacementLast.val
                · simp only [if_pos hle] at hc ⊢
                  simpa [corr.storedColorsAgree j] using hc
                · simp only [if_neg hle] at hc ⊢
                  exact hc
              · rw [← htreeMissingEq] at hn
                exact hn
          calc
            TashkinovStoredColors corr.replacementSeries.data replacementLast =
                TashkinovStoredColors originalPrefix.series.data
                  replacementLast := hcorrStored
            _ = TashkinovStoredColors ett.series.data
                  (Fin.castLE (by omega) replacementLast) :=
              (hprefixData replacementLast).2.2.2.2
            _ = TashkinovStoredColors ett.series.data q.castSucc := by
              rw [hlastMap]
        let replacementChoice : MaximumDefectiveChoice G e0
            (corr.replacementSeries.data.tree replacementLast.succ)
            (TashkinovStoredColors corr.replacementSeries.data replacementLast)
            (corr.replacementSeries.data.coloring replacementLast) := {
          selected := sigmaPrev
          selectedProper := hsigmaPrevProper
          selectedOneUncolored := hsigmaPrevOne
          selectedStable := by
            rw [hreplacementCurrentTree, hreplacementStored, hcorrFinalColor]
            exact newChoice.selectedStable
          vertex := choice.vertex
          vertexDefective := by
            rw [hreplacementCurrentTree]
            exact newChoice.vertexDefective
          maximal := by
            intro pi w hpiProper hpiOne hpiStable hw
            rw [hreplacementCurrentTree, hreplacementStored, hcorrFinalColor]
              at hpiStable
            rw [hreplacementCurrentTree] at hw ⊢
            exact newChoice.maximal pi w hpiProper hpiOne hpiStable hw
          edge := choice.edge
          edgeDefective := by
            rw [hreplacementCurrentTree]
            exact newChoice.edgeDefective
          edgeIncident := choice.edgeIncident
          otherEndpoint := choice.otherEndpoint
          otherOutside := by
            rw [hreplacementCurrentTree]
            exact newChoice.otherOutside
          edgeEnds := choice.edgeEnds
          color := choice.color
          edgeColor := newChoice.edgeColor }
        have hnoRevisitingReplacement : ¬ Nonempty
            (RevisitingExtensionCertificate corr.replacementSeries.data
              replacementLast) := by
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
                  have hswapGraph : TwoColorIncidenceGraph G
                        (TwoColorComponentSwap G oldSecond oldGamma
                          oldChoice.color (Sum.inl oldChoice.vertex))
                        oldGamma oldChoice.color =
                      TwoColorIncidenceGraph G oldSecond oldGamma
                        oldChoice.color := by
                    ext x y
                    cases x with
                    | inl v =>
                        cases y with
                        | inl w => simp [TwoColorIncidenceGraph]
                        | inr f =>
                            by_cases hf : Sum.inr f ∈ TwoColorComponent G
                                oldSecond oldGamma oldChoice.color
                                (Sum.inl oldChoice.vertex)
                            · by_cases hfg : oldSecond f = some oldGamma
                              · simp [TwoColorIncidenceGraph,
                                  TwoColorComponentSwap, hf, hfg]
                              · by_cases hfd : oldSecond f =
                                    some oldChoice.color
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
                                oldSecond oldGamma oldChoice.color
                                (Sum.inl oldChoice.vertex)
                            · by_cases hfg : oldSecond f = some oldGamma
                              · simp [TwoColorIncidenceGraph,
                                  TwoColorComponentSwap, hf, hfg]
                              · by_cases hfd : oldSecond f =
                                    some oldChoice.color
                                · simp [TwoColorIncidenceGraph,
                                    TwoColorComponentSwap, hf, hfg, hfd]
                                · simp [TwoColorIncidenceGraph,
                                    TwoColorComponentSwap, hf, hfg, hfd]
                            · simp [TwoColorIncidenceGraph,
                                TwoColorComponentSwap, hf]
                        | inr g => simp [TwoColorIncidenceGraph]
                  have horiginalExitGraph : TwoColorIncidenceGraph G
                        (ett.series.data.coloring q.castSucc)
                        available.gamma available.delta =
                      TwoColorIncidenceGraph G oldSecond oldGamma
                        oldChoice.color := by
                    calc
                      TwoColorIncidenceGraph G
                          (ett.series.data.coloring q.castSucc)
                          available.gamma available.delta =
                        TwoColorIncidenceGraph G
                          (originalPrefix.series.data.coloring oldi.succ)
                          available.gamma available.delta :=
                            congrArg (fun phi => TwoColorIncidenceGraph G phi
                              available.gamma available.delta)
                              holdPostOriginal.symm
                      _ = TwoColorIncidenceGraph G
                          (TwoColorComponentSwap G oldSecond oldGamma
                            oldChoice.color (Sum.inl oldChoice.vertex))
                          available.gamma available.delta :=
                            congrArg (fun phi => TwoColorIncidenceGraph G phi
                              available.gamma available.delta)
                              oldCurrentColoring
                      _ = TwoColorIncidenceGraph G
                          (TwoColorComponentSwap G oldSecond oldGamma
                            oldChoice.color (Sum.inl oldChoice.vertex))
                          oldGamma oldChoice.color := by
                            rw [holdGammaAvailable, holdDeltaAvailable]
                      _ = TwoColorIncidenceGraph G oldSecond oldGamma
                          oldChoice.color := hswapGraph
                  have holdGammaSecond : oldGamma ∈ MissingColors G oldSecond
                      oldChoice.vertex := by
                    rw [oldSecondStable.2 oldChoice.vertex
                      oldChoice.vertexDefective.1]
                    exact oldGammaRule.1
                  have hcomponentOnly := TreeExitComponentMeetsTreeOnlyAtExit
                    (originalPrefix.series.data.tree oldi.succ.castSucc)
                    oldSecond oldGamma oldChoice.color oldChoice.vertex
                    oldSecondProper holdGammaSecond oldExit
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
                        TwoColorComponent G oldSecond oldGamma oldChoice.color
                          (Sum.inl oldChoice.vertex) := by
                      unfold TwoColorComponent at hreturnExitOriginal ⊢
                      rw [← horiginalExitGraph]
                      exact hreturnExitOriginal
                    exact hreturnNeOld
                      ((hcomponentOnly available.returnVertex
                        (by simpa only [holdIndex] using
                          hreturnInOldEarlier)).mp hreturnExitSecond)
                  have hQMeetsFinal : ∃ v ∈ TreeSequenceVertexSet
                      (originalPrefix.series.data.tree
                        (Fin.last (originalPrefix.rounds + 1))),
                      Sum.inl v ∈ TwoColorComponent G
                        (ett.series.data.coloring q.castSucc)
                        available.gamma available.delta
                        (Sum.inr available.edge) :=
                    ⟨available.returnVertex, hreturnInFinal, hreturnInQ⟩
                  have horiginalRoundsLess : originalPrefix.rounds <
                      ett.rounds := by
                    rw [hr]
                    omega
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
                  have hinterchangeLower := hlowerPackage.2.1
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
        have hpeAlternativeReplacement : ∃ rho : PartialEdgeColoring E k,
            IsProperEdgeColoring G rho ∧ IsOneEdgeUncolored rho e0 ∧
              StableColoring
                (corr.replacementSeries.data.tree replacementLast.succ)
                (insert replacementChoice.color
                  (TashkinovStoredColors corr.replacementSeries.data
                    replacementLast)) replacementChoice.selected rho ∧
              ¬ Disjoint
                (MissingColors G rho replacementChoice.otherEndpoint)
                (TreeMissingColors rho
                  (corr.replacementSeries.data.tree replacementLast.succ)) := by
          rcases hnewAlternativeFails with
            ⟨rho, hrhoProper, hrhoOne, hrhoStable, hrhoNotDisjoint⟩
          refine ⟨rho, hrhoProper, hrhoOne, ?_, ?_⟩
          · change StableColoring
              (corr.replacementSeries.data.tree replacementLast.succ)
              (insert choice.color
                (TashkinovStoredColors corr.replacementSeries.data
                  replacementLast)) sigmaPrev rho
            rw [hreplacementCurrentTree, hreplacementStored]
            simpa [replacementChoice, newChoice] using hrhoStable
          · change ¬ Disjoint (MissingColors G rho choice.otherEndpoint)
              (TreeMissingColors rho
                (corr.replacementSeries.data.tree replacementLast.succ))
            rw [hreplacementCurrentTree]
            simpa [replacementChoice, newChoice] using hrhoNotDisjoint
        have hpeGammaRuleReplacement : ParallelExtensionColor
            corr.replacementSeries.data replacementLast
            replacementChoice.selected replacementChoice.vertex gamma := by
          have retainedKind : ∀ j : Fin (originalPrefix.rounds + 1),
              corr.replacementSeries.data.kind j =
                ett.series.data.kind (Fin.castLE (by omega) j) := by
            intro j
            exact (corr.extensionKindsAgree j).trans
              (hprefixData j).2.2.2.1
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
            intro X C phi ch g second hsecondProper hsecondStable hgSelected
            dsimp
            have hgSecond : g ∈ MissingColors G second ch.vertex := by
              rw [hsecondStable.2 ch.vertex ch.vertexDefective.1]
              exact hgSelected
            have hedgeSecond : second ch.edge = some ch.color := by
              exact (hsecondStable.1 ch.edge
                ⟨ch.vertex, ch.vertexDefective.1, ch.edgeIncident⟩
                ⟨ch.color, Finset.mem_union_right _
                  (Finset.mem_insert_self _ _), ch.edgeColor⟩).trans ch.edgeColor
            have hne : g ≠ ch.color := by
              intro heq
              have hpresent : g ∈ PresentColors G second ch.vertex := by
                simp only [PresentColors, Finset.mem_filter, Finset.mem_univ,
                  true_and]
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
                hne hsecondProper (Sum.inl ch.vertex)).2.1 ch.vertex rfl hgSecond
            have hedgePost : TwoColorComponentSwap G second g ch.color
                (Sum.inl ch.vertex) ch.edge = some g := by
              simp [TwoColorComponentSwap, hedgeComponent, hedgeSecond,
                hne, hne.symm]
            have hgammaPresent : g ∈ PresentColors G
                (TwoColorComponentSwap G second g ch.color
                  (Sum.inl ch.vertex)) ch.vertex := by
              simp only [PresentColors, Finset.mem_filter, Finset.mem_univ,
                true_and]
              exact ⟨ch.edge, ch.edgeIncident, hedgePost⟩
            exact ⟨hmissingDelta,
              by simpa [MissingColors] using hgammaPresent, hne⟩
          have retainedPEFields : ∀ (j : Fin (originalPrefix.rounds + 1)),
              0 < j.val →
              corr.replacementSeries.data.kind j =
                some TashkinovExtensionKind.PE →
              corr.replacementSeries.data.chosenVertex j =
                  ett.series.data.chosenVertex (Fin.castLE (by omega) j) ∧
                corr.replacementSeries.data.delta j =
                  ett.series.data.delta (Fin.castLE (by omega) j) ∧
                corr.replacementSeries.data.gamma j =
                  ett.series.data.gamma (Fin.castLE (by omega) j) := by
            intro j hjPositive hjPE
            let fullj : Fin (ett.rounds + 1) := Fin.castLE (by omega) j
            have hfullPE : ett.series.data.kind fullj =
                some TashkinovExtensionKind.PE := by
              simpa [fullj] using (retainedKind j).symm.trans hjPE
            have hfullStep := ett.series.certified fullj
            generalize hfullTarget : fullj = fullTarget at hfullStep
            cases hfullStep with
            | initial triple seedLength initialColoring initialStored initialEdges
                initialKind initialVertex initialOutside initialDelta initialGamma
                initialClosure =>
                have hbad := initialKind.symm.trans
                  (by simpa [hfullTarget] using hfullPE)
                simp at hbad
            | SE fulli fullPreviousProper fullPreviousOne fullPreviousClosed
                fullPreviousNotStrong fullNoRE fullChoice fullAlternative
                fullCurrentColoring fullCurrentStored fullCurrentEdges
                fullCurrentKind fullCurrentVertex fullCurrentOutside
                fullCurrentDelta fullCurrentGamma fullAdjoined
                fullAdjoinedExactly fullClosed fullOrdered fullStrict =>
                have hbad := fullCurrentKind.symm.trans
                  (by simpa [hfullTarget] using hfullPE)
                cases hbad
            | RE fulli fullPreviousProper fullPreviousOne fullPreviousClosed
                fullPreviousNotStrong fullAvailable fullCurrentColoring
                fullCurrentStored fullCurrentEdges fullCurrentKind
                fullCurrentVertex fullCurrentOutside fullCurrentDelta
                fullCurrentGamma fullAdjoined fullAdjoinedExactly fullClosed
                fullOrdered fullStrict =>
                have hbad := fullCurrentKind.symm.trans
                  (by simpa [hfullTarget] using hfullPE)
                cases hbad
            | PE fulli fullPreviousProper fullPreviousOne fullPreviousClosed
                fullPreviousNotStrong fullNoRE fullChoice fullAlternativeFails
                fullGamma fullGammaRule fullSecond fullSecondProper fullSecondOne
                fullSecondStable fullExit fullCurrentColoring fullCurrentProper
                fullCurrentOne fullCurrentStored fullCurrentEdges fullCurrentKind
                fullCurrentVertex fullCurrentOutside fullCurrentDelta
                fullCurrentGamma fullClosed fullOrdered fullStrict =>
                have hfullIndex : fulli.succ = fullj := by
                  simpa using hfullTarget.symm
                have hnewStep := corr.replacementSeries.certified j
                generalize hnewTarget : j = newTarget at hnewStep
                cases hnewStep with
                | initial triple seedLength initialColoring initialStored
                    initialEdges initialKind initialVertex initialOutside
                    initialDelta initialGamma initialClosure =>
                    have hbad := initialKind.symm.trans
                      (by simpa [hnewTarget] using hjPE)
                    simp at hbad
                | SE newi newPreviousProper newPreviousOne newPreviousClosed
                    newPreviousNotStrong newNoRE newChoice newAlternative
                    newCurrentColoring newCurrentStored newCurrentEdges
                    newCurrentKind newCurrentVertex newCurrentOutside
                    newCurrentDelta newCurrentGamma newAdjoined
                    newAdjoinedExactly newClosed newOrdered newStrict =>
                    have hbad := newCurrentKind.symm.trans
                      (by simpa [hnewTarget] using hjPE)
                    cases hbad
                | RE newi newPreviousProper newPreviousOne newPreviousClosed
                    newPreviousNotStrong newAvailable newCurrentColoring
                    newCurrentStored newCurrentEdges newCurrentKind
                    newCurrentVertex newCurrentOutside newCurrentDelta
                    newCurrentGamma newAdjoined newAdjoinedExactly newClosed
                    newOrdered newStrict =>
                    have hbad := newCurrentKind.symm.trans
                      (by simpa [hnewTarget] using hjPE)
                    cases hbad
                | PE newi newPreviousProper newPreviousOne newPreviousClosed
                    newPreviousNotStrong newNoRE newChoice newAlternativeFails
                    newGamma newGammaRule newSecond newSecondProper newSecondOne
                    newSecondStable newExit newCurrentColoring newCurrentProper
                    newCurrentOne newCurrentStored newCurrentEdges newCurrentKind
                    newCurrentVertex newCurrentOutside newCurrentDelta
                    newCurrentGamma newClosed newOrdered newStrict =>
                    have hnewIndex : newi.succ = j := by
                      simpa using hnewTarget.symm
                    have hindexMap : Fin.castLE (by omega) newi.succ =
                        fulli.succ := by
                      apply Fin.ext
                      have hf := congrArg Fin.val hfullIndex
                      have hn := congrArg Fin.val hnewIndex
                      simp [fullj] at hf hn ⊢
                      omega
                    have htree :
                        corr.replacementSeries.data.tree newi.succ.castSucc =
                          ett.series.data.tree fulli.succ.castSucc := by
                      calc
                        corr.replacementSeries.data.tree newi.succ.castSucc =
                            originalPrefix.series.data.tree
                              newi.succ.castSucc := corr.ladderTreesAgree newi
                        _ = ett.series.data.tree
                              (Fin.castLE (by omega) newi.succ.castSucc) :=
                          hprefixTrees newi.succ.castSucc
                        _ = ett.series.data.tree fulli.succ.castSucc := by
                          congr 1
                          apply Fin.ext
                          have hf := congrArg Fin.val hfullIndex
                          have hn := congrArg Fin.val hnewIndex
                          simp [fullj] at hf hn ⊢
                          omega
                    let fullChoiceOnNew : MaximumDefectiveChoice G e0
                        (corr.replacementSeries.data.tree newi.succ.castSucc)
                        (TashkinovStoredColors ett.series.data fulli.castSucc)
                        (ett.series.data.coloring fulli.castSucc) :=
                      htree.symm ▸ fullChoice
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
                      (TashkinovStoredColors ett.series.data fulli.castSucc)
                      (ett.series.data.coloring fulli.castSucc) fullChoice
                    have hfullEdgeCast : fullChoiceOnNew.edge =
                        fullChoice.edge := htransport.1
                    have hfullVertexCast : fullChoiceOnNew.vertex =
                        fullChoice.vertex := htransport.2.1
                    have hfullOtherCast : fullChoiceOnNew.otherEndpoint =
                        fullChoice.otherEndpoint := htransport.2.2.1
                    have hfullColorCast : fullChoiceOnNew.color =
                        fullChoice.color := htransport.2.2.2
                    have hedgePairs : ({fullChoiceOnNew.edge} : Finset E) =
                        {newChoice.edge} := by
                      have hfullEdges : ett.series.data.connectingEdges fullj =
                          {fullChoice.edge} := by
                        simpa [hfullIndex] using fullCurrentEdges
                      have hnewEdges :
                          corr.replacementSeries.data.connectingEdges j =
                            {newChoice.edge} := by
                        simpa [hnewIndex] using newCurrentEdges
                      calc
                        {fullChoiceOnNew.edge} = {fullChoice.edge} := by
                          rw [hfullEdgeCast]
                        _ = ett.series.data.connectingEdges fullj :=
                          hfullEdges.symm
                        _ = originalPrefix.series.data.connectingEdges j :=
                          (hprefixData j).2.2.1.symm
                        _ = corr.replacementSeries.data.connectingEdges j :=
                          (corr.connectingEdgesAgree j).symm
                        _ = {newChoice.edge} := hnewEdges
                    have hcolorPairs :
                        ({fullChoiceOnNew.color, fullGamma} : Finset (Fin k)) =
                          {newChoice.color, newGamma} := by
                      have hfullStored : ett.series.data.stored fullj =
                          {fullChoice.color, fullGamma} := by
                        simpa [hfullIndex] using fullCurrentStored
                      have hnewStored : corr.replacementSeries.data.stored j =
                          {newChoice.color, newGamma} := by
                        simpa [hnewIndex] using newCurrentStored
                      calc
                        {fullChoiceOnNew.color, fullGamma} =
                            {fullChoice.color, fullGamma} := by rw [hfullColorCast]
                        _ = ett.series.data.stored fullj := hfullStored.symm
                        _ = originalPrefix.series.data.stored j :=
                          (hprefixData j).2.1.symm
                        _ = corr.replacementSeries.data.stored j :=
                          (corr.storedColorsAgree j).symm
                        _ = {newChoice.color, newGamma} := hnewStored
                    have hedgeIdentity : newChoice.edge =
                        fullChoiceOnNew.edge := by
                      apply Finset.mem_singleton.mp
                      rw [hedgePairs]
                      exact Finset.mem_singleton_self _
                    have hends : s(fullChoiceOnNew.vertex,
                          fullChoiceOnNew.otherEndpoint) =
                        s(newChoice.vertex, newChoice.otherEndpoint) := by
                      calc
                        s(fullChoiceOnNew.vertex,
                            fullChoiceOnNew.otherEndpoint) =
                            G.ends fullChoiceOnNew.edge :=
                          fullChoiceOnNew.edgeEnds.symm
                        _ = G.ends newChoice.edge :=
                          congrArg G.ends hedgeIdentity.symm
                        _ = s(newChoice.vertex, newChoice.otherEndpoint) :=
                          newChoice.edgeEnds
                    have hvertexIdentity : newChoice.vertex =
                        fullChoiceOnNew.vertex := by
                      rcases Sym2.eq_iff.mp hends with hstraight | hcross
                      · exact hstraight.1.symm
                      · exfalso
                        exact newChoice.otherOutside
                          (hcross.1 ▸ fullChoiceOnNew.vertexDefective.1)
                    have hotherIdentity : newChoice.otherEndpoint =
                        fullChoiceOnNew.otherEndpoint := by
                      rcases Sym2.eq_iff.mp hends with hstraight | hcross
                      · exact hstraight.2.symm
                      · exfalso
                        exact fullChoiceOnNew.otherOutside
                          (hcross.2 ▸ newChoice.vertexDefective.1)
                    obtain ⟨hfullDeltaMissing, hfullGammaNotMissing, -⟩ :=
                      pePostStatus
                        (ett.series.data.tree fulli.succ.castSucc)
                        (TashkinovStoredColors ett.series.data fulli.castSucc)
                        (ett.series.data.coloring fulli.castSucc) fullChoice
                        fullGamma fullSecond fullSecondProper fullSecondStable
                        fullGammaRule.1
                    obtain ⟨hnewDeltaMissing, hnewGammaNotMissing, -⟩ :=
                      pePostStatus
                        (corr.replacementSeries.data.tree newi.succ.castSucc)
                        (TashkinovStoredColors corr.replacementSeries.data
                          newi.castSucc)
                        (corr.replacementSeries.data.coloring newi.castSucc)
                        newChoice newGamma newSecond newSecondProper
                        newSecondStable newGammaRule.1
                    rw [← fullCurrentColoring] at hfullDeltaMissing hfullGammaNotMissing
                    rw [← newCurrentColoring] at hnewDeltaMissing hnewGammaNotMissing
                    have hprefixPostFull :
                        originalPrefix.series.data.coloring newi.succ =
                          ett.series.data.coloring fulli.succ := by
                      calc
                        originalPrefix.series.data.coloring newi.succ =
                            originalPrefix.series.data.coloring j := by
                          rw [hnewIndex]
                        _ = ett.series.data.coloring
                              (Fin.castLE (by omega) j) :=
                          (hprefixData j).1
                        _ = ett.series.data.coloring fulli.succ := by
                          congr 1
                    have hvPrefix : fullChoice.vertex ∈
                        TreeSequenceVertexSet
                          (originalPrefix.series.data.tree
                            newi.succ.castSucc) := by
                      rw [← corr.ladderTreesAgree newi]
                      simpa [hfullVertexCast] using
                        fullChoiceOnNew.vertexDefective.1
                    have hstableMissing :=
                      (corr.replacementStable newi).2 fullChoice.vertex hvPrefix
                    have hmissing : MissingColors G
                          (ett.series.data.coloring fulli.succ)
                          fullChoiceOnNew.vertex =
                        MissingColors G
                          (corr.replacementSeries.data.coloring newi.succ)
                          newChoice.vertex := by
                      calc
                        MissingColors G
                            (ett.series.data.coloring fulli.succ)
                            fullChoiceOnNew.vertex =
                            MissingColors G
                              (ett.series.data.coloring fulli.succ)
                              fullChoice.vertex := congrArg _ hfullVertexCast
                        _ = MissingColors G
                              (originalPrefix.series.data.coloring newi.succ)
                              fullChoice.vertex := congrArg
                                (fun phi => MissingColors G phi fullChoice.vertex)
                                hprefixPostFull.symm
                        _ = MissingColors G
                              (corr.replacementSeries.data.coloring newi.succ)
                              fullChoice.vertex := hstableMissing.symm
                        _ = MissingColors G
                              (corr.replacementSeries.data.coloring newi.succ)
                              newChoice.vertex := congrArg _
                                (hvertexIdentity.trans hfullVertexCast).symm
                    have hfullDeltaForIdentification :
                        fullChoiceOnNew.color ∈ MissingColors G
                          (ett.series.data.coloring fulli.succ)
                          fullChoiceOnNew.vertex := by
                      simpa only [hfullColorCast, hfullVertexCast] using
                        hfullDeltaMissing
                    have hfullGammaForIdentification : fullGamma ∉
                        MissingColors G
                          (ett.series.data.coloring fulli.succ)
                          fullChoiceOnNew.vertex := by
                      simpa only [hfullVertexCast] using hfullGammaNotMissing
                    have hidentified := TdEarlierPEWitnessIdentification G k e0
                      (corr.replacementSeries.data.tree newi.succ.castSucc)
                      (TashkinovStoredColors ett.series.data fulli.castSucc)
                      (TashkinovStoredColors corr.replacementSeries.data
                        newi.castSucc)
                      (ett.series.data.coloring fulli.castSucc)
                      (corr.replacementSeries.data.coloring newi.castSucc)
                      fullChoiceOnNew newChoice fullGamma newGamma
                      (ett.series.data.coloring fulli.succ)
                      (corr.replacementSeries.data.coloring newi.succ)
                      hedgePairs hcolorPairs hmissing
                      hfullDeltaForIdentification hfullGammaForIdentification
                      hnewDeltaMissing hnewGammaNotMissing
                    rcases hidentified with ⟨-, hidentifiedVertex, -,
                      hidentifiedDelta, hidentifiedGamma⟩
                    constructor
                    · calc
                        corr.replacementSeries.data.chosenVertex newi.succ =
                            some newChoice.vertex := newCurrentVertex
                        _ = some fullChoiceOnNew.vertex :=
                          congrArg some hidentifiedVertex
                        _ = some fullChoice.vertex :=
                          congrArg some hfullVertexCast
                        _ = ett.series.data.chosenVertex fulli.succ :=
                          fullCurrentVertex.symm
                        _ = ett.series.data.chosenVertex
                            (Fin.castLE (by omega) newi.succ) :=
                          congrArg _ hindexMap.symm
                    · constructor
                      · calc
                          corr.replacementSeries.data.delta newi.succ =
                              some newChoice.color := newCurrentDelta
                          _ = some fullChoiceOnNew.color :=
                            congrArg some hidentifiedDelta
                          _ = some fullChoice.color :=
                            congrArg some hfullColorCast
                          _ = ett.series.data.delta fulli.succ :=
                            fullCurrentDelta.symm
                          _ = ett.series.data.delta
                              (Fin.castLE (by omega) newi.succ) :=
                            congrArg _ hindexMap.symm
                      · calc
                          corr.replacementSeries.data.gamma newi.succ =
                              some newGamma := newCurrentGamma
                          _ = some fullGamma := congrArg some hidentifiedGamma
                          _ = ett.series.data.gamma fulli.succ :=
                            fullCurrentGamma.symm
                          _ = ett.series.data.gamma
                              (Fin.castLE (by omega) newi.succ) :=
                            congrArg _ hindexMap.symm
          refine ⟨?_, ?_⟩
          · simpa [replacementChoice] using hgammaPrevMissing
          · rcases gammaRule.2 with history | noHistory
            · rcases history with
                ⟨h, hhPositive, hhAtMost, hhPE, hhVertex, hhDelta, hhMax⟩
              let j : Fin (originalPrefix.rounds + 1) :=
                ⟨h.val, by
                  have hb := h.isLt
                  simp [hr, q] at hhAtMost ⊢
                  omega⟩
              have hjFull : Fin.castLE (by omega) j = h := by
                apply Fin.ext
                rfl
              have hjPE : corr.replacementSeries.data.kind j =
                  some TashkinovExtensionKind.PE := by
                rw [retainedKind j, hjFull]
                exact hhPE
              have hfields := retainedPEFields j hhPositive hjPE
              refine Or.inl ⟨j, hhPositive, ?_, hjPE, ?_, ?_, ?_⟩
              · simp [j, replacementLast, q, hr] at hhAtMost ⊢
                omega
              · rw [hfields.1, hjFull]
                exact hhVertex
              · rw [hfields.2.1, hjFull]
                exact hhDelta
              · intro r hrPositive hrAtMost hrPE hrVertex
                let fullr : Fin (ett.rounds + 1) := Fin.castLE (by omega) r
                have hrFields := retainedPEFields r hrPositive hrPE
                apply hhMax fullr
                · exact hrPositive
                · simp [fullr, replacementLast, q, hr] at hrAtMost ⊢
                  omega
                · simpa [fullr] using (retainedKind r).symm.trans hrPE
                · simpa [fullr, replacementChoice] using
                    hrFields.1.symm.trans hrVertex
            · refine Or.inr ?_
              intro j hjPositive hjAtMost hjPE
              intro hjVertex
              let fullj : Fin (ett.rounds + 1) := Fin.castLE (by omega) j
              have hfields := retainedPEFields j hjPositive hjPE
              apply noHistory fullj hjPositive
              · simp [fullj, replacementLast, q, hr] at hjAtMost ⊢
                omega
              · simpa [fullj] using (retainedKind j).symm.trans hjPE
              · simpa [fullj, replacementChoice] using
                  hfields.1.symm.trans hjVertex
        rcases heligible with hparallel | hsimple
        · have hrouteClosure : TashkinovAugmentationSequence sigma
              (ett.series.data.tree (Fin.last ett.rounds).castSucc)
              closureTree := hparallel.2.trans hclosure.1
          have hterminalClosure : TashkinovClosure sigma
              (ett.series.data.tree (Fin.last ett.rounds).castSucc)
              closureTree := ⟨hrouteClosure, hclosure.2⟩
          let newStored : Finset (Fin k) := {choice.color, gamma}
          let newEdges : Finset E := {choice.edge}
          let newKind : Option TashkinovExtensionKind :=
            some TashkinovExtensionKind.PE
          let newVertex : Option V := some choice.vertex
          let newOutside : Option V := some choice.otherEndpoint
          let newDelta : Option (Fin k) := some choice.color
          let newGamma : Option (Fin k) := some gamma
          let appendedData := TashkinovSeriesDataAppend
            corr.replacementSeries.data closureTree sigma newStored newEdges
            newKind newVertex newOutside newDelta newGamma
          have happendedTree :
              appendedData.tree replacementLast.succ.castSucc =
                corr.replacementSeries.data.tree replacementLast.succ := by
            simp only [appendedData, TashkinovSeriesDataAppend]
            exact Fin.lastCases_castSucc replacementLast.succ
          have happendedStored : TashkinovStoredColors appendedData
                replacementLast.castSucc =
              TashkinovStoredColors corr.replacementSeries.data
                replacementLast :=
            TashkinovStoredColorsAppend corr.replacementSeries.data
              closureTree sigma newStored newEdges newKind newVertex newOutside
              newDelta newGamma replacementLast
          have happendedColor : appendedData.coloring
                replacementLast.castSucc =
              corr.replacementSeries.data.coloring replacementLast := by
            simp [appendedData, TashkinovSeriesDataAppend]
          let appendedChoice : MaximumDefectiveChoice G e0
              (appendedData.tree replacementLast.succ.castSucc)
              (TashkinovStoredColors appendedData replacementLast.castSucc)
              (appendedData.coloring replacementLast.castSucc) := {
            selected := replacementChoice.selected
            selectedProper := replacementChoice.selectedProper
            selectedOneUncolored := replacementChoice.selectedOneUncolored
            selectedStable := by
              rw [happendedTree, happendedStored, happendedColor]
              exact replacementChoice.selectedStable
            vertex := replacementChoice.vertex
            vertexDefective := by
              rw [happendedTree]
              exact replacementChoice.vertexDefective
            maximal := by
              intro pi w hpiProper hpiOne hpiStable hw
              rw [happendedTree, happendedStored, happendedColor] at hpiStable
              rw [happendedTree] at hw ⊢
              exact replacementChoice.maximal pi w hpiProper hpiOne hpiStable hw
            edge := replacementChoice.edge
            edgeDefective := by
              rw [happendedTree]
              exact replacementChoice.edgeDefective
            edgeIncident := replacementChoice.edgeIncident
            otherEndpoint := replacementChoice.otherEndpoint
            otherOutside := by
              rw [happendedTree]
              exact replacementChoice.otherOutside
            edgeEnds := replacementChoice.edgeEnds
            color := replacementChoice.color
            edgeColor := replacementChoice.edgeColor }
          have hnoRevisitingAppended : ¬ Nonempty
              (RevisitingExtensionCertificate appendedData
                replacementLast.castSucc) := by
            rintro ⟨cert⟩
            obtain ⟨oldCert, -, -, -, -, -⟩ :=
              (RevisitingExtensionCertificateAppend
                corr.replacementSeries.data closureTree sigma newStored
                newEdges newKind newVertex newOutside newDelta newGamma
                replacementLast).1 cert
            exact hnoRevisitingReplacement ⟨oldCert⟩
          have hpeAlternativeAppended : ∃ rho : PartialEdgeColoring E k,
              IsProperEdgeColoring G rho ∧ IsOneEdgeUncolored rho e0 ∧
                StableColoring
                  (appendedData.tree replacementLast.succ.castSucc)
                  (insert appendedChoice.color
                    (TashkinovStoredColors appendedData
                      replacementLast.castSucc)) appendedChoice.selected rho ∧
                ¬ Disjoint
                  (MissingColors G rho appendedChoice.otherEndpoint)
                  (TreeMissingColors rho
                    (appendedData.tree replacementLast.succ.castSucc)) := by
            rcases hpeAlternativeReplacement with
              ⟨rho, hrhoProper, hrhoOne, hrhoStable, hrhoNotDisjoint⟩
            refine ⟨rho, hrhoProper, hrhoOne, ?_, ?_⟩
            · change StableColoring
                (appendedData.tree replacementLast.succ.castSucc)
                (insert replacementChoice.color
                  (TashkinovStoredColors appendedData
                    replacementLast.castSucc)) replacementChoice.selected rho
              rw [happendedTree, happendedStored]
              exact hrhoStable
            · change ¬ Disjoint
                (MissingColors G rho replacementChoice.otherEndpoint)
                (TreeMissingColors rho
                  (appendedData.tree replacementLast.succ.castSucc))
              rw [happendedTree]
              exact hrhoNotDisjoint
          have hpeGammaRuleAppended : ParallelExtensionColor appendedData
              replacementLast.castSucc appendedChoice.selected
              appendedChoice.vertex gamma := by
            rw [ParallelExtensionColorAppend corr.replacementSeries.data
              closureTree sigma newStored newEdges newKind newVertex newOutside
              newDelta newGamma replacementLast appendedChoice.selected
              appendedChoice.vertex gamma]
            simpa [appendedChoice, replacementChoice] using
              hpeGammaRuleReplacement
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
            rw [← hlast]
            apply TashkinovSeriesStep.PE (i := replacementLast)
              (choice := appendedChoice) (gamma := gamma)
              (secondStable := sigmaPrev)
            · rw [happendedColor, hcorrFinalColor]
              exact hsigmaPrevProper
            · rw [happendedColor, hcorrFinalColor]
              exact hsigmaPrevOne
            · rw [happendedColor, happendedTree, hcorrFinalColor,
                hreplacementCurrentTree]
              exact hclosedPrev
            · rw [happendedColor, happendedTree, hcorrFinalColor,
                hreplacementCurrentTree]
              exact hnotStrongPrev
            · exact hnoRevisitingAppended
            · exact hpeAlternativeAppended
            · exact hpeGammaRuleAppended
            · exact hsigmaPrevProper
            · exact hsigmaPrevOne
            · exact (sc2 G e0
                (appendedData.tree replacementLast.succ.castSucc)
                (insert appendedChoice.color
                  (TashkinovStoredColors appendedData
                    replacementLast.castSucc))).refl
                ⟨sigmaPrev, hsigmaPrevProper, hsigmaPrevOne⟩
            · change TreeExit
                (appendedData.tree replacementLast.succ.castSucc) sigmaPrev
                gamma choice.color choice.vertex
              rw [happendedTree, hreplacementCurrentTree]
              exact hnewExit
            · simp [appendedChoice, replacementChoice, appendedData,
                TashkinovSeriesDataAppend,
                hlast, hsigmaRecovered]
            · simpa [appendedData, TashkinovSeriesDataAppend, hlast] using
                hsigmaProper
            · simpa [appendedData, TashkinovSeriesDataAppend, hlast] using
                hsigmaOne
            · simp [appendedChoice, replacementChoice, appendedData,
                TashkinovSeriesDataAppend, newStored, hlast]
            · simp [appendedChoice, replacementChoice, appendedData,
                TashkinovSeriesDataAppend, newEdges, hlast]
            · simp [appendedData, TashkinovSeriesDataAppend, newKind, hlast]
            · simp [appendedChoice, replacementChoice, appendedData,
                TashkinovSeriesDataAppend, newVertex, hlast]
            · simp [appendedChoice, replacementChoice, appendedData,
                TashkinovSeriesDataAppend, newOutside, hlast]
            · simp [appendedChoice, replacementChoice, appendedData,
                TashkinovSeriesDataAppend, newDelta, hlast]
            · simp [appendedData, TashkinovSeriesDataAppend, newGamma, hlast]
            · change TashkinovClosure
                (appendedData.coloring replacementLast.succ)
                (appendedData.tree replacementLast.succ.castSucc)
                (appendedData.tree replacementLast.succ.succ)
              rw [happendedTree, hreplacementCurrentTree]
              simpa [appendedData, TashkinovSeriesDataAppend, hlast, hqSucc]
                using hterminalClosure
            · change TreeSequenceInitialSegment
                (appendedData.tree replacementLast.succ.castSucc)
                (appendedData.tree (Fin.last (originalPrefix.rounds + 2)))
              rw [happendedTree, hreplacementCurrentTree]
              simpa [appendedData, TashkinovSeriesDataAppend, hqSucc] using
                hTnClosure
            · change (appendedData.tree replacementLast.succ.castSucc).length <
                (appendedData.tree
                  (Fin.last (originalPrefix.rounds + 2))).length
              rw [happendedTree, hreplacementCurrentTree]
              simpa [appendedData, TashkinovSeriesDataAppend, hqSucc] using
                hstrictClosure
          obtain ⟨extendedSeries, hextendedData⟩ :=
            TashkinovSeriesAppend G k originalPrefix.rounds e0
              corr.replacementInput corr.replacementSeries closureTree sigma
              newStored newEdges newKind newVertex newOutside newDelta newGamma
              lastStep
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
                    (Fin.last ett.rounds).castSucc := by
                exact hreplacementCurrentTree.trans
                  (congrArg ett.series.data.tree
                    (congrArg Fin.castSucc hqSucc))
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
                  _ = {choice.color, gamma} := rfl
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
                    _ = {choice.edge} := rfl
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
                    _ = some TashkinovExtensionKind.PE := rfl
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
        · rcases hsimple.1 with hse | hre
          · have hbad := hpeKind.symm.trans (by simpa [hqSucc] using hse)
            cases hbad
          · have hbad := hpeKind.symm.trans (by simpa [hqSucc] using hre)
            cases hbad
