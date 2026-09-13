import Tablet.ETTFirstAppearanceIndex
import Tablet.EarlierPECycleFirstNonrevisitingInternal
import Tablet.ColoredVertexSetClosed
import Tablet.ColoredVertexSetElementary
import Tablet.CertifiedETTRestriction
import Tablet.ExtensionRulesPEFirstAppearanceBound
import Tablet.HkuMissingStoredMonotone
import Tablet.HkuParallelBoundaryStructure
import Tablet.InternalEdges
import Tablet.ExtendedTashkinovTree
import Tablet.IsOneEdgeUncolored
import Tablet.IsProperEdgeColoring
import Tablet.MaximumProperty
import Tablet.MaximumDefectiveChoice
import Tablet.MissingColors
import Tablet.ParallelExtensionColor
import Tablet.PresentColors
import Tablet.RevisitingExtensionCertificate
import Tablet.SameColorSeriesPreserved
import Tablet.StableColoring
import Tablet.TashkinovExtensionKind
import Tablet.TashkinovSeries
import Tablet.TashkinovSeriesStep
import Tablet.TashkinovStoredColors
import Tablet.TechnicalTheoremBase
import Tablet.TreeInterchangeable
import Tablet.TreeExit
import Tablet.TreeExitComponentMeetsTreeOnlyAtExit
import Tablet.TreeExitPath
import Tablet.TreeMissingColors
import Tablet.TreeSequence
import Tablet.TreeSequenceInitialSegment
import Tablet.TreeSequenceVertexSet
import Tablet.TreeSequenceInitialSegmentVertexSetSubset
import Tablet.TwoColorComponent
import Tablet.TwoColorComponentCycle
import Tablet.TwoColorComponentSwap
import Tablet.TwoColorComponentsDisjoint
import Tablet.TwoColorInterchangeableDistinctComponentCycle
import Tablet.TwoColorIncidenceDegreeAtMostTwo
import Tablet.TwoColorIncidenceGraph
import Tablet.sc1

-- [TABLET NODE: ExtensionRulesTerminalStoredDisjoint]
theorem ExtensionRulesTerminalStoredDisjoint {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (generating : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T generating)
    (hMP : MaximumProperty ett) (hpositive : 0 < ett.rounds)
    (hLowerOne : ∀ {T' : TreeSequence G e0}
      {generating' : PartialEdgeColoring E k}
      (lower : ExtendedTashkinovTree G k e0 input T' generating'),
      0 < lower.rounds → lower.rounds < ett.rounds → MaximumProperty lower →
      ColoredVertexSetElementary G generating'
        (TreeSequenceVertexSet T'))
    (hLowerTwo : ∀ {T' : TreeSequence G e0}
      {generating' : PartialEdgeColoring E k}
      (lower : ExtendedTashkinovTree G k e0 input T' generating'),
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
           TreeInterchangeable G Tnext sigma alpha beta))
    (r : Fin ett.rounds) (vn vr : V)
    (hrEarlier : r.succ ≠ Fin.last ett.rounds)
    (hvnvr : vn ≠ vr)
    (hkindn : ett.series.data.kind (Fin.last ett.rounds) =
      some TashkinovExtensionKind.PE)
    (hkindr : ett.series.data.kind r.succ = some TashkinovExtensionKind.PE)
    (hvertexn : ett.series.data.chosenVertex (Fin.last ett.rounds) = some vn)
    (hvertexr : ett.series.data.chosenVertex r.succ = some vr)
    (hvn : vn ∈ TreeSequenceVertexSet T) (hvr : vr ∈ TreeSequenceVertexSet T)
    (hfirst : ETTFirstAppearanceIndex ett vn hvn =
      ETTFirstAppearanceIndex ett vr hvr) :
    Disjoint (ett.series.data.stored (Fin.last ett.rounds))
      (ett.series.data.stored r.succ) := by
-- BODY
  classical
  letI : DecidableEq V := Classical.decEq V
  have segmentRefl (A : TreeSequence G e0) : TreeSequenceInitialSegment A A :=
    ⟨le_rfl, (by intro i; rfl), (by intro i; rfl)⟩
  have segmentTrans {A B C : TreeSequence G e0}
      (hAB : TreeSequenceInitialSegment A B)
      (hBC : TreeSequenceInitialSegment B C) :
      TreeSequenceInitialSegment A C := by
    rcases hAB with ⟨hab, hvab, heab⟩
    rcases hBC with ⟨hbc, hvbc, hebc⟩
    refine ⟨hab.trans hbc, ?_, ?_⟩
    · intro i
      simpa using (hvbc (Fin.castLE (Nat.succ_le_succ hab) i)).trans (hvab i)
    · intro i
      simpa using (hebc (Fin.castLE hab i)).trans (heab i)
  have stepSegment : ∀ i : Fin (ett.rounds + 1), 0 < i.val →
      TreeSequenceInitialSegment (ett.series.data.tree i.castSucc)
        (ett.series.data.tree i.succ) := by
    intro i hi
    cases ett.series.certified i with
    | initial => simpa using hi
    | SE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => assumption
    | PE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => assumption
    | RE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => assumption
  have stageToStage (a b : ℕ) (ha : 1 ≤ a) (hab : a ≤ b)
      (hb : b ≤ ett.rounds) :
      TreeSequenceInitialSegment
        (ett.series.data.tree ⟨a, by omega⟩)
        (ett.series.data.tree ⟨b, by omega⟩) := by
    have chain (d : ℕ) (hd : a + d ≤ b) :
        TreeSequenceInitialSegment
          (ett.series.data.tree ⟨a, by omega⟩)
          (ett.series.data.tree ⟨a + d, by omega⟩) := by
      induction d with
      | zero => simpa using segmentRefl (ett.series.data.tree ⟨a, by omega⟩)
      | succ d ih =>
          have hprev := ih (by omega)
          let idx : Fin (ett.rounds + 1) := ⟨a + d, by omega⟩
          have hnext := stepSegment idx (by dsimp [idx]; omega)
          have hnext' : TreeSequenceInitialSegment
              (ett.series.data.tree ⟨a + d, by omega⟩)
              (ett.series.data.tree ⟨a + (d + 1), by omega⟩) := by
            simpa [idx, Nat.add_assoc] using hnext
          exact segmentTrans hprev hnext'
    have hchain := chain (b - a) (by omega)
    convert hchain using 1 <;> apply congrArg ett.series.data.tree <;>
      apply Fin.ext <;> simp <;> omega
  have boundaryIncident {A : TreeSequence G e0} {f : E}
      (hf : f ∈ BoundaryEdges G (TreeSequenceVertexSet A)) :
      TreeIncidentEdge A f := by
    simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ,
      true_and] at hf
    rcases hf with ⟨u, hu, v, hv, huv⟩
    exact ⟨u, hu, by simp [Incident, huv]⟩
  have controlCarry (r : Fin ett.rounds) (p : Fin ett.rounds)
      (hrp : r.val < p.val) :
      TreeMissingColors (ett.series.data.coloring r.succ)
            (ett.series.data.tree r.succ.succ) ∪
          TashkinovStoredColors ett.series.data r.succ ⊆
        TreeMissingColors (ett.series.data.coloring p.castSucc)
            (ett.series.data.tree p.succ.castSucc) ∪
          TashkinovStoredColors ett.series.data p.castSucc := by
    have carryNat : ∀ n : ℕ, r.val + 1 ≤ n → n < ett.rounds →
        ∀ q : Fin ett.rounds, q.val = n →
        TreeMissingColors (ett.series.data.coloring r.succ)
              (ett.series.data.tree r.succ.succ) ∪
            TashkinovStoredColors ett.series.data r.succ ⊆
          TreeMissingColors (ett.series.data.coloring q.castSucc)
              (ett.series.data.tree q.succ.castSucc) ∪
            TashkinovStoredColors ett.series.data q.castSucc := by
      intro n hn
      induction n, hn using Nat.le_induction with
      | base =>
          intro hnround q hq
          have hqeq : q.castSucc = r.succ := by
            apply Fin.ext
            simp only [Fin.val_castSucc, Fin.val_succ]
            omega
          have htree : q.succ.castSucc = r.succ.succ := by
            apply Fin.ext
            simp only [Fin.val_castSucc, Fin.val_succ]
            omega
          simpa [hqeq, htree]
      | succ n hn ih =>
          intro hnround q hq
          let prev : Fin ett.rounds := ⟨n, by omega⟩
          have hold := ih (by omega) prev rfl
          have hfirst := (HkuMissingStoredMonotone G k ett.rounds e0 input
            ett.series prev).1
          have hsecond := (HkuMissingStoredMonotone G k ett.rounds e0 input
            ett.series prev).2
          intro c hc
          have hc1 := hold hc
          have hc2 := hfirst hc1
          have hc3 := hsecond hc2
          have hcolor : q.castSucc = prev.succ := by apply Fin.ext; simp [prev]; omega
          have htree : q.succ.castSucc = prev.succ.succ := by
            apply Fin.ext
            simp [prev]
            omega
          simpa [hcolor, htree] using hc3
    exact carryNat p.val (by omega) p.isLt p rfl
  generalize hrTarget : r.succ = targetR
  have certR := ett.series.certified targetR
  cases certR with
  | initial triple seedLength initialColoring initialStored initialEdges
      initialKind initialVertex initialOutside initialDelta initialGamma
      initialClosure => exact (Fin.succ_ne_zero r hrTarget).elim
  | SE i previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternative
      currentColoring currentStored currentEdges currentKind currentVertex
      currentOutside currentDelta currentGamma adjoined adjoinedExactly
      closedExtension orderedExtension strictExtension =>
      have hbad := currentKind.symm.trans (by simpa [hrTarget] using hkindr)
      simp at hbad
  | RE i previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed available currentColoring currentStored
      currentEdges currentKind currentVertex currentOutside currentDelta
      currentGamma adjoined adjoinedExactly closedExtension orderedExtension
      strictExtension =>
      have hbad := currentKind.symm.trans (by simpa [hrTarget] using hkindr)
      simp at hbad
  | PE i previousProperR previousOneR previousClosedR previousNotStrongR
      noRevisitingR choiceR seriesAlternativeFailsR gammaR gammaRuleR
      secondStableR secondProperR secondOneR secondRelationR exitR
      currentColoringR currentProperR currentOneR currentStoredR currentEdgesR
      currentKindR currentVertexR currentOutsideR currentDeltaR currentGammaR
      closedExtensionR orderedExtensionR strictExtensionR =>
    have hi : i = r := by
      apply Fin.ext
      simpa using (congrArg Fin.val hrTarget).symm
    subst i
    have hvrChoice : choiceR.vertex = vr :=
      Option.some.inj (currentVertexR.symm.trans (by simpa [hrTarget] using hvertexr))
    subst vr
    generalize hnTarget : Fin.last ett.rounds = targetN
    have certN := ett.series.certified targetN
    cases certN with
    | initial triple seedLength initialColoring initialStored initialEdges
        initialKind initialVertex initialOutside initialDelta initialGamma
        initialClosure =>
        have hv := congrArg Fin.val hnTarget
        simp at hv
        omega
    | SE q previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed noRevisiting choice seriesAlternative
        currentColoring currentStored currentEdges currentKind currentVertex
        currentOutside currentDelta currentGamma adjoined adjoinedExactly
        closedExtension orderedExtension strictExtension =>
        have hbad := currentKind.symm.trans (by simpa [hnTarget] using hkindn)
        simp at hbad
    | RE q previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed available currentColoring currentStored
        currentEdges currentKind currentVertex currentOutside currentDelta
        currentGamma adjoined adjoinedExactly closedExtension orderedExtension
        strictExtension =>
        have hbad := currentKind.symm.trans (by simpa [hnTarget] using hkindn)
        simp at hbad
    | PE q previousProperN previousOneN previousClosedN previousNotStrongN
        noRevisitingN choiceN seriesAlternativeFailsN gammaN gammaRuleN
        secondStableN secondProperN secondOneN secondRelationN exitN
        currentColoringN currentProperN currentOneN currentStoredN currentEdgesN
        currentKindN currentVertexN currentOutsideN currentDeltaN currentGammaN
        closedExtensionN orderedExtensionN strictExtensionN =>
      have hvnChoice : choiceN.vertex = vn :=
        Option.some.inj (currentVertexN.symm.trans
          (by simpa [hnTarget] using hvertexn))
      subst vn
      have hqLast : q.succ = Fin.last ett.rounds := hnTarget.symm
      have hrBefore : r.val + 1 < ett.rounds := by
        have hle : r.succ.val ≤ (Fin.last ett.rounds).val :=
          Fin.le_last r.succ
        have hne : r.succ.val ≠ (Fin.last ett.rounds).val := by
          intro heq
          exact hrEarlier (Fin.ext heq)
        simpa using lt_of_le_of_ne hle hne
      let Th := ett.series.data.tree r.succ.castSucc
      let Thnext := ett.series.data.tree r.succ.succ
      have hvnTh : choiceN.vertex ∈ TreeSequenceVertexSet Th := by
        have hboundR := ExtensionRulesPEFirstAppearanceBound G k e0 input T
          generating ett r choiceR.vertex
          (by simpa [hrTarget] using hkindr)
          (by simpa [hrTarget] using hvertexr) hvr
        have hboundN : ETTFirstAppearanceIndex ett choiceN.vertex hvn ≤
            r.val + 1 := by
          rw [hfirst]
          exact hboundR
        let candidates : Finset (Fin (ett.rounds + 1)) :=
          Finset.univ.filter fun a =>
            choiceN.vertex ∈ TreeSequenceVertexSet
              (ExtendedTashkinovLadderStage ett a)
        have hlastStage : ExtendedTashkinovLadderStage ett
            (Fin.last ett.rounds) = T := by
          unfold ExtendedTashkinovLadderStage
          exact Fin.lastCases_last
        have hcandidates : candidates.Nonempty := by
          refine ⟨Fin.last ett.rounds, ?_⟩
          simp only [candidates, Finset.mem_filter, Finset.mem_univ, true_and]
          rw [hlastStage]
          exact hvn
        let m := candidates.min' hcandidates
        have hmMem : m ∈ candidates := Finset.min'_mem candidates hcandidates
        have hmVal : m.val ≤ r.val := by
          unfold ETTFirstAppearanceIndex at hboundN
          dsimp at hboundN
          change m.val + 1 ≤ r.val + 1 at hboundN
          omega
        let s : Fin ett.rounds := ⟨m.val, by omega⟩
        have hsm : s.castSucc = m := by apply Fin.ext; rfl
        have hvMin : choiceN.vertex ∈ TreeSequenceVertexSet
            (ett.series.data.tree s.succ.castSucc) := by
          have hmStage : choiceN.vertex ∈ TreeSequenceVertexSet
              (ExtendedTashkinovLadderStage ett m) := by
            simpa [candidates] using hmMem
          rw [← hsm] at hmStage
          simpa [ExtendedTashkinovLadderStage, Fin.lastCases_castSucc] using hmStage
        have hseg : TreeSequenceInitialSegment
            (ett.series.data.tree s.succ.castSucc) Th := by
          have hs := stageToStage (s.val + 1) (r.val + 1)
            (by omega) (by simpa [s] using hmVal) (by omega)
          convert hs using 1 <;> apply congrArg ett.series.data.tree <;>
            apply Fin.ext <;> simp [Th, s]
        exact TreeSequenceInitialSegmentVertexSetSubset hseg hvMin
      have hgammaMissingR : gammaR ∈ MissingColors G secondStableR
          choiceR.vertex := by
        rw [secondRelationR.2 choiceR.vertex choiceR.vertexDefective.1]
        exact gammaRuleR.1
      have hchoiceBoundaryR : choiceR.edge ∈
          BoundaryEdges G (TreeSequenceVertexSet Th) := by
        rcases choiceR.edgeDefective with ⟨c, hc, he⟩
        simpa [Th, BoundaryColorEdges] using (Finset.mem_filter.mp he).1
      have hchoiceSecondR : secondStableR choiceR.edge = some choiceR.color := by
        exact (secondRelationR.1 choiceR.edge
          ⟨choiceR.vertex, by simpa [Th] using choiceR.vertexDefective.1,
            choiceR.edgeIncident⟩
          ⟨choiceR.color, Finset.mem_union_right _
            (Finset.mem_insert_self _ _), choiceR.edgeColor⟩).trans
          choiceR.edgeColor
      have hgammaNeR : gammaR ≠ choiceR.color := by
        intro heq
        have hp : gammaR ∈ PresentColors G secondStableR choiceR.vertex := by
          simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨choiceR.edge, choiceR.edgeIncident, by simpa [heq] using hchoiceSecondR⟩
        have hnot : gammaR ∉ PresentColors G secondStableR choiceR.vertex := by
          simpa [MissingColors] using hgammaMissingR
        exact hnot hp
      have hclosedSelectedR : ColoredVertexSetClosed G choiceR.selected
          (TreeSequenceVertexSet Th) := by
        intro f c x hf hx hfc hmiss
        have hmissOld : c ∈ MissingColors G
            (ett.series.data.coloring r.castSucc) x := by
          rw [← choiceR.selectedStable.2 x (by simpa [Th] using hx)]
          exact hmiss
        have htreeOld : c ∈ TreeMissingColors
            (ett.series.data.coloring r.castSucc) Th := by
          simp only [TreeMissingColors, Finset.mem_biUnion]
          exact ⟨x, hx, hmissOld⟩
        have heq := (sc1 G e0 Th
          (TashkinovStoredColors ett.series.data r.castSucc)
          (ett.series.data.coloring r.castSucc) choiceR.selected
          previousProperR previousOneR choiceR.selectedProper
          choiceR.selectedOneUncolored).mp choiceR.selectedStable f
            (boundaryIncident hf)
            (Or.inr ⟨c, Finset.mem_union_left _ htreeOld, hfc⟩)
        exact previousClosedR (by simpa [Th] using hf) hx (heq.symm.trans hfc)
          hmissOld
      have hclosedSecondR : ColoredVertexSetClosed G secondStableR
          (TreeSequenceVertexSet Th) := by
        intro f c x hf hx hfc hmiss
        have hmissSel : c ∈ MissingColors G choiceR.selected x := by
          rw [← secondRelationR.2 x hx]
          exact hmiss
        have htreeSel : c ∈ TreeMissingColors choiceR.selected Th := by
          simp only [TreeMissingColors, Finset.mem_biUnion]
          exact ⟨x, hx, hmissSel⟩
        have heq := (sc1 G e0 Th
          (insert choiceR.color
            (TashkinovStoredColors ett.series.data r.castSucc))
          choiceR.selected secondStableR choiceR.selectedProper
          choiceR.selectedOneUncolored secondProperR secondOneR).mp
          secondRelationR f (boundaryIncident hf)
            (Or.inr ⟨c, Finset.mem_union_left _ htreeSel, hfc⟩)
        exact hclosedSelectedR hf hx (heq.symm.trans hfc) hmissSel
      have helemPrevR : ColoredVertexSetElementary G
          (ett.series.data.coloring r.castSucc) (TreeSequenceVertexSet Th) := by
        by_cases hrzero : r.val = 0
        · have hr0 : r = ⟨0, by omega⟩ := Fin.ext hrzero
          have hbase : ColoredVertexSetElementary G
              (ett.series.data.coloring 0)
              (TreeSequenceVertexSet
                (ett.series.data.tree ⟨1, by omega⟩)) :=
            (TechnicalTheoremBase G k ett.rounds e0 input ett.series).1
          simpa [Th, hr0] using hbase
        · obtain ⟨lower, hlowerRounds, hlowerMP, htree, hdata⟩ :=
            CertifiedETTRestriction G k e0 input T generating ett hMP r.val
              (by omega) r.isLt
          have helem : ColoredVertexSetElementary G
              (ett.series.data.coloring ⟨r.val, by omega⟩)
              (TreeSequenceVertexSet
                (ett.series.data.tree ⟨r.val + 1, by omega⟩)) :=
            hLowerOne lower (by omega) (by simpa [hlowerRounds]) hlowerMP
          have hcolorIndex : (⟨r.val, by omega⟩ : Fin (ett.rounds + 1)) =
              r.castSucc := by apply Fin.ext; rfl
          have htreeIndex : (⟨r.val + 1, by omega⟩ :
              Fin (ett.rounds + 2)) = r.succ.castSucc := by
            apply Fin.ext
            simp
          rw [hcolorIndex, htreeIndex] at helem
          simpa [Th] using helem
      have helemSecondR : ColoredVertexSetElementary G secondStableR
          (TreeSequenceVertexSet Th) := by
        intro u hu v hv huv
        have hd := helemPrevR hu hv huv
        simpa only [← choiceR.selectedStable.2 u hu,
          ← choiceR.selectedStable.2 v hv,
          ← secondRelationR.2 u hu, ← secondRelationR.2 v hv] using hd
      have hgammaNotMissingN : gammaR ∉ MissingColors G secondStableR
          choiceN.vertex := by
        intro hm
        have hd := helemSecondR hvnTh
          (by simpa [Th] using choiceR.vertexDefective.1) hvnvr
        exact (Finset.disjoint_left.mp hd) hm hgammaMissingR
      have hdeltaNotMissingN : choiceR.color ∉ MissingColors G secondStableR
          choiceN.vertex :=
        hclosedSecondR hchoiceBoundaryR hvnTh hchoiceSecondR
      obtain ⟨f, hfInc, hfColor⟩ : ∃ f : E, Incident G choiceN.vertex f ∧
          secondStableR f = some gammaR := by
        have hp : gammaR ∈ PresentColors G secondStableR choiceN.vertex := by
          simpa [MissingColors] using hgammaNotMissingN
        simpa [PresentColors] using hp
      obtain ⟨g, hgInc, hgColor⟩ : ∃ g : E, Incident G choiceN.vertex g ∧
          secondStableR g = some choiceR.color := by
        have hp : choiceR.color ∈ PresentColors G secondStableR choiceN.vertex := by
          simpa [MissingColors] using hdeltaNotMissingN
        simpa [PresentColors] using hp
      have hcomponentOnly := TreeExitComponentMeetsTreeOnlyAtExit Th secondStableR
        gammaR choiceR.color choiceR.vertex secondProperR hgammaMissingR exitR
      have hcompDistinct : TwoColorComponent G secondStableR gammaR choiceR.color
          (Sum.inl choiceR.vertex) ≠
          TwoColorComponent G secondStableR gammaR choiceR.color
            (Sum.inl choiceN.vertex) := by
        intro heq
        have hmem : Sum.inl choiceN.vertex ∈
            TwoColorComponent G secondStableR gammaR choiceR.color
              (Sum.inl choiceR.vertex) := by
          rw [heq]
          rfl
        exact hvnvr ((hcomponentOnly choiceN.vertex hvnTh).mp hmem)
      have hpathR : TwoColorPathComponent G secondStableR gammaR choiceR.color
          (Sum.inl choiceR.vertex) := by
        refine ⟨hgammaNeR, Sum.inl choiceR.vertex, rfl, ?_⟩
        intro x hx y hy
        cases x with
        | inl x => simp [SimpleGraph.mem_neighborSet, TwoColorIncidenceGraph] at hx
        | inr ex =>
          cases y with
          | inl y => simp [SimpleGraph.mem_neighborSet, TwoColorIncidenceGraph] at hy
          | inr ey =>
            simp only [SimpleGraph.mem_neighborSet, TwoColorIncidenceGraph] at hx hy
            have hex : secondStableR ex = some choiceR.color :=
              hx.2.resolve_left (by
                intro he
                have hnot : gammaR ∉ PresentColors G secondStableR
                    choiceR.vertex := by
                  simpa [MissingColors] using hgammaMissingR
                exact hnot (by simp [PresentColors]; exact ⟨ex, hx.1, he⟩))
            have hey : secondStableR ey = some choiceR.color :=
              hy.2.resolve_left (by
                intro he
                have hnot : gammaR ∉ PresentColors G secondStableR
                    choiceR.vertex := by
                  simpa [MissingColors] using hgammaMissingR
                exact hnot (by simp [PresentColors]; exact ⟨ey, hy.1, he⟩))
            by_cases he : ex = ey
            · exact congrArg Sum.inr he
            · exact (secondProperR he ⟨choiceR.vertex, hx.1, hy.1⟩ hex hey).elim
      have swapColorsR (e : E) :
          (TwoColorComponentSwap G secondStableR gammaR choiceR.color
              (Sum.inl choiceR.vertex) e = some gammaR ∨
            TwoColorComponentSwap G secondStableR gammaR choiceR.color
              (Sum.inl choiceR.vertex) e = some choiceR.color) ↔
          (secondStableR e = some gammaR ∨
            secondStableR e = some choiceR.color) := by
        unfold TwoColorComponentSwap
        by_cases hc : Sum.inr e ∈ TwoColorComponent G secondStableR gammaR
            choiceR.color (Sum.inl choiceR.vertex)
        · rw [if_pos hc]
          by_cases hg : secondStableR e = some gammaR
          · simp [hg, hgammaNeR, hgammaNeR.symm]
          · by_cases hd : secondStableR e = some choiceR.color
            · simp [hg, hd, hgammaNeR, hgammaNeR.symm]
            · simp [hg, hd]
        · rw [if_neg hc]
      have graphSwapR : TwoColorIncidenceGraph G
          (TwoColorComponentSwap G secondStableR gammaR choiceR.color
            (Sum.inl choiceR.vertex)) gammaR choiceR.color =
          TwoColorIncidenceGraph G secondStableR gammaR choiceR.color := by
        ext x y
        cases x with
        | inl x =>
          cases y with
          | inl y => simp [TwoColorIncidenceGraph]
          | inr e =>
            simp only [TwoColorIncidenceGraph]
            exact and_congr Iff.rfl (swapColorsR e)
        | inr e =>
          cases y with
          | inl y =>
            simp only [TwoColorIncidenceGraph]
            exact and_congr Iff.rfl (swapColorsR e)
          | inr f => simp [TwoColorIncidenceGraph]
      have graphCurrentR : TwoColorIncidenceGraph G
          (ett.series.data.coloring r.succ) gammaR choiceR.color =
          TwoColorIncidenceGraph G secondStableR gammaR choiceR.color := by
        rw [currentColoringR]
        exact graphSwapR
      have componentCurrentR (z : Sum V E) :
          TwoColorComponent G (ett.series.data.coloring r.succ) gammaR
              choiceR.color z =
            TwoColorComponent G secondStableR gammaR choiceR.color z := by
        unfold TwoColorComponent
        rw [graphCurrentR]
      have hpathCurrentR : TwoColorPathComponent G
          (ett.series.data.coloring r.succ) gammaR choiceR.color
          (Sum.inl choiceR.vertex) := by
        rcases hpathR with ⟨hne, x, hx, hsub⟩
        refine ⟨hne, x, ?_, ?_⟩
        · rw [componentCurrentR]
          exact hx
        · rw [graphCurrentR]
          exact hsub
      have hdeltaCurrentR : choiceR.color ∈ MissingColors G
          (ett.series.data.coloring r.succ) choiceR.vertex := by
        rw [currentColoringR]
        apply Finset.mem_sdiff.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        intro hp
        simp only [PresentColors, Finset.mem_filter, Finset.mem_univ,
          true_and] at hp
        rcases hp with ⟨e, he, hec⟩
        have heComp : Sum.inr e ∈ TwoColorComponent G secondStableR gammaR
            choiceR.color (Sum.inl choiceR.vertex) := by
          apply SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
          by_cases hge : secondStableR e = some gammaR
          · exact (by simp [TwoColorIncidenceGraph, he, hge])
          · by_cases hde : secondStableR e = some choiceR.color
            · exact (by simp [TwoColorIncidenceGraph, he, hde])
            · simp [TwoColorComponentSwap, hge, hde] at hec
        rw [TwoColorComponentSwap] at hec
        simp only [if_pos heComp] at hec
        by_cases hge : secondStableR e = some gammaR
        · have hnot : gammaR ∉ PresentColors G secondStableR
              choiceR.vertex := by
            simpa [MissingColors] using hgammaMissingR
          exact hnot (by simp [PresentColors]; exact ⟨e, he, hge⟩)
        · by_cases hde : secondStableR e = some choiceR.color
          · simp [hge, hde, hgammaNeR, hgammaNeR.symm] at hec
          · exact hde (by simpa [hge, hde] using hec)
      have hinterR : TreeInterchangeable G Thnext
          (ett.series.data.coloring r.succ) gammaR choiceR.color := by
        obtain ⟨lower, hlowerRounds, hlowerMP, htree, hdata⟩ :=
          CertifiedETTRestriction G k e0 input T generating ett hMP
            (r.val + 1) (by omega) hrBefore
        have hcolorRaw := (hdata (Fin.last lower.rounds)).1
        have htreeLast := htree (Fin.last (lower.rounds + 1))
        have hcolor : lower.series.data.coloring (Fin.last lower.rounds) =
            ett.series.data.coloring r.succ := by
          calc
            _ = ett.series.data.coloring
                (Fin.castLE (by omega) (Fin.last lower.rounds)) := hcolorRaw
            _ = ett.series.data.coloring r.succ := by
              congr 1
              apply Fin.ext
              simp [hlowerRounds]
        have htreeEq : lower.series.data.tree
            (Fin.last (lower.rounds + 1)) = Thnext := by
          calc
            _ = ett.series.data.tree
                (Fin.castLE (by omega) (Fin.last (lower.rounds + 1))) := htreeLast
            _ = Thnext := by
              congr 1
              apply Fin.ext
              simp [Thnext, hlowerRounds]
        have hinter := hLowerTwo lower (by omega)
          (by simpa [hlowerRounds]) hlowerMP
        dsimp at hinter
        have hstableRefl : StableColoring
            (lower.series.data.tree (Fin.last (lower.rounds + 1)))
            (TashkinovStoredColors lower.series.data (Fin.last lower.rounds))
            (lower.series.data.coloring (Fin.last lower.rounds))
            (lower.series.data.coloring (Fin.last lower.rounds)) := by
          unfold StableColoring
          exact ⟨(by intros; rfl), (by intros; rfl)⟩
        have hmissingLower : choiceR.color ∈ TreeMissingColors
            (lower.series.data.coloring (Fin.last lower.rounds))
            (lower.series.data.tree (Fin.last (lower.rounds + 1))) := by
          simp only [TreeMissingColors, Finset.mem_biUnion]
          refine ⟨choiceR.vertex, ?_, ?_⟩
          · have hvNext : choiceR.vertex ∈ TreeSequenceVertexSet Thnext :=
              TreeSequenceInitialSegmentVertexSetSubset orderedExtensionR
                (by simpa [Th] using choiceR.vertexDefective.1)
            rw [htreeEq]
            exact hvNext
          · have hm : choiceR.color ∈ MissingColors G
                (ett.series.data.coloring r.succ) choiceR.vertex := hdeltaCurrentR
            rw [hcolor]
            exact hm
        have result := hinter
          (lower.series.data.coloring (Fin.last lower.rounds))
          (by rw [hcolor]; exact currentProperR)
          (by rw [hcolor]; exact currentOneR)
          hstableRefl gammaR choiceR.color (Or.inr hmissingLower)
        rw [htreeEq, hcolor] at result
        exact result
      have hrVertexNext : choiceR.vertex ∈ TreeSequenceVertexSet Thnext :=
        TreeSequenceInitialSegmentVertexSetSubset orderedExtensionR
          (by simpa [Th] using choiceR.vertexDefective.1)
      have hnVertexNext : choiceN.vertex ∈ TreeSequenceVertexSet Thnext :=
        TreeSequenceInitialSegmentVertexSetSubset orderedExtensionR hvnTh
      have cycleComp := TwoColorInterchangeableDistinctComponentCycle G Thnext
        (ett.series.data.coloring r.succ) gammaR choiceR.color currentProperR
        (Sum.inl choiceR.vertex) (Sum.inl choiceN.vertex) hpathCurrentR hinterR
        ⟨choiceR.vertex, hrVertexNext, by rw [componentCurrentR]; rfl⟩
        ⟨choiceN.vertex, hnVertexNext, by rw [componentCurrentR]; rfl⟩
        (by simpa only [componentCurrentR] using hcompDistinct)
      rcases cycleComp with ⟨cycle, hcycleSupport⟩
      have hfQ : Sum.inr f ∈ TwoColorComponent G secondStableR gammaR
          choiceR.color (Sum.inl choiceN.vertex) := by
        apply SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
        simp [TwoColorIncidenceGraph, hfInc, hfColor]
      have hgQ : Sum.inr g ∈ TwoColorComponent G secondStableR gammaR
          choiceR.color (Sum.inl choiceN.vertex) := by
        apply SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
        simp [TwoColorIncidenceGraph, hgInc, hgColor]
      have hfNotP : Sum.inr f ∉ TwoColorComponent G secondStableR gammaR
          choiceR.color (Sum.inl choiceR.vertex) := by
        intro hfP
        apply hcompDistinct
        apply Set.Subset.antisymm
        · intro x hx
          change (TwoColorIncidenceGraph G secondStableR gammaR choiceR.color).connectedComponentMk x = _ at hx ⊢
          exact hx.trans ((show Sum.inr f ∈ TwoColorComponent G secondStableR
            gammaR choiceR.color (Sum.inl choiceR.vertex) from hfP).symm.trans hfQ)
        · intro x hx
          change (TwoColorIncidenceGraph G secondStableR gammaR choiceR.color).connectedComponentMk x = _ at hx ⊢
          exact hx.trans (hfQ.symm.trans hfP)
      have hgNotP : Sum.inr g ∉ TwoColorComponent G secondStableR gammaR
          choiceR.color (Sum.inl choiceR.vertex) := by
        intro hgP
        apply hcompDistinct
        apply Set.Subset.antisymm
        · intro x hx
          change (TwoColorIncidenceGraph G secondStableR gammaR choiceR.color).connectedComponentMk x = _ at hx ⊢
          exact hx.trans (hgP.symm.trans hgQ)
        · intro x hx
          change (TwoColorIncidenceGraph G secondStableR gammaR choiceR.color).connectedComponentMk x = _ at hx ⊢
          exact hx.trans (hgQ.symm.trans hgP)
      have hfCurrent : ett.series.data.coloring r.succ f = some gammaR := by
        rw [currentColoringR]
        simpa [TwoColorComponentSwap, hfNotP] using hfColor
      have hgCurrent : ett.series.data.coloring r.succ g = some choiceR.color := by
        rw [currentColoringR]
        simpa [TwoColorComponentSwap, hgNotP] using hgColor
      have hfCycle : Sum.inr f ∈ cycle.walk.support := by
        rw [hcycleSupport, componentCurrentR]
        exact hfQ
      have hgCycle : Sum.inr g ∈ cycle.walk.support := by
        rw [hcycleSupport, componentCurrentR]
        exact hgQ
      have hcycleMeets : ∃ v ∈ TreeSequenceVertexSet
          (ett.series.data.tree r.succ.castSucc),
          Sum.inl v ∈ cycle.walk.support := by
        refine ⟨choiceN.vertex, hvnTh, ?_⟩
        rw [hcycleSupport, componentCurrentR]
        rfl
      obtain ⟨p, hrp, hpKind, hpRevisiting, hpColor, hpInternal⟩ :=
        EarlierPECycleFirstNonrevisitingInternal G k ett.rounds e0 input
          ett.series r hrEarlier gammaR choiceR.color
          (by simpa [hrTarget] using hkindr)
          (by simpa [hrTarget] using currentGammaR)
          (by simpa [hrTarget] using currentDeltaR)
          cycle hcycleMeets hkindn
      have hdeltaControlR : choiceR.color ∈
          TreeMissingColors (ett.series.data.coloring r.succ) Thnext ∪
            TashkinovStoredColors ett.series.data r.succ := by
        apply Finset.mem_union_left
        simp only [TreeMissingColors, Finset.mem_biUnion]
        exact ⟨choiceR.vertex, hrVertexNext, hdeltaCurrentR⟩
      have hgammaControlR : gammaR ∈
          TreeMissingColors (ett.series.data.coloring r.succ) Thnext ∪
            TashkinovStoredColors ett.series.data r.succ := by
        by_cases hm : gammaR ∈ TreeMissingColors
            (ett.series.data.coloring r.succ) Thnext
        · exact Finset.mem_union_left _ hm
        · apply Finset.mem_union_right
          have hmTh : gammaR ∉ TreeMissingColors
              (ett.series.data.coloring r.succ) Th := by
            intro hmOld
            apply hm
            simp only [TreeMissingColors, Finset.mem_biUnion] at hmOld ⊢
            rcases hmOld with ⟨v, hv, hvm⟩
            exact ⟨v, TreeSequenceInitialSegmentVertexSetSubset
              orderedExtensionR hv, hvm⟩
          unfold TashkinovStoredColors
          have hrsucc : r.succ.val ≠ 0 := by simp
          rw [if_neg hrsucc]
          simp only [Finset.mem_sdiff]
          refine ⟨?_, hmTh⟩
          simp only [Finset.mem_biUnion]
          refine ⟨r.succ, Finset.mem_univ _, ?_⟩
          simp [currentStoredR]
      have hdeltaControlP := controlCarry r p hrp hdeltaControlR
      have hgammaControlP := controlCarry r p hrp hgammaControlR
      have hfInternal := hpInternal f hfCycle
      have hgInternal := hpInternal g hgCycle
      have hfIncidentP : TreeIncidentEdge
          (ett.series.data.tree p.succ.castSucc) f := by
        refine ⟨choiceN.vertex, ?_, hfInc⟩
        simpa [InternalEdges] using
          (Finset.mem_filter.mp hfInternal).2 choiceN.vertex hfInc
      have hgIncidentP : TreeIncidentEdge
          (ett.series.data.tree p.succ.castSucc) g := by
        refine ⟨choiceN.vertex, ?_, hgInc⟩
        simpa [InternalEdges] using
          (Finset.mem_filter.mp hgInternal).2 choiceN.vertex hgInc
      have hfAtP : ett.series.data.coloring p.castSucc f = some gammaR := by
        rw [hpColor]
        exact hfCurrent
      have hgAtP : ett.series.data.coloring p.castSucc g = some choiceR.color := by
        rw [hpColor]
        exact hgCurrent
      have hpq : p.val ≤ q.val := by
        have hqv := congrArg Fin.val hqLast
        simp at hqv
        omega
      have hfFinalRaw := (SameColorSeriesPreserved G k ett.rounds e0 input
        ett.series p q hpq f gammaR hfIncidentP hfAtP
        (by simpa [Thnext] using hgammaControlP)).2 hfInternal
      have hgFinalRaw := (SameColorSeriesPreserved G k ett.rounds e0 input
        ett.series p q hpq g choiceR.color hgIncidentP hgAtP
        (by simpa [Thnext] using hdeltaControlP)).2 hgInternal
      have hfFinal : ett.series.data.coloring (Fin.last ett.rounds) f =
          some gammaR := by
        rw [← hqLast]
        exact hfFinalRaw.trans hfAtP
      have hgFinal : ett.series.data.coloring (Fin.last ett.rounds) g =
          some choiceR.color := by
        rw [← hqLast]
        exact hgFinalRaw.trans hgAtP
      have hchoiceBoundaryN : choiceN.edge ∈ BoundaryEdges G
          (TreeSequenceVertexSet
            (ett.series.data.tree (Fin.last ett.rounds).castSucc)) := by
        rcases choiceN.edgeDefective with ⟨c, hc, he⟩
        have hb := (Finset.mem_filter.mp he).1
        simpa [hqLast] using hb
      have hchoiceSecondN : secondStableN choiceN.edge = some choiceN.color := by
        exact (secondRelationN.1 choiceN.edge
          ⟨choiceN.vertex, choiceN.vertexDefective.1, choiceN.edgeIncident⟩
          ⟨choiceN.color, Finset.mem_union_right _
            (Finset.mem_insert_self _ _), choiceN.edgeColor⟩).trans
          choiceN.edgeColor
      have hgammaMissingN : gammaN ∈ MissingColors G secondStableN
          choiceN.vertex := by
        rw [secondRelationN.2 choiceN.vertex choiceN.vertexDefective.1]
        exact gammaRuleN.1
      have hgammaNeN : gammaN ≠ choiceN.color := by
        intro heq
        have hp : gammaN ∈ PresentColors G secondStableN choiceN.vertex := by
          simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨choiceN.edge, choiceN.edgeIncident, by simpa [heq] using hchoiceSecondN⟩
        have hnot : gammaN ∉ PresentColors G secondStableN choiceN.vertex := by
          simpa [MissingColors] using hgammaMissingN
        exact hnot hp
      have hchoiceCompN : Sum.inr choiceN.edge ∈
          TwoColorComponent G secondStableN gammaN choiceN.color
            (Sum.inl choiceN.vertex) := by
        apply SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
        simp [TwoColorIncidenceGraph, choiceN.edgeIncident, hchoiceSecondN]
      have hparallelN := HkuParallelBoundaryStructure G k ett.rounds e0 input
        ett.series q choiceN.edge choiceN.color gammaN choiceN.vertex
        currentKindN currentEdgesN currentDeltaN currentGammaN currentVertexN
      have hchoiceCurrentQ : ett.series.data.coloring q.succ choiceN.edge =
          some gammaN := by
        have hm : choiceN.edge ∈ BoundaryColorEdges G
            (ett.series.data.coloring q.succ)
            (TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc))
            gammaN := by
          rw [hparallelN.1]
          simp
        exact (Finset.mem_filter.mp hm).2
      have hchoiceCurrentN : ett.series.data.coloring
          (Fin.last ett.rounds) choiceN.edge = some gammaN := by
        rw [← hqLast]
        exact hchoiceCurrentQ
      have hdeltaMissingN : choiceN.color ∈ MissingColors G
          (ett.series.data.coloring (Fin.last ett.rounds)) choiceN.vertex := by
        rw [← hqLast, currentColoringN]
        apply Finset.mem_sdiff.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        intro hpresent
        simp only [PresentColors, Finset.mem_filter, Finset.mem_univ,
          true_and] at hpresent
        rcases hpresent with ⟨e, he, hec⟩
        have heComp : Sum.inr e ∈ TwoColorComponent G secondStableN gammaN
            choiceN.color (Sum.inl choiceN.vertex) := by
          apply SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
          by_cases hge : secondStableN e = some gammaN
          · exact (by simp [TwoColorIncidenceGraph, he, hge])
          · by_cases hde : secondStableN e = some choiceN.color
            · exact (by simp [TwoColorIncidenceGraph, he, hde])
            · simp [TwoColorComponentSwap, hge, hde] at hec
        rw [TwoColorComponentSwap] at hec
        simp only [if_pos heComp] at hec
        by_cases hge : secondStableN e = some gammaN
        · have hnot : gammaN ∉ PresentColors G secondStableN
              choiceN.vertex := by
            simpa [MissingColors] using hgammaMissingN
          exact hnot (by simp [PresentColors]; exact ⟨e, he, hge⟩)
        · by_cases hde : secondStableN e = some choiceN.color
          · simp [hge, hde, hgammaNeN, hgammaNeN.symm] at hec
          · exact hde (by simpa [hge, hde] using hec)
      have hfInternalN : f ∈ InternalEdges G
          (TreeSequenceVertexSet
            (ett.series.data.tree (Fin.last ett.rounds).castSucc)) := by
        have hseg : TreeSequenceInitialSegment
            (ett.series.data.tree p.succ.castSucc)
            (ett.series.data.tree (Fin.last ett.rounds).castSucc) := by
          have hs := stageToStage (p.val + 1) ett.rounds (by omega)
            (by omega) le_rfl
          convert hs using 1 <;> apply congrArg ett.series.data.tree <;>
            apply Fin.ext <;> simp
        simp only [InternalEdges, Finset.mem_filter, Finset.mem_univ, true_and]
        intro v hvf
        exact TreeSequenceInitialSegmentVertexSetSubset hseg
          ((Finset.mem_filter.mp hfInternal).2 v hvf)
      have hgInternalN : g ∈ InternalEdges G
          (TreeSequenceVertexSet
            (ett.series.data.tree (Fin.last ett.rounds).castSucc)) := by
        have hseg : TreeSequenceInitialSegment
            (ett.series.data.tree p.succ.castSucc)
            (ett.series.data.tree (Fin.last ett.rounds).castSucc) := by
          have hs := stageToStage (p.val + 1) ett.rounds (by omega)
            (by omega) le_rfl
          convert hs using 1 <;> apply congrArg ett.series.data.tree <;>
            apply Fin.ext <;> simp
        simp only [InternalEdges, Finset.mem_filter, Finset.mem_univ, true_and]
        intro v hvg
        exact TreeSequenceInitialSegmentVertexSetSubset hseg
          ((Finset.mem_filter.mp hgInternal).2 v hvg)
      have hfNeChoice : f ≠ choiceN.edge := by
        intro heq
        subst f
        simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ,
          true_and] at hchoiceBoundaryN
        rcases hchoiceBoundaryN with ⟨u, hu, v, hv, huv⟩
        have hvin : Incident G v choiceN.edge := by simp [Incident, huv]
        exact hv ((Finset.mem_filter.mp hfInternalN).2 v hvin)
      have hgNeChoice : g ≠ choiceN.edge := by
        intro heq
        subst g
        simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ,
          true_and] at hchoiceBoundaryN
        rcases hchoiceBoundaryN with ⟨u, hu, v, hv, huv⟩
        have hvin : Incident G v choiceN.edge := by simp [Incident, huv]
        exact hv ((Finset.mem_filter.mp hgInternalN).2 v hvin)
      have hgammaRGammaN : gammaR ≠ gammaN := by
        intro heq
        have hfFinalQ : ett.series.data.coloring q.succ f = some gammaR := by
          rw [hqLast]
          exact hfFinal
        exact (currentProperN hfNeChoice
          ⟨choiceN.vertex, hfInc, choiceN.edgeIncident⟩ hfFinalQ)
          (by simpa [heq] using hchoiceCurrentQ)
      have hdeltaRGammaN : choiceR.color ≠ gammaN := by
        intro heq
        have hgFinalQ : ett.series.data.coloring q.succ g =
            some choiceR.color := by
          rw [hqLast]
          exact hgFinal
        exact (currentProperN hgNeChoice
          ⟨choiceN.vertex, hgInc, choiceN.edgeIncident⟩ hgFinalQ)
          (by simpa [heq] using hchoiceCurrentQ)
      have hgammaRDeltaN : gammaR ≠ choiceN.color := by
        intro heq
        have hp : choiceN.color ∈ PresentColors G
            (ett.series.data.coloring (Fin.last ett.rounds)) choiceN.vertex := by
          simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨f, hfInc, by simpa [heq] using hfFinal⟩
        have hnot : choiceN.color ∉ PresentColors G
            (ett.series.data.coloring (Fin.last ett.rounds)) choiceN.vertex := by
          simpa [MissingColors] using hdeltaMissingN
        exact hnot hp
      have hdeltaRDeltaN : choiceR.color ≠ choiceN.color := by
        intro heq
        have hp : choiceN.color ∈ PresentColors G
            (ett.series.data.coloring (Fin.last ett.rounds)) choiceN.vertex := by
          simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨g, hgInc, by simpa [heq] using hgFinal⟩
        have hnot : choiceN.color ∉ PresentColors G
            (ett.series.data.coloring (Fin.last ett.rounds)) choiceN.vertex := by
          simpa [MissingColors] using hdeltaMissingN
        exact hnot hp
      rw [currentStoredN, currentStoredR]
      apply Finset.disjoint_left.mpr
      intro c hcN hcR
      simp only [Finset.mem_insert, Finset.mem_singleton] at hcN hcR
      rcases hcN with hcN | hcN <;> rcases hcR with hcR | hcR
      · exact hdeltaRDeltaN (hcR.symm.trans hcN)
      · exact hgammaRDeltaN (hcR.symm.trans hcN)
      · exact hdeltaRGammaN (hcR.symm.trans hcN)
      · exact hgammaRGammaN (hcR.symm.trans hcN)
