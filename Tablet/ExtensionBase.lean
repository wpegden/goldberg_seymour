import Tablet.AdjacentEdges
import Tablet.BoundaryEdges
import Tablet.CertifiedETTRestriction
import Tablet.ColoredVertexSetClosed
import Tablet.ColoredVertexSetElementary
import Tablet.Degree
import Tablet.ExtensionBaseAlgorithmA
import Tablet.ExtensionBaseAlgorithmB
import Tablet.ExtensionBaseAlgorithmC
import Tablet.ExtensionBaseCaseOneSelection
import Tablet.ExtensionBaseCaseTwoContradiction
import Tablet.ExtensionBaseCaseTwoObservation19
import Tablet.ExtensionBaseCaseTwoObservation20
import Tablet.ExtensionBaseCaseTwoObservation21
import Tablet.ExtensionBaseCaseTwoObservation23
import Tablet.ExtensionBaseClaim43
import Tablet.ExtensionBaseClaim44
import Tablet.ExtensionBaseClaim45
import Tablet.ExtensionBaseClaim46
import Tablet.ExtensionBaseClaimMissingColors
import Tablet.ExtensionBaseClaimStrongInterchangeable
import Tablet.ExtensionBaseClaimTreeEdgeColors
import Tablet.ExtensionBaseClosure
import Tablet.ExtensionBaseDeltaExclusion
import Tablet.ExtensionBaseStoredPairOverlap
import Tablet.ExtensionBaseSupportClassColors
import Tablet.ExtensionBaseSupportOrder
import Tablet.ExtensionRules
import Tablet.IsOneEdgeUncolored
import Tablet.IsProperEdgeColoring
import Tablet.LooplessMultigraph
import Tablet.MaximumPropertyTransport
import Tablet.MaximumDegree
import Tablet.MissingColors
import Tablet.OutsideTreeColorSwapStable
import Tablet.PresentColors
import Tablet.TashTree
import Tablet.TashkinovAugmentationSequencePreservesTashkinovTree
import Tablet.TashkinovClosure
import Tablet.TashkinovOrder
import Tablet.TreeMissingColors
import Tablet.TreeSequenceInitialSegment
import Tablet.TreeSequenceVertexSet
import Tablet.TwoColorIncidenceDegreeAtMostTwo
import Tablet.TwoColorIncidenceGraph
import Tablet.TwoColorComponentSwapProper

set_option maxHeartbeats 800000

-- [TABLET NODE: ExtensionBase]
theorem ExtensionBase {V E : Type*} [Fintype V] [Fintype E]
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
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc
    ∀ (v : V) (gamma delta : Fin k),
      ett.series.data.kind n = some TashkinovExtensionKind.PE →
      ett.series.data.chosenVertex n = some v →
      ett.series.data.gamma n = some gamma →
      ett.series.data.delta n = some delta →
      ∀ sigma : PartialEdgeColoring E k,
        IsProperEdgeColoring G sigma → IsOneEdgeUncolored sigma e0 →
        StableColoring Tn
          (TashkinovStoredColors ett.series.data n)
          (ett.series.data.coloring n) sigma →
        ∀ w, w ∈ TreeSequenceVertexSet Tn →
          (Sum.inl w ∈ TwoColorComponent G sigma gamma delta
              (Sum.inl v) ↔ w = v) := by
-- BODY
  dsimp
  intro v gamma delta hterminalKind hterminalVertex hterminalGamma
    hterminalDelta sigma hsigmaProper hsigmaOne hsigmaStable w hw
  constructor
  · intro hwComponent
    apply of_not_not
    intro hwNe
    letI : DecidableEq V := Classical.decEq V
    have hcurrentIII := ExtensionRules G k e0 input T generating ett hMP
      hpositive (fun lower hlowerPositive hlowerRounds hlowerMP =>
        hlower lower hlowerPositive hlowerRounds hlowerMP)
    let q : Fin ett.rounds := ⟨ett.rounds - 1, by omega⟩
    have hqTerminal : q.val + 1 = ett.rounds := by
      simp only [q]
      omega
    have hqSucc : q.succ = Fin.last ett.rounds := by
      apply Fin.ext
      simpa using hqTerminal
    have hqKind : ett.series.data.kind q.succ =
        some TashkinovExtensionKind.PE := by
      rw [hqSucc]
      exact hterminalKind
    have hqVertex : ett.series.data.chosenVertex q.succ = some v := by
      rw [hqSucc]
      exact hterminalVertex
    have hqGamma : ett.series.data.gamma q.succ = some gamma := by
      rw [hqSucc]
      exact hterminalGamma
    have hqDelta : ett.series.data.delta q.succ = some delta := by
      rw [hqSucc]
      exact hterminalDelta
    have hvStage : v ∈ TreeSequenceVertexSet
        (ett.series.data.tree q.succ.castSucc) := by
      generalize htarget : q.succ = target
      cases ett.series.certified target with
      | initial triple seedLength initialColoring initialStored initialEdges
          initialKind initialVertex initialOutside initialDelta initialGamma
          initialClosure =>
        exact (Fin.succ_ne_zero q htarget).elim
      | SE i previousProper previousOneUncolored previousClosed
          previousNotStronglyClosed noRevisiting choice seriesAlternative
          currentColoring currentStored currentEdges currentKind currentVertex
          currentOutside currentDelta currentGamma adjoined adjoinedExactly
          closedExtension orderedExtension strictExtension =>
        have hbad : some TashkinovExtensionKind.SE =
            some TashkinovExtensionKind.PE :=
          currentKind.symm.trans (by simpa [htarget] using hqKind)
        cases hbad
      | RE i previousProper previousOneUncolored previousClosed
          previousNotStronglyClosed available currentColoring currentStored
          currentEdges currentKind currentVertex currentOutside currentDelta
          currentGamma adjoined adjoinedExactly closedExtension orderedExtension
          strictExtension =>
        have hbad : some TashkinovExtensionKind.RE =
            some TashkinovExtensionKind.PE :=
          currentKind.symm.trans (by simpa [htarget] using hqKind)
        cases hbad
      | PE i previousProper previousOneUncolored previousClosed
          previousNotStronglyClosed noRevisiting choice seriesAlternativeFails
          chosenGamma gammaRule secondStable secondStableProper
          secondStableOneUncolored secondStableRelation exitWitness
          currentColoring currentProper currentOneUncolored currentStored
          currentEdges currentKind currentVertex currentOutside currentDelta
          currentGamma closedExtension orderedExtension strictExtension =>
        have hi : i = q := by
          apply Fin.ext
          simpa using (congrArg Fin.val htarget).symm
        subst i
        have hvChoice : choice.vertex = v :=
          Option.some.inj
            (currentVertex.symm.trans (by simpa [htarget] using hqVertex))
        simpa [hvChoice] using choice.vertexDefective.1
    have hqTreeIndex : q.succ.castSucc =
        (⟨ett.rounds, by omega⟩ : Fin (ett.rounds + 2)) := by
      apply Fin.ext
      simpa using hqTerminal
    have hvFinal : v ∈ TreeSequenceVertexSet T := by
      have hvPenultimate : v ∈ TreeSequenceVertexSet
          (ett.series.data.tree ⟨ett.rounds, by omega⟩) := by
        simpa [hqTreeIndex] using hvStage
      rcases ett.abovePenultimate with ⟨hlen, hvertices, hedges⟩
      simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ,
        true_and] at hvPenultimate ⊢
      obtain ⟨i, hi⟩ := hvPenultimate
      refine ⟨Fin.castLE (Nat.succ_le_succ hlen) i, ?_⟩
      exact (hvertices i).trans hi
    have hfirstUpper : ETTFirstAppearanceIndex ett v hvFinal ≤ q.val + 1 :=
      ExtensionRulesPEFirstAppearanceBound G k e0 input T generating ett q v
        hqKind hqVertex hvFinal
    have hfirstPositive : 0 < ETTFirstAppearanceIndex ett v hvFinal := by
      unfold ETTFirstAppearanceIndex
      dsimp
      omega
    let jSlot : Fin ett.rounds :=
      ⟨ETTFirstAppearanceIndex ett v hvFinal - 1, by omega⟩
    have hjSlot : jSlot.val + 1 =
        ETTFirstAppearanceIndex ett v hvFinal := by
      simp only [jSlot]
      omega
    have hjle : jSlot.val ≤ q.val := by omega
    have hsigmaTerminal : StableColoring
        (ett.series.data.tree q.succ.castSucc)
        (TashkinovStoredColors ett.series.data q.succ)
        (ett.series.data.coloring q.succ) sigma := by
      simpa [hqSucc] using hsigmaStable
    have hcurrentTerminal := hcurrentIII.1 q v hqKind hqVertex hvFinal
      jSlot.castSucc (by simpa using hjSlot.symm) sigma hsigmaProper hsigmaOne
      hsigmaTerminal
    have hsigmaBefore := hcurrentTerminal.1
    have segmentRefl (A : TreeSequence G e0) :
        TreeSequenceInitialSegment A A :=
      ⟨le_rfl, (by intro i; rfl), (by intro i; rfl)⟩
    have segmentTrans {A B C : TreeSequence G e0}
        (hAB : TreeSequenceInitialSegment A B)
        (hBC : TreeSequenceInitialSegment B C) :
        TreeSequenceInitialSegment A C := by
      rcases hAB with ⟨hab, hvab, heab⟩
      rcases hBC with ⟨hbc, hvbc, hebc⟩
      refine ⟨hab.trans hbc, ?_, ?_⟩
      · intro i
        simpa using
          (hvbc (Fin.castLE (Nat.succ_le_succ hab) i)).trans (hvab i)
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
    have stageToStage : ∀ (a b : ℕ) (_ha : 1 ≤ a) (_hab : a ≤ b)
        (_hb : b ≤ ett.rounds),
        TreeSequenceInitialSegment
          (ett.series.data.tree ⟨a, by omega⟩)
          (ett.series.data.tree ⟨b, by omega⟩) := by
      intro a b ha hab hb
      have chain : ∀ (d : ℕ) (_hd : a + d ≤ b),
          TreeSequenceInitialSegment
            (ett.series.data.tree ⟨a, by omega⟩)
            (ett.series.data.tree ⟨a + d, by omega⟩) := by
        intro d hd
        induction d with
        | zero => simpa using segmentRefl (ett.series.data.tree ⟨a, by omega⟩)
        | succ d ih =>
            have hprev := ih (by omega)
            let idx : Fin (ett.rounds + 1) := ⟨a + d, by omega⟩
            have hone := stepSegment idx (by dsimp [idx]; omega)
            have hone' : TreeSequenceInitialSegment
                (ett.series.data.tree ⟨a + d, by omega⟩)
                (ett.series.data.tree ⟨a + (d + 1), by omega⟩) := by
              simpa [idx, Nat.add_assoc] using hone
            exact segmentTrans hprev hone'
      have hchain := chain (b - a) (by omega)
      convert hchain using 1 <;> congr 1 <;> apply Fin.ext <;> simp <;> omega
    have vertexTransfer {A B : TreeSequence G e0}
        (hAB : TreeSequenceInitialSegment A B) :
        TreeSequenceVertexSet A ⊆ TreeSequenceVertexSet B := by
      intro x hx
      simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ,
        true_and] at hx ⊢
      obtain ⟨i, rfl⟩ := hx
      rcases hAB with ⟨hlen, hvertices, hedges⟩
      exact ⟨Fin.castLE (Nat.succ_le_succ hlen) i, hvertices i⟩
    have orderRestrict {A B : TreeSequence G e0}
        (hAB : TreeSequenceInitialSegment A B) (x y : V)
        (hxA : x ∈ TreeSequenceVertexSet A)
        (hyA : y ∈ TreeSequenceVertexSet A)
        (hxy : TreeVertexOrder B x y) : TreeVertexOrder A x y := by
      rcases hAB with ⟨hlen, hvertices, hedges⟩
      rcases Finset.mem_image.mp hxA with ⟨ix, _, hix⟩
      rcases Finset.mem_image.mp hyA with ⟨iy, _, hiy⟩
      rcases hxy with ⟨jx, jy, hjx, hjy, hjlt⟩
      have hjxEq : jx = Fin.castLE (Nat.succ_le_succ hlen) ix := by
        apply B.vertex_injective
        exact hjx.trans ((hvertices ix).trans hix).symm
      have hjyEq : jy = Fin.castLE (Nat.succ_le_succ hlen) iy := by
        apply B.vertex_injective
        exact hjy.trans ((hvertices iy).trans hiy).symm
      refine ⟨ix, iy, hix, hiy, ?_⟩
      rw [hjxEq, hjyEq] at hjlt
      simpa using hjlt
    have hLowerElementary : ∀ r : Fin ett.rounds, r.val < q.val →
        ColoredVertexSetElementary G (ett.series.data.coloring r.castSucc)
          (TreeSequenceVertexSet
            (ett.series.data.tree r.succ.castSucc)) := by
      intro r hrq
      by_cases hrZero : r.val = 0
      · have hbase : ColoredVertexSetElementary G
            (ett.series.data.coloring 0)
            (TreeSequenceVertexSet
              (ett.series.data.tree ⟨1, by omega⟩)) :=
          (TechnicalTheoremBase G k ett.rounds e0 input ett.series).1
        have hrColor : r.castSucc = (0 : Fin (ett.rounds + 1)) := by
          apply Fin.ext
          simpa using hrZero
        have hrTree : r.succ.castSucc =
            (⟨1, by omega⟩ : Fin (ett.rounds + 2)) := by
          apply Fin.ext
          simpa using hrZero
        simpa [hrColor, hrTree] using hbase
      · obtain ⟨lower, hround, hlowerMP, htrees, hdata⟩ :=
          CertifiedETTRestriction G k e0 input T generating ett hMP r.val
            (by omega) (by omega)
        have hpack := hlower lower (by omega) (by omega) hlowerMP
        exact hpack.1
    have hLowerPartV : ∀ (r a : Fin ett.rounds), a.val < r.val →
        ∀ sigmaR : PartialEdgeColoring E k,
          IsProperEdgeColoring G sigmaR → IsOneEdgeUncolored sigmaR e0 →
          StableColoring (ett.series.data.tree r.succ.castSucc)
            (TashkinovStoredColors ett.series.data r.castSucc)
            (ett.series.data.coloring r.castSucc) sigmaR →
          ∀ deltaR : Fin k,
            DefectiveColor G sigmaR
              (TreeSequenceVertexSet
                (ett.series.data.tree r.succ.castSucc)) deltaR →
            ∀ x : V,
              BoundaryColorVertex G sigmaR
                (TreeSequenceVertexSet
                  (ett.series.data.tree r.succ.castSucc)) deltaR x →
              (∃ y : V, BoundaryColorVertex G sigmaR
                  (TreeSequenceVertexSet
                    (ett.series.data.tree r.succ.castSucc)) deltaR y ∧
                TreeVertexOrder
                  (ett.series.data.tree r.succ.castSucc) y x) →
              ∀ hxFinal : x ∈ TreeSequenceVertexSet T,
                ETTFirstAppearanceIndex ett x hxFinal ≤ a.val + 1 →
                ∀ xa : V,
                  (ett.series.data.kind a.succ =
                      some TashkinovExtensionKind.PE ∨
                    ett.series.data.kind a.succ =
                      some TashkinovExtensionKind.SE) →
                  ett.series.data.chosenVertex a.succ = some xa →
                  x = xa ∨ TreeVertexOrder
                    (ett.series.data.tree r.succ.castSucc) x xa := by
      intro r a har sigmaR hproperR honeR hstableR deltaR hdefectiveR x
        hboundaryR hearlierR hxFinal hfirstR xa hkindA hvertexA
      obtain ⟨lower, hround, hlowerMP, htrees, hdata⟩ :=
        CertifiedETTRestriction G k e0 input T generating ett hMP r.val
          (by omega) (by omega)
      let nLower : Fin (lower.rounds + 1) := Fin.last lower.rounds
      let aLower : Fin lower.rounds := ⟨a.val, by omega⟩
      have hnMap : Fin.castLE (by omega) nLower = r.castSucc := by
        apply Fin.ext
        simp [nLower, hround]
      have hnTreeMap : Fin.castLE (by omega) nLower.castSucc =
          r.castSucc.castSucc := by
        apply Fin.ext
        simp [nLower, hround]
      have haMap : Fin.castLE (by omega) aLower.succ = a.succ := by
        apply Fin.ext
        rfl
      let P : TreeSequence G e0 := ett.series.data.tree r.castSucc.castSucc
      let Tnext : TreeSequence G e0 := ett.series.data.tree r.succ.castSucc
      have hPNext : TreeSequenceInitialSegment P Tnext := by
        have hs := stepSegment r.castSucc (by simpa using (show 0 < r.val by omega))
        simpa [P, Tnext] using hs
      have hxP : x ∈ TreeSequenceVertexSet P := by
        let candidates : Finset (Fin (ett.rounds + 1)) :=
          Finset.univ.filter fun i =>
            x ∈ TreeSequenceVertexSet (ExtendedTashkinovLadderStage ett i)
        have hnonempty : candidates.Nonempty := by
          refine ⟨Fin.last ett.rounds, ?_⟩
          simp only [candidates, Finset.mem_filter, Finset.mem_univ, true_and]
          rw [show ExtendedTashkinovLadderStage ett (Fin.last ett.rounds) = T by
            simp [ExtendedTashkinovLadderStage, Fin.lastCases_last]]
          exact hxFinal
        let first := candidates.min' hnonempty
        have hfirstBound : first.val + 1 ≤ a.val + 1 := by
          have hfirstRaw := hfirstR
          unfold ETTFirstAppearanceIndex at hfirstRaw
          dsimp at hfirstRaw
          dsimp [first, candidates]
          convert hfirstRaw using 1 <;> congr
        have hfirstMem : first ∈ candidates :=
          Finset.min'_mem candidates hnonempty
        change first ∈ candidates at hfirstMem
        let firstBase : Fin ett.rounds := ⟨first.val, by omega⟩
        have hfirstEq : first = firstBase.castSucc := by
          apply Fin.ext
          rfl
        have hxFirst : x ∈ TreeSequenceVertexSet
            (ett.series.data.tree ⟨first.val + 1, by omega⟩) := by
          have hxLadder := (Finset.mem_filter.mp hfirstMem).2
          rw [hfirstEq] at hxLadder
          unfold ExtendedTashkinovLadderStage at hxLadder
          rw [Fin.lastCases_castSucc] at hxLadder
          convert hxLadder using 1 <;> congr 2 <;> apply Fin.ext <;> rfl
        have hseg := stageToStage (first.val + 1) r.val (by omega)
          (by omega) (by omega)
        have hxStage := vertexTransfer hseg hxFirst
        have hPIndex : (⟨r.val, by omega⟩ : Fin (ett.rounds + 2)) =
            r.castSucc.castSucc := by
          apply Fin.ext
          rfl
        rw [hPIndex] at hxStage
        exact hxStage
      obtain ⟨y, hyBoundary, hyx⟩ := hearlierR
      have hyP : y ∈ TreeSequenceVertexSet P := by
        rcases hPNext with ⟨hlen, hvertices, hedges⟩
        rcases Finset.mem_image.mp hxP with ⟨ix, _, hix⟩
        rcases hyx with ⟨jy, jx, hjy, hjx, hjlt⟩
        have hjxEq : jx = Fin.castLE (Nat.succ_le_succ hlen) ix := by
          apply Tnext.vertex_injective
          exact hjx.trans ((hvertices ix).trans hix).symm
        have hjyBound : jy.val < P.length + 1 := by
          have hjxVal := congrArg Fin.val hjxEq
          simp only [Fin.val_castLE] at hjxVal
          omega
        let iy : Fin (P.length + 1) := ⟨jy.val, hjyBound⟩
        apply Finset.mem_image.mpr
        refine ⟨iy, Finset.mem_univ _, ?_⟩
        have hcast : Fin.castLE (Nat.succ_le_succ hlen) iy = jy := by
          apply Fin.ext
          rfl
        have hnextIndex : r.castSucc.succ = r.succ.castSucc := by
          apply Fin.ext
          rfl
        have hjy' : Tnext.vertex jy = y := by
          simpa [Tnext, hnextIndex] using hjy
        exact (hvertices iy).symm.trans (by simpa [hcast] using hjy')
      have hyxP : TreeVertexOrder P y x :=
        orderRestrict hPNext y x hyP hxP hyx
      have hyne : y ≠ x := by
        intro hyxEq
        subst y
        rcases hyxP with ⟨iy, ix, hiy, hix, hlt⟩
        have : iy = ix := P.vertex_injective (hiy.trans hix.symm)
        omega
      have boundaryRestrict : ∀ z : V, z ∈ TreeSequenceVertexSet P →
          ∀ f : E, f ∈ BoundaryColorEdges G sigmaR
              (TreeSequenceVertexSet Tnext) deltaR →
            Incident G z f →
            f ∈ BoundaryColorEdges G sigmaR
              (TreeSequenceVertexSet P) deltaR := by
        intro z hzP f hf hzf
        have hfBoundary := (Finset.mem_filter.mp hf).1
        have hfColor := (Finset.mem_filter.mp hf).2
        simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ,
          true_and] at hfBoundary
        obtain ⟨zin, hzin, zout, hzout, hends⟩ := hfBoundary
        have hzNext := vertexTransfer hPNext hzP
        have hzCases : z = zin ∨ z = zout := by
          simpa [Incident, hends] using hzf
        have hzEq : z = zin := hzCases.resolve_right fun hzEq =>
          hzout (hzEq ▸ hzNext)
        apply Finset.mem_filter.mpr
        refine ⟨?_, hfColor⟩
        simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ,
          true_and]
        refine ⟨z, hzP, zout, ?_, ?_⟩
        · intro hzoutP
          exact hzout (vertexTransfer hPNext hzoutP)
        · simpa [hzEq] using hends
      obtain ⟨fx, hfxBoundary, hfxIncident⟩ := hboundaryR.2
      obtain ⟨fy, hfyBoundary, hfyIncident⟩ := hyBoundary.2
      have hfxP := boundaryRestrict x hxP fx hfxBoundary hfxIncident
      have hfyP := boundaryRestrict y hyP fy hfyBoundary hfyIncident
      have hfxy : fx ≠ fy := by
        intro hfeq
        subst fy
        have hfBoundary := (Finset.mem_filter.mp hfxBoundary).1
        simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ,
          true_and] at hfBoundary
        obtain ⟨zin, hzin, zout, hzout, hends⟩ := hfBoundary
        have hxCases : x = zin ∨ x = zout := by
          simpa [Incident, hends] using hfxIncident
        have hyCases : y = zin ∨ y = zout := by
          simpa [Incident, hends] using hfyIncident
        have hxNext := vertexTransfer hPNext hxP
        have hyNext := vertexTransfer hPNext hyP
        have hxEq : x = zin := hxCases.resolve_right fun hxEq =>
          hzout (hxEq ▸ hxNext)
        have hyEq : y = zin := hyCases.resolve_right fun hyEq =>
          hzout (hyEq ▸ hyNext)
        exact hyne (hyEq.trans hxEq.symm)
      have hdefectiveP : DefectiveColor G sigmaR
          (TreeSequenceVertexSet P) deltaR := by
        unfold DefectiveColor
        exact Finset.one_lt_card.mpr ⟨fx, hfxP, fy, hfyP, hfxy⟩
      have htreeLower : lower.series.data.tree nLower.castSucc =
          P := by
        rw [htrees nLower.castSucc, hnTreeMap]
      have hcolorLower : lower.series.data.coloring nLower =
          ett.series.data.coloring r.castSucc := by
        rw [(hdata nLower).1, hnMap]
      have hstoredLower : TashkinovStoredColors lower.series.data nLower =
          TashkinovStoredColors ett.series.data r.castSucc := by
        rw [(hdata nLower).2.2.2.2.2.2.2.2.1, hnMap]
      have hstableLower : StableColoring
          (lower.series.data.tree nLower.castSucc)
          (TashkinovStoredColors lower.series.data nLower)
          (lower.series.data.coloring nLower) sigmaR := by
        rw [htreeLower, hstoredLower, hcolorLower]
        constructor
        · intro f hfP hcontrolled
          apply hstableR.1 f
          · rcases hfP with ⟨z, hz, hzf⟩
            exact ⟨z, vertexTransfer hPNext hz, hzf⟩
          · rcases hcontrolled with ⟨c, hc, hfc⟩
            refine ⟨c, ?_, hfc⟩
            rcases Finset.mem_union.mp hc with hc | hc
            · apply Finset.mem_union.mpr
              left
              simp only [TreeMissingColors, Finset.mem_biUnion] at hc ⊢
              rcases hc with ⟨z, hz, hcz⟩
              exact ⟨z, vertexTransfer hPNext hz, hcz⟩
            · exact Finset.mem_union.mpr (Or.inr hc)
        · intro z hz
          exact hstableR.2 z (vertexTransfer hPNext hz)
      have hdefectiveLower : DefectiveColor G sigmaR
          (TreeSequenceVertexSet
            (lower.series.data.tree nLower.castSucc)) deltaR := by
        simpa [htreeLower] using hdefectiveP
      have hboundaryLower : BoundaryColorVertex G sigmaR
          (TreeSequenceVertexSet
            (lower.series.data.tree nLower.castSucc)) deltaR x := by
        rw [htreeLower]
        exact ⟨hxP, fx, hfxP, hfxIncident⟩
      have hearlierLower : ∃ y : V, BoundaryColorVertex G sigmaR
          (TreeSequenceVertexSet
          (lower.series.data.tree nLower.castSucc)) deltaR y ∧
          TreeVertexOrder (lower.series.data.tree nLower.castSucc) y x := by
        rw [htreeLower]
        exact ⟨y, ⟨hyP, fy, hfyP, hfyIncident⟩, hyxP⟩
      have hxLower : x ∈ TreeSequenceVertexSet
          (ett.series.data.tree ⟨r.val + 1, by omega⟩) := by
        have hx := hboundaryR.1
        convert hx using 1 <;> congr 2 <;> apply Fin.ext <;> rfl
      have hkindLower : lower.series.data.kind aLower.succ =
          some TashkinovExtensionKind.PE ∨
          lower.series.data.kind aLower.succ =
            some TashkinovExtensionKind.SE := by
        rcases hkindA with hkindA | hkindA
        · left
          rw [(hdata aLower.succ).2.2.2.1, haMap]
          exact hkindA
        · right
          rw [(hdata aLower.succ).2.2.2.1, haMap]
          exact hkindA
      have hvertexLower : lower.series.data.chosenVertex aLower.succ =
          some xa := by
        rw [(hdata aLower.succ).2.2.2.2.1, haMap]
        exact hvertexA
      have hfirstLower : ETTFirstAppearanceIndex lower x hxLower ≤
          aLower.val + 1 := by
        unfold ETTFirstAppearanceIndex
        dsimp
        let fullCandidates : Finset (Fin (ett.rounds + 1)) :=
          Finset.univ.filter fun i =>
            x ∈ TreeSequenceVertexSet (ExtendedTashkinovLadderStage ett i)
        have hfullNonempty : fullCandidates.Nonempty := by
          refine ⟨Fin.last ett.rounds, ?_⟩
          simp only [fullCandidates, Finset.mem_filter, Finset.mem_univ,
            true_and]
          rw [show ExtendedTashkinovLadderStage ett (Fin.last ett.rounds) = T by
            simp [ExtendedTashkinovLadderStage, Fin.lastCases_last]]
          exact hxFinal
        let mf := fullCandidates.min' hfullNonempty
        have hmfBound : mf.val + 1 ≤ a.val + 1 := by
          have hfirstRaw := hfirstR
          unfold ETTFirstAppearanceIndex at hfirstRaw
          dsimp at hfirstRaw
          dsimp [mf, fullCandidates]
          convert hfirstRaw using 1 <;> congr
        let lowerCandidates : Finset (Fin (lower.rounds + 1)) :=
          Finset.univ.filter fun i =>
            x ∈ TreeSequenceVertexSet
              (ExtendedTashkinovLadderStage lower i)
        have hlowerNonempty : lowerCandidates.Nonempty := by
          refine ⟨Fin.last lower.rounds, ?_⟩
          simp only [lowerCandidates, Finset.mem_filter, Finset.mem_univ,
            true_and]
          rw [show ExtendedTashkinovLadderStage lower
              (Fin.last lower.rounds) =
                ett.series.data.tree ⟨r.val + 1, by omega⟩ by
            unfold ExtendedTashkinovLadderStage
            exact Fin.lastCases_last]
          exact hxLower
        let mfLower : Fin (lower.rounds + 1) := ⟨mf.val, by omega⟩
        let mfBase : Fin lower.rounds := ⟨mf.val, by omega⟩
        let mfFull : Fin ett.rounds := ⟨mf.val, by omega⟩
        have hmfLower : mfLower = mfBase.castSucc := by
          apply Fin.ext
          rfl
        have hmfFull : mf = mfFull.castSucc := by
          apply Fin.ext
          rfl
        have hstageEq : ExtendedTashkinovLadderStage lower mfLower =
            ExtendedTashkinovLadderStage ett mf := by
          rw [hmfLower, hmfFull]
          unfold ExtendedTashkinovLadderStage
          rw [Fin.lastCases_castSucc, Fin.lastCases_castSucc,
            htrees mfBase.succ.castSucc]
          congr 1
        have hmfMemFull := Finset.min'_mem fullCandidates hfullNonempty
        have hmfMemLower : mfLower ∈ lowerCandidates := by
          simp only [lowerCandidates, Finset.mem_filter, Finset.mem_univ,
            true_and]
          rw [hstageEq]
          exact (Finset.mem_filter.mp hmfMemFull).2
        have hle := Finset.min'_le lowerCandidates mfLower hmfMemLower
        have hleVal := Fin.le_iff_val_le_val.mp hle
        have htarget :
            (lowerCandidates.min' hlowerNonempty).val + 1 ≤ a.val + 1 := by
          dsimp [mfLower] at hleVal
          omega
        convert htarget using 1 <;> congr
      have hpack := hlower lower (by omega) (by omega) hlowerMP
      have hresult := hpack.2.2.2.2.1 sigmaR hproperR honeR hstableLower
        deltaR hdefectiveLower x hboundaryLower hearlierLower hxLower aLower xa
        hkindLower hvertexLower hfirstLower
      exact hresult
    have hsupportOrder := ExtensionBaseSupportOrder ett v hvFinal q hqTerminal
      hqKind hqVertex hLowerPartV
    have hdeltaExclusion := ExtensionBaseDeltaExclusion ett v hvFinal q
      hqTerminal hqKind hqVertex jSlot hjSlot hLowerElementary hLowerPartV
    have hpairOverlap := ExtensionBaseStoredPairOverlap G k e0 input T
      generating ett v hvFinal q hqTerminal hqKind hqVertex jSlot hjSlot hMP
      hpositive hLowerElementary hLowerPartV
      (fun lower hlowerPositive hlowerRounds hlowerMP =>
        hlower lower hlowerPositive hlowerRounds hlowerMP)
    have htreeEdges := ExtensionBaseClaimTreeEdgeColors G k e0 input
      ett.rounds ett.series jSlot q hjle hqTerminal sigma hsigmaProper
      hsigmaOne hsigmaTerminal
    have hLowerInterchange : ∀ (t : Fin ett.rounds) (vt : V)
        (gammaT deltaT : Fin k),
        t ∈ ExtensionBaseActiveIndices ett v hvFinal →
        t.val < q.val →
        ett.series.data.chosenVertex t.succ = some vt →
        ett.series.data.gamma t.succ = some gammaT →
        ett.series.data.delta t.succ = some deltaT →
        TreeInterchangeable G (ett.series.data.tree t.succ.succ)
          (ett.series.data.coloring t.succ) gammaT deltaT := by
      intro t vt gammaT deltaT htActive htq htVertex htGamma htDelta
      have htKind : ett.series.data.kind t.succ =
          some TashkinovExtensionKind.PE := by
        have htData := htActive
        simp only [ExtensionBaseActiveIndices, Finset.mem_filter,
          Finset.mem_univ, true_and] at htData
        exact htData.2.1
      have htCurrent : IsOneEdgeUncolored
            (ett.series.data.coloring t.succ) e0 ∧
          deltaT ∈ MissingColors G
            (ett.series.data.coloring t.succ) vt := by
        generalize htarget : t.succ = target
        cases ett.series.certified target with
        | initial triple seedLength initialColoring initialStored initialEdges
            initialKind initialVertex initialOutside initialDelta initialGamma
            initialClosure =>
          exact (Fin.succ_ne_zero t htarget).elim
        | SE i previousProper previousOneUncolored previousClosed
            previousNotStronglyClosed noRevisiting choice seriesAlternative
            currentColoring currentStored currentEdges currentKind currentVertex
            currentOutside currentDelta currentGamma adjoined adjoinedExactly
            closedExtension orderedExtension strictExtension =>
          have hbad : some TashkinovExtensionKind.SE =
              some TashkinovExtensionKind.PE :=
            currentKind.symm.trans (by simpa [htarget] using htKind)
          cases hbad
        | RE i previousProper previousOneUncolored previousClosed
            previousNotStronglyClosed available currentColoring currentStored
            currentEdges currentKind currentVertex currentOutside currentDelta
            currentGamma adjoined adjoinedExactly closedExtension orderedExtension
            strictExtension =>
          have hbad : some TashkinovExtensionKind.RE =
              some TashkinovExtensionKind.PE :=
            currentKind.symm.trans (by simpa [htarget] using htKind)
          cases hbad
        | PE i previousProper previousOneUncolored previousClosed
            previousNotStronglyClosed noRevisiting choice seriesAlternativeFails
            actualGamma gammaRule secondStable secondStableProper
            secondStableOneUncolored secondStableRelation exitWitness
            currentColoring currentProper currentOneUncolored currentStored
            currentEdges currentKind currentVertex currentOutside currentDelta
            currentGamma closedExtension orderedExtension strictExtension =>
          have hi : i = t := by
            apply Fin.ext
            simpa using (congrArg Fin.val htarget).symm
          subst i
          have hvChoice : choice.vertex = vt :=
            Option.some.inj
              (currentVertex.symm.trans (by simpa [htarget] using htVertex))
          have hdeltaChoice : choice.color = deltaT :=
            Option.some.inj
              (currentDelta.symm.trans (by simpa [htarget] using htDelta))
          have hgammaChoice : actualGamma = gammaT :=
            Option.some.inj
              (currentGamma.symm.trans (by simpa [htarget] using htGamma))
          subst vt
          subst deltaT
          subst gammaT
          have hgammaMissing : actualGamma ∈
              MissingColors G secondStable choice.vertex := by
            exact (secondStableRelation.2 choice.vertex
              choice.vertexDefective.1).symm ▸ gammaRule.1
          have hedge : secondStable choice.edge = some choice.color := by
            exact (secondStableRelation.1 choice.edge
              ⟨choice.vertex, choice.vertexDefective.1, choice.edgeIncident⟩
              ⟨choice.color, by simp, choice.edgeColor⟩).trans choice.edgeColor
          have hgammaDelta : actualGamma ≠ choice.color := by
            intro heq
            have hpresent : actualGamma ∈
                PresentColors G secondStable choice.vertex := by
              simp only [PresentColors, Finset.mem_filter, Finset.mem_univ,
                true_and]
              exact ⟨choice.edge, choice.edgeIncident, by simpa [heq] using hedge⟩
            exact (Finset.mem_sdiff.mp hgammaMissing).2 hpresent
          have componentEdge : ∀ e : E, Incident G choice.vertex e →
              secondStable e = some actualGamma ∨
                secondStable e = some choice.color →
              Sum.inr e ∈ TwoColorComponent G secondStable actualGamma
                choice.color (Sum.inl choice.vertex) := by
            intro e he hcolor
            change (TwoColorIncidenceGraph G secondStable actualGamma
              choice.color).connectedComponentMk (Sum.inr e) = _
            apply SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
            simp [TwoColorIncidenceGraph, he, hcolor]
          have hgammaNo : ∀ e : E, Incident G choice.vertex e →
              secondStable e ≠ some actualGamma := by
            intro e he hec
            apply (Finset.mem_sdiff.mp hgammaMissing).2
            simp only [PresentColors, Finset.mem_filter, Finset.mem_univ,
              true_and]
            exact ⟨e, he, hec⟩
          have hdeltaMissing : choice.color ∈ MissingColors G
              (TwoColorComponentSwap G secondStable actualGamma choice.color
                (Sum.inl choice.vertex)) choice.vertex := by
            apply Finset.mem_sdiff.mpr
            refine ⟨by simp, ?_⟩
            intro hpresent
            simp only [PresentColors, Finset.mem_filter, Finset.mem_univ,
              true_and] at hpresent
            obtain ⟨e, he, hec⟩ := hpresent
            rw [TwoColorComponentSwap] at hec
            by_cases hcomp : Sum.inr e ∈ TwoColorComponent G secondStable
                actualGamma choice.color (Sum.inl choice.vertex)
            · simp [hcomp] at hec
              by_cases heg : secondStable e = some actualGamma
              · exact (hgammaNo e he heg).elim
              · by_cases hed : secondStable e = some choice.color
                · simp [hed, hgammaDelta] at hec
                  exact hgammaDelta hec.symm
                · simp [heg, hed] at hec
            · simp [hcomp] at hec
              exact hcomp (componentEdge e he (Or.inr hec))
          refine ⟨by simpa [htarget] using currentOneUncolored, ?_⟩
          rw [show ett.series.data.coloring t.succ =
              TwoColorComponentSwap G secondStable actualGamma choice.color
                (Sum.inl choice.vertex) by simpa [htarget] using currentColoring]
          exact hdeltaMissing
      obtain ⟨hcolorNe, htProper, htSegment, hvtStage, hrootPath,
          hrootOnly, hnonisolated⟩ :=
        ParallelStepRootComponentSetup ett.series t vt gammaT deltaT
          htKind htVertex htGamma htDelta
      have hdeltaTree : deltaT ∈ TreeMissingColors
          (ett.series.data.coloring t.succ)
          (ett.series.data.tree t.succ.succ) := by
        simp only [TreeMissingColors, Finset.mem_biUnion]
        exact ⟨vt, vertexTransfer htSegment hvtStage, htCurrent.2⟩
      let s := t.val + 1
      obtain ⟨lower, hround, hlowerMP, htrees, hdata⟩ :=
        CertifiedETTRestriction G k e0 input T generating ett hMP s
          (by simp [s]) (by dsimp [s]; omega)
      let nLower : Fin (lower.rounds + 1) := Fin.last lower.rounds
      let nextLower : Fin (lower.rounds + 2) := Fin.last (lower.rounds + 1)
      have hnMap : Fin.castLE (by omega) nLower = t.succ := by
        apply Fin.ext
        simp [nLower, hround, s]
      have hnextMap : Fin.castLE (by omega) nextLower = t.succ.succ := by
        apply Fin.ext
        simp [nextLower, hround, s]
      have htreeLower : lower.series.data.tree nextLower =
          ett.series.data.tree t.succ.succ := by
        rw [htrees nextLower, hnextMap]
      have htreeFinal : lower.series.data.tree
          (Fin.last (lower.rounds + 1)) =
          ett.series.data.tree t.succ.succ := by
        simpa [nextLower] using htreeLower
      have hcolorLower : lower.series.data.coloring nLower =
          ett.series.data.coloring t.succ := by
        rw [(hdata nLower).1, hnMap]
      have hstoredLower : TashkinovStoredColors lower.series.data nLower =
          TashkinovStoredColors ett.series.data t.succ := by
        rw [(hdata nLower).2.2.2.2.2.2.2.2.1, hnMap]
      have hstableSelf : StableColoring
          (ett.series.data.tree t.succ.succ)
          (TashkinovStoredColors ett.series.data t.succ)
          (ett.series.data.coloring t.succ)
          (ett.series.data.coloring t.succ) := by
        exact ⟨(by intros; rfl), (by intros; rfl)⟩
      have hstableLower : StableColoring
          (lower.series.data.tree nextLower)
          (TashkinovStoredColors lower.series.data nLower)
          (lower.series.data.coloring nLower)
          (ett.series.data.coloring t.succ) := by
        simpa [htreeLower, hstoredLower, hcolorLower] using hstableSelf
      have hpack := hlower lower (by omega) (by omega) hlowerMP
      have hdeltaLower : deltaT ∈ TreeMissingColors
          (ett.series.data.coloring t.succ)
          (lower.series.data.tree (Fin.last (lower.rounds + 1))) := by
        rw [htreeFinal]
        exact hdeltaTree
      have hinterchange := hpack.2.1 (ett.series.data.coloring t.succ)
        htProper htCurrent.1 hstableLower gammaT deltaT (Or.inr hdeltaLower)
      rw [htreeFinal] at hinterchange
      exact hinterchange
    have hstrongInterchange := ExtensionBaseClaimStrongInterchangeable ett v
      hvFinal q hqTerminal hqKind hqVertex hLowerInterchange sigma hsigmaProper
      hsigmaOne hsigmaTerminal
    have hPESlotData : ∀ t : Fin ett.rounds,
        ett.series.data.kind t.succ = some TashkinovExtensionKind.PE →
        ∃ vt : V, ∃ gammaT deltaT : Fin k,
          ett.series.data.chosenVertex t.succ = some vt ∧
            ett.series.data.gamma t.succ = some gammaT ∧
            ett.series.data.delta t.succ = some deltaT := by
      intro t htKind
      generalize htarget : t.succ = target
      cases ett.series.certified target with
      | initial triple seedLength initialColoring initialStored initialEdges
          initialKind initialVertex initialOutside initialDelta initialGamma
          initialClosure =>
        exact (Fin.succ_ne_zero t htarget).elim
      | SE i previousProper previousOneUncolored previousClosed
          previousNotStronglyClosed noRevisiting choice seriesAlternative
          currentColoring currentStored currentEdges currentKind currentVertex
          currentOutside currentDelta currentGamma adjoined adjoinedExactly
          closedExtension orderedExtension strictExtension =>
        have hbad : some TashkinovExtensionKind.SE =
            some TashkinovExtensionKind.PE :=
          currentKind.symm.trans (by simpa [htarget] using htKind)
        cases hbad
      | RE i previousProper previousOneUncolored previousClosed
          previousNotStronglyClosed available currentColoring currentStored
          currentEdges currentKind currentVertex currentOutside currentDelta
          currentGamma adjoined adjoinedExactly closedExtension orderedExtension
          strictExtension =>
        have hbad : some TashkinovExtensionKind.RE =
            some TashkinovExtensionKind.PE :=
          currentKind.symm.trans (by simpa [htarget] using htKind)
        cases hbad
      | PE i previousProper previousOneUncolored previousClosed
          previousNotStronglyClosed noRevisiting choice seriesAlternativeFails
          actualGamma gammaRule secondStable secondStableProper
          secondStableOneUncolored secondStableRelation exitWitness
          currentColoring currentProper currentOneUncolored currentStored
          currentEdges currentKind currentVertex currentOutside currentDelta
          currentGamma closedExtension orderedExtension strictExtension =>
        have hi : i = t := by
          apply Fin.ext
          simpa using (congrArg Fin.val htarget).symm
        subst i
        refine ⟨choice.vertex, actualGamma, choice.color, ?_, ?_, ?_⟩
        · simpa [htarget] using currentVertex
        · simpa [htarget] using currentGamma
        · simpa [htarget] using currentDelta
    have hPEStored : ∀ (t : Fin ett.rounds) (gammaT deltaT : Fin k),
        ett.series.data.kind t.succ = some TashkinovExtensionKind.PE →
        ett.series.data.gamma t.succ = some gammaT →
        ett.series.data.delta t.succ = some deltaT →
        ett.series.data.stored t.succ = {gammaT, deltaT} := by
      intro t gammaT deltaT htKind htGamma htDelta
      generalize htarget : t.succ = target
      cases ett.series.certified target with
      | initial triple seedLength initialColoring initialStored initialEdges
          initialKind initialVertex initialOutside initialDelta initialGamma
          initialClosure =>
        exact (Fin.succ_ne_zero t htarget).elim
      | SE i previousProper previousOneUncolored previousClosed
          previousNotStronglyClosed noRevisiting choice seriesAlternative
          currentColoring currentStored currentEdges currentKind currentVertex
          currentOutside currentDelta currentGamma adjoined adjoinedExactly
          closedExtension orderedExtension strictExtension =>
        have hbad : some TashkinovExtensionKind.SE =
            some TashkinovExtensionKind.PE :=
          currentKind.symm.trans (by simpa [htarget] using htKind)
        cases hbad
      | RE i previousProper previousOneUncolored previousClosed
          previousNotStronglyClosed available currentColoring currentStored
          currentEdges currentKind currentVertex currentOutside currentDelta
          currentGamma adjoined adjoinedExactly closedExtension orderedExtension
          strictExtension =>
        have hbad : some TashkinovExtensionKind.RE =
            some TashkinovExtensionKind.PE :=
          currentKind.symm.trans (by simpa [htarget] using htKind)
        cases hbad
      | PE i previousProper previousOneUncolored previousClosed
          previousNotStronglyClosed noRevisiting choice seriesAlternativeFails
          actualGamma gammaRule secondStable secondStableProper
          secondStableOneUncolored secondStableRelation exitWitness
          currentColoring currentProper currentOneUncolored currentStored
          currentEdges currentKind currentVertex currentOutside currentDelta
          currentGamma closedExtension orderedExtension strictExtension =>
        have hi : i = t := by
          apply Fin.ext
          simpa using (congrArg Fin.val htarget).symm
        subst i
        have hgammaEq : actualGamma = gammaT :=
          Option.some.inj
            (currentGamma.symm.trans (by simpa [htarget] using htGamma))
        have hdeltaEq : choice.color = deltaT :=
          Option.some.inj
            (currentDelta.symm.trans (by simpa [htarget] using htDelta))
        rw [show ett.series.data.stored t.succ = {choice.color, actualGamma} by
          simpa [htarget] using currentStored, hgammaEq, hdeltaEq]
        ext c
        simp [or_comm]
    have qStageToFinal : ∀ x : V,
        x ∈ TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc) →
        x ∈ TreeSequenceVertexSet T := by
      intro x hx
      have hxPenultimate : x ∈ TreeSequenceVertexSet
          (ett.series.data.tree ⟨ett.rounds, by omega⟩) := by
        simpa [hqTreeIndex] using hx
      exact vertexTransfer ett.abovePenultimate hxPenultimate
    have hclassPackage : ∀ u : V,
        (ExtensionBaseSupportClass ett v hvFinal u).Nonempty →
        ∃ p : ℕ, ∃ indices : Fin (p + 1) → Fin ett.rounds,
          ∃ gammaClass deltaClass : Fin (p + 1) → Fin k,
            (∀ a b, a.val < b.val →
              (indices a).val < (indices b).val) ∧
            (∀ r : Fin ett.rounds,
              r ∈ ExtensionBaseSupportClass ett v hvFinal u ↔
                ∃ a : Fin (p + 1), indices a = r) ∧
            (∀ a, ett.series.data.gamma (indices a).succ =
              some (gammaClass a)) ∧
            (∀ a, ett.series.data.delta (indices a).succ =
              some (deltaClass a)) ∧
            (∀ a : Fin p, gammaClass a.succ = deltaClass a.castSucc) ∧
            Function.Injective (Fin.cons (gammaClass 0) deltaClass) ∧
            (∀ x : V,
              x ∈ TreeSequenceVertexSet
                  (ett.series.data.tree jSlot.succ.castSucc) →
              (∀ r : Fin ett.rounds,
                r ∈ ExtensionBaseActiveIndices ett v hvFinal →
                ett.series.data.chosenVertex r.succ ≠ some x) →
              MissingColors G sigma x =
                MissingColors G
                  (ett.series.data.coloring jSlot.castSucc) x) ∧
            (let storedPairs := Finset.univ.biUnion fun a : Fin (p + 1) =>
                ett.series.data.stored (indices a).succ
             MissingColors G sigma u ∩ storedPairs =
                  {deltaClass (Fin.last p)} ∧
               MissingColors G (ett.series.data.coloring jSlot.castSucc) u =
                 (MissingColors G sigma u \ {deltaClass (Fin.last p)}) ∪
                   {gammaClass 0}) := by
      intro u hclassNonempty
      obtain ⟨p, indices, huStage, hincreasing, hclass, henumerates⟩ :=
        ExtensionBaseSupportClassEnumeration ett v hvFinal q hqTerminal u
          (fun s x hxFinal hsActive hsChosen =>
            (hsupportOrder.2.1 s x hxFinal hsActive hsChosen).1)
          hclassNonempty
      have hslot : ∀ a : Fin (p + 1), ∃ gammaA deltaA : Fin k,
          ett.series.data.gamma (indices a).succ = some gammaA ∧
            ett.series.data.delta (indices a).succ = some deltaA := by
        intro a
        have henum := (henumerates (indices a)).2 ⟨a, rfl⟩
        obtain ⟨uA, gammaA, deltaA, huA, hgammaA, hdeltaA⟩ :=
          hPESlotData (indices a) henum.2.1
        have huEq : uA = u := Option.some.inj (huA.symm.trans henum.2.2)
        exact ⟨gammaA, deltaA, hgammaA, hdeltaA⟩
      choose gammaClass deltaClass hgammaClass hdeltaClass using hslot
      have huFinal := qStageToFinal u huStage
      have hdeltaAvoids : ∀ a b, a.val ≤ b.val →
          deltaClass b ≠ gammaClass a := by
        intro a b hab
        have haClass := (hclass (indices a)).2 ⟨a, rfl⟩
        have hbClass := (hclass (indices b)).2 ⟨b, rfl⟩
        have haData := haClass
        have hbData := hbClass
        simp only [ExtensionBaseSupportClass, Finset.mem_filter] at haData hbData
        have haActive : indices a ∈ ExtensionBaseActiveIndices ett v hvFinal := by
          exact haData.1
        have hbActive : indices b ∈ ExtensionBaseActiveIndices ett v hvFinal := by
          exact hbData.1
        have habSlots : (indices a).val ≤ (indices b).val := by
          by_cases heq : a = b
          · subst b
            exact le_rfl
          · exact Nat.le_of_lt (hincreasing a b (by omega))
        exact (hdeltaExclusion.1 (indices a) (indices b) u u huFinal huFinal
          (deltaClass b) (gammaClass a) haActive hbActive habSlots
          haData.2 hbData.2 (hdeltaClass b) (hgammaClass a)).2
      obtain ⟨hchain, hinjective⟩ := ExtensionBaseSupportClassColors ett v
        hvFinal q hqTerminal u huStage p indices hincreasing hclass henumerates
        gammaClass deltaClass hgammaClass hdeltaClass hdeltaAvoids
      have hmissing := ExtensionBaseClaimMissingColors ett v hvFinal jSlot q
        hjle hqTerminal hqKind hqVertex hjSlot u huStage p indices hincreasing
        hclass henumerates (gammaClass 0) (deltaClass (Fin.last p))
        (hgammaClass 0) (hdeltaClass (Fin.last p)) sigma hsigmaProper
        hsigmaOne hsigmaTerminal
      exact ⟨p, indices, gammaClass, deltaClass, hincreasing, hclass,
        hgammaClass, hdeltaClass, hchain, hinjective, hmissing⟩
    have hterminalBefore : ∀ (t : Fin ett.rounds) (vt : V),
        t ∈ ExtensionBaseRestorationIndices ett v hvFinal →
        ett.series.data.chosenVertex t.succ = some vt →
        TreeVertexOrder T v vt := by
      intro t vt htRest htVertex
      have htData := htRest
      simp only [ExtensionBaseRestorationIndices, Finset.mem_sdiff] at htData
      have htActive := htData.1
      have htActiveData := htActive
      simp only [ExtensionBaseActiveIndices, Finset.mem_filter,
        Finset.mem_univ, true_and] at htActiveData
      obtain ⟨htFirst, htKind, vt0, hvt0Final, hvt0Vertex, hvt0First⟩ :=
        htActiveData
      have hvt0Eq : vt0 = vt :=
        Option.some.inj (hvt0Vertex.symm.trans htVertex)
      subst vt0
      have horder := (hsupportOrder.2.1 t vt hvt0Final htActive htVertex).2
      exact horder.resolve_left fun hEq => by
        apply htData.2
        simp only [ExtensionBaseSupportClass, Finset.mem_filter]
        exact ⟨htActive, by simpa [hEq] using htVertex⟩
    have hjInitial : ∀ t : Fin ett.rounds,
        t ∈ ExtensionBaseRestorationIndices ett v hvFinal →
        TreeSequenceInitialSegment
          (ett.series.data.tree jSlot.succ.castSucc)
          (ett.series.data.tree t.succ.castSucc) := by
      intro t htRest
      have htData := htRest
      simp only [ExtensionBaseRestorationIndices, Finset.mem_sdiff] at htData
      have htActiveData := htData.1
      simp only [ExtensionBaseActiveIndices, Finset.mem_filter,
        Finset.mem_univ, true_and] at htActiveData
      have hjt : jSlot.val + 1 ≤ t.val + 1 := by
        rw [hjSlot]
        exact htActiveData.1
      have hseg := stageToStage (jSlot.val + 1) (t.val + 1)
        (by omega) hjt (by omega)
      convert hseg using 1 <;> congr 1 <;> apply Fin.ext <;> rfl
    have hslotData : ∀ t : Fin ett.rounds,
        t ∈ ExtensionBaseRestorationIndices ett v hvFinal →
        ∃ vt : V, ∃ gammaT deltaT : Fin k,
          ett.series.data.chosenVertex t.succ = some vt ∧
            ett.series.data.gamma t.succ = some gammaT ∧
            ett.series.data.delta t.succ = some deltaT := by
      intro t htRest
      have htData := htRest
      simp only [ExtensionBaseRestorationIndices, Finset.mem_sdiff] at htData
      have htActiveData := htData.1
      simp only [ExtensionBaseActiveIndices, Finset.mem_filter,
        Finset.mem_univ, true_and] at htActiveData
      exact hPESlotData t htActiveData.2.1
    have hinitialSI : ∀ (t : Fin ett.rounds) (vt : V)
        (gammaT deltaT : Fin k),
        t ∈ ExtensionBaseActiveIndices ett v hvFinal →
        t ≠ q →
        ett.series.data.chosenVertex t.succ = some vt →
        ett.series.data.gamma t.succ = some gammaT →
        ett.series.data.delta t.succ = some deltaT →
        ETTStrongInterchangeable ett t vt sigma gammaT deltaT := by
      intro t vt gammaT deltaT htActive htNe htVertex htGamma htDelta
      have htq : t.val < q.val := by
        have htBound : t.val ≤ q.val := by omega
        exact lt_of_le_of_ne htBound fun h => htNe (Fin.ext h)
      exact hstrongInterchange t vt gammaT deltaT htActive htq htVertex
        htGamma htDelta
    have hclassMissing : ∀ (u : V) (t : Fin ett.rounds)
        (deltaT : Fin k),
        ExtensionBaseSupportClass ett v hvFinal u ⊆
            ExtensionBaseRestorationIndices ett v hvFinal →
        t ∈ ExtensionBaseSupportClass ett v hvFinal u →
        (∀ s : Fin ett.rounds,
          s ∈ ExtensionBaseSupportClass ett v hvFinal u → s.val ≤ t.val) →
        ett.series.data.delta t.succ = some deltaT →
        MissingColors G sigma u ∩
            (ExtensionBaseSupportClass ett v hvFinal u).biUnion
              (fun s => ett.series.data.stored s.succ) = {deltaT} := by
      intro u t deltaT hsubset htClass htMaximum htDelta
      obtain ⟨p, indices, gammaClass, deltaClass, hincreasing, hclass,
          hgammaClass, hdeltaClass, hchain, hinjective, hunsupportedClass,
          hmissing⟩ :=
        hclassPackage u ⟨t, htClass⟩
      dsimp at hmissing
      obtain ⟨aT, haT⟩ := (hclass t).1 htClass
      have haTLast : aT = Fin.last p := by
        by_contra hne
        have haLt : aT < Fin.last p :=
          Fin.lt_last_iff_ne_last.mpr hne
        have hindexLt := hincreasing aT (Fin.last p) haLt
        have hlastClass := (hclass (indices (Fin.last p))).2
          ⟨Fin.last p, rfl⟩
        have hlastLe := htMaximum (indices (Fin.last p)) hlastClass
        rw [haT] at hindexLt
        exact (not_lt_of_ge hlastLe) hindexLt
      have hindexLast : indices (Fin.last p) = t := by
        rw [← haT, haTLast]
      have hdeltaEq : deltaClass (Fin.last p) = deltaT := by
        apply Option.some.inj
        exact (hdeltaClass (Fin.last p)).symm.trans (by
          simpa [hindexLast] using htDelta)
      have hstoredEq :
          Finset.univ.biUnion (fun a : Fin (p + 1) =>
            ett.series.data.stored (indices a).succ) =
          (ExtensionBaseSupportClass ett v hvFinal u).biUnion
            (fun s => ett.series.data.stored s.succ) := by
        ext c
        simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨a, hc⟩
          exact ⟨indices a, (hclass (indices a)).2 ⟨a, rfl⟩, hc⟩
        · rintro ⟨s, hs, hc⟩
          obtain ⟨a, rfl⟩ := (hclass s).1 hs
          exact ⟨a, hc⟩
      rw [← hstoredEq, ← hdeltaEq]
      exact hmissing.1
    have hpairOverlapColors : ∀ (s t : Fin ett.rounds) (vs vt : V)
        (gammaS deltaS gammaT deltaT : Fin k),
        s ∈ ExtensionBaseActiveIndices ett v hvFinal →
        t ∈ ExtensionBaseActiveIndices ett v hvFinal →
        s.val < t.val →
        ett.series.data.chosenVertex s.succ = some vs →
        ett.series.data.chosenVertex t.succ = some vt →
        ett.series.data.gamma s.succ = some gammaS →
        ett.series.data.delta s.succ = some deltaS →
        ett.series.data.gamma t.succ = some gammaT →
        ett.series.data.delta t.succ = some deltaT →
        ((({gammaS, deltaS} : Finset (Fin k)) ∩ {gammaT, deltaT}).Nonempty ↔
          vs = vt ∧ ¬ ∃ r : Fin ett.rounds,
            r ∈ ExtensionBaseSupportClass ett v hvFinal vs ∧
              s.val < r.val ∧ r.val < t.val ∧
              ett.series.data.chosenVertex r.succ = some vs) ∧
        ((({gammaS, deltaS} : Finset (Fin k)) ∩
            {gammaT, deltaT}).Nonempty →
          ({gammaS, deltaS} : Finset (Fin k)) ∩ {gammaT, deltaT} =
              {gammaT} ∧
            ({gammaS, deltaS} : Finset (Fin k)) ∩ {gammaT, deltaT} =
              {deltaS}) := by
      intro s t vs vt gammaS deltaS gammaT deltaT hs ht hst hsVertex htVertex
        hsGamma hsDelta htGamma htDelta
      have hsData := hs
      have htData := ht
      simp only [ExtensionBaseActiveIndices, Finset.mem_filter,
        Finset.mem_univ, true_and] at hsData htData
      obtain ⟨hsFirst, hsKind, vs0, hvsFinal, hvsChosen, hvsFirst⟩ := hsData
      obtain ⟨htFirst, htKind, vt0, hvtFinal, hvtChosen, hvtFirst⟩ := htData
      have hvsEq : vs0 = vs :=
        Option.some.inj (hvsChosen.symm.trans hsVertex)
      have hvtEq : vt0 = vt :=
        Option.some.inj (hvtChosen.symm.trans htVertex)
      subst vs0
      subst vt0
      have hsStored := hPEStored s gammaS deltaS hsKind hsGamma hsDelta
      have htStored := hPEStored t gammaT deltaT htKind htGamma htDelta
      have hoverlap :=
        hpairOverlap s t vs vt hvsFinal hvtFinal gammaS deltaS gammaT deltaT
          hs ht hst hsVertex htVertex hsGamma hsDelta htGamma htDelta
      rw [hsStored, htStored] at hoverlap
      refine ⟨?_, hoverlap.2⟩
      constructor
      · intro hnonempty
        obtain ⟨hvs, hbetween⟩ := hoverlap.1.mp hnonempty
        refine ⟨hvs, ?_⟩
        rintro ⟨r, hrClass, hsr, hrt, hrVertex⟩
        have hrData :
            r ∈ ExtensionBaseActiveIndices ett v hvFinal ∧
              ett.series.data.chosenVertex r.succ = some vs := by
          simpa [ExtensionBaseSupportClass] using hrClass
        exact hbetween ⟨r, hrData.1, hsr, hrt, hrVertex⟩
      · rintro ⟨hvs, hbetween⟩
        apply hoverlap.1.mpr
        refine ⟨hvs, ?_⟩
        rintro ⟨r, hrActive, hsr, hrt, hrVertex⟩
        apply hbetween
        refine ⟨r, ?_, hsr, hrt, hrVertex⟩
        simp [ExtensionBaseSupportClass, hrActive, hrVertex]
    obtain ⟨trace, hinvariant⟩ := ExtensionBaseAlgorithmA ett v hvFinal
      jSlot q sigma hqTerminal hqKind hqVertex hjSlot hsigmaProper hsigmaOne
      hterminalBefore hjInitial hslotData hinitialSI hclassMissing
      hpairOverlapColors
    have hterminalJ : v ∈ TreeSequenceVertexSet
        (ett.series.data.tree jSlot.succ.castSucc) := by
      unfold ETTFirstAppearanceIndex at hjSlot
      dsimp at hjSlot
      let candidates : Finset (Fin (ett.rounds + 1)) :=
        Finset.univ.filter fun i =>
          v ∈ TreeSequenceVertexSet (ExtendedTashkinovLadderStage ett i)
      have hlast : Fin.last ett.rounds ∈ candidates := by
        simp only [candidates, Finset.mem_filter, Finset.mem_univ, true_and]
        have hfinal : ExtendedTashkinovLadderStage ett
            (Fin.last ett.rounds) = T := by
          unfold ExtendedTashkinovLadderStage
          exact Fin.lastCases_last
        rw [hfinal]
        exact hvFinal
      have hfirstEq : jSlot.val + 1 =
          (candidates.min' ⟨Fin.last ett.rounds, hlast⟩).val + 1 := by
        simpa [candidates] using hjSlot
      have hminVal :
          (candidates.min' ⟨Fin.last ett.rounds, hlast⟩).val =
            jSlot.val := by
        omega
      have hminEq : candidates.min' ⟨Fin.last ett.rounds, hlast⟩ =
          jSlot.castSucc := by
        apply Fin.ext
        simpa using hminVal
      have hjMember : jSlot.castSucc ∈ candidates := by
        rw [← hminEq]
        exact Finset.min'_mem candidates ⟨Fin.last ett.rounds, hlast⟩
      simp only [candidates, Finset.mem_filter, Finset.mem_univ, true_and]
        at hjMember
      simpa [ExtendedTashkinovLadderStage, Fin.lastCases_castSucc] using
        hjMember
    have hqActive : q ∈ ExtensionBaseActiveIndices ett v hvFinal := by
      simp only [ExtensionBaseActiveIndices, Finset.mem_filter,
        Finset.mem_univ, true_and]
      exact ⟨hfirstUpper, hqKind, v, hvFinal, hqVertex, le_rfl⟩
    have hqClass : q ∈ ExtensionBaseSupportClass ett v hvFinal v := by
      simp [ExtensionBaseSupportClass, hqActive, hqVertex]
    obtain ⟨p0, indices0, gamma0, delta0, hincreasing0, hclass0,
        hgamma0, hdelta0, hchain0, hinjective0, hunsupported, hmissing0⟩ :=
      hclassPackage v ⟨q, hqClass⟩
    have hclassPrepared : ∀ x : V,
        x ∈ TreeSequenceVertexSet
            (ett.series.data.tree jSlot.succ.castSucc) →
        x ≠ v →
        (∃ t : Fin ett.rounds,
          t ∈ ExtensionBaseRestorationIndices ett v hvFinal ∧
            ett.series.data.chosenVertex t.succ = some x) →
        ∃ p : ℕ, ∃ indices : Fin (p + 1) → Fin ett.rounds,
          ∃ gammaClass deltaClass : Fin (p + 1) → Fin k,
            (∀ a b, a.val < b.val →
              (indices a).val < (indices b).val) ∧
            (∀ r : Fin ett.rounds,
              r ∈ ExtensionBaseSupportClass ett v hvFinal x ↔
                ∃ a : Fin (p + 1), indices a = r) ∧
            (∀ a, ett.series.data.gamma (indices a).succ =
              some (gammaClass a)) ∧
            (∀ a, ett.series.data.delta (indices a).succ =
              some (deltaClass a)) ∧
            (∀ a : Fin p, gammaClass a.succ = deltaClass a.castSucc) ∧
            Function.Injective (Fin.cons (gammaClass 0) deltaClass) ∧
            MissingColors G (ett.series.data.coloring jSlot.castSucc) x =
              (MissingColors G sigma x \ {deltaClass (Fin.last p)}) ∪
                {gammaClass 0} := by
      intro x hxJ hxNe
      rintro ⟨t, htRest, htVertex⟩
      have htData := htRest
      simp only [ExtensionBaseRestorationIndices, Finset.mem_sdiff] at htData
      have htClass : t ∈ ExtensionBaseSupportClass ett v hvFinal x := by
        simp [ExtensionBaseSupportClass, htData.1, htVertex]
      obtain ⟨p, indices, gammaClass, deltaClass, hincreasing, hclass,
          hgammaClass, hdeltaClass, hchain, hinjective,
          hunsupportedClass, hmissing⟩ := hclassPackage x ⟨t, htClass⟩
      dsimp at hmissing
      exact ⟨p, indices, gammaClass, deltaClass, hincreasing, hclass,
        hgammaClass, hdeltaClass, hchain, hinjective, hmissing.2⟩
    have hclaim43 := ExtensionBaseClaim43 ett v hvFinal jSlot q hjle
      hqTerminal hqKind hqVertex hjSlot sigma
      (TashkinovStoredColors ett.series.data jSlot.castSucc) hterminalJ
      hsigmaProper hsigmaOne hsigmaTerminal hsigmaBefore trace hinvariant
      hunsupported hclassPrepared
    dsimp at hclaim43
    obtain ⟨hb1, hb2, hb3, hb4, hb5⟩ := hclaim43
    let rho1 : PartialEdgeColoring E k :=
      trace.coloring (Fin.last trace.steps)
    have hrho1Proper : IsProperEdgeColoring G rho1 := by
      simpa [rho1] using (hinvariant.1 (Fin.last trace.steps)).1
    have hrho1One : IsOneEdgeUncolored rho1 e0 := by
      simpa [rho1] using (hinvariant.1 (Fin.last trace.steps)).2
    have hb1Rho : StableColoringBeforeVertex T v hvFinal
        (TashkinovStoredColors ett.series.data jSlot.castSucc)
        (ett.series.data.coloring jSlot.castSucc) rho1 := by
      simpa [rho1] using hb1
    have hb2Missing :
        (∀ x : V,
          x ∈ (TreeSequenceVertexSet
              (ett.series.data.tree jSlot.succ.castSucc)).erase v →
          MissingColors G rho1 x =
            MissingColors G
              (ett.series.data.coloring jSlot.castSucc) x) ∧
        MissingColors G rho1 v = MissingColors G sigma v := by
      simpa [rho1] using hb2
    have hb2TreeEdges : ∀ a : Fin
        (ett.series.data.tree jSlot.succ.castSucc).length,
        rho1 ((ett.series.data.tree jSlot.succ.castSucc).edge a) =
            sigma ((ett.series.data.tree jSlot.succ.castSucc).edge a) ∧
          sigma ((ett.series.data.tree jSlot.succ.castSucc).edge a) =
            ett.series.data.coloring jSlot.castSucc
              ((ett.series.data.tree jSlot.succ.castSucc).edge a) := by
      simpa [rho1] using hb3
    have hb3EdgeEffects : ∀ f : E, rho1 f ≠ sigma f →
        f ∉ InternalEdges G
            (TreeSequenceVertexSet
              (ett.series.data.tree jSlot.succ.castSucc)) ∧
          ∃ c d : Fin k, sigma f = some c ∧ rho1 f = some d ∧
            c ∈ (ExtensionBaseRestorationIndices ett v hvFinal).biUnion
              (fun t => ett.series.data.stored t.succ) ∧
            d ∈ (ExtensionBaseRestorationIndices ett v hvFinal).biUnion
              (fun t => ett.series.data.stored t.succ) := by
      simpa [rho1] using hb4
    have hb4Interchange : ∀ (s : Fin ett.rounds)
        (gammaS deltaS : Fin k),
        s ∈ ExtensionBaseSupportClass ett v hvFinal v →
        s ≠ q →
        ett.series.data.chosenVertex s.succ = some v →
        ett.series.data.gamma s.succ = some gammaS →
        ett.series.data.delta s.succ = some deltaS →
        ETTStrongInterchangeable ett s v rho1 gammaS deltaS := by
      simpa [rho1] using hb5
    classical
    obtain ⟨terminalPosition, -, hterminalAt⟩ :=
      Finset.mem_image.mp hterminalJ
    have hterminalPositionPositive : 1 ≤ terminalPosition.val := by
      generalize htarget : q.succ = target
      cases hcert : ett.series.certified target with
      | initial => exact (Fin.succ_ne_zero q htarget).elim
      | SE i previousProper previousOneUncolored previousClosed
          previousNotStronglyClosed noRevisiting choice seriesAlternative
          currentColoring currentStored currentEdges currentKind currentVertex
          currentOutside currentDelta currentGamma adjoined adjoinedExactly
          closedExtension orderedExtension strictExtension =>
        have hbad : some TashkinovExtensionKind.SE =
            some TashkinovExtensionKind.PE :=
          currentKind.symm.trans (by simpa [htarget] using hqKind)
        cases hbad
      | RE i previousProper previousOneUncolored previousClosed
          previousNotStronglyClosed available currentColoring currentStored
          currentEdges currentKind currentVertex currentOutside currentDelta
          currentGamma adjoined adjoinedExactly closedExtension orderedExtension
          strictExtension =>
        have hbad : some TashkinovExtensionKind.RE =
            some TashkinovExtensionKind.PE :=
          currentKind.symm.trans (by simpa [htarget] using hqKind)
        cases hbad
      | PE i previousProper previousOneUncolored previousClosed
          previousNotStronglyClosed noRevisiting choice seriesAlternativeFails
          chosenGamma gammaRule secondStable secondStableProper
          secondStableOneUncolored secondStableRelation exitWitness
          currentColoring currentProper currentOneUncolored currentStored
          currentEdges currentKind currentVertex currentOutside currentDelta
          currentGamma closedExtension orderedExtension strictExtension =>
        have hi : i = q := by
          apply Fin.ext
          simpa using (congrArg Fin.val htarget).symm
        subst i
        have hvChoice : choice.vertex = v :=
          Option.some.inj
            (currentVertex.symm.trans (by simpa [htarget] using hqVertex))
        obtain ⟨defectiveColor, hdefective, hedgeBoundary⟩ :=
          choice.edgeDefective
        have hdefectiveColor : defectiveColor = choice.color := by
          have hedgeColor := (Finset.mem_filter.mp hedgeBoundary).2
          exact Option.some.inj (hedgeColor.symm.trans choice.edgeColor)
        let boundary := BoundaryColorEdges G choice.selected
          (TreeSequenceVertexSet
            (ett.series.data.tree q.succ.castSucc)) defectiveColor
        have hboundaryCard : 1 < boundary.card := by
          dsimp [boundary]
          exact Nat.lt_of_lt_of_le Nat.one_lt_two hdefective
        rcases Finset.exists_mem_ne hboundaryCard choice.edge with
          ⟨f, hfBoundary, hfNe⟩
        have hfBoundaryEdge : f ∈ BoundaryEdges G
            (TreeSequenceVertexSet
              (ett.series.data.tree q.succ.castSucc)) :=
          (Finset.mem_filter.mp hfBoundary).1
        have hfColor : choice.selected f = some choice.color := by
          have hc := (Finset.mem_filter.mp hfBoundary).2
          simpa [hdefectiveColor] using hc
        simp [BoundaryEdges] at hfBoundaryEdge
        obtain ⟨x, hxStage, xout, hends⟩ := hfBoundaryEdge
        rcases hends with ⟨hxout, hends⟩
        have hxf : Incident G x f := by
          change x ∈ G.ends f
          rw [hends]
          simp
        have hxDefective : DefectiveVertex G choice.selected
            (TreeSequenceVertexSet
              (ett.series.data.tree q.succ.castSucc)) x := by
          refine ⟨hxStage, f, ⟨defectiveColor, hdefective, hfBoundary⟩, hxf⟩
        have hxOrderOr := choice.maximal choice.selected x
          choice.selectedProper choice.selectedOneUncolored
          choice.selectedStable hxDefective
        have hxNe : x ≠ choice.vertex := by
          intro hxv
          have hadjacent : AdjacentEdges G choice.edge f :=
            ⟨choice.vertex, choice.edgeIncident, hxv ▸ hxf⟩
          exact choice.selectedProper hfNe.symm hadjacent choice.edgeColor
            hfColor
        have hxOrder : TreeVertexOrder
            (ett.series.data.tree q.succ.castSucc) x v := by
          simpa [hvChoice] using hxOrderOr.resolve_left hxNe
        have hTjQ : TreeSequenceInitialSegment
            (ett.series.data.tree jSlot.succ.castSucc)
            (ett.series.data.tree q.succ.castSucc) := by
          have hseg := stageToStage (jSlot.val + 1) (q.val + 1)
            (by omega) (by omega) (by omega)
          convert hseg using 1 <;> congr 1 <;> apply Fin.ext <;> rfl
        let terminalQ : Fin
            ((ett.series.data.tree q.succ.castSucc).length + 1) :=
          Fin.castLE (Nat.succ_le_succ hTjQ.1) terminalPosition
        have hterminalQ :
            (ett.series.data.tree q.succ.castSucc).vertex terminalQ = v := by
          exact (hTjQ.2.1 terminalPosition).trans hterminalAt
        rcases hxOrder with ⟨ix, iv, hix, hiv, hlt⟩
        have hivEq : iv = terminalQ := by
          apply (ett.series.data.tree q.succ.castSucc).vertex_injective
          exact hiv.trans hterminalQ.symm
        rw [hivEq] at hlt
        change ix.val < terminalPosition.val at hlt
        omega
    have hterminalPositionBound : terminalPosition.val ≤
        (ett.series.data.tree jSlot.succ.castSucc).length :=
      Nat.le_of_lt_succ terminalPosition.isLt
    let seed : TreeSequence G e0 :=
      TreeSequencePrefix (ett.series.data.tree jSlot.succ.castSucc)
        terminalPosition.val hterminalPositionPositive hterminalPositionBound
    have hjTreeIndex : jSlot.castSucc.succ = jSlot.succ.castSucc := by
      apply Fin.ext
      rfl
    have hseedTj : TreeSequenceInitialSegment seed
        (ett.series.data.tree jSlot.succ.castSucc) := by
      refine ⟨?_, ?_, ?_⟩
      · change terminalPosition.val ≤
          (ett.series.data.tree jSlot.castSucc.succ).length
        rw [hjTreeIndex]
        exact hterminalPositionBound
      · intro i
        rfl
      · intro i
        rfl
    have hseedTerminal : seed.vertex (Fin.last seed.length) = v := by
      have hlast : Fin.castLE (Nat.succ_le_succ hterminalPositionBound)
          (Fin.last terminalPosition.val) = terminalPosition := by
        apply Fin.ext
        simp
      simpa [seed, TreeSequencePrefix, hlast] using hterminalAt
    have hTjQ : TreeSequenceInitialSegment
        (ett.series.data.tree jSlot.succ.castSucc)
        (ett.series.data.tree q.succ.castSucc) := by
      have hseg := stageToStage (jSlot.val + 1) (q.val + 1)
        (by omega) (by omega) (by omega)
      convert hseg using 1 <;> congr 1 <;> apply Fin.ext <;> rfl
    have hqFinal : TreeSequenceInitialSegment
        (ett.series.data.tree q.succ.castSucc) T := by
      simpa [hqTreeIndex] using ett.abovePenultimate
    have hseedFinal : TreeSequenceInitialSegment seed T :=
      segmentTrans hseedTj (segmentTrans hTjQ hqFinal)
    have hseedVertexBefore (i : Fin (seed.length + 1))
        (hi : i.val < seed.length) :
        seed.vertex i ∈ TreeVerticesBefore T v hvFinal := by
      unfold TreeVerticesBefore
      apply Finset.mem_filter.mpr
      constructor
      · exact vertexTransfer hseedFinal (by simp [TreeSequenceVertexSet])
      · let p : Fin (T.length + 1) :=
          Fin.castLE (Nat.succ_le_succ hseedFinal.1) i
        let z : Fin (T.length + 1) :=
          Fin.castLE (Nat.succ_le_succ hseedFinal.1) (Fin.last seed.length)
        refine ⟨p, z, hseedFinal.2.1 i,
          (hseedFinal.2.1 (Fin.last seed.length)).trans hseedTerminal, ?_⟩
        simpa [p, z] using hi
    have segmentVertexBefore {A : TreeSequence G e0}
        (hAseed : TreeSequenceInitialSegment A seed)
        (hAlen : A.length < seed.length) {x : V}
        (hxA : x ∈ TreeSequenceVertexSet A) :
        x ∈ TreeVerticesBefore T v hvFinal := by
      obtain ⟨hAseedLen, hAseedVertices, -⟩ := hAseed
      simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ,
        true_and] at hxA
      obtain ⟨i, rfl⟩ := hxA
      have hi : (Fin.castLE (Nat.succ_le_succ hAseedLen) i).val <
          seed.length := by
        change i.val < seed.length
        omega
      rw [← hAseedVertices i]
      exact hseedVertexBefore _ hi
    have transportStep {A B : TreeSequence G e0}
        (hstep : TashkinovAugmentation
          (ett.series.data.coloring jSlot.castSucc) A B)
        (hBseed : TreeSequenceInitialSegment B seed) :
        TashkinovAugmentation rho1 A B := by
      rcases hstep with ⟨hlen, hAB, c, hcolor, hcMissing⟩
      have hAseed : TreeSequenceInitialSegment A seed :=
        segmentTrans hAB hBseed
      have hAlen : A.length < seed.length :=
        lt_of_lt_of_le (by omega) hBseed.1
      have hcMissingRho : c ∈ TreeMissingColors rho1 A := by
        unfold TreeMissingColors at hcMissing ⊢
        obtain ⟨x, hxA, hcx⟩ := Finset.mem_biUnion.mp hcMissing
        refine Finset.mem_biUnion.mpr ⟨x, hxA, ?_⟩
        rw [hb1Rho.2 x (segmentVertexBefore hAseed hAlen hxA)]
        exact hcx
      let added : Fin B.length := Fin.cast hlen.symm (Fin.last A.length)
      obtain ⟨attach, hattach⟩ := B.attaches added
      let oldPosition : Fin (B.length + 1) :=
        Fin.castLT attach
          (Nat.lt_trans attach.isLt (Nat.succ_lt_succ added.isLt))
      have holdValue : oldPosition.val < A.length + 1 := by
        dsimp [oldPosition, added]
        omega
      let oldA : Fin (A.length + 1) := ⟨oldPosition.val, holdValue⟩
      have holdEq : B.vertex oldPosition = A.vertex oldA := by
        have hcast : Fin.castLE (Nat.succ_le_succ hAB.1) oldA =
            oldPosition := by
          apply Fin.ext
          rfl
        rw [← hcast]
        exact hAB.2.1 oldA
      have holdA : A.vertex oldA ∈ TreeSequenceVertexSet A := by
        simp [TreeSequenceVertexSet]
      have holdBefore : B.vertex oldPosition ∈
          TreeVerticesBefore T v hvFinal := by
        rw [holdEq]
        exact segmentVertexBefore hAseed hAlen holdA
      have holdIncident : Incident G (B.vertex oldPosition) (B.edge added) := by
        unfold Incident
        rw [hattach]
        simp [oldPosition]
      have haddedFixed : rho1 (B.edge added) =
          ett.series.data.coloring jSlot.castSucc (B.edge added) := by
        apply hb1Rho.1 (B.edge added)
          ⟨B.vertex oldPosition, holdBefore, holdIncident⟩
        refine ⟨c, ?_, hcolor⟩
        apply Finset.mem_union_left
        unfold TreeMissingColors at hcMissing
        obtain ⟨x, hxA, hcx⟩ := Finset.mem_biUnion.mp hcMissing
        exact Finset.mem_biUnion.mpr
          ⟨x, segmentVertexBefore hAseed hAlen hxA, hcx⟩
      refine ⟨hlen, hAB, c, ?_, hcMissingRho⟩
      change rho1 (B.edge added) = some c
      exact haddedFixed.trans hcolor
    have transportSeedRoute (S : TreeSequence G e0)
        (hroute : TashkinovAugmentationSequence
          (ett.series.data.coloring jSlot.castSucc) S seed) :
        TashkinovAugmentationSequence rho1 S seed := by
      unfold TashkinovAugmentationSequence at hroute ⊢
      induction hroute using Relation.ReflTransGen.head_induction_on with
      | refl => exact Relation.ReflTransGen.refl
      | @head A B hAB hBseed ih =>
        have hBsegment : TreeSequenceInitialSegment B seed :=
          TashkinovAugmentationSequenceInitialSegment
            (ett.series.data.coloring jSlot.castSucc) B seed hBseed
        exact Relation.ReflTransGen.head (transportStep hAB hBsegment) ih
    have commonPrefix {A B C : TreeSequence G e0}
        (hAC : TreeSequenceInitialSegment A C)
        (hBC : TreeSequenceInitialSegment B C)
        (hlen : A.length ≤ B.length) :
        TreeSequenceInitialSegment A B := by
      rcases hAC with ⟨hACLen, hACVertices, hACEdges⟩
      rcases hBC with ⟨hBCLen, hBCVertices, hBCEdges⟩
      refine ⟨hlen, ?_, ?_⟩
      · intro i
        calc
          B.vertex (Fin.castLE (Nat.succ_le_succ hlen) i) =
              C.vertex (Fin.castLE (Nat.succ_le_succ hBCLen)
                (Fin.castLE (Nat.succ_le_succ hlen) i)) :=
            (hBCVertices _).symm
          _ = C.vertex (Fin.castLE (Nat.succ_le_succ hACLen) i) := by
            congr 1
          _ = A.vertex i := hACVertices i
      · intro i
        calc
          B.edge (Fin.castLE hlen i) =
              C.edge (Fin.castLE hBCLen (Fin.castLE hlen i)) :=
            (hBCEdges _).symm
          _ = C.edge (Fin.castLE hACLen i) := by congr 1
          _ = A.edge i := hACEdges i
    let supportColors := Finset.univ.biUnion fun a : Fin (p0 + 1) =>
      ett.series.data.stored (indices0 a).succ
    obtain ⟨TjPrime, hclosure, hprimeElementary, hcaseSplit⟩ :
        ∃ TjPrime : TreeSequence G e0,
          TashkinovClosure rho1 seed TjPrime ∧
            ColoredVertexSetElementary G rho1
              (TreeSequenceVertexSet TjPrime) ∧
            (let awayMissing :=
              ((TreeSequenceVertexSet TjPrime).erase v).biUnion
                fun x => MissingColors G rho1 x
             (awayMissing ∩ supportColors).Nonempty ∨
               awayMissing ∩ supportColors = ∅) := by
      by_cases hjPositive : 0 < jSlot.val
      · let Tprevious : TreeSequence G e0 :=
          ett.series.data.tree jSlot.castSucc.castSucc
        have hpreviousTj : TreeSequenceInitialSegment Tprevious
            (ett.series.data.tree jSlot.succ.castSucc) := by
          have hstep := stepSegment jSlot.castSucc (by simpa using hjPositive)
          rw [hjTreeIndex] at hstep
          exact hstep
        have hvNotPrevious : v ∉ TreeSequenceVertexSet Tprevious := by
          intro hvPrevious
          let candidates : Finset (Fin (ett.rounds + 1)) :=
            Finset.univ.filter fun i =>
              v ∈ TreeSequenceVertexSet (ExtendedTashkinovLadderStage ett i)
          have hlast : Fin.last ett.rounds ∈ candidates := by
            simp only [candidates, Finset.mem_filter, Finset.mem_univ, true_and]
            rw [show ExtendedTashkinovLadderStage ett
                (Fin.last ett.rounds) = T by
              unfold ExtendedTashkinovLadderStage
              exact Fin.lastCases_last]
            exact hvFinal
          have hfirst := hjSlot
          unfold ETTFirstAppearanceIndex at hfirst
          dsimp at hfirst
          have hminimumValue :
              (candidates.min' ⟨Fin.last ett.rounds, hlast⟩).val =
                jSlot.val := by
            change jSlot.val + 1 =
              (candidates.min' ⟨Fin.last ett.rounds, hlast⟩).val + 1 at hfirst
            omega
          let previousSlot : Fin ett.rounds :=
            ⟨jSlot.val - 1, by omega⟩
          have hpreviousIndex : previousSlot.succ = jSlot.castSucc := by
            apply Fin.ext
            simp [previousSlot]
            omega
          have hpreviousMember : previousSlot.castSucc ∈ candidates := by
            simp only [candidates, Finset.mem_filter, Finset.mem_univ, true_and]
            rw [show ExtendedTashkinovLadderStage ett previousSlot.castSucc =
                Tprevious by
              unfold ExtendedTashkinovLadderStage
              rw [Fin.lastCases_castSucc, hpreviousIndex]
              ]
            exact hvPrevious
          have hminimum := Finset.min'_le candidates previousSlot.castSucc
            hpreviousMember
          have hminimumVal := Fin.le_iff_val_le_val.mp hminimum
          rw [hminimumValue] at hminimumVal
          dsimp [previousSlot] at hminimumVal
          omega
        have hpreviousStrict : Tprevious.length < seed.length := by
          by_contra hnot
          have hpositionLe : terminalPosition.val ≤ Tprevious.length := by
            simpa [seed, TreeSequencePrefix] using Nat.le_of_not_gt hnot
          let previousPosition : Fin (Tprevious.length + 1) :=
            ⟨terminalPosition.val, by omega⟩
          have hcast : Fin.castLE (Nat.succ_le_succ hpreviousTj.1)
              previousPosition = terminalPosition := by
            apply Fin.ext
            rfl
          apply hvNotPrevious
          simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ,
            true_and]
          refine ⟨previousPosition, ?_⟩
          have hvertex := hpreviousTj.2.1 previousPosition
          rw [hcast] at hvertex
          exact hvertex.symm.trans hterminalAt
        have hpreviousSeed : TreeSequenceInitialSegment Tprevious seed :=
          commonPrefix hpreviousTj hseedTj (Nat.le_of_lt hpreviousStrict)
        have hseedBuild :
            (ett.series.data.kind jSlot.castSucc =
                some TashkinovExtensionKind.PE ∧
              TashkinovAugmentationSequence
                (ett.series.data.coloring jSlot.castSucc) Tprevious seed) ∨
            ((ett.series.data.kind jSlot.castSucc =
                  some TashkinovExtensionKind.SE ∨
                ett.series.data.kind jSlot.castSucc =
                  some TashkinovExtensionKind.RE) ∧
              ∃ (f : E) (adjoinSeed : TreeSequence G e0),
                ett.series.data.connectingEdges jSlot.castSucc = {f} ∧
                  TreeSequenceAdjoinEdge Tprevious f adjoinSeed ∧
                  TashkinovAugmentationSequence
                    (ett.series.data.coloring jSlot.castSucc)
                    adjoinSeed seed) := by
          generalize htarget : jSlot.castSucc = target
          cases ett.series.certified target with
          | initial =>
              have hzero := congrArg Fin.val htarget
              simp at hzero
              omega
          | SE i previousProper previousOneUncolored previousClosed
              previousNotStronglyClosed noRevisiting choice seriesAlternative
              currentColoring currentStored currentEdges currentKind currentVertex
              currentOutside currentDelta currentGamma adjoined adjoinedExactly
              closedExtension orderedExtension strictExtension =>
            have hi : i.succ = jSlot.castSucc := htarget.symm
            have hroute : TashkinovAugmentationSequence
                (ett.series.data.coloring jSlot.castSucc) adjoined
                (ett.series.data.tree jSlot.succ.castSucc) := by
              have h := closedExtension.1
              rw [hi, hjTreeIndex] at h
              exact h
            have hadjoinedTj : TreeSequenceInitialSegment adjoined
                (ett.series.data.tree jSlot.succ.castSucc) :=
              TashkinovAugmentationSequenceInitialSegment _ _ _ hroute
            have hadjoinedLength : adjoined.length ≤ seed.length := by
              rcases adjoinedExactly with ⟨hlen, -, -⟩
              have hpreviousEq :
                  ett.series.data.tree i.succ.castSucc = Tprevious := by
                rw [hi]
              rw [hpreviousEq] at hlen
              rw [hlen]
              omega
            have hadjoinedSeed : TreeSequenceInitialSegment adjoined seed :=
              commonPrefix hadjoinedTj hseedTj hadjoinedLength
            right
            refine ⟨Or.inl (by simpa [htarget] using currentKind),
              choice.edge, adjoined, ?_, ?_, ?_⟩
            · simpa [htarget] using currentEdges
            · rcases adjoinedExactly with ⟨hlen, hsegment, hedge⟩
              have hiCast : i.castSucc.succ =
                  jSlot.castSucc.castSucc := by
                apply Fin.ext
                simpa using congrArg Fin.val hi
              have hlenNew : adjoined.length = Tprevious.length + 1 := by
                simpa [Tprevious, hiCast] using hlen
              have hsegmentNew : TreeSequenceInitialSegment Tprevious
                  adjoined := by
                simpa [Tprevious, hiCast] using hsegment
              refine ⟨hlenNew, hsegmentNew, ?_⟩
              have haddedIndex :
                  Fin.cast hlenNew.symm (Fin.last Tprevious.length) =
                    Fin.cast hlen.symm
                      (Fin.last
                        (ett.series.data.tree i.succ.castSucc).length) := by
                apply Fin.ext
                simp [Tprevious, hiCast]
              rw [haddedIndex]
              exact hedge
            · simpa [hi] using
                (TashkinovAugmentationSequenceRestrict
                  (ett.series.data.coloring jSlot.castSucc) adjoined seed
                  (ett.series.data.tree jSlot.succ.castSucc) hroute
                  hadjoinedSeed hseedTj)
          | PE i previousProper previousOneUncolored previousClosed
              previousNotStronglyClosed noRevisiting choice seriesAlternativeFails
              chosenGamma gammaRule secondStable secondStableProper
              secondStableOneUncolored secondStableRelation exitWitness
              currentColoring currentProper currentOneUncolored currentStored
              currentEdges currentKind currentVertex currentOutside currentDelta
              currentGamma closedExtension orderedExtension strictExtension =>
            have hi : i.succ = jSlot.castSucc := htarget.symm
            have hroute : TashkinovAugmentationSequence
                (ett.series.data.coloring jSlot.castSucc) Tprevious
                (ett.series.data.tree jSlot.succ.castSucc) := by
              have h := closedExtension.1
              rw [hi, hjTreeIndex] at h
              exact h
            left
            refine ⟨by simpa [htarget] using currentKind, ?_⟩
            simpa [hi] using
              (TashkinovAugmentationSequenceRestrict
                (ett.series.data.coloring jSlot.castSucc) Tprevious seed
                (ett.series.data.tree jSlot.succ.castSucc) hroute
                hpreviousSeed hseedTj)
          | RE i previousProper previousOneUncolored previousClosed
              previousNotStronglyClosed available currentColoring currentStored
              currentEdges currentKind currentVertex currentOutside currentDelta
              currentGamma adjoined adjoinedExactly closedExtension orderedExtension
              strictExtension =>
            have hi : i.succ = jSlot.castSucc := htarget.symm
            have hroute : TashkinovAugmentationSequence
                (ett.series.data.coloring jSlot.castSucc) adjoined
                (ett.series.data.tree jSlot.succ.castSucc) := by
              have h := closedExtension.1
              rw [hi, hjTreeIndex] at h
              exact h
            have hadjoinedTj : TreeSequenceInitialSegment adjoined
                (ett.series.data.tree jSlot.succ.castSucc) :=
              TashkinovAugmentationSequenceInitialSegment _ _ _ hroute
            have hadjoinedLength : adjoined.length ≤ seed.length := by
              rcases adjoinedExactly with ⟨hlen, -, -⟩
              have hpreviousEq :
                  ett.series.data.tree i.succ.castSucc = Tprevious := by
                rw [hi]
              rw [hpreviousEq] at hlen
              rw [hlen]
              omega
            have hadjoinedSeed : TreeSequenceInitialSegment adjoined seed :=
              commonPrefix hadjoinedTj hseedTj hadjoinedLength
            right
            refine ⟨Or.inr (by simpa [htarget] using currentKind),
              available.edge, adjoined, ?_, ?_, ?_⟩
            · simpa [htarget] using currentEdges
            · rcases adjoinedExactly with ⟨hlen, hsegment, hedge⟩
              have hiCast : i.castSucc.succ =
                  jSlot.castSucc.castSucc := by
                apply Fin.ext
                simpa using congrArg Fin.val hi
              have hlenNew : adjoined.length = Tprevious.length + 1 := by
                simpa [Tprevious, hiCast] using hlen
              have hsegmentNew : TreeSequenceInitialSegment Tprevious
                  adjoined := by
                simpa [Tprevious, hiCast] using hsegment
              refine ⟨hlenNew, hsegmentNew, ?_⟩
              have haddedIndex :
                  Fin.cast hlenNew.symm (Fin.last Tprevious.length) =
                    Fin.cast hlen.symm
                      (Fin.last
                        (ett.series.data.tree i.succ.castSucc).length) := by
                apply Fin.ext
                simp [Tprevious, hiCast]
              rw [haddedIndex]
              exact hedge
            · simpa [hi] using
                (TashkinovAugmentationSequenceRestrict
                  (ett.series.data.coloring jSlot.castSucc) adjoined seed
                  (ett.series.data.tree jSlot.succ.castSucc) hroute
                  hadjoinedSeed hseedTj)
        have hseedBuildRho :
            (ett.series.data.kind jSlot.castSucc =
                some TashkinovExtensionKind.PE ∧
              TashkinovAugmentationSequence rho1 Tprevious seed) ∨
            ((ett.series.data.kind jSlot.castSucc =
                  some TashkinovExtensionKind.SE ∨
                ett.series.data.kind jSlot.castSucc =
                  some TashkinovExtensionKind.RE) ∧
              ∃ (f : E) (adjoinSeed : TreeSequence G e0),
                ett.series.data.connectingEdges jSlot.castSucc = {f} ∧
                  TreeSequenceAdjoinEdge Tprevious f adjoinSeed ∧
                  TashkinovAugmentationSequence rho1 adjoinSeed seed) := by
          rcases hseedBuild with hparallel | hserial
          · exact Or.inl ⟨hparallel.1,
              transportSeedRoute Tprevious hparallel.2⟩
          · rcases hserial with ⟨hkind, f, adjoinSeed, hconnecting,
                hadjoin, hroute⟩
            exact Or.inr ⟨hkind, f, adjoinSeed, hconnecting, hadjoin,
              transportSeedRoute adjoinSeed hroute⟩
        obtain ⟨lower, hround, hlowerMP, htrees, hdata⟩ :=
          CertifiedETTRestriction G k e0 input T generating ett hMP
            jSlot.val hjPositive jSlot.isLt
        let nLower : Fin (lower.rounds + 1) := Fin.last lower.rounds
        have hnMap : Fin.castLE (by omega) nLower = jSlot.castSucc := by
          apply Fin.ext
          simp [nLower, hround]
        have hnTreeMap : Fin.castLE (by omega) nLower.castSucc =
            jSlot.castSucc.castSucc := by
          apply Fin.ext
          simp [nLower, hround]
        have htreeLower : lower.series.data.tree nLower.castSucc =
            Tprevious := by
          rw [htrees nLower.castSucc, hnTreeMap]
        have hcolorLower : lower.series.data.coloring nLower =
            ett.series.data.coloring jSlot.castSucc := by
          rw [(hdata nLower).1, hnMap]
        have hstoredLower : TashkinovStoredColors lower.series.data nLower =
            TashkinovStoredColors ett.series.data jSlot.castSucc := by
          rw [(hdata nLower).2.2.2.2.2.2.2.2.1, hnMap]
        have hkindLower : lower.series.data.kind nLower =
            ett.series.data.kind jSlot.castSucc := by
          rw [(hdata nLower).2.2.2.1, hnMap]
        have hconnectingLower : lower.series.data.connectingEdges nLower =
            ett.series.data.connectingEdges jSlot.castSucc := by
          rw [(hdata nLower).2.2.1, hnMap]
        have hstablePrevious : StableColoring Tprevious
            (TashkinovStoredColors ett.series.data jSlot.castSucc)
            (ett.series.data.coloring jSlot.castSucc) rho1 := by
          constructor
          · intro f hfIncident hfControlled
            obtain ⟨x, hxPrevious, hxf⟩ := hfIncident
            apply hb1Rho.1 f
              ⟨x, segmentVertexBefore hpreviousSeed hpreviousStrict hxPrevious,
                hxf⟩
            obtain ⟨c, hcControlled, hfc⟩ := hfControlled
            refine ⟨c, ?_, hfc⟩
            rcases Finset.mem_union.mp hcControlled with hcMissing | hcStored
            · apply Finset.mem_union_left
              unfold TreeMissingColors at hcMissing
              obtain ⟨z, hzPrevious, hcz⟩ :=
                Finset.mem_biUnion.mp hcMissing
              exact Finset.mem_biUnion.mpr
                ⟨z, segmentVertexBefore hpreviousSeed hpreviousStrict
                  hzPrevious, hcz⟩
            · exact Finset.mem_union_right _ hcStored
          · intro x hxPrevious
            exact hb1Rho.2 x
              (segmentVertexBefore hpreviousSeed hpreviousStrict hxPrevious)
        have hstableLower : StableColoring
            (lower.series.data.tree nLower.castSucc)
            (TashkinovStoredColors lower.series.data nLower)
            (lower.series.data.coloring nLower) rho1 := by
          simpa [htreeLower, hstoredLower, hcolorLower] using hstablePrevious
        have hlowerPack := hlower lower (by omega) (by omega) hlowerMP
        have hmod : ModColoring lower rho1 :=
          hlowerPack.2.2.2.2.2 rho1 hrho1Proper hrho1One hstableLower
        have heligibleLower :
            (lower.series.data.kind nLower =
                some TashkinovExtensionKind.PE ∧
              TashkinovAugmentationSequence rho1
                (lower.series.data.tree nLower.castSucc) seed) ∨
            ((lower.series.data.kind nLower =
                  some TashkinovExtensionKind.SE ∨
                lower.series.data.kind nLower =
                  some TashkinovExtensionKind.RE) ∧
              ∃ (f : E) (adjoinSeed : TreeSequence G e0),
                lower.series.data.connectingEdges nLower = {f} ∧
                  TreeSequenceAdjoinEdge
                    (lower.series.data.tree nLower.castSucc) f adjoinSeed ∧
                  TashkinovAugmentationSequence rho1 adjoinSeed seed) := by
          rcases hseedBuildRho with hparallel | hserial
          · left
            simpa [hkindLower, htreeLower] using hparallel
          · right
            rcases hserial with ⟨hkind, f, adjoinSeed, hconnecting,
                hadjoin, hroute⟩
            refine ⟨?_, f, adjoinSeed, ?_, ?_, hroute⟩
            · simpa [hkindLower] using hkind
            · simpa [hconnectingLower] using hconnecting
            · simpa [htreeLower] using hadjoin
        obtain ⟨TjPrime, corr, hclosure, hcorrMP, hprimeElementary,
            hcaseSplit⟩ :=
          ExtensionBaseClosure lower rho1 seed v supportColors
            (by
              change TreeSequenceInitialSegment
                (lower.series.data.tree nLower.castSucc) seed
              rw [htreeLower]
              exact hpreviousSeed)
            (by
              change (lower.series.data.tree nLower.castSucc).length <
                seed.length
              rw [htreeLower]
              exact hpreviousStrict)
            (by exact heligibleLower) hmod hlowerMP
            (fun Tstar corr hcorrMP => by
              have hcorrRounds : corr.replacementETT.rounds = jSlot.val :=
                corr.rungAgreement.trans hround
              have hpackCorr := hlower corr.replacementETT
                corr.replacementETT.roundsPositive (by omega) hcorrMP
              unfold ColoredVertexSetElementary
              intro x hx y hy hxy
              exact hpackCorr.1 hx hy hxy)
        exact ⟨TjPrime, hclosure, hprimeElementary, hcaseSplit⟩
      · have hjZero : jSlot.val = 0 := by omega
        have hjIndex : jSlot.castSucc = (0 : Fin (ett.rounds + 1)) := by
          apply Fin.ext
          exact hjZero
        cases hcert : ett.series.certified (0 : Fin (ett.rounds + 1)) with
        | initial triple seedLength initialColoring initialStored initialEdges
            initialKind initialVertex initialOutside initialDelta initialGamma
            initialClosure =>
          have htreeOne : ett.series.data.tree 1 =
              ett.series.data.tree jSlot.succ.castSucc := by
            congr 1
            apply Fin.ext
            simp [hjZero]
          have hinitialTj : TreeSequenceInitialSegment
              (ett.series.data.tree 0)
              (ett.series.data.tree jSlot.succ.castSucc) := by
            have h := TashkinovAugmentationSequenceInitialSegment _ _ _
              initialClosure.1
            rw [htreeOne] at h
            exact h
          have hinitialSeed : TreeSequenceInitialSegment
              (ett.series.data.tree 0) seed := by
            apply commonPrefix hinitialTj hseedTj
            rw [seedLength]
            simpa [seed, TreeSequencePrefix] using hterminalPositionPositive
          have hrouteOld : TashkinovAugmentationSequence
              (ett.series.data.coloring jSlot.castSucc)
              (ett.series.data.tree 0) seed := by
            have hrestricted := TashkinovAugmentationSequenceRestrict
              (ett.series.data.coloring 0) (ett.series.data.tree 0) seed
              (ett.series.data.tree jSlot.succ.castSucc)
              (by simpa [htreeOne] using initialClosure.1)
              hinitialSeed hseedTj
            simpa [hjIndex] using hrestricted
          have hrouteRho : TashkinovAugmentationSequence rho1
              (ett.series.data.tree 0) seed :=
            transportSeedRoute (ett.series.data.tree 0) hrouteOld
          obtain ⟨TjPrime, hclosure⟩ := TashkinovClosureExists rho1 seed
          have htripleRho : KTriple G k e0 rho1 :=
            ⟨triple.1, triple.2.1, triple.2.2.1, hrho1Proper, hrho1One⟩
          have hinitialTree : TashkinovTree G e0 rho1
              (ett.series.data.tree 0) := by
            intro a ha
            rw [seedLength] at a
            omega
          have hprimeTree : TashkinovTree G e0 rho1 TjPrime :=
            TashkinovAugmentationSequencePreservesTashkinovTree G e0 rho1
              (ett.series.data.tree 0) TjPrime hinitialTree
              (Relation.ReflTransGen.trans hrouteRho hclosure.1)
          have hprimeElementary : ColoredVertexSetElementary G rho1
              (TreeSequenceVertexSet TjPrime) := by
            unfold ColoredVertexSetElementary
            intro x hx y hy hxy
            exact (TashTree G k e0 rho1 TjPrime htripleRho hprimeTree)
              hx hy hxy
          refine ⟨TjPrime, hclosure, hprimeElementary, ?_⟩
          let awayMissing :=
            ((TreeSequenceVertexSet TjPrime).erase v).biUnion
              fun x => MissingColors G rho1 x
          by_cases hnonempty : (awayMissing ∩ supportColors).Nonempty
          · exact Or.inl hnonempty
          · exact Or.inr (Finset.not_nonempty_iff_eq_empty.mp hnonempty)
    have hseedPrime : TreeSequenceInitialSegment seed TjPrime :=
      TashkinovAugmentationSequenceInitialSegment rho1 seed TjPrime hclosure.1
    have hterminalPrime : v ∈ TreeSequenceVertexSet TjPrime := by
      apply vertexTransfer hseedPrime
      simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ,
        true_and]
      exact ⟨Fin.last seed.length, hseedTerminal⟩
    have hqLast : indices0 (Fin.last p0) = q := by
      obtain ⟨a, ha⟩ := (hclass0 q).1 hqClass
      have haLast : a = Fin.last p0 := by
        by_contra hne
        have halt : a < Fin.last p0 := Fin.lt_last_iff_ne_last.mpr hne
        have hindexLt := hincreasing0 a (Fin.last p0) halt
        rw [ha] at hindexLt
        have hqMax : ∀ r : Fin ett.rounds, r.val ≤ q.val := by
          intro r
          omega
        exact (Nat.not_lt_of_ge (hqMax (indices0 (Fin.last p0)))) hindexLt
      rw [← haLast, ha]
    have hsupport0 : ∀ a : Fin (p0 + 1),
        ett.series.data.chosenVertex (indices0 a).succ = some v := by
      intro a
      have ha := (hclass0 (indices0 a)).2 ⟨a, rfl⟩
      simp only [ExtensionBaseSupportClass, Finset.mem_filter] at ha
      exact ha.2
    have hkind0 : ∀ a : Fin (p0 + 1),
        ett.series.data.kind (indices0 a).succ =
          some TashkinovExtensionKind.PE := by
      intro a
      have ha := (hclass0 (indices0 a)).2 ⟨a, rfl⟩
      have haData := ha
      simp only [ExtensionBaseSupportClass, Finset.mem_filter] at haData
      have hactive := haData.1
      simp only [ExtensionBaseActiveIndices, Finset.mem_filter,
        Finset.mem_univ, true_and] at hactive
      exact hactive.2.1
    have hstored0 : ∀ a : Fin (p0 + 1),
        ett.series.data.stored (indices0 a).succ =
          {gamma0 a, delta0 a} := by
      intro a
      exact hPEStored (indices0 a) (gamma0 a) (delta0 a) (hkind0 a)
        (hgamma0 a) (hdelta0 a)
    have hterminalIntersection : MissingColors G rho1 v ∩ supportColors =
        {delta0 (Fin.last p0)} := by
      dsimp [supportColors]
      rw [hb2Missing.2]
      exact hmissing0.1
    have hfirstGammaMissing : gamma0 0 ∈ MissingColors G
        (ett.series.data.coloring jSlot.castSucc) v := by
      rw [hmissing0.2]
      simp
    have hdeltaAvoidsTj : ∀ a : Fin (p0 + 1),
        delta0 a ∉ TreeMissingColors
          (ett.series.data.coloring jSlot.castSucc)
          (ett.series.data.tree jSlot.succ.castSucc) := by
      intro a
      have haClass := (hclass0 (indices0 a)).2 ⟨a, rfl⟩
      have haData := haClass
      simp only [ExtensionBaseSupportClass, Finset.mem_filter] at haData
      exact hdeltaExclusion.2 (indices0 a) v hvFinal (delta0 a)
        haData.1 (hsupport0 a) (hdelta0 a)
    have hTjElementary : ColoredVertexSetElementary G
        (ett.series.data.coloring jSlot.castSucc)
        (TreeSequenceVertexSet
          (ett.series.data.tree jSlot.succ.castSucc)) := by
      by_cases hjPositive : 0 < jSlot.val
      · obtain ⟨lower, hround, hlowerMP, htrees, hdata⟩ :=
          CertifiedETTRestriction G k e0 input T generating ett hMP
            jSlot.val hjPositive jSlot.isLt
        exact (hlower lower (by omega) (by omega) hlowerMP).1
      · have hjZero : jSlot.val = 0 := by omega
        have hbase : ColoredVertexSetElementary G
            (ett.series.data.coloring 0)
            (TreeSequenceVertexSet
              (ett.series.data.tree ⟨1, by omega⟩)) := by
          unfold ColoredVertexSetElementary
          intro x hx y hy hxy
          exact (TechnicalTheoremBase G k ett.rounds e0 input
            ett.series).1 hx hy hxy
        have hcolor : jSlot.castSucc = (0 : Fin (ett.rounds + 1)) := by
          apply Fin.ext
          exact hjZero
        have htree : jSlot.succ.castSucc =
            (⟨1, by omega⟩ : Fin (ett.rounds + 2)) := by
          apply Fin.ext
          simp [hjZero]
        simpa [hcolor, htree] using hbase
    have hTjFinal : TreeSequenceInitialSegment
        (ett.series.data.tree jSlot.succ.castSucc) T :=
      segmentTrans hTjQ hqFinal
    have hbeforeTjFinal : TreeVerticesBefore
          (ett.series.data.tree jSlot.succ.castSucc) v hterminalJ ⊆
        TreeVerticesBefore T v hvFinal := by
      intro x hx
      unfold TreeVerticesBefore at hx ⊢
      simp only [Finset.mem_filter] at hx ⊢
      refine ⟨vertexTransfer hTjFinal hx.1, ?_⟩
      rcases hx.2 with ⟨ix, iv, hix, hiv, hlt⟩
      refine ⟨Fin.castLE (Nat.succ_le_succ hTjFinal.1) ix,
        Fin.castLE (Nat.succ_le_succ hTjFinal.1) iv,
        (hTjFinal.2.1 ix).trans hix,
        (hTjFinal.2.1 iv).trans hiv, ?_⟩
      simpa using hlt
    have hb1Tj : StableColoringBeforeVertex
        (ett.series.data.tree jSlot.succ.castSucc) v hterminalJ
        (TashkinovStoredColors ett.series.data jSlot.castSucc)
        (ett.series.data.coloring jSlot.castSucc) rho1 := by
      constructor
      · intro f hfIncident hfControlled
        obtain ⟨x, hxBefore, hxf⟩ := hfIncident
        apply hb1Rho.1 f ⟨x, hbeforeTjFinal hxBefore, hxf⟩
        obtain ⟨c, hcControlled, hfc⟩ := hfControlled
        refine ⟨c, ?_, hfc⟩
        rcases Finset.mem_union.mp hcControlled with hcMissing | hcStored
        · apply Finset.mem_union_left
          obtain ⟨z, hzBefore, hcz⟩ := Finset.mem_biUnion.mp hcMissing
          exact Finset.mem_biUnion.mpr
            ⟨z, hbeforeTjFinal hzBefore, hcz⟩
        · exact Finset.mem_union_right _ hcStored
      · intro x hxBefore
        exact hb1Rho.2 x (hbeforeTjFinal hxBefore)
    have hcaseOnePrepared :
        (((TreeSequenceVertexSet TjPrime).erase v).biUnion
            (fun x => MissingColors G rho1 x) ∩ supportColors).Nonempty →
          ∃ (u : V) (huPrime : u ∈ TreeSequenceVertexSet TjPrime)
            (b : Fin (p0 + 1))
            (traceB : ExtensionBaseAlgorithmBTrace ett v rho1 u
              p0 indices0 b),
            u ∉ TreeSequenceVertexSet
                (ett.series.data.tree jSlot.succ.castSucc) ∧
              ExtensionBaseAlgorithmBInvariant ett v jSlot rho1 u
                p0 indices0 b traceB ∧
              (let rho2 := traceB.coloring (Fin.last traceB.steps)
               StableColoringBeforeVertex
                    (ett.series.data.tree jSlot.succ.castSucc) v hterminalJ
                    (TashkinovStoredColors ett.series.data jSlot.castSucc)
                    (ett.series.data.coloring jSlot.castSucc) rho2 ∧
                 ((∀ x : V,
                    x ∈ TreeSequenceVertexSet
                          (ett.series.data.tree jSlot.succ.castSucc) ∪
                        TreeVerticesBefore TjPrime u huPrime →
                    MissingColors G rho2 x = MissingColors G rho1 x) ∧
                  ∀ f : E,
                    ((∃ a : Fin (ett.series.data.tree
                          jSlot.succ.castSucc).length,
                        (ett.series.data.tree
                          jSlot.succ.castSucc).edge a = f) ∨
                      ∃ (a : Fin TjPrime.length)
                        (z : Fin (TjPrime.length + 1)),
                        TjPrime.vertex z = u ∧ a.val < z.val ∧
                          TjPrime.edge a = f) →
                    rho2 f = rho1 f) ∧
                 gamma0 0 ∈ MissingColors G rho2 u) := by
      intro hcaseOne
      obtain ⟨u, huPrime, b, huNe, hselected, hminimal, hfirstChoice,
          huOutside, hprefixData⟩ :=
        ExtensionBaseCaseOneSelection ett v hvFinal jSlot q hjle hqTerminal
          hjSlot rho1 seed TjPrime terminalPosition hterminalAt
          hterminalPositionPositive rfl hclosure hterminalPrime p0 indices0
          gamma0 delta0 hincreasing0 hclass0 hqLast hgamma0 hdelta0 hstored0
          hchain0 hinjective0 (by simpa [supportColors] using hcaseOne)
          hprimeElementary (by simpa [supportColors] using hterminalIntersection)
          hTjElementary hb2Missing.1 hfirstGammaMissing hdeltaAvoidsTj
      dsimp only at hprefixData
      have hinitialB : ∀ a : Fin (p0 + 1), a.val < b.val →
          ETTStrongInterchangeable ett (indices0 a) v rho1
            (gamma0 a) (delta0 a) := by
        intro a hab
        apply hb4Interchange (indices0 a) (gamma0 a) (delta0 a)
        · exact (hclass0 (indices0 a)).2 ⟨a, rfl⟩
        · intro heq
          have haLast : a.val < (Fin.last p0).val :=
            lt_of_lt_of_le hab (Fin.le_last b)
          have hindexLt := hincreasing0 a (Fin.last p0) haLast
          rw [hqLast, heq] at hindexLt
          exact (Nat.lt_irrefl _ hindexLt)
        · exact hsupport0 a
        · exact hgamma0 a
        · exact hdelta0 a
      have hTjInitialB : ∀ a : Fin (p0 + 1), a.val < b.val →
          TreeSequenceInitialSegment
            (ett.series.data.tree jSlot.succ.castSucc)
            (ett.series.data.tree (indices0 a).succ.castSucc) := by
        intro a hab
        have haClass := (hclass0 (indices0 a)).2 ⟨a, rfl⟩
        have haData := haClass
        simp only [ExtensionBaseSupportClass, Finset.mem_filter] at haData
        have haActive := haData.1
        have haActiveData := haActive
        simp only [ExtensionBaseActiveIndices, Finset.mem_filter,
          Finset.mem_univ, true_and] at haActiveData
        have hjIndexLe : jSlot.val + 1 ≤ (indices0 a).val + 1 := by
          rw [hjSlot]
          exact haActiveData.1
        have hseg := stageToStage (jSlot.val + 1)
          ((indices0 a).val + 1) (by omega) hjIndexLe (by omega)
        convert hseg using 1 <;> congr 1 <;> apply Fin.ext <;> rfl
      obtain ⟨traceB, hinvariantB⟩ :=
        ExtensionBaseAlgorithmB ett v jSlot rho1 u p0 indices0 gamma0 delta0
          b hrho1Proper hrho1One hincreasing0 hsupport0 hkind0 hgamma0
          hdelta0 hchain0 hinjective0 hselected hminimal hinitialB
          hTjInitialB hprefixData.2.2 hstored0
      have hprefixSubset :
          (ExtensionBaseCaseOneIndices ett p0 indices0 b).biUnion
              (fun t => ett.series.data.stored t.succ) ⊆
            supportColors := by
        intro c hc
        obtain ⟨t, ht, hct⟩ := Finset.mem_biUnion.mp hc
        unfold ExtensionBaseCaseOneIndices at ht
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp ht
        exact Finset.mem_biUnion.mpr ⟨a, Finset.mem_univ _, hct⟩
      have hprefixAvoids :
          (TreeVerticesBefore TjPrime u huPrime).biUnion
                (fun x => MissingColors G rho1 x) ∩
              ((ExtensionBaseCaseOneIndices ett p0 indices0 b).biUnion
                fun t => ett.series.data.stored t.succ) = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro c hc
        obtain ⟨hcBefore, hcPrefix⟩ := Finset.mem_inter.mp hc
        have hcSupport := hprefixSubset hcPrefix
        have hcNe : c ≠ delta0 (Fin.last p0) := by
          intro hEq
          apply hprefixData.2.1
          rw [← hEq]
          exact hcPrefix
        have hcDifference : c ∈ supportColors \ {delta0 (Fin.last p0)} :=
          Finset.mem_sdiff.mpr ⟨hcSupport, by simpa using hcNe⟩
        have hcEmpty : c ∈ (∅ : Finset (Fin k)) := by
          rw [← hprefixData.1]
          exact Finset.mem_inter.mpr ⟨hcBefore, hcDifference⟩
        simpa using hcEmpty
      have hclaim44 := ExtensionBaseClaim44 ett v hvFinal jSlot hjSlot rho1
        (TashkinovStoredColors ett.series.data jSlot.castSucc) u TjPrime seed
        terminalPosition hterminalAt hterminalPositionPositive rfl huPrime p0
        indices0 gamma0 delta0 b hincreasing0 hclass0 traceB hinvariantB
        hb1Tj huOutside hclosure hprefixAvoids hselected hminimal hgamma0
        hdelta0 hchain0 hinjective0 hstored0
      dsimp only at hclaim44
      exact ⟨u, huPrime, b, traceB, huOutside, hinvariantB, hclaim44⟩
    rcases hcaseSplit with hcaseOne | hcaseTwo
    · obtain ⟨u, huPrime, b, traceB, huOutside, hinvariantB,
          hclaim44⟩ := hcaseOnePrepared hcaseOne
      let rho2 : PartialEdgeColoring E k :=
        traceB.coloring (Fin.last traceB.steps)
      dsimp only at hclaim44
      obtain ⟨c1, c2, c3⟩ := hclaim44
      have hrho2Proper : IsProperEdgeColoring G rho2 := by
        simpa [rho2] using (hinvariantB.1 (Fin.last traceB.steps)).1
      have hrho2One : IsOneEdgeUncolored rho2 e0 := by
        simpa [rho2] using (hinvariantB.1 (Fin.last traceB.steps)).2
      obtain ⟨uPosition, -, huPosition⟩ := Finset.mem_image.mp huPrime
      have huNotSeed : u ∉ TreeSequenceVertexSet seed := by
        intro huSeed
        exact huOutside (vertexTransfer hseedTj huSeed)
      have hseedBeforeU : seed.length < uPosition.val := by
        by_contra hnot
        have huBound : uPosition.val ≤ seed.length := Nat.le_of_not_gt hnot
        let i : Fin (seed.length + 1) := ⟨uPosition.val, by omega⟩
        have hcast : Fin.castLE (Nat.succ_le_succ hseedPrime.1) i =
            uPosition := by
          apply Fin.ext
          rfl
        apply huNotSeed
        simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ,
          true_and]
        refine ⟨i, ?_⟩
        exact (hseedPrime.2.1 i).symm.trans (hcast ▸ huPosition)
      have huPositionPositive : 1 ≤ uPosition.val := by
        exact seed.positive.trans (Nat.le_of_lt hseedBeforeU)
      have huPositionBound : uPosition.val ≤ TjPrime.length :=
        Nat.lt_succ_iff.mp uPosition.isLt
      let U : TreeSequence G e0 :=
        TreeSequencePrefix TjPrime uPosition.val huPositionPositive
          huPositionBound
      have hUPrime : TreeSequenceInitialSegment U TjPrime := by
        refine ⟨huPositionBound, ?_, ?_⟩
        · intro i
          simp [U, TreeSequencePrefix]
        · intro i
          simp [U, TreeSequencePrefix]
      have hseedU : TreeSequenceInitialSegment seed U := by
        apply commonPrefix hseedPrime hUPrime
        exact Nat.le_of_lt hseedBeforeU
      have hrouteRhoOneU : TashkinovAugmentationSequence rho1 seed U :=
        TashkinovAugmentationSequenceRestrict rho1 seed U TjPrime
          hclosure.1 hseedU hUPrime
      have hprimeVertexBefore (i : Fin (TjPrime.length + 1))
          (hi : i.val < uPosition.val) :
          TjPrime.vertex i ∈ TreeVerticesBefore TjPrime u huPrime := by
        unfold TreeVerticesBefore
        apply Finset.mem_filter.mpr
        constructor
        · simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ,
            true_and]
          exact ⟨i, rfl⟩
        · exact ⟨i, uPosition, rfl, huPosition, hi⟩
      have hUsegmentVertexBefore {A : TreeSequence G e0}
          (hAU : TreeSequenceInitialSegment A U)
          (hAlen : A.length < U.length) {x : V}
          (hxA : x ∈ TreeSequenceVertexSet A) :
          x ∈ TreeVerticesBefore TjPrime u huPrime := by
        obtain ⟨hAULen, hAUVertices, -⟩ := hAU
        simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ,
          true_and] at hxA
        obtain ⟨i, rfl⟩ := hxA
        let iU : Fin (U.length + 1) :=
          Fin.castLE (Nat.succ_le_succ hAULen) i
        let iPrime : Fin (TjPrime.length + 1) :=
          Fin.castLE (Nat.succ_le_succ hUPrime.1) iU
        have hiPrime : iPrime.val < uPosition.val := by
          change i.val < uPosition.val
          have hUlen : U.length = uPosition.val := by
            simp [U, TreeSequencePrefix]
          omega
        rw [← hAUVertices i, ← hUPrime.2.1 iU]
        exact hprimeVertexBefore iPrime hiPrime
      have transportUStep {A B : TreeSequence G e0}
          (hstep : TashkinovAugmentation rho1 A B)
          (hBU : TreeSequenceInitialSegment B U) :
          TashkinovAugmentation rho2 A B := by
        rcases hstep with ⟨hlen, hAB, c, hcolor, hcMissing⟩
        have hAU : TreeSequenceInitialSegment A U := segmentTrans hAB hBU
        have hAlen : A.length < U.length :=
          lt_of_lt_of_le (by omega) hBU.1
        have hcMissingRho : c ∈ TreeMissingColors rho2 A := by
          unfold TreeMissingColors at hcMissing ⊢
          obtain ⟨x, hxA, hcx⟩ := Finset.mem_biUnion.mp hcMissing
          refine Finset.mem_biUnion.mpr ⟨x, hxA, ?_⟩
          rw [c2.1 x (Finset.mem_union_right _
            (hUsegmentVertexBefore hAU hAlen hxA))]
          exact hcx
        let added : Fin B.length := Fin.cast hlen.symm (Fin.last A.length)
        let addedU : Fin U.length := Fin.castLE hBU.1 added
        let addedPrime : Fin TjPrime.length := Fin.castLE hUPrime.1 addedU
        have haddedPosition : addedPrime.val < uPosition.val := by
          change A.length < uPosition.val
          have hUlen : U.length = uPosition.val := by
            simp [U, TreeSequencePrefix]
          omega
        have haddedIdentity : TjPrime.edge addedPrime = B.edge added :=
          (hUPrime.2.2 addedU).trans (hBU.2.2 added)
        have haddedFixed : rho2 (B.edge added) = rho1 (B.edge added) := by
          apply c2.2 (B.edge added)
          exact Or.inr ⟨addedPrime, uPosition, huPosition,
            haddedPosition, haddedIdentity⟩
        refine ⟨hlen, hAB, c, ?_, hcMissingRho⟩
        change rho2 (B.edge added) = some c
        exact haddedFixed.trans hcolor
      have transportURoute (S : TreeSequence G e0)
          (hroute : TashkinovAugmentationSequence rho1 S U) :
          TashkinovAugmentationSequence rho2 S U := by
        unfold TashkinovAugmentationSequence at hroute ⊢
        induction hroute using Relation.ReflTransGen.head_induction_on with
        | refl => exact Relation.ReflTransGen.refl
        | @head A B hAB hBU ih =>
            have hBsegment : TreeSequenceInitialSegment B U :=
              TashkinovAugmentationSequenceInitialSegment rho1 B U hBU
            exact Relation.ReflTransGen.head
              (transportUStep hAB hBsegment) ih
      have hrouteRhoTwoU : TashkinovAugmentationSequence rho2 seed U :=
        transportURoute seed hrouteRhoOneU
      have hterminalMissingEq : MissingColors G rho2 v =
          MissingColors G rho1 v := by
        exact c2.1 v (Finset.mem_union_left _ hterminalJ)
      have hterminalInclusion : MissingColors G
            (ett.series.data.coloring jSlot.castSucc) v ⊆
          MissingColors G rho2 v ∪ MissingColors G rho2 u := by
        intro c hc
        rw [hmissing0.2] at hc
        rcases Finset.mem_union.mp hc with hcSigma | hcGamma
        · apply Finset.mem_union_left
          rw [hterminalMissingEq, hb2Missing.2]
          exact (Finset.mem_sdiff.mp hcSigma).1
        · apply Finset.mem_union_right
          have hcgamma : c = gamma0 0 := Finset.mem_singleton.mp hcGamma
          simpa [hcgamma] using c3
      let Tprevious : TreeSequence G e0 :=
        ett.series.data.tree jSlot.castSucc.castSucc
      have hvNotPrevious (hjPositive : 0 < jSlot.val) :
          v ∉ TreeSequenceVertexSet Tprevious := by
        intro hvPrevious
        let candidates : Finset (Fin (ett.rounds + 1)) :=
          Finset.univ.filter fun i =>
            v ∈ TreeSequenceVertexSet (ExtendedTashkinovLadderStage ett i)
        have hlast : Fin.last ett.rounds ∈ candidates := by
          simp only [candidates, Finset.mem_filter, Finset.mem_univ, true_and]
          rw [show ExtendedTashkinovLadderStage ett
              (Fin.last ett.rounds) = T by
            unfold ExtendedTashkinovLadderStage
            exact Fin.lastCases_last]
          exact hvFinal
        have hfirst := hjSlot
        unfold ETTFirstAppearanceIndex at hfirst
        dsimp at hfirst
        have hminimumValue :
            (candidates.min' ⟨Fin.last ett.rounds, hlast⟩).val =
              jSlot.val := by
          change jSlot.val + 1 =
            (candidates.min' ⟨Fin.last ett.rounds, hlast⟩).val + 1 at hfirst
          omega
        let previousSlot : Fin ett.rounds :=
          ⟨jSlot.val - 1, by omega⟩
        have hpreviousIndex : previousSlot.succ = jSlot.castSucc := by
          apply Fin.ext
          simp [previousSlot]
          omega
        have hpreviousMember : previousSlot.castSucc ∈ candidates := by
          simp only [candidates, Finset.mem_filter, Finset.mem_univ, true_and]
          rw [show ExtendedTashkinovLadderStage ett previousSlot.castSucc =
              Tprevious by
            unfold ExtendedTashkinovLadderStage
            rw [Fin.lastCases_castSucc, hpreviousIndex]]
          exact hvPrevious
        have hminimum := Finset.min'_le candidates previousSlot.castSucc
          hpreviousMember
        have hminimumVal := Fin.le_iff_val_le_val.mp hminimum
        rw [hminimumValue] at hminimumVal
        dsimp [previousSlot] at hminimumVal
        omega
      have hpreviousTj (hjPositive : 0 < jSlot.val) :
          TreeSequenceInitialSegment Tprevious
            (ett.series.data.tree jSlot.succ.castSucc) := by
        have hstep := stepSegment jSlot.castSucc (by simpa using hjPositive)
        rw [hjTreeIndex] at hstep
        exact hstep
      have hpreviousStrict (hjPositive : 0 < jSlot.val) :
          Tprevious.length < seed.length := by
        by_contra hnot
        have hpositionLe : terminalPosition.val ≤ Tprevious.length := by
          simpa [seed, TreeSequencePrefix] using Nat.le_of_not_gt hnot
        let previousPosition : Fin (Tprevious.length + 1) :=
          ⟨terminalPosition.val, by omega⟩
        have hcast : Fin.castLE
            (Nat.succ_le_succ (hpreviousTj hjPositive).1)
            previousPosition = terminalPosition := by
          apply Fin.ext
          rfl
        apply hvNotPrevious hjPositive
        simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ,
          true_and]
        refine ⟨previousPosition, ?_⟩
        have hvertex := (hpreviousTj hjPositive).2.1 previousPosition
        rw [hcast] at hvertex
        exact hvertex.symm.trans hterminalAt
      have hpreviousSeed (hjPositive : 0 < jSlot.val) :
          TreeSequenceInitialSegment Tprevious seed :=
        commonPrefix (hpreviousTj hjPositive) hseedTj
          (Nat.le_of_lt (hpreviousStrict hjPositive))
      have hroutePhiTj : TashkinovAugmentationSequence
          (ett.series.data.coloring jSlot.castSucc) seed
          (ett.series.data.tree jSlot.succ.castSucc) := by as_aux_lemma =>
        generalize htarget : jSlot.castSucc = target
        cases ett.series.certified target with
        | initial triple seedLength initialColoring initialStored initialEdges
            initialKind initialVertex initialOutside initialDelta initialGamma
            initialClosure =>
          have htargetZero : jSlot.val = 0 := by
            have := congrArg Fin.val htarget
            simpa using this
          have htreeOne : ett.series.data.tree 1 =
              ett.series.data.tree jSlot.succ.castSucc := by
            congr 1
            apply Fin.ext
            simp [htargetZero]
          have hinitialTj : TreeSequenceInitialSegment
              (ett.series.data.tree 0)
              (ett.series.data.tree jSlot.succ.castSucc) := by
            have h := TashkinovAugmentationSequenceInitialSegment _ _ _
              initialClosure.1
            rw [htreeOne] at h
            exact h
          have hbaseSeed : TreeSequenceInitialSegment
              (ett.series.data.tree 0) seed := by
            apply commonPrefix hinitialTj hseedTj
            rw [seedLength]
            exact seed.positive
          have hrouteOld : TashkinovAugmentationSequence
              (ett.series.data.coloring 0) (ett.series.data.tree 0)
              (ett.series.data.tree jSlot.succ.castSucc) := by
            rw [← htreeOne]
            exact initialClosure.1
          have hroute := TashkinovAugmentationSequenceSuffix
            (ett.series.data.coloring 0) (ett.series.data.tree 0) seed
            (ett.series.data.tree jSlot.succ.castSucc) hrouteOld hbaseSeed
            hseedTj
          simpa [htargetZero] using hroute
        | SE i previousProper previousOneUncolored previousClosed
            previousNotStronglyClosed noRevisiting choice seriesAlternative
            currentColoring currentStored currentEdges currentKind currentVertex
            currentOutside currentDelta currentGamma adjoined adjoinedExactly
            closedExtension orderedExtension strictExtension =>
          have hi : i.succ = jSlot.castSucc := htarget.symm
          have hjPositive : 0 < jSlot.val := by
            have := congrArg Fin.val hi
            simp at this
            omega
          have hroute : TashkinovAugmentationSequence
              (ett.series.data.coloring jSlot.castSucc) adjoined
              (ett.series.data.tree jSlot.succ.castSucc) := by
            have h := closedExtension.1
            rw [hi, hjTreeIndex] at h
            exact h
          have hadjoinedTj : TreeSequenceInitialSegment adjoined
              (ett.series.data.tree jSlot.succ.castSucc) :=
            TashkinovAugmentationSequenceInitialSegment _ _ _ hroute
          have hadjoinedLength : adjoined.length ≤ seed.length := by
            rcases adjoinedExactly with ⟨hlen, -, -⟩
            have hiCast : i.succ.castSucc = jSlot.castSucc.castSucc := by
              apply Fin.ext
              simpa using congrArg Fin.val hi
            have hprev : ett.series.data.tree i.succ.castSucc =
                Tprevious := by rw [hiCast]
            rw [hprev] at hlen
            rw [hlen]
            exact Nat.succ_le_of_lt (hpreviousStrict hjPositive)
          have hadjoinedSeed : TreeSequenceInitialSegment adjoined seed :=
            commonPrefix hadjoinedTj hseedTj hadjoinedLength
          simpa [hi] using
            (TashkinovAugmentationSequenceSuffix
              (ett.series.data.coloring jSlot.castSucc) adjoined seed _ hroute
                hadjoinedSeed hseedTj)
        | PE i previousProper previousOneUncolored previousClosed
            previousNotStronglyClosed noRevisiting choice seriesAlternativeFails
            chosenGamma gammaRule secondStable secondStableProper
            secondStableOneUncolored secondStableRelation exitWitness
            currentColoring currentProper currentOneUncolored currentStored
            currentEdges currentKind currentVertex currentOutside currentDelta
            currentGamma closedExtension orderedExtension strictExtension =>
          have hi : i.succ = jSlot.castSucc := htarget.symm
          have hjPositive : 0 < jSlot.val := by
            have := congrArg Fin.val hi
            simp at this
            omega
          have hroute : TashkinovAugmentationSequence
              (ett.series.data.coloring jSlot.castSucc) Tprevious
              (ett.series.data.tree jSlot.succ.castSucc) := by
            have h := closedExtension.1
            rw [hi, hjTreeIndex] at h
            simpa [Tprevious, hi] using h
          simpa [hi] using
            (TashkinovAugmentationSequenceSuffix
              (ett.series.data.coloring jSlot.castSucc) Tprevious seed _ hroute
                (hpreviousSeed hjPositive) hseedTj)
        | RE i previousProper previousOneUncolored previousClosed
            previousNotStronglyClosed available currentColoring currentStored
            currentEdges currentKind currentVertex currentOutside currentDelta
            currentGamma adjoined adjoinedExactly closedExtension orderedExtension
            strictExtension =>
          have hi : i.succ = jSlot.castSucc := htarget.symm
          have hjPositive : 0 < jSlot.val := by
            have := congrArg Fin.val hi
            simp at this
            omega
          have hroute : TashkinovAugmentationSequence
              (ett.series.data.coloring jSlot.castSucc) adjoined
              (ett.series.data.tree jSlot.succ.castSucc) := by
            have h := closedExtension.1
            rw [hi, hjTreeIndex] at h
            exact h
          have hadjoinedTj : TreeSequenceInitialSegment adjoined
              (ett.series.data.tree jSlot.succ.castSucc) :=
            TashkinovAugmentationSequenceInitialSegment _ _ _ hroute
          have hadjoinedLength : adjoined.length ≤ seed.length := by
            rcases adjoinedExactly with ⟨hlen, -, -⟩
            have hiCast : i.succ.castSucc = jSlot.castSucc.castSucc := by
              apply Fin.ext
              simpa using congrArg Fin.val hi
            have hprev : ett.series.data.tree i.succ.castSucc =
                Tprevious := by rw [hiCast]
            rw [hprev] at hlen
            rw [hlen]
            exact Nat.succ_le_of_lt (hpreviousStrict hjPositive)
          have hadjoinedSeed : TreeSequenceInitialSegment adjoined seed :=
            commonPrefix hadjoinedTj hseedTj hadjoinedLength
          simpa [hi] using
            (TashkinovAugmentationSequenceSuffix
              (ett.series.data.coloring jSlot.castSucc) adjoined seed _ hroute
                hadjoinedSeed hseedTj)
      let Tj0 : TreeSequence G e0 :=
        ett.series.data.tree jSlot.succ.castSucc
      have hroutePhiTj0 : TashkinovAugmentationSequence
          (ett.series.data.coloring jSlot.castSucc) seed Tj0 := by
        simpa [Tj0] using hroutePhiTj
      have hseedTj0 : TreeSequenceInitialSegment seed Tj0 := by
        simpa [Tj0] using hseedTj
      obtain ⟨M, ⟨hunion⟩⟩ := OrderedTreeUnionExists U Tj0
      have huU : u ∈ TreeSequenceVertexSet U := by
        simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ,
          true_and]
        refine ⟨Fin.last U.length, ?_⟩
        change TjPrime.vertex (Fin.castLE (Nat.succ_le_succ huPositionBound)
          (Fin.last uPosition.val)) = u
        have hindex : Fin.castLE (Nat.succ_le_succ huPositionBound)
            (Fin.last uPosition.val) = uPosition := by
          apply Fin.ext
          rfl
        rw [hindex]
        exact huPosition
      have hrouteUM : TashkinovAugmentationSequence rho2 U M := by
        as_aux_lemma =>
        have hleftSegment := hunion.leftSegment
        have hnewEntryFromRight := hunion.newEntryFromRight
        have heveryNewRightEntry := hunion.everyNewRightEntry
        have hrightOrder := hunion.rightOrder
        have prefixSegment (A : TreeSequence G e0) (r : Nat)
            (hr : 1 ≤ r) (hrA : r ≤ A.length) :
            TreeSequenceInitialSegment
              (TreeSequencePrefix A r hr hrA) A := by
          refine ⟨hrA, ?_, ?_⟩
          · intro i
            simp [TreeSequencePrefix]
          · intro i
            simp [TreeSequencePrefix]
        have prefixPrefix (A : TreeSequence G e0) (r : Nat)
            (hr : 1 ≤ r) (hrA : r + 1 ≤ A.length) :
            TreeSequenceInitialSegment
              (TreeSequencePrefix A r hr
                (Nat.le_trans (Nat.le_succ r) hrA))
              (TreeSequencePrefix A (r + 1) (by omega) hrA) := by
          refine ⟨Nat.le_succ r, ?_, ?_⟩
          · intro i
            change A.vertex _ = A.vertex _
            congr 1
          · intro i
            change A.edge _ = A.edge _
            congr 1
        have prefixSelf (A : TreeSequence G e0) :
            TreeSequencePrefix A A.length A.positive le_rfl = A := by
          cases A with
          | mk len pos vertex edge vinj einj first attach =>
            rw [TreeSequence.mk.injEq]
            refine ⟨rfl, ?_, ?_⟩
            · apply heq_of_eq
              funext i
              rfl
            · apply heq_of_eq
              funext i
              rfl
        have equalPrefixes {A B D : TreeSequence G e0}
            (hAD : TreeSequenceInitialSegment A D)
            (hBD : TreeSequenceInitialSegment B D)
            (hlen : A.length = B.length) : A = B := by
          rcases hAD with ⟨hlenAD, hvertexAD, hedgeAD⟩
          rcases hBD with ⟨hlenBD, hvertexBD, hedgeBD⟩
          cases A with
          | mk alen apos avertex aedge avinj aeinf afirst aattach =>
            cases B with
            | mk blen bpos bvertex bedge bvinj beinj bfirst battach =>
              simp only at hlen
              subst blen
              rw [TreeSequence.mk.injEq]
              refine ⟨rfl, ?_, ?_⟩
              · apply heq_of_eq
                funext i
                calc
                  avertex i = D.vertex
                      (Fin.castLE (Nat.succ_le_succ hlenAD) i) :=
                    (hvertexAD i).symm
                  _ = D.vertex
                      (Fin.castLE (Nat.succ_le_succ hlenBD) i) := by
                    congr 1
                  _ = bvertex i := hvertexBD i
              · apply heq_of_eq
                funext i
                calc
                  aedge i = D.edge (Fin.castLE hlenAD i) :=
                    (hedgeAD i).symm
                  _ = D.edge (Fin.castLE hlenBD i) := by congr 1
                  _ = bedge i := hedgeBD i
        have prefixAtLeft :
            TreeSequencePrefix M U.length U.positive hleftSegment.1 = U := by
          apply equalPrefixes
            (prefixSegment M U.length U.positive hleftSegment.1)
            hleftSegment
          rfl
        have hseedTjSegment : TreeSequenceInitialSegment seed Tj0 :=
          TashkinovAugmentationSequenceInitialSegment _ _ _ hroutePhiTj0
        have firstStep {A B : TreeSequence G e0}
            (hAB : TashkinovAugmentationSequence
              (ett.series.data.coloring jSlot.castSucc) A B)
            (hlt : A.length < B.length) :
            ∃ C, TashkinovAugmentation
                (ett.series.data.coloring jSlot.castSucc) A C ∧
              TashkinovAugmentationSequence
                (ett.series.data.coloring jSlot.castSucc) C B := by
          unfold TashkinovAugmentationSequence at hAB ⊢
          induction hAB using Relation.ReflTransGen.head_induction_on with
          | refl => omega
          | @head A C hAC hCB ih => exact ⟨C, hAC, hCB⟩
        have replay : ∀ n (hnU : U.length ≤ n) (hnM : n ≤ M.length),
            TashkinovAugmentationSequence rho2 U
              (TreeSequencePrefix M n
                (Nat.le_trans U.positive hnU) hnM) := by
          intro n hnU hnM
          induction n, hnU using Nat.le_induction with
          | base =>
              simpa [prefixAtLeft] using
                (show TashkinovAugmentationSequence rho2 U U from
                  Relation.ReflTransGen.refl)
          | @succ n hnU ih =>
              by_cases hnEq : n = M.length
              · omega
              have hnSuccM : n + 1 ≤ M.length := by omega
              have hnM' : n ≤ M.length :=
                Nat.le_trans (Nat.le_succ n) hnSuccM
              have ih' := ih hnM'
              let X := TreeSequencePrefix M n
                (Nat.le_trans U.positive hnU) hnM'
              let Y := TreeSequencePrefix M (n + 1)
                (Nat.le_trans U.positive
                  (Nat.le_trans hnU (Nat.le_succ n))) hnSuccM
              let mIndex : Fin M.length := ⟨n, by omega⟩
              obtain ⟨i, hedgeMTj, hvertexMTj⟩ :=
                hnewEntryFromRight mIndex hnU
              have hrightOutside :
                  Tj0.vertex i.succ ∉ TreeSequenceVertexSet U := by
                intro hmem
                simp only [TreeSequenceVertexSet, Finset.mem_image,
                  Finset.mem_univ, true_and] at hmem
                obtain ⟨a, ha⟩ := hmem
                have hmvertex : M.vertex
                      (Fin.castLE (Nat.succ_le_succ hleftSegment.1) a) =
                    U.vertex a := hleftSegment.2.1 a
                have heq : M.vertex mIndex.succ =
                    M.vertex
                      (Fin.castLE (Nat.succ_le_succ hleftSegment.1) a) :=
                  hvertexMTj.trans (ha.symm.trans hmvertex.symm)
                have hindex := congrArg Fin.val (M.vertex_injective heq)
                simp [mIndex] at hindex
                omega
              have hiSeed : seed.length ≤ i.val := by
                by_contra hnot
                have hi : i.val < seed.length := Nat.lt_of_not_ge hnot
                let a : Fin (seed.length + 1) := ⟨i.val + 1, by omega⟩
                have hTjSeedA : Tj0.vertex
                      (Fin.castLE (Nat.succ_le_succ hseedTjSegment.1) a) =
                    seed.vertex a := hseedTjSegment.2.1 a
                apply hrightOutside
                simp only [TreeSequenceVertexSet, Finset.mem_image,
                  Finset.mem_univ, true_and]
                refine ⟨Fin.castLE (Nat.succ_le_succ hseedU.1) a, ?_⟩
                have hia : Fin.castLE
                      (Nat.succ_le_succ hseedTjSegment.1) a = i.succ := by
                  apply Fin.ext
                  simp [a]
                rw [hia] at hTjSeedA
                exact (hseedU.2.1 a).trans hTjSeedA.symm
              have hiTj : i.val < Tj0.length := i.isLt
              let RX := TreeSequencePrefix Tj0 i.val
                (Nat.le_trans seed.positive hiSeed) (Nat.le_of_lt hiTj)
              have hseedRX : TreeSequenceInitialSegment seed RX := by
                refine ⟨hiSeed, ?_, ?_⟩
                · intro a
                  change Tj0.vertex _ = seed.vertex a
                  calc
                    Tj0.vertex _ = Tj0.vertex
                        (Fin.castLE (Nat.succ_le_succ hseedTjSegment.1)
                          a) := by congr 1
                    _ = seed.vertex a := hseedTjSegment.2.1 a
                · intro a
                  change Tj0.edge _ = seed.edge a
                  calc
                    Tj0.edge _ = Tj0.edge
                        (Fin.castLE hseedTjSegment.1 a) := by congr 1
                    _ = seed.edge a := hseedTjSegment.2.2 a
              have hRXTj : TreeSequenceInitialSegment RX Tj0 :=
                prefixSegment Tj0 i.val
                  (Nat.le_trans seed.positive hiSeed) (Nat.le_of_lt hiTj)
              have hsuffix : TashkinovAugmentationSequence
                  (ett.series.data.coloring jSlot.castSucc) RX Tj0 :=
                TashkinovAugmentationSequenceSuffix _ seed RX Tj0
                  hroutePhiTj0 hseedRX hRXTj
              have hRXlen : RX.length = i.val := rfl
              obtain ⟨A, hRXA, hATj⟩ := firstStep hsuffix (by omega)
              rcases hRXA with
                ⟨hlenA, hRXASegment, c, hcolorA, hmissingRX⟩
              have hATjSegment : TreeSequenceInitialSegment A Tj0 :=
                TashkinovAugmentationSequenceInitialSegment _ _ _ hATj
              have hAi : A.length = i.val + 1 := by omega
              let ai : Fin A.length := ⟨i.val, by omega⟩
              have hcolorTj :
                  ett.series.data.coloring jSlot.castSucc (Tj0.edge i) =
                    some c := by
                have haiLast : ai =
                    Fin.cast hlenA.symm (Fin.last RX.length) := by
                  apply Fin.ext
                  simp [ai, hRXlen]
                have hTjai : Tj0.edge
                      (Fin.castLE hATjSegment.1 ai) = A.edge ai :=
                  hATjSegment.2.2 ai
                have hcast : Fin.castLE hATjSegment.1 ai = i := by
                  apply Fin.ext
                  simp [ai]
                rw [← hcast, hTjai, haiLast]
                exact hcolorA
              have hleftX {x : V} (hxU : x ∈ TreeSequenceVertexSet U) :
                  x ∈ TreeSequenceVertexSet X := by
                simp only [TreeSequenceVertexSet, Finset.mem_image,
                  Finset.mem_univ, true_and] at hxU ⊢
                obtain ⟨a, ha⟩ := hxU
                refine ⟨Fin.castLE (Nat.succ_le_succ hnU) a, ?_⟩
                change M.vertex _ = x
                calc
                  M.vertex _ = M.vertex
                      (Fin.castLE (Nat.succ_le_succ hleftSegment.1) a) := by
                    congr 1
                  _ = U.vertex a := hleftSegment.2.1 a
                  _ = x := ha
              have hmissingX : c ∈ TreeMissingColors rho2 X := by
                unfold TreeMissingColors at hmissingRX ⊢
                obtain ⟨x, hxRX, hcx⟩ :=
                  Finset.mem_biUnion.mp hmissingRX
                simp only [TreeSequenceVertexSet, Finset.mem_image,
                  Finset.mem_univ, true_and] at hxRX
                obtain ⟨a, ha⟩ := hxRX
                have hxTj : x ∈ TreeSequenceVertexSet Tj0 :=
                  vertexTransfer hRXTj
                    (by
                      simp only [TreeSequenceVertexSet, Finset.mem_image,
                        Finset.mem_univ, true_and]
                      exact ⟨a, ha⟩)
                have hxX : x ∈ TreeSequenceVertexSet X := by
                  by_cases hxU : x ∈ TreeSequenceVertexSet U
                  · exact hleftX hxU
                  · have haPos : 1 ≤ a.val := by
                      by_contra hzero
                      have haZero : a.val = 0 := by omega
                      let p0 : Fin (seed.length + 1) := ⟨0, by omega⟩
                      have hTjp0 := hseedTjSegment.2.1 p0
                      have hUp0 := hseedU.2.1 p0
                      apply hxU
                      simp only [TreeSequenceVertexSet, Finset.mem_image,
                        Finset.mem_univ, true_and]
                      refine ⟨Fin.castLE (Nat.succ_le_succ hseedU.1) p0, ?_⟩
                      have haTj : Tj0.vertex
                            (Fin.castLE
                              (Nat.succ_le_succ (Nat.le_of_lt hiTj)) a) =
                          x := by
                        simpa [RX, TreeSequencePrefix] using ha
                      have ha0 : Fin.castLE
                            (Nat.succ_le_succ (Nat.le_of_lt hiTj)) a =
                          Fin.castLE
                            (Nat.succ_le_succ hseedTjSegment.1) p0 := by
                        apply Fin.ext
                        exact haZero
                      rw [ha0, hTjp0] at haTj
                      exact hUp0.trans haTj
                    let r : Fin Tj0.length := ⟨a.val - 1, by
                      have haLt : a.val < RX.length + 1 := a.isLt
                      simp [RX] at haLt
                      omega⟩
                    have hrSucc : r.succ = Fin.castLE
                        (Nat.succ_le_succ (Nat.le_of_lt hiTj)) a := by
                      apply Fin.ext
                      exact Nat.sub_add_cancel haPos
                    have hrv : Tj0.vertex r.succ = x := by
                      rw [hrSucc]
                      simpa [RX, TreeSequencePrefix] using ha
                    have hrOutside :
                        Tj0.vertex r.succ ∉ TreeSequenceVertexSet U := by
                      simpa [hrv] using hxU
                    have hri : r.val < i.val := by
                      have haLt : a.val < RX.length + 1 := a.isLt
                      simp [RX, r] at haLt ⊢
                      omega
                    obtain ⟨qM, hqU, hedgeq, hvertexq⟩ :=
                      heveryNewRightEntry r hrOutside
                    have hqn : qM.val < n :=
                      hrightOrder r i hrOutside hrightOutside hri qM mIndex
                        hvertexq hvertexMTj
                    simp only [TreeSequenceVertexSet, Finset.mem_image,
                      Finset.mem_univ, true_and]
                    let qX : Fin (X.length + 1) := ⟨qM.val + 1, by
                      change qM.val + 1 < n + 1
                      omega⟩
                    refine ⟨qX, ?_⟩
                    rw [← hrv, ← hvertexq]
                    change M.vertex _ = M.vertex qM.succ
                    congr 1
                by_cases hxTerminal : x = v
                · have hcTerminalOld : c ∈ MissingColors G
                      (ett.series.data.coloring jSlot.castSucc) v := by
                    rw [← hxTerminal]
                    exact hcx
                  rcases Finset.mem_union.mp
                      (hterminalInclusion hcTerminalOld) with
                    hcTerminal | hcU
                  · exact Finset.mem_biUnion.mpr ⟨x, hxX, by
                      simpa [hxTerminal] using hcTerminal⟩
                  · exact Finset.mem_biUnion.mpr ⟨u, hleftX huU, hcU⟩
                · refine Finset.mem_biUnion.mpr ⟨x, hxX, ?_⟩
                  have hxTj' : x ∈ TreeSequenceVertexSet
                      (ett.series.data.tree jSlot.succ.castSucc) := by
                    simpa [Tj0] using hxTj
                  rw [c2.1 x (Finset.mem_union_left _ hxTj'),
                    hb2Missing.1 x
                      (Finset.mem_erase.mpr ⟨hxTerminal, hxTj'⟩)]
                  exact hcx
              have hXY : TashkinovAugmentation rho2 X Y := by
                have hlenXY : Y.length = X.length + 1 := by
                  change n + 1 = n + 1
                  rfl
                refine ⟨hlenXY, ?_, c, ?_, hmissingX⟩
                · simpa [X, Y] using prefixPrefix M n
                    (Nat.le_trans U.positive hnU) hnSuccM
                · have hfixedTj : rho2 (Tj0.edge i) =
                      ett.series.data.coloring jSlot.castSucc
                        (Tj0.edge i) := by
                    have hc2 : rho2 (Tj0.edge i) = rho1 (Tj0.edge i) := by
                      apply c2.2
                      apply Or.inl
                      exact ⟨i, by simp [Tj0]⟩
                    have hb2 := hb2TreeEdges
                      (Fin.cast (by simp [Tj0]) i)
                    simpa [Tj0] using hc2.trans (hb2.1.trans hb2.2)
                  have hcolorM : rho2 (M.edge mIndex) = some c := by
                    rw [hedgeMTj]
                    exact hfixedTj.trans hcolorTj
                  change rho2 (M.edge _) = some c
                  convert hcolorM using 1
                  apply congrArg rho2
                  apply congrArg M.edge
                  apply Fin.ext
                  rfl
              change TashkinovAugmentationSequence rho2 U Y
              exact Relation.ReflTransGen.tail ih' hXY
        have hfull := replay M.length hleftSegment.1 le_rfl
        simpa [prefixSelf] using hfull
      obtain ⟨C, hclosureMC⟩ := TashkinovClosureExists rho2 M
      have hrouteUC : TashkinovAugmentationSequence rho2 U C :=
        Relation.ReflTransGen.trans hrouteUM hclosureMC.1
      have hrouteSeedC : TashkinovAugmentationSequence rho2 seed C :=
        Relation.ReflTransGen.trans hrouteRhoTwoU hrouteUC
      have hclosedC :
          ColoredVertexSetClosed G rho2 (TreeSequenceVertexSet C) :=
        hclosureMC.2
      have hseedVertexBeforeJ (i : Fin (seed.length + 1))
          (hi : i.val < seed.length) :
          seed.vertex i ∈ TreeVerticesBefore
            (ett.series.data.tree jSlot.succ.castSucc) v hterminalJ := by
        unfold TreeVerticesBefore
        apply Finset.mem_filter.mpr
        constructor
        · exact vertexTransfer hseedTj
            (by simp [TreeSequenceVertexSet])
        · let p : Fin
              ((ett.series.data.tree jSlot.succ.castSucc).length + 1) :=
            Fin.castLE (Nat.succ_le_succ hseedTj.1) i
          let z : Fin
              ((ett.series.data.tree jSlot.succ.castSucc).length + 1) :=
            Fin.castLE (Nat.succ_le_succ hseedTj.1)
              (Fin.last seed.length)
          refine ⟨p, z, hseedTj.2.1 i,
            (hseedTj.2.1 (Fin.last seed.length)).trans hseedTerminal, ?_⟩
          simpa [p, z] using hi
      have segmentVertexBeforeJ {A : TreeSequence G e0}
          (hAseed : TreeSequenceInitialSegment A seed)
          (hAlen : A.length < seed.length) {x : V}
          (hxA : x ∈ TreeSequenceVertexSet A) :
          x ∈ TreeVerticesBefore
            (ett.series.data.tree jSlot.succ.castSucc) v hterminalJ := by
        obtain ⟨hAseedLen, hAseedVertices, -⟩ := hAseed
        simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ,
          true_and] at hxA
        obtain ⟨i, rfl⟩ := hxA
        have hi : (Fin.castLE (Nat.succ_le_succ hAseedLen) i).val <
            seed.length := by
          change i.val < seed.length
          omega
        rw [← hAseedVertices i]
        exact hseedVertexBeforeJ _ hi
      have transportSeedStep2 {A B : TreeSequence G e0}
          (hstep : TashkinovAugmentation
            (ett.series.data.coloring jSlot.castSucc) A B)
          (hBseed : TreeSequenceInitialSegment B seed) :
          TashkinovAugmentation rho2 A B := by
        rcases hstep with ⟨hlen, hAB, c, hcolor, hcMissing⟩
        have hAseed : TreeSequenceInitialSegment A seed :=
          segmentTrans hAB hBseed
        have hAlen : A.length < seed.length :=
          lt_of_lt_of_le (by omega) hBseed.1
        have hcMissingRho : c ∈ TreeMissingColors rho2 A := by
          unfold TreeMissingColors at hcMissing ⊢
          obtain ⟨x, hxA, hcx⟩ := Finset.mem_biUnion.mp hcMissing
          refine Finset.mem_biUnion.mpr ⟨x, hxA, ?_⟩
          rw [c1.2 x (segmentVertexBeforeJ hAseed hAlen hxA)]
          exact hcx
        let added : Fin B.length := Fin.cast hlen.symm (Fin.last A.length)
        obtain ⟨attach, hattach⟩ := B.attaches added
        let oldPosition : Fin (B.length + 1) :=
          Fin.castLT attach
            (Nat.lt_trans attach.isLt (Nat.succ_lt_succ added.isLt))
        have holdValue : oldPosition.val < A.length + 1 := by
          dsimp [oldPosition, added]
          omega
        let oldA : Fin (A.length + 1) := ⟨oldPosition.val, holdValue⟩
        have holdEq : B.vertex oldPosition = A.vertex oldA := by
          have hcast : Fin.castLE (Nat.succ_le_succ hAB.1) oldA =
              oldPosition := by
            apply Fin.ext
            rfl
          rw [← hcast]
          exact hAB.2.1 oldA
        have holdA : A.vertex oldA ∈ TreeSequenceVertexSet A := by
          simp [TreeSequenceVertexSet]
        have holdBefore : B.vertex oldPosition ∈ TreeVerticesBefore
            (ett.series.data.tree jSlot.succ.castSucc) v hterminalJ := by
          rw [holdEq]
          exact segmentVertexBeforeJ hAseed hAlen holdA
        have holdIncident : Incident G (B.vertex oldPosition)
            (B.edge added) := by
          unfold Incident
          rw [hattach]
          simp [oldPosition]
        have haddedFixed : rho2 (B.edge added) =
            ett.series.data.coloring jSlot.castSucc (B.edge added) := by
          apply c1.1 (B.edge added)
            ⟨B.vertex oldPosition, holdBefore, holdIncident⟩
          refine ⟨c, ?_, hcolor⟩
          apply Finset.mem_union_left
          unfold TreeMissingColors at hcMissing
          obtain ⟨x, hxA, hcx⟩ := Finset.mem_biUnion.mp hcMissing
          exact Finset.mem_biUnion.mpr
            ⟨x, segmentVertexBeforeJ hAseed hAlen hxA, hcx⟩
        refine ⟨hlen, hAB, c, ?_, hcMissingRho⟩
        change rho2 (B.edge added) = some c
        exact haddedFixed.trans hcolor
      have transportSeedRoute2 (S : TreeSequence G e0)
          (hroute : TashkinovAugmentationSequence
            (ett.series.data.coloring jSlot.castSucc) S seed) :
          TashkinovAugmentationSequence rho2 S seed := by
        unfold TashkinovAugmentationSequence at hroute ⊢
        induction hroute using Relation.ReflTransGen.head_induction_on with
        | refl => exact Relation.ReflTransGen.refl
        | @head A B hAB hBseed ih =>
            have hBsegment : TreeSequenceInitialSegment B seed :=
              TashkinovAugmentationSequenceInitialSegment _ B seed hBseed
            exact Relation.ReflTransGen.head
              (transportSeedStep2 hAB hBsegment) ih
      have huM : u ∈ TreeSequenceVertexSet M := by
        rw [hunion.vertexSet]
        exact Finset.mem_union_left _ huU
      have hMCsegment : TreeSequenceInitialSegment M C :=
        TashkinovAugmentationSequenceInitialSegment rho2 M C hclosureMC.1
      have huC : u ∈ TreeSequenceVertexSet C :=
        vertexTransfer hMCsegment huM
      have hTj0C : TreeSequenceVertexSet Tj0 ⊆
          TreeSequenceVertexSet C := by
        intro x hx
        apply vertexTransfer hMCsegment
        rw [hunion.vertexSet]
        exact Finset.mem_union_right _ hx
      have hTj0StrictC : TreeSequenceVertexSet Tj0 <
          TreeSequenceVertexSet C :=
        Finset.ssubset_iff_subset_ne.mpr ⟨hTj0C, by
          intro heq
          apply huOutside
          have huTj0 : u ∈ TreeSequenceVertexSet Tj0 := heq.symm.subset huC
          simpa [Tj0] using huTj0⟩
      by_cases hjPositive : 0 < jSlot.val
      · have hseedBuildPhi :
            (ett.series.data.kind jSlot.castSucc =
                some TashkinovExtensionKind.PE ∧
              TashkinovAugmentationSequence
                (ett.series.data.coloring jSlot.castSucc) Tprevious seed) ∨
            ((ett.series.data.kind jSlot.castSucc =
                  some TashkinovExtensionKind.SE ∨
                ett.series.data.kind jSlot.castSucc =
                  some TashkinovExtensionKind.RE) ∧
              ∃ (f : E) (adjoinSeed : TreeSequence G e0),
                ett.series.data.connectingEdges jSlot.castSucc = {f} ∧
                  TreeSequenceAdjoinEdge Tprevious f adjoinSeed ∧
                  TashkinovAugmentationSequence
                    (ett.series.data.coloring jSlot.castSucc)
                    adjoinSeed seed) := by as_aux_lemma =>
          generalize htarget : jSlot.castSucc = target
          cases ett.series.certified target with
          | initial =>
              have hzero := congrArg Fin.val htarget
              simp at hzero
              omega
          | SE i previousProper previousOneUncolored previousClosed
              previousNotStronglyClosed noRevisiting choice seriesAlternative
              currentColoring currentStored currentEdges currentKind currentVertex
              currentOutside currentDelta currentGamma adjoined adjoinedExactly
              closedExtension orderedExtension strictExtension =>
            have hi : i.succ = jSlot.castSucc := htarget.symm
            have hroute : TashkinovAugmentationSequence
                (ett.series.data.coloring jSlot.castSucc) adjoined
                (ett.series.data.tree jSlot.succ.castSucc) := by
              have h := closedExtension.1
              rw [hi, hjTreeIndex] at h
              exact h
            have hadjoinedTj : TreeSequenceInitialSegment adjoined
                (ett.series.data.tree jSlot.succ.castSucc) :=
              TashkinovAugmentationSequenceInitialSegment _ _ _ hroute
            have hadjoinedLength : adjoined.length ≤ seed.length := by
              rcases adjoinedExactly with ⟨hlen, -, -⟩
              have hiCast : i.succ.castSucc =
                  jSlot.castSucc.castSucc := by
                apply Fin.ext
                simpa using congrArg Fin.val hi
              have hprev : ett.series.data.tree i.succ.castSucc =
                  Tprevious := by rw [hiCast]
              rw [hprev] at hlen
              rw [hlen]
              exact Nat.succ_le_of_lt (hpreviousStrict hjPositive)
            have hadjoinedSeed : TreeSequenceInitialSegment adjoined seed :=
              commonPrefix hadjoinedTj hseedTj hadjoinedLength
            right
            refine ⟨Or.inl (by simpa [htarget] using currentKind),
              choice.edge, adjoined, ?_, ?_, ?_⟩
            · simpa [htarget] using currentEdges
            · rcases adjoinedExactly with ⟨hlen, hsegment, hedge⟩
              have hiCast : i.castSucc.succ =
                  jSlot.castSucc.castSucc := by
                apply Fin.ext
                simpa using congrArg Fin.val hi
              have hlenNew : adjoined.length = Tprevious.length + 1 := by
                simpa [Tprevious, hiCast] using hlen
              have hsegmentNew :
                  TreeSequenceInitialSegment Tprevious adjoined := by
                simpa [Tprevious, hiCast] using hsegment
              refine ⟨hlenNew, hsegmentNew, ?_⟩
              have haddedIndex :
                  Fin.cast hlenNew.symm (Fin.last Tprevious.length) =
                    Fin.cast hlen.symm
                      (Fin.last
                        (ett.series.data.tree i.succ.castSucc).length) := by
                apply Fin.ext
                simp [Tprevious, hiCast]
              rw [haddedIndex]
              exact hedge
            · simpa [hi] using
                (TashkinovAugmentationSequenceRestrict
                  (ett.series.data.coloring jSlot.castSucc) adjoined seed
                  (ett.series.data.tree jSlot.succ.castSucc) hroute
                  hadjoinedSeed hseedTj)
          | PE i previousProper previousOneUncolored previousClosed
              previousNotStronglyClosed noRevisiting choice
              seriesAlternativeFails chosenGamma gammaRule secondStable
              secondStableProper secondStableOneUncolored secondStableRelation
              exitWitness currentColoring currentProper currentOneUncolored
              currentStored currentEdges currentKind currentVertex currentOutside
              currentDelta currentGamma closedExtension orderedExtension
              strictExtension =>
            have hi : i.succ = jSlot.castSucc := htarget.symm
            have hroute : TashkinovAugmentationSequence
                (ett.series.data.coloring jSlot.castSucc) Tprevious
                (ett.series.data.tree jSlot.succ.castSucc) := by
              have h := closedExtension.1
              rw [hi, hjTreeIndex] at h
              simpa [Tprevious, hi] using h
            left
            refine ⟨by simpa [htarget] using currentKind, ?_⟩
            simpa [hi] using
              (TashkinovAugmentationSequenceRestrict
                (ett.series.data.coloring jSlot.castSucc) Tprevious seed
                (ett.series.data.tree jSlot.succ.castSucc) hroute
                (hpreviousSeed hjPositive) hseedTj)
          | RE i previousProper previousOneUncolored previousClosed
              previousNotStronglyClosed available currentColoring currentStored
              currentEdges currentKind currentVertex currentOutside currentDelta
              currentGamma adjoined adjoinedExactly closedExtension orderedExtension
              strictExtension =>
            have hi : i.succ = jSlot.castSucc := htarget.symm
            have hroute : TashkinovAugmentationSequence
                (ett.series.data.coloring jSlot.castSucc) adjoined
                (ett.series.data.tree jSlot.succ.castSucc) := by
              have h := closedExtension.1
              rw [hi, hjTreeIndex] at h
              exact h
            have hadjoinedTj : TreeSequenceInitialSegment adjoined
                (ett.series.data.tree jSlot.succ.castSucc) :=
              TashkinovAugmentationSequenceInitialSegment _ _ _ hroute
            have hadjoinedLength : adjoined.length ≤ seed.length := by
              rcases adjoinedExactly with ⟨hlen, -, -⟩
              have hiCast : i.succ.castSucc =
                  jSlot.castSucc.castSucc := by
                apply Fin.ext
                simpa using congrArg Fin.val hi
              have hprev : ett.series.data.tree i.succ.castSucc =
                  Tprevious := by rw [hiCast]
              rw [hprev] at hlen
              rw [hlen]
              exact Nat.succ_le_of_lt (hpreviousStrict hjPositive)
            have hadjoinedSeed : TreeSequenceInitialSegment adjoined seed :=
              commonPrefix hadjoinedTj hseedTj hadjoinedLength
            right
            refine ⟨Or.inr (by simpa [htarget] using currentKind),
              available.edge, adjoined, ?_, ?_, ?_⟩
            · simpa [htarget] using currentEdges
            · rcases adjoinedExactly with ⟨hlen, hsegment, hedge⟩
              have hiCast : i.castSucc.succ =
                  jSlot.castSucc.castSucc := by
                apply Fin.ext
                simpa using congrArg Fin.val hi
              have hlenNew : adjoined.length = Tprevious.length + 1 := by
                simpa [Tprevious, hiCast] using hlen
              have hsegmentNew :
                  TreeSequenceInitialSegment Tprevious adjoined := by
                simpa [Tprevious, hiCast] using hsegment
              refine ⟨hlenNew, hsegmentNew, ?_⟩
              have haddedIndex :
                  Fin.cast hlenNew.symm (Fin.last Tprevious.length) =
                    Fin.cast hlen.symm
                      (Fin.last
                        (ett.series.data.tree i.succ.castSucc).length) := by
                apply Fin.ext
                simp [Tprevious, hiCast]
              rw [haddedIndex]
              exact hedge
            · simpa [hi] using
                (TashkinovAugmentationSequenceRestrict
                  (ett.series.data.coloring jSlot.castSucc) adjoined seed
                  (ett.series.data.tree jSlot.succ.castSucc) hroute
                  hadjoinedSeed hseedTj)
        have hseedBuildRho2 :
            (ett.series.data.kind jSlot.castSucc =
                some TashkinovExtensionKind.PE ∧
              TashkinovAugmentationSequence rho2 Tprevious seed) ∨
            ((ett.series.data.kind jSlot.castSucc =
                  some TashkinovExtensionKind.SE ∨
                ett.series.data.kind jSlot.castSucc =
                  some TashkinovExtensionKind.RE) ∧
              ∃ (f : E) (adjoinSeed : TreeSequence G e0),
                ett.series.data.connectingEdges jSlot.castSucc = {f} ∧
                  TreeSequenceAdjoinEdge Tprevious f adjoinSeed ∧
                  TashkinovAugmentationSequence rho2 adjoinSeed seed) := by
          as_aux_lemma =>
          rcases hseedBuildPhi with hparallel | hserial
          · exact Or.inl ⟨hparallel.1,
              transportSeedRoute2 Tprevious hparallel.2⟩
          · rcases hserial with ⟨hkind, f, adjoinSeed, hconnecting,
                hadjoin, hroute⟩
            exact Or.inr ⟨hkind, f, adjoinSeed, hconnecting, hadjoin,
              transportSeedRoute2 adjoinSeed hroute⟩
        obtain ⟨lower, hround, hLowerMP, htrees, hdata⟩ :=
          CertifiedETTRestriction G k e0 input T generating ett hMP
            jSlot.val hjPositive jSlot.isLt
        let nLower : Fin (lower.rounds + 1) := Fin.last lower.rounds
        have hnMap : Fin.castLE (by omega) nLower = jSlot.castSucc := by
          apply Fin.ext
          simp [nLower, hround]
        have hnTreeMap : Fin.castLE (by omega) nLower.castSucc =
            jSlot.castSucc.castSucc := by
          apply Fin.ext
          simp [nLower, hround]
        have hLowerTree : lower.series.data.tree nLower.castSucc =
            Tprevious := by
          rw [htrees nLower.castSucc, hnTreeMap]
        have hLowerColor : lower.series.data.coloring nLower =
            ett.series.data.coloring jSlot.castSucc := by
          rw [(hdata nLower).1, hnMap]
        have hLowerStored : TashkinovStoredColors lower.series.data nLower =
            TashkinovStoredColors ett.series.data jSlot.castSucc := by
          rw [(hdata nLower).2.2.2.2.2.2.2.2.1, hnMap]
        have hLowerKind : lower.series.data.kind nLower =
            ett.series.data.kind jSlot.castSucc := by
          rw [(hdata nLower).2.2.2.1, hnMap]
        have hLowerConnecting : lower.series.data.connectingEdges nLower =
            ett.series.data.connectingEdges jSlot.castSucc := by
          rw [(hdata nLower).2.2.1, hnMap]
        have hstablePrevious : StableColoring Tprevious
            (TashkinovStoredColors ett.series.data jSlot.castSucc)
            (ett.series.data.coloring jSlot.castSucc) rho2 := by
          constructor
          · intro f hfIncident hfControlled
            obtain ⟨x, hxPrevious, hxf⟩ := hfIncident
            apply c1.1 f
              ⟨x, segmentVertexBeforeJ (hpreviousSeed hjPositive)
                (hpreviousStrict hjPositive) hxPrevious, hxf⟩
            obtain ⟨color, hcControlled, hfc⟩ := hfControlled
            refine ⟨color, ?_, hfc⟩
            rcases Finset.mem_union.mp hcControlled with hcMissing | hcStored
            · apply Finset.mem_union_left
              unfold TreeMissingColors at hcMissing
              obtain ⟨z, hzPrevious, hcz⟩ :=
                Finset.mem_biUnion.mp hcMissing
              exact Finset.mem_biUnion.mpr
                ⟨z, segmentVertexBeforeJ (hpreviousSeed hjPositive)
                  (hpreviousStrict hjPositive) hzPrevious, hcz⟩
            · exact Finset.mem_union_right _ hcStored
          · intro x hxPrevious
            exact c1.2 x
              (segmentVertexBeforeJ (hpreviousSeed hjPositive)
                (hpreviousStrict hjPositive) hxPrevious)
        have hstableLower : StableColoring
            (lower.series.data.tree nLower.castSucc)
            (TashkinovStoredColors lower.series.data nLower)
            (lower.series.data.coloring nLower) rho2 := by
          simpa [hLowerTree, hLowerStored, hLowerColor] using hstablePrevious
        have hLowerPack := hlower lower (by omega) (by omega) hLowerMP
        have hmod : ModColoring lower rho2 :=
          hLowerPack.2.2.2.2.2 rho2 hrho2Proper hrho2One hstableLower
        have hPreviousC : TreeSequenceInitialSegment Tprevious C := by
          rcases hseedBuildRho2 with hparallel | hserial
          · exact TashkinovAugmentationSequenceInitialSegment rho2 Tprevious C
              (Relation.ReflTransGen.trans hparallel.2 hrouteSeedC)
          · rcases hserial with ⟨-, f, adjoinSeed, -, hadjoin, hroute⟩
            exact segmentTrans hadjoin.2.1
              (TashkinovAugmentationSequenceInitialSegment rho2 adjoinSeed C
                (Relation.ReflTransGen.trans hroute hrouteSeedC))
        have huNotPrevious : u ∉ TreeSequenceVertexSet Tprevious := by
          intro huPrevious
          exact huOutside (vertexTransfer (hpreviousTj hjPositive) huPrevious)
        have hPreviousStrictC : Tprevious.length < C.length := by
          have hsubset : TreeSequenceVertexSet Tprevious ⊆
              TreeSequenceVertexSet C := vertexTransfer hPreviousC
          have hstrict : TreeSequenceVertexSet Tprevious <
              TreeSequenceVertexSet C :=
            Finset.ssubset_iff_subset_ne.mpr ⟨hsubset, by
              intro heq
              exact huNotPrevious (heq.symm.subset huC)⟩
          have hcard := Finset.card_lt_card hstrict
          simpa [TreeSequenceVertexSet, Finset.card_image_of_injective,
            Tprevious.vertex_injective, C.vertex_injective] using hcard
        have hLowerEligible :
            (lower.series.data.kind nLower =
                  some TashkinovExtensionKind.PE ∧
                TashkinovAugmentationSequence rho2 Tprevious C) ∨
              ((lower.series.data.kind nLower =
                    some TashkinovExtensionKind.SE ∨
                  lower.series.data.kind nLower =
                    some TashkinovExtensionKind.RE) ∧
                ∃ (f : E) (adjoinSeed : TreeSequence G e0),
                  lower.series.data.connectingEdges nLower = {f} ∧
                    TreeSequenceAdjoinEdge Tprevious f adjoinSeed ∧
                    TashkinovAugmentationSequence rho2 adjoinSeed C) := by
          rcases hseedBuildRho2 with hparallel | hserial
          · exact Or.inl ⟨hLowerKind.trans hparallel.1,
              Relation.ReflTransGen.trans hparallel.2 hrouteSeedC⟩
          · rcases hserial with ⟨hkind, f, adjoinSeed, hconnecting,
                hadjoin, hroute⟩
            exact Or.inr
              ⟨Or.imp (hLowerKind.trans) (hLowerKind.trans) hkind,
                f, adjoinSeed, hLowerConnecting.trans hconnecting, hadjoin,
                Relation.ReflTransGen.trans hroute hrouteSeedC⟩
        have hcorrNonempty : Nonempty
            (CorrespondingExtendedTashkinovTree G k e0 lower rho2 C) := by
          have hmod' := hmod
          unfold ModColoring at hmod'
          dsimp only at hmod'
          apply hmod'.2.2 C
          · rw [hLowerTree]
            exact hPreviousC
          · rw [hLowerTree]
            exact hPreviousStrictC
          · change
              (lower.series.data.kind nLower =
                    some TashkinovExtensionKind.PE ∧
                  TashkinovAugmentationSequence rho2
                    (lower.series.data.tree nLower.castSucc) C) ∨
                ((lower.series.data.kind nLower =
                      some TashkinovExtensionKind.SE ∨
                    lower.series.data.kind nLower =
                      some TashkinovExtensionKind.RE) ∧
                  ∃ (f : E) (adjoinSeed : TreeSequence G e0),
                    lower.series.data.connectingEdges nLower = {f} ∧
                      TreeSequenceAdjoinEdge
                        (lower.series.data.tree nLower.castSucc) f adjoinSeed ∧
                      TashkinovAugmentationSequence rho2 adjoinSeed C)
            rw [hLowerTree]
            exact hLowerEligible
        obtain ⟨corr⟩ := hcorrNonempty
        have hreplacementMP : MaximumProperty corr.replacementETT :=
          MaximumPropertyTransport G k e0 lower rho2 hmod C corr hLowerMP
        have hcorrRounds : corr.replacementETT.rounds = jSlot.val :=
          corr.rungAgreement.trans hround
        have hCElementary :
            ColoredVertexSetElementary G rho2 (TreeSequenceVertexSet C) :=
          (hlower corr.replacementETT corr.replacementETT.roundsPositive
            (by omega) hreplacementMP).1
        have hbound : (TreeSequenceVertexSet C).card ≤
            (TreeSequenceVertexSet Tj0).card := by
          have hMP' := hMP
          unfold MaximumProperty at hMP'
          have hstage := hMP'.2 jSlot.val hjPositive jSlot.isLt
          dsimp only at hstage
          have hidx : (⟨jSlot.val, by omega⟩ : Fin (ett.rounds + 1)) =
              jSlot.castSucc := by
            apply Fin.ext
            rfl
          have hnextIdx :
              (⟨jSlot.val + 1, by omega⟩ : Fin (ett.rounds + 2)) =
                jSlot.succ.castSucc := by
            apply Fin.ext
            rfl
          rw [hidx, hnextIdx] at hstage
          rcases hseedBuildRho2 with hparallel | hserial
          · have hclosurePreviousC : TashkinovClosure rho2 Tprevious C :=
              ⟨Relation.ReflTransGen.trans hparallel.2 hrouteSeedC,
                hclosedC⟩
            have hraw := hstage rho2 Tprevious C hrho2Proper hrho2One
              hstablePrevious
              (Or.inl ⟨hparallel.1, rfl⟩) hclosurePreviousC
            simpa [Tprevious, Tj0] using hraw
          · rcases hserial with ⟨hkind, f, adjoinSeed, hconnecting,
                hadjoin, hroute⟩
            have hclosureAdjoinC : TashkinovClosure rho2 adjoinSeed C :=
              ⟨Relation.ReflTransGen.trans hroute hrouteSeedC, hclosedC⟩
            have hraw := hstage rho2 adjoinSeed C hrho2Proper hrho2One
              hstablePrevious
              (Or.inr ⟨hkind, f, hconnecting, by
                simpa [Tprevious] using hadjoin⟩) hclosureAdjoinC
            simpa [Tj0] using hraw
        have hstrictCard := Finset.card_lt_card hTj0StrictC
        exact (Nat.not_lt_of_ge hbound) hstrictCard
      · have hjZero : jSlot.val = 0 := by omega
        have hjIndex : jSlot.castSucc =
            (0 : Fin (ett.rounds + 1)) := by
          apply Fin.ext
          exact hjZero
        set_option maxHeartbeats 800000 in
          cases hcert : ett.series.certified
              (0 : Fin (ett.rounds + 1)) with
          | initial triple seedLength initialColoring initialStored initialEdges
            initialKind initialVertex initialOutside initialDelta initialGamma
            initialClosure =>
            have htreeOne : ett.series.data.tree 1 = Tj0 := by
              unfold Tj0
              congr 1
              apply Fin.ext
              simp [hjZero]
            have hinitialTj : TreeSequenceInitialSegment
                (ett.series.data.tree 0) Tj0 := by
              have h := TashkinovAugmentationSequenceInitialSegment _ _ _
                initialClosure.1
              simpa [htreeOne] using h
            have hinitialSeed : TreeSequenceInitialSegment
                (ett.series.data.tree 0) seed := by
              apply commonPrefix hinitialTj
                (by simpa [Tj0] using hseedTj0)
              rw [seedLength]
              exact seed.positive
            have hroutePhiSeed : TashkinovAugmentationSequence
                (ett.series.data.coloring jSlot.castSucc)
                (ett.series.data.tree 0) seed := by
              have hrestricted := TashkinovAugmentationSequenceRestrict
                (ett.series.data.coloring 0) (ett.series.data.tree 0) seed
                Tj0 (by simpa [htreeOne] using initialClosure.1)
                hinitialSeed (by simpa [Tj0] using hseedTj0)
              simpa [hjIndex] using hrestricted
            have hrouteRhoTwoBase : TashkinovAugmentationSequence rho2
                (ett.series.data.tree 0) seed :=
              transportSeedRoute2 (ett.series.data.tree 0) hroutePhiSeed
            have hrouteBaseC : TashkinovAugmentationSequence rho2
                (ett.series.data.tree 0) C :=
              Relation.ReflTransGen.trans hrouteRhoTwoBase hrouteSeedC
            have htripleRho : KTriple G k e0 rho2 :=
              ⟨triple.1, triple.2.1, triple.2.2.1,
                hrho2Proper, hrho2One⟩
            have hinitialTree : TashkinovTree G e0 rho2
                (ett.series.data.tree 0) := by
              intro a ha
              rw [seedLength] at a
              omega
            have hCTree : TashkinovTree G e0 rho2 C :=
              TashkinovAugmentationSequencePreservesTashkinovTree G e0 rho2
                (ett.series.data.tree 0) C hinitialTree hrouteBaseC
            have hk : ChromaticIndex G - 1 = k := by
              have hchromatic := triple.2.1
              omega
            have hCOrder : (TreeSequenceVertexSet C).card ≤
                TashkinovOrder G := by
              unfold TashkinovOrder
              dsimp only
              apply Finset.le_max'
              apply Finset.mem_insert_of_mem
              simp only [Finset.mem_filter, Finset.mem_range]
              constructor
              · exact Nat.lt_succ_of_le (Finset.card_le_univ _)
              · rw [hk]
                exact ⟨e0, rho2, C, htripleRho, hCTree, rfl⟩
            have hTjOrder : (TreeSequenceVertexSet Tj0).card =
                TashkinovOrder G := by
              rw [← htreeOne]
              exact hMP.1
            have hbound : (TreeSequenceVertexSet C).card ≤
                (TreeSequenceVertexSet Tj0).card := by
              rw [hTjOrder]
              exact hCOrder
            exact (Nat.not_lt_of_ge hbound)
              (Finset.card_lt_card hTj0StrictC)
    · have hcaseTwoPointwise : ∀ x : V,
          x ∈ (TreeSequenceVertexSet TjPrime).erase v →
            MissingColors G rho1 x ∩ supportColors = ∅ := by
        intro x hx
        apply Finset.eq_empty_of_forall_notMem
        intro c hc
        have hbig : c ∈
            ((TreeSequenceVertexSet TjPrime).erase v).biUnion
                (fun y => MissingColors G rho1 y) ∩ supportColors := by
          exact Finset.mem_inter.mpr
            ⟨Finset.mem_biUnion.mpr ⟨x, hx, (Finset.mem_inter.mp hc).1⟩,
              (Finset.mem_inter.mp hc).2⟩
        rw [hcaseTwo] at hbig
        simpa using hbig
      have hsupportSet : supportColors =
          (ExtensionBaseSupportClass ett v hvFinal v).biUnion
            (fun s => ett.series.data.stored s.succ) := by
        ext c
        simp only [supportColors, Finset.mem_biUnion, Finset.mem_univ,
          true_and]
        constructor
        · rintro ⟨a, hc⟩
          exact ⟨indices0 a, (hclass0 (indices0 a)).2 ⟨a, rfl⟩, hc⟩
        · rintro ⟨s, hs, hc⟩
          obtain ⟨a, rfl⟩ := (hclass0 s).1 hs
          exact ⟨a, hc⟩
      have hterminalClass : q ∈ ExtensionBaseSupportClass ett v hvFinal v :=
        hqClass
      have hgammaLast : gamma0 (Fin.last p0) = gamma := by
        apply Option.some.inj
        exact (hgamma0 (Fin.last p0)).symm.trans (by
          rw [hqLast]
          exact hqGamma)
      have hdeltaLast : delta0 (Fin.last p0) = delta := by
        apply Option.some.inj
        exact (hdelta0 (Fin.last p0)).symm.trans (by
          rw [hqLast]
          exact hqDelta)
      let gammaFirst : Fin k := gamma0 0
      have hgammaSupport : gamma ∈ supportColors := by
        simp only [supportColors, Finset.mem_biUnion, Finset.mem_univ,
          true_and]
        refine ⟨Fin.last p0, ?_⟩
        rw [hstored0, hgammaLast]
        simp
      have hdeltaSupport : delta ∈ supportColors := by
        simp only [supportColors, Finset.mem_biUnion, Finset.mem_univ,
          true_and]
        refine ⟨Fin.last p0, ?_⟩
        rw [hstored0, hdeltaLast]
        simp
      have hgammaFirstSupport : gammaFirst ∈ supportColors := by
        simp only [supportColors, Finset.mem_biUnion, Finset.mem_univ,
          true_and]
        refine ⟨0, ?_⟩
        rw [hstored0]
        simp [gammaFirst]
      have hgammaDelta : gamma ≠ delta :=
        (ParallelStepRootComponentSetup ett.series q v gamma delta hqKind
          hqVertex hqGamma hqDelta).1
      let restorationColors :=
        (ExtensionBaseRestorationIndices ett v hvFinal).biUnion
          (fun s => ett.series.data.stored s.succ)
      have hterminalColorsNotRestored :
          gamma ∉ restorationColors ∧ delta ∉ restorationColors := by
        have hseparate : ∀ c : Fin k, c ∈ ({gamma, delta} : Finset (Fin k)) →
            c ∉ restorationColors := by
          intro c hcTerminal hcRestored
          obtain ⟨s, hsRestored, hcStored⟩ :=
            Finset.mem_biUnion.mp hcRestored
          have hsData := hsRestored
          simp only [ExtensionBaseRestorationIndices, Finset.mem_sdiff] at hsData
          have hsActiveData := hsData.1
          simp only [ExtensionBaseActiveIndices, Finset.mem_filter,
            Finset.mem_univ, true_and] at hsActiveData
          obtain ⟨hsFirst, hsKind, vs, hvsFinal, hsVertex, hsAppearance⟩ :=
            hsActiveData
          obtain ⟨vs', gammaS, deltaS, hsVertex', hsGamma, hsDelta⟩ :=
            hPESlotData s hsKind
          have hvsEq : vs' = vs :=
            Option.some.inj (hsVertex'.symm.trans hsVertex)
          subst vs'
          have hsStored : ett.series.data.stored s.succ =
              {gammaS, deltaS} :=
            hPEStored s gammaS deltaS hsKind hsGamma hsDelta
          have hsNeQ : s ≠ q := by
            intro hsq
            apply hsData.2
            simpa [hsq] using hqClass
          have hsq : s.val < q.val := by
            have hsle : s.val ≤ q.val := by omega
            exact lt_of_le_of_ne hsle (fun heq => hsNeQ (Fin.ext heq))
          have hoverlap := hpairOverlapColors s q vs v gammaS deltaS gamma delta
            hsData.1 hqActive hsq hsVertex hqVertex hsGamma hsDelta hqGamma
            hqDelta
          have hnonempty :
              (({gammaS, deltaS} : Finset (Fin k)) ∩ {gamma, delta}).Nonempty := by
            refine ⟨c, ?_⟩
            rw [← hsStored]
            exact Finset.mem_inter.mpr ⟨hcStored, hcTerminal⟩
          have hsameSupport : vs = v := (hoverlap.1.mp hnonempty).1
          apply hsData.2
          simp only [ExtensionBaseSupportClass, Finset.mem_filter]
          refine ⟨hsData.1, ?_⟩
          simpa [hsameSupport] using hsVertex
        exact ⟨hseparate gamma (by simp), hseparate delta (by simp)⟩
      have hsupportColors : ∀ (s : Fin ett.rounds)
          (gammaS deltaS : Fin k),
          s ∈ (ExtensionBaseSupportClass ett v hvFinal v).erase q →
          ett.series.data.gamma s.succ = some gammaS →
          ett.series.data.delta s.succ = some deltaS →
          gammaS ∈ supportColors ∧ deltaS ∈ supportColors := by
        intro s gammaS deltaS hs hsGamma hsDelta
        have hsClass := (Finset.mem_erase.mp hs).2
        have hsClassData := hsClass
        simp only [ExtensionBaseSupportClass, Finset.mem_filter] at hsClassData
        have hsActiveData := hsClassData.1
        simp only [ExtensionBaseActiveIndices, Finset.mem_filter,
          Finset.mem_univ, true_and] at hsActiveData
        have hsStored := hPEStored s gammaS deltaS hsActiveData.2.1
          hsGamma hsDelta
        rw [hsupportSet]
        constructor <;> apply Finset.mem_biUnion.mpr <;>
          refine ⟨s, hsClass, ?_⟩ <;> rw [hsStored] <;> simp
      have hdeltaEarlier : ∀ (s : Fin ett.rounds)
          (gammaS deltaS : Fin k),
          s ∈ (ExtensionBaseSupportClass ett v hvFinal v).erase q →
          ett.series.data.gamma s.succ = some gammaS →
          ett.series.data.delta s.succ = some deltaS →
          delta ≠ gammaS ∧ delta ≠ deltaS := by
        intro s gammaS deltaS hs hsGamma hsDelta
        have hsNeQ := (Finset.mem_erase.mp hs).1
        have hsClass := (Finset.mem_erase.mp hs).2
        obtain ⟨a, ha⟩ := (hclass0 s).1 hsClass
        have haNeLast : a ≠ Fin.last p0 := by
          intro haLast
          apply hsNeQ
          rw [← ha, haLast, hqLast]
        have hsq : s.val < q.val := by
          have haLt : a.val < (Fin.last p0).val :=
            Fin.lt_last_iff_ne_last.mpr haNeLast
          have hlt := hincreasing0 a (Fin.last p0) haLt
          simpa [ha, hqLast] using hlt
        have hsClassData := hsClass
        simp only [ExtensionBaseSupportClass, Finset.mem_filter] at hsClassData
        have hsGammaNe : delta ≠ gammaS :=
          (hdeltaExclusion.1 s q v v hvFinal hvFinal delta gammaS
            hsClassData.1 hqActive (Nat.le_of_lt hsq) hsClassData.2 hqVertex
            hqDelta hsGamma).2
        have hdeltaAEq : delta0 a = deltaS := by
          apply Option.some.inj
          exact (hdelta0 a).symm.trans (by simpa [ha] using hsDelta)
        have hsDeltaNe : delta ≠ deltaS := by
          intro hEq
          have hvalues :
              (Fin.cons (gamma0 0) delta0 : Fin (p0 + 2) → Fin k) a.succ =
                (Fin.cons (gamma0 0) delta0 : Fin (p0 + 2) → Fin k)
                  (Fin.last p0).succ := by
            simp [hdeltaAEq, hdeltaLast, hEq]
          have hindices := hinjective0 hvalues
          apply haNeLast
          apply Fin.ext
          have hvals := congrArg Fin.val hindices
          simpa using hvals
        exact ⟨hsGammaNe, hsDeltaNe⟩
      have hpreterminalPackage : 0 < p0 →
          ∃ preterminalSlot : Fin ett.rounds,
            preterminalSlot.val < q.val ∧
              preterminalSlot ∈
                (ExtensionBaseSupportClass ett v hvFinal v).erase q ∧
              ett.series.data.delta preterminalSlot.succ = some gamma := by
        intro hp0
        let a : Fin p0 := ⟨p0 - 1, by omega⟩
        let a0 : Fin (p0 + 1) := ⟨p0 - 1, by omega⟩
        have haCast : a.castSucc = a0 := by
          apply Fin.ext
          rfl
        have haSucc : a.succ = Fin.last p0 := by
          apply Fin.ext
          simp [a]
          omega
        have haLast : a0.val < (Fin.last p0).val := by
          simp [a0]
          omega
        have hslotOrder : (indices0 a0).val < q.val := by
          have h := hincreasing0 a0 (Fin.last p0) haLast
          simpa [hqLast] using h
        have hslotClass : indices0 a0 ∈
            ExtensionBaseSupportClass ett v hvFinal v :=
          (hclass0 (indices0 a0)).2 ⟨a0, rfl⟩
        have hslotNe : indices0 a0 ≠ q := by
          intro heq
          rw [heq] at hslotOrder
          exact (Nat.lt_irrefl _ hslotOrder)
        have hdeltaGamma : ett.series.data.delta (indices0 a0).succ =
            some gamma := by
          rw [hdelta0 a0]
          have hchain := hchain0 a
          rw [haCast, haSucc] at hchain
          rw [← hchain, hgammaLast]
        exact ⟨indices0 a0, hslotOrder,
          Finset.mem_erase.mpr ⟨hslotNe, hslotClass⟩, hdeltaGamma⟩
      have hb4Earlier : ∀ (s : Fin ett.rounds)
          (gammaS deltaS : Fin k),
          s ∈ (ExtensionBaseSupportClass ett v hvFinal v).erase q →
          ett.series.data.gamma s.succ = some gammaS →
          ett.series.data.delta s.succ = some deltaS →
          ETTStrongInterchangeable ett s v rho1 gammaS deltaS := by
        intro s gammaS deltaS hs hsGamma hsDelta
        have hsNe := (Finset.mem_erase.mp hs).1
        have hsClass := (Finset.mem_erase.mp hs).2
        have hsClassData := hsClass
        simp only [ExtensionBaseSupportClass, Finset.mem_filter] at hsClassData
        exact hb4Interchange s gammaS deltaS hsClass hsNe hsClassData.2
          hsGamma hsDelta
      have hsupportComponentOrder : ∀ (s : Fin ett.rounds)
          (gammaS deltaS : Fin k),
          s ∈ (ExtensionBaseSupportClass ett v hvFinal v).erase q →
          ett.series.data.gamma s.succ = some gammaS →
          ett.series.data.delta s.succ = some deltaS →
          ∀ x : V,
            x ∈ TreeSequenceVertexSet
                (ett.series.data.tree s.succ.castSucc) →
            x ≠ v →
            ∀ y : V, Sum.inl y ∈
              TwoColorComponent G rho1 gammaS deltaS (Sum.inl x) →
              y ∈ TreeSequenceVertexSet
                (ett.series.data.tree q.succ.castSucc) := by
        intro s gammaS deltaS hs hsGamma hsDelta x hx hxNe y hy
        have hsNeQ := (Finset.mem_erase.mp hs).1
        have hsClass := (Finset.mem_erase.mp hs).2
        obtain ⟨hneColors, hsKind, hsVertex, epsilon, hsEpsilon,
            hepsilonKind, hbetween, hcycles⟩ :=
          hb4Earlier s gammaS deltaS hs hsGamma hsDelta
        have hsq : s.val < q.val := by
          have hle : s.val ≤ q.val := by omega
          exact lt_of_le_of_ne hle (fun heq => hsNeQ (Fin.ext heq))
        have hepsilonQ : epsilon.val ≤ q.val := by
          by_contra hnot
          have hqRE := hbetween q hsq (by omega)
          rw [hqKind] at hqRE
          simp at hqRE
        have hyEpsilon := (hcycles x hx hxNe).2.2 y hy
        have hsegment := stageToStage (epsilon.val + 1) (q.val + 1)
          (by omega) (by omega) (by omega)
        have hyQ := vertexTransfer hsegment hyEpsilon
        convert hyQ using 1 <;> congr 1 <;> apply Fin.ext <;> rfl
      have hterminalInclusion : MissingColors G
            (ett.series.data.coloring jSlot.castSucc) v ⊆
          MissingColors G rho1 v ∪ {gammaFirst} := by
        intro c hc
        rw [hmissing0.2] at hc
        rcases Finset.mem_union.mp hc with hcSigma | hcFirst
        · apply Finset.mem_union_left
          rw [hb2Missing.2]
          exact (Finset.mem_sdiff.mp hcSigma).1
        · apply Finset.mem_union_right
          simpa [gammaFirst] using hcFirst
      have hb2EdgesFromSeed : ∀ a : Fin
          (ett.series.data.tree jSlot.succ.castSucc).length,
          seed.length ≤ a.val →
          rho1 ((ett.series.data.tree jSlot.succ.castSucc).edge a) =
            ett.series.data.coloring jSlot.castSucc
              ((ett.series.data.tree jSlot.succ.castSucc).edge a) := by
        intro a ha
        exact (hb2TreeEdges a).1.trans (hb2TreeEdges a).2
      have hdeltaPhiJ : delta ∉ TreeMissingColors
          (ett.series.data.coloring jSlot.castSucc)
          (ett.series.data.tree jSlot.succ.castSucc) := by
        simpa [hdeltaLast] using hdeltaAvoidsTj (Fin.last p0)
      have hterminalSeed : v ∈ TreeSequenceVertexSet seed := by
        simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ,
          true_and]
        exact ⟨Fin.last seed.length, hseedTerminal⟩
      have hseedN : TreeSequenceInitialSegment seed
          (ett.series.data.tree q.succ.castSucc) :=
        segmentTrans hseedTj hTjQ
      obtain ⟨fN, hfNEdges, hfNterminal, hphiNProper, hphiNOne⟩ :
          ∃ fN : E,
            ett.series.data.connectingEdges q.succ = {fN} ∧
              Incident G v fN ∧
              IsProperEdgeColoring G (ett.series.data.coloring q.succ) ∧
              IsOneEdgeUncolored (ett.series.data.coloring q.succ) e0 := by
        generalize htarget : q.succ = target
        cases ett.series.certified target with
        | initial => exact (Fin.succ_ne_zero q htarget).elim
        | SE i previousProper previousOneUncolored previousClosed
            previousNotStronglyClosed noRevisiting choice seriesAlternative
            currentColoring currentStored currentEdges currentKind currentVertex
            currentOutside currentDelta currentGamma adjoined adjoinedExactly
            closedExtension orderedExtension strictExtension =>
          have hbad : some TashkinovExtensionKind.SE =
              some TashkinovExtensionKind.PE :=
            currentKind.symm.trans (by simpa [htarget] using hqKind)
          cases hbad
        | RE i previousProper previousOneUncolored previousClosed
            previousNotStronglyClosed available currentColoring currentStored
            currentEdges currentKind currentVertex currentOutside currentDelta
            currentGamma adjoined adjoinedExactly closedExtension orderedExtension
            strictExtension =>
          have hbad : some TashkinovExtensionKind.RE =
              some TashkinovExtensionKind.PE :=
            currentKind.symm.trans (by simpa [htarget] using hqKind)
          cases hbad
        | PE i previousProper previousOneUncolored previousClosed
            previousNotStronglyClosed noRevisiting choice seriesAlternativeFails
            actualGamma gammaRule secondStable secondStableProper
            secondStableOneUncolored secondStableRelation exitWitness
            currentColoring currentProper currentOneUncolored currentStored
            currentEdges currentKind currentVertex currentOutside currentDelta
            currentGamma closedExtension orderedExtension strictExtension =>
          have hi : i = q := by
            apply Fin.ext
            simpa using (congrArg Fin.val htarget).symm
          subst i
          have hvChoice : choice.vertex = v :=
            Option.some.inj
              (currentVertex.symm.trans (by simpa [htarget] using hqVertex))
          refine ⟨choice.edge, ?_, ?_, ?_, ?_⟩
          · simpa [htarget] using currentEdges
          · simpa [hvChoice] using choice.edgeIncident
          · simpa [htarget] using currentProper
          · simpa [htarget] using currentOneUncolored
      have hboundaryStructure := HkuParallelBoundaryStructure G k ett.rounds
        e0 input ett.series q fN delta gamma v hqKind hfNEdges hqDelta
          hqGamma hqVertex
      have hgammaBoundary : BoundaryColorEdges G
          (ett.series.data.coloring q.succ)
          (TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc)) gamma =
            {fN} := hboundaryStructure.1
      have hdeltaLocation : ∀ f ∈ BoundaryColorEdges G
          (ett.series.data.coloring q.succ)
          (TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc)) delta,
          ∃ y ∈ TreeSequenceVertexSet seed, Incident G y f := by
        intro f hf
        obtain ⟨y, hyOrder, hyf⟩ := hboundaryStructure.2.1 f hf
        rcases hyOrder with ⟨iy, iv, hiy, hiv, hlt⟩
        let terminalN : Fin
            ((ett.series.data.tree q.succ.castSucc).length + 1) :=
          Fin.castLE (Nat.succ_le_succ hseedN.1) (Fin.last seed.length)
        have hterminalN :
            (ett.series.data.tree q.succ.castSucc).vertex terminalN = v := by
          exact (hseedN.2.1 (Fin.last seed.length)).trans hseedTerminal
        have hivTerminal : iv = terminalN := by
          apply (ett.series.data.tree q.succ.castSucc).vertex_injective
          exact hiv.trans hterminalN.symm
        have hiyBound : iy.val < seed.length + 1 := by
          rw [hivTerminal] at hlt
          have hiyStrict : iy.val < seed.length := by
            simpa [terminalN] using hlt
          omega
        let iySeed : Fin (seed.length + 1) := ⟨iy.val, hiyBound⟩
        have hcast : Fin.castLE (Nat.succ_le_succ hseedN.1) iySeed = iy := by
          apply Fin.ext
          rfl
        have hySeed : seed.vertex iySeed = y := by
          have hvertex := hseedN.2.1 iySeed
          rw [hcast] at hvertex
          exact hvertex.symm.trans hiy
        refine ⟨y, ?_, hyf⟩
        simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ,
          true_and]
        exact ⟨iySeed, hySeed⟩
      have hdeltaMissing : delta ∈ MissingColors G rho1 v := by
        have hmember : delta ∈ MissingColors G rho1 v ∩ supportColors := by
          rw [hterminalIntersection, hdeltaLast]
          simp
        exact (Finset.mem_inter.mp hmember).1
      have hterminalIntersection' :
          MissingColors G rho1 v ∩ supportColors = {delta} := by
        simpa [hdeltaLast] using hterminalIntersection
      obtain ⟨hprimeMissingColors, hprimeAppendedEdges⟩ :=
        ExtensionBaseCaseTwoObservation19 rho1 seed TjPrime v supportColors
          delta hclosure hterminalPrime hcaseTwoPointwise
            hterminalIntersection'
      let controlled : Finset (Fin k) :=
        TreeMissingColors (ett.series.data.coloring q.succ)
            (ett.series.data.tree q.succ.castSucc) ∪
          TashkinovStoredColors ett.series.data q.succ
      have hterminalRawStored : ett.series.data.stored q.succ =
          {gamma, delta} :=
        hPEStored q gamma delta hqKind hqGamma hqDelta
      have hterminalColorControlled : ∀ c : Fin k,
          c ∈ ({gamma, delta} : Finset (Fin k)) → c ∈ controlled := by
        intro c hc
        by_cases hcMissing : c ∈ TreeMissingColors
            (ett.series.data.coloring q.succ)
            (ett.series.data.tree q.succ.castSucc)
        · exact Finset.mem_union_left _ hcMissing
        · apply Finset.mem_union_right
          unfold TashkinovStoredColors
          have hqSuccNe : q.succ.val ≠ 0 := Nat.succ_ne_zero q.val
          rw [if_neg hqSuccNe]
          apply Finset.mem_sdiff.mpr
          refine ⟨?_, hcMissing⟩
          apply Finset.mem_biUnion.mpr
          refine ⟨q.succ, Finset.mem_univ _, ?_⟩
          rw [if_pos le_rfl, hterminalRawStored]
          exact hc
      have hgammaControlled : gamma ∈ controlled :=
        hterminalColorControlled gamma (by simp)
      have hdeltaControlled : delta ∈ controlled :=
        hterminalColorControlled delta (by simp)
      have hsigmaControlled : StableColoring
          (ett.series.data.tree q.succ.castSucc) controlled
          (ett.series.data.coloring q.succ) sigma := by
        constructor
        · intro f hfIncident hfControl
          apply hsigmaTerminal.1 f hfIncident
          obtain ⟨c, hc, hfc⟩ := hfControl
          refine ⟨c, ?_, hfc⟩
          rcases Finset.mem_union.mp hc with hcMissing | hcControlled
          · exact Finset.mem_union_left _ hcMissing
          · change c ∈ TreeMissingColors
                (ett.series.data.coloring q.succ)
                (ett.series.data.tree q.succ.castSucc) ∪
              TashkinovStoredColors ett.series.data q.succ at hcControlled
            exact hcControlled
        · exact hsigmaTerminal.2
      obtain ⟨hgammaBoundaryRho, hdeltaBoundaryRho⟩ :=
        ExtensionBaseCaseTwoObservation20
          (ett.series.data.tree q.succ.castSucc) seed TjPrime
          (ett.series.data.coloring q.succ) sigma rho1 controlled
          restorationColors gamma delta fN v hphiNProper hphiNOne hsigmaProper
          hsigmaOne hrho1Proper hrho1One hsigmaControlled hgammaControlled
          hdeltaControlled (fun f hf => (hb3EdgeEffects f hf).2)
          hterminalColorsNotRestored.1 hterminalColorsNotRestored.2
          hgammaBoundary hdeltaLocation hseedN hseedTerminal hclosure
          hterminalSeed hdeltaMissing
      have hterminalEdgeValues : ∀ f : E,
          (sigma f = some gamma ∨ sigma f = some delta) ↔
            (rho1 f = some gamma ∨ rho1 f = some delta) := by
        intro f
        constructor
        · intro hf
          by_cases heq : rho1 f = sigma f
          · simpa [heq] using hf
          · obtain ⟨c, d, hsc, hrd, hcRestored, hdRestored⟩ :=
              (hb3EdgeEffects f heq).2
            rcases hf with hfgamma | hfdelta
            · have hc : c = gamma := Option.some.inj (hsc.symm.trans hfgamma)
              exact False.elim (hterminalColorsNotRestored.1 (hc ▸ hcRestored))
            · have hc : c = delta := Option.some.inj (hsc.symm.trans hfdelta)
              exact False.elim (hterminalColorsNotRestored.2 (hc ▸ hcRestored))
        · intro hf
          by_cases heq : rho1 f = sigma f
          · simpa [heq] using hf
          · obtain ⟨c, d, hsc, hrd, hcRestored, hdRestored⟩ :=
              (hb3EdgeEffects f heq).2
            rcases hf with hfgamma | hfdelta
            · have hd : d = gamma := Option.some.inj (hrd.symm.trans hfgamma)
              exact False.elim (hterminalColorsNotRestored.1 (hd ▸ hdRestored))
            · have hd : d = delta := Option.some.inj (hrd.symm.trans hfdelta)
              exact False.elim (hterminalColorsNotRestored.2 (hd ▸ hdRestored))
      have hterminalGraph :
          TwoColorIncidenceGraph G sigma gamma delta =
            TwoColorIncidenceGraph G rho1 gamma delta := by
        apply SimpleGraph.ext
        funext a b
        cases a <;> cases b <;>
          simp [TwoColorIncidenceGraph, hterminalEdgeValues]
      have hwComponentRho : Sum.inl w ∈
          TwoColorComponent G rho1 gamma delta (Sum.inl v) := by
        unfold TwoColorComponent
        rw [← hterminalGraph]
        exact hwComponent
      let H := TwoColorIncidenceGraph G rho1 gamma delta
      let C := TwoColorComponent G rho1 gamma delta (Sum.inl v)
      have hfNBoundaryRho : fN ∈ BoundaryColorEdges G rho1
          (TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc))
          gamma := by
        rw [hgammaBoundaryRho]
        simp
      have hfNColorRho : rho1 fN = some gamma :=
        (Finset.mem_filter.mp hfNBoundaryRho).2
      have hfNAdj : H.Adj (Sum.inl v) (Sum.inr fN) := by
        simpa [H, TwoColorIncidenceGraph] using
          (show Incident G v fN ∧
              (rho1 fN = some gamma ∨ rho1 fN = some delta) from
            ⟨hfNterminal, Or.inl hfNColorRho⟩)
      have hvDegree : @SimpleGraph.degree _ H (Sum.inl v)
          (Fintype.ofFinite _) ≤ 1 := by
        have hdegree := MissingColorIncidenceEndpoint G rho1 delta gamma
          hgammaDelta.symm hrho1Proper v hdeltaMissing
        have hcolorOrder :
            TwoColorIncidenceGraph G rho1 delta gamma = H := by
          apply SimpleGraph.ext
          funext a b
          cases a <;> cases b <;>
            simp [H, TwoColorIncidenceGraph, or_comm]
        rw [hcolorOrder] at hdegree
        exact hdegree
      have hvSub : Set.Subsingleton (H.neighborSet (Sum.inl v)) := by
        letI : Fintype (H.neighborSet (Sum.inl v)) := Fintype.ofFinite _
        have hcard : (H.neighborFinset (Sum.inl v)).card ≤ 1 := by
          rw [SimpleGraph.card_neighborFinset_eq_degree]
          exact hvDegree
        intro a ha b hb
        exact (Finset.card_le_one.mp hcard) a
          (by simpa [SimpleGraph.mem_neighborFinset] using ha) b
          (by simpa [SimpleGraph.mem_neighborFinset] using hb)
      obtain ⟨a, b, spanningPath, hspanningPath, hspanningSupport⟩ :=
        TwoColorComponentSpanningPath G rho1 gamma delta hrho1Proper
          (Sum.inl v)
      have hvC : Sum.inl v ∈ C := by
        change Sum.inl v ∈ H.connectedComponentMk (Sum.inl v)
        exact (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mpr rfl
      have hvSpanning : Sum.inl v ∈ spanningPath.support := by
        change Sum.inl v ∈ {z | z ∈ spanningPath.support}
        rw [hspanningSupport]
        exact hvC
      have hvEndpoint : (Sum.inl v : Sum V E) = a ∨ Sum.inl v = b := by
        by_contra hn
        push_neg at hn
        exact (hspanningPath.isTrail.not_mem_support_of_subsingleton_neighborSet
          hn.1 hn.2 hvSub) hvSpanning
      obtain ⟨endpoint, componentPath, hcomponentPath, hcomponentSupport⟩ :
          ∃ endpoint,
            ∃ componentPath : H.Walk (Sum.inl v) endpoint,
              componentPath.IsPath ∧
                {z | z ∈ componentPath.support} = C := by
        rcases hvEndpoint with hva | hvb
        · subst a
          exact ⟨b, spanningPath, hspanningPath, hspanningSupport⟩
        · subst b
          refine ⟨a, spanningPath.reverse, hspanningPath.reverse, ?_⟩
          ext z
          rw [SimpleGraph.Walk.support_reverse]
          simpa using Set.ext_iff.mp hspanningSupport z
      have hfNComponent : Sum.inr fN ∈ C := by
        change H.connectedComponentMk (Sum.inr fN) =
          H.connectedComponentMk (Sum.inl v)
        exact
          (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
            hfNAdj).symm
      have hcomponentNonempty : ¬ componentPath.Nil := by
        intro hnil
        have hfNSupport : Sum.inr fN ∈ componentPath.support := by
          change Sum.inr fN ∈ {z | z ∈ componentPath.support}
          rw [hcomponentSupport]
          exact hfNComponent
        cases hnil
        simp at hfNSupport
      have hcomponentPositive : 0 < componentPath.length :=
        SimpleGraph.Walk.not_nil_iff_lt_length.mp hcomponentNonempty
      have hendpointC : endpoint ∈ C := by
        rw [← hcomponentSupport]
        change endpoint ∈ componentPath.support
        simpa only [componentPath.getVert_length] using
          componentPath.getVert_mem_support componentPath.length
      have hendpointNeighbor : ∀ z, H.Adj endpoint z →
          z = componentPath.getVert (componentPath.length - 1) := by
        intro z hez
        have hzC : z ∈ C := by
          change H.connectedComponentMk z = H.connectedComponentMk (Sum.inl v)
          change H.connectedComponentMk endpoint =
            H.connectedComponentMk (Sum.inl v) at hendpointC
          exact
            (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
              hez).symm.trans hendpointC
        have hzSupport : z ∈ componentPath.support := by
          change z ∈ {y | y ∈ componentPath.support}
          rw [hcomponentSupport]
          exact hzC
        obtain ⟨n, hn, hnle⟩ :=
          SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hzSupport
        have hnlt : n < componentPath.length := by
          have hnne : n ≠ componentPath.length := by
            intro heq
            have hze : z = endpoint := by
              rw [← hn, heq, componentPath.getVert_length]
            exact hez.ne hze.symm
          omega
        by_cases hpen : n + 1 = componentPath.length
        · rw [← hn]
          congr 1
          omega
        by_cases hn0 : n = 0
        · have hnext : H.Adj (Sum.inl v) (componentPath.getVert 1) := by
            simpa [hn0, componentPath.getVert_zero] using
              componentPath.adj_getVert_succ hnlt
          have hendStart : H.Adj (Sum.inl v) endpoint := by
            rw [← hn, hn0, componentPath.getVert_zero] at hez
            exact hez.symm
          have hnextNe : componentPath.getVert 1 ≠ endpoint := by
            intro heq
            have hindices := hcomponentPath.getVert_injOn
              (show 1 ≤ componentPath.length by omega)
              (show componentPath.length ≤ componentPath.length by rfl)
              (heq.trans componentPath.getVert_length.symm)
            omega
          exact False.elim (hnextNe (hvSub hnext hendStart))
        · have hleft : H.Adj z (componentPath.getVert (n - 1)) := by
            rw [← hn]
            have hadj := componentPath.adj_getVert_succ (i := n - 1) (by omega)
            simpa only [Nat.sub_add_cancel (by omega : 1 ≤ n)] using hadj.symm
          have hright : H.Adj z (componentPath.getVert (n + 1)) := by
            rw [← hn]
            exact componentPath.adj_getVert_succ hnlt
          have hendNeLeft : endpoint ≠ componentPath.getVert (n - 1) := by
            intro heq
            have hindices := hcomponentPath.getVert_injOn
              (show componentPath.length ≤ componentPath.length by rfl)
              (show n - 1 ≤ componentPath.length by omega)
              (componentPath.getVert_length.trans heq)
            omega
          have hendNeRight : endpoint ≠ componentPath.getVert (n + 1) := by
            intro heq
            have hindices := hcomponentPath.getVert_injOn
              (show componentPath.length ≤ componentPath.length by rfl)
              (show n + 1 ≤ componentPath.length by omega)
              (componentPath.getVert_length.trans heq)
            omega
          have hlrNe : componentPath.getVert (n - 1) ≠
              componentPath.getVert (n + 1) := by
            intro heq
            have hindices := hcomponentPath.getVert_injOn
              (show n - 1 ≤ componentPath.length by omega)
              (show n + 1 ≤ componentPath.length by omega) heq
            omega
          letI : Fintype (H.neighborSet z) := Fintype.ofFinite _
          have hthree : 3 ≤ @SimpleGraph.degree _ H z (Fintype.ofFinite _) := by
            rw [← SimpleGraph.card_neighborFinset_eq_degree]
            let neighbors : Finset (Sum V E) :=
              {endpoint, componentPath.getVert (n - 1),
                componentPath.getVert (n + 1)}
            have hsubset : neighbors ⊆ H.neighborFinset z := by
              intro y hy
              simp only [neighbors, Finset.mem_insert, Finset.mem_singleton] at hy
              rcases hy with rfl | rfl | rfl
              · simpa [SimpleGraph.mem_neighborFinset] using hez.symm
              · simpa [SimpleGraph.mem_neighborFinset] using hleft
              · simpa [SimpleGraph.mem_neighborFinset] using hright
            have hcard : 3 ≤ neighbors.card := by
              simp [neighbors, hendNeLeft, hendNeRight, hlrNe]
            exact hcard.trans (Finset.card_le_card hsubset)
          have htwo : @SimpleGraph.degree _ H z (Fintype.ofFinite _) ≤ 2 := by
            change @SimpleGraph.degree _
              (TwoColorIncidenceGraph G rho1 gamma delta) z
                (Fintype.ofFinite _) ≤ 2
            exact TwoColorIncidenceDegreeAtMostTwo G rho1 gamma delta
              hrho1Proper z
          omega
      have hendpointVertex : ∃ x : V, endpoint = Sum.inl x := by
        cases hendpoint : endpoint with
        | inl x => exact ⟨x, rfl⟩
        | inr f =>
            have hlastAdj : H.Adj
                (componentPath.getVert (componentPath.length - 1)) endpoint := by
              simpa only [Nat.sub_add_cancel (by omega : 1 ≤ componentPath.length),
                componentPath.getVert_length] using
                componentPath.adj_getVert_succ
                  (i := componentPath.length - 1) (by omega)
            have hfColor : rho1 f = some gamma ∨ rho1 f = some delta := by
              cases hprevious : componentPath.getVert
                  (componentPath.length - 1) with
              | inl y =>
                  rw [hprevious, hendpoint] at hlastAdj
                  simpa [H, TwoColorIncidenceGraph] using hlastAdj |>.2
              | inr g =>
                  rw [hprevious, hendpoint] at hlastAdj
                  simp [H, TwoColorIncidenceGraph] at hlastAdj
            induction hends : G.ends f using Sym2.inductionOn with
            | _ y z =>
                have hyz : y ≠ z := by
                  intro hyz
                  subst z
                  exact G.loopless f y hends
                have hyAdj : H.Adj endpoint (Sum.inl y) := by
                  rw [hendpoint]
                  simpa [H, TwoColorIncidenceGraph, Incident, hends] using
                    (show Incident G y f ∧
                        (rho1 f = some gamma ∨ rho1 f = some delta) from
                      ⟨by simp [Incident, hends], hfColor⟩)
                have hzAdj : H.Adj endpoint (Sum.inl z) := by
                  rw [hendpoint]
                  simpa [H, TwoColorIncidenceGraph, Incident, hends] using
                    (show Incident G z f ∧
                        (rho1 f = some gamma ∨ rho1 f = some delta) from
                      ⟨by simp [Incident, hends], hfColor⟩)
                have heq := (hendpointNeighbor _ hyAdj).trans
                  (hendpointNeighbor _ hzAdj).symm
                exact False.elim (hyz (Sum.inl.inj heq))
      obtain ⟨x, hendpoint⟩ := hendpointVertex
      subst endpoint
      have hxNe : x ≠ v := by
        intro hxv
        subst x
        have hnil : componentPath.Nil :=
          hcomponentPath.nil_iff_eq.mpr rfl
        exact hcomponentNonempty hnil
      have swapBothPresent (phi : PartialEdgeColoring E k)
          (alpha beta : Fin k) (hne : alpha ≠ beta) (root : Sum V E)
          (y : V) (halpha : alpha ∈ PresentColors G phi y)
          (hbeta : beta ∈ PresentColors G phi y) :
          alpha ∈ PresentColors G
              (TwoColorComponentSwap G phi alpha beta root) y ∧
            beta ∈ PresentColors G
              (TwoColorComponentSwap G phi alpha beta root) y := by
        obtain ⟨eAlpha, heAlphaIncident, heAlphaColor⟩ := by
          simpa only [PresentColors, Finset.mem_filter, Finset.mem_univ,
            true_and] using halpha
        obtain ⟨eBeta, heBetaIncident, heBetaColor⟩ := by
          simpa only [PresentColors, Finset.mem_filter, Finset.mem_univ,
            true_and] using hbeta
        let K := TwoColorComponent G phi alpha beta root
        have hedgeSameComponent : Sum.inr eAlpha ∈ K ↔ Sum.inr eBeta ∈ K := by
          let J := TwoColorIncidenceGraph G phi alpha beta
          have hAlphaAdj : J.Adj (Sum.inl y) (Sum.inr eAlpha) := by
            simpa [J, TwoColorIncidenceGraph] using
              (show Incident G y eAlpha ∧
                  (phi eAlpha = some alpha ∨ phi eAlpha = some beta) from
                ⟨heAlphaIncident, Or.inl heAlphaColor⟩)
          have hBetaAdj : J.Adj (Sum.inl y) (Sum.inr eBeta) := by
            simpa [J, TwoColorIncidenceGraph] using
              (show Incident G y eBeta ∧
                  (phi eBeta = some alpha ∨ phi eBeta = some beta) from
                ⟨heBetaIncident, Or.inr heBetaColor⟩)
          constructor
          · intro hAlpha
            change J.connectedComponentMk (Sum.inr eBeta) =
              J.connectedComponentMk root
            change J.connectedComponentMk (Sum.inr eAlpha) =
              J.connectedComponentMk root at hAlpha
            exact
              (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
                hBetaAdj).symm.trans
              ((SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
                hAlphaAdj).trans hAlpha)
          · intro hBeta
            change J.connectedComponentMk (Sum.inr eAlpha) =
              J.connectedComponentMk root
            change J.connectedComponentMk (Sum.inr eBeta) =
              J.connectedComponentMk root at hBeta
            exact
              (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
                hAlphaAdj).symm.trans
              ((SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
                hBetaAdj).trans hBeta)
        by_cases hAlphaK : Sum.inr eAlpha ∈ K
        · have hBetaK : Sum.inr eBeta ∈ K := hedgeSameComponent.mp hAlphaK
          constructor
          · simp only [PresentColors, Finset.mem_filter, Finset.mem_univ,
              true_and]
            refine ⟨eBeta, heBetaIncident, ?_⟩
            simp [TwoColorComponentSwap, K, hBetaK, heBetaColor, hne]
          · simp only [PresentColors, Finset.mem_filter, Finset.mem_univ,
              true_and]
            refine ⟨eAlpha, heAlphaIncident, ?_⟩
            simp [TwoColorComponentSwap, K, hAlphaK, heAlphaColor]
        · have hBetaK : Sum.inr eBeta ∉ K := by
            intro h
            exact hAlphaK (hedgeSameComponent.mpr h)
          constructor
          · simp only [PresentColors, Finset.mem_filter, Finset.mem_univ,
              true_and]
            exact ⟨eAlpha, heAlphaIncident, by
              simpa [TwoColorComponentSwap, K, hAlphaK] using heAlphaColor⟩
          · simp only [PresentColors, Finset.mem_filter, Finset.mem_univ,
              true_and]
            exact ⟨eBeta, heBetaIncident, by
              simpa [TwoColorComponentSwap, K, hBetaK] using heBetaColor⟩
      have hTnElementary : ColoredVertexSetElementary G
          (ett.series.data.coloring q.castSucc)
          (TreeSequenceVertexSet
            (ett.series.data.tree q.succ.castSucc)) := by
        by_cases hqPositive : 0 < q.val
        · obtain ⟨lower, hround, hlowerMP, htrees, hdata⟩ :=
            CertifiedETTRestriction G k e0 input T generating ett hMP
              q.val hqPositive q.isLt
          exact (hlower lower (by omega) (by omega) hlowerMP).1
        · have hqZero : q.val = 0 := by omega
          have hbase : ColoredVertexSetElementary G
              (ett.series.data.coloring 0)
              (TreeSequenceVertexSet
                (ett.series.data.tree ⟨1, by omega⟩)) :=
            (TechnicalTheoremBase G k ett.rounds e0 input ett.series).1
          have hcolor : q.castSucc = (0 : Fin (ett.rounds + 1)) := by
            apply Fin.ext
            exact hqZero
          have htree : q.succ.castSucc =
              (⟨1, by omega⟩ : Fin (ett.rounds + 2)) := by
            apply Fin.ext
            simp [hqZero]
          simpa [hcolor, htree] using hbase
      have hgammaMissingPre : gamma ∈ MissingColors G
          (ett.series.data.coloring q.castSucc) v := by
        generalize htarget : q.succ = target
        cases ett.series.certified target with
        | initial => exact (Fin.succ_ne_zero q htarget).elim
        | SE i previousProper previousOneUncolored previousClosed
            previousNotStronglyClosed noRevisiting choice seriesAlternative
            currentColoring currentStored currentEdges currentKind currentVertex
            currentOutside currentDelta currentGamma adjoined adjoinedExactly
            closedExtension orderedExtension strictExtension =>
          have hbad : some TashkinovExtensionKind.SE =
              some TashkinovExtensionKind.PE :=
            currentKind.symm.trans (by simpa [htarget] using hqKind)
          cases hbad
        | RE i previousProper previousOneUncolored previousClosed
            previousNotStronglyClosed available currentColoring currentStored
            currentEdges currentKind currentVertex currentOutside currentDelta
            currentGamma adjoined adjoinedExactly closedExtension orderedExtension
            strictExtension =>
          have hbad : some TashkinovExtensionKind.RE =
              some TashkinovExtensionKind.PE :=
            currentKind.symm.trans (by simpa [htarget] using hqKind)
          cases hbad
        | PE i previousProper previousOneUncolored previousClosed
            previousNotStronglyClosed noRevisiting choice seriesAlternativeFails
            actualGamma gammaRule secondStable secondStableProper
            secondStableOneUncolored secondStableRelation exitWitness
            currentColoring currentProper currentOneUncolored currentStored
            currentEdges currentKind currentVertex currentOutside currentDelta
            currentGamma closedExtension orderedExtension strictExtension =>
          have hi : i = q := by
            apply Fin.ext
            simpa using (congrArg Fin.val htarget).symm
          subst i
          have hvChoice : choice.vertex = v :=
            Option.some.inj
              (currentVertex.symm.trans (by simpa [htarget] using hqVertex))
          have hgammaChoice : actualGamma = gamma :=
            Option.some.inj
              (currentGamma.symm.trans (by simpa [htarget] using hqGamma))
          have hmissingSelected : actualGamma ∈ MissingColors G
              choice.selected choice.vertex := gammaRule.1
          rw [choice.selectedStable.2 choice.vertex
            choice.vertexDefective.1] at hmissingSelected
          simpa only [hgammaChoice, hvChoice] using hmissingSelected
      have hdeltaNotMissingPre : delta ∉ TreeMissingColors
          (ett.series.data.coloring q.castSucc)
          (ett.series.data.tree q.succ.castSucc) :=
        (hdeltaExclusion.1 q q v v hvFinal hvFinal delta gamma hqActive
          hqActive le_rfl hqVertex hqVertex hqDelta hqGamma).1
      have hterminalPresentSigma : ∀ y : V,
          y ∈ TreeSequenceVertexSet
              (ett.series.data.tree q.succ.castSucc) →
          y ≠ v →
          gamma ∈ PresentColors G sigma y ∧
            delta ∈ PresentColors G sigma y := by
        intro y hy hyv
        have hgammaNotMissingPre : gamma ∉ MissingColors G
            (ett.series.data.coloring q.castSucc) y := by
          intro hgammaY
          have hdisjoint := hTnElementary hvStage hy hyv.symm
          exact (Finset.disjoint_left.mp hdisjoint) hgammaMissingPre hgammaY
        have hdeltaNotMissingPreY : delta ∉ MissingColors G
            (ett.series.data.coloring q.castSucc) y := by
          intro hdeltaY
          apply hdeltaNotMissingPre
          unfold TreeMissingColors
          exact Finset.mem_biUnion.mpr ⟨y, hy, hdeltaY⟩
        generalize htarget : q.succ = target
        cases ett.series.certified target with
        | initial => exact (Fin.succ_ne_zero q htarget).elim
        | SE i previousProper previousOneUncolored previousClosed
            previousNotStronglyClosed noRevisiting choice seriesAlternative
            currentColoring currentStored currentEdges currentKind currentVertex
            currentOutside currentDelta currentGamma adjoined adjoinedExactly
            closedExtension orderedExtension strictExtension =>
          have hbad : some TashkinovExtensionKind.SE =
              some TashkinovExtensionKind.PE :=
            currentKind.symm.trans (by simpa [htarget] using hqKind)
          cases hbad
        | RE i previousProper previousOneUncolored previousClosed
            previousNotStronglyClosed available currentColoring currentStored
            currentEdges currentKind currentVertex currentOutside currentDelta
            currentGamma adjoined adjoinedExactly closedExtension orderedExtension
            strictExtension =>
          have hbad : some TashkinovExtensionKind.RE =
              some TashkinovExtensionKind.PE :=
            currentKind.symm.trans (by simpa [htarget] using hqKind)
          cases hbad
        | PE i previousProper previousOneUncolored previousClosed
            previousNotStronglyClosed noRevisiting choice seriesAlternativeFails
            actualGamma gammaRule secondStable secondStableProper
            secondStableOneUncolored secondStableRelation exitWitness
            currentColoring currentProper currentOneUncolored currentStored
            currentEdges currentKind currentVertex currentOutside currentDelta
            currentGamma closedExtension orderedExtension strictExtension =>
          have hi : i = q := by
            apply Fin.ext
            simpa using (congrArg Fin.val htarget).symm
          subst i
          have hvChoice : choice.vertex = v :=
            Option.some.inj
              (currentVertex.symm.trans (by simpa [htarget] using hqVertex))
          have hgammaChoice : actualGamma = gamma :=
            Option.some.inj
              (currentGamma.symm.trans (by simpa [htarget] using hqGamma))
          have hdeltaChoice : choice.color = delta :=
            Option.some.inj
              (currentDelta.symm.trans (by simpa [htarget] using hqDelta))
          have hgammaSecondNot : actualGamma ∉
              MissingColors G secondStable y := by
            rw [secondStableRelation.2 y hy, choice.selectedStable.2 y hy]
            simpa only [hgammaChoice] using hgammaNotMissingPre
          have hdeltaSecondNot : choice.color ∉
              MissingColors G secondStable y := by
            rw [secondStableRelation.2 y hy, choice.selectedStable.2 y hy]
            simpa only [hdeltaChoice] using hdeltaNotMissingPreY
          have hgammaSecond : actualGamma ∈
              PresentColors G secondStable y := by
            simpa [MissingColors] using hgammaSecondNot
          have hdeltaSecond : choice.color ∈
              PresentColors G secondStable y := by
            simpa [MissingColors] using hdeltaSecondNot
          have hchoiceNe : actualGamma ≠ choice.color := by
            simpa only [hgammaChoice, hdeltaChoice] using hgammaDelta
          have hcurrentPresent := swapBothPresent secondStable actualGamma
            choice.color hchoiceNe (Sum.inl choice.vertex) y hgammaSecond
              hdeltaSecond
          have hgammaCurrent : actualGamma ∈ PresentColors G
              (ett.series.data.coloring q.succ) y := by
            rw [currentColoring]
            exact hcurrentPresent.1
          have hdeltaCurrent : choice.color ∈ PresentColors G
              (ett.series.data.coloring q.succ) y := by
            rw [currentColoring]
            exact hcurrentPresent.2
          have hgammaSigmaNot : actualGamma ∉ MissingColors G sigma y := by
            rw [hsigmaTerminal.2 y hy]
            simpa [MissingColors] using hgammaCurrent
          have hdeltaSigmaNot : choice.color ∉ MissingColors G sigma y := by
            rw [hsigmaTerminal.2 y hy]
            simpa [MissingColors] using hdeltaCurrent
          exact ⟨by
              simpa [hgammaChoice, MissingColors] using hgammaSigmaNot,
            by simpa [hdeltaChoice, MissingColors] using hdeltaSigmaNot⟩
      have hxOutsideN : x ∉ TreeSequenceVertexSet
          (ett.series.data.tree q.succ.castSucc) := by
        intro hxN
        obtain ⟨hxGamma, hxDelta⟩ := hterminalPresentSigma x hxN hxNe
        obtain ⟨eGamma, heGammaIncident, heGammaColor⟩ := by
          simpa only [PresentColors, Finset.mem_filter, Finset.mem_univ,
            true_and] using hxGamma
        obtain ⟨eDelta, heDeltaIncident, heDeltaColor⟩ := by
          simpa only [PresentColors, Finset.mem_filter, Finset.mem_univ,
            true_and] using hxDelta
        have hedgeNe : eGamma ≠ eDelta := by
          intro heq
          subst eDelta
          exact hgammaDelta
            (Option.some.inj (heGammaColor.symm.trans heDeltaColor))
        have hgammaAdjSigma :
            (TwoColorIncidenceGraph G sigma gamma delta).Adj
              (Sum.inl x) (Sum.inr eGamma) := by
          simpa [TwoColorIncidenceGraph] using
            (show Incident G x eGamma ∧
                (sigma eGamma = some gamma ∨ sigma eGamma = some delta) from
              ⟨heGammaIncident, Or.inl heGammaColor⟩)
        have hdeltaAdjSigma :
            (TwoColorIncidenceGraph G sigma gamma delta).Adj
              (Sum.inl x) (Sum.inr eDelta) := by
          simpa [TwoColorIncidenceGraph] using
            (show Incident G x eDelta ∧
                (sigma eDelta = some gamma ∨ sigma eDelta = some delta) from
              ⟨heDeltaIncident, Or.inr heDeltaColor⟩)
        rw [hterminalGraph] at hgammaAdjSigma hdeltaAdjSigma
        have heq := (hendpointNeighbor _ hgammaAdjSigma).trans
          (hendpointNeighbor _ hdeltaAdjSigma).symm
        exact hedgeNe (Sum.inr.inj heq)
      have hxOutsidePrime : x ∉ TreeSequenceVertexSet TjPrime := by
        intro hxPrime
        have hxErase : x ∈ (TreeSequenceVertexSet TjPrime).erase v :=
          Finset.mem_erase.mpr ⟨hxNe, hxPrime⟩
        have hxEmpty := hcaseTwoPointwise x hxErase
        have hgammaNotMissing : gamma ∉ MissingColors G rho1 x := by
          intro hgammaMissing
          have hmember : gamma ∈ MissingColors G rho1 x ∩ supportColors :=
            Finset.mem_inter.mpr ⟨hgammaMissing, hgammaSupport⟩
          rw [hxEmpty] at hmember
          simpa using hmember
        have hdeltaNotMissing : delta ∉ MissingColors G rho1 x := by
          intro hdeltaMissingX
          have hmember : delta ∈ MissingColors G rho1 x ∩ supportColors :=
            Finset.mem_inter.mpr ⟨hdeltaMissingX, hdeltaSupport⟩
          rw [hxEmpty] at hmember
          simpa using hmember
        have hxGamma : gamma ∈ PresentColors G rho1 x := by
          simpa [MissingColors] using hgammaNotMissing
        have hxDelta : delta ∈ PresentColors G rho1 x := by
          simpa [MissingColors] using hdeltaNotMissing
        obtain ⟨eGamma, heGammaIncident, heGammaColor⟩ := by
          simpa only [PresentColors, Finset.mem_filter, Finset.mem_univ,
            true_and] using hxGamma
        obtain ⟨eDelta, heDeltaIncident, heDeltaColor⟩ := by
          simpa only [PresentColors, Finset.mem_filter, Finset.mem_univ,
            true_and] using hxDelta
        have hedgeNe : eGamma ≠ eDelta := by
          intro heq
          subst eDelta
          exact hgammaDelta
            (Option.some.inj (heGammaColor.symm.trans heDeltaColor))
        have hgammaAdj : H.Adj (Sum.inl x) (Sum.inr eGamma) := by
          simpa [H, TwoColorIncidenceGraph] using
            (show Incident G x eGamma ∧
                (rho1 eGamma = some gamma ∨ rho1 eGamma = some delta) from
              ⟨heGammaIncident, Or.inl heGammaColor⟩)
        have hdeltaAdj : H.Adj (Sum.inl x) (Sum.inr eDelta) := by
          simpa [H, TwoColorIncidenceGraph] using
            (show Incident G x eDelta ∧
                (rho1 eDelta = some gamma ∨ rho1 eDelta = some delta) from
              ⟨heDeltaIncident, Or.inr heDeltaColor⟩)
        have heq := (hendpointNeighbor _ hgammaAdj).trans
          (hendpointNeighbor _ hdeltaAdj).symm
        exact hedgeNe (Sum.inr.inj heq)
      have hxOutside : x ∉
          TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc) ∪
            TreeSequenceVertexSet TjPrime := by
        intro hx
        rcases Finset.mem_union.mp hx with hx | hx
        · exact hxOutsideN hx
        · exact hxOutsidePrime hx
      have hwPath : Sum.inl w ∈ componentPath.support := by
        change Sum.inl w ∈ {z | z ∈ componentPath.support}
        rw [hcomponentSupport]
        exact hwComponentRho
      have hwStage : w ∈ TreeSequenceVertexSet
          (ett.series.data.tree q.succ.castSucc) := by
        rw [hqSucc]
        exact hw
      have htwoN : ∃ y ∈ TreeSequenceVertexSet
          (ett.series.data.tree q.succ.castSucc),
          y ≠ v ∧ Sum.inl y ∈ componentPath.support :=
        ⟨w, hwStage, hwNe, hwPath⟩
      obtain ⟨u, exitPath, huDiff, hexitPath, hexitLength,
          hexitSupport, hexitIntersection, hexitBoundary, huNotFN⟩ :=
        ExtensionBaseCaseTwoObservation21
          (ett.series.data.tree q.succ.castSucc) TjPrime rho1 gamma delta
          fN v x componentPath hcomponentPath (by simpa [C] using
            hcomponentSupport) hvStage hterminalPrime hxOutside htwoN
          hgammaBoundaryRho hdeltaBoundaryRho hfNterminal
      have huPrime : u ∈ TreeSequenceVertexSet TjPrime :=
        (Finset.mem_sdiff.mp huDiff).1
      have huOutside : u ∉ TreeSequenceVertexSet
          (ett.series.data.tree q.succ.castSucc) :=
        (Finset.mem_sdiff.mp huDiff).2
      have hdegree : MaximumDegree G + 1 ≤ k := by
        have step := ett.series.certified 0
        cases step with
        | initial triple => exact triple.2.2.1
      obtain ⟨beta, hbeta⟩ :=
        MissingColorsNonemptyOfMaximumDegree G rho1 hdegree u
      have huTerminal : u ≠ v := by
        intro huv
        apply huOutside
        simpa [huv] using hvStage
      have huErase : u ∈ (TreeSequenceVertexSet TjPrime).erase v :=
        Finset.mem_erase.mpr ⟨huTerminal, huPrime⟩
      have hbetaSupport : beta ∉ supportColors := by
        intro hbetaIn
        have hmember : beta ∈ MissingColors G rho1 u ∩ supportColors :=
          Finset.mem_inter.mpr ⟨hbeta, hbetaIn⟩
        rw [hcaseTwoPointwise u huErase] at hmember
        simpa using hmember
      have hbetaGammaFirst : beta ≠ gammaFirst := by
        intro hEq
        exact hbetaSupport (hEq ▸ hgammaFirstSupport)
      have hbetaTerminal : beta ∉ MissingColors G rho1 v := by
        intro hbetaV
        have hdisjoint := hprimeElementary huPrime hterminalPrime huTerminal
        exact (Finset.disjoint_left.mp hdisjoint) hbeta hbetaV
      have huSeed : u ∉ TreeSequenceVertexSet seed := by
        intro hu
        exact huOutside (vertexTransfer hseedN hu)
      let Tprevious : TreeSequence G e0 :=
        ett.series.data.tree jSlot.castSucc.castSucc
      have hvNotPrevious (hjPositive : 0 < jSlot.val) :
          v ∉ TreeSequenceVertexSet Tprevious := by
        intro hvPrevious
        let candidates : Finset (Fin (ett.rounds + 1)) :=
          Finset.univ.filter fun i =>
            v ∈ TreeSequenceVertexSet (ExtendedTashkinovLadderStage ett i)
        have hlast : Fin.last ett.rounds ∈ candidates := by
          simp only [candidates, Finset.mem_filter, Finset.mem_univ, true_and]
          rw [show ExtendedTashkinovLadderStage ett
              (Fin.last ett.rounds) = T by
            unfold ExtendedTashkinovLadderStage
            exact Fin.lastCases_last]
          exact hvFinal
        have hfirst := hjSlot
        unfold ETTFirstAppearanceIndex at hfirst
        dsimp at hfirst
        have hminimumValue :
            (candidates.min' ⟨Fin.last ett.rounds, hlast⟩).val =
              jSlot.val := by
          change jSlot.val + 1 =
            (candidates.min' ⟨Fin.last ett.rounds, hlast⟩).val + 1 at hfirst
          omega
        let previousSlot : Fin ett.rounds :=
          ⟨jSlot.val - 1, by omega⟩
        have hpreviousIndex : previousSlot.succ = jSlot.castSucc := by
          apply Fin.ext
          simp [previousSlot]
          omega
        have hpreviousMember : previousSlot.castSucc ∈ candidates := by
          simp only [candidates, Finset.mem_filter, Finset.mem_univ, true_and]
          rw [show ExtendedTashkinovLadderStage ett previousSlot.castSucc =
              Tprevious by
            unfold ExtendedTashkinovLadderStage
            rw [Fin.lastCases_castSucc, hpreviousIndex]]
          exact hvPrevious
        have hminimum := Finset.min'_le candidates previousSlot.castSucc
          hpreviousMember
        have hminimumVal := Fin.le_iff_val_le_val.mp hminimum
        rw [hminimumValue] at hminimumVal
        dsimp [previousSlot] at hminimumVal
        omega
      have hpreviousTj (hjPositive : 0 < jSlot.val) :
          TreeSequenceInitialSegment Tprevious
            (ett.series.data.tree jSlot.succ.castSucc) := by
        have hstep := stepSegment jSlot.castSucc (by simpa using hjPositive)
        rw [hjTreeIndex] at hstep
        exact hstep
      have hpreviousStrict (hjPositive : 0 < jSlot.val) :
          Tprevious.length < seed.length := by
        by_contra hnot
        have hpositionLe : terminalPosition.val ≤ Tprevious.length := by
          simpa [seed, TreeSequencePrefix] using Nat.le_of_not_gt hnot
        let previousPosition : Fin (Tprevious.length + 1) :=
          ⟨terminalPosition.val, by omega⟩
        have hcast : Fin.castLE
            (Nat.succ_le_succ (hpreviousTj hjPositive).1)
            previousPosition = terminalPosition := by
          apply Fin.ext
          rfl
        apply hvNotPrevious hjPositive
        simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ,
          true_and]
        refine ⟨previousPosition, ?_⟩
        have hvertex := (hpreviousTj hjPositive).2.1 previousPosition
        rw [hcast] at hvertex
        exact hvertex.symm.trans hterminalAt
      have hpreviousSeed (hjPositive : 0 < jSlot.val) :
          TreeSequenceInitialSegment Tprevious seed :=
        commonPrefix (hpreviousTj hjPositive) hseedTj
          (Nat.le_of_lt (hpreviousStrict hjPositive))
      have haugmentation : TashkinovAugmentationSequence
          (ett.series.data.coloring jSlot.castSucc) seed
          (ett.series.data.tree jSlot.succ.castSucc) := by as_aux_lemma =>
        generalize htarget : jSlot.castSucc = target
        cases ett.series.certified target with
        | initial triple seedLength initialColoring initialStored initialEdges
            initialKind initialVertex initialOutside initialDelta initialGamma
            initialClosure =>
          have htargetZero : jSlot.val = 0 := by
            have := congrArg Fin.val htarget
            simpa using this
          have htreeOne : ett.series.data.tree 1 =
              ett.series.data.tree jSlot.succ.castSucc := by
            congr 1
            apply Fin.ext
            simp [htargetZero]
          have hinitialTj : TreeSequenceInitialSegment
              (ett.series.data.tree 0)
              (ett.series.data.tree jSlot.succ.castSucc) := by
            have h := TashkinovAugmentationSequenceInitialSegment _ _ _
              initialClosure.1
            rw [htreeOne] at h
            exact h
          have hbaseSeed : TreeSequenceInitialSegment
              (ett.series.data.tree 0) seed := by
            apply commonPrefix hinitialTj hseedTj
            rw [seedLength]
            exact seed.positive
          have hrouteOld : TashkinovAugmentationSequence
              (ett.series.data.coloring 0) (ett.series.data.tree 0)
              (ett.series.data.tree jSlot.succ.castSucc) := by
            rw [← htreeOne]
            exact initialClosure.1
          have hroute := TashkinovAugmentationSequenceSuffix
            (ett.series.data.coloring 0) (ett.series.data.tree 0) seed
            (ett.series.data.tree jSlot.succ.castSucc) hrouteOld hbaseSeed
            hseedTj
          simpa [htargetZero] using hroute
        | SE i previousProper previousOneUncolored previousClosed
            previousNotStronglyClosed noRevisiting choice seriesAlternative
            currentColoring currentStored currentEdges currentKind currentVertex
            currentOutside currentDelta currentGamma adjoined adjoinedExactly
            closedExtension orderedExtension strictExtension =>
          have hi : i.succ = jSlot.castSucc := htarget.symm
          have hjPositive : 0 < jSlot.val := by
            have := congrArg Fin.val hi
            simp at this
            omega
          have hroute : TashkinovAugmentationSequence
              (ett.series.data.coloring jSlot.castSucc) adjoined
              (ett.series.data.tree jSlot.succ.castSucc) := by
            have h := closedExtension.1
            rw [hi, hjTreeIndex] at h
            exact h
          have hadjoinedTj : TreeSequenceInitialSegment adjoined
              (ett.series.data.tree jSlot.succ.castSucc) :=
            TashkinovAugmentationSequenceInitialSegment _ _ _ hroute
          have hadjoinedLength : adjoined.length ≤ seed.length := by
            rcases adjoinedExactly with ⟨hlen, -, -⟩
            have hiCast : i.succ.castSucc = jSlot.castSucc.castSucc := by
              apply Fin.ext
              simpa using congrArg Fin.val hi
            have hprev : ett.series.data.tree i.succ.castSucc =
                Tprevious := by rw [hiCast]
            rw [hprev] at hlen
            rw [hlen]
            exact Nat.succ_le_of_lt (hpreviousStrict hjPositive)
          have hadjoinedSeed : TreeSequenceInitialSegment adjoined seed :=
            commonPrefix hadjoinedTj hseedTj hadjoinedLength
          simpa [hi] using
            (TashkinovAugmentationSequenceSuffix
              (ett.series.data.coloring jSlot.castSucc) adjoined seed _ hroute
                hadjoinedSeed hseedTj)
        | PE i previousProper previousOneUncolored previousClosed
            previousNotStronglyClosed noRevisiting choice seriesAlternativeFails
            chosenGamma gammaRule secondStable secondStableProper
            secondStableOneUncolored secondStableRelation exitWitness
            currentColoring currentProper currentOneUncolored currentStored
            currentEdges currentKind currentVertex currentOutside currentDelta
            currentGamma closedExtension orderedExtension strictExtension =>
          have hi : i.succ = jSlot.castSucc := htarget.symm
          have hjPositive : 0 < jSlot.val := by
            have := congrArg Fin.val hi
            simp at this
            omega
          have hroute : TashkinovAugmentationSequence
              (ett.series.data.coloring jSlot.castSucc) Tprevious
              (ett.series.data.tree jSlot.succ.castSucc) := by
            have h := closedExtension.1
            rw [hi, hjTreeIndex] at h
            simpa [Tprevious, hi] using h
          simpa [hi] using
            (TashkinovAugmentationSequenceSuffix
              (ett.series.data.coloring jSlot.castSucc) Tprevious seed _ hroute
                (hpreviousSeed hjPositive) hseedTj)
        | RE i previousProper previousOneUncolored previousClosed
            previousNotStronglyClosed available currentColoring currentStored
            currentEdges currentKind currentVertex currentOutside currentDelta
            currentGamma adjoined adjoinedExactly closedExtension orderedExtension
            strictExtension =>
          have hi : i.succ = jSlot.castSucc := htarget.symm
          have hjPositive : 0 < jSlot.val := by
            have := congrArg Fin.val hi
            simp at this
            omega
          have hroute : TashkinovAugmentationSequence
              (ett.series.data.coloring jSlot.castSucc) adjoined
              (ett.series.data.tree jSlot.succ.castSucc) := by
            have h := closedExtension.1
            rw [hi, hjTreeIndex] at h
            exact h
          have hadjoinedTj : TreeSequenceInitialSegment adjoined
              (ett.series.data.tree jSlot.succ.castSucc) :=
            TashkinovAugmentationSequenceInitialSegment _ _ _ hroute
          have hadjoinedLength : adjoined.length ≤ seed.length := by
            rcases adjoinedExactly with ⟨hlen, -, -⟩
            have hiCast : i.succ.castSucc = jSlot.castSucc.castSucc := by
              apply Fin.ext
              simpa using congrArg Fin.val hi
            have hprev : ett.series.data.tree i.succ.castSucc =
                Tprevious := by rw [hiCast]
            rw [hprev] at hlen
            rw [hlen]
            exact Nat.succ_le_of_lt (hpreviousStrict hjPositive)
          have hadjoinedSeed : TreeSequenceInitialSegment adjoined seed :=
            commonPrefix hadjoinedTj hseedTj hadjoinedLength
          simpa [hi] using
            (TashkinovAugmentationSequenceSuffix
              (ett.series.data.coloring jSlot.castSucc) adjoined seed _ hroute
                hadjoinedSeed hseedTj)
      obtain ⟨z, hz, zPosition, hzPosition, hzAfter,
          hzChoice, hzBefore, hzEdges⟩ :=
        ExtensionBaseCaseTwoObservation23
          (ett.series.data.tree jSlot.succ.castSucc) seed TjPrime
          (ett.series.data.coloring jSlot.castSucc) rho1 v u beta gammaFirst
          hseedTj hseedPrime hseedTerminal huPrime huSeed hprimeElementary
          hbeta hterminalSeed hb2Missing.1 hbetaTerminal hterminalInclusion
          hbetaGammaFirst haugmentation hb2EdgesFromSeed
      have hcaseTwoObservationPackage :
          (u ∈ TreeSequenceVertexSet TjPrime ∧
            u ∉ TreeSequenceVertexSet
              (ett.series.data.tree q.succ.castSucc)) ∧
          (exitPath.IsPath ∧ 2 ≤ exitPath.length ∧
            (∀ y : Sum V E, y ∈ exitPath.support →
              y ∈ componentPath.support) ∧
            (∀ y : V,
              y ∈ TreeSequenceVertexSet
                  (ett.series.data.tree q.succ.castSucc) ∪
                    TreeSequenceVertexSet TjPrime →
              (Sum.inl y ∈ exitPath.support ↔ y = u)) ∧
            (∃ g ∈ BoundaryColorEdges G rho1
                (TreeSequenceVertexSet
                    (ett.series.data.tree q.succ.castSucc) ∪
                  TreeSequenceVertexSet TjPrime) gamma,
              Incident G u g ∧ Sum.inr g ∈ exitPath.support) ∧
            ¬ Incident G u fN) ∧
          (beta ∈ MissingColors G rho1 u ∧ beta ∉ supportColors) ∧
          (z ∈ TreeSequenceVertexSet
              (ett.series.data.tree jSlot.succ.castSucc) ∧
            (ett.series.data.tree jSlot.succ.castSucc).vertex zPosition = z ∧
            seed.length ≤ zPosition.val ∧
            ((seed.length < zPosition.val ∧
                beta ∈ MissingColors G rho1 z ∧
                ∀ r : Fin
                    ((ett.series.data.tree jSlot.succ.castSucc).length + 1),
                  seed.length < r.val → r.val < zPosition.val →
                  beta ∉ MissingColors G rho1
                    ((ett.series.data.tree jSlot.succ.castSucc).vertex r)) ∨
              (zPosition = Fin.last
                  (ett.series.data.tree jSlot.succ.castSucc).length ∧
                ∀ r : Fin
                    ((ett.series.data.tree jSlot.succ.castSucc).length + 1),
                  seed.length < r.val →
                  beta ∉ MissingColors G rho1
                    ((ett.series.data.tree jSlot.succ.castSucc).vertex r))) ∧
            (∀ y ∈ TreeVerticesBefore
                (ett.series.data.tree jSlot.succ.castSucc) z hz,
              beta ∉ MissingColors G rho1 y) ∧
            ∀ a : Fin (ett.series.data.tree jSlot.succ.castSucc).length,
              seed.length ≤ a.val → a.val < zPosition.val →
              rho1 ((ett.series.data.tree jSlot.succ.castSucc).edge a) ≠
                some beta) := by
        exact ⟨⟨huPrime, huOutside⟩,
          ⟨hexitPath, hexitLength, hexitSupport, hexitIntersection,
            hexitBoundary, huNotFN⟩,
          ⟨hbeta, hbetaSupport⟩,
          ⟨hz, hzPosition, hzAfter, hzChoice, hzBefore, hzEdges⟩⟩
      have hpreterminalGammaPresent : ∀ (u : V) (beta : Fin k),
          u ∈ TreeSequenceVertexSet TjPrime →
          u ∉ TreeSequenceVertexSet
            (ett.series.data.tree q.succ.castSucc) →
          beta ∈ MissingColors G rho1 u →
          ∀ a : Fin p0,
            gamma0 a.castSucc ∈ PresentColors G
              (TwoColorComponentSwap G
                (OutsideTreeColorSwap TjPrime rho1 beta delta)
                gamma beta (Sum.inl u)) u := by
        intro u' beta' huPrime' huOutside' hbeta' a
        let aSlot : Fin (p0 + 1) := a.castSucc
        have hgammaASupport : gamma0 aSlot ∈ supportColors := by
          simp only [supportColors, Finset.mem_biUnion, Finset.mem_univ,
            true_and]
          refine ⟨aSlot, ?_⟩
          rw [hstored0]
          simp
        have huNe : u' ≠ v := by
          intro huv
          apply huOutside'
          simpa [huv] using hvStage
        have huErase : u' ∈ (TreeSequenceVertexSet TjPrime).erase v :=
          Finset.mem_erase.mpr ⟨huNe, huPrime'⟩
        have hgammaANotMissing :
            gamma0 aSlot ∉ MissingColors G rho1 u' := by
          intro hmissing
          have hmember : gamma0 aSlot ∈
              MissingColors G rho1 u' ∩ supportColors :=
            Finset.mem_inter.mpr ⟨hmissing, hgammaASupport⟩
          rw [hcaseTwoPointwise u' huErase] at hmember
          simpa using hmember
        have hgammaAPresent : gamma0 aSlot ∈ PresentColors G rho1 u' := by
          simpa [MissingColors] using hgammaANotMissing
        have hgammaANeBeta : gamma0 aSlot ≠ beta' := by
          intro heq
          have hbetaSupport' : beta' ∉ supportColors := by
            intro hbetaSupport'
            have hmember : beta' ∈ MissingColors G rho1 u' ∩ supportColors :=
              Finset.mem_inter.mpr ⟨hbeta', hbetaSupport'⟩
            rw [hcaseTwoPointwise u' huErase] at hmember
            simpa using hmember
          exact hbetaSupport' (heq ▸ hgammaASupport)
        have hconsGamma (r : Fin (p0 + 1)) :
            (Fin.cons (gamma0 0) delta0 : Fin (p0 + 2) → Fin k)
                r.castSucc = gamma0 r := by
          refine Fin.cases ?_ (fun s => ?_) r
          · simp
          · rw [show (Fin.succ s).castSucc = s.castSucc.succ by
              apply Fin.ext
              rfl]
            rw [Fin.cons_succ]
            exact (hchain0 s).symm
        have hgammaANeGamma : gamma0 aSlot ≠ gamma := by
          intro heq
          have hvalues :
              (Fin.cons (gamma0 0) delta0 : Fin (p0 + 2) → Fin k)
                  aSlot.castSucc =
                (Fin.cons (gamma0 0) delta0 : Fin (p0 + 2) → Fin k)
                  (Fin.last p0).castSucc := by
            rw [hconsGamma, hconsGamma, hgammaLast]
            exact heq
          have hindices := hinjective0 hvalues
          have hvals := congrArg Fin.val hindices
          simp [aSlot] at hvals
          omega
        obtain ⟨f, huf, hcolor⟩ := by
          simpa only [PresentColors, Finset.mem_filter, Finset.mem_univ,
            true_and] using hgammaAPresent
        have htreeIncident : TreeIncidentEdge TjPrime f :=
          ⟨u', huPrime', huf⟩
        have houtsideColor :
            OutsideTreeColorSwap TjPrime rho1 beta' delta f =
              some (gamma0 aSlot) := by
          simp [OutsideTreeColorSwap, htreeIncident, hcolor]
        simp only [PresentColors, Finset.mem_filter, Finset.mem_univ,
          true_and]
        refine ⟨f, huf, ?_⟩
        by_cases hfComponent : Sum.inr f ∈
            TwoColorComponent G
              (OutsideTreeColorSwap TjPrime rho1 beta' delta)
              gamma beta' (Sum.inl u')
        · simp [TwoColorComponentSwap, hfComponent, houtsideColor,
            hgammaANeGamma, hgammaANeBeta, aSlot]
        · simp [TwoColorComponentSwap, hfComponent, houtsideColor, aSlot]
      have hTjInitialEarlier : ∀ s : Fin ett.rounds,
          s ∈ (ExtensionBaseSupportClass ett v hvFinal v).erase q →
          TreeSequenceInitialSegment
            (ett.series.data.tree jSlot.succ.castSucc)
            (ett.series.data.tree s.succ.castSucc) := by
        intro s hs
        have hsClass := (Finset.mem_erase.mp hs).2
        have hsData := hsClass
        simp only [ExtensionBaseSupportClass, Finset.mem_filter] at hsData
        have hsActive := hsData.1
        simp only [ExtensionBaseActiveIndices, Finset.mem_filter,
          Finset.mem_univ, true_and] at hsActive
        have hjIndexLe : jSlot.val + 1 ≤ s.val + 1 := by
          rw [hjSlot]
          exact hsActive.1
        have hseg := stageToStage (jSlot.val + 1) (s.val + 1)
          (by omega) hjIndexLe (by omega)
        convert hseg using 1 <;> congr 1 <;> apply Fin.ext <;> rfl
      have hpositiveClaim45 (hp0 : 0 < p0) :=
        let hpreterminal := hpreterminalPackage hp0
        let preterminalSlot := Classical.choose hpreterminal
        ExtensionBaseClaim45 ett q preterminalSlot jSlot hqTerminal
          (Classical.choose_spec hpreterminal).1 v hvFinal
          (ett.series.data.tree jSlot.succ.castSucc)
          (ett.series.data.tree q.succ.castSucc) seed TjPrime
          (ett.series.data.coloring jSlot.castSucc)
          (ett.series.data.coloring q.succ) sigma rho1
          (TashkinovStoredColors ett.series.data jSlot.castSucc)
          controlled restorationColors supportColors gammaFirst gamma delta
          fN x componentPath hphiNProper hphiNOne hsigmaProper hsigmaOne
          hrho1Proper hrho1One hTjQ hseedTj hseedPrime hseedTerminal
          hterminalJ hterminalSeed hclosure hprimeElementary
          hcaseTwoPointwise hterminalIntersection' hgammaSupport
          hdeltaSupport hgammaFirstSupport hgammaDelta hsigmaControlled
          hgammaControlled hdeltaControlled
          (fun f hf => hb3EdgeEffects f hf)
          hterminalColorsNotRestored.1 hterminalColorsNotRestored.2
          hgammaBoundary hdeltaLocation hdeltaMissing hcomponentPath
          (by simpa [C] using hcomponentSupport) hxOutside htwoN hfNterminal
          hb1Tj hb2Missing.1 hterminalInclusion haugmentation
          hb2EdgesFromSeed hdeltaPhiJ hsupportSet hterminalClass
          (Classical.choose_spec hpreterminal).2.1
          (Classical.choose_spec hpreterminal).2.2 hqGamma hqDelta hb4Earlier
          hsupportColors hdeltaEarlier hsupportComponentOrder p0 indices0
          gamma0 delta0 hincreasing0 hclass0 hqLast hsupport0 hkind0
          hgamma0 hdelta0 hstored0 hchain0 hinjective0 rfl
          hTjInitialEarlier rfl hpreterminalGammaPresent
      have hgammaFirstZero (hp0 : p0 = 0) : gammaFirst = gamma := by
        unfold gammaFirst
        rw [← hgammaLast]
        congr 1
        apply Fin.ext
        simp [hp0]
      let rho0 := OutsideTreeColorSwap TjPrime rho1 beta delta
      let rho3 := TwoColorComponentSwap G rho0 gamma beta (Sum.inl u)
      have hbetaDelta : beta ≠ delta := by
        intro heq
        exact hbetaSupport (heq ▸ hdeltaSupport)
      have hbetaGamma : beta ≠ gamma := by
        intro heq
        exact hbetaSupport (heq ▸ hgammaSupport)
      have hbetaTree : beta ∈ TreeMissingColors rho1 TjPrime := by
        unfold TreeMissingColors
        exact Finset.mem_biUnion.mpr ⟨u, huPrime, hbeta⟩
      have hdeltaTree : delta ∈ TreeMissingColors rho1 TjPrime := by
        unfold TreeMissingColors
        exact Finset.mem_biUnion.mpr ⟨v, hterminalPrime, hdeltaMissing⟩
      have houtside := OutsideTreeColorSwapStable TjPrime supportColors rho1
        beta delta hrho1Proper hrho1One hclosure.2 hbetaTree hdeltaTree
          hbetaDelta
      change IsProperEdgeColoring G rho0 ∧ IsOneEdgeUncolored rho0 e0 ∧
          StableColoring TjPrime supportColors rho1 rho0 ∧
          ∀ f : E, TreeIncidentEdge TjPrime f → rho0 f = rho1 f at houtside
      rcases houtside with
        ⟨hrho0Proper, hrho0One, hrho0Stable, hrho0Fixed⟩
      have hrho3Proper : IsProperEdgeColoring G rho3 :=
        TwoColorComponentSwapProper G rho0 gamma beta
          (Ne.symm hbetaGamma) hrho0Proper (Sum.inl u)
      have hrho3One : IsOneEdgeUncolored rho3 e0 := by
        unfold IsOneEdgeUncolored at hrho0One ⊢
        constructor
        · simp [rho3, TwoColorComponentSwap, hrho0One.1]
        · intro f hfe
          obtain ⟨c, hc⟩ := hrho0One.2 f hfe
          have hne : rho3 f ≠ none := by
            by_cases hK : Sum.inr f ∈
                TwoColorComponent G rho0 gamma beta (Sum.inl u)
            · by_cases hcg : c = gamma
              · simp [rho3, TwoColorComponentSwap, hK, hc, hcg]
              · by_cases hcb : c = beta
                · simp [rho3, TwoColorComponentSwap, hK, hc, hcg, hcb,
                    hbetaGamma, hbetaGamma.symm]
                · simp [rho3, TwoColorComponentSwap, hK, hc, hcg, hcb]
            · simp [rho3, TwoColorComponentSwap, hK, hc]
          obtain ⟨d, hd⟩ := Option.ne_none_iff_exists.mp hne
          exact ⟨d, hd.symm⟩
      have hbetaRho0 : beta ∈ MissingColors G rho0 u := by
        rw [hrho0Stable.2 u huPrime]
        exact hbeta
      obtain ⟨g, hgBoundary, hug, hgExit⟩ := hexitBoundary
      have hgRho1 : rho1 g = some gamma :=
        (Finset.mem_filter.mp hgBoundary).2
      have hgRho0 : rho0 g = some gamma := by
        rw [hrho0Fixed g ⟨u, huPrime, hug⟩]
        exact hgRho1
      have hgComponent : Sum.inr g ∈
          TwoColorComponent G rho0 gamma beta (Sum.inl u) := by
        change (TwoColorIncidenceGraph G rho0 gamma beta).connectedComponentMk
            (Sum.inr g) =
          (TwoColorIncidenceGraph G rho0 gamma beta).connectedComponentMk
            (Sum.inl u)
        have hadj : (TwoColorIncidenceGraph G rho0 gamma beta).Adj
            (Sum.inl u) (Sum.inr g) := ⟨hug, Or.inl hgRho0⟩
        exact
          (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
            hadj).symm
      have hgRho3 : rho3 g = some beta := by
        simp [rho3, TwoColorComponentSwap, hgComponent, hgRho0,
          hbetaGamma, hbetaGamma.symm]
      have hbetaRho3 : beta ∉ MissingColors G rho3 u := by
        intro hb
        have hbPresent : beta ∉ PresentColors G rho3 u := by
          simpa [MissingColors] using hb
        apply hbPresent
        simp only [PresentColors, Finset.mem_filter, Finset.mem_univ,
          true_and]
        exact ⟨g, hug, hgRho3⟩
      have hgammaRho3 : gamma ∈ MissingColors G rho3 u := by
        apply Finset.mem_sdiff.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        intro hgammaPresent
        simp only [PresentColors, Finset.mem_filter, Finset.mem_univ,
          true_and] at hgammaPresent
        obtain ⟨f, huf, hfRho3⟩ := hgammaPresent
        by_cases hfComponent : Sum.inr f ∈
            TwoColorComponent G rho0 gamma beta (Sum.inl u)
        · by_cases hfGamma : rho0 f = some gamma
          · have : (some beta : Option (Fin k)) = some gamma := by
              simpa [rho3, TwoColorComponentSwap, hfComponent, hfGamma,
                hbetaGamma, hbetaGamma.symm] using hfRho3
            exact hbetaGamma (Option.some.inj this)
          · by_cases hfBeta : rho0 f = some beta
            · have hnotPresent : beta ∉ PresentColors G rho0 u := by
                simpa [MissingColors] using hbetaRho0
              exact hnotPresent (by
                simp only [PresentColors, Finset.mem_filter,
                  Finset.mem_univ, true_and]
                exact ⟨f, huf, hfBeta⟩)
            · have : rho0 f = some gamma := by
                simpa [rho3, TwoColorComponentSwap, hfComponent, hfGamma,
                  hfBeta] using hfRho3
              exact hfGamma this
        · have hfRho0 : rho0 f = some gamma := by
            simpa [rho3, TwoColorComponentSwap, hfComponent] using hfRho3
          have hadj : (TwoColorIncidenceGraph G rho0 gamma beta).Adj
              (Sum.inl u) (Sum.inr f) := ⟨huf, Or.inl hfRho0⟩
          apply hfComponent
          change (TwoColorIncidenceGraph G rho0 gamma beta).connectedComponentMk
              (Sum.inr f) =
            (TwoColorIncidenceGraph G rho0 gamma beta).connectedComponentMk
              (Sum.inl u)
          exact
            (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
              hadj).symm
      have hgammaFirstRho3 (hp0 : p0 = 0) :
          gammaFirst ∈ MissingColors G rho3 u := by
        rw [hgammaFirstZero hp0]
        exact hgammaRho3
      sorry
  · intro hwv
    subst w
    change Sum.inl v ∈
      (TwoColorIncidenceGraph G sigma gamma delta).connectedComponentMk
        (Sum.inl v)
    exact (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mpr rfl
