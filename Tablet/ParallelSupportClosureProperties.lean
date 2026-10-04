import Tablet.CertifiedETTRestriction
import Tablet.ColoredVertexSetClosed
import Tablet.ColoredVertexSetElementary
import Tablet.CorrespondingExtendedTashkinovTree
import Tablet.ETTFirstAppearanceIndex
import Tablet.ExtendedTashkinovTree
import Tablet.HierarchyBase
import Tablet.HkuTreeColorsControlled
import Tablet.InternalEdges
import Tablet.IsOneEdgeUncolored
import Tablet.KTriple
import Tablet.MaximumPropertyTransport
import Tablet.ModColoring
import Tablet.SameColorSeriesPreserved
import Tablet.StableColoring
import Tablet.StableColoringBeforeVertex
import Tablet.TashkinovAugmentation
import Tablet.TashkinovAugmentationSequence
import Tablet.TashkinovAugmentationSequenceRestrict
import Tablet.TashkinovClosure
import Tablet.TashkinovSeries
import Tablet.TashkinovSeriesStep
import Tablet.TechnicalInductionContext
import Tablet.TechnicalTheoremBase
import Tablet.TreeInterchangeable
import Tablet.TreeMissingColors
import Tablet.TreeSequence
import Tablet.TreeSequenceInitialSegment
import Tablet.TreeSequenceVertexSet
import Tablet.TwoColorPathComponent
import Tablet.sc2

-- [TABLET NODE: ParallelSupportClosureProperties]
theorem ParallelSupportClosureProperties {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (ctx : TechnicalInductionContext G k e0 ett.rounds)
    (hMP : MaximumProperty ett) (hpositive : 0 < ett.rounds)
    (hPE : ett.series.data.kind (Fin.last ett.rounds) =
      some TashkinovExtensionKind.PE)
    (sigma : PartialEdgeColoring E k)
    (hproper : IsProperEdgeColoring G sigma)
    (hone : IsOneEdgeUncolored sigma e0)
    (hstable : StableColoring
      (ett.series.data.tree (Fin.last ett.rounds).castSucc)
      (TashkinovStoredColors ett.series.data (Fin.last ett.rounds))
      phi sigma)
    (base : HierarchyBase ett sigma) :
    ColoredVertexSetElementary G sigma
        (TreeSequenceVertexSet base.closure) ∧
      ColoredVertexSetClosed G sigma
        (TreeSequenceVertexSet base.closure) ∧
      ∀ alpha beta : Fin k,
        (alpha ∈ TreeMissingColors sigma base.closure ∨
          beta ∈ TreeMissingColors sigma base.closure) →
        TreeInterchangeable G base.closure sigma alpha beta := by
-- BODY
  classical
  let n : Fin (ett.rounds + 1) := Fin.last ett.rounds
  let q : Fin ett.rounds := ⟨ett.rounds - 1, by omega⟩
  have hqSucc : q.succ = n := by
    apply Fin.ext
    simp [q, n]
    omega
  let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc
  let v : V := Tn.vertex base.supportPosition
  let P : TreeSequence G e0 :=
    TreeSequencePrefix Tn base.supportPosition.val base.supportPositive
      (Nat.le_of_lt_succ base.supportPosition.isLt)
  have hparallel :
      ett.series.data.chosenVertex n = some v ∧
        TashkinovClosure sigma P base.closure ∧
        Nonempty (OrderedTreeUnion Tn base.closure base.core) := by
    simpa [n, Tn, v, P] using base.parallel hPE
  have hTnT : TreeSequenceInitialSegment Tn T := by
    have hindex : n.castSucc =
        (⟨ett.rounds, by omega⟩ : Fin (ett.rounds + 2)) := by
      apply Fin.ext
      simp [n]
    change TreeSequenceInitialSegment (ett.series.data.tree n.castSucc) T
    rw [hindex]
    exact ett.abovePenultimate
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
  have vertexTransfer {A B : TreeSequence G e0}
      (hAB : TreeSequenceInitialSegment A B) :
      TreeSequenceVertexSet A ⊆ TreeSequenceVertexSet B := by
    intro x hx
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ,
      true_and] at hx ⊢
    obtain ⟨i, rfl⟩ := hx
    exact ⟨Fin.castLE (Nat.succ_le_succ hAB.1) i, hAB.2.1 i⟩
  have sequenceSegment {A B : TreeSequence G e0}
      {rho : PartialEdgeColoring E k}
      (hAB : TashkinovAugmentationSequence rho A B) :
      TreeSequenceInitialSegment A B := by
    unfold TashkinovAugmentationSequence at hAB
    induction hAB using Relation.ReflTransGen.head_induction_on with
    | refl => exact segmentRefl _
    | @head A B hstep htail ih =>
        exact segmentTrans hstep.2.1 ih
  have missingTransfer {A B : TreeSequence G e0}
      {rho : PartialEdgeColoring E k}
      (hAB : TreeSequenceInitialSegment A B) :
      TreeMissingColors rho A ⊆ TreeMissingColors rho B := by
    intro c hc
    simp only [TreeMissingColors, Finset.mem_biUnion] at hc ⊢
    obtain ⟨x, hx, hxc⟩ := hc
    exact ⟨x, vertexTransfer hAB hx, hxc⟩
  have hP_Tn : TreeSequenceInitialSegment P Tn := by
    refine ⟨Nat.le_of_lt_succ base.supportPosition.isLt, ?_, ?_⟩
    · intro i
      simp [P, TreeSequencePrefix]
    · intro i
      simp [P, TreeSequencePrefix]
  have hP_T : TreeSequenceInitialSegment P T := segmentTrans hP_Tn hTnT
  have hvTn : v ∈ TreeSequenceVertexSet Tn := by
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ,
      true_and]
    exact ⟨base.supportPosition, rfl⟩
  have hvT : v ∈ TreeSequenceVertexSet T := vertexTransfer hTnT hvTn
  let candidates : Finset (Fin (ett.rounds + 1)) :=
    Finset.univ.filter fun i =>
      v ∈ TreeSequenceVertexSet (ExtendedTashkinovLadderStage ett i)
  have hqmem : q.castSucc ∈ candidates := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    unfold ExtendedTashkinovLadderStage
    rw [Fin.lastCases_castSucc]
    have hindex : q.succ.castSucc = n.castSucc := by
      exact congrArg Fin.castSucc hqSucc
    rw [hindex]
    exact hvTn
  let candidatesNonempty : candidates.Nonempty := ⟨q.castSucc, hqmem⟩
  let minimum : Fin (ett.rounds + 1) :=
    candidates.min' candidatesNonempty
  have hfirstDef : ETTFirstAppearanceIndex ett v hvT = minimum.val + 1 := by
    unfold ETTFirstAppearanceIndex
    dsimp
    change _ = (candidates.min' candidatesNonempty).val + 1
    congr
  have hfirstPositive : 0 < ETTFirstAppearanceIndex ett v hvT := by
    rw [hfirstDef]
    omega
  have hfirstUpper : ETTFirstAppearanceIndex ett v hvT ≤ q.val + 1 := by
    rw [hfirstDef]
    have hle : minimum ≤ q.castSucc := by
      exact Finset.min'_le candidates q.castSucc hqmem
    have hnat := Fin.le_iff_val_le_val.mp hle
    simpa only [Fin.val_castSucc] using Nat.add_le_add_right hnat 1
  let j : Fin ett.rounds :=
    ⟨ETTFirstAppearanceIndex ett v hvT - 1, by omega⟩
  have hjFirst : ETTFirstAppearanceIndex ett v hvT = j.val + 1 := by
    simp only [j]
    omega
  have hjq : j.val ≤ q.val := by
    dsimp [j]
    omega
  have hkindQ : ett.series.data.kind q.succ =
      some TashkinovExtensionKind.PE := by
    simpa [hqSucc, n] using hPE
  have hvertexQ : ett.series.data.chosenVertex q.succ = some v := by
    simpa [hqSucc] using hparallel.1
  have hcurrent := (ctx.currentThree ett rfl hMP).1 q v hkindQ hvertexQ
    hvT j.castSucc (by simpa using hjFirst) sigma hproper hone
    (by
      have hgenN : phi = ett.series.data.coloring n := by
        simpa [n] using ett.generatingColoring
      have hs : StableColoring Tn
          (TashkinovStoredColors ett.series.data n)
          (ett.series.data.coloring n) sigma := by
        rw [← hgenN]
        simpa [Tn, n] using hstable
      simpa [hqSucc] using hs)
  have hsigmaBefore : StableColoringBeforeVertex T v hvT
      (TashkinovStoredColors ett.series.data j.castSucc)
      (ett.series.data.coloring j.castSucc) sigma := hcurrent.1
  have stepSegment : ∀ i : Fin (ett.rounds + 1), 0 < i.val →
      TreeSequenceInitialSegment (ett.series.data.tree i.castSucc)
        (ett.series.data.tree i.succ) := by
    intro i hi
    cases ett.series.certified i with
    | initial => simpa using hi
    | SE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => assumption
    | PE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
        assumption
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
      | zero =>
          simpa using segmentRefl (ett.series.data.tree ⟨a, by omega⟩)
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
  let Tj : TreeSequence G e0 := ett.series.data.tree j.succ.castSucc
  have hvStage : v ∈ TreeSequenceVertexSet Tj := by
    rw [hfirstDef] at hjFirst
    change v ∈ TreeSequenceVertexSet
      (ett.series.data.tree j.succ.castSucc)
    have hminVal : minimum.val = j.val := by omega
    have hminEq : minimum = j.castSucc := by
      apply Fin.ext
      exact hminVal
    have hminimumMember : minimum ∈ candidates := by
      exact Finset.min'_mem candidates candidatesNonempty
    have hjMember : j.castSucc ∈ candidates := by
      rw [← hminEq]
      exact hminimumMember
    simp only [candidates, Finset.mem_filter, Finset.mem_univ, true_and]
      at hjMember
    simpa [ExtendedTashkinovLadderStage, Fin.lastCases_castSucc] using
      hjMember
  have hStageTn : TreeSequenceInitialSegment Tj Tn := by
    have hseg := stageToStage (j.val + 1) ett.rounds (by omega)
      (by omega) le_rfl
    change TreeSequenceInitialSegment
      (ett.series.data.tree j.succ.castSucc)
      (ett.series.data.tree n.castSucc)
    convert hseg using 1 <;> congr 1 <;> apply Fin.ext <;> simp [n]
  have hPLength : P.length = base.supportPosition.val := by
    simp [P, TreeSequencePrefix]
  have hPLeStage : P.length ≤
      Tj.length := by
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ,
      true_and] at hvStage
    obtain ⟨i, hi⟩ := hvStage
    have hindex : Fin.castLE (Nat.succ_le_succ hStageTn.1) i =
        base.supportPosition := by
      apply Tn.vertex_injective
      exact (hStageTn.2.1 i).trans (hi.trans (by rfl))
    rw [hPLength]
    have := congrArg Fin.val hindex
    dsimp at this
    omega
  have hPStage : TreeSequenceInitialSegment P
      Tj :=
    commonPrefix hP_Tn hStageTn hPLeStage
  have segmentVertexBefore {A : TreeSequence G e0}
      (hAP : TreeSequenceInitialSegment A P)
      (hAlen : A.length < P.length) {x : V}
      (hxA : x ∈ TreeSequenceVertexSet A) :
      x ∈ TreeVerticesBefore T v hvT := by
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ,
      true_and] at hxA
    obtain ⟨i, rfl⟩ := hxA
    unfold TreeVerticesBefore
    apply Finset.mem_filter.mpr
    let iP : Fin (P.length + 1) :=
      Fin.castLE (Nat.succ_le_succ hAP.1) i
    let iT : Fin (T.length + 1) :=
      Fin.castLE (Nat.succ_le_succ hP_T.1) iP
    let vT : Fin (T.length + 1) :=
      Fin.castLE (Nat.succ_le_succ hTnT.1) base.supportPosition
    refine ⟨vertexTransfer (segmentTrans hAP hP_T) (by
      simp [TreeSequenceVertexSet]), iT, vT, ?_, ?_, ?_⟩
    · exact (hP_T.2.1 iP).trans (hAP.2.1 i)
    · exact hTnT.2.1 base.supportPosition
    · change i.val < base.supportPosition.val
      rw [← hPLength]
      omega
  have transportStep {A B : TreeSequence G e0}
      (hstep : TashkinovAugmentation
        (ett.series.data.coloring j.castSucc) A B)
      (hBP : TreeSequenceInitialSegment B P) :
      TashkinovAugmentation sigma A B := by
    rcases hstep with ⟨hlen, hAB, c, hcolor, hcMissing⟩
    have hAP : TreeSequenceInitialSegment A P := segmentTrans hAB hBP
    have hAlen : A.length < P.length :=
      lt_of_lt_of_le (by omega) hBP.1
    have hcMissingSigma : c ∈ TreeMissingColors sigma A := by
      unfold TreeMissingColors at hcMissing ⊢
      obtain ⟨x, hxA, hcx⟩ := Finset.mem_biUnion.mp hcMissing
      refine Finset.mem_biUnion.mpr ⟨x, hxA, ?_⟩
      rw [hsigmaBefore.2 x (segmentVertexBefore hAP hAlen hxA)]
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
    have holdBefore : B.vertex oldPosition ∈ TreeVerticesBefore T v hvT := by
      rw [holdEq]
      exact segmentVertexBefore hAP hAlen (by simp [TreeSequenceVertexSet])
    have holdIncident : Incident G (B.vertex oldPosition) (B.edge added) := by
      unfold Incident
      rw [hattach]
      simp [oldPosition]
    have haddedFixed : sigma (B.edge added) =
        ett.series.data.coloring j.castSucc (B.edge added) := by
      apply hsigmaBefore.1 (B.edge added)
        ⟨B.vertex oldPosition, holdBefore, holdIncident⟩
      refine ⟨c, ?_, hcolor⟩
      apply Finset.mem_union_left
      unfold TreeMissingColors at hcMissing
      obtain ⟨x, hxA, hcx⟩ := Finset.mem_biUnion.mp hcMissing
      exact Finset.mem_biUnion.mpr
        ⟨x, segmentVertexBefore hAP hAlen hxA, hcx⟩
    exact ⟨hlen, hAB, c, haddedFixed.trans hcolor, hcMissingSigma⟩
  have transportRoute (S : TreeSequence G e0)
      (hroute : TashkinovAugmentationSequence
        (ett.series.data.coloring j.castSucc) S P) :
      TashkinovAugmentationSequence sigma S P := by
    unfold TashkinovAugmentationSequence at hroute ⊢
    induction hroute using Relation.ReflTransGen.head_induction_on with
    | refl => exact Relation.ReflTransGen.refl
    | @head A B hAB hBP ih =>
        have hBsegment : TreeSequenceInitialSegment B P :=
          sequenceSegment hBP
        exact Relation.ReflTransGen.head (transportStep hAB hBsegment) ih
  have hPClosure : TreeSequenceInitialSegment P base.closure :=
    sequenceSegment hparallel.2.1.1
  have hclosed : ColoredVertexSetClosed G sigma
      (TreeSequenceVertexSet base.closure) := hparallel.2.1.2
  have hminimumVal : minimum.val = j.val := by
    rw [hfirstDef] at hjFirst
    omega
  have hvP : v ∈ TreeSequenceVertexSet P := by
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ,
      true_and]
    let lastP : Fin (P.length + 1) := Fin.last P.length
    refine ⟨lastP, ?_⟩
    have hlastIndex : Fin.castLE (Nat.succ_le_succ hP_Tn.1) lastP =
        base.supportPosition := by
      apply Fin.ext
      simp [lastP, hPLength]
    exact (hP_Tn.2.1 lastP).symm.trans (congrArg Tn.vertex hlastIndex)
  by_cases hjPositive : 0 < j.val
  · let Tprev : TreeSequence G e0 :=
      ett.series.data.tree j.castSucc.castSucc
    have hPrevStage : TreeSequenceInitialSegment Tprev Tj := by
      have hseg := stepSegment j.castSucc (by simpa using hjPositive)
      change TreeSequenceInitialSegment
        (ett.series.data.tree j.castSucc.castSucc)
        (ett.series.data.tree j.succ.castSucc)
      convert hseg using 1 <;> congr 1 <;> apply Fin.ext <;> rfl
    have hNotPrev : v ∉ TreeSequenceVertexSet Tprev := by
      intro hvPrev
      let jp : Fin ett.rounds := ⟨j.val - 1, by omega⟩
      have hjpSucc : jp.succ = j.castSucc := by
        apply Fin.ext
        simp [jp]
        omega
      have hjpMem : jp.castSucc ∈ candidates := by
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        unfold ExtendedTashkinovLadderStage
        rw [Fin.lastCases_castSucc]
        have hindex : jp.succ.castSucc = j.castSucc.castSucc :=
          congrArg Fin.castSucc hjpSucc
        rw [hindex]
        exact hvPrev
      have hle : minimum ≤ jp.castSucc := by
        exact Finset.min'_le candidates jp.castSucc hjpMem
      have hvals := Fin.le_iff_val_le_val.mp hle
      dsimp [jp] at hvals
      omega
    have hPrevTn : TreeSequenceInitialSegment Tprev Tn :=
      segmentTrans hPrevStage hStageTn
    have hPrevStrictP : Tprev.length < P.length := by
      by_contra hnot
      have hPPrev : TreeSequenceInitialSegment P Tprev :=
        commonPrefix hP_Tn hPrevTn (by omega)
      exact hNotPrev (vertexTransfer hPPrev hvP)
    have hPrevP : TreeSequenceInitialSegment Tprev P :=
      commonPrefix hPrevStage hPStage (Nat.le_of_lt hPrevStrictP)
    obtain ⟨seed, hEligibility, hrouteOld, hseedP⟩ :
        ∃ seed : TreeSequence G e0,
          ((ett.series.data.kind j.castSucc =
                some TashkinovExtensionKind.PE ∧ seed = Tprev) ∨
            ((ett.series.data.kind j.castSucc =
                  some TashkinovExtensionKind.SE ∨
                ett.series.data.kind j.castSucc =
                  some TashkinovExtensionKind.RE) ∧
              ∃ f : E, ett.series.data.connectingEdges j.castSucc = {f} ∧
                TreeSequenceAdjoinEdge Tprev f seed)) ∧
          TashkinovAugmentationSequence
              (ett.series.data.coloring j.castSucc) seed Tj ∧
          TreeSequenceInitialSegment seed P := by
      have hcert := ett.series.certified j.castSucc
      generalize htarget : j.castSucc = target at hcert
      cases hcert with
      | initial triple seedLength initialColoring initialStored initialEdges
          initialKind initialVertex initialOutside initialDelta initialGamma
          initialClosure =>
          have hvals := congrArg Fin.val htarget
          simp at hvals
          omega
      | SE ci previousProper previousOneUncolored previousClosed
          previousNotStronglyClosed noRevisiting choice seriesAlternative
          currentColoring currentStored currentEdges currentKind currentVertex
          currentOutside currentDelta currentGamma adjoined adjoinedExactly
          closedExtension orderedExtension strictExtension =>
          have hciSucc : ci.succ = j.castSucc := htarget.symm
          have hnext : ci.succ.succ = j.succ.castSucc := by
            apply Fin.ext
            simp only [Fin.val_succ, Fin.val_castSucc]
            have hvals := congrArg Fin.val hciSucc
            simpa using congrArg Nat.succ hvals
          have hroute : TashkinovAugmentationSequence
              (ett.series.data.coloring ci.succ) adjoined Tj := by
            simpa only [Tj, hnext] using closedExtension.1
          have hseedStage : TreeSequenceInitialSegment adjoined Tj :=
            sequenceSegment hroute
          have hseedLe : adjoined.length ≤ P.length := by
            rcases adjoinedExactly with ⟨hlen, _, _⟩
            rw [hlen]
            have hprevEq : ett.series.data.tree ci.succ.castSucc = Tprev := by
              simpa only [Tprev, hciSucc]
            rw [hprevEq]
            omega
          have hseedP' : TreeSequenceInitialSegment adjoined P :=
            commonPrefix hseedStage hPStage hseedLe
          refine ⟨adjoined, ?_, hroute, hseedP'⟩
          right
          refine ⟨Or.inl ?_, choice.edge, ?_, ?_⟩
          · simpa only [hciSucc] using currentKind
          · simpa only [hciSucc] using currentEdges
          · simpa only [Tprev, hciSucc] using adjoinedExactly
      | PE ci previousProper previousOneUncolored previousClosed
          previousNotStronglyClosed noRevisiting choice seriesAlternativeFails
          gamma gammaRule secondStable secondStableProper
          secondStableOneUncolored secondStableRelation exitWitness
          currentColoring currentProper currentOneUncolored currentStored
          currentEdges currentKind currentVertex currentOutside currentDelta
          currentGamma closedExtension orderedExtension strictExtension =>
          have hciSucc : ci.succ = j.castSucc := htarget.symm
          have hnext : ci.succ.succ = j.succ.castSucc := by
            apply Fin.ext
            simp only [Fin.val_succ, Fin.val_castSucc]
            have hvals := congrArg Fin.val hciSucc
            simpa using congrArg Nat.succ hvals
          have hroute : TashkinovAugmentationSequence
              (ett.series.data.coloring ci.succ) Tprev Tj := by
            have hroute' := closedExtension.1
            rw [hnext] at hroute'
            simpa only [Tprev, Tj, hciSucc] using hroute'
          refine ⟨Tprev, ?_, hroute, hPrevP⟩
          left
          exact ⟨by simpa only [hciSucc] using currentKind, rfl⟩
      | RE ci previousProper previousOneUncolored previousClosed
          previousNotStronglyClosed available currentColoring currentStored
          currentEdges currentKind currentVertex currentOutside currentDelta
          currentGamma adjoined adjoinedExactly closedExtension orderedExtension
          strictExtension =>
          have hciSucc : ci.succ = j.castSucc := htarget.symm
          have hnext : ci.succ.succ = j.succ.castSucc := by
            apply Fin.ext
            simp only [Fin.val_succ, Fin.val_castSucc]
            have hvals := congrArg Fin.val hciSucc
            simpa using congrArg Nat.succ hvals
          have hroute : TashkinovAugmentationSequence
              (ett.series.data.coloring ci.succ) adjoined Tj := by
            simpa only [Tj, hnext] using closedExtension.1
          have hseedStage : TreeSequenceInitialSegment adjoined Tj :=
            sequenceSegment hroute
          have hseedLe : adjoined.length ≤ P.length := by
            rcases adjoinedExactly with ⟨hlen, _, _⟩
            rw [hlen]
            have hprevEq : ett.series.data.tree ci.succ.castSucc = Tprev := by
              simpa only [Tprev, hciSucc]
            rw [hprevEq]
            omega
          have hseedP' : TreeSequenceInitialSegment adjoined P :=
            commonPrefix hseedStage hPStage hseedLe
          refine ⟨adjoined, ?_, hroute, hseedP'⟩
          right
          refine ⟨Or.inr ?_, available.edge, ?_, ?_⟩
          · simpa only [hciSucc] using currentKind
          · simpa only [hciSucc] using currentEdges
          · simpa only [Tprev, hciSucc] using adjoinedExactly
    have hrouteOldP : TashkinovAugmentationSequence
        (ett.series.data.coloring j.castSucc) seed P :=
      TashkinovAugmentationSequenceRestrict
        (ett.series.data.coloring j.castSucc) seed P Tj
        hrouteOld hseedP hPStage
    have hrouteSigmaP : TashkinovAugmentationSequence sigma seed P :=
      transportRoute seed hrouteOldP
    have hrouteSigmaClosure : TashkinovAugmentationSequence
        sigma seed base.closure :=
      Relation.ReflTransGen.trans hrouteSigmaP hparallel.2.1.1
    have hclosureSeed : TashkinovClosure sigma seed base.closure :=
      ⟨hrouteSigmaClosure, hclosed⟩
    obtain ⟨lower, hround, hlowerMP, htrees, hdata⟩ :=
      CertifiedETTRestriction G k e0 input T phi ett hMP j.val
        (by omega) (by exact j.isLt)
    let lowerTerminal : Fin (lower.rounds + 1) := Fin.last lower.rounds
    have htreeLower : lower.series.data.tree lowerTerminal.castSucc =
        Tprev := by
      calc
        lower.series.data.tree lowerTerminal.castSucc =
            ett.series.data.tree
              (Fin.castLE (by omega) lowerTerminal.castSucc) :=
          htrees lowerTerminal.castSucc
        _ = Tprev := by
          change ett.series.data.tree _ =
            ett.series.data.tree j.castSucc.castSucc
          congr 1
          apply Fin.ext
          simp [lowerTerminal, hround]
    obtain ⟨hcolorLower, hstoredRawLower, hconnectingLower,
        hkindLower, hchosenLower, houtsideLower, hdeltaLower, hgammaLower,
        hstoredLower, hcertLower⟩ := hdata lowerTerminal
    have hcolorLower' : lower.series.data.coloring lowerTerminal =
        ett.series.data.coloring j.castSucc := by
      calc
        lower.series.data.coloring lowerTerminal =
            ett.series.data.coloring (Fin.castLE (by omega) lowerTerminal) :=
          hcolorLower
        _ = ett.series.data.coloring j.castSucc := by
          congr 1
          apply Fin.ext
          simp [lowerTerminal, hround]
    have hstoredLower' : TashkinovStoredColors lower.series.data
        lowerTerminal = TashkinovStoredColors ett.series.data j.castSucc := by
      calc
        TashkinovStoredColors lower.series.data lowerTerminal =
            TashkinovStoredColors ett.series.data
              (Fin.castLE (by omega) lowerTerminal) := hstoredLower
        _ = TashkinovStoredColors ett.series.data j.castSucc := by
          congr 1
          apply Fin.ext
          simp [lowerTerminal, hround]
    have hkindLower' : lower.series.data.kind lowerTerminal =
        ett.series.data.kind j.castSucc := by
      calc
        lower.series.data.kind lowerTerminal =
            ett.series.data.kind (Fin.castLE (by omega) lowerTerminal) :=
          hkindLower
        _ = ett.series.data.kind j.castSucc := by
          congr 1
          apply Fin.ext
          simp [lowerTerminal, hround]
    have hconnectingLower' : lower.series.data.connectingEdges lowerTerminal =
        ett.series.data.connectingEdges j.castSucc := by
      calc
        lower.series.data.connectingEdges lowerTerminal =
            ett.series.data.connectingEdges
              (Fin.castLE (by omega) lowerTerminal) := hconnectingLower
        _ = ett.series.data.connectingEdges j.castSucc := by
          congr 1
          apply Fin.ext
          simp [lowerTerminal, hround]
    have hstableLower : StableColoring
        (lower.series.data.tree lowerTerminal.castSucc)
        (TashkinovStoredColors lower.series.data lowerTerminal)
        (lower.series.data.coloring lowerTerminal) sigma := by
      rw [htreeLower, hstoredLower', hcolorLower']
      simpa [Tprev] using hcurrent.2 (by simpa using hjPositive)
    have hmod : ModColoring lower sigma :=
      ctx.lowerSix lower (by omega) (by omega) hlowerMP sigma hproper hone
        (by simpa [lowerTerminal] using hstableLower)
    have hPrevClosure : TreeSequenceInitialSegment Tprev base.closure :=
      segmentTrans hPrevP hPClosure
    have hLowerTerminalClosure : TreeSequenceInitialSegment
        (lower.series.data.tree lowerTerminal.castSucc) base.closure := by
      rw [htreeLower]
      exact hPrevClosure
    have hLowerStrict :
        (lower.series.data.tree lowerTerminal.castSucc).length <
          base.closure.length := by
      rw [htreeLower]
      exact lt_of_lt_of_le hPrevStrictP hPClosure.1
    have hEligibilityLower :
        (lower.series.data.kind lowerTerminal =
              some TashkinovExtensionKind.PE ∧
            TashkinovAugmentationSequence sigma
              (lower.series.data.tree lowerTerminal.castSucc) base.closure) ∨
          ((lower.series.data.kind lowerTerminal =
                some TashkinovExtensionKind.SE ∨
              lower.series.data.kind lowerTerminal =
                some TashkinovExtensionKind.RE) ∧
            ∃ (f : E) (seed' : TreeSequence G e0),
              lower.series.data.connectingEdges lowerTerminal = {f} ∧
                TreeSequenceAdjoinEdge
                  (lower.series.data.tree lowerTerminal.castSucc) f seed' ∧
                TashkinovAugmentationSequence sigma seed' base.closure) := by
      rcases hEligibility with hparallelSeed | hnonparallelSeed
      · left
        refine ⟨hkindLower'.trans hparallelSeed.1, ?_⟩
        rw [htreeLower]
        simpa only [hparallelSeed.2] using hrouteSigmaClosure
      · right
        rcases hnonparallelSeed with ⟨hkind, f, hedgeSet, hadjoin⟩
        refine ⟨?_, f, seed, ?_, ?_, hrouteSigmaClosure⟩
        · rcases hkind with hse | hre
          · exact Or.inl (hkindLower'.trans hse)
          · exact Or.inr (hkindLower'.trans hre)
        · exact hconnectingLower'.trans hedgeSet
        · rw [htreeLower]
          exact hadjoin
    obtain ⟨corr⟩ : Nonempty
        (CorrespondingExtendedTashkinovTree G k e0 lower sigma base.closure) :=
      hmod.2.2 base.closure
        (by simpa [lowerTerminal] using hLowerTerminalClosure)
        (by simpa [lowerTerminal] using hLowerStrict)
        (by simpa [lowerTerminal] using hEligibilityLower)
    have hreplacementMP : MaximumProperty corr.replacementETT :=
      MaximumPropertyTransport G k e0 lower sigma hmod base.closure corr
        hlowerMP
    have hreplacementPositive : 0 < corr.replacementETT.rounds := by
      exact corr.replacementETT.roundsPositive
    have hreplacementBefore : corr.replacementETT.rounds < ett.rounds := by
      rw [corr.rungAgreement, hround]
      exact j.isLt
    have helementary : ColoredVertexSetElementary G sigma
        (TreeSequenceVertexSet base.closure) :=
      ctx.lowerOne corr.replacementETT hreplacementPositive
        hreplacementBefore hreplacementMP
    let replacementTerminal : Fin (corr.replacementETT.rounds + 1) :=
      Fin.last corr.replacementETT.rounds
    let L : TreeSequence G e0 :=
      corr.replacementETT.series.data.tree
        (Fin.last (corr.replacementETT.rounds + 1))
    have hselfStable : StableColoring L
        (TashkinovStoredColors corr.replacementETT.series.data
          replacementTerminal)
        (corr.replacementETT.series.data.coloring replacementTerminal)
        sigma := by
      have hgenerating : sigma =
          corr.replacementETT.series.data.coloring replacementTerminal := by
        simpa [replacementTerminal] using
          corr.replacementETT.generatingColoring
      rw [← hgenerating]
      let a : {rho : PartialEdgeColoring E k //
          IsProperEdgeColoring G rho ∧ IsOneEdgeUncolored rho e0} :=
        ⟨sigma, hproper, hone⟩
      have hrefl := (sc2 G e0 L
        (TashkinovStoredColors corr.replacementETT.series.data
          replacementTerminal)).refl a
      simpa [a] using hrefl
    have hclosureL : TreeSequenceInitialSegment base.closure L := by
      simpa [L] using corr.replacementETT.belowFinal
    have hinterchangeable : ∀ alpha beta : Fin k,
        (alpha ∈ TreeMissingColors sigma base.closure ∨
          beta ∈ TreeMissingColors sigma base.closure) →
        TreeInterchangeable G base.closure sigma alpha beta := by
      intro alpha beta hmissing
      have hmissingL : alpha ∈ TreeMissingColors sigma L ∨
          beta ∈ TreeMissingColors sigma L := by
        rcases hmissing with ha | hb
        · exact Or.inl (missingTransfer hclosureL ha)
        · exact Or.inr (missingTransfer hclosureL hb)
      have hinterL : TreeInterchangeable G L sigma alpha beta := by
        have h := ctx.lowerTwo corr.replacementETT hreplacementPositive
          hreplacementBefore hreplacementMP sigma hproper hone
          (by simpa [replacementTerminal, L] using hselfStable)
          alpha beta (by simpa [L] using hmissingL)
        simpa [L] using h
      unfold TreeInterchangeable at hinterL ⊢
      intro z w hz hw hzMeet hwMeet
      apply hinterL z w hz hw
      · obtain ⟨x, hx, hxComponent⟩ := hzMeet
        exact ⟨x, vertexTransfer hclosureL hx, hxComponent⟩
      · obtain ⟨x, hx, hxComponent⟩ := hwMeet
        exact ⟨x, vertexTransfer hclosureL hx, hxComponent⟩
    exact ⟨helementary, hclosed, hinterchangeable⟩
  · have hjZero : j.val = 0 := by omega
    have hjZeroIndex : j.castSucc = (0 : Fin (ett.rounds + 1)) := by
      apply Fin.ext
      simpa using hjZero
    have hTjOne : Tj = ett.series.data.tree
        (1 : Fin (ett.rounds + 2)) := by
      change ett.series.data.tree j.succ.castSucc =
        ett.series.data.tree (1 : Fin (ett.rounds + 2))
      congr 1
      apply Fin.ext
      simp
      exact hjZero
    have hcert := ett.series.certified j.castSucc
    generalize htarget : j.castSucc = target at hcert
    cases hcert with
    | initial triple seedLength initialColoring initialStored initialEdges
        initialKind initialVertex initialOutside initialDelta initialGamma
        initialClosure =>
        let seed : TreeSequence G e0 := ett.series.data.tree 0
        have hrouteOld : TashkinovAugmentationSequence
            (ett.series.data.coloring j.castSucc) seed Tj := by
          simpa only [seed, hjZeroIndex, hTjOne] using initialClosure.1
        have hseedStage : TreeSequenceInitialSegment seed Tj :=
          sequenceSegment hrouteOld
        have hseedLe : seed.length ≤ P.length := by
          have hseedLength : seed.length = 1 := by
            simpa only [seed] using seedLength
          rw [hseedLength, hPLength]
          exact base.supportPositive
        have hseedP : TreeSequenceInitialSegment seed P :=
          commonPrefix hseedStage hPStage hseedLe
        have hrouteOldP : TashkinovAugmentationSequence
            (ett.series.data.coloring j.castSucc) seed P :=
          TashkinovAugmentationSequenceRestrict
            (ett.series.data.coloring j.castSucc) seed P Tj
            hrouteOld hseedP hPStage
        have hrouteSigmaP : TashkinovAugmentationSequence sigma seed P :=
          transportRoute seed hrouteOldP
        have hrouteSigmaClosure : TashkinovAugmentationSequence
            sigma seed base.closure :=
          Relation.ReflTransGen.trans hrouteSigmaP hparallel.2.1.1
        have hclosureSigma : TashkinovClosure sigma seed base.closure :=
          ⟨hrouteSigmaClosure, hclosed⟩
        let zeroData : TashkinovSeriesData G k 0 e0 := {
          tree := Fin.cases seed (fun _ => base.closure)
          coloring := fun _ => sigma
          stored := fun _ => ∅
          connectingEdges := fun _ => ∅
          kind := fun _ => none
          chosenVertex := fun _ => none
          outsideVertex := fun _ => none
          delta := fun _ => none
          gamma := fun _ => none }
        have htripleSigma : KTriple G k e0 sigma :=
          ⟨triple.1, triple.2.1, triple.2.2.1, hproper, hone⟩
        let zeroSeries : TashkinovSeries G k 0 e0 sigma := {
          data := zeroData
          certified := by
            intro i
            have hi : i = 0 := Fin.eq_zero i
            subst i
            exact TashkinovSeriesStep.initial htripleSigma
              (by simpa [zeroData, seed] using seedLength)
              rfl rfl rfl rfl rfl rfl rfl rfl hclosureSigma }
        have htreeOne : zeroSeries.data.tree (1 : Fin 2) =
            base.closure := by
          rfl
        have htechnical := TechnicalTheoremBase G k 0 e0 sigma zeroSeries
        have helementary : ColoredVertexSetElementary G sigma
            (TreeSequenceVertexSet base.closure) := by
          rw [← htreeOne]
          exact htechnical.1
        have hselfStable : StableColoring base.closure
            (TashkinovStoredColors zeroSeries.data (0 : Fin 1))
            (zeroSeries.data.coloring 0) sigma := by
          have hstoredZero : TashkinovStoredColors zeroSeries.data
              (0 : Fin 1) = ∅ := by
            simp [TashkinovStoredColors]
          have hcolorZero : zeroSeries.data.coloring (0 : Fin 1) = sigma := by
            rfl
          rw [hstoredZero, hcolorZero]
          let a : {rho : PartialEdgeColoring E k //
              IsProperEdgeColoring G rho ∧ IsOneEdgeUncolored rho e0} :=
            ⟨sigma, hproper, hone⟩
          have hrefl := (sc2 G e0 base.closure (∅ : Finset (Fin k))).refl a
          simpa [a] using hrefl
        have hinterchangeable : ∀ alpha beta : Fin k,
            (alpha ∈ TreeMissingColors sigma base.closure ∨
              beta ∈ TreeMissingColors sigma base.closure) →
            TreeInterchangeable G base.closure sigma alpha beta := by
          intro alpha beta hmissing
          have h := htechnical.2 sigma hproper hone
            (by simpa [htreeOne] using hselfStable) alpha beta
            (by simpa [htreeOne] using hmissing)
          simpa [htreeOne] using h
        exact ⟨helementary, hclosed, hinterchangeable⟩
    | SE ci previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed noRevisiting choice seriesAlternative
        currentColoring currentStored currentEdges currentKind currentVertex
        currentOutside currentDelta currentGamma adjoined adjoinedExactly
        closedExtension orderedExtension strictExtension =>
        have hvals := congrArg Fin.val htarget
        simp at hvals
        omega
    | PE ci previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed noRevisiting choice seriesAlternativeFails
        gamma gammaRule secondStable secondStableProper
        secondStableOneUncolored secondStableRelation exitWitness
        currentColoring currentProper currentOneUncolored currentStored
        currentEdges currentKind currentVertex currentOutside currentDelta
        currentGamma closedExtension orderedExtension strictExtension =>
        have hvals := congrArg Fin.val htarget
        simp at hvals
        omega
    | RE ci previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed available currentColoring currentStored
        currentEdges currentKind currentVertex currentOutside currentDelta
        currentGamma adjoined adjoinedExactly closedExtension orderedExtension
        strictExtension =>
        have hvals := congrArg Fin.val htarget
        simp at hvals
        omega
