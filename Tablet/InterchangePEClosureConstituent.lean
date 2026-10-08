import Tablet.BoundaryColorVertex
import Tablet.CertifiedETTPredecessor
import Tablet.CertifiedETTRestriction
import Tablet.ColoredVertexSetElementary
import Tablet.CombinedStableClosurePreserved
import Tablet.CombinedStableColoring
import Tablet.CorrespondingExtendedTashkinovTree
import Tablet.DefectiveColor
import Tablet.ETTFirstAppearanceIndex
import Tablet.ExtendedTashkinovTree
import Tablet.ExtensionRules
import Tablet.HierarchyBase
import Tablet.IsOneEdgeUncolored
import Tablet.IsProperEdgeColoring
import Tablet.KTriple
import Tablet.LooplessMultigraph
import Tablet.MaximumProperty
import Tablet.MaximumPropertyTransport
import Tablet.ModColoring
import Tablet.OrderedTreeUnion
import Tablet.PartialEdgeColoring
import Tablet.P2634_T1_PETerminalFacts
import Tablet.StableColoring
import Tablet.StableColoringBeforeVertex
import Tablet.TashkinovAugmentation
import Tablet.TashkinovAugmentationSequence
import Tablet.TashkinovAugmentationSequenceInitialSegment
import Tablet.TashkinovAugmentationSequenceRestrict
import Tablet.TashkinovClosure
import Tablet.TashkinovExtensionKind
import Tablet.TashkinovSeries
import Tablet.TashkinovSeriesData
import Tablet.TashkinovSeriesStep
import Tablet.TashkinovStoredColors
import Tablet.Td
import Tablet.TechnicalTheoremBase
import Tablet.TreeInterchangeable
import Tablet.TreeMissingColors
import Tablet.TreeSequence
import Tablet.TreeSequenceAdjoinEdge
import Tablet.TreeSequenceInitialSegment
import Tablet.TreeSequenceInitialSegmentVertexSetSubset
import Tablet.TreeSequencePrefix
import Tablet.TreeSequenceVertexSet
import Tablet.TreeVertexOrder
import Tablet.TwoColorComponent

-- [TABLET NODE: InterchangePEClosureConstituent]
theorem InterchangePEClosureConstituent {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (generating sigma : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T generating)
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
    (hPE : ett.series.data.kind (Fin.last ett.rounds) =
      some TashkinovExtensionKind.PE)
    (base : HierarchyBase ett generating)
    (hproper : IsProperEdgeColoring G sigma)
    (hone : IsOneEdgeUncolored sigma e0)
    (hstable : CombinedStableColoring
      (ett.series.data.tree (Fin.last ett.rounds).castSucc)
      base.closure
      (TashkinovStoredColors ett.series.data (Fin.last ett.rounds))
      generating sigma)
    (alpha beta : Fin k) :
    alpha ∈ TreeMissingColors sigma base.closure →
      TreeInterchangeable G base.closure sigma alpha beta := by
-- BODY
  classical
  intro hmissing
  have segmentTrans {A B C : TreeSequence G e0}
      (hAB : TreeSequenceInitialSegment A B)
      (hBC : TreeSequenceInitialSegment B C) :
      TreeSequenceInitialSegment A C := by
    refine ⟨hAB.1.trans hBC.1, ?_, ?_⟩
    · intro i
      exact (hBC.2.1 (Fin.castLE (Nat.succ_le_succ hAB.1) i)).trans
        (hAB.2.1 i)
    · intro i
      exact (hBC.2.2 (Fin.castLE hAB.1 i)).trans (hAB.2.2 i)
  have commonPrefix {A B C : TreeSequence G e0}
      (hAC : TreeSequenceInitialSegment A C)
      (hBC : TreeSequenceInitialSegment B C) (hlen : A.length ≤ B.length) :
      TreeSequenceInitialSegment A B := by
    refine ⟨hlen, ?_, ?_⟩
    · intro i
      exact (hBC.2.1 (Fin.castLE (Nat.succ_le_succ hlen) i)).symm.trans
        (hAC.2.1 i)
    · intro i
      exact (hBC.2.2 (Fin.castLE hlen i)).symm.trans (hAC.2.2 i)
  have stepSegment (i : Fin (ett.rounds + 1)) :
      TreeSequenceInitialSegment (ett.series.data.tree i.castSucc)
        (ett.series.data.tree i.succ) := by
    cases ett.series.certified i with
    | initial triple seedLength initialColoring initialStored initialEdges
        initialKind initialVertex initialOutside initialDelta initialGamma
        initialClosure =>
      exact TashkinovAugmentationSequenceInitialSegment _ _ _ initialClosure.1
    | SE => assumption
    | PE => assumption
    | RE => assumption
  have stageSegment (a b : ℕ) (hab : a ≤ b) (hb : b ≤ ett.rounds + 1) :
      TreeSequenceInitialSegment
        (ett.series.data.tree ⟨a, by omega⟩)
        (ett.series.data.tree ⟨b, by omega⟩) := by
    induction b, hab using Nat.le_induction with
    | base => exact ⟨le_rfl, (fun _ => rfl), (fun _ => rfl)⟩
    | succ b hab ih =>
      have hprev := ih (by omega)
      have hstep := stepSegment ⟨b, by omega⟩
      exact segmentTrans hprev hstep
  let n : Fin (ett.rounds + 1) := Fin.last ett.rounds
  let Tn := ett.series.data.tree n.castSucc
  let B := TreeSequencePrefix Tn base.supportPosition.val
    base.supportPositive (Nat.le_of_lt_succ base.supportPosition.isLt)
  let v := Tn.vertex base.supportPosition
  have hBTn : TreeSequenceInitialSegment B Tn :=
    ⟨Nat.le_of_lt_succ base.supportPosition.isLt,
      (fun _ => rfl), (fun _ => rfl)⟩
  have hTnT : TreeSequenceInitialSegment Tn T := ett.abovePenultimate
  have hBT := segmentTrans hBTn hTnT
  have hvTn : v ∈ TreeSequenceVertexSet Tn := by
    simp [v, TreeSequenceVertexSet]
  have hvT : v ∈ TreeSequenceVertexSet T :=
    TreeSequenceInitialSegmentVertexSetSubset hTnT hvTn
  have hvB : B.vertex (Fin.last B.length) = v := by
    dsimp [B, TreeSequencePrefix, v]
    congr 1
  have hchosen : ett.series.data.chosenVertex n = some v :=
    (base.parallel hPE).1
  obtain ⟨hproperGen, honeGen, _⟩ := P2634_T1_PETerminalFacts ett hPE
  have hclosure : TashkinovClosure sigma B base.closure :=
    (CombinedStableClosurePreserved G k e0 input T generating generating sigma
      ett hpositive base ett.generatingColoring hPE hproperGen honeGen
      hproper hone hstable).2.2
  -- The zero-based index j corresponds to first appearance in stage j + 1.
  let candidates : Finset (Fin (ett.rounds + 1)) :=
    Finset.univ.filter fun i =>
      v ∈ TreeSequenceVertexSet (ExtendedTashkinovLadderStage ett i)
  have hcandidates : candidates.Nonempty := by
    refine ⟨Fin.last ett.rounds, ?_⟩
    simp only [candidates, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [ExtendedTashkinovLadderStage, Fin.lastCases_last]
    exact hvT
  let j := candidates.min' hcandidates
  have hfirst : ETTFirstAppearanceIndex ett v hvT = j.val + 1 := by
    unfold ETTFirstAppearanceIndex
    dsimp
    apply congrArg (fun i : Fin (ett.rounds + 1) => i.val + 1)
    apply (Finset.min'_eq_iff _ _ j).mpr
    constructor
    · have hmem := Finset.min'_mem candidates hcandidates
      change j ∈ candidates at hmem
      simpa only [candidates, Finset.mem_filter, Finset.mem_univ, true_and] using hmem
    · intro b hb
      exact Finset.min'_le candidates b (by
        simpa only [candidates, Finset.mem_filter, Finset.mem_univ, true_and] using hb)
  let q : Fin ett.rounds := ⟨ett.rounds - 1, by omega⟩
  have hq : q.succ = n := by
    apply Fin.ext
    dsimp [q, n]
    omega
  have hjbound : j.val + 1 ≤ ett.rounds := by
    have hbound := ExtensionRulesPEFirstAppearanceBound G k e0 input T
      generating ett q v (by simpa [hq] using hPE)
      (by simpa [hq] using hchosen) hvT
    rw [hfirst] at hbound
    dsimp [q] at hbound
    omega
  let p : Fin ett.rounds := ⟨j.val, by omega⟩
  have hpj : p.castSucc = j := by apply Fin.ext; rfl
  let A := ett.series.data.tree j.succ
  let P := ett.series.data.tree j.castSucc
  have hvA : v ∈ TreeSequenceVertexSet A := by
    have hmem := Finset.min'_mem candidates hcandidates
    have hvstage : v ∈ TreeSequenceVertexSet
        (ExtendedTashkinovLadderStage ett j) := (Finset.mem_filter.mp hmem).2
    rw [← hpj, ExtendedTashkinovLadderStage, Fin.lastCases_castSucc] at hvstage
    have hidx : p.succ.castSucc = j.succ := by apply Fin.ext; rfl
    simpa only [hidx, A] using hvstage
  have hATn : TreeSequenceInitialSegment A Tn :=
    stageSegment (j.val + 1) ett.rounds hjbound (by omega)
  have hPA : TreeSequenceInitialSegment P A := stepSegment j
  have hBA : TreeSequenceInitialSegment B A := by
    obtain ⟨iv, hiv⟩ := (show ∃ iv, A.vertex iv = v from by
      simpa [TreeSequenceVertexSet] using hvA)
    have hivEq : Fin.castLE (Nat.succ_le_succ hATn.1) iv =
        base.supportPosition :=
      Tn.vertex_injective ((hATn.2.1 iv).trans hiv)
    have hlen : B.length ≤ A.length := by
      have := congrArg Fin.val hivEq
      dsimp [B, TreeSequencePrefix] at ⊢
      simp only [Fin.val_castLE] at this
      omega
    exact commonPrefix hBTn hATn hlen
  have hbefore := (ExtensionRules G k e0 input T generating ett hMP hpositive
    (fun lower hp hlt hmax => hlower lower hp hlt hmax)).1 q v
      (by simpa [hq] using hPE) (by simpa [hq] using hchosen) hvT j hfirst
      sigma hproper hone (by simpa only [hq, n, ← ett.generatingColoring] using hstable.1)
  have hvNotP (hj : 0 < j.val) : v ∉ TreeSequenceVertexSet P := by
    intro hvP
    let u : Fin ett.rounds := ⟨j.val - 1, by omega⟩
    have huj : u.succ = j := by apply Fin.ext; dsimp [u]; omega
    have huMem : u.castSucc ∈ candidates := by
      simp only [candidates, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [ExtendedTashkinovLadderStage, Fin.lastCases_castSucc, huj]
      exact hvP
    have hle := Finset.min'_le candidates u.castSucc huMem
    change j ≤ u.castSucc at hle
    have := Fin.le_iff_val_le_val.mp hle
    dsimp [u] at this
    omega
  have hPBstrict (hj : 0 < j.val) : P.length < B.length := by
    by_contra hnot
    have hBP := commonPrefix hBA hPA (by omega)
    apply hvNotP hj
    apply TreeSequenceInitialSegmentVertexSetSubset hBP
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨Fin.last B.length, hvB⟩
  have vertexBefore {X : TreeSequence G e0}
      (hXB : TreeSequenceInitialSegment X B) (hlen : X.length < B.length)
      {x : V} (hx : x ∈ TreeSequenceVertexSet X) :
      x ∈ TreeVerticesBefore T v hvT := by
    obtain ⟨ix, hix⟩ := (show ∃ ix, X.vertex ix = x from by
      simpa [TreeSequenceVertexSet] using hx)
    have hXT := segmentTrans hXB hBT
    refine Finset.mem_filter.mpr
      ⟨TreeSequenceInitialSegmentVertexSetSubset hXT hx, ?_⟩
    refine ⟨Fin.castLE (Nat.succ_le_succ hXT.1) ix,
      Fin.castLE (Nat.succ_le_succ hBT.1) (Fin.last B.length),
      (hXT.2.1 ix).trans hix, (hBT.2.1 _).trans hvB, ?_⟩
    simp only [Fin.val_castLE, Fin.val_last]
    omega
  -- This transports the step adjoining the support as well as all earlier steps.
  have transportRoute (S : TreeSequence G e0)
      (hSA : TashkinovAugmentationSequence (ett.series.data.coloring j) S A)
      (hSB : TreeSequenceInitialSegment S B) :
      TashkinovAugmentationSequence sigma S B := by
    have hroute := TashkinovAugmentationSequenceRestrict _ S B A hSA hSB hBA
    clear hSA hSB
    unfold TashkinovAugmentationSequence at hroute ⊢
    induction hroute using Relation.ReflTransGen.head_induction_on with
    | refl => exact Relation.ReflTransGen.refl
    | @head X Y hstep htail ih =>
      have hYB := TashkinovAugmentationSequenceInitialSegment _ _ _ htail
      rcases hstep with ⟨hlen, hXY, c, hcolor, hcmissing⟩
      have hXB := segmentTrans hXY hYB
      have hlt : X.length < B.length := by have := hYB.1; omega
      have beforeX : ∀ x ∈ TreeSequenceVertexSet X,
          x ∈ TreeVerticesBefore T v hvT := fun x hx => vertexBefore hXB hlt hx
      obtain ⟨x, hx, hxc⟩ := Finset.mem_biUnion.mp hcmissing
      have hcsigma : c ∈ TreeMissingColors sigma X := by
        apply Finset.mem_biUnion.mpr
        exact ⟨x, hx, (hbefore.1.2 x (beforeX x hx)) ▸ hxc⟩
      let last : Fin Y.length := Fin.cast hlen.symm (Fin.last X.length)
      obtain ⟨i, hi⟩ := Y.attaches last
      let ix : Fin (X.length + 1) := ⟨i.val, by
        have := i.isLt
        change i.val < last.val + 1 at this
        dsimp [last] at this
        omega⟩
      have hinc : Incident G (X.vertex ix) (Y.edge last) := by
        change X.vertex ix ∈ G.ends (Y.edge last)
        rw [hi]
        have heq : Y.vertex (Fin.castLT i
            (Nat.lt_trans i.isLt (Nat.succ_lt_succ last.isLt))) = X.vertex ix := by
          exact hXY.2.1 ix
        rw [heq]
        exact Sym2.mem_mk_right _ _
      have hix : X.vertex ix ∈ TreeSequenceVertexSet X := by
        simp [TreeSequenceVertexSet]
      have heq := hbefore.1.1 (Y.edge last)
        ⟨X.vertex ix, beforeX _ hix, hinc⟩
        ⟨c, Finset.mem_union_left _
          (Finset.mem_biUnion.mpr ⟨x, beforeX x hx, hxc⟩), hcolor⟩
      exact Relation.ReflTransGen.head
        ⟨hlen, hXY, c, heq.trans hcolor, hcsigma⟩ ih
  have seedData (t : Fin (ett.rounds + 1)) :
      ∃ S : TreeSequence G e0,
        TashkinovAugmentationSequence (ett.series.data.coloring t) S
          (ett.series.data.tree t.succ) ∧
        ((t.val = 0 ∧ S = ett.series.data.tree 0 ∧ S.length = 1) ∨
          (ett.series.data.kind t = some TashkinovExtensionKind.PE ∧
            S = ett.series.data.tree t.castSucc) ∨
          ((ett.series.data.kind t = some TashkinovExtensionKind.SE ∨
              ett.series.data.kind t = some TashkinovExtensionKind.RE) ∧
            ∃ f : E, ett.series.data.connectingEdges t = {f} ∧
              TreeSequenceAdjoinEdge (ett.series.data.tree t.castSucc) f S)) := by
    cases ett.series.certified t with
    | initial triple seedLength initialColoring initialStored initialEdges
        initialKind initialVertex initialOutside initialDelta initialGamma
        initialClosure =>
      exact ⟨_, initialClosure.1, Or.inl ⟨rfl, rfl, seedLength⟩⟩
    | SE i previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed noRevisiting choice seriesAlternative
        currentColoring currentStored currentEdges currentKind currentVertex
        currentOutside currentDelta currentGamma adjoined adjoinedExactly
        closedExtension orderedExtension strictExtension =>
      exact ⟨adjoined, closedExtension.1,
        Or.inr (Or.inr ⟨Or.inl currentKind, choice.edge, currentEdges, adjoinedExactly⟩)⟩
    | PE i previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed noRevisiting choice seriesAlternativeFails
        gamma gammaRule secondStable secondStableProper
        secondStableOneUncolored secondStableRelation exitWitness
        currentColoring currentProper currentOneUncolored currentStored
        currentEdges currentKind currentVertex currentOutside currentDelta
        currentGamma closedExtension orderedExtension strictExtension =>
      exact ⟨_, closedExtension.1, Or.inr (Or.inl ⟨currentKind, rfl⟩)⟩
    | RE i previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed available currentColoring currentStored
        currentEdges currentKind currentVertex currentOutside currentDelta
        currentGamma adjoined adjoinedExactly closedExtension orderedExtension
        strictExtension =>
      exact ⟨adjoined, closedExtension.1,
        Or.inr (Or.inr ⟨Or.inr currentKind, available.edge, currentEdges, adjoinedExactly⟩)⟩
  obtain ⟨S, hSA, hseed⟩ := seedData j
  have hSlen : S.length ≤ B.length := by
    rcases hseed with ⟨hj, hs, hlen⟩ | ⟨hkind, hs⟩ | ⟨hkind, f, hf, hadjoin⟩
    · rw [hlen]
      exact B.positive
    · rw [hs]
      by_cases hj : 0 < j.val
      · exact le_of_lt (hPBstrict hj)
      · have hjzero : j = 0 := by apply Fin.ext; change j.val = 0; omega
        have hkindzero : ett.series.data.kind 0 = none := by
          cases ett.series.certified 0 with
          | initial => assumption
        rw [hjzero, hkindzero] at hkind
        cases hkind
    · obtain ⟨hlen, _, _⟩ := hadjoin
      have hj : 0 < j.val := by
        by_contra hn
        have hjzero : j = 0 := by apply Fin.ext; change j.val = 0; omega
        have hkindzero : ett.series.data.kind 0 = none := by
          cases ett.series.certified 0 with
          | initial => assumption
        rw [hjzero, hkindzero] at hkind
        rcases hkind with hkind | hkind <;> cases hkind
      have hstrict := hPBstrict hj
      dsimp [P] at hstrict
      omega
  have hSB : TreeSequenceInitialSegment S B :=
    commonPrefix (TashkinovAugmentationSequenceInitialSegment _ _ _ hSA) hBA hSlen
  have hSR : TashkinovAugmentationSequence sigma S base.closure :=
    (transportRoute S hSA hSB).trans hclosure.1
  have hBR := TashkinovAugmentationSequenceInitialSegment _ _ _ hclosure.1
  by_cases hj : 0 < j.val
  · have hjlt : j.val < ett.rounds := by omega
    obtain ⟨restricted, hr, hmax, htrees, hdata⟩ :=
      CertifiedETTRestriction G k e0 input T generating ett hMP j.val hj hjlt
    let rn : Fin (restricted.rounds + 1) := Fin.last restricted.rounds
    have hidx : Fin.castLE (by omega : restricted.rounds + 1 ≤ ett.rounds + 1) rn = j := by
      apply Fin.ext
      simpa only [rn, Fin.val_castLE, Fin.val_last] using hr
    have htidx : Fin.castLE (by omega : restricted.rounds + 2 ≤ ett.rounds + 2)
        rn.castSucc = j.castSucc := by
      apply Fin.ext
      simpa only [rn, Fin.val_castLE, Fin.val_castSucc, Fin.val_last] using hr
    have htree : restricted.series.data.tree rn.castSucc = P := by
      simpa only [htidx, P] using htrees rn.castSucc
    have hcolor : restricted.series.data.coloring rn = ett.series.data.coloring j := by
      simpa only [hidx] using (hdata rn).1
    have hstored : TashkinovStoredColors restricted.series.data rn =
        TashkinovStoredColors ett.series.data j := by
      simpa only [hidx] using (hdata rn).2.2.2.2.2.2.2.2.1
    have hkind : restricted.series.data.kind rn = ett.series.data.kind j := by
      simpa only [hidx] using (hdata rn).2.2.2.1
    have hedges : restricted.series.data.connectingEdges rn =
        ett.series.data.connectingEdges j := by
      simpa only [hidx] using (hdata rn).2.2.1
    have hmod : ModColoring restricted sigma := by
      apply Td G k e0 input _ _ restricted hmax (by omega)
        (fun lower hp hlt hmax => hlower lower hp (by omega) hmax)
        sigma hproper hone
      change StableColoring (restricted.series.data.tree rn.castSucc)
        (TashkinovStoredColors restricted.series.data rn)
        (restricted.series.data.coloring rn) sigma
      rw [htree, hstored, hcolor]
      exact hbefore.2 hj
    have hPR : TreeSequenceInitialSegment P base.closure :=
      segmentTrans (commonPrefix hPA hBA (le_of_lt (hPBstrict hj))) hBR
    have hstrict : P.length < base.closure.length :=
      lt_of_lt_of_le (hPBstrict hj) hBR.1
    have hextension :
        ((restricted.series.data.kind rn = some TashkinovExtensionKind.PE ∧
            TashkinovAugmentationSequence sigma
              (restricted.series.data.tree rn.castSucc) base.closure) ∨
          ((restricted.series.data.kind rn = some TashkinovExtensionKind.SE ∨
              restricted.series.data.kind rn = some TashkinovExtensionKind.RE) ∧
            ∃ (f : E) (seed : TreeSequence G e0),
              restricted.series.data.connectingEdges rn = {f} ∧
                TreeSequenceAdjoinEdge (restricted.series.data.tree rn.castSucc) f seed ∧
                TashkinovAugmentationSequence sigma seed base.closure)) := by
      rw [hkind, htree, hedges]
      rcases hseed with ⟨hjzero, _, _⟩ | ⟨hPEj, hs⟩ | ⟨hSEj, f, hf, hadjoin⟩
      · omega
      · exact Or.inl ⟨hPEj, by simpa only [hs, P] using hSR⟩
      · exact Or.inr ⟨hSEj, f, S, hf, hadjoin, hSR⟩
    obtain ⟨corr⟩ := hmod.2.2 base.closure
      (by change TreeSequenceInitialSegment (restricted.series.data.tree rn.castSucc) _
          rw [htree]
          exact hPR)
      (by change (restricted.series.data.tree rn.castSucc).length < _
          rw [htree]
          exact hstrict) hextension
    have hmaxCorr := MaximumPropertyTransport G k e0 restricted sigma hmod
      base.closure corr hmax
    have hroundCorr : corr.replacementETT.rounds < ett.rounds := by
      rw [corr.rungAgreement, hr]
      exact hjlt
    have htwo := (hlower corr.replacementETT
      (by have := corr.replacementETT.roundsPositive; omega) hroundCorr hmaxCorr).2.1
    let L := corr.replacementETT.series.data.tree
      (Fin.last (corr.replacementETT.rounds + 1))
    have hRL : TreeSequenceInitialSegment base.closure L :=
      corr.replacementETT.belowFinal
    have hmissingL : alpha ∈ TreeMissingColors sigma L := by
      obtain ⟨x, hx, hxc⟩ := Finset.mem_biUnion.mp hmissing
      exact Finset.mem_biUnion.mpr
        ⟨x, TreeSequenceInitialSegmentVertexSetSubset hRL hx, hxc⟩
    have hreflexive : StableColoring L
        (TashkinovStoredColors corr.replacementETT.series.data
          (Fin.last corr.replacementETT.rounds))
        (corr.replacementETT.series.data.coloring
          (Fin.last corr.replacementETT.rounds)) sigma := by
      rw [← corr.replacementETT.generatingColoring]
      exact ⟨(by intro f hf hc; rfl), (by intro x hx; rfl)⟩
    have hinterchange := htwo sigma hproper hone hreflexive alpha beta (Or.inl hmissingL)
    intro z w hz hw hzR hwR
    obtain ⟨x, hx, hxz⟩ := hzR
    obtain ⟨y, hy, hyw⟩ := hwR
    exact hinterchange z w hz hw
      ⟨x, TreeSequenceInitialSegmentVertexSetSubset hRL hx, hxz⟩
      ⟨y, TreeSequenceInitialSegmentVertexSetSubset hRL hy, hyw⟩
  · have hjzero : j = 0 := by apply Fin.ext; change j.val = 0; omega
    have hkindzero : ett.series.data.kind 0 = none := by
      cases ett.series.certified 0 with
      | initial => assumption
    have hs : S = ett.series.data.tree 0 := by
      rcases hseed with ⟨_, hs, _⟩ | ⟨hkind, _⟩ | ⟨hkind, _⟩
      · exact hs
      · rw [hjzero, hkindzero] at hkind
        cases hkind
      · rw [hjzero, hkindzero] at hkind
        rcases hkind with hkind | hkind <;> cases hkind
    have hseedLength : (ett.series.data.tree 0).length = 1 := by
      cases ett.series.certified 0 with
      | initial => assumption
    have htriple : KTriple G k e0 sigma := by
      have hinput : KTriple G k e0 input := by
        cases ett.series.certified 0 with
        | initial => assumption
      exact ⟨hinput.1, hinput.2.1, hinput.2.2.1, hproper, hone⟩
    -- First appearance in T1 uses an actual zero-round series, not a zero-rung ETT.
    let data0 : TashkinovSeriesData G k 0 e0 :=
      { tree := fun i => if i.val = 0 then ett.series.data.tree 0 else base.closure
        coloring := fun _ => sigma
        stored := fun _ => ∅
        connectingEdges := fun _ => ∅
        kind := fun _ => none
        chosenVertex := fun _ => none
        outsideVertex := fun _ => none
        delta := fun _ => none
        gamma := fun _ => none }
    have hclosure0 : TashkinovClosure sigma (ett.series.data.tree 0) base.closure :=
      ⟨hs ▸ hSR, hclosure.2⟩
    let series0 : TashkinovSeries G k 0 e0 sigma :=
      { data := data0
        certified := by
          intro i
          have hi : i = 0 := by
            apply Fin.ext
            have := i.isLt
            change i.val = 0
            omega
          subst i
          apply TashkinovSeriesStep.initial
          · exact htriple
          · exact hseedLength
          · rfl
          · rfl
          · rfl
          · rfl
          · rfl
          · rfl
          · rfl
          · rfl
          · exact hclosure0 }
    have htwo := (TechnicalTheoremBase G k 0 e0 sigma series0).2
    have hreflexive : StableColoring (series0.data.tree ⟨1, by omega⟩)
        (TashkinovStoredColors series0.data 0) (series0.data.coloring 0) sigma :=
      ⟨(by intro f hf hc; rfl), (by intro x hx; rfl)⟩
    exact htwo sigma hproper hone hreflexive alpha beta (Or.inl hmissing)
