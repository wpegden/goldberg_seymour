import Tablet.ChangeLemma
import Tablet.ChangeLemmaBothInside
import Tablet.CertifiedETTRestriction
import Tablet.ColoredVertexSetClosed
import Tablet.ColoredVertexSetElementary
import Tablet.CombinedStableColoring
import Tablet.CorrespondingExtendedTashkinovTree
import Tablet.ExtendedTashkinovTree
import Tablet.GoodHierarchy
import Tablet.GoodHierarchyNewMissingClosed
import Tablet.GoodHierarchyPrefixRepackage
import Tablet.GoodHierarchyCommonOriginalBaseTransport
import Tablet.HierarchyBase
import Tablet.HierarchyCounterexample
import Tablet.HierarchyCounterexampleLess
import Tablet.HierarchyCounterexampleMeasure
import Tablet.HierarchyFirstMissingPositionPrefixCutoff
import Tablet.HierarchyLEMStable
import Tablet.HierarchyNonparallelFirstEdge
import Tablet.HierarchySegmentColors
import Tablet.HierarchyStageMissingColors
import Tablet.HierarchyStarredStage
import Tablet.HierarchyStoredColorsAntitone
import Tablet.HierarchyStoredColorsAt
import Tablet.HierarchyWeaklyStable
import Tablet.IsProperEdgeColoring
import Tablet.MaximumDefectiveChoice
import Tablet.MaximumProperty
import Tablet.MaximumPropertyTransport
import Tablet.MissingColors
import Tablet.MissingColorIncidenceEndpoint
import Tablet.ModColoring
import Tablet.OutsideKempeRecoloring
import Tablet.OutsideKempeRecoloringStable
import Tablet.SameGoodHierarchy
import Tablet.SameHierarchyStages
import Tablet.StableChange
import Tablet.StableColoring
import Tablet.TashkinovAugmentation
import Tablet.TashkinovAugmentationSequence
import Tablet.TashkinovAugmentationSequenceColoringTransport
import Tablet.TashkinovAugmentationSequenceInitialSegment
import Tablet.TashkinovAugmentationSequencePosition
import Tablet.TashkinovAugmentationSequenceRestrict
import Tablet.TashkinovAugmentationSequenceSuffix
import Tablet.TashkinovClosure
import Tablet.TashkinovHierarchy
import Tablet.TashkinovSeries
import Tablet.TashkinovSeriesStep
import Tablet.TashkinovStoredColors
import Tablet.Td
import Tablet.TreeColorSetClosed
import Tablet.TreeColorSetMinusClosed
import Tablet.TreeColoringInvariant
import Tablet.TreeInterchangeable
import Tablet.TreeMissingColors
import Tablet.TreeSequence
import Tablet.TreeSequenceAdjoinEdge
import Tablet.TreeSequenceInitialSegment
import Tablet.TreeSequenceInitialSegmentVertexSetSubset
import Tablet.TreeSequencePrefix
import Tablet.TreeSequenceVertexSet
import Tablet.TwoColorComponent
import Tablet.TwoColorComponentSpanningPath
import Tablet.TwoColorComponentSwap
import Tablet.TwoColorComponentSwapMissingBehavior
import Tablet.TwoColorIncidenceGraph
import Tablet.TwoColorIncidenceDegreeAtMostTwo
import Tablet.TwoColorPathComponent
import Tablet.step1

-- [TABLET NODE: HierarchyCounterexampleOneAdditionPositiveDividerImpossible]
theorem HierarchyCounterexampleOneAdditionPositiveDividerImpossible
    {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi)
    (C : HierarchyCounterexample base)
    (hproper : IsProperEdgeColoring G phi)
    (hone : IsOneEdgeUncolored phi e0)
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
    (hfewer : ∀ {input' : PartialEdgeColoring E k}
      {T' : TreeSequence G e0}
      {generating' : PartialEdgeColoring E k}
      (other : ExtendedTashkinovTree G k e0 input' T' generating'),
      other.rounds = ett.rounds → MaximumProperty other →
      ∀ (base' : HierarchyBase other generating')
        (K : TashkinovHierarchy other base'),
        GoodHierarchy K → K.dividerCount < C.hierarchy.dividerCount →
        ColoredVertexSetElementary G generating'
          (TreeSequenceVertexSet T'))
    (hminimal : ∀ {input' : PartialEdgeColoring E k}
      {T' : TreeSequence G e0}
      {generating' : PartialEdgeColoring E k}
      {other : ExtendedTashkinovTree G k e0 input' T' generating'}
      {base' : HierarchyBase other generating'}
      (C' : HierarchyCounterexample base'),
      other.rounds = ett.rounds →
      C'.hierarchy.dividerCount = C.hierarchy.dividerCount →
      ¬ HierarchyCounterexampleLess
        (HierarchyCounterexampleMeasure C')
        (HierarchyCounterexampleMeasure C))
    (hlarge :
      let n : Fin (ett.rounds + 1) := Fin.last ett.rounds
      let Tn := ett.series.data.tree n.castSucc
      2 * ett.rounds + 11 ≤ (TreeMissingColors phi Tn).card)
    (honeAddition :
      let H := C.hierarchy
      let A := HierarchyStarredStage H (Fin.last H.dividerCount)
      T.length - A.length = 1)
    (hprefixElementary :
      let H := C.hierarchy
      let A := HierarchyStarredStage H (Fin.last H.dividerCount)
      let ell := T.length - A.length
      let Ty := TreeSequencePrefix T
        (min (A.length + (ell - 1)) T.length)
        (by have hA := A.positive; have hT := T.positive; omega)
        (Nat.min_le_right _ _)
      ColoredVertexSetElementary G phi (TreeSequenceVertexSet Ty))
    (hpositive : 0 < C.hierarchy.dividerCount) : False := by
-- BODY
  classical
  let H := C.hierarchy
  let q : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
  let i : Fin H.dividerCount := ⟨H.dividerCount - 1, by
    change 0 < H.dividerCount at hpositive
    omega⟩
  let A := HierarchyStarredStage H q
  let n : Fin (ett.rounds + 1) := Fin.last ett.rounds
  let Tn := ett.series.data.tree n.castSucc
  let Tnext := ett.series.data.tree n.succ
  have hqpos : 0 < H.dividerCount := hpositive
  have hiq : i.succ = q := by
    apply Fin.ext
    dsimp [i, q]
    omega
  have hA : A = H.stage q.castSucc := by
    dsimp [A]
    rw [← hiq]
    rfl
  have hlen : T.length = A.length + 1 := by
    have hs := H.strict q
    have ht : H.stage q.succ = T := H.terminalStage
    rw [ht, ← hA] at hs
    change T.length - A.length = 1 at honeAddition
    omega
  have segmentTrans {X Y Z : TreeSequence G e0}
      (hXY : TreeSequenceInitialSegment X Y)
      (hYZ : TreeSequenceInitialSegment Y Z) :
      TreeSequenceInitialSegment X Z := by
    refine ⟨le_trans hXY.1 hYZ.1, ?_, ?_⟩
    · intro j
      exact (hYZ.2.1 (Fin.castLE (Nat.succ_le_succ hXY.1) j)).trans
        (hXY.2.1 j)
    · intro j
      exact (hYZ.2.2 (Fin.castLE hXY.1 j)).trans (hXY.2.2 j)
  have commonPrefix {X Y Z : TreeSequence G e0}
      (hXZ : TreeSequenceInitialSegment X Z)
      (hYZ : TreeSequenceInitialSegment Y Z)
      (hXY : X.length ≤ Y.length) :
      TreeSequenceInitialSegment X Y := by
    refine ⟨hXY, ?_, ?_⟩
    · intro j
      exact (hYZ.2.1 (Fin.castLE (Nat.succ_le_succ hXY) j)).symm.trans
        (hXZ.2.1 j)
    · intro j
      exact (hYZ.2.2 (Fin.castLE hXY j)).symm.trans (hXZ.2.2 j)
  have equalTrees {X Y : TreeSequence G e0}
      (hXY : TreeSequenceInitialSegment X Y)
      (hlenXY : X.length = Y.length) : X = Y := by
    rcases hXY with ⟨hle, hv, he⟩
    cases X with
    | mk lx px vx ex vix eix fx ax =>
      cases Y with
      | mk ly py vy ey viy eiy fy ay =>
        simp only at hlenXY
        subst ly
        rw [TreeSequence.mk.injEq]
        refine ⟨rfl, ?_, ?_⟩
        · apply heq_of_eq
          funext j
          simpa only [Fin.castLE] using (hv j).symm
        · apply heq_of_eq
          funext j
          simpa only [Fin.castLE] using (he j).symm
  have hAT : TreeSequenceInitialSegment A T := by
    rw [hA]
    have ht : H.stage q.succ = T := H.terminalStage
    have h := H.nested q
    rw [ht] at h
    exact h
  have stagesNested : ∀ a b : Fin (H.dividerCount + 2),
      a.val ≤ b.val → TreeSequenceInitialSegment (H.stage a) (H.stage b) := by
    have chain : ∀ r : ℕ, ∀ a : Fin (H.dividerCount + 2),
        ∀ hr : a.val + r < H.dividerCount + 2,
          TreeSequenceInitialSegment (H.stage a) (H.stage ⟨a.val + r, hr⟩) := by
      intro r
      induction r with
      | zero =>
          intro a hr
          exact ⟨le_rfl, fun _ => rfl, fun _ => rfl⟩
      | succ r ih =>
          intro a hr
          have hprev := ih a (by omega)
          have hstep := H.nested ⟨a.val + r, by omega⟩
          exact segmentTrans hprev hstep
    intro a b hab
    have h := chain (b.val - a.val) a (by omega)
    have he : (⟨a.val + (b.val - a.val), by omega⟩ :
        Fin (H.dividerCount + 2)) = b := by
      apply Fin.ext
      change a.val + (b.val - a.val) = b.val
      omega
    rw [he] at h
    exact h
  have hTnA : TreeSequenceInitialSegment Tn A := by
    rw [hA]
    have h := stagesNested 0 q.castSucc (by simp)
    simpa only [H.baseStage] using h
  have hTnStrictA : Tn.length < A.length := by
    have hfirst := H.strict 0
    have hz : (0 : Fin (H.dividerCount + 1)).castSucc =
        (0 : Fin (H.dividerCount + 2)) := Fin.ext (by simp)
    have ho : (0 : Fin (H.dividerCount + 1)).succ =
        (⟨1, by omega⟩ : Fin (H.dividerCount + 2)) := Fin.ext (by simp)
    rw [hz, ho, H.baseStage] at hfirst
    have hfirstA := stagesNested ⟨1, by omega⟩ q.castSucc (by
      change 1 ≤ H.dividerCount
      omega)
    rw [hA]
    exact lt_of_lt_of_le hfirst hfirstA.1
  have hTnext : Tnext = ett.series.data.tree (Fin.last (ett.rounds + 1)) := rfl
  have hTTnext : TreeSequenceInitialSegment T Tnext := ett.belowFinal
  have hATnext := segmentTrans hAT hTTnext
  have prefixSegment (m : ℕ) (hm : 1 ≤ m) (hmT : m ≤ T.length) :
      TreeSequenceInitialSegment (TreeSequencePrefix T m hm hmT) T := by
    exact ⟨hmT, fun _ => rfl, fun _ => rfl⟩
  have hprefixEq :
      TreeSequencePrefix T
        (min (A.length + (T.length - A.length - 1)) T.length)
        (by have := A.positive; have := T.positive; omega)
        (Nat.min_le_right _ _) = A := by
    apply equalTrees
    · apply commonPrefix
        (prefixSegment _ _ _) hAT
      change min (A.length + (T.length - A.length - 1)) T.length ≤ A.length
      omega
    · change min (A.length + (T.length - A.length - 1)) T.length = A.length
      omega
  have hAElem : ColoredVertexSetElementary G phi (TreeSequenceVertexSet A) := by
    change ColoredVertexSetElementary G phi
      (TreeSequenceVertexSet (TreeSequencePrefix T
        (min (A.length + (T.length - A.length - 1)) T.length) _ _)) at hprefixElementary
    rw [hprefixEq] at hprefixElementary
    exact hprefixElementary
  let r : Fin T.length := ⟨A.length, by omega⟩
  let f : E := T.edge r
  let y : V := T.vertex (Fin.last T.length)
  have hyOutside : y ∉ TreeSequenceVertexSet A := by
    intro hy
    obtain ⟨j, hj⟩ : ∃ j, A.vertex j = y := by
      simpa only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and] using hy
    have he := hAT.2.1 j
    have hjy : T.vertex (Fin.castLE (Nat.succ_le_succ hAT.1) j) =
        T.vertex (Fin.last T.length) := he.trans hj
    have hidx := congrArg Fin.val (T.vertex_injective hjy)
    have hjlt := j.isLt
    simp only [Fin.coe_castLE, Fin.val_last] at hidx
    omega
  have hvertices : TreeSequenceVertexSet T = insert y (TreeSequenceVertexSet A) := by
    ext v
    constructor
    · intro hv
      simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and] at hv
      obtain ⟨j, rfl⟩ := hv
      by_cases hj : j.val ≤ A.length
      · apply Finset.mem_insert_of_mem
        let ja : Fin (A.length + 1) := ⟨j.val, by omega⟩
        have he : Fin.castLE (Nat.succ_le_succ hAT.1) ja = j := Fin.ext rfl
        simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
        exact ⟨ja, by rw [← hAT.2.1 ja, he]⟩
      · have he : j = Fin.last T.length := by
          apply Fin.ext
          simp only [Fin.val_last]
          omega
        rw [he]
        exact Finset.mem_insert_self _ _
    · intro hv
      rcases Finset.mem_insert.mp hv with rfl | hv
      · simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
        exact ⟨Fin.last T.length, rfl⟩
      · exact TreeSequenceInitialSegmentVertexSetSubset hAT hv
  have hcommon : ∃ alpha : Fin k,
      alpha ∈ TreeMissingColors phi A ∧ alpha ∈ MissingColors G phi y := by
    have hnot := C.notElementary
    unfold ColoredVertexSetElementary at hnot
    push_neg at hnot
    obtain ⟨u, hu, v, hv, huv, hdisjoint⟩ := hnot
    obtain ⟨alpha, hau, hav⟩ := Finset.not_disjoint_iff.mp hdisjoint
    rw [hvertices] at hu hv
    rcases Finset.mem_insert.mp hu with rfl | hu
    · have hvA : v ∈ TreeSequenceVertexSet A :=
        (Finset.mem_insert.mp hv).resolve_left (Ne.symm huv)
      exact ⟨alpha, Finset.mem_biUnion.mpr ⟨v, hvA, hav⟩, hau⟩
    · rcases Finset.mem_insert.mp hv with rfl | hv
      · exact ⟨alpha, Finset.mem_biUnion.mpr ⟨u, hu, hau⟩, hav⟩
      · exact False.elim (Finset.disjoint_left.mp (hAElem hu hv huv) hau hav)
  obtain ⟨alpha, halphaA, halphay⟩ := hcommon
  -- Retain the actual PE route or the exact SE/RE connecting seed.
  have terminalRoute : ∀ j : Fin (ett.rounds + 1), 0 < j.val →
      (ett.series.data.kind j = some TashkinovExtensionKind.PE ∧
        TashkinovAugmentationSequence (ett.series.data.coloring j)
          (ett.series.data.tree j.castSucc) (ett.series.data.tree j.succ)) ∨
      ((ett.series.data.kind j = some TashkinovExtensionKind.SE ∨
          ett.series.data.kind j = some TashkinovExtensionKind.RE) ∧
        ∃ (edge : E) (seed : TreeSequence G e0),
          ett.series.data.connectingEdges j = {edge} ∧
          TreeSequenceAdjoinEdge (ett.series.data.tree j.castSucc) edge seed ∧
          TashkinovAugmentationSequence (ett.series.data.coloring j)
            seed (ett.series.data.tree j.succ)) := by
    intro j hj
    have cert := ett.series.certified j
    cases cert with
    | initial => simp at hj
    | SE a previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed noRevisiting choice seriesAlternative
        currentColoring currentStored currentEdges currentKind currentVertex
        currentOutside currentDelta currentGamma adjoined adjoinedExactly
        closedExtension orderedExtension strictExtension =>
      exact Or.inr ⟨Or.inl currentKind, choice.edge, adjoined,
        currentEdges, adjoinedExactly, closedExtension.1⟩
    | PE a previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed noRevisiting choice seriesAlternativeFails
        gamma gammaRule secondStable secondStableProper secondStableOneUncolored
        secondStableRelation exitWitness currentColoring currentProper
        currentOneUncolored currentStored currentEdges currentKind currentVertex
        currentOutside currentDelta currentGamma closedExtension orderedExtension
        strictExtension =>
      exact Or.inl ⟨currentKind, closedExtension.1⟩
    | RE a previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed available currentColoring currentStored
        currentEdges currentKind currentVertex currentOutside currentDelta
        currentGamma adjoined adjoinedExactly closedExtension orderedExtension
        strictExtension =>
      exact Or.inr ⟨Or.inr currentKind, available.edge, adjoined,
        currentEdges, adjoinedExactly, closedExtension.1⟩
  have hroute := terminalRoute n (by dsimp [n]; have := ett.roundsPositive; omega)
  rw [← ett.generatingColoring] at hroute
  have hAtoT : TashkinovAugmentationSequence phi A T := by
    rcases hroute with ⟨hkind, hseq⟩ | ⟨hkind, edge, seed, hedges, hseed, hseq⟩
    · have hTnT := segmentTrans hTnA hAT
      have htoT := TashkinovAugmentationSequenceRestrict phi Tn T Tnext
        hseq hTnT hTTnext
      exact TashkinovAugmentationSequenceSuffix phi Tn A T htoT hTnA hAT
    · have hseedFinal := TashkinovAugmentationSequenceInitialSegment phi seed Tnext hseq
      have hseedA : TreeSequenceInitialSegment seed A :=
        commonPrefix hseedFinal hATnext (by
          have hseedLen : seed.length = Tn.length + 1 := hseed.1
          omega)
      have hseedT := segmentTrans hseedA hAT
      have htoT := TashkinovAugmentationSequenceRestrict phi seed T Tnext
        hseq hseedT hTTnext
      exact TashkinovAugmentationSequenceSuffix phi seed A T htoT hseedA hAT
  have hfinalAugmentation : TashkinovAugmentation phi A T := by
    have hpos := (TashkinovAugmentationSequencePosition phi A T hAtoT r
      (by rfl)).1
    have hpreA : TreeSequencePrefix T r.val A.positive (Nat.le_of_lt r.isLt) = A := by
      apply equalTrees
      · exact commonPrefix (prefixSegment _ _ _) hAT (le_refl _)
      · rfl
    have hpreT : TreeSequencePrefix T (r.val + 1) (by have := A.positive; omega)
        (Nat.succ_le_of_lt r.isLt) = T := by
      exact equalTrees (prefixSegment _ _ _) hlen.symm
    rw [hpreA, hpreT] at hpos
    exact hpos
  obtain ⟨hauglen, haugseg, gamma, hgammaEdge, hgammaA⟩ := hfinalAugmentation
  have hgammaf : phi f = some gamma := by
    have he : Fin.cast hauglen.symm (Fin.last A.length) = r := Fin.ext rfl
    simpa only [he] using hgammaEdge
  have hfEnds : ∃ u ∈ TreeSequenceVertexSet A, G.ends f = Sym2.mk u y := by
    obtain ⟨a, ha⟩ := T.attaches r
    let aa : Fin (A.length + 1) := ⟨a.val, by have := a.isLt; dsimp [r] at this; omega⟩
    have hv : T.vertex (Fin.castLT a
        (Nat.lt_trans a.isLt (Nat.succ_lt_succ r.isLt))) = A.vertex aa := by
      have he : Fin.castLT a (Nat.lt_trans a.isLt (Nat.succ_lt_succ r.isLt)) =
          Fin.castLE (Nat.succ_le_succ hAT.1) aa := Fin.ext rfl
      rw [he]
      exact hAT.2.1 aa
    have hr : r.succ = Fin.last T.length := by
      apply Fin.ext
      change A.length + 1 = T.length
      exact hlen.symm
    have he : G.ends f = Sym2.mk y (A.vertex aa) := by
      simpa only [f, hr, hv] using ha
    have haa : A.vertex aa ∈ TreeSequenceVertexSet A :=
      by
        simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
        exact ⟨aa, rfl⟩
    exact ⟨A.vertex aa, haa, he.trans Sym2.eq_swap⟩
  have hfBoundary : f ∈ BoundaryColorEdges G phi (TreeSequenceVertexSet A) gamma := by
    obtain ⟨u, hu, he⟩ := hfEnds
    simp only [BoundaryColorEdges, Finset.mem_filter, BoundaryEdges, Finset.mem_univ,
      true_and]
    exact ⟨⟨u, hu, y, hyOutside, he⟩, hgammaf⟩
  have hgammaReserved : gamma ∈
      (HierarchyStoredColorsAt H q).biUnion (C.good.gamma i.castSucc) := by
    by_contra hnot
    have hstage : H.stage i.succ.castSucc = A := by rw [hiq, ← hA]
    have hminus := C.good.minusClosed i
    change TreeColorSetMinusClosed G phi (H.stage i.succ.castSucc)
      ((HierarchyStoredColorsAt H i.succ).biUnion (C.good.gamma i.castSucc)) at hminus
    rw [hstage, hiq] at hminus
    have hc := hminus gamma (Finset.mem_sdiff.mpr ⟨hgammaA, hnot⟩)
    rw [hc] at hfBoundary
    simpa using hfBoundary
  have firstMissingAfter (eta : Fin k) (heta : eta ∉ TreeMissingColors phi A) :
      (HierarchyFirstMissingPosition phi T eta).val = T.length := by
    unfold HierarchyFirstMissingPosition
    dsimp only
    split
    · rename_i hc
      let candidates : Finset (Fin (T.length + 1)) :=
        Finset.univ.filter fun j => eta ∈ MissingColors G phi (T.vertex j)
      let p := candidates.min' hc
      have hp := (Finset.mem_filter.mp (Finset.min'_mem candidates hc)).2
      have hpgt : A.length < p.val := by
        by_contra hle
        let pa : Fin (A.length + 1) := ⟨p.val, by omega⟩
        have he : Fin.castLE (Nat.succ_le_succ hAT.1) pa = p := Fin.ext rfl
        apply heta
        refine Finset.mem_biUnion.mpr ⟨A.vertex pa,
          ?_, ?_⟩
        · simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
          exact ⟨pa, rfl⟩
        · rw [← hAT.2.1 pa, he]
          exact hp
      have hplt := p.isLt
      change p.val = T.length
      omega
    · rfl
  have hgammaTerminalExcluded : ∀ eta ∈ HierarchyStoredColorsAt H q,
      gamma ∉ C.good.gamma q eta := by
    intro eta heta hgamma
    have hetaMissing : eta ∉ TreeMissingColors phi A :=
      (Finset.mem_sdiff.mp heta).2
    have hcutoff := firstMissingAfter eta hetaMissing
    have hseg : gamma ∈ HierarchySegmentColors H q eta := by
      unfold HierarchySegmentColors
      dsimp only
      have ht : H.stage q.succ = T := H.terminalStage
      rw [ht]
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, r, le_rfl, ?_, hgammaf⟩
      rw [hcutoff]
      dsimp [r]
      omega
    exact (Finset.mem_sdiff.mp (C.good.avoidance q eta heta hgamma)).2 hseg
  obtain ⟨eta, ⟨heta, hrefresh, hother⟩, hunique⟩ := C.good.uniqueRefresh i
  have hcard := C.good.twoColors i.succ eta heta
  obtain ⟨theta, hthetaPair⟩ : (C.good.gamma i.succ eta).Nonempty :=
    Finset.card_pos.mp (by omega)
  have hthetaNew := hrefresh hthetaPair
  obtain ⟨x, hxNew, hthetax⟩ := Finset.mem_biUnion.mp hthetaNew
  have hxA : x ∈ TreeSequenceVertexSet A := by
    have hx := (Finset.mem_sdiff.mp hxNew).1
    change x ∈ TreeSequenceVertexSet (H.stage i.succ.castSucc) at hx
    rw [hiq, ← hA] at hx
    exact hx
  have hthetaA : theta ∈ TreeMissingColors phi A :=
    Finset.mem_biUnion.mpr ⟨x, hxA, hthetax⟩
  have hthetaClosed : TreeColorSetClosed G phi A {theta} := by
    have hstage : H.stage i.succ.castSucc = A := by rw [hiq, ← hA]
    have helem : ColoredVertexSetElementary G phi
        (TreeSequenceVertexSet (H.stage i.succ.castSucc)) := by
      rw [hstage]
      exact hAElem
    have hc := GoodHierarchyNewMissingClosed C.good i helem theta hthetaNew
    rw [hstage] at hc
    intro c hc'
    have he : c = theta := Finset.mem_singleton.mp hc'
    simpa only [he] using hc
  have hthetaGamma : theta ≠ gamma := by
    intro he
    have hp : theta ∈ C.good.gamma q eta := by
      simpa only [hiq] using hthetaPair
    have heStored : eta ∈ HierarchyStoredColorsAt H q := by
      simpa only [hiq] using heta
    exact hgammaTerminalExcluded eta heStored (he ▸ hp)
  have graphSwap (psi : PartialEdgeColoring E k) (c d : Fin k) :
      TwoColorIncidenceGraph G psi c d = TwoColorIncidenceGraph G psi d c := by
    ext z w
    cases z <;> cases w <;> simp [TwoColorIncidenceGraph, or_comm]
  have missingLeaf (psi : PartialEdgeColoring E k) (hpsi : IsProperEdgeColoring G psi)
      (c d : Fin k) (hcd : c ≠ d) (v : V)
      (hc : c ∈ MissingColors G psi v ∨ d ∈ MissingColors G psi v) :
      Set.Subsingleton ((TwoColorIncidenceGraph G psi c d).neighborSet (Sum.inl v)) := by
    letI : Fintype ((TwoColorIncidenceGraph G psi c d).neighborSet (Sum.inl v)) :=
      Fintype.ofFinite _
    have hdegree : @SimpleGraph.degree _ (TwoColorIncidenceGraph G psi c d)
        (Sum.inl v) (Fintype.ofFinite _) ≤ 1 := by
      rcases hc with hc | hc
      · exact MissingColorIncidenceEndpoint G psi c d hcd hpsi v hc
      · rw [graphSwap psi c d]
        exact MissingColorIncidenceEndpoint G psi d c hcd.symm hpsi v hc
    have hcard : Fintype.card
        ((TwoColorIncidenceGraph G psi c d).neighborSet (Sum.inl v)) ≤ 1 := by
      rw [SimpleGraph.card_neighborSet_eq_degree]
      exact hdegree
    intro z hz w hw
    exact congrArg Subtype.val
      (Fintype.card_le_one_iff.mp hcard ⟨z, hz⟩ ⟨w, hw⟩)
  have pathMissing (psi : PartialEdgeColoring E k) (hpsi : IsProperEdgeColoring G psi)
      (c d : Fin k) (hcd : c ≠ d) (v : V)
      (hc : c ∈ MissingColors G psi v ∨ d ∈ MissingColors G psi v) :
      TwoColorPathComponent G psi c d (Sum.inl v) :=
    ⟨hcd, Sum.inl v, rfl, missingLeaf psi hpsi c d hcd v hc⟩
  -- A missing-color component outside A cannot acquire a third endpoint.
  -- The coincident-witness case is an isolated component and is handled separately.
  have outsideMissingComponent (psi : PartialEdgeColoring E k)
      (hpsi : IsProperEdgeColoring G psi) (c d : Fin k) (hcd : c ≠ d)
      (hcA : c ∈ TreeMissingColors psi A) (hdA : d ∈ TreeMissingColors psi A)
      (w : V) (hwOutside : w ∉ TreeSequenceVertexSet A)
      (hcw : c ∈ MissingColors G psi w ∨ d ∈ MissingColors G psi w)
      (hinter : TreeInterchangeable G A psi c d) :
      ∀ v ∈ TreeSequenceVertexSet A,
        Sum.inl v ∉ TwoColorComponent G psi c d (Sum.inl w) := by
    obtain ⟨u, huA, hcu⟩ := Finset.mem_biUnion.mp hcA
    obtain ⟨v, hvA, hdv⟩ := Finset.mem_biUnion.mp hdA
    intro z hzA hzC
    have huvC := hinter (Sum.inl u) (Sum.inl v)
      (pathMissing psi hpsi c d hcd u (Or.inl hcu))
      (pathMissing psi hpsi c d hcd v (Or.inr hdv))
      ⟨u, huA, rfl⟩ ⟨v, hvA, rfl⟩
    have huwC := hinter (Sum.inl u) (Sum.inl w)
      (pathMissing psi hpsi c d hcd u (Or.inl hcu))
      (pathMissing psi hpsi c d hcd w hcw) ⟨u, huA, rfl⟩ ⟨z, hzA, hzC⟩
    have hvC : Sum.inl v ∈ TwoColorComponent G psi c d (Sum.inl u) := by
      rw [huvC]
      rfl
    have hwC : Sum.inl w ∈ TwoColorComponent G psi c d (Sum.inl u) := by
      rw [huwC]
      rfl
    have huw : Sum.inl u ≠ (Sum.inl w : Sum V E) := by
      intro he
      exact hwOutside (Sum.inl.inj he ▸ huA)
    have hvw : Sum.inl v ≠ (Sum.inl w : Sum V E) := by
      intro he
      exact hwOutside (Sum.inl.inj he ▸ hvA)
    by_cases huv : u = v
    · subst v
      have hnone : (TwoColorIncidenceGraph G psi c d).neighborSet (Sum.inl u) = ∅ := by
        ext z
        simp only [Set.mem_empty_iff_false, iff_false]
        intro hz
        cases z with
        | inl z => exact hz
        | inr edge =>
          change Incident G u edge ∧ (psi edge = some c ∨ psi edge = some d) at hz
          obtain ⟨hinc, hcolor⟩ := hz
          have hcnot : c ∉ PresentColors G psi u := by
            simpa [MissingColors] using hcu
          have hdnot : d ∉ PresentColors G psi u := by
            simpa [MissingColors] using hdv
          rcases hcolor with hcolor | hcolor
          · apply hcnot
            simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨edge, hinc, hcolor⟩
          · apply hdnot
            simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨edge, hinc, hcolor⟩
      have hreach : (TwoColorIncidenceGraph G psi c d).Reachable
          (Sum.inl u) (Sum.inl w) :=
        SimpleGraph.ConnectedComponent.reachable_of_mem_supp _ rfl hwC
      exact SimpleGraph.not_reachable_of_neighborSet_left_eq_empty huw hnone hreach
    · obtain ⟨a, b, p, hp, hsupport⟩ :=
        TwoColorComponentSpanningPath G psi c d hpsi (Sum.inl u)
      have endpoint (t : V)
          (htC : Sum.inl t ∈ TwoColorComponent G psi c d (Sum.inl u))
          (htMissing : c ∈ MissingColors G psi t ∨ d ∈ MissingColors G psi t) :
          Sum.inl t = a ∨ Sum.inl t = b := by
        by_contra hnot
        push_neg at hnot
        have htSupport : Sum.inl t ∈ p.support := by
          change Sum.inl t ∈ {z | z ∈ p.support}
          rw [hsupport]
          exact htC
        exact (hp.isTrail.not_mem_support_of_subsingleton_neighborSet
          hnot.1 hnot.2 (missingLeaf psi hpsi c d hcd t htMissing)) htSupport
      have huEnd := endpoint u rfl (Or.inl hcu)
      have hvEnd := endpoint v hvC (Or.inr hdv)
      have hwEnd := endpoint w hwC hcw
      have huv' : Sum.inl u ≠ (Sum.inl v : Sum V E) := fun he => huv (Sum.inl.inj he)
      rcases huEnd with huEnd | huEnd <;>
        rcases hvEnd with hvEnd | hvEnd <;>
        rcases hwEnd with hwEnd | hwEnd
      all_goals first
        | exact huv' (huEnd.trans hvEnd.symm)
        | exact huw (huEnd.trans hwEnd.symm)
        | exact hvw (hvEnd.trans hwEnd.symm)
  have stepInterchange (beta : Fin k) (hne : theta ≠ beta) :
      TreeInterchangeable G A phi theta beta := by
    have hstage : H.stage i.succ.castSucc = A := by rw [hiq, ← hA]
    have hm : theta ∈ TreeMissingColors phi (H.stage i.succ.castSucc) := by
      rw [hstage]
      exact hthetaA
    have hc : TreeColorSetClosed G phi (H.stage i.succ.castSucc) {theta} := by
      rw [hstage]
      exact hthetaClosed
    have hi := step1 G k e0 input T phi ett C.maximum C.positive hproper hone
      hlower base H C.good hfewer hlarge i theta beta hm hne hc
    rw [hstage] at hi
    exact hi
  have hthetaAlpha : theta ≠ alpha := by
    intro he
    have hthetay : theta ∈ MissingColors G phi y := by rw [he]; exact halphay
    have hout := outsideMissingComponent phi hproper theta gamma hthetaGamma hthetaA hgammaA
      y hyOutside (Or.inl hthetay) (stepInterchange gamma hthetaGamma)
    obtain ⟨u, huA, hends⟩ := hfEnds
    have hyf : (TwoColorIncidenceGraph G phi theta gamma).Adj (Sum.inl y) (Sum.inr f) := by
      refine ⟨?_, Or.inr hgammaf⟩
      change y ∈ G.ends f
      rw [hends]
      exact Sym2.mem_mk_right _ _
    have hfu : (TwoColorIncidenceGraph G phi theta gamma).Adj (Sum.inr f) (Sum.inl u) := by
      refine ⟨?_, Or.inr hgammaf⟩
      change u ∈ G.ends f
      rw [hends]
      exact Sym2.mem_mk_left _ _
    apply hout u huA
    change (TwoColorIncidenceGraph G phi theta gamma).connectedComponentMk (Sum.inl u) =
      (TwoColorIncidenceGraph G phi theta gamma).connectedComponentMk (Sum.inl y)
    exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hfu).symm.trans
      (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hyf).symm
  have hcomponentOutside : ∀ v ∈ TreeSequenceVertexSet A,
      Sum.inl v ∉ TwoColorComponent G phi theta alpha (Sum.inl y) :=
    outsideMissingComponent phi hproper theta alpha hthetaAlpha hthetaA halphaA y hyOutside
      (Or.inr halphay) (stepInterchange alpha hthetaAlpha)
  let sigma := TwoColorComponentSwap G phi theta alpha (Sum.inl y)
  have hrecolorA : OutsideKempeRecoloring A phi sigma theta alpha := by
    refine ⟨hthetaAlpha, {Sum.inl y}, ?_, ?_⟩
    · intro z hz v hv hvA
      have he : z = Sum.inl y := Finset.mem_singleton.mp hz
      subst z
      exact hcomponentOutside v hvA hv
    · intro edge
      simp only [sigma, TwoColorComponentSwap, Finset.mem_singleton, exists_eq_left]
  have hstableA := OutsideKempeRecoloringStable G e0 A
    (TashkinovStoredColors ett.series.data n) phi sigma theta alpha
    hproper hone hrecolorA
  have missingFirstInA (c : Fin k) (hc : c ∈ TreeMissingColors phi A) :
      c ∈ MissingColors G phi (T.vertex (HierarchyFirstMissingPosition phi T c)) ∧
        T.vertex (HierarchyFirstMissingPosition phi T c) ∈ TreeSequenceVertexSet A := by
    obtain ⟨v, hvA, hcv⟩ := Finset.mem_biUnion.mp hc
    obtain ⟨j, hj⟩ : ∃ j, A.vertex j = v := by
      simpa only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and] using hvA
    let jt := Fin.castLE (Nat.succ_le_succ hAT.1) j
    let candidates := Finset.univ.filter fun p : Fin (T.length + 1) =>
      c ∈ MissingColors G phi (T.vertex p)
    have hjmem : jt ∈ candidates := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      rw [hAT.2.1 j, hj]
      exact hcv
    have hnonempty : candidates.Nonempty := ⟨jt, hjmem⟩
    unfold HierarchyFirstMissingPosition
    rw [dif_pos hnonempty]
    refine ⟨(Finset.mem_filter.mp (Finset.min'_mem candidates hnonempty)).2, ?_⟩
    have hp := Finset.min'_le candidates jt hjmem
    have hpBound : (candidates.min' hnonempty).val < A.length + 1 :=
      lt_of_le_of_lt hp j.isLt
    let pa : Fin (A.length + 1) := ⟨(candidates.min' hnonempty).val, hpBound⟩
    have he : Fin.castLE (Nat.succ_le_succ hAT.1) pa = candidates.min' hnonempty :=
      Fin.ext rfl
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨pa, by rw [← he, hAT.2.1 pa]⟩
  have hstableLadder : StableColoring Tn
      (TashkinovStoredColors ett.series.data n)
      (ett.series.data.coloring n) sigma := by
    have hsub := TreeSequenceInitialSegmentVertexSetSubset hTnA
    constructor
    · intro edge he _
      rw [← ett.generatingColoring]
      apply hstableA.2.2.2.2 edge
      obtain ⟨v, hv, hinc⟩ := he
      exact ⟨v, hsub hv, hinc⟩
    · intro v hv
      rw [← ett.generatingColoring]
      exact hstableA.2.2.1.2 v (hsub hv)
  have hmod : ModColoring ett sigma := Td G k e0 input T phi ett C.maximum
    C.positive hlower sigma hstableA.1 hstableA.2.1 hstableLadder
  have hfixedEdges : ∀ t : Fin T.length, sigma (T.edge t) = phi (T.edge t) := by
    intro t
    apply hstableA.2.2.2.2
    by_cases ht : t.val < A.length
    · let ta : Fin A.length := ⟨t.val, ht⟩
      have he : Fin.castLE hAT.1 ta = t := Fin.ext rfl
      obtain ⟨j, hj⟩ := A.attaches ta
      refine ⟨A.vertex ta.succ, ?_, ?_⟩
      · simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
        exact ⟨ta.succ, rfl⟩
      · change A.vertex ta.succ ∈ G.ends (T.edge t)
        rw [← he, hAT.2.2 ta, hj]
        exact Sym2.mem_mk_left _ _
    · have he : t = r := by
        apply Fin.ext
        have := t.isLt
        dsimp [r]
        omega
      rw [he]
      obtain ⟨u, huA, hends⟩ := hfEnds
      refine ⟨u, huA, ?_⟩
      change u ∈ G.ends f
      rw [hends]
      exact Sym2.mem_mk_left _ _
  have hsigmaRoute :
      (ett.series.data.kind n = some TashkinovExtensionKind.PE ∧
        TashkinovAugmentationSequence sigma Tn T) ∨
      ((ett.series.data.kind n = some TashkinovExtensionKind.SE ∨
          ett.series.data.kind n = some TashkinovExtensionKind.RE) ∧
        ∃ (edge : E) (seed : TreeSequence G e0),
          ett.series.data.connectingEdges n = {edge} ∧
          TreeSequenceAdjoinEdge Tn edge seed ∧
          TashkinovAugmentationSequence sigma seed T) := by
    rcases hroute with ⟨hkind, hseq⟩ | ⟨hkind, edge, seed, hedges, hseed, hseq⟩
    · have hTnT := segmentTrans hTnA hAT
      have htoT := TashkinovAugmentationSequenceRestrict phi Tn T Tnext
        hseq hTnT hTTnext
      exact Or.inl ⟨hkind, TashkinovAugmentationSequenceColoringTransport
        phi sigma Tn A T htoT hAT hlen (fun t _ => hfixedEdges t)
        hstableA.2.2.2.1.2⟩
    · have hseedFinal := TashkinovAugmentationSequenceInitialSegment phi seed Tnext hseq
      have hseedA : TreeSequenceInitialSegment seed A :=
        commonPrefix hseedFinal hATnext (by
          have hseedLen : seed.length = Tn.length + 1 := hseed.1
          omega)
      have htoT := TashkinovAugmentationSequenceRestrict phi seed T Tnext
        hseq (segmentTrans hseedA hAT) hTTnext
      exact Or.inr ⟨hkind, edge, seed, hedges, hseed,
        TashkinovAugmentationSequenceColoringTransport phi sigma seed A T
          htoT hAT hlen (fun t _ => hfixedEdges t) hstableA.2.2.2.1.2⟩
  obtain ⟨corrT⟩ := hmod.2.2 T ett.abovePenultimate ett.strictAbovePenultimate hsigmaRoute
  have hmaximumT : MaximumProperty corrT.replacementETT :=
    MaximumPropertyTransport G k e0 ett sigma hmod T corrT C.maximum
  have hnotElementarySigma : ¬ ColoredVertexSetElementary G sigma
      (TreeSequenceVertexSet T) := by
    have hswap := TwoColorComponentSwapMissingBehavior G phi theta alpha
      hthetaAlpha hproper (Sum.inl y)
    have hthetay : theta ∈ MissingColors G sigma y := hswap.2.2.1 y rfl halphay
    have hthetaxSigma : theta ∈ MissingColors G sigma x := by
      rw [hstableA.2.2.2.1.2 x hxA]
      exact hthetax
    have hxT := TreeSequenceInitialSegmentVertexSetSubset hAT hxA
    have hyT : y ∈ TreeSequenceVertexSet T := by
      simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
      exact ⟨Fin.last T.length, rfl⟩
    have hxy : x ≠ y := fun he => hyOutside (he ▸ hxA)
    intro helem
    exact Finset.disjoint_left.mp (helem hxT hyT hxy) hthetaxSigma hthetay
  obtain ⟨ettPrefix, hmaximumPrefix, hrungPrefix, hseriesPrefix,
      basePrefix, hcorePrefix, hclosurePrefix, hsupportPrefix,
      HP, hcountPrefix, hstagesPrefix, hdividersPrefix,
      goodPrefix, hcolorsPrefix, hminusPrefix⟩ :=
    GoodHierarchyPrefixRepackage G k e0 input T phi phi ett C.maximum
      base H C.good q (by change 1 ≤ H.dividerCount; omega)
  have hrecolorPrefix : OutsideKempeRecoloring (H.stage q.castSucc)
      phi sigma theta alpha := by
    rw [← hA]
    exact hrecolorA
  have hprefixTransport := HierarchyLEMStable G k e0 input (H.stage q.castSucc)
    phi sigma ettPrefix hmaximumPrefix (by rw [hrungPrefix]; exact C.positive)
    (fun lower hp hl hm => hlower lower hp (lt_of_lt_of_eq hl hrungPrefix) hm)
    basePrefix HP goodPrefix hproper hone theta alpha hrecolorPrefix
  obtain ⟨corrPrefix, hmaximumPrefixSigma, basePrefixSigma, KP,
      goodPrefixSigma, hsamePrefixSigma, hminusPrefixSigma⟩ :=
    hprefixTransport.2.2.2.2
  -- Both certificates below are tied to the original certified series.
  -- No equality between independently chosen replacement certificates is used.
  rcases ettPrefix with ⟨roundsPrefix, positivePrefix, seriesPrefix,
    abovePrefix, strictPrefix, belowPrefix, generatingPrefix⟩
  dsimp only at hrungPrefix hseriesPrefix
  cases hrungPrefix
  have hseriesEq : seriesPrefix = ett.series := eq_of_heq hseriesPrefix
  cases hseriesEq
  let corrA : CorrespondingExtendedTashkinovTree G k e0 ett sigma
      (H.stage q.castSucc) := {
    replacementInput := corrPrefix.replacementInput
    replacementSeries := corrPrefix.replacementSeries
    replacementETT := corrPrefix.replacementETT
    rungAgreement := corrPrefix.rungAgreement
    seriesPresentation := corrPrefix.seriesPresentation
    finalGeneratingColoring := corrPrefix.finalGeneratingColoring
    ladderTreesAgree := corrPrefix.ladderTreesAgree
    storedColorsAgree := corrPrefix.storedColorsAgree
    connectingEdgesAgree := corrPrefix.connectingEdgesAgree
    extensionKindsAgree := corrPrefix.extensionKindsAgree
    replacementProper := corrPrefix.replacementProper
    replacementOneUncolored := corrPrefix.replacementOneUncolored
    replacementStable := corrPrefix.replacementStable }
  obtain ⟨baseT, hcoreTA, hclosureTA, hsupportTA⟩ :=
    GoodHierarchyCommonOriginalBaseTransport G k e0 input T phi sigma ett
      (H.stage q.castSucc) T corrA basePrefixSigma corrT
  have hcoreT : baseT.core = base.core :=
    hcoreTA.trans (hsamePrefixSigma.1.1.symm.trans hcorePrefix)
  have hterminalTree :
      corrT.replacementETT.series.data.tree
        (Fin.last corrT.replacementETT.rounds).castSucc = Tn := by
    rcases corrT with ⟨replacementInput, replacementSeries, replacementETT,
      rungAgreement, seriesPresentation, finalGeneratingColoring,
      ladderTreesAgree, storedColorsAgree, connectingEdgesAgree,
      extensionKindsAgree, replacementProper, replacementOneUncolored,
      replacementStable⟩
    cases replacementETT with
    | mk rounds roundsPositive replacementData above strict below generating =>
      cases rungAgreement
      have hs : replacementData = replacementSeries := eq_of_heq seriesPresentation
      cases hs
      let lastRung : Fin ett.rounds := ⟨ett.rounds - 1, by
        have := ett.roundsPositive
        omega⟩
      have he : lastRung.succ = Fin.last ett.rounds := by
        apply Fin.ext
        change ett.rounds - 1 + 1 = ett.rounds
        have := ett.roundsPositive
        omega
      change replacementSeries.data.tree (Fin.last ett.rounds).castSucc = Tn
      change replacementSeries.data.tree (Fin.last ett.rounds).castSucc =
        ett.series.data.tree (Fin.last ett.rounds).castSucc
      rw [← he]
      exact ladderTreesAgree lastRung
  let K : TashkinovHierarchy corrT.replacementETT baseT := {
    dividerCount := H.dividerCount
    stage := H.stage
    baseStage := H.baseStage.trans hterminalTree.symm
    terminalStage := H.terminalStage
    nested := H.nested
    strict := H.strict
    dividerPosition := H.dividerPosition
    dividerPositive := H.dividerPositive
    dividerIncreasing := H.dividerIncreasing
    dividerStage := H.dividerStage
    coreInsideFirst := by rw [hcoreT]; exact H.coreInsideFirst }
  have missingTree (B : TreeSequence G e0)
      (hBA : TreeSequenceVertexSet B ⊆ TreeSequenceVertexSet A) :
      TreeMissingColors sigma B = TreeMissingColors phi B := by
    ext c
    simp only [TreeMissingColors, Finset.mem_biUnion]
    constructor <;> rintro ⟨v, hv, hc⟩
    · exact ⟨v, hv, by rw [← hstableA.2.2.2.1.2 v (hBA hv)]; exact hc⟩
    · exact ⟨v, hv, by rw [hstableA.2.2.2.1.2 v (hBA hv)]; exact hc⟩
  have stageInsideA (j : Fin (H.dividerCount + 1)) :
      TreeSequenceInitialSegment (H.stage j.castSucc) A := by
    rw [hA]
    exact stagesNested j.castSucc q.castSucc (Fin.le_last j)
  have coreInsideA : TreeSequenceVertexSet base.core ⊆ TreeSequenceVertexSet A :=
    TreeSequenceInitialSegmentVertexSetSubset
      (segmentTrans H.coreInsideFirst
        (by
          rw [hA]
          exact stagesNested ⟨1, by omega⟩ q.castSucc (by change 1 ≤ H.dividerCount; omega)))
  have starredInsideA (j : Fin (H.dividerCount + 1)) :
      TreeSequenceVertexSet (HierarchyStarredStage H j) ⊆ TreeSequenceVertexSet A := by
    refine Fin.cases ?_ (fun a => ?_) j
    · exact coreInsideA
    · exact TreeSequenceInitialSegmentVertexSetSubset (stageInsideA a.succ)
  have starredEq (j : Fin (H.dividerCount + 1)) :
      HierarchyStarredStage K j = HierarchyStarredStage H j := by
    refine Fin.cases ?_ (fun a => ?_) j
    · exact hcoreT
    · rfl
  have terminalColors :
      corrT.replacementETT.series.data.kind (Fin.last corrT.replacementETT.rounds) =
        ett.series.data.kind n ∧
      TashkinovStoredColors corrT.replacementETT.series.data
          (Fin.last corrT.replacementETT.rounds) =
        TashkinovStoredColors ett.series.data n := by
    rcases corrT with ⟨replacementInput, replacementSeries, replacementETT,
      rungAgreement, seriesPresentation, finalGeneratingColoring,
      ladderTreesAgree, storedColorsAgree, connectingEdgesAgree,
      extensionKindsAgree, replacementProper, replacementOneUncolored,
      replacementStable⟩
    cases replacementETT with
    | mk rounds roundsPositive replacementData above strict below generating =>
      cases rungAgreement
      have hs : replacementData = replacementSeries := eq_of_heq seriesPresentation
      cases hs
      let a : Fin ett.rounds := ⟨ett.rounds - 1, by have := ett.roundsPositive; omega⟩
      have ha : a.succ = Fin.last ett.rounds := by
        apply Fin.ext
        change ett.rounds - 1 + 1 = ett.rounds
        have := ett.roundsPositive
        omega
      have ht : replacementSeries.data.tree (Fin.last ett.rounds).castSucc = Tn := by
        change replacementSeries.data.tree (Fin.last ett.rounds).castSucc =
          ett.series.data.tree (Fin.last ett.rounds).castSucc
        rw [← ha]
        exact ladderTreesAgree a
      have hm : TreeMissingColors (replacementSeries.data.coloring (Fin.last ett.rounds))
          (replacementSeries.data.tree (Fin.last ett.rounds).castSucc) =
          TreeMissingColors phi Tn := by
        rw [← finalGeneratingColoring, ht]
        exact missingTree Tn (TreeSequenceInitialSegmentVertexSetSubset hTnA)
      have hmOld : TreeMissingColors (ett.series.data.coloring (Fin.last ett.rounds))
          (ett.series.data.tree (Fin.last ett.rounds).castSucc) =
          TreeMissingColors phi Tn := by
        rw [← ett.generatingColoring]
      refine ⟨extensionKindsAgree (Fin.last ett.rounds), ?_⟩
      change TashkinovStoredColors replacementSeries.data (Fin.last ett.rounds) =
        TashkinovStoredColors ett.series.data (Fin.last ett.rounds)
      simp only [TashkinovStoredColors, storedColorsAgree, hm, hmOld]
  have storedEq (j : Fin (H.dividerCount + 1)) :
      HierarchyStoredColorsAt K j = HierarchyStoredColorsAt H j := by
    unfold HierarchyStoredColorsAt
    dsimp only
    rw [terminalColors.2, starredEq j, missingTree _ (starredInsideA j)]
  have stageMissingEq (j : Fin (H.dividerCount + 1)) :
      HierarchyStageMissingColors K j = HierarchyStageMissingColors H j := by
    refine Fin.cases ?_ (fun a => ?_) j
    · change TreeMissingColors sigma
        (corrT.replacementETT.series.data.tree
          (Fin.last corrT.replacementETT.rounds).castSucc) = TreeMissingColors phi Tn
      rw [hterminalTree]
      exact missingTree Tn (TreeSequenceInitialSegmentVertexSetSubset hTnA)
    · exact missingTree _ (TreeSequenceInitialSegmentVertexSetSubset (stageInsideA a.succ))
  have firstBound (psi : PartialEdgeColoring E k) (c : Fin k)
      (hc : c ∈ TreeMissingColors psi A) :
      (HierarchyFirstMissingPosition psi T c).val ≤ A.length := by
    obtain ⟨v, hvA, hcv⟩ := Finset.mem_biUnion.mp hc
    obtain ⟨j, hj⟩ : ∃ j, A.vertex j = v := by
      simpa only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and] using hvA
    let jt := Fin.castLE (Nat.succ_le_succ hAT.1) j
    let candidates := Finset.univ.filter fun p : Fin (T.length + 1) =>
      c ∈ MissingColors G psi (T.vertex p)
    have hjmem : jt ∈ candidates := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      rw [hAT.2.1 j, hj]
      exact hcv
    have hn : candidates.Nonempty := ⟨jt, hjmem⟩
    unfold HierarchyFirstMissingPosition
    rw [dif_pos hn]
    exact le_trans (Finset.min'_le candidates jt hjmem) (Nat.le_of_lt_succ j.isLt)
  have firstMissingEq (c : Fin k) :
      HierarchyFirstMissingPosition sigma T c = HierarchyFirstMissingPosition phi T c := by
    have hswap := TwoColorComponentSwapMissingBehavior G phi theta alpha
      hthetaAlpha hproper (Sum.inl y)
    by_cases hc : c = theta ∨ c = alpha
    · have hcA : c ∈ TreeMissingColors phi A := by
        rcases hc with rfl | rfl
        · exact hthetaA
        · exact halphaA
      have hcsA : c ∈ TreeMissingColors sigma A := by
        rw [missingTree A (fun _ h => h)]
        exact hcA
      have hfirstA : HierarchyFirstMissingPosition sigma A c =
          HierarchyFirstMissingPosition phi A c := by
        have hsets :
            (Finset.univ.filter fun j : Fin (A.length + 1) =>
              c ∈ MissingColors G sigma (A.vertex j)) =
            (Finset.univ.filter fun j : Fin (A.length + 1) =>
              c ∈ MissingColors G phi (A.vertex j)) := by
          ext j
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          have hv : A.vertex j ∈ TreeSequenceVertexSet A := by
            simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
            exact ⟨j, rfl⟩
          rw [hstableA.2.2.2.1.2 _ hv]
        unfold HierarchyFirstMissingPosition
        rw [hsets]
      have hcutPhi := HierarchyFirstMissingPositionPrefixCutoff phi A T hAT c A.length le_rfl
      have hcutSigma := HierarchyFirstMissingPositionPrefixCutoff sigma A T hAT c A.length le_rfl
      rw [hfirstA] at hcutSigma
      have hp := firstBound phi c hcA
      have hs := firstBound sigma c hcsA
      apply Fin.ext
      omega
    · have hct : c ≠ theta := fun h => hc (Or.inl h)
      have hca : c ≠ alpha := fun h => hc (Or.inr h)
      have hsets :
          (Finset.univ.filter fun j : Fin (T.length + 1) =>
            c ∈ MissingColors G sigma (T.vertex j)) =
          (Finset.univ.filter fun j : Fin (T.length + 1) =>
            c ∈ MissingColors G phi (T.vertex j)) := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact hswap.2.2.2 _ c hct hca
      unfold HierarchyFirstMissingPosition
      rw [hsets]
  have stageFixed (j : Fin (H.dividerCount + 1)) (t : Fin (H.stage j.succ).length) :
      sigma ((H.stage j.succ).edge t) = phi ((H.stage j.succ).edge t) := by
    have hs := stagesNested j.succ (Fin.last (H.dividerCount + 1)) (Fin.le_last _)
    rw [H.terminalStage] at hs
    have he := hs.2.2 t
    rw [← he]
    exact hfixedEdges _
  have segmentEq (j : Fin (H.dividerCount + 1)) (c : Fin k) :
      HierarchySegmentColors K j c = HierarchySegmentColors H j c := by
    unfold HierarchySegmentColors
    dsimp only
    rw [starredEq j, firstMissingEq c]
    simp only [K, stageFixed]
  have boundaryEq (B : TreeSequence G e0)
      (hBA : TreeSequenceVertexSet B ⊆ TreeSequenceVertexSet A) (c : Fin k) :
      BoundaryColorEdges G sigma (TreeSequenceVertexSet B) c =
        BoundaryColorEdges G phi (TreeSequenceVertexSet B) c := by
    ext edge
    simp only [BoundaryColorEdges, Finset.mem_filter]
    have hfixed : edge ∈ BoundaryEdges G (TreeSequenceVertexSet B) → sigma edge = phi edge := by
      intro he
      obtain ⟨u, hu, v, hv, hends⟩ := by simpa [BoundaryEdges] using he
      apply hstableA.2.2.2.2
      refine ⟨u, hBA hu, ?_⟩
      change u ∈ G.ends edge
      rw [hends]
      exact Sym2.mem_mk_left _ _
    constructor <;> rintro ⟨he, hc⟩
    · exact ⟨he, by rw [← hfixed he]; exact hc⟩
    · exact ⟨he, by rw [hfixed he]; exact hc⟩
  have minusEq (B : TreeSequence G e0)
      (hBA : TreeSequenceVertexSet B ⊆ TreeSequenceVertexSet A) (R : Finset (Fin k)) :
      TreeColorSetMinusClosed G sigma B R ↔ TreeColorSetMinusClosed G phi B R := by
    unfold TreeColorSetMinusClosed TreeColorSetClosed
    rw [missingTree B hBA]
    simp only [boundaryEq B hBA]
  have closureEq (hpe : corrT.replacementETT.series.data.kind
      (Fin.last corrT.replacementETT.rounds) = some TashkinovExtensionKind.PE) :
      baseT.closure = base.closure := by
    have hpeOld : ett.series.data.kind n = some TashkinovExtensionKind.PE := by
      rw [← terminalColors.1]
      exact hpe
    exact hclosureTA.trans
      ((hsamePrefixSigma.1.2.2.2.2.2 hpeOld).symm.trans hclosurePrefix)
  let goodT : GoodHierarchy K := {
    gamma := C.good.gamma
    twoColors := by
      intro j c hc
      exact C.good.twoColors j c (by rw [storedEq j] at hc; exact hc)
    avoidance := by
      intro j c hc
      change C.good.gamma j c ⊆ HierarchyStageMissingColors K j \ HierarchySegmentColors K j c
      rw [stageMissingEq j, segmentEq j c]
      exact C.good.avoidance j c (by rw [storedEq j] at hc; exact hc)
    disjointPairs := by
      intro j c d hc hd hne
      exact C.good.disjointPairs j c d
        (by rw [storedEq j] at hc; exact hc)
        (by rw [storedEq j] at hd; exact hd) hne
    uniqueRefresh := by
      intro a
      have hnew :
          ((TreeSequenceVertexSet (H.stage a.succ.castSucc) \
            TreeSequenceVertexSet (HierarchyStarredStage H a.castSucc)).biUnion
              fun v => MissingColors G sigma v) =
          ((TreeSequenceVertexSet (H.stage a.succ.castSucc) \
            TreeSequenceVertexSet (HierarchyStarredStage H a.castSucc)).biUnion
              fun v => MissingColors G phi v) := by
        ext c
        simp only [Finset.mem_biUnion]
        constructor <;> rintro ⟨v, hv, hc⟩
        · exact ⟨v, hv, by
            rw [← hstableA.2.2.2.1.2 v
              (TreeSequenceInitialSegmentVertexSetSubset (stageInsideA a.succ)
                (Finset.mem_sdiff.mp hv).1)]
            exact hc⟩
        · exact ⟨v, hv, by
            rw [hstableA.2.2.2.1.2 v
              (TreeSequenceInitialSegmentVertexSetSubset (stageInsideA a.succ)
                (Finset.mem_sdiff.mp hv).1)]
            exact hc⟩
      change ∃! c : Fin k,
        c ∈ HierarchyStoredColorsAt K a.succ ∧
          C.good.gamma a.succ c ⊆
            ((TreeSequenceVertexSet (H.stage a.succ.castSucc) \
              TreeSequenceVertexSet (HierarchyStarredStage K a.castSucc)).biUnion
                fun v => MissingColors G sigma v) ∧
          ∀ d ∈ HierarchyStoredColorsAt K a.succ, d ≠ c →
            C.good.gamma a.succ d = C.good.gamma a.castSucc d
      rw [starredEq a.castSucc, hnew]
      simp only [storedEq]
      exact C.good.uniqueRefresh a
    parallelBase := by
      dsimp only
      intro hpe
      have hpeOld : ett.series.data.kind n = some TashkinovExtensionKind.PE := by
        rw [← terminalColors.1]
        exact hpe
      have hcl : TreeSequenceVertexSet base.closure ⊆ TreeSequenceVertexSet A := by
        obtain ⟨_, _, ⟨ordered⟩⟩ := base.parallel hpeOld
        intro v hv
        apply coreInsideA
        rw [ordered.vertexSet]
        exact Finset.mem_union_right _ hv
      obtain ⟨hnot, hcard⟩ := C.good.parallelBase hpeOld
      constructor
      · change ¬ TreeColorSetMinusClosed G sigma baseT.core
          ((HierarchyStoredColorsAt K 0).biUnion (C.good.gamma 0))
        rw [hcoreT, storedEq 0, minusEq base.core coreInsideA]
        exact hnot
      · change 4 ≤ ((TreeMissingColors sigma
          (corrT.replacementETT.series.data.tree
            (Fin.last corrT.replacementETT.rounds).castSucc) ∩
          TreeMissingColors sigma baseT.closure) \
            (HierarchyStoredColorsAt K 0).biUnion (C.good.gamma 0)).card
        rw [hterminalTree, closureEq hpe, storedEq 0,
          missingTree Tn (TreeSequenceInitialSegmentVertexSetSubset hTnA),
          missingTree base.closure hcl]
        exact hcard
    minusClosed := by
      intro a
      change TreeColorSetMinusClosed G sigma (H.stage a.succ.castSucc)
        ((HierarchyStoredColorsAt K a.succ).biUnion (C.good.gamma a.castSucc))
      rw [storedEq a.succ, minusEq _
        (TreeSequenceInitialSegmentVertexSetSubset (stageInsideA a.succ))]
      exact C.good.minusClosed a }
  let Cs : HierarchyCounterexample baseT := {
    positive := by rw [corrT.rungAgreement]; exact C.positive
    hierarchy := K
    good := goodT
    maximum := hmaximumT
    notElementary := hnotElementarySigma }
  have hstarK : HierarchyStarredStage K (Fin.last K.dividerCount) = A := starredEq q
  have pathNumberEq : HierarchyPathNumber K = HierarchyPathNumber H := by
    unfold HierarchyPathNumber
    dsimp only
    rw [starredEq q]
  have measureEq : HierarchyCounterexampleMeasure Cs = HierarchyCounterexampleMeasure C := by
    change (HierarchyPathNumber K,
      T.length - (K.stage ⟨K.dividerCount, by omega⟩).length) =
      (HierarchyPathNumber H,
        T.length - (H.stage ⟨H.dividerCount, by omega⟩).length)
    rw [pathNumberEq]
  have hAElemSigma : ColoredVertexSetElementary G sigma (TreeSequenceVertexSet A) := by
    intro u hu v hv huv
    rw [hstableA.2.2.2.1.2 u hu, hstableA.2.2.2.1.2 v hv]
    exact hAElem hu hv huv
  have hprefixK :
      TreeSequencePrefix T
        (min ((HierarchyStarredStage K (Fin.last K.dividerCount)).length +
          (T.length - (HierarchyStarredStage K (Fin.last K.dividerCount)).length - 1))
          T.length)
        (by
          have := (HierarchyStarredStage K (Fin.last K.dividerCount)).positive
          have := T.positive
          omega)
        (Nat.min_le_right _ _) = A := by
    have hlengthStar := congrArg TreeSequence.length hstarK
    apply equalTrees
    · apply commonPrefix (prefixSegment _ _ _) hAT
      change min ((HierarchyStarredStage K (Fin.last K.dividerCount)).length +
        (T.length - (HierarchyStarredStage K (Fin.last K.dividerCount)).length - 1))
        T.length ≤ A.length
      omega
    · change min ((HierarchyStarredStage K (Fin.last K.dividerCount)).length +
        (T.length - (HierarchyStarredStage K (Fin.last K.dividerCount)).length - 1))
        T.length = A.length
      omega
  have hprefixSigma :
      let A' := HierarchyStarredStage K (Fin.last K.dividerCount)
      let ell' := T.length - A'.length
      let U := TreeSequencePrefix T
        (min (A'.length + (ell' - 1)) T.length)
        (by have := A'.positive; have := T.positive; omega)
        (Nat.min_le_right _ _)
      ColoredVertexSetElementary G sigma (TreeSequenceVertexSet U) := by
    dsimp only
    rw [hprefixK]
    exact hAElemSigma
  have hlargeSigma : 2 * corrT.replacementETT.rounds + 11 ≤
      (TreeMissingColors sigma (corrT.replacementETT.series.data.tree
        (Fin.last corrT.replacementETT.rounds).castSucc)).card := by
    rw [hterminalTree, missingTree Tn (TreeSequenceInitialSegmentVertexSetSubset hTnA),
      corrT.rungAgreement]
    exact hlarge
  have hthetaSigmaA : theta ∈ TreeMissingColors sigma A := by
    rw [missingTree A (fun _ h => h)]
    exact hthetaA
  have hgammaSigmaA : gamma ∈ TreeMissingColors sigma A := by
    rw [missingTree A (fun _ h => h)]
    exact hgammaA
  have hthetaClosedSigma : TreeColorSetClosed G sigma A {theta} := by
    intro c hc
    rw [boundaryEq A (fun _ h => h) c]
    exact hthetaClosed c hc
  have hresult := ChangeLemmaBothInside G k e0 corrT.replacementInput T sigma
    corrT.replacementETT baseT Cs hstableA.1 hstableA.2.1
    (fun lower hp hl hm =>
      hlower lower hp (lt_of_lt_of_eq hl corrT.rungAgreement) hm)
    (fun other hr hm b J g hj =>
      hfewer other (hr.trans corrT.rungAgreement) hm b J g hj)
    (fun C' hr hq => by
      rw [measureEq]
      exact hminimal C' (hr.trans corrT.rungAgreement) hq)
    hprefixSigma hlargeSigma theta gamma hthetaGamma
    (by
      dsimp only
      change theta ∈ TreeMissingColors sigma
          (TreeSequencePrefix T
            (min ((HierarchyStarredStage K (Fin.last K.dividerCount)).length +
              (T.length - (HierarchyStarredStage K (Fin.last K.dividerCount)).length - 1))
              T.length) _ _) ∧
        gamma ∈ TreeMissingColors sigma
          (TreeSequencePrefix T
            (min ((HierarchyStarredStage K (Fin.last K.dividerCount)).length +
              (T.length - (HierarchyStarredStage K (Fin.last K.dividerCount)).length - 1))
              T.length) _ _)
      rw [hprefixK]
      exact ⟨hthetaSigmaA, hgammaSigmaA⟩)
    (by
      dsimp only
      change (theta ∉ TreeMissingColors sigma
          (HierarchyStarredStage K (Fin.last K.dividerCount)) ∨
        gamma ∉ TreeMissingColors sigma
          (HierarchyStarredStage K (Fin.last K.dividerCount))) → _
      rw [hstarK]
      intro hbad
      exact False.elim (hbad.elim (fun h => h hthetaSigmaA) (fun h => h hgammaSigmaA)))
    (by
      change T.vertex (HierarchyFirstMissingPosition sigma T theta) ∈
          TreeSequenceVertexSet (HierarchyStarredStage K (Fin.last K.dividerCount)) ∧
        T.vertex (HierarchyFirstMissingPosition sigma T gamma) ∈
          TreeSequenceVertexSet (HierarchyStarredStage K (Fin.last K.dividerCount))
      rw [hstarK, firstMissingEq theta, firstMissingEq gamma]
      exact ⟨(missingFirstInA theta hthetaA).2, (missingFirstInA gamma hgammaA).2⟩)
  have hinterSigma : TreeInterchangeable G A sigma theta gamma := by
    have hh := hresult.2.2
    change (theta ∈ TreeMissingColors sigma (HierarchyStarredStage K (Fin.last K.dividerCount)) ∧
      TreeColorSetClosed G sigma (HierarchyStarredStage K (Fin.last K.dividerCount)) {theta}) → _ at hh
    rw [hstarK] at hh
    exact (hh ⟨hthetaSigmaA, hthetaClosedSigma⟩).2
  have hswap := TwoColorComponentSwapMissingBehavior G phi theta alpha
    hthetaAlpha hproper (Sum.inl y)
  have hthetaySigma : theta ∈ MissingColors G sigma y := hswap.2.2.1 y rfl halphay
  have hout := outsideMissingComponent sigma hstableA.1 theta gamma hthetaGamma
    hthetaSigmaA hgammaSigmaA y hyOutside (Or.inl hthetaySigma) hinterSigma
  have hgammafSigma : sigma f = some gamma := (hfixedEdges r).trans hgammaf
  obtain ⟨u, huA, hends⟩ := hfEnds
  have hyf : (TwoColorIncidenceGraph G sigma theta gamma).Adj (Sum.inl y) (Sum.inr f) := by
    refine ⟨?_, Or.inr hgammafSigma⟩
    change y ∈ G.ends f
    rw [hends]
    exact Sym2.mem_mk_right _ _
  have hfu : (TwoColorIncidenceGraph G sigma theta gamma).Adj (Sum.inr f) (Sum.inl u) := by
    refine ⟨?_, Or.inr hgammafSigma⟩
    change u ∈ G.ends f
    rw [hends]
    exact Sym2.mem_mk_left _ _
  apply hout u huA
  change (TwoColorIncidenceGraph G sigma theta gamma).connectedComponentMk (Sum.inl u) =
    (TwoColorIncidenceGraph G sigma theta gamma).connectedComponentMk (Sum.inl y)
  exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hfu).symm.trans
    (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hyf).symm
