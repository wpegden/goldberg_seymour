import Tablet.BoundaryColorEdges
import Tablet.ColoredVertexSetElementary
import Tablet.CombinedStableClosurePreserved
import Tablet.CombinedStableColoring
import Tablet.CorrespondingExtendedTashkinovTree
import Tablet.GoodHierarchy
import Tablet.HierarchyBase
import Tablet.HierarchyCounterexample
import Tablet.HierarchyCounterexampleLess
import Tablet.HierarchyCounterexampleMeasure
import Tablet.HierarchyFirstMissingPosition
import Tablet.HierarchyPathNumber
import Tablet.HierarchySegmentColors
import Tablet.HierarchySplitter
import Tablet.HierarchyStageMissingColors
import Tablet.HierarchyStarredStage
import Tablet.HierarchyStoredColorsAt
import Tablet.HkuTreeColorsControlled
import Tablet.IsOneEdgeUncolored
import Tablet.IsProperEdgeColoring
import Tablet.MaximumDefectiveChoice
import Tablet.MaximumProperty
import Tablet.MaximumPropertyTransport
import Tablet.ModColoring
import Tablet.MissingColors
import Tablet.PresentColors
import Tablet.RevisitingExtensionCertificate
import Tablet.SameGoodHierarchy
import Tablet.SameHierarchyStages
import Tablet.StableColoring
import Tablet.TashkinovAugmentation
import Tablet.TashkinovAugmentationSequence
import Tablet.TashkinovAugmentationSequenceRestrict
import Tablet.TashkinovHierarchy
import Tablet.TashkinovSeriesStep
import Tablet.TashkinovStoredColors
import Tablet.Td
import Tablet.TreeColorSetMinusClosed
import Tablet.TreeSequenceInitialSegment
import Tablet.TreeSequencePrefix
import Tablet.TreeVertexOrder
import Tablet.TwoColorComponent
import Tablet.TwoColorComponentSwap
import Tablet.TwoColorComponentSwapProper
import Tablet.TwoColorComponentsDisjoint
import Tablet.GoodHierarchyTerminalPrefixRepackage
import Tablet.TreeSequenceInitialSegmentVertexSetSubset
import Tablet.TashkinovAugmentationSequenceInitialSegment
import Tablet.TashkinovAugmentationSequencePosition
import Tablet.TwoColorComponentSwapMissingBehavior

-- [TABLET NODE: ChangeLemmaBothOutside]
theorem ChangeLemmaBothOutside {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
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
    (hprefixElementary :
      let H := C.hierarchy
      let A := HierarchyStarredStage H (Fin.last H.dividerCount)
      let ell := T.length - A.length
      let Ty := TreeSequencePrefix T
        (min (A.length + (ell - 1)) T.length)
        (by have hA := A.positive; have hT := T.positive; omega)
        (Nat.min_le_right _ _)
      ColoredVertexSetElementary G phi (TreeSequenceVertexSet Ty))
    (hlarge :
      let n : Fin (ett.rounds + 1) := Fin.last ett.rounds
      let Tn := ett.series.data.tree n.castSucc
      2 * ett.rounds + 11 ≤ (TreeMissingColors phi Tn).card)
    (alpha beta : Fin k) (hne : alpha ≠ beta)
    (hmissingPrefix :
      let H := C.hierarchy
      let A := HierarchyStarredStage H (Fin.last H.dividerCount)
      let ell := T.length - A.length
      let Ty := TreeSequencePrefix T
        (min (A.length + (ell - 1)) T.length)
        (by have hA := A.positive; have hT := T.positive; omega)
        (Nat.min_le_right _ _)
      alpha ∈ TreeMissingColors phi Ty ∧
        beta ∈ TreeMissingColors phi Ty)
    (horderedUnused :
      let H := C.hierarchy
      let q : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
      let A := HierarchyStarredStage H q
      let ia := HierarchyFirstMissingPosition phi T alpha
      let ib := HierarchyFirstMissingPosition phi T beta
      (alpha ∉ TreeMissingColors phi A ∨ beta ∉ TreeMissingColors phi A) →
        TreeVertexOrder T (T.vertex ia) (T.vertex ib) ∧
          alpha ∉ (Finset.univ.filter fun c =>
            ∃ t : Fin T.length,
              A.length ≤ t.val ∧ t.val < ib.val ∧
                phi (T.edge t) = some c))
    (hlocation :
      let H := C.hierarchy
      let q : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
      let A := HierarchyStarredStage H q
      let va := T.vertex (HierarchyFirstMissingPosition phi T alpha)
      let vb := T.vertex (HierarchyFirstMissingPosition phi T beta)
      va ∉ TreeSequenceVertexSet A ∧
        vb ∉ TreeSequenceVertexSet A) :
    let H := C.hierarchy
    let q : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
    let n : Fin (ett.rounds + 1) := Fin.last ett.rounds
    let A := HierarchyStarredStage H q
    let Tnq := H.stage ⟨H.dividerCount, by omega⟩
    let Tn := ett.series.data.tree n.castSucc
    let Dn := TashkinovStoredColors ett.series.data n
    let Dnq := HierarchyStoredColorsAt H q
    let va := T.vertex (HierarchyFirstMissingPosition phi T alpha)
    let vb := T.vertex (HierarchyFirstMissingPosition phi T beta)
    let sameComponent := TwoColorComponent G phi alpha beta (Sum.inl va) =
      TwoColorComponent G phi alpha beta (Sum.inl vb)
    (0 < H.dividerCount ∧
        (alpha ∈ TreeMissingColors phi Tnq ∨
          Disjoint ({alpha, beta} : Finset (Fin k)) Dnq) →
      sameComponent) ∧
    (H.dividerCount = 0 ∧
        (alpha ∈ TreeMissingColors phi Tn ∨
          Disjoint ({alpha, beta} : Finset (Fin k)) Dn) →
      sameComponent) := by
-- BODY
  classical
  let H := C.hierarchy
  let q : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
  let A := HierarchyStarredStage H q
  let n : Fin (ett.rounds + 1) := Fin.last ett.rounds
  let Tn := ett.series.data.tree n.castSucc
  let Dn := TashkinovStoredColors ett.series.data n
  let ia := HierarchyFirstMissingPosition phi T alpha
  let ib := HierarchyFirstMissingPosition phi T beta
  let va := T.vertex ia
  let vb := T.vertex ib
  let ell := T.length - A.length
  let yLength := min (A.length + (ell - 1)) T.length
  let Y := TreeSequencePrefix T yLength
    (by have hA := A.positive; have hT := T.positive; omega)
    (Nat.min_le_right _ _)
  have segRefl (S : TreeSequence G e0) : TreeSequenceInitialSegment S S :=
    ⟨le_rfl, (by intro i; rfl), (by intro i; rfl)⟩
  have segTrans {S U W : TreeSequence G e0}
      (hSU : TreeSequenceInitialSegment S U)
      (hUW : TreeSequenceInitialSegment U W) :
      TreeSequenceInitialSegment S W := by
    refine ⟨le_trans hSU.1 hUW.1, ?_, ?_⟩
    · intro i
      exact (hUW.2.1 (Fin.castLE (Nat.succ_le_succ hSU.1) i)).trans (hSU.2.1 i)
    · intro i
      exact (hUW.2.2 (Fin.castLE hSU.1 i)).trans (hSU.2.2 i)
  have commonPrefix {S U W : TreeSequence G e0}
      (hSW : TreeSequenceInitialSegment S W)
      (hUW : TreeSequenceInitialSegment U W) (hlen : S.length ≤ U.length) :
      TreeSequenceInitialSegment S U := by
    refine ⟨hlen, ?_, ?_⟩
    · intro i
      exact (hUW.2.1 (Fin.castLE (Nat.succ_le_succ hlen) i)).symm.trans (hSW.2.1 i)
    · intro i
      exact (hUW.2.2 (Fin.castLE hlen i)).symm.trans (hSW.2.2 i)
  have stageSegment (a d : ℕ) (hbound : a + d ≤ H.dividerCount + 1) :
      TreeSequenceInitialSegment (H.stage ⟨a, by omega⟩)
        (H.stage ⟨a + d, by omega⟩) := by
    induction d with
    | zero => simpa using segRefl (H.stage ⟨a, by omega⟩)
    | succ d ih =>
      exact segTrans (ih (by omega)) (H.nested ⟨a + d, by omega⟩)
  have stageToT (j : Fin (H.dividerCount + 2)) :
      TreeSequenceInitialSegment (H.stage j) T := by
    have hs := stageSegment j.val (H.dividerCount + 1 - j.val) (by omega)
    have he : (⟨j.val + (H.dividerCount + 1 - j.val), by omega⟩ :
        Fin (H.dividerCount + 2)) = Fin.last (H.dividerCount + 1) :=
      Fin.ext (by simp only [Fin.val_mk, Fin.val_last]; have := j.isLt; omega)
    simpa [he, H.terminalStage] using hs
  have lastZero (hz : H.dividerCount = 0) : A = base.core := by
    simp [A, q, HierarchyStarredStage, hz, Fin.last]
  have lastPositive (hz : H.dividerCount ≠ 0) :
      A = H.stage ⟨H.dividerCount, by omega⟩ := by
    obtain hzero | ⟨i, hi⟩ := Fin.eq_zero_or_eq_succ q
    · have hv := congrArg Fin.val hzero
      simp [q] at hv
      exact (hz hv).elim
    · simp only [A, HierarchyStarredStage, hi, Fin.cases_succ]
      congr 1
      apply Fin.ext
      have hv := congrArg Fin.val hi
      simpa [q] using hv.symm
  have coreToA : TreeSequenceInitialSegment base.core A := by
    by_cases hz : H.dividerCount = 0
    · rw [lastZero hz]
      exact segRefl _
    · rw [lastPositive hz]
      have hs := stageSegment 1 (H.dividerCount - 1) (by omega)
      have he : 1 + (H.dividerCount - 1) = H.dividerCount := by omega
      simpa [he] using segTrans H.coreInsideFirst hs
  have TnToCore : TreeSequenceInitialSegment Tn base.core := by
    by_cases hp : ett.series.data.kind n = some TashkinovExtensionKind.PE
    · exact (Classical.choice (base.parallel hp).2.2).leftSegment
    · rw [base.nonparallel hp]
      exact segRefl _
  have TnToA := segTrans TnToCore coreToA
  have AToT : TreeSequenceInitialSegment A T := by
    by_cases hz : H.dividerCount = 0
    · rw [lastZero hz]
      exact segTrans H.coreInsideFirst (stageToT ⟨1, by omega⟩)
    · rw [lastPositive hz]
      exact stageToT _
  have ordinaryToA (j : Fin (H.dividerCount + 1)) :
      TreeSequenceInitialSegment (H.stage j.castSucc) A := by
    by_cases hz : H.dividerCount = 0
    · have hj : j.castSucc = (0 : Fin (H.dividerCount + 2)) := Fin.ext (by simp; omega)
      rw [hj, H.baseStage]
      exact TnToA
    · have hs := stageSegment j.val (H.dividerCount - j.val) (by omega)
      rw [lastPositive hz]
      convert hs using 1 <;> apply congrArg H.stage <;> apply Fin.ext <;>
        simp only [Fin.val_castSucc, Fin.val_mk] <;> omega
  have starredToA (j : Fin (H.dividerCount + 1)) :
      TreeSequenceInitialSegment (HierarchyStarredStage H j) A := by
    exact Fin.cases coreToA (fun i => ordinaryToA i.succ) j
  have YToT : TreeSequenceInitialSegment Y T :=
    ⟨Nat.min_le_right _ _, (by intro i; rfl), (by intro i; rfl)⟩
  have hmissingY : alpha ∈ TreeMissingColors phi Y ∧ beta ∈ TreeMissingColors phi Y :=
    hmissingPrefix
  have hElementaryY : ColoredVertexSetElementary G phi (TreeSequenceVertexSet Y) :=
    hprefixElementary
  have firstMissing (c : Fin k) (hc : c ∈ TreeMissingColors phi Y) :
      c ∈ MissingColors G phi (T.vertex (HierarchyFirstMissingPosition phi T c)) ∧
        (HierarchyFirstMissingPosition phi T c).val ≤ Y.length := by
    obtain ⟨v, hv, hcv⟩ := Finset.mem_biUnion.mp hc
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and] at hv
    obtain ⟨i, hi⟩ := hv
    let it := Fin.castLE (Nat.succ_le_succ YToT.1) i
    have hci : c ∈ MissingColors G phi (T.vertex it) := by
      rw [YToT.2.1 i, hi]
      exact hcv
    let candidates := Finset.univ.filter fun j => c ∈ MissingColors G phi (T.vertex j)
    have hit : it ∈ candidates := by simp [candidates, hci]
    have hnon : candidates.Nonempty := ⟨it, hit⟩
    have hmem := Finset.min'_mem candidates hnon
    have hle := Finset.min'_le candidates it hit
    refine ⟨?_, ?_⟩
    · simpa [HierarchyFirstMissingPosition, candidates, hnon] using
        (Finset.mem_filter.mp hmem).2
    · have hiv : it.val ≤ Y.length := Nat.le_of_lt_succ i.isLt
      have hval : (candidates.min' hnon).val ≤ it.val := hle
      simpa [HierarchyFirstMissingPosition, candidates, hnon] using le_trans hval hiv
  have ha := firstMissing alpha hmissingY.1
  have hb := firstMissing beta hmissingY.2
  have vertexY (i : Fin (T.length + 1)) (hi : i.val ≤ Y.length) :
      T.vertex i ∈ TreeSequenceVertexSet Y := by
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨⟨i.val, by omega⟩, rfl⟩
  have haY : va ∈ TreeSequenceVertexSet Y := vertexY ia ha.2
  have hbY : vb ∈ TreeSequenceVertexSet Y := vertexY ib hb.2
  have hout : va ∉ TreeSequenceVertexSet A ∧ vb ∉ TreeSequenceVertexSet A := hlocation
  have outsideIndex (i : Fin (T.length + 1))
      (hi : T.vertex i ∉ TreeSequenceVertexSet A) : A.length < i.val := by
    by_contra h
    have hle : i.val ≤ A.length := by omega
    apply hi
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨⟨i.val, by omega⟩, (AToT.2.1 ⟨i.val, by omega⟩).symm⟩
  have hAia := outsideIndex ia hout.1
  have hAib := outsideIndex ib hout.2
  have AToY : TreeSequenceInitialSegment A Y :=
    commonPrefix AToT YToT (by omega)
  have missingNotA (c : Fin k) (i : Fin (T.length + 1))
      (hmi : c ∈ MissingColors G phi (T.vertex i))
      (hiy : T.vertex i ∈ TreeSequenceVertexSet Y)
      (hia : T.vertex i ∉ TreeSequenceVertexSet A) : c ∉ TreeMissingColors phi A := by
    intro hc
    obtain ⟨v, hv, hcv⟩ := Finset.mem_biUnion.mp hc
    have hne : v ≠ T.vertex i := by intro he; exact hia (he ▸ hv)
    exact (Finset.disjoint_left.mp
      (hElementaryY (TreeSequenceInitialSegmentVertexSetSubset AToY hv) hiy hne)) hcv hmi
  have halphaA : alpha ∉ TreeMissingColors phi A := missingNotA alpha ia ha.1 haY hout.1
  have hbetaA : beta ∉ TreeMissingColors phi A := missingNotA beta ib hb.1 hbY hout.2
  have horder := horderedUnused (Or.inl halphaA)
  have habIndex : ia.val < ib.val := by
    obtain ⟨i, j, hi, hj, hij⟩ := horder.1
    have hei := T.vertex_injective hi
    have hej := T.vertex_injective hj
    simpa [hei, hej] using hij
  have havb : va ≠ vb := by
    intro he
    have hi := congrArg Fin.val (T.vertex_injective he)
    omega
  -- Keep the exact ordered prefix ending at the beta-missing vertex.
  let B := TreeSequencePrefix T ib.val (by have := A.positive; omega)
    (Nat.le_of_lt_succ ib.isLt)
  have BToT : TreeSequenceInitialSegment B T :=
    ⟨Nat.le_of_lt_succ ib.isLt, (by intro i; rfl), (by intro i; rfl)⟩
  have AToB : TreeSequenceInitialSegment A B := commonPrefix AToT BToT (by exact le_of_lt hAib)
  have ABstrict : A.length < B.length := hAib
  have BToY : TreeSequenceInitialSegment B Y := commonPrefix BToT YToT hb.2
  have BstrictT : B.length < T.length := by
    have hAT := AToT.1
    have hY : Y.length = min (A.length + (T.length - A.length - 1)) T.length := rfl
    have hBY := BToY.1
    have hAB := ABstrict
    omega
  obtain ⟨ettB, hMPB, hrB, hsB, baseB, hcoreB, hclosureB, hsupportB,
      HB, hcountB, hstagesB, hdividersB, goodB, hgoodB⟩ :=
    GoodHierarchyTerminalPrefixRepackage G k e0 input T phi phi ett C.maximum
      base H C.good B AToB ABstrict BToT
  rcases ettB with ⟨rB, rpB, seriesB, aboveB, strictB, belowB, genB⟩
  cases hrB
  have heqB : seriesB = ett.series := eq_of_heq hsB
  cases heqB
  let ettB : ExtendedTashkinovTree G k e0 input B phi :=
    ⟨ett.rounds, rpB, ett.series, aboveB, strictB, belowB, genB⟩
  have missingSubset {S U : TreeSequence G e0} (hSU : TreeSequenceInitialSegment S U) :
      TreeMissingColors phi S ⊆ TreeMissingColors phi U := by
    intro c hc
    obtain ⟨v, hv, hcv⟩ := Finset.mem_biUnion.mp hc
    exact Finset.mem_biUnion.mpr
      ⟨v, TreeSequenceInitialSegmentVertexSetSubset hSU hv, hcv⟩
  have outsideStored (hcase :
      (0 < H.dividerCount ∧ (alpha ∈ TreeMissingColors phi (H.stage ⟨H.dividerCount, by omega⟩) ∨
        Disjoint ({alpha, beta} : Finset (Fin k)) (HierarchyStoredColorsAt H q))) ∨
      (H.dividerCount = 0 ∧ (alpha ∈ TreeMissingColors phi Tn ∨
        Disjoint ({alpha, beta} : Finset (Fin k)) Dn))) :
      alpha ∉ Dn ∧ beta ∉ Dn := by
    rcases hcase with ⟨hp, hm | hd⟩ | ⟨hz, hm | hd⟩
    · exact (halphaA (by simpa [lastPositive (by omega)] using hm)).elim
    · have hn (c : Fin k) (hc : c ∈ ({alpha, beta} : Finset (Fin k)))
          (hcm : c ∉ TreeMissingColors phi A) : c ∉ Dn := by
        intro hcd
        apply Finset.disjoint_left.mp hd hc
        exact Finset.mem_sdiff.mpr ⟨hcd, hcm⟩
      exact ⟨hn alpha (by simp) halphaA, hn beta (by simp) hbetaA⟩
    · exact (halphaA (missingSubset TnToA hm)).elim
    · exact ⟨fun hc => Finset.disjoint_left.mp hd (by simp) hc,
        fun hc => Finset.disjoint_left.mp hd (by simp) hc⟩
  have finish (hDn : alpha ∉ Dn ∧ beta ∉ Dn) :
      TwoColorComponent G phi alpha beta (Sum.inl va) =
        TwoColorComponent G phi alpha beta (Sum.inl vb) := by
    by_contra hcomponents
    let K := TwoColorComponent G phi alpha beta (Sum.inl vb)
    let sigma := TwoColorComponentSwap G phi alpha beta (Sum.inl vb)
    have hdisjoint : Disjoint (TwoColorComponent G phi alpha beta (Sum.inl va)) K :=
      (TwoColorComponentsDisjoint G phi alpha beta (Sum.inl va) (Sum.inl vb)).resolve_left
        hcomponents
    have haK : Sum.inl va ∉ K := by
      intro h
      exact Set.disjoint_left.mp hdisjoint (show Sum.inl va ∈
        TwoColorComponent G phi alpha beta (Sum.inl va) from rfl) h
    have behavior := TwoColorComponentSwapMissingBehavior G phi alpha beta hne hproper
      (Sum.inl vb)
    have edgeOfVertex {v : V} {f : E} (hv : Sum.inl v ∈ K)
        (hf : Incident G v f) (hc : phi f = some alpha ∨ phi f = some beta) :
        Sum.inr f ∈ K := by
      have hadj : (TwoColorIncidenceGraph G phi alpha beta).Adj (Sum.inr f) (Sum.inl v) :=
        ⟨hf, hc⟩
      exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj).trans hv
    have unaffected (f : E) (c : Fin k) (hca : c ≠ alpha) (hcb : c ≠ beta) :
        sigma f = some c ↔ phi f = some c := by
      by_cases hf : Sum.inr f ∈ K
      · by_cases ha : phi f = some alpha
        · simp [sigma, TwoColorComponentSwap, K, hf, ha, hca.symm, hcb.symm]
        · by_cases hb : phi f = some beta
          · simp [sigma, TwoColorComponentSwap, K, hf, ha, hb, hne.symm,
              hca.symm, hcb.symm]
          · simp [sigma, TwoColorComponentSwap, K, hf, ha, hb]
      · simp [sigma, TwoColorComponentSwap, K, hf]
    have fixedValue (f : E) (ha : phi f ≠ some alpha) (hb : phi f ≠ some beta) :
        sigma f = phi f := by
      simp [sigma, TwoColorComponentSwap, ha, hb]
    have sigmaProper : IsProperEdgeColoring G sigma :=
      TwoColorComponentSwapProper G phi alpha beta hne hproper _
    have sigmaOne : IsOneEdgeUncolored sigma e0 := by
      refine ⟨?_, ?_⟩
      · simp [sigma, TwoColorComponentSwap, hone.1]
      · intro f hf
        obtain ⟨c, hc⟩ := hone.2 f hf
        by_cases ha : c = alpha
        · subst c
          by_cases hK : Sum.inr f ∈ K
          · exact ⟨beta, by simp [sigma, TwoColorComponentSwap, K, hK, hc]⟩
          · exact ⟨alpha, by simp [sigma, TwoColorComponentSwap, K, hK, hc]⟩
        · by_cases hb : c = beta
          · subst c
            by_cases hK : Sum.inr f ∈ K
            · exact ⟨alpha, by simp [sigma, TwoColorComponentSwap, K, hK, hc, hne.symm]⟩
            · exact ⟨beta, by simp [sigma, TwoColorComponentSwap, K, hK, hc]⟩
          · exact ⟨c, (unaffected f c ha hb).mpr hc⟩
    have vertexB (i : Fin (T.length + 1)) (hi : i.val ≤ B.length) :
        T.vertex i ∈ TreeSequenceVertexSet B := by
      simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
      exact ⟨⟨i.val, by omega⟩, rfl⟩
    have haB : va ∈ TreeSequenceVertexSet B := vertexB ia (le_of_lt habIndex)
    have hbB : vb ∈ TreeSequenceVertexSet B := vertexB ib le_rfl
    -- Elementarity fixes missing sets before the swapped endpoint, even inside its component.
    have missingBefore (v : V) (hv : v ∈ TreeSequenceVertexSet B) (hvb : v ≠ vb) :
        MissingColors G sigma v = MissingColors G phi v := by
      by_cases hvK : Sum.inl v ∈ K
      · have hva : v ≠ va := by intro he; exact haK (he ▸ hvK)
        have hvY := TreeSequenceInitialSegmentVertexSetSubset BToY hv
        have han : alpha ∉ MissingColors G phi v := fun hc =>
          Finset.disjoint_left.mp (hElementaryY hvY haY hva) hc ha.1
        have hbn : beta ∉ MissingColors G phi v := fun hc =>
          Finset.disjoint_left.mp (hElementaryY hvY hbY hvb) hc hb.1
        have hpa : ∃ f, Incident G v f ∧ phi f = some alpha := by
          simpa [MissingColors, PresentColors] using han
        have hpb : ∃ f, Incident G v f ∧ phi f = some beta := by
          simpa [MissingColors, PresentColors] using hbn
        obtain ⟨fa, hfa, hfca⟩ := hpa
        obtain ⟨fb, hfb, hfcb⟩ := hpb
        have hfaK := edgeOfVertex hvK hfa (Or.inl hfca)
        have hfbK := edgeOfVertex hvK hfb (Or.inr hfcb)
        have hnewa : sigma fb = some alpha := by
          simp [sigma, TwoColorComponentSwap, K, hfbK, hfcb, hne.symm]
        have hnewb : sigma fa = some beta := by
          simp [sigma, TwoColorComponentSwap, K, hfaK, hfca]
        have hana : alpha ∉ MissingColors G sigma v := by
          simp only [MissingColors, Finset.mem_sdiff, Finset.mem_univ, true_and,
            PresentColors, Finset.mem_filter, not_not]
          exact ⟨fb, hfb, hnewa⟩
        have hbnb : beta ∉ MissingColors G sigma v := by
          simp only [MissingColors, Finset.mem_sdiff, Finset.mem_univ, true_and,
            PresentColors, Finset.mem_filter, not_not]
          exact ⟨fa, hfa, hnewb⟩
        ext c
        by_cases hca : c = alpha
        · subst c; simp [hana, han]
        · by_cases hcb : c = beta
          · subst c; simp [hbnb, hbn]
          · exact behavior.2.2.2 v c hca hcb
      · exact behavior.1 v hvK
    have hnewa : alpha ∈ MissingColors G sigma va := by
      rw [behavior.1 va haK]
      exact ha.1
    have hnewb : alpha ∈ MissingColors G sigma vb :=
      behavior.2.2.1 vb (show Sum.inl vb ∈ K from rfl) hb.1
    have sigmaNotElementary : ¬ ColoredVertexSetElementary G sigma (TreeSequenceVertexSet B) :=
      fun he => Finset.disjoint_left.mp (he haB hbB havb) hnewa hnewb
    have missingA (v : V) (hv : v ∈ TreeSequenceVertexSet A) :
        MissingColors G sigma v = MissingColors G phi v :=
      missingBefore v (TreeSequenceInitialSegmentVertexSetSubset AToB hv)
        (by intro he; exact hout.2 (he ▸ hv))
    have treeMissingEq (S : TreeSequence G e0)
        (hS : TreeSequenceVertexSet S ⊆ TreeSequenceVertexSet A) :
        TreeMissingColors sigma S = TreeMissingColors phi S := by
      unfold TreeMissingColors
      exact Finset.biUnion_congr rfl (fun v hv => missingA v (hS hv))
    have stable (S : TreeSequence G e0) (hS : TreeSequenceVertexSet S ⊆ TreeSequenceVertexSet A)
        (D : Finset (Fin k)) (hD : alpha ∉ D ∧ beta ∉ D) :
        StableColoring S D phi sigma := by
      refine ⟨?_, fun v hv => missingA v (hS hv)⟩
      intro f hf hcontrol
      obtain ⟨c, hc, hcol⟩ := hcontrol
      have hnot (d : Fin k) (hdA : d ∉ TreeMissingColors phi A) (hdD : d ∉ D) : c ≠ d := by
        intro he; subst c
        rcases Finset.mem_union.mp hc with hm | hm
        · obtain ⟨v, hv, hcv⟩ := Finset.mem_biUnion.mp hm
          exact hdA (Finset.mem_biUnion.mpr ⟨v, hS hv, hcv⟩)
        · exact hdD hm
      exact ((unaffected f c (hnot alpha halphaA hD.1) (hnot beta hbetaA hD.2)).mpr hcol).trans
        hcol.symm
    have stableTn : StableColoring Tn Dn phi sigma :=
      stable Tn (TreeSequenceInitialSegmentVertexSetSubset TnToA) Dn hDn
    have TnToB := segTrans TnToA AToB
    have TnStrictB : Tn.length < B.length := lt_of_le_of_lt TnToA.1 ABstrict
    have BToFinal := segTrans BToT ett.belowFinal
    have notControlled (c : Fin k) (hc : c = alpha ∨ c = beta) :
        c ∉ TreeMissingColors phi Tn ∪ Dn := by
      intro hm
      rcases Finset.mem_union.mp hm with hm | hm
      · rcases hc with rfl | rfl
        · exact halphaA (missingSubset TnToA hm)
        · exact hbetaA (missingSubset TnToA hm)
      · rcases hc with rfl | rfl
        · exact hDn.1 hm
        · exact hDn.2 hm
    have storedOrMissing (c : Fin k) (hc : c ∈ ett.series.data.stored n) :
        c ∈ TreeMissingColors phi Tn ∪ Dn := by
      by_cases hm : c ∈ TreeMissingColors phi Tn
      · exact Finset.mem_union_left _ hm
      · apply Finset.mem_union_right
        unfold Dn TashkinovStoredColors
        have hn : n.val ≠ 0 := by dsimp [n]; have := C.positive; omega
        simp only [if_neg hn]
        refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
        · exact Finset.mem_biUnion.mpr ⟨n, Finset.mem_univ _, by simp [hc]⟩
        · have hg : ett.series.data.coloring n = phi := ett.generatingColoring.symm
          simpa only [hg, Tn] using hm
    -- Nonparallel extensions retain the certified connecting edge and one-edge seed.
    have terminalRoute :
        (ett.series.data.kind n = some TashkinovExtensionKind.PE ∧
          TashkinovAugmentationSequence phi Tn B) ∨
        ((ett.series.data.kind n = some TashkinovExtensionKind.SE ∨
          ett.series.data.kind n = some TashkinovExtensionKind.RE) ∧
          ∃ (f : E) (seed : TreeSequence G e0),
            ett.series.data.connectingEdges n = {f} ∧ TreeSequenceAdjoinEdge Tn f seed ∧
            TashkinovAugmentationSequence phi seed B ∧
            phi f ≠ some alpha ∧ phi f ≠ some beta) := by
      have step := ett.series.certified n
      generalize hi : n = i at step
      cases step with
      | initial => have hv := congrArg Fin.val hi; simp [n] at hv; have := C.positive; omega
      | SE j _ _ _ _ _ choice _ coloring stored edges kind vertex outside delta gamma
          seed adjoin closure ordered strict =>
        have hj : j.succ = n := hi.symm
        have hlast : j.succ.succ = Fin.last (ett.rounds + 1) :=
          Fin.ext (by have hv := congrArg Fin.val hj; simp [n] at hv ⊢; omega)
        have hroute : TashkinovAugmentationSequence phi seed
            (ett.series.data.tree (Fin.last (ett.rounds + 1))) := by
          simpa [hj, hlast, ← ett.generatingColoring, n] using closure.1
        have hseedB : TreeSequenceInitialSegment seed B :=
          commonPrefix (TashkinovAugmentationSequenceInitialSegment phi _ _ hroute)
            BToFinal (by have hl := adjoin.1; rw [hj] at hl; change seed.length = Tn.length + 1 at hl; omega)
        have hcol : phi choice.edge = some choice.color := by
          have hg : phi = choice.selected := by
            simpa only [← hj, coloring, n] using ett.generatingColoring
          simpa only [hg] using choice.edgeColor
        have hc : choice.color ∈ ett.series.data.stored n := by rw [← hj, stored]; simp
        have hnot (c : Fin k) (he : c = alpha ∨ c = beta) : phi choice.edge ≠ some c := by
          intro hc'
          have heq := Option.some.inj (hcol.symm.trans hc')
          exact notControlled c he (heq ▸ storedOrMissing choice.color hc)
        exact Or.inr ⟨Or.inl (by simpa [hj] using kind), choice.edge, seed,
          by simpa [hj] using edges, by simpa [Tn, hj] using adjoin,
          TashkinovAugmentationSequenceRestrict phi seed B _ hroute hseedB BToFinal,
          hnot alpha (Or.inl rfl), hnot beta (Or.inr rfl)⟩
      | PE j _ _ _ _ _ choice _ gamma _ second _ _ _ exit coloring proper one stored
          edges kind vertex outside delta gammaEq closure ordered strict =>
        have hj : j.succ = n := hi.symm
        have hlast : j.succ.succ = Fin.last (ett.rounds + 1) :=
          Fin.ext (by have hv := congrArg Fin.val hj; simp [n] at hv ⊢; omega)
        refine Or.inl ⟨by simpa [hj] using kind, ?_⟩
        apply TashkinovAugmentationSequenceRestrict phi Tn B _ _ TnToB BToFinal
        simpa [Tn, hj, hlast, ← ett.generatingColoring, n] using closure.1
      | RE j _ _ _ _ available coloring stored edges kind vertex outside delta gamma
          seed adjoin closure ordered strict =>
        have hj : j.succ = n := hi.symm
        have hlast : j.succ.succ = Fin.last (ett.rounds + 1) :=
          Fin.ext (by have hv := congrArg Fin.val hj; simp [n] at hv ⊢; omega)
        have hroute : TashkinovAugmentationSequence phi seed
            (ett.series.data.tree (Fin.last (ett.rounds + 1))) := by
          simpa [hj, hlast, ← ett.generatingColoring, n] using closure.1
        have hseedB : TreeSequenceInitialSegment seed B :=
          commonPrefix (TashkinovAugmentationSequenceInitialSegment phi _ _ hroute)
            BToFinal (by have hl := adjoin.1; rw [hj] at hl; change seed.length = Tn.length + 1 at hl; omega)
        have hcol : phi available.edge = some available.gamma ∨
            phi available.edge = some available.delta := by
          have hg : phi = ett.series.data.coloring j.castSucc := by
            simpa only [← hj, coloring, n] using ett.generatingColoring
          simp only [hg]
          have hadj := available.returnPath.adj_snd
            (SimpleGraph.Walk.not_nil_of_ne (by intro he; cases he))
          cases hh : available.returnPath.snd with
          | inl v =>
            have hc : (TwoColorIncidenceGraph G (ett.series.data.coloring j.castSucc)
                available.gamma available.delta).Adj (Sum.inr available.edge) (Sum.inl v) :=
              hh ▸ hadj
            exact hc.2
          | inr f =>
            have hc : (TwoColorIncidenceGraph G (ett.series.data.coloring j.castSucc)
                available.gamma available.delta).Adj (Sum.inr available.edge) (Sum.inr f) :=
              hh ▸ hadj
            exact False.elim hc
        have hcontrol : ∃ c, phi available.edge = some c ∧
            c ∈ TreeMissingColors phi Tn ∪ Dn := by
          rcases hcol with h | h
          · exact ⟨available.gamma, h, storedOrMissing _ (by rw [← hj, stored]; simp)⟩
          · exact ⟨available.delta, h, storedOrMissing _ (by rw [← hj, stored]; simp)⟩
        have hnot (c : Fin k) (he : c = alpha ∨ c = beta) : phi available.edge ≠ some c := by
          intro hc'
          obtain ⟨d, hd, hdmem⟩ := hcontrol
          have heq := Option.some.inj (hd.symm.trans hc')
          exact notControlled c he (heq ▸ hdmem)
        exact Or.inr ⟨Or.inr (by simpa [hj] using kind), available.edge, seed,
          by simpa [hj] using edges, by simpa [Tn, hj] using adjoin,
          TashkinovAugmentationSequenceRestrict phi seed B _ hroute hseedB BToFinal,
          hnot alpha (Or.inl rfl), hnot beta (Or.inr rfl)⟩
    have treeControlled (t : Fin Tn.length) :
        phi (Tn.edge t) ≠ some alpha ∧ phi (Tn.edge t) ≠ some beta := by
      by_cases ht : t.val = 0
      · have he : Tn.edge t = e0 := by
          rw [show t = ⟨0, Tn.positive⟩ from Fin.ext ht]
          exact Tn.first_edge
        simp [he, hone.1]
      · let j : Fin ett.rounds := ⟨ett.rounds - 1, by have := C.positive; omega⟩
        have hj : j.succ = n := Fin.ext (by simp [j, n]; have := C.positive; omega)
        have hused (c : Fin k) (hc : phi (Tn.edge t) = some c) :
            c ∈ TreeMissingColors phi Tn ∪ Dn := by
          have hu : c ∈ TreeUsedColors (ett.series.data.coloring j.succ)
              (ett.series.data.tree j.succ.castSucc) := by
            simp only [hj, ← ett.generatingColoring, n]
            simp only [TreeUsedColors, Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨t, by omega, hc⟩
          simpa [hj, ← ett.generatingColoring, Tn, Dn, n] using
            (HkuTreeColorsControlled G k ett.rounds e0 input ett.series j).2.1 hu
        exact ⟨fun hc => notControlled alpha (Or.inl rfl) (hused alpha hc),
          fun hc => notControlled beta (Or.inr rfl) (hused beta hc)⟩
    have augmentationControlled (S : TreeSequence G e0)
        (hseq : TashkinovAugmentationSequence phi S B) (t : Fin B.length)
        (ht : S.length ≤ t.val) :
        phi (B.edge t) ≠ some alpha ∧ phi (B.edge t) ≠ some beta := by
      have hstep := (TashkinovAugmentationSequencePosition phi S B hseq t ht).1
      obtain ⟨hl, hinit, c, hcol, hm⟩ := hstep
      have hcolB : phi (B.edge t) = some c := by
        convert hcol using 1
        congr 2
      obtain ⟨v, hv, hcv⟩ := Finset.mem_biUnion.mp hm
      simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and] at hv
      obtain ⟨iv, hiv⟩ := hv
      let ivT : Fin (T.length + 1) := ⟨iv.val, by have htB := BToT.1; have := iv.isLt; simp only [TreeSequencePrefix] at this; omega⟩
      have hcvT : c ∈ MissingColors G phi (T.vertex ivT) := by
        have he : (TreeSequencePrefix B t.val (le_trans S.positive ht) (Nat.le_of_lt t.isLt)).vertex iv =
            T.vertex ivT := rfl
        rw [← he, hiv]
        exact hcv
      have hnotA : c ≠ alpha := by
        intro he; subst c
        by_cases htA : t.val ≤ A.length
        · apply halphaA
          have hivA : ivT.val ≤ A.length := by
            change iv.val ≤ A.length
            have hiv : iv.val ≤ t.val := Nat.le_of_lt_succ iv.isLt
            omega
          have hvA : T.vertex ivT ∈ TreeSequenceVertexSet A := by
            simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
            exact ⟨⟨ivT.val, by omega⟩, (AToT.2.1 ⟨ivT.val, by omega⟩).symm⟩
          exact Finset.mem_biUnion.mpr ⟨T.vertex ivT, hvA, hcvT⟩
        · apply horder.2
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Fin.castLE BToT.1 t,
            by change A.length ≤ t.val; omega, t.isLt, by rw [BToT.2.2 t]; exact hcolB⟩
      have hnotB : c ≠ beta := by
        intro he; subst c
        have hivB : ivT.val < ib.val := by
          have := iv.isLt
          simp only [TreeSequencePrefix] at this
          have htB : t.val < ib.val := t.isLt
          dsimp [ivT]
          omega
        have hivY : ivT.val ≤ Y.length := by omega
        have hvY := vertexY ivT hivY
        have hneV : T.vertex ivT ≠ vb := by
          intro he
          have hi := congrArg Fin.val (T.vertex_injective he)
          omega
        exact Finset.disjoint_left.mp (hElementaryY hvY hbY hneV) hcvT hb.1
      exact ⟨fun hc => hnotA (Option.some.inj (hcolB.symm.trans hc)),
        fun hc => hnotB (Option.some.inj (hcolB.symm.trans hc))⟩
    have allControlled (t : Fin B.length) :
        phi (B.edge t) ≠ some alpha ∧ phi (B.edge t) ≠ some beta := by
      by_cases ht : t.val < Tn.length
      · have he := TnToB.2.2 ⟨t.val, ht⟩
        have hi : Fin.castLE TnToB.1 ⟨t.val, ht⟩ = t := Fin.ext rfl
        rw [hi] at he
        rw [he]
        exact treeControlled _
      · rcases terminalRoute with ⟨hp, hs⟩ | ⟨hk, f, seed, hedges, hadjoin, hs, hfa, hfb⟩
        · exact augmentationControlled Tn hs t (by omega)
        · by_cases he : t.val = Tn.length
          · have hSB := TashkinovAugmentationSequenceInitialSegment phi seed B hs
            have hi := hSB.2.2 (Fin.cast hadjoin.1.symm (Fin.last Tn.length))
            have hj : Fin.castLE hSB.1 (Fin.cast hadjoin.1.symm (Fin.last Tn.length)) = t :=
              Fin.ext (by simpa using he.symm)
            rw [hj, hadjoin.2.2] at hi
            simpa [hi] using And.intro hfa hfb
          · exact augmentationControlled seed hs t (by have := hadjoin.1; omega)
    have edgesFixed (t : Fin B.length) : sigma (B.edge t) = phi (B.edge t) :=
      fixedValue _ (allControlled t).1 (allControlled t).2
    have routeTransport (S : TreeSequence G e0) (hs : TashkinovAugmentationSequence phi S B) :
        TashkinovAugmentationSequence sigma S B := by
      unfold TashkinovAugmentationSequence at hs ⊢
      induction hs using Relation.ReflTransGen.head_induction_on with
      | refl => exact Relation.ReflTransGen.refl
      | @head U W hstep htail ih =>
        have hWB := TashkinovAugmentationSequenceInitialSegment phi W B htail
        obtain ⟨hlen, hUW, c, hcol, hm⟩ := hstep
        have hUB := segTrans hUW hWB
        have hlt : U.length < B.length := by have := hWB.1; omega
        refine Relation.ReflTransGen.head ⟨hlen, hUW, c, ?_, ?_⟩ ih
        · have hf := edgesFixed (Fin.castLE hWB.1 (Fin.cast hlen.symm (Fin.last U.length)))
          rw [hWB.2.2] at hf
          exact hf.trans hcol
        · obtain ⟨v, hv, hcv⟩ := Finset.mem_biUnion.mp hm
          have hvB := TreeSequenceInitialSegmentVertexSetSubset hUB hv
          have hvb : v ≠ vb := by
            intro he
            simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and] at hv
            obtain ⟨i, hi⟩ := hv
            have ht := hUB.2.1 i
            have htT := BToT.2.1 (Fin.castLE (Nat.succ_le_succ hUB.1) i)
            have eqv : T.vertex (Fin.castLE (Nat.succ_le_succ BToT.1)
                (Fin.castLE (Nat.succ_le_succ hUB.1) i)) = T.vertex ib := htT.trans (ht.trans (hi.trans he))
            have hh := congrArg Fin.val (T.vertex_injective eqv)
            have := i.isLt
            change i.val = ib.val at hh
            change U.length < ib.val at hlt
            omega
          exact Finset.mem_biUnion.mpr ⟨v, hv, by rw [missingBefore v hvB hvb]; exact hcv⟩
    have replacement :
        ∃ corr : CorrespondingExtendedTashkinovTree G k e0 ettB sigma B,
          MaximumProperty corr.replacementETT ∧
          ∃ baseS : HierarchyBase corr.replacementETT sigma,
            ∃ HS : TashkinovHierarchy corr.replacementETT baseS,
              SameHierarchyStages HB HS := by
      by_cases hPE : ett.series.data.kind n = some TashkinovExtensionKind.PE
      · have closureSubset : TreeSequenceVertexSet baseB.closure ⊆ TreeSequenceVertexSet A := by
          obtain ⟨_, _, ⟨u⟩⟩ := baseB.parallel hPE
          intro v hv
          apply TreeSequenceInitialSegmentVertexSetSubset coreToA
          rw [← hcoreB, u.vertexSet]
          exact Finset.mem_union_right _ hv
        have hcombined : CombinedStableColoring Tn baseB.closure Dn phi sigma :=
          ⟨stableTn, stable baseB.closure closureSubset ∅ (by simp)⟩
        have hseq : TashkinovAugmentationSequence sigma Tn B := by
          rcases terminalRoute with ⟨_, hs⟩ | ⟨hk, _⟩
          · exact routeTransport Tn hs
          · rcases hk with hk | hk <;> rw [hPE] at hk <;> cases hk
        exact HierarchySplitter G k e0 input B phi sigma ettB hMPB C.positive
          hlower baseB HB hPE hproper hone sigmaProper sigmaOne hcombined hseq
      · have hmod : ModColoring ettB sigma :=
          Td G k e0 input B phi ettB hMPB C.positive hlower sigma sigmaProper sigmaOne
            (by simpa only [ettB, ← ett.generatingColoring, n, Tn, Dn] using stableTn)
        have hroute :
            ((ettB.series.data.kind (Fin.last ettB.rounds) = some TashkinovExtensionKind.PE ∧
              TashkinovAugmentationSequence sigma Tn B) ∨
            ((ettB.series.data.kind (Fin.last ettB.rounds) = some TashkinovExtensionKind.SE ∨
              ettB.series.data.kind (Fin.last ettB.rounds) = some TashkinovExtensionKind.RE) ∧
              ∃ (f : E) (seed : TreeSequence G e0),
                ettB.series.data.connectingEdges (Fin.last ettB.rounds) = {f} ∧
                TreeSequenceAdjoinEdge Tn f seed ∧ TashkinovAugmentationSequence sigma seed B)) := by
          rcases terminalRoute with ⟨hp, _⟩ | ⟨hk, f, seed, hedges, hadjoin, hs, _⟩
          · exact (hPE hp).elim
          · exact Or.inr ⟨hk, f, seed, hedges, hadjoin, routeTransport seed hs⟩
        obtain ⟨corr⟩ := hmod.2.2 B TnToB TnStrictB hroute
        have hMP := MaximumPropertyTransport G k e0 ettB sigma hmod B corr hMPB
        refine ⟨corr, hMP, ?_⟩
        rcases corr with ⟨newInput, newSeries, newETT, hr, hs, hgen, htrees, hstored,
          hedges, hkinds, hproperSeries, honeSeries, hstableSeries⟩
        rcases newETT with ⟨r, rp, series, above, strict, below, gen⟩
        cases hr
        have heq : series = newSeries := eq_of_heq hs
        cases heq
        let rep : ExtendedTashkinovTree G k e0 newInput B sigma :=
          ⟨ett.rounds, rp, newSeries, above, strict, below, gen⟩
        let j : Fin ett.rounds := ⟨ett.rounds - 1, by have := C.positive; omega⟩
        have hj : j.succ = n := Fin.ext (by simp [j, n]; have := C.positive; omega)
        have htree : newSeries.data.tree n.castSucc = Tn := by simpa [hj, ettB, Tn] using htrees j
        have hkind := hkinds n
        let pos : Fin ((newSeries.data.tree n.castSucc).length + 1) :=
          Fin.cast (congrArg (fun S : TreeSequence G e0 => S.length + 1) htree.symm)
            baseB.supportPosition
        let baseS : HierarchyBase rep sigma :=
          { core := baseB.core
            closure := baseB.closure
            supportPosition := pos
            supportPositive := by simpa [pos] using baseB.supportPositive
            terminalMissingColors := rfl
            parallel := by
              dsimp only [rep]
              intro hp
              exact (hPE (hkind.symm.trans hp)).elim
            nonparallel := by
              dsimp only [rep]
              intro hp
              exact (baseB.nonparallel hPE).trans htree.symm }
        let HS : TashkinovHierarchy rep baseS :=
          { dividerCount := HB.dividerCount
            stage := HB.stage
            baseStage := HB.baseStage.trans htree.symm
            terminalStage := HB.terminalStage
            nested := HB.nested
            strict := HB.strict
            dividerPosition := HB.dividerPosition
            dividerPositive := HB.dividerPositive
            dividerIncreasing := HB.dividerIncreasing
            dividerStage := HB.dividerStage
            coreInsideFirst := HB.coreInsideFirst }
        refine ⟨baseS, HS, ?_⟩
        refine ⟨rfl, rfl, HEq.rfl, HEq.rfl, ?_, ?_⟩
        · exact ⟨fun hp => (hPE hp).elim, fun hp => (hPE (hkind.symm.trans hp)).elim⟩
        · intro hp; exact (hPE hp).elim
    obtain ⟨corr, hMPS, baseS, HS, hsame⟩ := replacement
    have storedS : TashkinovStoredColors corr.replacementETT.series.data
        (Fin.last corr.replacementETT.rounds) = Dn := by
      rcases corr with ⟨newInput, newSeries, newETT, hr, hs, hgen, htrees, hstored,
        hedges, hkinds, hproperSeries, honeSeries, hstableSeries⟩
      rcases newETT with ⟨r, rp, series, above, strict, below, gen⟩
      cases hr
      have heq : series = newSeries := eq_of_heq hs
      cases heq
      let j : Fin ett.rounds := ⟨ett.rounds - 1, by have := C.positive; omega⟩
      have hj : j.succ = n := Fin.ext (by simp [j, n]; have := C.positive; omega)
      have htree : newSeries.data.tree n.castSucc = Tn := by simpa [hj, ettB, Tn] using htrees j
      have hm := treeMissingEq Tn (TreeSequenceInitialSegmentVertexSetSubset TnToA)
      unfold Dn TashkinovStoredColors
      simp only [ettB, hstored, ← hgen, ← ett.generatingColoring, htree, hm, n, Tn]
    have hrS : corr.replacementETT.rounds = ett.rounds := corr.rungAgreement
    have stageBToA (j : Fin (HB.dividerCount + 1)) :
        TreeSequenceInitialSegment (HB.stage j.castSucc) A := by
      rw [(hstagesB j).1]
      exact ordinaryToA _
    have starBToA (j : Fin (HB.dividerCount + 1)) :
        TreeSequenceInitialSegment (HierarchyStarredStage HB j) A := by
      rw [(hstagesB j).2]
      exact starredToA _
    have stageBToB (j : Fin (HB.dividerCount + 2)) :
        TreeSequenceInitialSegment (HB.stage j) B := by
      exact Fin.reverseInduction
        (motive := fun j => TreeSequenceInitialSegment (HB.stage j) B)
        (by simpa only [HB.terminalStage] using segRefl B)
        (fun i hi => segTrans (HB.nested i) hi) j
    have closureBToA (hp : ett.series.data.kind n = some TashkinovExtensionKind.PE) :
        TreeSequenceVertexSet baseB.closure ⊆ TreeSequenceVertexSet A := by
      obtain ⟨_, _, ⟨u⟩⟩ := baseB.parallel hp
      intro v hv
      apply TreeSequenceInitialSegmentVertexSetSubset coreToA
      rw [← hcoreB, u.vertexSet]
      exact Finset.mem_union_right _ hv
    have minusEq (S : TreeSequence G e0)
        (hS : TreeSequenceVertexSet S ⊆ TreeSequenceVertexSet A) (D : Finset (Fin k)) :
        TreeColorSetMinusClosed G sigma S D ↔ TreeColorSetMinusClosed G phi S D := by
      unfold TreeColorSetMinusClosed TreeColorSetClosed
      rw [treeMissingEq S hS]
      have boundaryEq (c : Fin k) (hc : c ∈ TreeMissingColors phi S) :
          BoundaryColorEdges G sigma (TreeSequenceVertexSet S) c =
            BoundaryColorEdges G phi (TreeSequenceVertexSet S) c := by
        obtain ⟨v, hv, hcv⟩ := Finset.mem_biUnion.mp hc
        have hcA : c ∈ TreeMissingColors phi A := Finset.mem_biUnion.mpr ⟨v, hS hv, hcv⟩
        have hca : c ≠ alpha := by intro he; exact halphaA (he ▸ hcA)
        have hcb : c ≠ beta := by intro he; exact hbetaA (he ▸ hcA)
        ext f
        simp only [BoundaryColorEdges, Finset.mem_filter]
        exact and_congr_right (fun _ => unaffected f c hca hcb)
      exact ⟨fun hs c hc => (boundaryEq c (Finset.mem_sdiff.mp hc).1).symm.trans (hs c hc),
        fun hs c hc => (boundaryEq c (Finset.mem_sdiff.mp hc).1).trans (hs c hc)⟩
    rcases HB with ⟨count, stages, hbbase, hbterminal, hbnested, hbstrict, positions,
      hbpositive, hbincreasing, hbdivider, hbcore⟩
    rcases HS with ⟨countS, stagesS, hsbase, hsterminal, hsnested, hsstrict, positionsS,
      hspositive, hsincreasing, hsdivider, hscore⟩
    rcases hsame with ⟨hcore, hcount, hstages, hpositions, hpe, hclosure⟩
    dsimp only at hcount hstages hpositions
    cases hcount
    have hstage : stages = stagesS := eq_of_heq hstages
    cases hstage
    let HB : TashkinovHierarchy ettB baseB :=
      ⟨count, stages, hbbase, hbterminal, hbnested, hbstrict, positions,
        hbpositive, hbincreasing, hbdivider, hbcore⟩
    let HS : TashkinovHierarchy corr.replacementETT baseS :=
      ⟨count, stages, hsbase, hsterminal, hsnested, hsstrict, positionsS,
        hspositive, hsincreasing, hsdivider, hscore⟩
    have starEq (j : Fin (count + 1)) :
        HierarchyStarredStage HS j = HierarchyStarredStage HB j := by
      exact Fin.cases hcore.symm (fun i => rfl) j
    have storedEq (j : Fin (count + 1)) :
        HierarchyStoredColorsAt HS j = HierarchyStoredColorsAt HB j := by
      change TashkinovStoredColors corr.replacementETT.series.data
          (Fin.last corr.replacementETT.rounds) \ TreeMissingColors sigma (HierarchyStarredStage HS j) =
        Dn \ TreeMissingColors phi (HierarchyStarredStage HB j)
      rw [storedS, starEq, treeMissingEq _ (TreeSequenceInitialSegmentVertexSetSubset (starBToA j))]
    have missingEq (j : Fin (count + 1)) :
        HierarchyStageMissingColors HS j = HierarchyStageMissingColors HB j := by
      refine Fin.cases ?_ (fun i => ?_) j
      · change TreeMissingColors sigma (corr.replacementETT.series.data.tree
            (Fin.last corr.replacementETT.rounds).castSucc) = TreeMissingColors phi Tn
        have htree : corr.replacementETT.series.data.tree
            (Fin.last corr.replacementETT.rounds).castSucc = Tn :=
          hsbase.symm.trans hbbase
        rw [htree, treeMissingEq _ (TreeSequenceInitialSegmentVertexSetSubset TnToA)]
      · exact treeMissingEq _ (TreeSequenceInitialSegmentVertexSetSubset (stageBToA i.succ))
    -- Only stored colors require a transported first-missing cutoff.
    have firstEq (eta : Fin k) (he : eta ∈ Dn) :
        HierarchyFirstMissingPosition sigma B eta = HierarchyFirstMissingPosition phi B eta := by
      have hea : eta ≠ alpha := by intro h; exact hDn.1 (h ▸ he)
      have heb : eta ≠ beta := by intro h; exact hDn.2 (h ▸ he)
      have hcandidates : (Finset.univ.filter fun i => eta ∈ MissingColors G sigma (B.vertex i)) =
          (Finset.univ.filter fun i => eta ∈ MissingColors G phi (B.vertex i)) := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact behavior.2.2.2 _ eta hea heb
      unfold HierarchyFirstMissingPosition
      rw [hcandidates]
    have segmentEq (j : Fin (count + 1)) (eta : Fin k)
        (he : eta ∈ HierarchyStoredColorsAt HB j) :
        HierarchySegmentColors HS j eta = HierarchySegmentColors HB j eta := by
      have heDn : eta ∈ Dn := (Finset.mem_sdiff.mp he).1
      have hedge (t : Fin (stages j.succ).length) :
          sigma ((stages j.succ).edge t) = phi ((stages j.succ).edge t) := by
        have hSB := stageBToB j.succ
        have hf := edgesFixed (Fin.castLE hSB.1 t)
        rw [hSB.2.2] at hf
        exact hf
      unfold HierarchySegmentColors
      simp only [starEq, firstEq eta heDn, HS, HB, hedge]
    have refreshEq (i : Fin count) :
        ((TreeSequenceVertexSet (HS.stage i.succ.castSucc) \
          TreeSequenceVertexSet (HierarchyStarredStage HS i.castSucc)).biUnion
            fun v => MissingColors G sigma v) =
        ((TreeSequenceVertexSet (HB.stage i.succ.castSucc) \
          TreeSequenceVertexSet (HierarchyStarredStage HB i.castSucc)).biUnion
            fun v => MissingColors G phi v) := by
      rw [starEq]
      apply Finset.biUnion_congr rfl
      intro v hv
      exact missingA v (TreeSequenceInitialSegmentVertexSetSubset (stageBToA i.succ)
        (Finset.mem_sdiff.mp hv).1)
    let goodS : GoodHierarchy HS :=
      { gamma := goodB.gamma
        twoColors := by intro j eta he; exact goodB.twoColors j eta (storedEq j ▸ he)
        avoidance := by
          intro j eta he
          rw [missingEq, segmentEq j eta (storedEq j ▸ he)]
          exact goodB.avoidance j eta (storedEq j ▸ he)
        disjointPairs := by
          intro j eta theta he ht hne
          exact goodB.disjointPairs j eta theta (storedEq j ▸ he) (storedEq j ▸ ht) hne
        uniqueRefresh := by
          intro i
          simpa only [storedEq, refreshEq] using goodB.uniqueRefresh i
        parallelBase := by
          dsimp only
          intro hp
          have hpOld := hpe.mpr hp
          have hc := hclosure hpOld
          have htree : corr.replacementETT.series.data.tree
              (Fin.last corr.replacementETT.rounds).castSucc = Tn := hsbase.symm.trans hbbase
          change ¬TreeColorSetMinusClosed G sigma baseS.core
              ((HierarchyStoredColorsAt HS 0).biUnion (goodB.gamma 0)) ∧
            4 ≤ ((TreeMissingColors sigma (corr.replacementETT.series.data.tree
              (Fin.last corr.replacementETT.rounds).castSucc) ∩
              TreeMissingColors sigma baseS.closure) \
              (HierarchyStoredColorsAt HS 0).biUnion (goodB.gamma 0)).card
          rw [← hcore, ← hc, storedEq, htree,
            treeMissingEq _ (TreeSequenceInitialSegmentVertexSetSubset TnToA),
            treeMissingEq _ (closureBToA hpOld),
            minusEq _ (by rw [hcoreB]; exact TreeSequenceInitialSegmentVertexSetSubset coreToA)]
          exact goodB.parallelBase hpOld
        minusClosed := by
          intro i
          rw [storedEq, minusEq _ (TreeSequenceInitialSegmentVertexSetSubset (stageBToA i.succ))]
          exact goodB.minusClosed i }
    let CS : HierarchyCounterexample baseS :=
      { positive := by rw [hrS]; exact C.positive
        hierarchy := HS
        good := goodS
        maximum := hMPS
        notElementary := sigmaNotElementary }
    have hstarLast : HierarchyStarredStage HS (Fin.last count) = A := by
      rw [starEq]
      have hs := (hstagesB (Fin.last count)).2
      have hj : Fin.cast (congrArg (fun n : ℕ => n + 1) hcountB) (Fin.last count) = q :=
        Fin.ext (by simp [q])
      simpa only [hj] using hs
    have hlastOrd : HS.stage (Fin.last count).castSucc = H.stage q.castSucc := by
      have hs := (hstagesB (Fin.last count)).1
      have hj : Fin.cast (congrArg (fun n : ℕ => n + 1) hcountB) (Fin.last count) = q :=
        Fin.ext (by simp [q])
      simpa only [hj] using hs
    -- Path candidates restrict to the shorter prefix; the second measure decreases strictly.
    have pathLe : HierarchyPathNumber HS ≤ HierarchyPathNumber H := by
      let tailB := B.length - A.length
      let candidatesT := (Finset.Icc 1 ell).filter fun i =>
        ∀ t : Fin T.length, A.length + i ≤ t.val →
          G.ends (T.edge t) = s(T.vertex t.castSucc, T.vertex t.succ)
      let candidatesB := (Finset.Icc 1 tailB).filter fun i =>
        ∀ t : Fin B.length, A.length + i ≤ t.val →
          G.ends (B.edge t) = s(B.vertex t.castSucc, B.vertex t.succ)
      have htail : 1 ≤ tailB := by dsimp [tailB]; omega
      have htailT : 1 ≤ ell := by dsimp [ell]; omega
      have htmem : ell ∈ candidatesT := by
        refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨htailT, le_rfl⟩, ?_⟩
        intro t ht
        have hAT := AToT.1
        have := t.isLt
        dsimp [ell] at ht
        omega
      have hbmem : tailB ∈ candidatesB := by
        refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨htail, le_rfl⟩, ?_⟩
        intro t ht
        have := t.isLt
        dsimp [tailB] at ht
        omega
      have hnT : candidatesT.Nonempty := ⟨ell, htmem⟩
      have hnB : candidatesB.Nonempty := ⟨tailB, hbmem⟩
      have hmT := Finset.min'_mem candidatesT hnT
      have hbounds := Finset.mem_Icc.mp (Finset.mem_filter.mp hmT).1
      have hminB : candidatesB.min' hnB ≤ candidatesT.min' hnT := by
        by_cases ht : candidatesT.min' hnT ≤ tailB
        · apply Finset.min'_le
          refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hbounds.1, ht⟩, ?_⟩
          intro t hpos
          have he := (Finset.mem_filter.mp hmT).2 (Fin.castLE BToT.1 t) hpos
          have hv0 := BToT.2.1 t.castSucc
          have hv1 := BToT.2.1 t.succ
          have hi0 : (Fin.castLE BToT.1 t).castSucc =
              Fin.castLE (Nat.succ_le_succ BToT.1) t.castSucc := Fin.ext rfl
          have hi1 : (Fin.castLE BToT.1 t).succ =
              Fin.castLE (Nat.succ_le_succ BToT.1) t.succ := Fin.ext rfl
          simpa only [BToT.2.2, hi0, hi1, hv0, hv1] using he
        · exact le_trans (Finset.min'_le candidatesB tailB hbmem) (by omega)
      unfold HierarchyPathNumber
      rw [hstarLast]
      change (if h : candidatesB.Nonempty then candidatesB.min' h else tailB) ≤
        (if h : candidatesT.Nonempty then candidatesT.min' h else ell)
      rw [dif_pos hnB, dif_pos hnT]
      exact hminB
    have tailLess : B.length - (HS.stage (Fin.last count).castSucc).length <
        T.length - (H.stage q.castSucc).length := by
      rw [hlastOrd]
      have hlen := (ordinaryToA q).1
      omega
    have hless : HierarchyCounterexampleLess (HierarchyCounterexampleMeasure CS)
        (HierarchyCounterexampleMeasure C) := by
      change HierarchyPathNumber HS < HierarchyPathNumber H ∨
        (HierarchyPathNumber HS = HierarchyPathNumber H ∧
          B.length - (HS.stage (Fin.last count).castSucc).length <
            T.length - (H.stage q.castSucc).length)
      rcases lt_or_eq_of_le pathLe with hlt | heq
      · exact Or.inl hlt
      · exact Or.inr ⟨heq, tailLess⟩
    exact hminimal CS hrS hcountB hless
  exact ⟨fun h => finish (outsideStored (Or.inl h)),
    fun h => finish (outsideStored (Or.inr h))⟩
