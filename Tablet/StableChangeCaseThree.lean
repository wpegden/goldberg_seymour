import Tablet.ChangeLemma
import Tablet.CombinedStableClosurePreserved
import Tablet.CorrespondingExtendedTashkinovTree
import Tablet.GoodHierarchyPrefixRepackage
import Tablet.HierarchySplitter
import Tablet.HierarchyWeaklyStable
import Tablet.HkuTreeColorsControlled
import Tablet.MaximumPropertyTransport
import Tablet.OrderedTreeUnion
import Tablet.SameGoodHierarchy
import Tablet.TashkinovAugmentation
import Tablet.TashkinovAugmentationSequenceRestrict
import Tablet.Td
import Tablet.TreeColorSetMinusClosed
import Tablet.TwoColorComponentSwap
import Tablet.TwoColorComponentSwapProper
import Tablet.ChangeLemmaBothOutside
import Tablet.TashkinovAugmentationSequenceInitialSegment
import Tablet.TashkinovAugmentationSequencePosition
import Tablet.TashkinovAugmentationSequenceSuffix
import Tablet.TashkinovAugmentationSequenceComponentSwap
import Tablet.TreeSequenceInitialSegmentVertexSetSubset
import Tablet.TwoColorComponentSwapMissingBehavior

-- [TABLET NODE: StableChangeCaseThree]
theorem StableChangeCaseThree {V E : Type*}
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
    (z : Sum V E) (sigma : PartialEdgeColoring E k)
    (hsigma : sigma = TwoColorComponentSwap G phi alpha beta z)
    (hAprecedes :
      let H := C.hierarchy
      let q : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
      let A := HierarchyStarredStage H q
      let va := T.vertex (HierarchyFirstMissingPosition phi T alpha)
      ∀ u ∈ TreeSequenceVertexSet A, TreeVertexOrder T u va)
    (hordered :
      let va := T.vertex (HierarchyFirstMissingPosition phi T alpha)
      let vb := T.vertex (HierarchyFirstMissingPosition phi T beta)
      TreeVertexOrder T va vb)
    (hnotStored :
      let H := C.hierarchy
      let q : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
      let Dnq := HierarchyStoredColorsAt H q
      alpha ∉ Dnq ∧ beta ∉ Dnq)
    (hunused :
      let ia := HierarchyFirstMissingPosition phi T alpha
      let ib := HierarchyFirstMissingPosition phi T beta
      alpha ∉ (Finset.univ.filter fun c =>
        ∃ t : Fin T.length,
          ia.val ≤ t.val ∧ t.val < ib.val ∧
            phi (T.edge t) = some c)) :
    let H := C.hierarchy
    let q : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
    let n : Fin (ett.rounds + 1) := Fin.last ett.rounds
    let A := HierarchyStarredStage H q
    let Tnq := H.stage ⟨H.dividerCount, by omega⟩
    let Tn := ett.series.data.tree n.castSucc
    let Dnq := HierarchyStoredColorsAt H q
    HierarchyWeaklyStable H q sigma ∧
      ModColoring ett sigma ∧
      (A = Tn ∨
        ∃ inputA : PartialEdgeColoring E k,
          ∃ ettA : ExtendedTashkinovTree G k e0 inputA A sigma,
            MaximumProperty ettA) ∧
      (∀ hq : 0 < H.dividerCount,
        ∃ inputA : PartialEdgeColoring E k,
          ∃ ettA : ExtendedTashkinovTree G k e0 inputA A sigma,
            ∃ baseA : HierarchyBase ettA sigma,
              ∃ K : TashkinovHierarchy ettA baseA,
                ∃ goodA : GoodHierarchy K,
                  MaximumProperty ettA ∧
                    ∃ hcount : K.dividerCount + 1 = H.dividerCount,
                      baseA.core = base.core ∧
                      baseA.closure = base.closure ∧
                      (∀ j : Fin (K.dividerCount + 2),
                        K.stage j = H.stage ⟨j.val, by omega⟩) ∧
                      (∀ j : Fin (K.dividerCount + 1),
                        let jH : Fin (H.dividerCount + 1) :=
                          ⟨j.val, by omega⟩
                        HierarchyStoredColorsAt K j =
                            HierarchyStoredColorsAt H jH ∧
                          ∀ eta ∈ HierarchyStoredColorsAt K j,
                            goodA.gamma j eta = C.good.gamma jH eta) ∧
                      TreeColorSetMinusClosed G sigma Tnq
                        (Dnq.biUnion
                          (C.good.gamma ⟨C.hierarchy.dividerCount - 1,
                            by omega⟩))) ∧
      (∃ corrT : CorrespondingExtendedTashkinovTree
            G k e0 ett sigma T,
          MaximumProperty corrT.replacementETT ∧
            ∃ baseT : HierarchyBase corrT.replacementETT sigma,
              ∃ K : TashkinovHierarchy corrT.replacementETT baseT,
                ∃ goodT : GoodHierarchy K,
                  SameGoodHierarchy C.good goodT) := by
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
  let Y := TreeSequencePrefix T (min (A.length + (ell - 1)) T.length)
    (by have := A.positive; have := T.positive; omega) (Nat.min_le_right _ _)
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
  have equalTrees {S U : TreeSequence G e0}
      (hSU : TreeSequenceInitialSegment S U) (hlen : S.length = U.length) : S = U := by
    cases S with
    | mk ls ps vs es vis eis fs aas =>
      cases U with
      | mk lu pu vu eu viu eiu fu aau =>
        simp only at hlen
        subst lu
        rw [TreeSequence.mk.injEq]
        refine ⟨rfl, ?_, ?_⟩
        · apply heq_of_eq
          funext i
          simpa only [Fin.castLE] using (hSU.2.1 i).symm
        · apply heq_of_eq
          funext i
          simpa only [Fin.castLE] using (hSU.2.2 i).symm
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
    · rw [lastZero hz]; exact segRefl _
    · rw [lastPositive hz]
      have hs := stageSegment 1 (H.dividerCount - 1) (by omega)
      have he : 1 + (H.dividerCount - 1) = H.dividerCount := by omega
      simpa [he] using segTrans H.coreInsideFirst hs
  have TnToCore : TreeSequenceInitialSegment Tn base.core := by
    by_cases hp : ett.series.data.kind n = some TashkinovExtensionKind.PE
    · exact (Classical.choice (base.parallel hp).2.2).leftSegment
    · rw [base.nonparallel hp]; exact segRefl _
  have TnToA := segTrans TnToCore coreToA
  have AToT : TreeSequenceInitialSegment A T := by
    by_cases hz : H.dividerCount = 0
    · rw [lastZero hz]
      exact segTrans H.coreInsideFirst (stageToT ⟨1, by omega⟩)
    · rw [lastPositive hz]; exact stageToT _
  have ordinaryToA (j : Fin (H.dividerCount + 1)) :
      TreeSequenceInitialSegment (H.stage j.castSucc) A := by
    by_cases hz : H.dividerCount = 0
    · have hj : j.castSucc = (0 : Fin (H.dividerCount + 2)) := Fin.ext (by simp; omega)
      rw [hj, H.baseStage]; exact TnToA
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
      rw [YToT.2.1 i, hi]; exact hcv
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
  have firstLe (c : Fin k) (i : Fin (T.length + 1))
      (hc : c ∈ MissingColors G phi (T.vertex i)) :
      (HierarchyFirstMissingPosition phi T c).val ≤ i.val := by
    let candidates := Finset.univ.filter fun j => c ∈ MissingColors G phi (T.vertex j)
    have hi : i ∈ candidates := by simp [candidates, hc]
    have hn : candidates.Nonempty := ⟨i, hi⟩
    simpa [HierarchyFirstMissingPosition, candidates, hn] using
      (Finset.min'_le candidates i hi)
  have ha := firstMissing alpha hmissingY.1
  have hb := firstMissing beta hmissingY.2
  have habIndex : ia.val < ib.val := by
    obtain ⟨i, j, hi, hj, hij⟩ := hordered
    have hei := T.vertex_injective hi
    have hej := T.vertex_injective hj
    simpa [ia, ib, hei, hej] using hij
  have hout : va ∉ TreeSequenceVertexSet A ∧ vb ∉ TreeSequenceVertexSet A := by
    constructor
    · intro hv
      obtain ⟨i, j, hi, hj, hij⟩ := hAprecedes va hv
      have he := T.vertex_injective (hi.trans hj.symm)
      have hv := congrArg Fin.val he
      omega
    · intro hv
      obtain ⟨i, j, hi, hj, hij⟩ := hAprecedes vb hv
      have hei := T.vertex_injective hi
      have hej := T.vertex_injective hj
      have hvi := congrArg Fin.val hei
      have hvj := congrArg Fin.val hej
      change i.val = ib.val at hvi
      change j.val = ia.val at hvj
      omega
  have outsideIndex (i : Fin (T.length + 1))
      (hi : T.vertex i ∉ TreeSequenceVertexSet A) : A.length < i.val := by
    by_contra h
    have hle : i.val ≤ A.length := by omega
    apply hi
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨⟨i.val, by omega⟩, (AToT.2.1 ⟨i.val, by omega⟩).symm⟩
  have hAia := outsideIndex ia hout.1
  have hAib := outsideIndex ib hout.2
  have AToY : TreeSequenceInitialSegment A Y := commonPrefix AToT YToT (by omega)
  have vertexY (i : Fin (T.length + 1)) (hi : i.val ≤ Y.length) :
      T.vertex i ∈ TreeSequenceVertexSet Y := by
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨⟨i.val, by omega⟩, rfl⟩
  have haY : va ∈ TreeSequenceVertexSet Y := vertexY ia ha.2
  have hbY : vb ∈ TreeSequenceVertexSet Y := vertexY ib hb.2
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
  have missingSubset {S U : TreeSequence G e0} (hSU : TreeSequenceInitialSegment S U) :
      TreeMissingColors phi S ⊆ TreeMissingColors phi U := by
    intro c hc
    obtain ⟨v, hv, hcv⟩ := Finset.mem_biUnion.mp hc
    exact Finset.mem_biUnion.mpr ⟨v, TreeSequenceInitialSegmentVertexSetSubset hSU hv, hcv⟩
  have hDn : alpha ∉ Dn ∧ beta ∉ Dn := by
    constructor
    · intro hc
      exact hnotStored.1 (Finset.mem_sdiff.mpr ⟨hc, halphaA⟩)
    · intro hc
      exact hnotStored.2 (Finset.mem_sdiff.mpr ⟨hc, hbetaA⟩)
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
  -- The route includes the actual connecting seed, not merely a vertex-set extension.
  have terminalRoute :
      (ett.series.data.kind n = some TashkinovExtensionKind.PE ∧
        TashkinovAugmentationSequence phi Tn T) ∨
      ((ett.series.data.kind n = some TashkinovExtensionKind.SE ∨
          ett.series.data.kind n = some TashkinovExtensionKind.RE) ∧
        ∃ (f : E) (seed : TreeSequence G e0),
          ett.series.data.connectingEdges n = {f} ∧ TreeSequenceAdjoinEdge Tn f seed ∧
          TashkinovAugmentationSequence phi seed T ∧
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
      have hseedT : TreeSequenceInitialSegment seed T :=
        commonPrefix (TashkinovAugmentationSequenceInitialSegment phi _ _ hroute)
          ett.belowFinal (by
            have hl := adjoin.1; rw [hj] at hl
            change seed.length = Tn.length + 1 at hl
            have hs := ett.strictAbovePenultimate
            change Tn.length < T.length at hs
            omega)
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
        TashkinovAugmentationSequenceRestrict phi seed T _ hroute hseedT ett.belowFinal,
        hnot alpha (Or.inl rfl), hnot beta (Or.inr rfl)⟩
    | PE j _ _ _ _ _ choice _ gamma _ second _ _ _ exit coloring proper one stored
        edges kind vertex outside delta gammaEq closure ordered strict =>
      have hj : j.succ = n := hi.symm
      have hlast : j.succ.succ = Fin.last (ett.rounds + 1) :=
        Fin.ext (by have hv := congrArg Fin.val hj; simp [n] at hv ⊢; omega)
      refine Or.inl ⟨by simpa [hj] using kind, ?_⟩
      apply TashkinovAugmentationSequenceRestrict phi Tn T _ _ ett.abovePenultimate ett.belowFinal
      simpa [Tn, hj, hlast, ← ett.generatingColoring, n] using closure.1
    | RE j _ _ _ _ available coloring stored edges kind vertex outside delta gamma
        seed adjoin closure ordered strict =>
      have hj : j.succ = n := hi.symm
      have hlast : j.succ.succ = Fin.last (ett.rounds + 1) :=
        Fin.ext (by have hv := congrArg Fin.val hj; simp [n] at hv ⊢; omega)
      have hroute : TashkinovAugmentationSequence phi seed
          (ett.series.data.tree (Fin.last (ett.rounds + 1))) := by
        simpa [hj, hlast, ← ett.generatingColoring, n] using closure.1
      have hseedT : TreeSequenceInitialSegment seed T :=
        commonPrefix (TashkinovAugmentationSequenceInitialSegment phi _ _ hroute)
          ett.belowFinal (by
            have hl := adjoin.1; rw [hj] at hl
            change seed.length = Tn.length + 1 at hl
            have hs := ett.strictAbovePenultimate
            change Tn.length < T.length at hs
            omega)
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
        TashkinovAugmentationSequenceRestrict phi seed T _ hroute hseedT ett.belowFinal,
        hnot alpha (Or.inl rfl), hnot beta (Or.inr rfl)⟩
  have treeControlled (t : Fin Tn.length) :
      phi (Tn.edge t) ≠ some alpha ∧ phi (Tn.edge t) ≠ some beta := by
    by_cases ht : t.val = 0
    · have he : Tn.edge t = e0 := by
        rw [show t = ⟨0, Tn.positive⟩ from Fin.ext ht]; exact Tn.first_edge
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
      (hseq : TashkinovAugmentationSequence phi S T) (t : Fin T.length)
      (ht : S.length ≤ t.val) (htb : t.val < ib.val) :
      phi (T.edge t) ≠ some alpha ∧ phi (T.edge t) ≠ some beta := by
    have hstep := (TashkinovAugmentationSequencePosition phi S T hseq t ht).1
    obtain ⟨hl, hinit, c, hcol, hm⟩ := hstep
    have hcolT : phi (T.edge t) = some c := by
      convert hcol using 1; congr 2
    obtain ⟨v, hv, hcv⟩ := Finset.mem_biUnion.mp hm
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and] at hv
    obtain ⟨iv, hiv⟩ := hv
    let ivT : Fin (T.length + 1) := ⟨iv.val, by
      have := iv.isLt; change iv.val < t.val + 1 at this; omega⟩
    have hcvT : c ∈ MissingColors G phi (T.vertex ivT) := by
      have he : (TreeSequencePrefix T t.val (le_trans S.positive ht)
          (Nat.le_of_lt t.isLt)).vertex iv = T.vertex ivT := rfl
      rw [← he, hiv]; exact hcv
    have hiv : ivT.val ≤ t.val := Nat.le_of_lt_succ iv.isLt
    have hnotAlpha : c ≠ alpha := by
      intro he; subst c
      by_cases hta : t.val < ia.val
      · have hle := firstLe alpha ivT hcvT
        change ia.val ≤ ivT.val at hle
        omega
      · apply hunused
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, t, by omega, htb, hcolT⟩
    have hnotBeta : c ≠ beta := by
      intro he; subst c
      have hle := firstLe beta ivT hcvT
      change ib.val ≤ ivT.val at hle
      omega
    exact ⟨fun he => hnotAlpha (Option.some.inj (hcolT.symm.trans he)),
      fun he => hnotBeta (Option.some.inj (hcolT.symm.trans he))⟩
  have prefixControlled (t : Fin T.length) (htb : t.val < ib.val) :
      phi (T.edge t) ≠ some alpha ∧ phi (T.edge t) ≠ some beta := by
    by_cases htn : t.val < Tn.length
    · let tn : Fin Tn.length := ⟨t.val, htn⟩
      have he : Fin.castLE ett.abovePenultimate.1 tn = t := Fin.ext rfl
      rw [← he, ett.abovePenultimate.2.2 tn]
      exact treeControlled tn
    · rcases terminalRoute with ⟨hkind, hseq⟩ | ⟨hkind, f, seed, hedges, hseed, hseq, hfa, hfb⟩
      · exact augmentationControlled Tn hseq t (by omega) htb
      · by_cases htseed : t.val < seed.length
        · have ht : t.val = Tn.length := by have := hseed.1; omega
          have hs := TashkinovAugmentationSequenceInitialSegment phi seed T hseq
          let ts : Fin seed.length := ⟨t.val, htseed⟩
          have he : Fin.castLE hs.1 ts = t := Fin.ext rfl
          rw [← he, hs.2.2 ts]
          have hlast : ts = Fin.cast hseed.1.symm (Fin.last Tn.length) := Fin.ext ht
          rw [hlast, hseed.2.2]
          exact ⟨hfa, hfb⟩
        · exact augmentationControlled seed hseq t (by omega) htb
  have horderedUnused :
      (alpha ∉ TreeMissingColors phi A ∨ beta ∉ TreeMissingColors phi A) →
        TreeVertexOrder T va vb ∧ alpha ∉ (Finset.univ.filter fun c =>
          ∃ t : Fin T.length, A.length ≤ t.val ∧ t.val < ib.val ∧
            phi (T.edge t) = some c) := by
    intro _
    refine ⟨hordered, ?_⟩
    intro hc
    obtain ⟨_, t, hlo, hhi, hcol⟩ := Finset.mem_filter.mp hc
    exact (prefixControlled t hhi).1 hcol
  have hchange := ChangeLemmaBothOutside G k e0 input T phi ett base C hproper hone
    hlower hfewer hminimal hprefixElementary hlarge alpha beta hne hmissingPrefix
    horderedUnused hout
  have sameComponent : TwoColorComponent G phi alpha beta (Sum.inl va) =
      TwoColorComponent G phi alpha beta (Sum.inl vb) := by
    by_cases hz : H.dividerCount = 0
    · apply hchange.2
      refine ⟨hz, Or.inr ?_⟩
      apply Finset.disjoint_left.mpr
      intro c hc hd
      rcases Finset.mem_insert.mp hc with rfl | hc
      · exact hDn.1 hd
      · have he := Finset.mem_singleton.mp hc; subst c; exact hDn.2 hd
    · apply hchange.1
      refine ⟨by change 0 < H.dividerCount; omega, Or.inr ?_⟩
      apply Finset.disjoint_left.mpr
      intro c hc hd
      rcases Finset.mem_insert.mp hc with rfl | hc
      · exact hnotStored.1 hd
      · have he := Finset.mem_singleton.mp hc; subst c; exact hnotStored.2 hd
  have behavior := TwoColorComponentSwapMissingBehavior G phi alpha beta hne hproper z
  have fixedValue (f : E) (ha : phi f ≠ some alpha) (hb : phi f ≠ some beta) :
      sigma f = phi f := by
    rw [hsigma]
    simp [TwoColorComponentSwap, ha, hb]
  have unaffected (f : E) (c : Fin k) (hca : c ≠ alpha) (hcb : c ≠ beta) :
      sigma f = some c ↔ phi f = some c := by
    rw [hsigma]
    by_cases hf : Sum.inr f ∈ TwoColorComponent G phi alpha beta z
    · by_cases ha : phi f = some alpha
      · simp [TwoColorComponentSwap, hf, ha, hca.symm, hcb.symm]
      · by_cases hb : phi f = some beta
        · simp [TwoColorComponentSwap, hf, ha, hb, hne.symm, hca.symm, hcb.symm]
        · simp [TwoColorComponentSwap, hf, ha, hb]
    · simp [TwoColorComponentSwap, hf]
  have missingUnaffected (v : V) (c : Fin k) (hca : c ≠ alpha) (hcb : c ≠ beta) :
      c ∈ MissingColors G sigma v ↔ c ∈ MissingColors G phi v := by
    rw [hsigma]
    exact behavior.2.2.2 v c hca hcb
  have sigmaProper : IsProperEdgeColoring G sigma := by
    rw [hsigma]
    exact TwoColorComponentSwapProper G phi alpha beta hne hproper z
  have sigmaOne : IsOneEdgeUncolored sigma e0 := by
    refine ⟨?_, ?_⟩
    · rw [hsigma]; simp [TwoColorComponentSwap, hone.1]
    · intro f hf
      obtain ⟨c, hc⟩ := hone.2 f hf
      by_cases ha : c = alpha
      · subst c
        by_cases hQ : Sum.inr f ∈ TwoColorComponent G phi alpha beta z
        · exact ⟨beta, by rw [hsigma]; simp [TwoColorComponentSwap, hQ, hc]⟩
        · exact ⟨alpha, by rw [hsigma]; simp [TwoColorComponentSwap, hQ, hc]⟩
      · by_cases hb : c = beta
        · subst c
          by_cases hQ : Sum.inr f ∈ TwoColorComponent G phi alpha beta z
          · exact ⟨alpha, by rw [hsigma]; simp [TwoColorComponentSwap, hQ, hc, hne.symm]⟩
          · exact ⟨beta, by rw [hsigma]; simp [TwoColorComponentSwap, hQ, hc]⟩
        · exact ⟨c, (unaffected f c ha hb).mpr hc⟩
  have missingA (v : V) (hv : v ∈ TreeSequenceVertexSet A) :
      MissingColors G sigma v = MissingColors G phi v := by
    by_cases hvQ : Sum.inl v ∈ TwoColorComponent G phi alpha beta z
    · have han : alpha ∉ MissingColors G phi v := fun hc =>
        halphaA (Finset.mem_biUnion.mpr ⟨v, hv, hc⟩)
      have hbn : beta ∉ MissingColors G phi v := fun hc =>
        hbetaA (Finset.mem_biUnion.mpr ⟨v, hv, hc⟩)
      have hpa : ∃ f, Incident G v f ∧ phi f = some alpha := by
        simpa [MissingColors, PresentColors] using han
      have hpb : ∃ f, Incident G v f ∧ phi f = some beta := by
        simpa [MissingColors, PresentColors] using hbn
      obtain ⟨fa, hfa, hfca⟩ := hpa
      obtain ⟨fb, hfb, hfcb⟩ := hpb
      have edgeOfVertex {f : E} (hf : Incident G v f)
          (hc : phi f = some alpha ∨ phi f = some beta) :
          Sum.inr f ∈ TwoColorComponent G phi alpha beta z := by
        have hadj : (TwoColorIncidenceGraph G phi alpha beta).Adj (Sum.inr f) (Sum.inl v) :=
          ⟨hf, hc⟩
        exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj).trans hvQ
      have hnewa : sigma fb = some alpha := by
        rw [hsigma]
        simp [TwoColorComponentSwap, edgeOfVertex hfb (Or.inr hfcb), hfcb, hne.symm]
      have hnewb : sigma fa = some beta := by
        rw [hsigma]
        simp [TwoColorComponentSwap, edgeOfVertex hfa (Or.inl hfca), hfca]
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
        · exact missingUnaffected v c hca hcb
    · rw [hsigma]
      exact behavior.1 v hvQ
  have treeMissingEq (S : TreeSequence G e0)
      (hS : TreeSequenceVertexSet S ⊆ TreeSequenceVertexSet A) :
      TreeMissingColors sigma S = TreeMissingColors phi S := by
    unfold TreeMissingColors
    exact Finset.biUnion_congr rfl (fun v hv => missingA v (hS hv))
  have stable (S : TreeSequence G e0)
      (hS : TreeSequenceVertexSet S ⊆ TreeSequenceVertexSet A)
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
    exact ((unaffected f c (hnot alpha halphaA hD.1)
      (hnot beta hbetaA hD.2)).mpr hcol).trans hcol.symm
  have stableTn : StableColoring Tn Dn phi sigma :=
    stable Tn (TreeSequenceInitialSegmentVertexSetSubset TnToA) Dn hDn
  have closureInsideA (hPE : ett.series.data.kind n = some TashkinovExtensionKind.PE) :
      TreeSequenceVertexSet base.closure ⊆ TreeSequenceVertexSet A := by
    have ordered := Classical.choice (base.parallel hPE).2.2
    intro v hv
    apply TreeSequenceInitialSegmentVertexSetSubset coreToA
    rw [ordered.vertexSet]
    exact Finset.mem_union_right _ hv
  have combined (hPE : ett.series.data.kind n = some TashkinovExtensionKind.PE) :
      CombinedStableColoring Tn base.closure Dn phi sigma :=
    ⟨stableTn, stable base.closure (closureInsideA hPE) ∅ (by simp)⟩
  have invariant (S : TreeSequence G e0) (hSA : TreeSequenceInitialSegment S A) :
      TreeColoringInvariant S phi sigma := by
    refine ⟨?_, fun v hv => missingA v (TreeSequenceInitialSegmentVertexSetSubset hSA hv)⟩
    intro t ht
    have hST := segTrans hSA AToT
    have hc := prefixControlled (Fin.castLE hST.1 t) (by
      have := t.isLt; have := hSA.1; simp only [Fin.coe_castLE]; omega)
    rw [hST.2.2 t] at hc
    exact fixedValue _ hc.1 hc.2
  have weak : HierarchyWeaklyStable H q sigma := by
    have bs : (if ett.series.data.kind n = some TashkinovExtensionKind.PE then
        CombinedStableColoring Tn base.closure Dn phi sigma else StableColoring Tn Dn phi sigma) := by
      split
      · rename_i hp; exact combined hp
      · exact stableTn
    have allWeak (j : Fin (H.dividerCount + 1)) : HierarchyWeaklyStable H j sigma := by
      refine Fin.cases bs (fun i => ⟨bs, invariant _ (ordinaryToA i.succ)⟩) j
    exact allWeak q
  have stableLadder : StableColoring Tn Dn (ett.series.data.coloring n) sigma := by
    rw [show ett.series.data.coloring n = phi from ett.generatingColoring.symm]
    exact stableTn
  have hmod : ModColoring ett sigma := Td G k e0 input T phi ett C.maximum
    C.positive hlower sigma sigmaProper sigmaOne stableLadder
  -- Before b every augmentation color is unaffected. Beyond b both colors remain missing.
  let B := TreeSequencePrefix T ib.val (by have := A.positive; omega)
    (Nat.le_of_lt_succ ib.isLt)
  have BToT : TreeSequenceInitialSegment B T :=
    ⟨Nat.le_of_lt_succ ib.isLt, (by intro i; rfl), (by intro i; rfl)⟩
  have AToB : TreeSequenceInitialSegment A B := commonPrefix AToT BToT (le_of_lt hAib)
  have vertexB (i : Fin (T.length + 1)) (hi : i.val ≤ B.length) :
      T.vertex i ∈ TreeSequenceVertexSet B := by
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨⟨i.val, by omega⟩, rfl⟩
  have haB : va ∈ TreeSequenceVertexSet B := vertexB ia (le_of_lt habIndex)
  have hbB : vb ∈ TreeSequenceVertexSet B := vertexB ib le_rfl
  have together : (Sum.inl va ∈ TwoColorComponent G phi alpha beta z) ↔
      (Sum.inl vb ∈ TwoColorComponent G phi alpha beta z) := by
    have hab : Sum.inl va ∈ TwoColorComponent G phi alpha beta (Sum.inl vb) := by
      rw [← sameComponent]; exact rfl
    change (TwoColorIncidenceGraph G phi alpha beta).connectedComponentMk (Sum.inl va) =
      (TwoColorIncidenceGraph G phi alpha beta).connectedComponentMk (Sum.inl vb) at hab
    change (_ = _) ↔ (_ = _)
    rw [hab]
  have bothMissingB : alpha ∈ TreeMissingColors sigma B ∧ beta ∈ TreeMissingColors sigma B := by
    by_cases hva : Sum.inl va ∈ TwoColorComponent G phi alpha beta z
    · have hvb := together.mp hva
      constructor
      · exact Finset.mem_biUnion.mpr ⟨vb, hbB, by
          rw [hsigma]; exact behavior.2.2.1 vb hvb hb.1⟩
      · exact Finset.mem_biUnion.mpr ⟨va, haB, by
          rw [hsigma]; exact behavior.2.1 va hva ha.1⟩
    · have hvb : Sum.inl vb ∉ TwoColorComponent G phi alpha beta z := fun h => hva (together.mpr h)
      constructor
      · exact Finset.mem_biUnion.mpr ⟨va, haB, by rw [hsigma, behavior.1 va hva]; exact ha.1⟩
      · exact Finset.mem_biUnion.mpr ⟨vb, hbB, by rw [hsigma, behavior.1 vb hvb]; exact hb.1⟩
  have transportBefore (S U : TreeSequence G e0)
      (hseq : TashkinovAugmentationSequence phi S U)
      (hUT : TreeSequenceInitialSegment U T) (hU : U.length ≤ ib.val) :
      TashkinovAugmentationSequence sigma S U := by
    unfold TashkinovAugmentationSequence at hseq ⊢
    induction hseq with
    | refl => exact Relation.ReflTransGen.refl
    | @tail U W hSU hUW ih =>
      have hlen := hUW.1
      have hinit := hUW.2.1
      obtain ⟨c, hcol, hm⟩ := hUW.2.2
      let t := Fin.cast hlen.symm (Fin.last U.length)
      let tt := Fin.castLE hUT.1 t
      have hct := prefixControlled tt (by
        change U.length < ib.val; have := hU; omega)
      rw [hUT.2.2 t] at hct
      have hca : c ≠ alpha := by intro he; subst c; exact hct.1 hcol
      have hcb : c ≠ beta := by intro he; subst c; exact hct.2 hcol
      have hm' : c ∈ TreeMissingColors sigma U := by
        obtain ⟨v, hv, hcv⟩ := Finset.mem_biUnion.mp hm
        exact Finset.mem_biUnion.mpr ⟨v, hv, (missingUnaffected v c hca hcb).mpr hcv⟩
      exact Relation.ReflTransGen.tail (ih (segTrans hinit hUT) (by omega))
        ⟨hlen, hinit, c, (unaffected _ c hca hcb).mpr hcol, hm'⟩
  have transportRoute (S : TreeSequence G e0)
      (hseq : TashkinovAugmentationSequence phi S T)
      (hSB : TreeSequenceInitialSegment S B) :
      TashkinovAugmentationSequence sigma S T := by
    have hpre := TashkinovAugmentationSequenceRestrict phi S B T hseq hSB BToT
    have hsuf := TashkinovAugmentationSequenceSuffix phi S B T hseq hSB BToT
    have hpreSigma := transportBefore S B hpre BToT le_rfl
    have hsufSigma : TashkinovAugmentationSequence sigma B T := by
      rw [hsigma] at bothMissingB ⊢
      exact TashkinovAugmentationSequenceComponentSwap G k e0 phi alpha beta hne z
        B T hsuf bothMissingB.1 bothMissingB.2
    exact hpreSigma.trans hsufSigma
  have sigmaRoute :
      (ett.series.data.kind n = some TashkinovExtensionKind.PE ∧
        TashkinovAugmentationSequence sigma Tn T) ∨
      ((ett.series.data.kind n = some TashkinovExtensionKind.SE ∨
          ett.series.data.kind n = some TashkinovExtensionKind.RE) ∧
        ∃ (f : E) (seed : TreeSequence G e0),
          ett.series.data.connectingEdges n = {f} ∧ TreeSequenceAdjoinEdge Tn f seed ∧
          TashkinovAugmentationSequence sigma seed T) := by
    rcases terminalRoute with ⟨hp, hseq⟩ | ⟨hp, f, seed, hedges, hseed, hseq, hfa, hfb⟩
    · exact Or.inl ⟨hp, transportRoute Tn hseq (segTrans TnToA AToB)⟩
    · have hseedB : TreeSequenceInitialSegment seed B :=
        commonPrefix (TashkinovAugmentationSequenceInitialSegment phi _ _ hseq) BToT
          (by have := hseed.1; have := TnToA.1; change _ ≤ ib.val; omega)
      exact Or.inr ⟨hp, f, seed, hedges, hseed, transportRoute seed hseq hseedB⟩
  have corrData (corr : CorrespondingExtendedTashkinovTree G k e0 ett sigma T) :
      corr.replacementETT.series.data.tree
          (Fin.last corr.replacementETT.rounds).castSucc = Tn ∧
      corr.replacementETT.series.data.kind (Fin.last corr.replacementETT.rounds) =
          ett.series.data.kind n ∧
      TashkinovStoredColors corr.replacementETT.series.data
          (Fin.last corr.replacementETT.rounds) = Dn := by
    rcases corr with ⟨replacementInput, replacementSeries, replacementETT,
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
        exact treeMissingEq Tn (TreeSequenceInitialSegmentVertexSetSubset TnToA)
      have hmOld : TreeMissingColors (ett.series.data.coloring (Fin.last ett.rounds))
          (ett.series.data.tree (Fin.last ett.rounds).castSucc) =
          TreeMissingColors phi Tn := by
        rw [← ett.generatingColoring]
      refine ⟨ht, extensionKindsAgree (Fin.last ett.rounds), ?_⟩
      change TashkinovStoredColors replacementSeries.data (Fin.last ett.rounds) =
        TashkinovStoredColors ett.series.data (Fin.last ett.rounds)
      simp only [TashkinovStoredColors, storedColorsAgree, hm, hmOld]
  have fullBase :
      ∃ corr : CorrespondingExtendedTashkinovTree G k e0 ett sigma T,
        MaximumProperty corr.replacementETT ∧
        ∃ baseT : HierarchyBase corr.replacementETT sigma,
          baseT.core = base.core ∧ baseT.closure = base.closure := by
    by_cases hp : ett.series.data.kind n = some TashkinovExtensionKind.PE
    · have hb : TashkinovAugmentationSequence sigma Tn T := by
        rcases sigmaRoute with ⟨_, hseq⟩ | ⟨hk, rest⟩
        · exact hseq
        · rcases hk with hk | hk <;> rw [hp] at hk <;> cases hk
      obtain ⟨corr, hMP, baseT, K0, hsame⟩ := HierarchySplitter G k e0 input T phi sigma
        ett C.maximum C.positive hlower base H hp hproper hone sigmaProper sigmaOne (combined hp) hb
      exact ⟨corr, hMP, baseT, hsame.1.symm, (hsame.2.2.2.2.2 hp).symm⟩
    · obtain ⟨corr⟩ := hmod.2.2 T ett.abovePenultimate ett.strictAbovePenultimate sigmaRoute
      have hd := corrData corr
      let pos : Fin ((corr.replacementETT.series.data.tree
          (Fin.last corr.replacementETT.rounds).castSucc).length + 1) :=
        Fin.cast (congrArg (fun W : TreeSequence G e0 => W.length + 1) hd.1.symm)
          base.supportPosition
      let baseT : HierarchyBase corr.replacementETT sigma := {
        core := base.core
        closure := base.closure
        supportPosition := pos
        supportPositive := by simpa [pos] using base.supportPositive
        terminalMissingColors := rfl
        parallel := by
          dsimp only
          intro hPE
          exact False.elim (hp (hd.2.1.symm.trans hPE))
        nonparallel := by
          dsimp only
          intro _
          exact (base.nonparallel hp).trans hd.1.symm }
      exact ⟨corr, MaximumPropertyTransport G k e0 ett sigma hmod T corr C.maximum,
        baseT, rfl, rfl⟩
  obtain ⟨corrT, hmaximumT, baseT, hcoreT, hclosureT⟩ := fullBase
  have terminalData := corrData corrT
  let K : TashkinovHierarchy corrT.replacementETT baseT := {
    dividerCount := H.dividerCount
    stage := H.stage
    baseStage := H.baseStage.trans terminalData.1.symm
    terminalStage := H.terminalStage
    nested := H.nested
    strict := H.strict
    dividerPosition := H.dividerPosition
    dividerPositive := H.dividerPositive
    dividerIncreasing := H.dividerIncreasing
    dividerStage := H.dividerStage
    coreInsideFirst := by rw [hcoreT]; exact H.coreInsideFirst }
  have starredEq (j : Fin (H.dividerCount + 1)) :
      HierarchyStarredStage K j = HierarchyStarredStage H j := by
    exact Fin.cases hcoreT (fun _ => rfl) j
  have storedEq (j : Fin (H.dividerCount + 1)) :
      HierarchyStoredColorsAt K j = HierarchyStoredColorsAt H j := by
    unfold HierarchyStoredColorsAt
    dsimp only
    rw [terminalData.2.2, starredEq j,
      treeMissingEq _ (TreeSequenceInitialSegmentVertexSetSubset (starredToA j))]
  have stageMissingEq (j : Fin (H.dividerCount + 1)) :
      HierarchyStageMissingColors K j = HierarchyStageMissingColors H j := by
    refine Fin.cases ?_ (fun a => ?_) j
    · change TreeMissingColors sigma
        (corrT.replacementETT.series.data.tree
          (Fin.last corrT.replacementETT.rounds).castSucc) = TreeMissingColors phi Tn
      rw [terminalData.1]
      exact treeMissingEq Tn (TreeSequenceInitialSegmentVertexSetSubset TnToA)
    · exact treeMissingEq _ (TreeSequenceInitialSegmentVertexSetSubset (ordinaryToA a.succ))
  have stageMissingInside (j : Fin (H.dividerCount + 1)) :
      HierarchyStageMissingColors H j ⊆ TreeMissingColors phi A := by
    exact Fin.cases (missingSubset TnToA) (fun a => missingSubset (ordinaryToA a.succ)) j
  have ownerNot (j : Fin (H.dividerCount + 1)) (eta : Fin k)
      (heta : eta ∈ HierarchyStoredColorsAt H j) : eta ≠ alpha ∧ eta ≠ beta := by
    have hd : eta ∈ Dn := (Finset.mem_sdiff.mp heta).1
    exact ⟨fun he => hDn.1 (he ▸ hd), fun he => hDn.2 (he ▸ hd)⟩
  have gammaNot (j : Fin (H.dividerCount + 1)) (eta : Fin k)
      (heta : eta ∈ HierarchyStoredColorsAt H j) (c : Fin k)
      (hc : c ∈ C.good.gamma j eta) : c ≠ alpha ∧ c ≠ beta := by
    have hm := stageMissingInside j (Finset.mem_sdiff.mp (C.good.avoidance j eta heta hc)).1
    exact ⟨fun he => halphaA (he ▸ hm), fun he => hbetaA (he ▸ hm)⟩
  have firstEq (c : Fin k) (hca : c ≠ alpha) (hcb : c ≠ beta) :
      HierarchyFirstMissingPosition sigma T c = HierarchyFirstMissingPosition phi T c := by
    have hsets :
        (Finset.univ.filter fun j : Fin (T.length + 1) =>
          c ∈ MissingColors G sigma (T.vertex j)) =
        (Finset.univ.filter fun j : Fin (T.length + 1) =>
          c ∈ MissingColors G phi (T.vertex j)) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact missingUnaffected _ c hca hcb
    unfold HierarchyFirstMissingPosition
    rw [hsets]
  have segmentTransfer (j : Fin (H.dividerCount + 1)) (eta : Fin k)
      (heta : eta ∈ HierarchyStoredColorsAt H j) (c : Fin k)
      (hca : c ≠ alpha) (hcb : c ≠ beta)
      (hc : c ∈ HierarchySegmentColors K j eta) :
      c ∈ HierarchySegmentColors H j eta := by
    unfold HierarchySegmentColors at hc ⊢
    dsimp only at hc ⊢
    rw [starredEq j, firstEq eta (ownerNot j eta heta).1 (ownerNot j eta heta).2] at hc
    obtain ⟨_, t, hlo, hhi, hcol⟩ := Finset.mem_filter.mp hc
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, t, hlo, hhi,
      (unaffected _ c hca hcb).mp hcol⟩
  have boundaryEq (S : TreeSequence G e0) (c : Fin k) (hca : c ≠ alpha) (hcb : c ≠ beta) :
      BoundaryColorEdges G sigma (TreeSequenceVertexSet S) c =
        BoundaryColorEdges G phi (TreeSequenceVertexSet S) c := by
    ext f
    simp only [BoundaryColorEdges, Finset.mem_filter]
    rw [unaffected f c hca hcb]
  have minusEq (S : TreeSequence G e0)
      (hS : TreeSequenceVertexSet S ⊆ TreeSequenceVertexSet A) (R : Finset (Fin k)) :
      TreeColorSetMinusClosed G sigma S R ↔ TreeColorSetMinusClosed G phi S R := by
    unfold TreeColorSetMinusClosed TreeColorSetClosed
    rw [treeMissingEq S hS]
    have hnot (c : Fin k) (hc : c ∈ TreeMissingColors phi S) : c ≠ alpha ∧ c ≠ beta := by
      obtain ⟨v, hv, hcv⟩ := Finset.mem_biUnion.mp hc
      have hm := Finset.mem_biUnion.mpr ⟨v, hS hv, hcv⟩
      exact ⟨fun he => halphaA (he ▸ hm), fun he => hbetaA (he ▸ hm)⟩
    constructor <;> intro h c hc
    · have hh := h c hc
      rw [boundaryEq S c (hnot c (Finset.mem_sdiff.mp hc).1).1
        (hnot c (Finset.mem_sdiff.mp hc).1).2] at hh
      exact hh
    · rw [boundaryEq S c (hnot c (Finset.mem_sdiff.mp hc).1).1
        (hnot c (Finset.mem_sdiff.mp hc).1).2]
      exact h c hc
  let goodT : GoodHierarchy K := {
    gamma := C.good.gamma
    twoColors := by
      intro j eta heta
      exact C.good.twoColors j eta (by rw [storedEq j] at heta; exact heta)
    avoidance := by
      intro j eta heta c hc
      have ho : eta ∈ HierarchyStoredColorsAt H j := by rw [← storedEq j]; exact heta
      have old := C.good.avoidance j eta ho hc
      refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
      · rw [stageMissingEq j]; exact (Finset.mem_sdiff.mp old).1
      · intro hseg
        exact (Finset.mem_sdiff.mp old).2
          (segmentTransfer j eta ho c (gammaNot j eta ho c hc).1 (gammaNot j eta ho c hc).2 hseg)
    disjointPairs := by
      intro j eta theta heta htheta hne
      exact C.good.disjointPairs j eta theta
        (by rw [storedEq j] at heta; exact heta)
        (by rw [storedEq j] at htheta; exact htheta) hne
    uniqueRefresh := by
      intro a
      have hnew :
          ((TreeSequenceVertexSet (H.stage a.succ.castSucc) \
            TreeSequenceVertexSet (HierarchyStarredStage H a.castSucc)).biUnion
              fun v => MissingColors G sigma v) =
          ((TreeSequenceVertexSet (H.stage a.succ.castSucc) \
            TreeSequenceVertexSet (HierarchyStarredStage H a.castSucc)).biUnion
              fun v => MissingColors G phi v) := by
        apply Finset.biUnion_congr rfl
        intro v hv
        exact missingA v (TreeSequenceInitialSegmentVertexSetSubset (ordinaryToA a.succ)
          (Finset.mem_sdiff.mp hv).1)
      change ∃! eta : Fin k,
        eta ∈ HierarchyStoredColorsAt K a.succ ∧
          C.good.gamma a.succ eta ⊆
            ((TreeSequenceVertexSet (H.stage a.succ.castSucc) \
              TreeSequenceVertexSet (HierarchyStarredStage K a.castSucc)).biUnion
                fun v => MissingColors G sigma v) ∧
          ∀ theta ∈ HierarchyStoredColorsAt K a.succ, theta ≠ eta →
            C.good.gamma a.succ theta = C.good.gamma a.castSucc theta
      rw [starredEq a.castSucc, hnew]
      simp only [storedEq]
      exact C.good.uniqueRefresh a
    parallelBase := by
      dsimp only
      intro hp
      have hpOld : ett.series.data.kind n = some TashkinovExtensionKind.PE :=
        terminalData.2.1.symm.trans hp
      obtain ⟨hnot, hcard⟩ := C.good.parallelBase hpOld
      constructor
      · change ¬ TreeColorSetMinusClosed G sigma baseT.core
          ((HierarchyStoredColorsAt K 0).biUnion (C.good.gamma 0))
        rw [hcoreT, storedEq 0,
          minusEq base.core (TreeSequenceInitialSegmentVertexSetSubset coreToA)]
        exact hnot
      · change 4 ≤ ((TreeMissingColors sigma
          (corrT.replacementETT.series.data.tree
            (Fin.last corrT.replacementETT.rounds).castSucc) ∩
          TreeMissingColors sigma baseT.closure) \
            (HierarchyStoredColorsAt K 0).biUnion (C.good.gamma 0)).card
        rw [terminalData.1, hclosureT, storedEq 0,
          treeMissingEq Tn (TreeSequenceInitialSegmentVertexSetSubset TnToA),
          treeMissingEq base.closure (closureInsideA hpOld)]
        exact hcard
    minusClosed := by
      intro a
      change TreeColorSetMinusClosed G sigma (H.stage a.succ.castSucc)
        ((HierarchyStoredColorsAt K a.succ).biUnion (C.good.gamma a.castSucc))
      rw [storedEq a.succ, minusEq _ (TreeSequenceInitialSegmentVertexSetSubset (ordinaryToA a.succ))]
      exact C.good.minusClosed a }
  have same : SameGoodHierarchy C.good goodT := by
    refine ⟨?_, rfl, ?_⟩
    · refine ⟨hcoreT.symm, rfl, HEq.rfl, HEq.rfl, ?_, fun _ => hclosureT.symm⟩
      exact ⟨fun hp => terminalData.2.1.trans hp, fun hp => terminalData.2.1.symm.trans hp⟩
    · intro j
      exact ⟨(storedEq j).symm, fun _ _ => rfl⟩
  have prefixMaximum : A = Tn ∨
      ∃ inputA : PartialEdgeColoring E k,
        ∃ ettA : ExtendedTashkinovTree G k e0 inputA A sigma, MaximumProperty ettA := by
    by_cases he : A = Tn
    · exact Or.inl he
    · have hstrict : Tn.length < A.length := by
        have hle := TnToA.1
        by_contra h
        have hlen : Tn.length = A.length := by omega
        exact he (equalTrees TnToA hlen).symm
      have routeA :
          (ett.series.data.kind n = some TashkinovExtensionKind.PE ∧
            TashkinovAugmentationSequence sigma Tn A) ∨
          ((ett.series.data.kind n = some TashkinovExtensionKind.SE ∨
              ett.series.data.kind n = some TashkinovExtensionKind.RE) ∧
            ∃ (f : E) (seed : TreeSequence G e0),
              ett.series.data.connectingEdges n = {f} ∧ TreeSequenceAdjoinEdge Tn f seed ∧
              TashkinovAugmentationSequence sigma seed A) := by
        rcases terminalRoute with ⟨hp, hseq⟩ | ⟨hp, f, seed, hedges, hseed, hseq, hfa, hfb⟩
        · have hpre := TashkinovAugmentationSequenceRestrict phi Tn A T hseq TnToA AToT
          exact Or.inl ⟨hp, transportBefore Tn A hpre AToT (le_of_lt hAib)⟩
        · have hseedA : TreeSequenceInitialSegment seed A :=
            commonPrefix (TashkinovAugmentationSequenceInitialSegment phi _ _ hseq) AToT
              (by have := hseed.1; omega)
          have hpre := TashkinovAugmentationSequenceRestrict phi seed A T hseq hseedA AToT
          exact Or.inr ⟨hp, f, seed, hedges, hseed, transportBefore seed A hpre AToT (le_of_lt hAib)⟩
      obtain ⟨corrA⟩ := hmod.2.2 A TnToA hstrict routeA
      exact Or.inr ⟨corrA.replacementInput, corrA.replacementETT,
        MaximumPropertyTransport G k e0 ett sigma hmod A corrA C.maximum⟩
  refine ⟨weak, hmod, prefixMaximum, ?_, corrT, hmaximumT, baseT, K, goodT, same⟩
  intro hq
  have hqK : 1 ≤ q.val := by change 0 < H.dividerCount at hq; dsimp [q]; omega
  have hqpos : H.dividerCount ≠ 0 := by change 0 < H.dividerCount at hq; omega
  have hA : A = H.stage q.castSucc := by
    rw [lastPositive hqpos]
    rfl
  have positivePackage (U : TreeSequence G e0) (hU : U = H.stage q.castSucc) :
      ∃ inputA : PartialEdgeColoring E k,
        ∃ ettA : ExtendedTashkinovTree G k e0 inputA U sigma,
          ∃ baseA : HierarchyBase ettA sigma,
            ∃ KA : TashkinovHierarchy ettA baseA,
              ∃ goodA : GoodHierarchy KA,
                MaximumProperty ettA ∧
                  ∃ hcount : KA.dividerCount + 1 = H.dividerCount,
                    baseA.core = base.core ∧ baseA.closure = base.closure ∧
                    (∀ j : Fin (KA.dividerCount + 2),
                      KA.stage j = H.stage ⟨j.val, by omega⟩) ∧
                    (∀ j : Fin (KA.dividerCount + 1),
                      let jH : Fin (H.dividerCount + 1) := ⟨j.val, by omega⟩
                      HierarchyStoredColorsAt KA j = HierarchyStoredColorsAt H jH ∧
                        ∀ eta ∈ HierarchyStoredColorsAt KA j,
                          goodA.gamma j eta = C.good.gamma jH eta) ∧
                    TreeColorSetMinusClosed G sigma (H.stage ⟨H.dividerCount, by omega⟩)
                      ((HierarchyStoredColorsAt H q).biUnion
                        (C.good.gamma ⟨H.dividerCount - 1, by
                          exact Nat.lt_succ_of_le (Nat.sub_le H.dividerCount 1)⟩)) := by
    subst U
    obtain ⟨ettA, hMPA, hrA, hsA, baseA, hcoreA, hclosureA, hsupportA,
        KA, hcount, hstages, hdividers, goodA, hgammaA, hminusA⟩ :=
      GoodHierarchyPrefixRepackage G k e0 corrT.replacementInput T sigma sigma
        corrT.replacementETT hmaximumT baseT K goodT q hqK
    refine ⟨corrT.replacementInput, ettA, baseA, KA, goodA, hMPA, ?_⟩
    have hcount' : KA.dividerCount + 1 = H.dividerCount := by
      change KA.dividerCount = H.dividerCount - 1 at hcount
      change 0 < H.dividerCount at hq
      omega
    refine ⟨hcount', hcoreA.trans hcoreT, hclosureA.trans hclosureT, ?_, ?_, ?_⟩
    · intro j
      let jp : Fin (q.val + 1) := ⟨j.val, by dsimp [q]; have := j.isLt; omega⟩
      have he : Fin.cast (by omega) jp = j := Fin.ext rfl
      simpa only [he] using hstages jp
    · intro j
      let jp : Fin q.val := ⟨j.val, by dsimp [q]; have := j.isLt; omega⟩
      have he : Fin.cast (by omega) jp = j := Fin.ext rfl
      have hg := hgammaA jp
      simp only [he] at hg
      refine ⟨hg.1.trans (storedEq _), ?_⟩
      intro eta heta
      exact hg.2 eta
    · have he : (Fin.last H.dividerCount).castSucc =
          (⟨H.dividerCount, by omega⟩ : Fin (H.dividerCount + 2)) := Fin.ext rfl
      simpa [K, goodT, storedEq, q, he] using hminusA
  exact positivePackage A hA
