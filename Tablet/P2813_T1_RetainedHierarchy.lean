import Tablet.P2813_T1_BaseControl
import Tablet.P2813_T1_DisplayedEdges
import Tablet.P2813_T1_PrefixReconstruction
import Tablet.P2813_T1_MinusClosedTransport
import Tablet.P2813_T1_PrefixSegmentTransport
import Tablet.GoodHierarchyPrefixRepackage
import Tablet.HierarchySplitter
import Tablet.HierarchyStoredColorsAntitone
import Tablet.CorrespondingExtendedTashkinovTree
import Tablet.CertifiedETTPredecessor
import Tablet.GoodHierarchyNewMissingClosed
import Tablet.SameHierarchyStages
import Tablet.TechnicalTheoremBase
import Tablet.TashkinovAugmentationSequenceInitialSegment
import Tablet.TashkinovAugmentationSequenceRestrict
import Tablet.TreeSequenceInitialSegmentVertexSetSubset
import Tablet.OutsideKempeRecoloringStable
import Tablet.rutcor
import Tablet.ColoredVertexSetElementary
import Tablet.BoundaryEdges
import Tablet.HierarchySegmentColors

-- [TABLET NODE: P2813_T1_RetainedHierarchy]
theorem P2813_T1_RetainedHierarchy {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi)
    (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
    (hprefixElementary :
      let H := C.hierarchy
      let A := HierarchyStarredStage H (Fin.last H.dividerCount)
      let ell := T.length - A.length
      let Ty := TreeSequencePrefix T
        (min (A.length + (ell - 1)) T.length)
        (by have hA := A.positive; have hT := T.positive; omega)
        (Nat.min_le_right _ _)
      ColoredVertexSetElementary G phi (TreeSequenceVertexSet Ty))
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
    (z : Sum V E) (hpath : TwoColorPathComponent G phi alpha beta z)
    (sigma : PartialEdgeColoring E k)
    (hsigma : sigma = TwoColorComponentSwap G phi alpha beta z)
    (hcase :
      let H := C.hierarchy
      let q : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
      let n : Fin (ett.rounds + 1) := Fin.last ett.rounds
      let A := HierarchyStarredStage H q
      let Tnq := H.stage ⟨H.dividerCount, by omega⟩
      let Tn := ett.series.data.tree n.castSucc
      let Dn := TashkinovStoredColors ett.series.data n
      (0 < H.dividerCount ∧ alpha ∈ TreeMissingColors phi Tnq) ∨
        (H.dividerCount = 0 ∧
          (alpha ∈ TreeMissingColors phi Tn ∨
            (alpha ∈ TreeMissingColors phi A ∧
              alpha ∉ Dn ∧ beta ∉ Dn))))
    (hdisjoint :
      let va := T.vertex (HierarchyFirstMissingPosition phi T alpha)
      Disjoint (TwoColorComponent G phi alpha beta z)
        (TwoColorComponent G phi alpha beta (Sum.inl va))) :
    let H := C.hierarchy
    let q : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
    let n : Fin (ett.rounds + 1) := Fin.last ett.rounds
    let A := HierarchyStarredStage H q
    let Tnq := H.stage ⟨H.dividerCount, by omega⟩
    let Tn := ett.series.data.tree n.castSucc
    let Dnq := HierarchyStoredColorsAt H q
    (∀ hq : 0 < H.dividerCount,
        ∃ inputA : PartialEdgeColoring E k,
          ∃ ettA : ExtendedTashkinovTree G k e0 inputA A sigma,
            ∃ baseA : HierarchyBase ettA sigma,
              ∃ K : TashkinovHierarchy ettA baseA,
                ∃ goodA : GoodHierarchy K,
                  MaximumProperty ettA ∧
                    ettA.series.data.kind (Fin.last ettA.rounds) =
                        ett.series.data.kind (Fin.last ett.rounds) ∧
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
                            by omega⟩))) := by
-- BODY
  sorry
