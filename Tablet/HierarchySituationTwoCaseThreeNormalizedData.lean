import Tablet.HierarchyFullTailPrefix
import Tablet.HierarchySituationTwoCaseThreeData
import Tablet.HierarchyStarredStage
import Tablet.HierarchyStoredColorsAt
import Tablet.TashkinovStoredColors
import Tablet.TreeMissingColors

-- [TABLET NODE: HierarchySituationTwoCaseThreeNormalizedData]
structure HierarchySituationTwoCaseThreeNormalizedData {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi)
    (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext
      G k e0 input T phi ett base C) extends
    HierarchySituationTwoCaseThreeData
      G k e0 input T phi ett base C ctx where
-- BODY
  alphaMissingTwoBefore :
    alpha ∈ TreeMissingColors phi
      (HierarchyFullTailPrefix C (HierarchyFullTailLength C - 2))
  alphaUnusedOnFullTail :
    let H := C.hierarchy
    let A := HierarchyStarredStage H (Fin.last H.dividerCount)
    ∀ t : Fin T.length, A.length ≤ t.val →
      phi (T.edge t) ≠ some alpha
  normalizedAlternative :
    let H := C.hierarchy
    let q : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
    let n : Fin (ett.rounds + 1) := Fin.last ett.rounds
    let Dn := TashkinovStoredColors ett.series.data n
    let Dnq := HierarchyStoredColorsAt H q
    let Gamma := Dnq.biUnion (C.good.gamma q)
    let A := HierarchyStarredStage H q
    let tailUsed := (Finset.univ : Finset (Fin k)).filter fun c =>
      ∃ t : Fin T.length, A.length ≤ t.val ∧
        phi (T.edge t) = some c
    (0 < H.dividerCount ∧ alpha ∉ Dnq ∧ alpha ∉ Gamma) ∨
      (H.dividerCount = 0 ∧ alpha ∉ Dn ∧ alpha ∉ Gamma) ∨
      (alpha ∈ Dnq ∧ Disjoint (C.good.gamma q alpha) tailUsed)
