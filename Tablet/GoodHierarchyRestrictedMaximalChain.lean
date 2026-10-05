import Tablet.GoodHierarchy
import Tablet.HierarchyFirstMissingPosition
import Tablet.HierarchyStarredStage
import Tablet.HierarchyStoredColorsAt
import Tablet.TashkinovAugmentation
import Tablet.TashkinovAugmentationSequence
import Tablet.TashkinovHierarchy
import Tablet.TreeSequenceInitialSegment
import Tablet.TreeSequenceVertexSet

-- [TABLET NODE: GoodHierarchyRestrictedMaximalChain]
theorem GoodHierarchyRestrictedMaximalChain {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (J : TreeSequence G e0)
    (sigma : PartialEdgeColoring E k)
    {generating : PartialEdgeColoring E k}
    {ett : ExtendedTashkinovTree G k e0 input J generating}
    (baseJ : HierarchyBase ett sigma)
    (KJ : TashkinovHierarchy ett baseJ) (goodJ : GoodHierarchy KJ) :
    let lastJ : Fin (KJ.dividerCount + 1) := Fin.last KJ.dividerCount
    let A : TreeSequence G e0 := HierarchyStarredStage KJ lastJ
    let restrictedColors : TreeSequence G e0 → Fin k → Finset (Fin k) :=
      fun W eta => Finset.univ.filter fun c =>
        ∃ r : Fin W.length, A.length ≤ r.val ∧
          r.val < min (HierarchyFirstMissingPosition sigma W eta).val W.length ∧
          sigma (W.edge r) = some c
    ∃ (m : ℕ) (chain : Fin (m + 1) → TreeSequence G e0)
        (U : TreeSequence G e0),
      chain 0 = J ∧ chain (Fin.last m) = U ∧
      (∀ r : Fin m,
        TashkinovAugmentation sigma (chain r.castSucc) (chain r.succ) ∧
          ∀ eta : Fin k, eta ∈ HierarchyStoredColorsAt KJ lastJ →
            Disjoint (goodJ.gamma lastJ eta)
              (restrictedColors (chain r.succ) eta)) ∧
      (∀ r : Fin (m + 1), (chain r).length = J.length + r.val) ∧
      (∀ r s : Fin (m + 1), r.val ≤ s.val →
        TreeSequenceInitialSegment (chain r) (chain s)) ∧
      (∀ r : Fin m,
        TreeSequenceVertexSet (chain r.castSucc) ⊂
          TreeSequenceVertexSet (chain r.succ)) ∧
      TashkinovAugmentationSequence sigma J U ∧
      (∀ eta : Fin k, eta ∈ HierarchyStoredColorsAt KJ lastJ →
        Disjoint (goodJ.gamma lastJ eta) (restrictedColors U eta)) ∧
      (∀ W : TreeSequence G e0,
        TashkinovAugmentation sigma U W →
        (∀ eta : Fin k, eta ∈ HierarchyStoredColorsAt KJ lastJ →
          Disjoint (goodJ.gamma lastJ eta) (restrictedColors W eta)) →
        False) := by
-- BODY
  sorry
