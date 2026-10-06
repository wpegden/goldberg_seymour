import Tablet.BoundaryMissingColorAugmentation
import Tablet.GoodHierarchy
import Tablet.HierarchyFirstMissingPosition
import Tablet.HierarchyFirstMissingPositionPrefixCutoff
import Tablet.HierarchyStarredStage
import Tablet.HierarchyStoredColorsAt
import Tablet.HierarchyTerminalStoredColors
import Tablet.TashkinovAugmentation
import Tablet.TreeColorSetMinusClosed
import Tablet.TreeColorSetClosed
import Tablet.TreeMissingColors

-- [TABLET NODE: GoodHierarchyRestrictedEndpointMinusClosed]
theorem GoodHierarchyRestrictedEndpointMinusClosed {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    {inputJ inputU : PartialEdgeColoring E k}
    (J U : TreeSequence G e0) (sigma : PartialEdgeColoring E k)
    {generatingJ generatingU : PartialEdgeColoring E k}
    {ettJ : ExtendedTashkinovTree G k e0 inputJ J generatingJ}
    {ettU : ExtendedTashkinovTree G k e0 inputU U generatingU}
    {baseJ : HierarchyBase ettJ sigma} {baseU : HierarchyBase ettU sigma}
    (KJ : TashkinovHierarchy ettJ baseJ) (goodJ : GoodHierarchy KJ)
    (KU : TashkinovHierarchy ettU baseU) (goodU : GoodHierarchy KU)
    (hgammaLast : ∀ eta : Fin k,
      goodU.gamma (Fin.last KU.dividerCount) eta =
        goodJ.gamma (Fin.last KJ.dividerCount) eta)
    (hterminal : HierarchyTerminalStoredColors KU ⊆
      HierarchyStoredColorsAt KJ (Fin.last KJ.dividerCount))
    (hnewMissing : ∀ eta : Fin k,
      eta ∈ HierarchyStoredColorsAt KJ (Fin.last KJ.dividerCount) →
      eta ∉ HierarchyTerminalStoredColors KU →
      eta ∈ TreeMissingColors sigma U) :
    let lastJ : Fin (KJ.dividerCount + 1) := Fin.last KJ.dividerCount
    let A : TreeSequence G e0 := HierarchyStarredStage KJ lastJ
    let restrictedColors : TreeSequence G e0 → Fin k → Finset (Fin k) :=
      fun W eta => Finset.univ.filter fun c =>
        ∃ r : Fin W.length, A.length ≤ r.val ∧
          r.val < min (HierarchyFirstMissingPosition sigma W eta).val W.length ∧
          sigma (W.edge r) = some c
    (∀ eta : Fin k, eta ∈ HierarchyStoredColorsAt KJ lastJ →
      Disjoint (goodJ.gamma lastJ eta) (restrictedColors U eta)) →
    (∀ W : TreeSequence G e0,
      TashkinovAugmentation sigma U W →
      (∀ eta : Fin k, eta ∈ HierarchyStoredColorsAt KJ lastJ →
        Disjoint (goodJ.gamma lastJ eta) (restrictedColors W eta)) →
      False) →
    TreeColorSetMinusClosed G sigma U
      ((HierarchyTerminalStoredColors KU).biUnion
        (goodU.gamma (Fin.last KU.dividerCount))) := by
-- BODY
  sorry
