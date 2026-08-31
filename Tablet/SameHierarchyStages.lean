import Tablet.TashkinovHierarchy
import Tablet.TashkinovExtensionKind

-- [TABLET NODE: SameHierarchyStages]
def SameHierarchyStages {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    {input₁ input₂ : PartialEdgeColoring E k} {T : TreeSequence G e0}
    {generating₁ generating₂ phi₁ phi₂ : PartialEdgeColoring E k}
    {ett₁ : ExtendedTashkinovTree G k e0 input₁ T generating₁}
    {ett₂ : ExtendedTashkinovTree G k e0 input₂ T generating₂}
    {base₁ : HierarchyBase ett₁ phi₁} {base₂ : HierarchyBase ett₂ phi₂}
    (H₁ : TashkinovHierarchy ett₁ base₁)
    (H₂ : TashkinovHierarchy ett₂ base₂) : Prop :=
-- BODY
  base₁.core = base₂.core ∧
    H₁.dividerCount = H₂.dividerCount ∧
    HEq H₁.stage H₂.stage ∧
    HEq H₁.dividerPosition H₂.dividerPosition ∧
    ((ett₁.series.data.kind (Fin.last ett₁.rounds) =
        some TashkinovExtensionKind.PE ∨
      ett₂.series.data.kind (Fin.last ett₂.rounds) =
        some TashkinovExtensionKind.PE) →
      base₁.closure = base₂.closure)
