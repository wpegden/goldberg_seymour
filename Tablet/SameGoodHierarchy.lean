import Tablet.GoodHierarchy
import Tablet.SameHierarchyStages

-- [TABLET NODE: SameGoodHierarchy]
def SameGoodHierarchy {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    {input₁ input₂ : PartialEdgeColoring E k} {T : TreeSequence G e0}
    {generating₁ generating₂ phi₁ phi₂ : PartialEdgeColoring E k}
    {ett₁ : ExtendedTashkinovTree G k e0 input₁ T generating₁}
    {ett₂ : ExtendedTashkinovTree G k e0 input₂ T generating₂}
    {base₁ : HierarchyBase ett₁ phi₁} {base₂ : HierarchyBase ett₂ phi₂}
    {H₁ : TashkinovHierarchy ett₁ base₁}
    {H₂ : TashkinovHierarchy ett₂ base₂}
    (good₁ : GoodHierarchy H₁) (good₂ : GoodHierarchy H₂) : Prop :=
-- BODY
  SameHierarchyStages H₁ H₂ ∧ HEq good₁.gamma good₂.gamma
