import Tablet.HierarchyPathNumber
import Tablet.SameHierarchyStages
import Tablet.HierarchyFullTailLength
import Tablet.HierarchyCounterexampleMeasure

-- [TABLET NODE: P2752_T2_HierarchyMeasures]
theorem P2752_T2_HierarchyMeasures {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    {input₁ input₂ phi₁ phi₂ : PartialEdgeColoring E k}
    {T : TreeSequence G e0}
    {ett₁ : ExtendedTashkinovTree G k e0 input₁ T phi₁}
    {ett₂ : ExtendedTashkinovTree G k e0 input₂ T phi₂}
    {base₁ : HierarchyBase ett₁ phi₁} {base₂ : HierarchyBase ett₂ phi₂}
    (H₁ : TashkinovHierarchy ett₁ base₁)
    (H₂ : TashkinovHierarchy ett₂ base₂)
    (hsame : SameHierarchyStages H₁ H₂) :
    HierarchyStarredStage H₁ (Fin.last H₁.dividerCount) =
        HierarchyStarredStage H₂ (Fin.last H₂.dividerCount) ∧
      HierarchyPathNumber H₁ = HierarchyPathNumber H₂ ∧
      H₁.stage ⟨H₁.dividerCount, by omega⟩ =
        H₂.stage ⟨H₂.dividerCount, by omega⟩ := by
-- BODY
  classical
  cases H₁ with
  | mk q₁ stage₁ baseStage₁ terminalStage₁ nested₁ strict₁
      divider₁ positive₁ increasing₁ dividerStage₁ coreInside₁ =>
    cases H₂ with
    | mk q₂ stage₂ baseStage₂ terminalStage₂ nested₂ strict₂
        divider₂ positive₂ increasing₂ dividerStage₂ coreInside₂ =>
      rcases hsame with ⟨hcore, hcount, hstage, _, _, _⟩
      dsimp only at hcount hstage
      cases hcount
      have heq : stage₁ = stage₂ := eq_of_heq hstage
      cases heq
      have hstar :
          HierarchyStarredStage
            (TashkinovHierarchy.mk q₁ stage₁ baseStage₁ terminalStage₁ nested₁ strict₁
              divider₁ positive₁ increasing₁ dividerStage₁ coreInside₁) (Fin.last q₁) =
          HierarchyStarredStage
            (TashkinovHierarchy.mk q₁ stage₁ baseStage₂ terminalStage₂ nested₂ strict₂
              divider₂ positive₂ increasing₂ dividerStage₂ coreInside₂) (Fin.last q₁) := by
        simp only [HierarchyStarredStage]
        rw [hcore]
      refine ⟨hstar, ?_, rfl⟩
      unfold HierarchyPathNumber
      rw [hstar]
