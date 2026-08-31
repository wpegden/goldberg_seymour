import Tablet.OutsideKempeRecoloringStable
import Tablet.SameGoodHierarchy

-- [TABLET NODE: OutsideKempeGoodHierarchy]
theorem OutsideKempeGoodHierarchy {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    {input₁ input₂ : PartialEdgeColoring E k} (T : TreeSequence G e0)
    (phi sigma : PartialEdgeColoring E k)
    (ett₁ : ExtendedTashkinovTree G k e0 input₁ T phi)
    (ett₂ : ExtendedTashkinovTree G k e0 input₂ T sigma)
    (base₁ : HierarchyBase ett₁ phi) (base₂ : HierarchyBase ett₂ sigma)
    (H₁ : TashkinovHierarchy ett₁ base₁)
    (H₂ : TashkinovHierarchy ett₂ base₂)
    (hsame : SameHierarchyStages H₁ H₂)
    (good₁ : GoodHierarchy H₁)
    (hproper : IsProperEdgeColoring G phi)
    (hone : IsOneEdgeUncolored phi e0)
    (alpha beta : Fin k)
    (hrecolor : OutsideKempeRecoloring T phi sigma alpha beta)
    (hrung : ett₁.rounds = ett₂.rounds)
    (hseries :
      ∀ i : Fin (ett₁.rounds + 1),
        ett₁.series.data.stored i = ett₂.series.data.stored
          (Fin.cast (congrArg (fun r => r + 1) hrung) i)) :
    ∃ good₂ : GoodHierarchy H₂, SameGoodHierarchy good₁ good₂ := by
-- BODY
  sorry
