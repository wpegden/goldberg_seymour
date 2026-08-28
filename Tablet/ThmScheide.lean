import Tablet.ScheideOrderNineStructuralConfiguration
import Tablet.ScheideStructuralLemma

-- [TABLET NODE: ThmScheide]
theorem ThmScheide {V E : Type*} [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (hcritical : Critical G)
    (hnoisolated : ∀ v : V, ∃ e : E, Incident G v e)
    (hdegree : MaximumDegree G + 2 ≤ ChromaticIndex G)
    (horder : TashkinovOrder G < 11) : Elementary G := by
-- BODY
  classical
  let k := ChromaticIndex G - 1
  have hindex : ChromaticIndex G = k + 1 := by
    dsimp [k]
    omega
  have hkdegree : MaximumDegree G + 1 ≤ k := by
    dsimp [k]
    omega
  by_contra hnonelementary
  obtain ⟨e0, phi, T, ⟨C⟩⟩ :=
    ScheideOrderNineStructuralConfiguration G k hcritical hindex hkdegree
      hnoisolated hnonelementary horder
  exact hnonelementary (ScheideStructuralLemma G k e0 phi T C)
