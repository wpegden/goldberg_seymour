/- The 16 protected Tablet declarations recorded in ../../semantic-closure.json, copied byte for byte from Tablet/. -/

import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Sym.Sym2

open scoped Sym2

-- [TABLET NODE: LooplessMultigraph]
structure LooplessMultigraph (V E : Type*) where
-- BODY
  ends : E → Sym2 V
  loopless : ∀ e v, ends e ≠ s(v, v)

-- [TABLET NODE: Incident]
def Incident {V E : Type*} (G : LooplessMultigraph V E) (v : V) (e : E) : Prop :=
-- BODY
  v ∈ G.ends e

-- [TABLET NODE: AdjacentEdges]
def AdjacentEdges {V E : Type*} (G : LooplessMultigraph V E) (e f : E) : Prop :=
-- BODY
  ∃ v, Incident G v e ∧ Incident G v f

-- [TABLET NODE: PartialEdgeColoring]
abbrev PartialEdgeColoring (E : Type*) (k : ℕ) :=
-- BODY
  E → Option (Fin k)

-- [TABLET NODE: IsFullEdgeColoring]
def IsFullEdgeColoring {E : Type*} {k : ℕ} (φ : PartialEdgeColoring E k) : Prop :=
-- BODY
  ∀ e, ∃ c, φ e = some c

-- [TABLET NODE: IsProperEdgeColoring]
def IsProperEdgeColoring {V E : Type*} (G : LooplessMultigraph V E) {k : ℕ}
    (φ : PartialEdgeColoring E k) : Prop :=
-- BODY
  ∀ ⦃e f c⦄, e ≠ f → AdjacentEdges G e f → φ e = some c → φ f ≠ some c

-- [TABLET NODE: HasKEdgeColoring]
def HasKEdgeColoring {V E : Type*} (G : LooplessMultigraph V E) (k : ℕ) : Prop :=
-- BODY
  ∃ φ : PartialEdgeColoring E k, IsProperEdgeColoring G φ ∧ IsFullEdgeColoring φ

-- [TABLET NODE: ColoringExists]
theorem ColoringExists {V E : Type*} [Fintype V] [Fintype E]
    (G : LooplessMultigraph V E) : ∃ k, HasKEdgeColoring G k := by
-- BODY
  classical
  refine ⟨Fintype.card E, fun e => some (Fintype.equivFin E e), ?_, fun e => ?_⟩
  · intro e f c hne hadj he hf
    apply hne
    apply (Fintype.equivFin E).injective
    exact Option.some.inj (he.trans hf.symm)
  · exact ⟨Fintype.equivFin E e, rfl⟩

-- [TABLET NODE: ChromaticIndex]
noncomputable def ChromaticIndex {V E : Type*} [Fintype V] [Fintype E]
    (G : LooplessMultigraph V E) : ℕ := by
-- BODY
  classical
  exact Nat.find (ColoringExists G)

-- [TABLET NODE: Degree]
noncomputable def Degree {V E : Type*} [Fintype V] [Fintype E]
    (G : LooplessMultigraph V E) (v : V) : ℕ := by
-- BODY
  classical
  exact (Finset.univ.filter fun e => Incident G v e).card

-- [TABLET NODE: InternalEdges]
noncomputable def InternalEdges {V E : Type*} [Fintype V] [Fintype E]
    (G : LooplessMultigraph V E) (U : Finset V) : Finset E := by
-- BODY
  classical
  exact Finset.univ.filter fun e => ∀ v, Incident G v e → v ∈ U

-- [TABLET NODE: DensityValue]
noncomputable def DensityValue {V E : Type*} [Fintype V] [Fintype E]
    (G : LooplessMultigraph V E) (U : Finset V) : ℚ :=
-- BODY
  (2 * (InternalEdges G U).card : ℚ) / (U.card - 1)

-- [TABLET NODE: EligibleOddSet]
def EligibleOddSet {V : Type*} (U : Finset V) : Prop :=
-- BODY
  3 ≤ U.card ∧ Odd U.card

-- [TABLET NODE: Density]
noncomputable def Density {V E : Type*} [Fintype V] [Fintype E]
    (G : LooplessMultigraph V E) : ℚ := by
-- BODY
  classical
  let eligible := Finset.univ.powerset.filter fun U : Finset V => EligibleOddSet U
  let values := eligible.image (DensityValue G)
  exact (insert 0 values).max' (by simp)

-- [TABLET NODE: DensityCeil]
noncomputable def DensityCeil {V E : Type*} [Fintype V] [Fintype E]
    (G : LooplessMultigraph V E) : ℕ :=
-- BODY
  ⌈Density G⌉₊

-- [TABLET NODE: MaximumDegree]
noncomputable def MaximumDegree {V E : Type*} [Fintype V] [Fintype E]
    (G : LooplessMultigraph V E) : ℕ := by
-- BODY
  classical
  exact (insert 0 (Finset.univ.image fun v => Degree G v)).max' (by simp)
