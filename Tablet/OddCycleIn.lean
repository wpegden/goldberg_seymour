import Tablet.LooplessMultigraph

open scoped Sym2

-- [TABLET NODE: OddCycleIn]
def OddCycleIn {V E : Type*} (G : LooplessMultigraph V E)
    (X : Finset V) : Prop :=
-- BODY
  ∃ (n : ℕ) (hpos : 0 < n) (vertex : Fin n → V) (edge : Fin n → E),
    3 ≤ n ∧ Odd n ∧ Function.Injective vertex ∧ Function.Injective edge ∧
      (∀ i, vertex i ∈ X) ∧
      ∀ i, G.ends (edge i) =
        s(vertex i,
          vertex ⟨(i.val + 1) % n, Nat.mod_lt (i.val + 1) hpos⟩)
