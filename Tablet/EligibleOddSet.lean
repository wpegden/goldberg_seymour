import Tablet.Preamble

-- [TABLET NODE: EligibleOddSet]
def EligibleOddSet {V : Type*} (U : Finset V) : Prop :=
-- BODY
  3 ≤ U.card ∧ Odd U.card
