import Tablet.TreeSequence

open scoped Sym2

-- [TABLET NODE: TashTreeSuffixPath]
def TashTreeSuffixPath {V E : Type*} (G : LooplessMultigraph V E)
    {e0 : E} (T : TreeSequence G e0) (q : ℕ) : Prop :=
-- BODY
  1 ≤ q ∧ q ≤ T.length ∧
    ∀ i : Fin T.length, q ≤ i.val →
      G.ends (T.edge i) = s(T.vertex i.castSucc, T.vertex i.succ)
