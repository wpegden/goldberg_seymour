import Tablet.NormalGlobalMaximumTriple
import Tablet.NormalTripleTrunk
import Tablet.TashkinovTree
import Tablet.TreeSequenceInitialSegment
import Tablet.TreeSequenceVertexSet
import Tablet.TreeUsedColors

-- [TABLET NODE: ScheideBalancedCandidate]
structure ScheideBalancedCandidate {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    {phi : PartialEdgeColoring E k} {T : TreeSequence G e0}
    (N : NormalGlobalMaximumTriple G k e0 phi T)
    (S : TreeSequence G e0) : Prop where
-- BODY
  tashkinov : TashkinovTree G e0 phi S
  oddOrder : Odd (TreeSequenceVertexSet S).card
  exactTrunk : TreeSequenceInitialSegment (NormalTripleTrunk N) S
  usedColors : TreeUsedColors phi S ⊆ TreeUsedColors phi T
  paired : ∀ j : ℕ, ∀ hlow : N.height < 2 * j,
    ∀ hupp : 2 * j < S.length + 1,
      phi (S.edge ⟨2 * j - 2, by omega⟩) =
        phi (S.edge ⟨2 * j - 1, by omega⟩)
