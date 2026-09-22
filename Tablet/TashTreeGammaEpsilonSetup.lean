import Tablet.MissingColorsNonemptyOfMaximumDegree
import Tablet.TashTreeBadPair
import Tablet.TashTreeFourUnusedColors
import Tablet.TashTreeMinimumBadPair
import Tablet.TashTreeProperPrefixElementary
import Tablet.TashkinovTree
import Tablet.TreeColorUnusedThrough
import Tablet.TreeFreeColors
import Tablet.TreeMissingColors
import Tablet.TreeSequencePrefix
import Tablet.TreeUsedColors

-- [TABLET NODE: TashTreeGammaEpsilonSetup]
theorem TashTreeGammaEpsilonSetup {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (hmin : TashTreeMinimumBadPair G k e0 phi T)
    (hq : 2 < TashTreePathIndex G T)
    (hbefore : TashTreePathIndex G T < T.length)
    (hnone : ¬ ∃ alpha : Fin k, ∃ i : Fin (T.length + 1),
      TashTreePathIndex G T ≤ i.val ∧ i.val < T.length ∧
      alpha ∈ MissingColors G phi (T.vertex i) ∧
      alpha ∈ MissingColors G phi (T.vertex (Fin.last T.length)))
    (beta : Fin k)
    (hbeta : beta ∈
      MissingColors G phi (T.vertex (Fin.last T.length))) :
    let q : Fin (T.length + 1) :=
      ⟨TashTreePathIndex G T, Nat.lt_succ_of_lt hbefore⟩
    ∃ (gamma epsilon : Fin k) (m : Fin (T.length + 1)),
      gamma ≠ beta ∧ epsilon ≠ gamma ∧
      gamma ∈ MissingColors G phi (T.vertex q) ∧
      epsilon ∈ MissingColors G phi (T.vertex m) ∧
      TreeColorUnusedThrough phi T gamma q ∧
      TreeColorUnusedThrough phi T epsilon q ∧
      m.val + 2 ≤ TashTreePathIndex G T := by
-- BODY
  sorry
