import Tablet.TashTreeControlledRepeatedSuffixContradiction
import Tablet.TashTreeDisjointComponentNormalization
import Tablet.TreeColorUnusedThrough
import Tablet.TreeSequence
import Tablet.TwoColorComponent
import Tablet.TwoColorIncidenceGraph
import Tablet.TwoColorComponentSwap
import Tablet.TwoColorComponentSwapMissingBehavior

-- [TABLET NODE: TashTreeNoRepeatedDisjointReduction]
theorem TashTreeNoRepeatedDisjointReduction {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (hmin : TashTreeMinimumBadPair G k e0 phi T)
    (hq : 2 < TashTreePathIndex G T)
    (hbefore : TashTreePathIndex G T < T.length)
    (beta gamma epsilon : Fin k)
    (hge : gamma ≠ beta) (heg : epsilon ≠ gamma) (heb : epsilon ≠ beta)
    (i m : Fin (T.length + 1))
    (hi : i.val + 2 ≤ TashTreePathIndex G T)
    (hm : m.val + 2 ≤ TashTreePathIndex G T)
    (hbeta : beta ∈ MissingColors G phi (T.vertex i))
    (hlast : beta ∈
      MissingColors G phi (T.vertex (Fin.last T.length)))
    (hepsilon : epsilon ∈ MissingColors G phi (T.vertex m))
    (hgamma : gamma ∈ MissingColors G phi
      (T.vertex ⟨TashTreePathIndex G T, Nat.lt_succ_of_lt hbefore⟩))
    (hgammaUnused : TreeColorUnusedThrough phi T gamma
      ⟨TashTreePathIndex G T, Nat.lt_succ_of_lt hbefore⟩)
    (hepsilonUnused : TreeColorUnusedThrough phi T epsilon
      ⟨TashTreePathIndex G T, Nat.lt_succ_of_lt hbefore⟩)
    (havoid : ∀ s : Fin (T.length + 1),
      s.val + 1 ≤ TashTreePathIndex G T →
      Sum.inl (T.vertex s) ∉
        TwoColorComponent G phi epsilon beta
          (Sum.inl (T.vertex (Fin.last T.length)))) : False := by
-- BODY
  sorry
