import Tablet.ScheideMaximalContainsEveryTree
import Tablet.TreeColorUnusedThrough
import Tablet.TwoColorComponentSpanningPath
import Tablet.TwoColorComponentSwapProper

-- [TABLET NODE: ScheideMaximalKempePath]
theorem ScheideMaximalKempePath {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T S : TreeSequence G e0)
    (htriple : KTriple G k e0 phi)
    (hmax : FixedPairMaximalTashkinovTree G e0 phi T)
    (hS : TashkinovTree G e0 phi S)
    (i j : Fin (S.length + 1)) (hij : i.val < j.val)
    (gamma delta : Fin k)
    (hgamma : gamma ∈ MissingColors G phi (S.vertex i))
    (hdelta : delta ∈ MissingColors G phi (S.vertex j)) :
    gamma ≠ delta ∧
      ∃ p : (TwoColorIncidenceGraph G phi gamma delta).Walk
          (Sum.inl (S.vertex i)) (Sum.inl (S.vertex j)),
        p.IsPath ∧
          {z | z ∈ p.support} =
            TwoColorComponent G phi gamma delta (Sum.inl (S.vertex i)) ∧
          4 ∣ p.length ∧
          (∀ v : V, Sum.inl v ∈ p.support →
            v ∈ TreeSequenceVertexSet T) ∧
          (TreeColorUnusedThrough phi S gamma j →
            IsProperEdgeColoring G
                (TwoColorComponentSwap G phi gamma delta
                  (Sum.inl (S.vertex i))) ∧
              IsOneEdgeUncolored
                (TwoColorComponentSwap G phi gamma delta
                  (Sum.inl (S.vertex i))) e0 ∧
              TashkinovTree G e0
                (TwoColorComponentSwap G phi gamma delta
                  (Sum.inl (S.vertex i))) S) := by
-- BODY
  sorry
