import Tablet.IsProperEdgeColoring
import Tablet.MissingColorIncidenceEndpoint
import Tablet.MissingColors
import Tablet.TashkinovTree
import Tablet.TreeColorUnusedThrough
import Tablet.TreeSequence
import Tablet.TreeSequenceInitialSegment
import Tablet.TwoColorComponent
import Tablet.TwoColorComponentSpanningPath
import Tablet.TwoColorComponentSwap
import Tablet.TwoColorComponentSwapMissingBehavior
import Tablet.TwoColorIncidenceGraph

-- [TABLET NODE: TashkinovTreeComponentSwapWitnessTransport]
theorem TashkinovTreeComponentSwapWitnessTransport {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (hproper : IsProperEdgeColoring G phi)
    (hTash : TashkinovTree G e0 phi T)
    (i j : Fin (T.length + 1)) (hij : i.val < j.val)
    (alpha beta : Fin k) (hne : alpha ≠ beta)
    (ha : alpha ∈ MissingColors G phi (T.vertex i))
    (hb : beta ∈ MissingColors G phi (T.vertex j))
    (hau : TreeColorUnusedThrough phi T alpha j)
    (hbu : TreeColorUnusedThrough phi T beta j) :
    let C := TwoColorComponent G phi alpha beta (Sum.inl (T.vertex j))
    let phi' := TwoColorComponentSwap G phi alpha beta (Sum.inl (T.vertex j))
    (∀ r : Fin T.length, 1 ≤ r.val → r.val < j.val →
      phi' (T.edge r) = phi (T.edge r)) ∧
      (∀ S : TreeSequence G e0, TreeSequenceInitialSegment S T →
        S.length = j.val → TashkinovTree G e0 phi' S) ∧
      (Sum.inl (T.vertex i) ∈ C →
        (∀ r : Fin T.length, j.val ≤ r.val →
          ∀ w : Fin (r.val + 1), ∀ c : Fin k,
            phi (T.edge r) = some c →
            c ∈ MissingColors G phi
              (T.vertex (Fin.castLT w
                (Nat.lt_trans w.isLt (Nat.succ_lt_succ r.isLt)))) →
            ∃ w' : Fin (r.val + 1), ∃ c' : Fin k,
              phi' (T.edge r) = some c' ∧
              c' ∈ MissingColors G phi'
                (T.vertex (Fin.castLT w'
                  (Nat.lt_trans w'.isLt (Nat.succ_lt_succ r.isLt))))) ∧
          TashkinovTree G e0 phi' T) := by
-- BODY
  classical
  dsimp
  let C := TwoColorComponent G phi alpha beta (Sum.inl (T.vertex j))
  let phi' := TwoColorComponentSwap G phi alpha beta (Sum.inl (T.vertex j))
  have hbehavior := TwoColorComponentSwapMissingBehavior G phi alpha beta hne hproper
    (Sum.inl (T.vertex j))
  have hfixed : ∀ r : Fin T.length, 1 ≤ r.val → r.val < j.val →
      phi' (T.edge r) = phi (T.edge r) := by
    intro r hr hj
    have ha' := hau r hr hj
    have hb' := hbu r hr hj
    simp [phi', TwoColorComponentSwap, ha', hb']
  refine ⟨hfixed, ?_, ?_⟩
  · intro S hS hlen
    rcases hS with ⟨hbound, hvertices, hedges⟩
    intro r hr
    have hrj : r.val < j.val := by simpa [hlen] using r.isLt
    let rT : Fin T.length := Fin.castLE (by omega) (Fin.cast hlen r)
    obtain ⟨q, c, hc, hcm⟩ := hTash rT (by simpa [rT] using hr)
    have hrT : 1 ≤ rT.val := by simpa [rT] using hr
    have hrTj : rT.val < j.val := by simpa [rT] using hrj
    have hca : c ≠ alpha := by
      intro hca
      apply (hau rT hrT hrTj)
      simpa [hc, hca]
    have hcb : c ≠ beta := by
      intro hcb
      apply (hbu rT hrT hrTj)
      simpa [hc, hcb]
    let qS : Fin (r.val + 1) := Fin.cast (by simp [rT]) q
    let qFull : Fin (S.length + 1) := Fin.castLE (by omega) qS
    refine ⟨qS, c, ?_, ?_⟩
    · rw [← hedges r]
      have hre : Fin.castLE hbound r = rT := by
        apply Fin.ext
        simp [rT]
      rw [hre]
      change phi' (T.edge rT) = some c
      exact (hfixed rT hrT hrTj).trans hc
    · have hvq := hvertices qFull
      have hmissing : c ∈ MissingColors G phi' (T.vertex
          (Fin.castLT q (Nat.lt_trans q.isLt (Nat.succ_lt_succ rT.isLt)))) :=
        (hbehavior.2.2.2 _ c hca hcb).2 hcm
      simpa [qFull, qS, rT, hlen] using (hvq ▸ hmissing)
  · intro hiC
    have hia : beta ∈ MissingColors G phi' (T.vertex i) :=
      hbehavior.2.1 _ hiC ha
    have hjb : alpha ∈ MissingColors G phi' (T.vertex j) := by
      have hjC : Sum.inl (T.vertex j) ∈ C := by
        change Sum.inl (T.vertex j) ∈
          ((TwoColorIncidenceGraph G phi alpha beta).connectedComponentMk
            (Sum.inl (T.vertex j))).supp
        rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
      exact hbehavior.2.2.1 _ hjC hb
    have transport : ∀ (r : Fin T.length), j.val ≤ r.val →
        ∀ w : Fin (r.val + 1), ∀ c : Fin k,
          phi (T.edge r) = some c →
          c ∈ MissingColors G phi
            (T.vertex (Fin.castLT w
              (Nat.lt_trans w.isLt (Nat.succ_lt_succ r.isLt)))) →
          ∃ w' : Fin (r.val + 1), ∃ c' : Fin k,
            phi' (T.edge r) = some c' ∧
            c' ∈ MissingColors G phi'
              (T.vertex (Fin.castLT w'
                (Nat.lt_trans w'.isLt (Nat.succ_lt_succ r.isLt)))) := by
      intro r hr w c he hc
      have hir : i.val ≤ r.val := le_trans (Nat.le_of_lt hij) hr
      by_cases hca : c = alpha
      · by_cases hm : Sum.inr (T.edge r) ∈ C
        · refine ⟨⟨i.val, Nat.lt_succ_of_le hir⟩, beta, ?_, ?_⟩
          · simp [phi', C, TwoColorComponentSwap, hm, he, hca, hne]
          · simpa using hia
        · refine ⟨⟨j.val, Nat.lt_succ_of_le hr⟩, alpha, ?_, ?_⟩
          · simp [phi', C, TwoColorComponentSwap, hm, he, hca]
          · simpa using hjb
      · by_cases hcb : c = beta
        · by_cases hm : Sum.inr (T.edge r) ∈ C
          · refine ⟨⟨j.val, Nat.lt_succ_of_le hr⟩, alpha, ?_, ?_⟩
            · simp [phi', C, TwoColorComponentSwap, hm, he, hcb, hne]
            · simpa using hjb
          · refine ⟨⟨i.val, Nat.lt_succ_of_le hir⟩, beta, ?_, ?_⟩
            · simp [phi', C, TwoColorComponentSwap, hm, he, hcb]
            · simpa using hia
        · refine ⟨w, c, ?_, ?_⟩
          · by_cases hm : Sum.inr (T.edge r) ∈ C
            · simp [phi', C, TwoColorComponentSwap, hm, he, hca, hcb]
            · simp [phi', C, TwoColorComponentSwap, hm, he, hca, hcb]
          · by_cases hw : Sum.inl (T.vertex (Fin.castLT w
                (Nat.lt_trans w.isLt (Nat.succ_lt_succ r.isLt)))) ∈ C
            · exact (hbehavior.2.2.2 _ c hca hcb).2 hc
            · rw [hbehavior.1 _ hw]
              exact hc
    refine ⟨transport, ?_⟩
    intro r hr
    by_cases hjr : r.val < j.val
    · obtain ⟨q, c, he, hm⟩ := hTash r hr
      exact ⟨q, c, (show phi' (T.edge r) = some c from
        (hfixed r (by omega) hjr).trans he), by
        have hneac : c ≠ alpha := by
          intro h
          exact (hau r (by omega) hjr) (h ▸ he)
        have hnebc : c ≠ beta := by
          intro h
          exact (hbu r (by omega) hjr) (h ▸ he)
        exact (hbehavior.2.2.2 _ c hneac hnebc).2 hm⟩
    · have hrj : j.val ≤ r.val := by omega
      obtain ⟨w, c, he, hm⟩ := hTash r (by omega)
      exact transport r hrj w c he hm
