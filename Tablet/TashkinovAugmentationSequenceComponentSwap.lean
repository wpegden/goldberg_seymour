import Tablet.MissingColors
import Tablet.TashkinovAugmentation
import Tablet.TashkinovAugmentationSequence
import Tablet.TreeMissingColors
import Tablet.TreeSequenceInitialSegment
import Tablet.TreeSequenceVertexSet
import Tablet.TwoColorComponentSwap

-- [TABLET NODE: TashkinovAugmentationSequenceComponentSwap]
theorem TashkinovAugmentationSequenceComponentSwap {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (alpha beta : Fin k)
    (hne : alpha ≠ beta) (z : Sum V E)
    (X Y : TreeSequence G e0)
    (hsequence : TashkinovAugmentationSequence phi X Y)
    (halpha : alpha ∈ TreeMissingColors
      (TwoColorComponentSwap G phi alpha beta z) X)
    (hbeta : beta ∈ TreeMissingColors
      (TwoColorComponentSwap G phi alpha beta z) X) :
    TashkinovAugmentationSequence
      (TwoColorComponentSwap G phi alpha beta z) X Y := by
-- BODY
  classical
  let sigma := TwoColorComponentSwap G phi alpha beta z
  have vertexTransfer {A B : TreeSequence G e0}
      (hab : TreeSequenceInitialSegment A B) {v : V}
      (hv : v ∈ TreeSequenceVertexSet A) :
      v ∈ TreeSequenceVertexSet B := by
    simp [TreeSequenceVertexSet] at hv ⊢
    rcases hv with ⟨i, hi⟩
    rcases hab with ⟨hlen, hvertices, hedges⟩
    refine ⟨Fin.castLE (Nat.succ_le_succ hlen) i, ?_⟩
    exact (hvertices i).trans hi
  have missingTransfer {c : Fin k} {A B : TreeSequence G e0}
      (hab : TreeSequenceInitialSegment A B)
      (hc : c ∈ TreeMissingColors sigma A) :
      c ∈ TreeMissingColors sigma B := by
    simp only [TreeMissingColors, Finset.mem_biUnion] at hc ⊢
    rcases hc with ⟨v, hv, hvc⟩
    exact ⟨v, vertexTransfer hab hv, hvc⟩
  have missingStable {c : Fin k} (hcα : c ≠ alpha) (hcβ : c ≠ beta)
      {v : V} (hv : c ∈ MissingColors G phi v) :
      c ∈ MissingColors G sigma v := by
    unfold MissingColors at hv ⊢
    rw [Finset.mem_sdiff] at hv ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    intro hp
    apply hv.2
    rw [PresentColors]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [PresentColors] at hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    rcases hp with ⟨e, he, hpe⟩
    refine ⟨e, he, ?_⟩
    change TwoColorComponentSwap G phi alpha beta z e = some c at hpe
    unfold TwoColorComponentSwap at hpe
    by_cases hcomp : Sum.inr e ∈ TwoColorComponent G phi alpha beta z
    · simp only [if_pos hcomp] at hpe
      by_cases ha : phi e = some alpha
      · simp only [if_pos ha] at hpe
        exact (hcβ (Option.some.inj hpe).symm).elim
      · by_cases hb : phi e = some beta
        · simp only [if_neg ha, if_pos hb] at hpe
          exact (hcα (Option.some.inj hpe).symm).elim
        · simp only [if_neg ha, if_neg hb] at hpe
          exact hpe
    · simpa [hcomp] using hpe
  have stepTransfer {A B : TreeSequence G e0}
      (hstep : TashkinovAugmentation phi A B)
      (ha : alpha ∈ TreeMissingColors sigma A)
      (hb : beta ∈ TreeMissingColors sigma A) :
      TashkinovAugmentation sigma A B := by
    rcases hstep with ⟨hlen, hinit, c, hedge, hc⟩
    refine ⟨hlen, hinit, ?_⟩
    have hcolor : phi (B.edge (Fin.cast hlen.symm (Fin.last A.length))) = some c := hedge
    have hcases : c = alpha ∨ c = beta ∨ (c ≠ alpha ∧ c ≠ beta) := by
      by_cases ha : c = alpha
      · exact Or.inl ha
      · by_cases hb : c = beta
        · exact Or.inr (Or.inl hb)
        · exact Or.inr (Or.inr ⟨ha, hb⟩)
    rcases hcases with hca | hcb | ⟨hcα, hcβ⟩
    · subst c
      by_cases hcomp : Sum.inr (B.edge (Fin.cast hlen.symm (Fin.last A.length))) ∈
          TwoColorComponent G phi alpha beta z
      · refine ⟨beta, ?_, hb⟩
        simp [sigma, TwoColorComponentSwap, hcomp, hcolor, hne]
      · refine ⟨alpha, ?_, ha⟩
        simp [sigma, TwoColorComponentSwap, hcomp, hcolor]
    · subst c
      by_cases hcomp : Sum.inr (B.edge (Fin.cast hlen.symm (Fin.last A.length))) ∈
          TwoColorComponent G phi alpha beta z
      · refine ⟨alpha, ?_, ha⟩
        simp [sigma, TwoColorComponentSwap, hcomp, hcolor, hne]
      · refine ⟨beta, ?_, hb⟩
        simp [sigma, TwoColorComponentSwap, hcomp, hcolor]
    · refine ⟨c, ?_, ?_⟩
      · change sigma (B.edge (Fin.cast hlen.symm (Fin.last A.length))) = some c
        by_cases hcomp : Sum.inr (B.edge (Fin.cast hlen.symm (Fin.last A.length))) ∈
            TwoColorComponent G phi alpha beta z
        · simp [sigma, TwoColorComponentSwap, hcomp, hcolor, hcα, hcβ]
        · simp [sigma, TwoColorComponentSwap, hcomp, hcolor]
      · rw [TreeMissingColors] at hc
        rcases Finset.mem_biUnion.mp hc with ⟨v, hv, hvc⟩
        simp only [TreeMissingColors, Finset.mem_biUnion]
        exact ⟨v, hv, missingStable hcα hcβ hvc⟩
  have transport : ∀ (A B : TreeSequence G e0),
      TashkinovAugmentationSequence phi A B →
      alpha ∈ TreeMissingColors sigma A →
      beta ∈ TreeMissingColors sigma A →
      TashkinovAugmentationSequence sigma A B := by
    intro A B hreach
    unfold TashkinovAugmentationSequence at hreach ⊢
    induction hreach using Relation.ReflTransGen.head_induction_on with
    | refl =>
        intro ha hb
        exact Relation.ReflTransGen.refl
    | head hstep htail ih =>
        intro ha hb
        rcases hstep with ⟨hlen, hinit, c, hedge, hc⟩
        have hac := missingTransfer hinit ha
        have hbc := missingTransfer hinit hb
        exact Relation.ReflTransGen.head
          (stepTransfer ⟨hlen, hinit, c, hedge, hc⟩ ha hb) (ih hac hbc)
  exact transport X Y hsequence halpha hbeta
