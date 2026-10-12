import Tablet.BoundaryEdges
import Tablet.ColoredVertexSetClosed
import Tablet.ColoredVertexSetElementary
import Tablet.Incident
import Tablet.MissingColors
import Tablet.OutsideTreeColorSwap
import Tablet.PresentColors
import Tablet.TashkinovAugmentation
import Tablet.TashkinovAugmentationSequence
import Tablet.TreeIncidentEdge
import Tablet.TreeMissingColors
import Tablet.TreeSequence
import Tablet.TreeSequenceInitialSegmentVertexSetSubset
import Tablet.TreeSequenceVertexSet
import Tablet.TreeVerticesBefore

set_option maxHeartbeats 400000

-- [TABLET NODE: P2966_T1_OutsideSwapPrefixEffects]
theorem P2966_T1_OutsideSwapPrefixEffects {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    (Tn Tj seed TjPrime : TreeSequence G e0)
    (phiJ rho1 rho0 mu0 : PartialEdgeColoring E k)
    (deltaN beta : Fin k) (terminalSupport u z : V)
    (zPosition : Fin (Tj.length + 1))
    (hTjN : TreeSequenceInitialSegment Tj Tn)
    (hterminalPrime : terminalSupport ∈ TreeSequenceVertexSet TjPrime)
    (hprimeClosed : ColoredVertexSetClosed G rho1
      (TreeSequenceVertexSet TjPrime))
    (hprimeElementary : ColoredVertexSetElementary G rho1
      (TreeSequenceVertexSet TjPrime))
    (hbetaDelta : beta ≠ deltaN)
    (hbeta : beta ∈ MissingColors G rho1 u)
    (hdeltaMissing : deltaN ∈ MissingColors G rho1 terminalSupport)
    (hb2Missing : ∀ v : V,
      v ∈ (TreeSequenceVertexSet Tj).erase terminalSupport →
      MissingColors G rho1 v = MissingColors G phiJ v)
    (haugmentation : TashkinovAugmentationSequence phiJ seed Tj)
    (hb2Edges : ∀ a : Fin Tj.length, seed.length ≤ a.val →
      rho1 (Tj.edge a) = phiJ (Tj.edge a))
    (hdeltaPhiJ : deltaN ∉ TreeMissingColors phiJ Tj)
    (hz : z ∈ TreeSequenceVertexSet Tj)
    (hzPosition : Tj.vertex zPosition = z)
    (hzAfter : seed.length ≤ zPosition.val)
    (huPrime : u ∈ TreeSequenceVertexSet TjPrime)
    (huOutside : u ∉ TreeSequenceVertexSet Tn)
    (hzBefore : ∀ w ∈ TreeVerticesBefore Tj z hz,
      beta ∉ MissingColors G rho1 w)
    (hzEdges : ∀ a : Fin Tj.length, seed.length ≤ a.val →
      a.val < zPosition.val → rho1 (Tj.edge a) ≠ some beta)
    (hrho0 : rho0 = OutsideTreeColorSwap TjPrime rho1 beta deltaN)
    (hrho0Fixed : ∀ f : E, TreeIncidentEdge TjPrime f → rho0 f = rho1 f)
    (hmuRho0Fixed : ∀ w : V,
      w ∈ TreeSequenceVertexSet Tn ∪ TreeSequenceVertexSet TjPrime →
      w ≠ u → ∀ f : E, Incident G w f → mu0 f = rho0 f)
    (hmissingPrime : ∀ w : V,
      w ∈ TreeSequenceVertexSet TjPrime → w ≠ u →
      MissingColors G mu0 w = MissingColors G rho1 w)
    (htreeEdgeFixed : ∀ a : Fin TjPrime.length,
      mu0 (TjPrime.edge a) = rho1 (TjPrime.edge a))
    (rho0_unaffected : ∀ c : Fin k, c ≠ beta → c ≠ deltaN →
      ∀ f : E, (rho0 f = some c ↔ rho1 f = some c)) :
    (∀ v : V,
      v ∈ (((TreeVerticesBefore Tj z hz ∪ {z}) ∪
          (TreeVerticesBefore TjPrime u huPrime ∪ {u})).erase u).erase z →
      MissingColors G mu0 v = MissingColors G rho1 v) ∧
    (∀ f : E,
      ((∃ a : Fin Tj.length,
          seed.length ≤ a.val ∧ a.val < zPosition.val ∧
            Tj.edge a = f) ∨
        (∃ (a : Fin TjPrime.length)
          (uPosition : Fin (TjPrime.length + 1)),
          TjPrime.vertex uPosition = u ∧ a.val < uPosition.val ∧
            TjPrime.edge a = f)) →
      mu0 f = rho1 f) ∧
    (beta ∈ MissingColors G rho1 z →
      deltaN ∈ MissingColors G mu0 z) ∧
    (z ∈ TreeVerticesBefore TjPrime u huPrime →
      MissingColors G mu0 z = MissingColors G rho1 z) := by
-- BODY
  classical
  have augmentation_edge_missing {B : TreeSequence G e0}
      (hreach : TashkinovAugmentationSequence phiJ seed B) :
      ∀ a : Fin B.length, seed.length ≤ a.val →
        ∃ i : Fin (B.length + 1), i.val ≤ a.val ∧
          ∃ c : Fin k, phiJ (B.edge a) = some c ∧
            c ∈ MissingColors G phiJ (B.vertex i) := by
    unfold TashkinovAugmentationSequence at hreach
    induction hreach with
    | refl =>
        intro a ha
        omega
    | @tail A B hprior ih hstep =>
        intro a ha
        rcases ih with ⟨hlen, hinit, cnew, hcolor, hmissing⟩
        by_cases hold : a.val < A.length
        · let old : Fin A.length := ⟨a.val, hold⟩
          obtain ⟨i, hi, c, hcol, hmiss⟩ := hstep old (by simpa [old] using ha)
          refine ⟨Fin.castLE (Nat.succ_le_succ hinit.1) i, ?_, c, ?_, ?_⟩
          · simpa using hi
          · have haold : Fin.castLE hinit.1 old = a := by
              apply Fin.ext
              rfl
            rw [← haold, hinit.2.2]
            simpa [old] using hcol
          · simpa [hinit.2.1] using hmiss
        · have hnew : a.val = A.length := by omega
          let last : Fin B.length := ⟨a.val, by omega⟩
          have hlast : a = last := by
            apply Fin.ext
            simp [last]
          rw [hlast]
          rw [show B.edge last = B.edge (Fin.cast hlen.symm (Fin.last _)) by
            congr 1
            apply Fin.ext
            simpa [last] using hnew]
          rw [hcolor]
          rw [TreeMissingColors] at hmissing
          obtain ⟨w, hw, hwm⟩ := Finset.mem_biUnion.mp hmissing
          simp only [TreeSequenceVertexSet, Finset.mem_image] at hw
          obtain ⟨i, hi, hwi⟩ := hw
          refine ⟨Fin.castLE (Nat.succ_le_succ hinit.1) i, ?_, cnew, rfl, ?_⟩
          · change i.val ≤ a.val
            omega
          · rw [hinit.2.1, hwi]
            exact hwm
  have hTjEdgeFixed : ∀ a : Fin Tj.length, seed.length ≤ a.val →
      a.val < zPosition.val → mu0 (Tj.edge a) = rho1 (Tj.edge a) := by
    intro a ha hapos
    have hnotBeta := hzEdges a ha hapos
    have hnotDelta : rho1 (Tj.edge a) ≠ some deltaN := by
      intro hdelta
      obtain ⟨i, hi, c, hcolor, hmissing⟩ :=
        augmentation_edge_missing haugmentation a ha
      have hphiDelta : phiJ (Tj.edge a) = some deltaN := by
        rw [← hb2Edges a ha]
        exact hdelta
      have hc : c = deltaN := Option.some.inj (hcolor.symm.trans hphiDelta)
      subst c
      apply hdeltaPhiJ
      unfold TreeMissingColors
      exact Finset.mem_biUnion.mpr ⟨Tj.vertex i, by
        simp [TreeSequenceVertexSet], hmissing⟩
    have hlaterJ : Tj.vertex a.succ ∈ TreeSequenceVertexSet Tj := by
      simp [TreeSequenceVertexSet]
    have hlaterN := TreeSequenceInitialSegmentVertexSetSubset hTjN hlaterJ
    obtain ⟨i, hi⟩ := Tj.attaches a
    have hlaterInc : Incident G (Tj.vertex a.succ) (Tj.edge a) := by
      change Tj.vertex a.succ ∈ G.ends (Tj.edge a)
      rw [hi]
      simp
    have hmuRho0 := hmuRho0Fixed (Tj.vertex a.succ)
      (Finset.mem_union.mpr (Or.inl hlaterN))
      (by intro h; subst u; exact huOutside hlaterN) (Tj.edge a) hlaterInc
    rw [hmuRho0]
    by_cases ht : TreeIncidentEdge TjPrime (Tj.edge a)
    · exact hrho0Fixed (Tj.edge a) ht
    · simp [hrho0, OutsideTreeColorSwap, ht, hnotBeta, hnotDelta]
  have before_mem_and_ne : ∀ {A : TreeSequence G e0} {a : V}
      (ha : a ∈ TreeSequenceVertexSet A) (w : V),
      w ∈ TreeVerticesBefore A a ha →
        w ∈ TreeSequenceVertexSet A ∧ w ≠ a := by
    intro A a ha w hw
    unfold TreeVerticesBefore at hw
    obtain ⟨hwA, i, j, hiw, hja, hij⟩ := Finset.mem_filter.mp hw
    refine ⟨hwA, ?_⟩
    intro hwa
    have hijEq : i = j := A.vertex_injective (hiw.trans (hwa.trans hja.symm))
    subst j
    omega
  have missing_eq_mu_rho0 : ∀ (w : V),
      (∀ f : E, Incident G w f → mu0 f = rho0 f) →
      MissingColors G mu0 w = MissingColors G rho0 w := by
    intro w hfixed
    apply Finset.ext
    intro c
    simp only [MissingColors, Finset.mem_sdiff, Finset.mem_univ, true_and,
      PresentColors, Finset.mem_filter]
    constructor
    · intro hnew hold
      obtain ⟨f, hwf, hfc⟩ := hold
      exact hnew ⟨f, hwf, (hfixed f hwf).trans hfc⟩
    · intro hold hnew
      obtain ⟨f, hwf, hfc⟩ := hnew
      exact hold ⟨f, hwf, (hfixed f hwf).symm.trans hfc⟩
  have outside_before_missing_eq : ∀ w : V,
      w ∈ TreeVerticesBefore Tj z hz →
      w ∉ TreeSequenceVertexSet TjPrime →
      MissingColors G mu0 w = MissingColors G rho1 w := by
    intro w hwBefore hwOutsidePrime
    obtain ⟨hwJ, hwz⟩ := before_mem_and_ne hz w hwBefore
    have hwN := TreeSequenceInitialSegmentVertexSetSubset hTjN hwJ
    have hwu : w ≠ u := by
      intro h
      subst w
      exact huOutside hwN
    have hwTerminal : w ≠ terminalSupport := by
      intro h
      subst w
      exact hwOutsidePrime hterminalPrime
    have hbetaPresentRho : beta ∈ PresentColors G rho1 w := by
      simpa [MissingColors] using hzBefore w hwBefore
    have hdeltaNotMissingPhi :
        deltaN ∉ MissingColors G phiJ w := by
      intro hdelta
      apply hdeltaPhiJ
      unfold TreeMissingColors
      exact Finset.mem_biUnion.mpr ⟨w, hwJ, hdelta⟩
    have hdeltaNotMissingRho :
        deltaN ∉ MissingColors G rho1 w := by
      rw [hb2Missing w (Finset.mem_erase.mpr ⟨hwTerminal, hwJ⟩)]
      exact hdeltaNotMissingPhi
    have hdeltaPresentRho : deltaN ∈ PresentColors G rho1 w := by
      simpa [MissingColors] using hdeltaNotMissingRho
    have affected_not_tree : ∀ (f : E), Incident G w f →
        (rho1 f = some beta ∨ rho1 f = some deltaN) →
        ¬ TreeIncidentEdge TjPrime f := by
      intro f hwf hcolor ht
      obtain ⟨q, hqPrime, hqf⟩ := ht
      have hqw : q ≠ w := by
        intro h
        subst q
        exact hwOutsidePrime hqPrime
      have hboundary : f ∈ BoundaryEdges G
          (TreeSequenceVertexSet TjPrime) := by
        unfold BoundaryEdges
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨q, hqPrime, w, hwOutsidePrime,
          (Sym2.mem_and_mem_iff hqw).mp ⟨hqf, hwf⟩⟩
      rcases hcolor with hcolor | hcolor
      · exact (hprimeClosed hboundary huPrime hcolor) hbeta
      · exact (hprimeClosed hboundary hterminalPrime hcolor) hdeltaMissing
    have hbetaPresentRho0 : beta ∈ PresentColors G rho0 w := by
      simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
      simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
        at hdeltaPresentRho
      obtain ⟨f, hwf, hcolor⟩ := hdeltaPresentRho
      have ht := affected_not_tree f hwf (Or.inr hcolor)
      refine ⟨f, hwf, ?_⟩
      simp [hrho0, OutsideTreeColorSwap, ht, hcolor, hbetaDelta,
        hbetaDelta.symm]
    have hdeltaPresentRho0 : deltaN ∈ PresentColors G rho0 w := by
      simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
      simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
        at hbetaPresentRho
      obtain ⟨f, hwf, hcolor⟩ := hbetaPresentRho
      have ht := affected_not_tree f hwf (Or.inl hcolor)
      refine ⟨f, hwf, ?_⟩
      simp [hrho0, OutsideTreeColorSwap, ht, hcolor, hbetaDelta,
        hbetaDelta.symm]
    have hpresentEq : PresentColors G rho0 w = PresentColors G rho1 w := by
      apply Finset.ext
      intro c
      by_cases hcb : c = beta
      · subst c
        exact iff_of_true hbetaPresentRho0 hbetaPresentRho
      · by_cases hcd : c = deltaN
        · subst c
          exact iff_of_true hdeltaPresentRho0 hdeltaPresentRho
        · simp only [PresentColors, Finset.mem_filter, Finset.mem_univ,
            true_and]
          constructor
          · rintro ⟨f, hwf, hfc⟩
            exact ⟨f, hwf, (rho0_unaffected c hcb hcd f).mp hfc⟩
          · rintro ⟨f, hwf, hfc⟩
            exact ⟨f, hwf, (rho0_unaffected c hcb hcd f).mpr hfc⟩
    have hrhoMissing : MissingColors G rho0 w = MissingColors G rho1 w := by
      simp [MissingColors, hpresentEq]
    exact (missing_eq_mu_rho0 w (hmuRho0Fixed w
      (Finset.mem_union.mpr (Or.inl hwN)) hwu)).trans hrhoMissing
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro v hv
    obtain ⟨hvz, hv⟩ := Finset.mem_erase.mp hv
    obtain ⟨hvu, hv⟩ := Finset.mem_erase.mp hv
    rcases Finset.mem_union.mp hv with hv | hv
    · rcases Finset.mem_union.mp hv with hvBefore | hvz'
      · by_cases hvPrime : v ∈ TreeSequenceVertexSet TjPrime
        · exact hmissingPrime v hvPrime hvu
        · exact outside_before_missing_eq v hvBefore hvPrime
      · exact False.elim (hvz (by simpa using hvz'))
    · rcases Finset.mem_union.mp hv with hvBefore | hvu'
      · exact hmissingPrime v (before_mem_and_ne huPrime v hvBefore).1 hvu
      · exact False.elim (hvu (by simpa using hvu'))
  · intro f hf
    rcases hf with hf | hf
    · obtain ⟨a, ha, haz, rfl⟩ := hf
      exact hTjEdgeFixed a ha haz
    · obtain ⟨a, uPosition, huPosition, hau, rfl⟩ := hf
      exact htreeEdgeFixed a
  · intro hbetaZ
    have hzN := TreeSequenceInitialSegmentVertexSetSubset hTjN hz
    have hzu : z ≠ u := by
      intro h
      apply huOutside
      rw [← h]
      exact hzN
    have hmuRho0Z := missing_eq_mu_rho0 z (hmuRho0Fixed z
      (Finset.mem_union.mpr (Or.inl hzN)) hzu)
    rw [hmuRho0Z]
    by_cases hzPrime : z ∈ TreeSequenceVertexSet TjPrime
    · have hdisjoint := hprimeElementary hzPrime huPrime hzu
      exact False.elim ((Finset.disjoint_left.mp hdisjoint) hbetaZ hbeta)
    · apply Finset.mem_sdiff.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      intro hdeltaPresent
      simp only [PresentColors, Finset.mem_filter, Finset.mem_univ,
        true_and] at hdeltaPresent
      obtain ⟨f, hzf, hfRho0⟩ := hdeltaPresent
      by_cases ht : TreeIncidentEdge TjPrime f
      · have hfRho1 : rho1 f = some deltaN := by
          simpa [hrho0, OutsideTreeColorSwap, ht] using hfRho0
        obtain ⟨q, hqPrime, hqf⟩ := ht
        have hqz : q ≠ z := by
          intro h
          subst q
          exact hzPrime hqPrime
        have hboundary : f ∈ BoundaryEdges G
            (TreeSequenceVertexSet TjPrime) := by
          unfold BoundaryEdges
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨q, hqPrime, z, hzPrime,
            (Sym2.mem_and_mem_iff hqz).mp ⟨hqf, hzf⟩⟩
        exact (hprimeClosed hboundary hterminalPrime hfRho1) hdeltaMissing
      · have hfBeta : rho1 f = some beta := by
          by_cases hfb : rho1 f = some beta
          · exact hfb
          · by_cases hfd : rho1 f = some deltaN
            · have : (some beta : Option (Fin k)) = some deltaN := by
                simpa [hrho0, OutsideTreeColorSwap, ht, hfb, hfd,
                  hbetaDelta, hbetaDelta.symm] using hfRho0
              exact False.elim (hbetaDelta (Option.some.inj this))
            · have : rho1 f = some deltaN := by
                simpa [hrho0, OutsideTreeColorSwap, ht, hfb, hfd]
                  using hfRho0
              exact False.elim (hfd this)
        have hbetaNotPresent : beta ∉ PresentColors G rho1 z := by
          simpa [MissingColors] using hbetaZ
        exact hbetaNotPresent (by
          simp only [PresentColors, Finset.mem_filter, Finset.mem_univ,
            true_and]
          exact ⟨f, hzf, hfBeta⟩)
  · intro hzBeforePrime
    obtain ⟨hzPrime, hzu⟩ :=
      before_mem_and_ne huPrime z hzBeforePrime
    exact hmissingPrime z hzPrime hzu
