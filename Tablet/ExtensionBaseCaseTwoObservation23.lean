import Tablet.ColoredVertexSetElementary
import Tablet.MissingColors
import Tablet.TashkinovAugmentation
import Tablet.TashkinovAugmentationSequence
import Tablet.TreeMissingColors
import Tablet.TreeSequenceInitialSegment
import Tablet.TreeSequenceVertexSet
import Tablet.TreeVerticesBefore

-- [TABLET NODE: ExtensionBaseCaseTwoObservation23]
theorem ExtensionBaseCaseTwoObservation23 {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    (Tj seed TjPrime : TreeSequence G e0)
    (phiJ rho1 : PartialEdgeColoring E k)
    (terminalSupport u : V) (beta gammaFirst : Fin k)
    (hseedJ : TreeSequenceInitialSegment seed Tj)
    (hseedPrime : TreeSequenceInitialSegment seed TjPrime)
    (hseedTerminal : seed.vertex (Fin.last seed.length) = terminalSupport)
    (huPrime : u ∈ TreeSequenceVertexSet TjPrime)
    (huSeed : u ∉ TreeSequenceVertexSet seed)
    (hprimeElementary : ColoredVertexSetElementary G rho1
      (TreeSequenceVertexSet TjPrime))
    (hbetaU : beta ∈ MissingColors G rho1 u)
    (hterminalSeed : terminalSupport ∈ TreeSequenceVertexSet seed)
    (hb2Missing : ∀ v : V,
      v ∈ (TreeSequenceVertexSet Tj).erase terminalSupport →
      MissingColors G rho1 v = MissingColors G phiJ v)
    (hterminalRho : beta ∉ MissingColors G rho1 terminalSupport)
    (hterminalInclusion : MissingColors G phiJ terminalSupport ⊆
      MissingColors G rho1 terminalSupport ∪ {gammaFirst})
    (hbetaGamma : beta ≠ gammaFirst)
    (haugmentation : TashkinovAugmentationSequence phiJ seed Tj)
    (hb2Edges : ∀ a : Fin Tj.length, seed.length ≤ a.val →
      rho1 (Tj.edge a) = phiJ (Tj.edge a)) :
    ∃ (z : V) (hz : z ∈ TreeSequenceVertexSet Tj)
      (zPosition : Fin (Tj.length + 1)),
      Tj.vertex zPosition = z ∧ seed.length ≤ zPosition.val ∧
        ((seed.length < zPosition.val ∧
            beta ∈ MissingColors G rho1 z ∧
            ∀ r : Fin (Tj.length + 1),
              seed.length < r.val → r.val < zPosition.val →
              beta ∉ MissingColors G rho1 (Tj.vertex r)) ∨
          (zPosition = Fin.last Tj.length ∧
            ∀ r : Fin (Tj.length + 1), seed.length < r.val →
              beta ∉ MissingColors G rho1 (Tj.vertex r))) ∧
        (∀ w ∈ TreeVerticesBefore Tj z hz,
          beta ∉ MissingColors G rho1 w) ∧
        ∀ a : Fin Tj.length, seed.length ≤ a.val →
          a.val < zPosition.val → rho1 (Tj.edge a) ≠ some beta := by
-- BODY
  classical
  have initial_subset {A B : TreeSequence G e0}
      (h : TreeSequenceInitialSegment A B) :
      TreeSequenceVertexSet A ⊆ TreeSequenceVertexSet B := by
    intro v hv
    simp only [TreeSequenceVertexSet, Finset.mem_image] at hv ⊢
    obtain ⟨i, hi, hvi⟩ := hv
    obtain ⟨hlen, hvertices, hedges⟩ := h
    exact ⟨Fin.castLE (Nat.succ_le_succ hlen) i, Finset.mem_univ _,
      (hvertices i).trans hvi⟩
  have reach_subset {A B : TreeSequence G e0}
      (h : TashkinovAugmentationSequence phiJ A B) :
      TreeSequenceVertexSet A ⊆ TreeSequenceVertexSet B := by
    unfold TashkinovAugmentationSequence at h
    induction h using Relation.ReflTransGen.head_induction_on with
    | refl => exact Finset.Subset.rfl
    | head hstep htail ih =>
        exact (initial_subset hstep.2.1).trans ih
  have seed_subset_prime : TreeSequenceVertexSet seed ⊆
      TreeSequenceVertexSet TjPrime := initial_subset hseedPrime
  have seed_subset_j : TreeSequenceVertexSet seed ⊆
      TreeSequenceVertexSet Tj := reach_subset haugmentation
  have beta_seed : ∀ v ∈ TreeSequenceVertexSet seed,
      beta ∉ MissingColors G rho1 v := by
    intro v hv hvm
    have hvp : v ∈ TreeSequenceVertexSet TjPrime := seed_subset_prime hv
    have huv : u ≠ v := by
      intro huv
      apply huSeed
      simpa [huv] using hv
    have hd := hprimeElementary (u := v) (v := u) hvp huPrime huv.symm
    exact (Finset.disjoint_left.1 hd) hvm hbetaU
  let candidates := (Finset.univ : Finset (Fin (Tj.length + 1))).filter
    (fun i => seed.length < i.val ∧
      beta ∈ MissingColors G rho1 (Tj.vertex i))
  have last_after : seed.length ≤ (Fin.last Tj.length).val := by
    have hlen : seed.length ≤ Tj.length := by
      exact Nat.le_trans hseedJ.1 (le_refl _)
    simp
    omega
  have edge_missing {B : TreeSequence G e0}
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
          obtain ⟨v, hv, hvm⟩ := Finset.mem_biUnion.mp hmissing
          simp only [TreeSequenceVertexSet, Finset.mem_image] at hv
          obtain ⟨i, hi, hvi⟩ := hv
          refine ⟨Fin.castLE (Nat.succ_le_succ hinit.1) i, ?_, cnew, rfl, ?_⟩
          · change i.val ≤ a.val
            omega
          · rw [hinit.2.1]
            rw [hvi]
            exact hvm
  by_cases hcandidates : candidates.Nonempty
  · let q := candidates.min' hcandidates
    let z := Tj.vertex q
    have hqmem : q ∈ candidates := Finset.min'_mem candidates hcandidates
    have hqafter : seed.length < q.val := (Finset.mem_filter.mp hqmem).2.1
    have hqmiss : beta ∈ MissingColors G rho1 z := (Finset.mem_filter.mp hqmem).2.2
    have before_exclusion : ∀ i : Fin (Tj.length + 1), i.val < q.val →
        beta ∉ MissingColors G rho1 (Tj.vertex i) := by
      intro i hi hmiss
      by_cases hsmall : i.val < seed.length
      · obtain ⟨hlen, hvertices, hedges⟩ := hseedJ
        let si : Fin (seed.length + 1) := ⟨i.val, by omega⟩
        have heq : Fin.castLE (Nat.succ_le_succ hlen) si = i := by
          apply Fin.ext
          rfl
        have hseedmiss : beta ∈ MissingColors G rho1 (seed.vertex si) := by
          rw [← hvertices si, heq]
          exact hmiss
        exact beta_seed (seed.vertex si) (by
          simp [TreeSequenceVertexSet]) hseedmiss
      · by_cases heq : i.val = seed.length
        · obtain ⟨hlen, hvertices, hedges⟩ := hseedJ
          have hlast : (Fin.last seed.length).val = seed.length := rfl
          let si : Fin (seed.length + 1) := Fin.last seed.length
          have hpos : Fin.castLE (Nat.succ_le_succ hlen) si = i := by
            apply Fin.ext
            simpa [si] using heq.symm
          have hterm : Tj.vertex i = terminalSupport := by
            rw [← hpos, hvertices, hseedTerminal]
          rw [hterm] at hmiss
          exact hterminalRho hmiss
        · have hlarge : seed.length < i.val := by omega
          have hrmem : i ∈ candidates := Finset.mem_filter.mpr
            ⟨Finset.mem_univ _, hlarge, hmiss⟩
          have hmin := Finset.min'_le candidates i hrmem
          exact (Nat.not_lt_of_ge hmin) hi
    have hzset : z ∈ TreeSequenceVertexSet Tj := by
      simp [TreeSequenceVertexSet, z]
    refine ⟨z, hzset, q, rfl, le_of_lt hqafter, Or.inl ⟨hqafter,
      hqmiss, ?_⟩, ?_, ?_⟩
    · intro r hr hrl
      intro hmiss
      have hrmem : r ∈ candidates := Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, hr, hmiss⟩
      have hmin := Finset.min'_le candidates r hrmem
      exact (Nat.not_lt_of_ge hmin) hrl
    · intro w hw
      unfold TreeVerticesBefore at hw
      have horder := (Finset.mem_filter.mp hw).2
      rcases horder with ⟨i, j, hi, hj, hij⟩
      have hjq : j = q := Tj.vertex_injective (hj.trans rfl)
      subst j
      rw [← hi]
      exact before_exclusion i (by simpa using hij)
    · intro a ha hlt hbad
      obtain ⟨i, hi, c, hcol, hmiss⟩ := edge_missing haugmentation a ha
      have hil : i.val < q.val := lt_of_le_of_lt hi hlt
      have hrho : beta ∉ MissingColors G rho1 (Tj.vertex i) :=
        before_exclusion i hil
      have hphi : beta ∉ MissingColors G phiJ (Tj.vertex i) := by
        by_cases hit : Tj.vertex i = terminalSupport
        · intro hb
          rw [hit] at hb
          have hin := hterminalInclusion hb
          rcases Finset.mem_union.mp hin with hin | hin
          · exact hterminalRho (hit ▸ hin)
          · have : beta = gammaFirst := by simpa using hin
            exact hbetaGamma this
        · have hiSet : Tj.vertex i ∈ (TreeSequenceVertexSet Tj).erase terminalSupport :=
            Finset.mem_erase.mpr ⟨hit, by
              simp [TreeSequenceVertexSet]⟩
          rw [← hb2Missing _ hiSet]
          exact hrho
      have hbad' : phiJ (Tj.edge a) = some beta := by
        rw [← hb2Edges a ha]
        exact hbad
      have hcEq : c = beta := Option.some.inj (hcol.symm.trans hbad')
      subst c
      exact hphi hmiss
  · have hqmiss : ∀ r : Fin (Tj.length + 1), seed.length < r.val →
        beta ∉ MissingColors G rho1 (Tj.vertex r) := by
      intro r hr hmiss
      apply hcandidates
      exact ⟨r, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr, hmiss⟩⟩
    let q : Fin (Tj.length + 1) := Fin.last Tj.length
    let z := Tj.vertex q
    have hzset : z ∈ TreeSequenceVertexSet Tj := by
      simp [TreeSequenceVertexSet, z]
    refine ⟨z, hzset, q, rfl, ?_, Or.inr ⟨rfl, hqmiss⟩, ?_, ?_⟩
    · simpa [q] using last_after
    · intro w hw
      unfold TreeVerticesBefore at hw
      have horder := (Finset.mem_filter.mp hw).2
      rcases horder with ⟨i, j, hi, hj, hij⟩
      have hjq : j = q := Tj.vertex_injective (hj.trans rfl)
      subst j
      rw [← hi]
      exact (by
        by_cases hsmall : i.val ≤ seed.length
        · by_cases heq : i.val = seed.length
          · obtain ⟨hlen, hvertices, hedges⟩ := hseedJ
            let si : Fin (seed.length + 1) := Fin.last seed.length
            have hpos : Fin.castLE (Nat.succ_le_succ hlen) si = i := by
              apply Fin.ext
              simpa [si] using heq.symm
            have hterm : Tj.vertex i = terminalSupport := by
              rw [← hpos, hvertices, hseedTerminal]
            rw [hterm]
            exact hterminalRho
          · have hlt : i.val < seed.length := by omega
            obtain ⟨hlen, hvertices, hedges⟩ := hseedJ
            let si : Fin (seed.length + 1) := ⟨i.val, by omega⟩
            have hpos : Fin.castLE (Nat.succ_le_succ hlen) si = i := by
              apply Fin.ext
              rfl
            have hset : seed.vertex si ∈ TreeSequenceVertexSet seed := by
              simp [TreeSequenceVertexSet]
            rw [← hpos, hvertices]
            exact beta_seed _ hset
        · exact hqmiss i (by omega))
    · intro a ha hlt hbad
      exact (by
        obtain ⟨i, hi, c, hcol, hmiss⟩ := edge_missing haugmentation a ha
        have hil : i.val < q.val := lt_of_le_of_lt hi hlt
        have hiMiss : beta ∉ MissingColors G rho1 (Tj.vertex i) := by
          by_cases hiSeed : i.val ≤ seed.length
          · by_cases hiTerm : i.val = seed.length
            · obtain ⟨hlen, hvertices, hedges⟩ := hseedJ
              let si : Fin (seed.length + 1) := Fin.last seed.length
              have hpos : Fin.castLE (Nat.succ_le_succ hlen) si = i := by
                apply Fin.ext
                simpa [si] using hiTerm.symm
              rw [← hpos, hvertices, hseedTerminal]
              exact hterminalRho
            · obtain ⟨hlen, hvertices, hedges⟩ := hseedJ
              let si : Fin (seed.length + 1) := ⟨i.val, by omega⟩
              have hpos : Fin.castLE (Nat.succ_le_succ hlen) si = i := by
                apply Fin.ext
                rfl
              rw [← hpos, hvertices]
              exact beta_seed _ (by
                simp [TreeSequenceVertexSet])
          · exact hqmiss i (by omega)
        have hphi : beta ∉ MissingColors G phiJ (Tj.vertex i) := by
          by_cases hit : Tj.vertex i = terminalSupport
          · intro hb
            rw [hit] at hb
            have hin := hterminalInclusion hb
            rcases Finset.mem_union.mp hin with hin | hin
            · exact hterminalRho (hit ▸ hin)
            · exact hbetaGamma (by simpa using hin)
          · rw [← hb2Missing _ (Finset.mem_erase.mpr ⟨hit, by
              simp [TreeSequenceVertexSet]⟩)]
            exact hiMiss
        have hbad' : phiJ (Tj.edge a) = some beta := by
          rw [← hb2Edges a ha]
          exact hbad
        have : c = beta := Option.some.inj (hcol.symm.trans hbad')
        subst c
        exact hphi hmiss)
