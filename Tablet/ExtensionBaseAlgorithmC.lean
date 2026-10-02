import Tablet.AdjacentEdges
import Tablet.ETTStrongInterchangeable
import Tablet.ExtensionBaseAlgorithmCInvariant
import Tablet.ExtensionBaseAlgorithmCTrace
import Tablet.ExtensionBaseSupportClass
import Tablet.ExtensionBaseSupportClassColors
import Tablet.Incident
import Tablet.IsOneEdgeUncolored
import Tablet.IsProperEdgeColoring
import Tablet.MissingColors
import Tablet.PresentColors
import Tablet.StrongInterchangeabilityKempePreserved
import Tablet.TashkinovExtensionKind
import Tablet.TreeSequenceInitialSegment
import Tablet.TreeSequenceVertexSet
import Tablet.TwoColorComponent
import Tablet.TwoColorComponentCycle
import Tablet.TwoColorComponentSpanningPath
import Tablet.TwoColorComponentSwap
import Tablet.TwoColorComponentSwapProper
import Tablet.TwoColorCycle
import Tablet.TwoColorIncidenceDegreeAtMostTwo
import Tablet.TwoColorIncidenceGraph
import Tablet.TwoColorNontrivialPathComponent

-- [TABLET NODE: ExtensionBaseAlgorithmC]
theorem ExtensionBaseAlgorithmC {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    {input : PartialEdgeColoring E k} {T : TreeSequence G e0}
    {generating : PartialEdgeColoring E k}
    (ett : ExtendedTashkinovTree G k e0 input T generating)
    (terminalSupport : V)
    (hterminalSupport : terminalSupport ∈ TreeSequenceVertexSet T)
    (terminalSlot jSlot : Fin ett.rounds)
    (mu0 : PartialEdgeColoring E k) (u : V)
    (p : ℕ) (indices : Fin (p + 1) → Fin ett.rounds)
    (gamma delta : Fin (p + 1) → Fin k)
    (hproper : IsProperEdgeColoring G mu0)
    (hone : IsOneEdgeUncolored mu0 e0)
    (hterminalAtEnd : terminalSlot.val + 1 = ett.rounds)
    (hincreasing : ∀ a c, a.val < c.val →
      (indices a).val < (indices c).val)
    (hclass : ∀ s : Fin ett.rounds,
      s ∈ ExtensionBaseSupportClass ett terminalSupport hterminalSupport
          terminalSupport ↔
        ∃ a : Fin (p + 1), indices a = s)
    (hterminalIndex : indices (Fin.last p) = terminalSlot)
    (hsupport : ∀ a,
      ett.series.data.chosenVertex (indices a).succ = some terminalSupport)
    (hkind : ∀ a,
      ett.series.data.kind (indices a).succ =
        some TashkinovExtensionKind.PE)
    (hgamma : ∀ a,
      ett.series.data.gamma (indices a).succ = some (gamma a))
    (hdelta : ∀ a,
      ett.series.data.delta (indices a).succ = some (delta a))
    (hstored : ∀ a,
      ett.series.data.stored (indices a).succ = {gamma a, delta a})
    (hchain : ∀ a : Fin p, gamma a.succ = delta a.castSucc)
    (hdistinct : Function.Injective (Fin.cons (gamma 0) delta))
    (hTjInitial : ∀ s : Fin ett.rounds,
      s ∈ (ExtensionBaseSupportClass ett terminalSupport hterminalSupport
          terminalSupport).erase terminalSlot →
        TreeSequenceInitialSegment
          (ett.series.data.tree jSlot.succ.castSucc)
          (ett.series.data.tree s.succ.castSucc))
    (hterminalGammaMissing :
      gamma (Fin.last p) ∈ MissingColors G mu0 u)
    (hinitialGammaPresent : ∀ a : Fin p,
      gamma a.castSucc ∈ PresentColors G mu0 u)
    (hinitialSI : ∀ (s : Fin ett.rounds) (gammaS deltaS : Fin k),
      s ∈ (ExtensionBaseSupportClass ett terminalSupport hterminalSupport
          terminalSupport).erase terminalSlot →
      ett.series.data.gamma s.succ = some gammaS →
      ett.series.data.delta s.succ = some deltaS →
      ETTStrongInterchangeable ett s terminalSupport mu0 gammaS deltaS)
    (hterminalNoMissing :
      MissingColors G mu0 terminalSupport ∩
        ((ExtensionBaseSupportClass ett terminalSupport hterminalSupport
          terminalSupport).erase terminalSlot).biUnion
            (fun s => ett.series.data.stored s.succ) = ∅) :
    ∃ trace : ExtensionBaseAlgorithmCTrace ett terminalSupport
        hterminalSupport terminalSlot mu0 u,
      ExtensionBaseAlgorithmCInvariant ett terminalSupport
        hterminalSupport terminalSlot jSlot mu0 u trace := by
-- BODY
  classical
  let supportClass :=
    ExtensionBaseSupportClass ett terminalSupport hterminalSupport terminalSupport
  have hterminalInClass : terminalSlot ∈ supportClass := by
    rw [hclass]
    exact ⟨Fin.last p, hterminalIndex⟩
  have herased : supportClass.erase terminalSlot =
      Finset.univ.image (fun a : Fin p => indices a.castSucc) := by
    ext s
    constructor
    · intro hs
      have hsClass : s ∈ supportClass := (Finset.mem_erase.mp hs).2
      obtain ⟨a, ha⟩ := (hclass s).mp hsClass
      have haLast : a ≠ Fin.last p := by
        intro h
        apply (Finset.mem_erase.mp hs).1
        rw [← ha, h, hterminalIndex]
      have haLt : a.val < p := by
        have haLe : a.val ≤ p := Nat.le_of_lt_succ a.isLt
        rcases lt_or_eq_of_le haLe with hlt | heq
        · exact hlt
        · exact False.elim (haLast (Fin.ext heq))
      let b : Fin p := ⟨a.val, haLt⟩
      have hb : b.castSucc = a := Fin.ext rfl
      rw [Finset.mem_image]
      exact ⟨b, Finset.mem_univ b, by simpa [hb] using ha⟩
    · intro hs
      rw [Finset.mem_image] at hs
      obtain ⟨a, -, ha⟩ := hs
      rw [Finset.mem_erase]
      refine ⟨?_, (hclass s).2 ⟨a.castSucc, ha⟩⟩
      intro hsTerminal
      have hindexEq : indices a.castSucc = indices (Fin.last p) := by
        rw [ha, hsTerminal, hterminalIndex]
      have hvalLt : a.castSucc.val < (Fin.last p).val := by
        simp
      exact (Nat.ne_of_lt (hincreasing a.castSucc (Fin.last p) hvalLt))
        (congrArg Fin.val hindexEq)
  by_cases hp : p = 0
  · subst p
    let trace : ExtensionBaseAlgorithmCTrace ett terminalSupport
        hterminalSupport terminalSlot mu0 u := {
      steps := 0
      slot := fun a => Fin.elim0 a
      gamma := fun a => Fin.elim0 a
      delta := fun a => Fin.elim0 a
      coloring := fun _ => mu0
      initialColoring := rfl
      terminalAtEnd := hterminalAtEnd
      terminalInClass := hterminalInClass
      enumerates := by simpa [supportClass] using herased.symm
      strictlyDescending := fun a => Fin.elim0 a
      chosenSupport := fun a => Fin.elim0 a
      extensionKind := fun a => Fin.elim0 a
      gammaField := fun a => Fin.elim0 a
      deltaField := fun a => Fin.elim0 a
      transition := fun a => Fin.elim0 a }
    refine ⟨trace, ?_⟩
    unfold ExtensionBaseAlgorithmCInvariant
    refine ⟨?_, ?_, ?_⟩
    · intro a
      exact ⟨hproper, hone⟩
    · intro a
      exact Fin.elim0 a
    · intro s gammaS deltaS hs _ hsupportS hgammaS hdeltaS
      exact hinitialSI s gammaS deltaS hs hgammaS hdeltaS
  · have hpPos : 0 < p := Nat.pos_of_ne_zero hp
    let reversePosition : Fin p → Fin (p + 1) := fun a => a.rev.castSucc
    let slot : Fin p → Fin ett.rounds := fun a => indices (reversePosition a)
    let traceGamma : Fin p → Fin k := fun a => gamma (reversePosition a)
    let traceDelta : Fin p → Fin k := fun a => delta (reversePosition a)
    let nextColoring : ℕ → PartialEdgeColoring E k → PartialEdgeColoring E k :=
      fun a phi => if ha : a < p then
        TwoColorComponentSwap G phi
          (traceGamma ⟨a, ha⟩) (traceDelta ⟨a, ha⟩) (Sum.inl u)
      else phi
    let coloringNat : ℕ → PartialEdgeColoring E k :=
      Nat.rec mu0 (fun a phi => nextColoring a phi)
    let coloring : Fin (p + 1) → PartialEdgeColoring E k :=
      fun a => coloringNat a.val
    have hslotEnumerates : Finset.univ.image slot = supportClass.erase terminalSlot := by
      rw [herased]
      ext s
      simp only [Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨a, rfl⟩
        exact ⟨a.rev, by simp [slot, reversePosition]⟩
      · rintro ⟨a, rfl⟩
        exact ⟨a.rev, by simp [slot, reversePosition]⟩
    have hslotDescending : ∀ a b : Fin p, a.val < b.val →
        (slot b).val < (slot a).val := by
      intro a b hab
      apply hincreasing
      change b.rev.val < a.rev.val
      exact Fin.rev_lt_rev.mpr hab
    have htransition : ∀ a : Fin p,
        coloring a.succ = TwoColorComponentSwap G (coloring a.castSucc)
          (traceGamma a) (traceDelta a) (Sum.inl u) := by
      intro a
      simp [coloring, coloringNat, nextColoring, a.isLt]
    let trace : ExtensionBaseAlgorithmCTrace ett terminalSupport
        hterminalSupport terminalSlot mu0 u := {
      steps := p
      slot := slot
      gamma := traceGamma
      delta := traceDelta
      coloring := coloring
      initialColoring := by simp [coloring, coloringNat]
      terminalAtEnd := hterminalAtEnd
      terminalInClass := hterminalInClass
      enumerates := hslotEnumerates
      strictlyDescending := hslotDescending
      chosenSupport := fun a => hsupport (reversePosition a)
      extensionKind := fun a => hkind (reversePosition a)
      gammaField := fun a => hgamma (reversePosition a)
      deltaField := fun a => hdelta (reversePosition a)
      transition := htransition }
    let colorChain : Fin (p + 2) → Fin k := Fin.cons (gamma 0) delta
    have gamma_eq_chain (q : Fin (p + 1)) :
        gamma q = colorChain q.castSucc := by
      cases q using Fin.cases with
      | zero => simp [colorChain]
      | succ a => simpa [colorChain] using hchain a
    have delta_eq_chain (q : Fin (p + 1)) :
        delta q = colorChain q.succ := by
      simp [colorChain]
    have trace_colors_ne (a : Fin p) :
        trace.gamma a ≠ trace.delta a := by
      change gamma (reversePosition a) ≠ delta (reversePosition a)
      rw [gamma_eq_chain, delta_eq_chain]
      intro h
      have hi := hdistinct h
      have hv := congrArg Fin.val hi
      simp at hv
    have surviving_gamma_ne (a b : Fin p) (hab : a.val < b.val) :
        trace.gamma b ≠ trace.gamma a ∧
          trace.gamma b ≠ trace.delta a := by
      change gamma (reversePosition b) ≠ gamma (reversePosition a) ∧
        gamma (reversePosition b) ≠ delta (reversePosition a)
      rw [gamma_eq_chain, gamma_eq_chain, delta_eq_chain]
      constructor <;> intro h
      · have hi := hdistinct h
        have hv := congrArg Fin.val hi
        change b.rev.val = a.rev.val at hv
        have := Fin.rev_lt_rev.mpr hab
        omega
      · have hi := hdistinct h
        have hv := congrArg Fin.val hi
        change b.rev.val = a.rev.val + 1 at hv
        have := Fin.rev_lt_rev.mpr hab
        omega
    refine ⟨trace, ?_⟩
    let L := supportClass.erase terminalSlot
    let U := L.biUnion fun t => ett.series.data.stored t.succ
    have hposition (a : Fin p) :
        (reversePosition a).val + a.val + 1 = p := by
      simp [reversePosition, Fin.rev]
      omega
    have htraceGamma (a : Fin p) :
        trace.gamma a = gamma (reversePosition a) := rfl
    have htraceDelta (a : Fin p) :
        trace.delta a = delta (reversePosition a) := rfl
    have hslotIdentity (a : Fin p) :
        trace.slot a = indices (reversePosition a) := rfl
    have slot_mem (a : Fin p) : trace.slot a ∈ L := by
      change trace.slot a ∈ supportClass.erase terminalSlot
      rw [← trace.enumerates]
      exact Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩
    have gamma_mem_U (a : Fin p) : trace.gamma a ∈ U := by
      apply Finset.mem_biUnion.mpr
      refine ⟨trace.slot a, slot_mem a, ?_⟩
      rw [hslotIdentity a, hstored (reversePosition a),
        ← htraceGamma a]
      simp
    have delta_mem_U (a : Fin p) : trace.delta a ∈ U := by
      apply Finset.mem_biUnion.mpr
      refine ⟨trace.slot a, slot_mem a, ?_⟩
      rw [hslotIdentity a, hstored (reversePosition a),
        ← htraceDelta a]
      simp
    have initial_terminal_present (c : Fin k) (hc : c ∈ U) :
        c ∈ PresentColors G mu0 terminalSupport := by
      have hn : c ∉ MissingColors G mu0 terminalSupport := by
        intro hm
        have hi : c ∈ MissingColors G mu0 terminalSupport ∩ U :=
          Finset.mem_inter.mpr ⟨hm, hc⟩
        change c ∈ MissingColors G mu0 terminalSupport ∩
          ((ExtensionBaseSupportClass ett terminalSupport hterminalSupport
            terminalSupport).erase terminalSlot).biUnion
              (fun t => ett.series.data.stored t.succ) at hi
        rw [hterminalNoMissing] at hi
        simpa using hi
      simpa [MissingColors] using hn
    have initial_gamma_present (a : Fin p) :
        trace.gamma a ∈ PresentColors G mu0 u := by
      rw [htraceGamma]
      exact hinitialGammaPresent a.rev
    have initial_survivor (s : Fin ett.rounds) (gammaS deltaS : Fin k)
        (hs : s ∈ L)
        (hgs : ett.series.data.gamma s.succ = some gammaS)
        (hds : ett.series.data.delta s.succ = some deltaS) :
        ETTStrongInterchangeable ett s terminalSupport mu0 gammaS deltaS := by
      exact hinitialSI s gammaS deltaS hs hgs hds
    have next_delta_eq_gamma (a c : Fin p)
        (hca : c.val = a.val + 1) : trace.delta c = trace.gamma a := by
      have ha := hposition a
      have hc := hposition c
      let q : Fin p := c.rev
      have hpc : reversePosition c = q.castSucc := Fin.ext rfl
      have hpa : reversePosition a = q.succ := by
        apply Fin.ext
        simp [q]
        omega
      rw [htraceDelta c, htraceGamma a, hpc, hpa]
      exact (hchain q).symm
    have single_step (t : Fin ett.rounds) (phi : PartialEdgeColoring E k)
        (alpha beta : Fin k)
        (hproperPhi : IsProperEdgeColoring G phi)
        (hSI : ETTStrongInterchangeable ett t terminalSupport phi alpha beta)
        (hbetaMissing : beta ∈ MissingColors G phi u)
        (halphaPresent : alpha ∈ PresentColors G phi u)
        (hterminalAlphaPresent : alpha ∈ PresentColors G phi terminalSupport)
        (hterminalBetaPresent : beta ∈ PresentColors G phi terminalSupport) :
        TwoColorNontrivialPathComponent G phi alpha beta (Sum.inl u) ∧
          (∀ w : V,
            w ∈ TreeSequenceVertexSet
                (ett.series.data.tree t.succ.castSucc) →
            Sum.inl w ∈ TwoColorComponent G phi alpha beta (Sum.inl u) →
            w = terminalSupport) ∧
          (Sum.inl terminalSupport ∈
              TwoColorComponent G phi alpha beta (Sum.inl u) →
            ¬ Set.Subsingleton
              ((TwoColorIncidenceGraph G phi alpha beta).neighborSet
                (Sum.inl terminalSupport))) := by
      let H := TwoColorIncidenceGraph G phi alpha beta
      let C := TwoColorComponent G phi alpha beta (Sum.inl u)
      have hne : alpha ≠ beta := hSI.1
      have hbetaNotPresent : beta ∉ PresentColors G phi u :=
        (Finset.mem_sdiff.mp hbetaMissing).2
      obtain ⟨eAlpha, heAlphaIncident, heAlphaColor⟩ := by
        simpa only [PresentColors, Finset.mem_filter, Finset.mem_univ,
          true_and] using halphaPresent
      have heAlphaAdj : H.Adj (Sum.inl u) (Sum.inr eAlpha) := by
        simpa [H, TwoColorIncidenceGraph] using
          And.intro heAlphaIncident (Or.inl heAlphaColor)
      have heAlphaComponent : Sum.inr eAlpha ∈ C := by
        change H.connectedComponentMk (Sum.inr eAlpha) =
          H.connectedComponentMk (Sum.inl u)
        exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
          heAlphaAdj).symm
      have huComponent : Sum.inl u ∈ C := by rfl
      have huSubsingleton : Set.Subsingleton (H.neighborSet (Sum.inl u)) := by
        intro x hx y hy
        cases x with
        | inl x =>
            simp [SimpleGraph.mem_neighborSet, H, TwoColorIncidenceGraph] at hx
        | inr e =>
            cases y with
            | inl y =>
                simp [SimpleGraph.mem_neighborSet, H, TwoColorIncidenceGraph] at hy
            | inr f =>
                have hxData : Incident G u e ∧
                    (phi e = some alpha ∨ phi e = some beta) := by
                  simpa [SimpleGraph.mem_neighborSet, H, TwoColorIncidenceGraph]
                    using hx
                have hyData : Incident G u f ∧
                    (phi f = some alpha ∨ phi f = some beta) := by
                  simpa [SimpleGraph.mem_neighborSet, H, TwoColorIncidenceGraph]
                    using hy
                have heColor : phi e = some alpha := by
                  rcases hxData.2 with he | he
                  · exact he
                  · exact False.elim (hbetaNotPresent (by
                      simp only [PresentColors, Finset.mem_filter,
                        Finset.mem_univ, true_and]
                      exact ⟨e, hxData.1, he⟩))
                have hfColor : phi f = some alpha := by
                  rcases hyData.2 with hf | hf
                  · exact hf
                  · exact False.elim (hbetaNotPresent (by
                      simp only [PresentColors, Finset.mem_filter,
                        Finset.mem_univ, true_and]
                      exact ⟨f, hyData.1, hf⟩))
                congr 1
                by_contra hef
                exact (hproperPhi hef ⟨u, hxData.1, hyData.1⟩ heColor) hfColor
      have hpath : TwoColorPathComponent G phi alpha beta (Sum.inl u) := by
        refine ⟨hne, Sum.inl u, huComponent, ?_⟩
        simpa [H] using huSubsingleton
      have hnontrivial : TwoColorNontrivialPathComponent G phi alpha beta
          (Sum.inl u) := ⟨hpath, eAlpha, heAlphaComponent⟩
      refine ⟨hnontrivial, ?_, ?_⟩
      · intro w hwTree hwComponent
        by_contra hwne
        obtain ⟨hcycle, -, -⟩ :=
          hSI.2.2.2.choose_spec.2.2.2 w hwTree hwne
        have huInW : Sum.inl u ∈
            TwoColorComponent G phi alpha beta (Sum.inl w) := by
          change H.connectedComponentMk (Sum.inl u) =
            H.connectedComponentMk (Sum.inl w)
          change H.connectedComponentMk (Sum.inl w) =
            H.connectedComponentMk (Sum.inl u) at hwComponent
          exact hwComponent.symm
        have hpathW : TwoColorPathComponent G phi alpha beta (Sum.inl w) := by
          refine ⟨hne, Sum.inl u, huInW, ?_⟩
          simpa [H] using huSubsingleton
        exact (TwoColorPathComponentNotCycle G phi alpha beta (Sum.inl w)
          hpathW) hcycle
      · intro _ hsub
        obtain ⟨eAlphaN, heAlphaNIncident, heAlphaNColor⟩ := by
          simpa only [PresentColors, Finset.mem_filter, Finset.mem_univ,
            true_and] using hterminalAlphaPresent
        obtain ⟨eBetaN, heBetaNIncident, heBetaNColor⟩ := by
          simpa only [PresentColors, Finset.mem_filter, Finset.mem_univ,
            true_and] using hterminalBetaPresent
        have hedgeNe : eAlphaN ≠ eBetaN := by
          intro heq
          subst eBetaN
          exact hne (Option.some.inj (heAlphaNColor.symm.trans heBetaNColor))
        have hAlphaNeighbor : Sum.inr eAlphaN ∈
            H.neighborSet (Sum.inl terminalSupport) := by
          simpa [SimpleGraph.mem_neighborSet, H, TwoColorIncidenceGraph] using
            And.intro heAlphaNIncident (Or.inl heAlphaNColor)
        have hBetaNeighbor : Sum.inr eBetaN ∈
            H.neighborSet (Sum.inl terminalSupport) := by
          simpa [SimpleGraph.mem_neighborSet, H, TwoColorIncidenceGraph] using
            And.intro heBetaNIncident (Or.inr heBetaNColor)
        exact hedgeNe (Sum.inr.inj (hsub hAlphaNeighbor hBetaNeighbor))
    have swap_preserves_one {phi : PartialEdgeColoring E k}
        {alpha beta : Fin k} {z : Sum V E}
        (h : IsOneEdgeUncolored phi e0) :
        IsOneEdgeUncolored (TwoColorComponentSwap G phi alpha beta z) e0 := by
      constructor
      · simp [TwoColorComponentSwap, h.1]
      · intro e he0
        obtain ⟨c, hc⟩ := h.2 e he0
        by_cases heK : Sum.inr e ∈ TwoColorComponent G phi alpha beta z
        · by_cases heAlpha : phi e = some alpha
          · exact ⟨beta, by simp [TwoColorComponentSwap, heK, heAlpha]⟩
          · by_cases heBeta : phi e = some beta
            · exact ⟨alpha, by
                simp [TwoColorComponentSwap, heK, heAlpha, heBeta]⟩
            · exact ⟨c, by
                simpa [TwoColorComponentSwap, heK, heAlpha, heBeta] using hc⟩
        · exact ⟨c, by simpa [TwoColorComponentSwap, heK] using hc⟩
    have swap_present_other {phi : PartialEdgeColoring E k} {v : V}
        {alpha beta c : Fin k} {z : Sum V E}
        (hc : c ∈ PresentColors G phi v) (hca : c ≠ alpha)
        (hcb : c ≠ beta) :
        c ∈ PresentColors G (TwoColorComponentSwap G phi alpha beta z) v := by
      simp only [PresentColors, Finset.mem_filter, Finset.mem_univ,
        true_and] at hc ⊢
      rcases hc with ⟨e, hev, hec⟩
      refine ⟨e, hev, ?_⟩
      by_cases heK : Sum.inr e ∈ TwoColorComponent G phi alpha beta z
      · simp [TwoColorComponentSwap, heK, hec, hca, hcb]
      · simpa [TwoColorComponentSwap, heK] using hec
    have root_swap_exchange {phi : PartialEdgeColoring E k} {v : V}
        {alpha beta : Fin k}
        (hne : alpha ≠ beta)
        (hbeta : beta ∈ MissingColors G phi v)
        (halpha : alpha ∈ PresentColors G phi v) :
        alpha ∈ MissingColors G
            (TwoColorComponentSwap G phi alpha beta (Sum.inl v)) v ∧
          beta ∈ PresentColors G
            (TwoColorComponentSwap G phi alpha beta (Sum.inl v)) v := by
      have hbetaNotPresent : beta ∉ PresentColors G phi v := by
        simpa [MissingColors] using hbeta
      obtain ⟨eAlpha, heAlphaIncident, heAlphaColor⟩ := by
        simpa only [PresentColors, Finset.mem_filter, Finset.mem_univ,
          true_and] using halpha
      have heAlphaComponent : Sum.inr eAlpha ∈
          TwoColorComponent G phi alpha beta (Sum.inl v) := by
        let H := TwoColorIncidenceGraph G phi alpha beta
        have hadj : H.Adj (Sum.inl v) (Sum.inr eAlpha) := by
          simpa [H, TwoColorIncidenceGraph] using
            And.intro heAlphaIncident (Or.inl heAlphaColor)
        change H.connectedComponentMk (Sum.inr eAlpha) =
          H.connectedComponentMk (Sum.inl v)
        exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
          hadj).symm
      constructor
      · unfold MissingColors
        rw [Finset.mem_sdiff]
        refine ⟨Finset.mem_univ _, ?_⟩
        intro hpresent
        simp only [PresentColors, Finset.mem_filter, Finset.mem_univ,
          true_and] at hpresent
        rcases hpresent with ⟨e, hev, heColor⟩
        by_cases heK :
            Sum.inr e ∈ TwoColorComponent G phi alpha beta (Sum.inl v)
        · have heBeta : phi e = some beta := by
            unfold TwoColorComponentSwap at heColor
            rw [if_pos heK] at heColor
            by_cases heAlpha : phi e = some alpha
            · rw [if_pos heAlpha] at heColor
              exact False.elim (hne (Option.some.inj heColor).symm)
            · by_cases heBeta : phi e = some beta
              · exact heBeta
              · rw [if_neg heAlpha, if_neg heBeta] at heColor
                exact False.elim (heAlpha heColor)
          apply hbetaNotPresent
          simp only [PresentColors, Finset.mem_filter, Finset.mem_univ,
            true_and]
          exact ⟨e, hev, heBeta⟩
        · have heOldAlpha : phi e = some alpha := by
            simpa [TwoColorComponentSwap, heK] using heColor
          have heAdj : (TwoColorIncidenceGraph G phi alpha beta).Adj
              (Sum.inl v) (Sum.inr e) := by
            simpa [TwoColorIncidenceGraph] using
              And.intro hev (Or.inl heOldAlpha)
          apply heK
          change (TwoColorIncidenceGraph G phi alpha beta).connectedComponentMk
              (Sum.inr e) =
            (TwoColorIncidenceGraph G phi alpha beta).connectedComponentMk
              (Sum.inl v)
          exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
            heAdj).symm
      · simp only [PresentColors, Finset.mem_filter, Finset.mem_univ,
          true_and]
        exact ⟨eAlpha, heAlphaIncident, by
          simp [TwoColorComponentSwap, heAlphaComponent, heAlphaColor, hne]⟩
    have swap_preserves_present {phi : PartialEdgeColoring E k} {v : V}
        {alpha beta : Fin k} {z : Sum V E}
        (hne : alpha ≠ beta)
        (halpha : alpha ∈ PresentColors G phi v)
        (hbeta : beta ∈ PresentColors G phi v) :
        ∀ c : Fin k, c ∈ PresentColors G phi v →
          c ∈ PresentColors G
            (TwoColorComponentSwap G phi alpha beta z) v := by
      intro c hc
      by_cases hca : c = alpha
      · subst c
        by_cases hvK : Sum.inl v ∈ TwoColorComponent G phi alpha beta z
        · obtain ⟨e, hev, heColor⟩ := by
            simpa only [PresentColors, Finset.mem_filter, Finset.mem_univ,
              true_and] using hbeta
          have heK : Sum.inr e ∈ TwoColorComponent G phi alpha beta z := by
            let H := TwoColorIncidenceGraph G phi alpha beta
            have hadj : H.Adj (Sum.inl v) (Sum.inr e) := by
              simpa [H, TwoColorIncidenceGraph] using
                And.intro hev (Or.inr heColor)
            change H.connectedComponentMk (Sum.inr e) =
              H.connectedComponentMk z
            change H.connectedComponentMk (Sum.inl v) =
              H.connectedComponentMk z at hvK
            exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
              hadj).symm.trans hvK
          simp only [PresentColors, Finset.mem_filter, Finset.mem_univ,
            true_and]
          exact ⟨e, hev, by
            simp [TwoColorComponentSwap, heK, heColor, hne]⟩
        · obtain ⟨e, hev, heColor⟩ := by
            simpa only [PresentColors, Finset.mem_filter, Finset.mem_univ,
              true_and] using halpha
          have heK : Sum.inr e ∉ TwoColorComponent G phi alpha beta z := by
            intro heK
            apply hvK
            let H := TwoColorIncidenceGraph G phi alpha beta
            have hadj : H.Adj (Sum.inl v) (Sum.inr e) := by
              simpa [H, TwoColorIncidenceGraph] using
                And.intro hev (Or.inl heColor)
            change H.connectedComponentMk (Sum.inr e) =
              H.connectedComponentMk z at heK
            change H.connectedComponentMk (Sum.inl v) =
              H.connectedComponentMk z
            exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
              hadj).trans heK
          simp only [PresentColors, Finset.mem_filter, Finset.mem_univ,
            true_and]
          exact ⟨e, hev, by
            simpa [TwoColorComponentSwap, heK] using heColor⟩
      · by_cases hcb : c = beta
        · subst c
          by_cases hvK : Sum.inl v ∈ TwoColorComponent G phi alpha beta z
          · obtain ⟨e, hev, heColor⟩ := by
              simpa only [PresentColors, Finset.mem_filter, Finset.mem_univ,
                true_and] using halpha
            have heK : Sum.inr e ∈ TwoColorComponent G phi alpha beta z := by
              let H := TwoColorIncidenceGraph G phi alpha beta
              have hadj : H.Adj (Sum.inl v) (Sum.inr e) := by
                simpa [H, TwoColorIncidenceGraph] using
                  And.intro hev (Or.inl heColor)
              change H.connectedComponentMk (Sum.inr e) =
                H.connectedComponentMk z
              change H.connectedComponentMk (Sum.inl v) =
                H.connectedComponentMk z at hvK
              exact
                (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
                  hadj).symm.trans hvK
            simp only [PresentColors, Finset.mem_filter, Finset.mem_univ,
              true_and]
            exact ⟨e, hev, by
              simp [TwoColorComponentSwap, heK, heColor, hne]⟩
          · obtain ⟨e, hev, heColor⟩ := by
              simpa only [PresentColors, Finset.mem_filter, Finset.mem_univ,
                true_and] using hbeta
            have heK : Sum.inr e ∉ TwoColorComponent G phi alpha beta z := by
              intro heK
              apply hvK
              let H := TwoColorIncidenceGraph G phi alpha beta
              have hadj : H.Adj (Sum.inl v) (Sum.inr e) := by
                simpa [H, TwoColorIncidenceGraph] using
                  And.intro hev (Or.inr heColor)
              change H.connectedComponentMk (Sum.inr e) =
                H.connectedComponentMk z at heK
              change H.connectedComponentMk (Sum.inl v) =
                H.connectedComponentMk z
              exact
                (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
                  hadj).trans heK
            simp only [PresentColors, Finset.mem_filter, Finset.mem_univ,
              true_and]
            exact ⟨e, hev, by
              simpa [TwoColorComponentSwap, heK] using heColor⟩
        · exact swap_present_other hc hca hcb
    have invariant : ∀ n : Fin (trace.steps + 1),
        (IsProperEdgeColoring G (trace.coloring n) ∧
          IsOneEdgeUncolored (trace.coloring n) e0) ∧
        (∀ c : Fin k, c ∈ U →
          c ∈ PresentColors G (trace.coloring n) terminalSupport) ∧
        (∀ a : Fin trace.steps, n.val ≤ a.val →
          trace.gamma a ∈ PresentColors G (trace.coloring n) u) ∧
        (∀ a : Fin trace.steps, a.val = n.val →
          trace.delta a ∈ MissingColors G (trace.coloring n) u) ∧
        ∀ (s : Fin ett.rounds) (gammaS deltaS : Fin k),
          s ∈ L →
          (∀ a : Fin trace.steps, a.val < n.val → trace.slot a ≠ s) →
          ett.series.data.chosenVertex s.succ = some terminalSupport →
          ett.series.data.gamma s.succ = some gammaS →
          ett.series.data.delta s.succ = some deltaS →
          ETTStrongInterchangeable ett s terminalSupport
            (trace.coloring n) gammaS deltaS := by
      intro n
      induction n using Fin.induction with
      | zero =>
          rw [trace.initialColoring]
          refine ⟨⟨hproper, hone⟩, initial_terminal_present,
            (fun a _ => initial_gamma_present a), ?_, ?_⟩
          · intro a ha
            let q : Fin p := a.rev
            have hpos : reversePosition a = q.castSucc := Fin.ext rfl
            have hlast : Fin.last p = q.succ := by
              apply Fin.ext
              have hpa := hposition a
              change p = a.rev.val + 1
              change a.rev.val + a.val + 1 = p at hpa
              simp at ha
              omega
            rw [htraceDelta a, hpos, ← hchain q, ← hlast]
            exact hterminalGammaMissing
          · intro s gammaS deltaS hs _ _ hgs hds
            exact initial_survivor s gammaS deltaS hs hgs hds
      | succ a ih =>
          rcases ih with ⟨hgood, hterminal, hfuture, hnext, hsurvivor⟩
          have hgammaPresent : trace.gamma a ∈
              PresentColors G (trace.coloring a.castSucc) u :=
            hfuture a (by rfl)
          have hdeltaMissing : trace.delta a ∈
              MissingColors G (trace.coloring a.castSucc) u :=
            hnext a rfl
          have hcurrentSI : ETTStrongInterchangeable ett (trace.slot a)
              terminalSupport (trace.coloring a.castSucc)
              (trace.gamma a) (trace.delta a) := by
            apply hsurvivor (trace.slot a) (trace.gamma a) (trace.delta a)
                (slot_mem a)
            · intro c hc hca
              have hdesc := trace.strictlyDescending c a hc
              rw [hca] at hdesc
              exact (Nat.lt_irrefl _ hdesc)
            · exact trace.chosenSupport a
            · exact trace.gammaField a
            · exact trace.deltaField a
          have hterminalGamma : trace.gamma a ∈
              PresentColors G (trace.coloring a.castSucc) terminalSupport :=
            hterminal (trace.gamma a) (gamma_mem_U a)
          have hterminalDelta : trace.delta a ∈
              PresentColors G (trace.coloring a.castSucc) terminalSupport :=
            hterminal (trace.delta a) (delta_mem_U a)
          have hstep := single_step (trace.slot a)
            (trace.coloring a.castSucc) (trace.gamma a) (trace.delta a)
            hgood.1 hcurrentSI hdeltaMissing hgammaPresent hterminalGamma
            hterminalDelta
          have hproperNext :
              IsProperEdgeColoring G (trace.coloring a.succ) := by
            rw [trace.transition a]
            exact TwoColorComponentSwapProper G (trace.coloring a.castSucc)
              (trace.gamma a) (trace.delta a) (trace_colors_ne a) hgood.1
              (Sum.inl u)
          have honeNext : IsOneEdgeUncolored (trace.coloring a.succ) e0 := by
            rw [trace.transition a]
            exact swap_preserves_one hgood.2
          have hexchange := root_swap_exchange (trace_colors_ne a)
            hdeltaMissing hgammaPresent
          rw [← trace.transition a] at hexchange
          refine ⟨⟨hproperNext, honeNext⟩, ?_, ?_, ?_, ?_⟩
          · intro c hc
            have hpresent := swap_preserves_present (z := Sum.inl u)
              (trace_colors_ne a) hterminalGamma hterminalDelta c
              (hterminal c hc)
            rw [← trace.transition a] at hpresent
            exact hpresent
          · intro c hac
            have hac' : a.val < c.val := by
              change a.val + 1 ≤ c.val at hac
              omega
            have hne := surviving_gamma_ne a c hac'
            have hpresent := swap_present_other (z := Sum.inl u)
              (hfuture c (Nat.le_of_lt hac')) hne.1 hne.2
            rw [← trace.transition a] at hpresent
            exact hpresent
          · intro c hca
            rw [next_delta_eq_gamma a c (by simpa using hca)]
            exact hexchange.1
          · intro s gammaS deltaS hs hnot hsupportS hgammaS hdeltaS
            have hsOld : ETTStrongInterchangeable ett s terminalSupport
                (trace.coloring a.castSucc) gammaS deltaS := by
              apply hsurvivor s gammaS deltaS hs
              · intro c hc
                apply hnot c
                change c.val < a.val at hc
                change c.val < a.val + 1
                omega
              · exact hsupportS
              · exact hgammaS
              · exact hdeltaS
            have hsImage : s ∈ Finset.univ.image trace.slot := by
              rw [trace.enumerates]
              exact hs
            rcases Finset.mem_image.mp hsImage with ⟨c, -, hc⟩
            have hac : a.val < c.val := by
              by_contra hle
              have hca : c.val < a.succ.val := by
                simp
                omega
              exact hnot c hca hc
            have hslt : s.val < (trace.slot a).val := by
              have hdesc := trace.strictlyDescending a c hac
              simpa [hc] using hdesc
            have hpreserved := StrongInterchangeabilityKempePreserved ett s
              (trace.slot a) terminalSupport terminalSupport gammaS deltaS
              (trace.gamma a) (trace.delta a) (trace.coloring a.castSucc)
              (Sum.inl u) hgood.1 hgood.2 hgammaS hdeltaS
              (trace.gammaField a) (trace.deltaField a) (Or.inr hslt)
              (by intro hneSupport; exact (hneSupport rfl).elim) hstep.1
              hcurrentSI hsOld
            rw [trace.transition a]
            exact hpreserved.2.2
    unfold ExtensionBaseAlgorithmCInvariant
    refine ⟨?_, ?_, ?_⟩
    · intro a
      exact (invariant a).1
    · intro a
      rcases invariant a.castSucc with
        ⟨hgood, hterminal, hfuture, hnext, hsurvivor⟩
      have hmissing := hnext a rfl
      have hpresent := hfuture a (by rfl)
      have hterminalGamma := hterminal (trace.gamma a) (gamma_mem_U a)
      have hterminalDelta := hterminal (trace.delta a) (delta_mem_U a)
      have hsi : ETTStrongInterchangeable ett (trace.slot a) terminalSupport
          (trace.coloring a.castSucc) (trace.gamma a) (trace.delta a) := by
        apply hsurvivor (trace.slot a) (trace.gamma a) (trace.delta a)
            (slot_mem a)
        · intro c hc hca
          have hdesc := trace.strictlyDescending c a hc
          rw [hca] at hdesc
          exact (Nat.lt_irrefl _ hdesc)
        · exact trace.chosenSupport a
        · exact trace.gammaField a
        · exact trace.deltaField a
      have hstep := single_step (trace.slot a)
        (trace.coloring a.castSucc) (trace.gamma a) (trace.delta a)
        hgood.1 hsi hmissing hpresent hterminalGamma hterminalDelta
      refine ⟨?_, hmissing, hstep.1, hstep.2.1, hstep.2.2, ?_⟩
      · exact hTjInitial (trace.slot a) (slot_mem a)
      · intro s gammaS deltaS hs hnot hsupportS hgammaS hdeltaS
        have hnextInvariant := invariant a.succ
        exact hnextInvariant.2.2.2.2 s gammaS deltaS hs (by
          intro c hc
          apply hnot c
          change c.val < a.val + 1 at hc
          omega) hsupportS hgammaS hdeltaS
    · intro s gammaS deltaS hs hnot _ _ _
      have hsImage : s ∈ Finset.univ.image trace.slot := by
        rw [trace.enumerates]
        exact hs
      rcases Finset.mem_image.mp hsImage with ⟨a, -, ha⟩
      exact False.elim (hnot a ha)
