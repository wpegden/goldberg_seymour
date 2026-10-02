import Tablet.ExtensionBaseAlgorithmB
import Tablet.ExtensionBaseAlgorithmBInvariant
import Tablet.ExtensionBaseAlgorithmBTrace
import Tablet.ExtensionBaseCaseOneIndices
import Tablet.ExtensionBaseSupportClass
import Tablet.ETTFirstAppearanceIndex
import Tablet.IsProperEdgeColoring
import Tablet.LooplessMultigraph
import Tablet.MissingColors
import Tablet.StableColoringBeforeVertex
import Tablet.TashkinovAugmentation
import Tablet.TashkinovAugmentationSequence
import Tablet.TashkinovClosure
import Tablet.TreeMissingColors
import Tablet.TreeSequence
import Tablet.TreeSequenceInitialSegment
import Tablet.TreeSequencePrefix
import Tablet.TreeVerticesBefore
import Tablet.TwoColorComponent
import Tablet.TwoColorComponentSwap
import Tablet.TwoColorIncidenceDegreeAtMostTwo
import Tablet.TwoColorIncidenceGraph
import Tablet.TwoColorNontrivialPathComponent

-- [TABLET NODE: ExtensionBaseClaim44]
theorem ExtensionBaseClaim44 {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    {input : PartialEdgeColoring E k} {T : TreeSequence G e0}
    {generating : PartialEdgeColoring E k}
    (ett : ExtendedTashkinovTree G k e0 input T generating)
    (terminalSupport : V)
    (hterminalSupport : terminalSupport ∈ TreeSequenceVertexSet T)
    (jSlot : Fin ett.rounds)
    (hjSlot : jSlot.val + 1 =
      ETTFirstAppearanceIndex ett terminalSupport hterminalSupport)
    (rho1 : PartialEdgeColoring E k)
    (C : Finset (Fin k)) (u : V)
    (TjPrime seed : TreeSequence G e0)
    (terminalPosition : Fin
      ((ett.series.data.tree jSlot.succ.castSucc).length + 1))
    (hterminalAt :
      (ett.series.data.tree jSlot.succ.castSucc).vertex terminalPosition =
        terminalSupport)
    (hterminalPositionPositive : 1 ≤ terminalPosition.val)
    (hseed : seed = TreeSequencePrefix
      (ett.series.data.tree jSlot.succ.castSucc) terminalPosition.val
      hterminalPositionPositive
      (Nat.le_of_lt_succ terminalPosition.isLt))
    (huPrime : u ∈ TreeSequenceVertexSet TjPrime)
    (p : ℕ) (indices : Fin (p + 1) → Fin ett.rounds)
    (gamma delta : Fin (p + 1) → Fin k) (b : Fin (p + 1))
    (hincreasing : ∀ a c, a.val < c.val →
      (indices a).val < (indices c).val)
    (hclass : ∀ r : Fin ett.rounds,
      r ∈ ExtensionBaseSupportClass ett terminalSupport
          hterminalSupport terminalSupport ↔
        ∃ a : Fin (p + 1), indices a = r)
    (trace : ExtensionBaseAlgorithmBTrace ett terminalSupport rho1 u
      p indices b)
    (hinvariant : ExtensionBaseAlgorithmBInvariant ett terminalSupport
      jSlot rho1 u p indices b trace)
    (hbaseStable : StableColoringBeforeVertex
      (ett.series.data.tree jSlot.succ.castSucc) terminalSupport
      (by
        rw [← hterminalAt]
        simp [TreeSequenceVertexSet])
      C (ett.series.data.coloring jSlot.castSucc) rho1)
    (huOutsideTj : u ∉ TreeSequenceVertexSet
      (ett.series.data.tree jSlot.succ.castSucc))
    (hclosure : TashkinovClosure rho1 seed TjPrime)
    (hprefixAvoids :
      (TreeVerticesBefore TjPrime u huPrime).biUnion
          (fun v => MissingColors G rho1 v) ∩
        ((ExtensionBaseCaseOneIndices ett p indices b).biUnion
          fun t => ett.series.data.stored t.succ) = ∅)
    (hselected : gamma b ∈ MissingColors G rho1 u)
    (hminimal : ∀ a : Fin (p + 1), a.val < b.val →
      gamma a ∉ MissingColors G rho1 u)
    (hgamma : ∀ a,
      ett.series.data.gamma (indices a).succ = some (gamma a))
    (hdelta : ∀ a,
      ett.series.data.delta (indices a).succ = some (delta a))
    (hchain : ∀ a : Fin p, gamma a.succ = delta a.castSucc)
    (hdistinct : Function.Injective (Fin.cons (gamma 0) delta))
    (hstored : ∀ a,
      ett.series.data.stored (indices a).succ = {gamma a, delta a}) :
    let rho2 := trace.coloring (Fin.last trace.steps)
    StableColoringBeforeVertex
        (ett.series.data.tree jSlot.succ.castSucc) terminalSupport
        (by
          rw [← hterminalAt]
          simp [TreeSequenceVertexSet])
        C (ett.series.data.coloring jSlot.castSucc) rho2 ∧
      ((∀ v : V,
        v ∈ TreeSequenceVertexSet
              (ett.series.data.tree jSlot.succ.castSucc) ∪
            TreeVerticesBefore TjPrime u huPrime →
        MissingColors G rho2 v = MissingColors G rho1 v) ∧
       ∀ f : E,
        ((∃ a : Fin (ett.series.data.tree
              jSlot.succ.castSucc).length,
            (ett.series.data.tree jSlot.succ.castSucc).edge a = f) ∨
          ∃ (a : Fin TjPrime.length) (z : Fin (TjPrime.length + 1)),
            TjPrime.vertex z = u ∧ a.val < z.val ∧
              TjPrime.edge a = f) →
        rho2 f = rho1 f) ∧
      gamma 0 ∈ MissingColors G rho2 u := by
-- BODY
  classical
  dsimp only
  have hindicesInjective : Function.Injective indices := by
    intro a c hac
    apply Fin.ext
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hstrict := hincreasing a c hlt
      rw [hac] at hstrict
      exact (Nat.lt_irrefl _ hstrict)
    · have hstrict := hincreasing c a hgt
      rw [hac] at hstrict
      exact (Nat.lt_irrefl _ hstrict)
  have hslotInjective : Function.Injective trace.slot := by
    intro a c hac
    apply Fin.ext
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hstrict := trace.strictlyDescending a c hlt
      rw [hac] at hstrict
      exact (Nat.lt_irrefl _ hstrict)
    · have hstrict := trace.strictlyDescending c a hgt
      rw [hac] at hstrict
      exact (Nat.lt_irrefl _ hstrict)
  have hsteps : trace.steps = b.val := by
    have hleft : (Finset.univ.image trace.slot).card = trace.steps := by
      rw [Finset.card_image_of_injective Finset.univ hslotInjective]
      simp
    have hright :
        (ExtensionBaseCaseOneIndices ett p indices b).card = b.val := by
      unfold ExtensionBaseCaseOneIndices
      rw [Finset.card_image_of_injective _ hindicesInjective]
      let s := Finset.univ.filter fun a : Fin (p + 1) => a.val < b.val
      change s.card = b.val
      calc
        s.card = Fintype.card s := (Fintype.card_coe s).symm
        _ = Fintype.card (Fin b.val) := Fintype.card_congr {
          toFun := fun a => ⟨a.val.val, (Finset.mem_filter.mp a.property).2⟩
          invFun := fun a =>
            ⟨⟨a.val, by omega⟩, Finset.mem_filter.mpr ⟨by simp, a.isLt⟩⟩
          left_inv := by intro a; apply Subtype.ext; apply Fin.ext; rfl
          right_inv := by intro a; apply Fin.ext; rfl
        }
        _ = b.val := Fintype.card_fin b.val
    rw [← hleft, trace.enumerates, hright]
  have hpositionInjective : Function.Injective trace.position := by
    intro a c hac
    apply hslotInjective
    rw [trace.slotIdentity, trace.slotIdentity, hac]
  have hpositionSurjectiveBelow : ∀ q : Fin (p + 1), q.val < b.val →
      ∃ a : Fin trace.steps, trace.position a = q := by
    intro q hqb
    have hmem : indices q ∈ Finset.univ.image trace.slot := by
      rw [trace.enumerates]
      unfold ExtensionBaseCaseOneIndices
      exact Finset.mem_image.mpr ⟨q, by simpa using hqb, rfl⟩
    obtain ⟨a, -, ha⟩ := Finset.mem_image.mp hmem
    refine ⟨a, hindicesInjective ?_⟩
    rw [← trace.slotIdentity a]
    exact ha
  let positionBelow : Fin b.val → Fin b.val := fun a =>
    ⟨(trace.position (Fin.cast hsteps.symm a)).val,
      trace.positionBefore (Fin.cast hsteps.symm a)⟩
  have hpositionBelowAnti : StrictAnti positionBelow := by
    intro a c hac
    have hdesc := trace.strictlyDescending
      (Fin.cast hsteps.symm a) (Fin.cast hsteps.symm c) (by simpa using hac)
    rw [trace.slotIdentity, trace.slotIdentity] at hdesc
    by_contra hnot
    have hle : (trace.position (Fin.cast hsteps.symm a)).val ≤
        (trace.position (Fin.cast hsteps.symm c)).val := Nat.le_of_not_gt hnot
    rcases lt_or_eq_of_le hle with hlt | heq
    · have hinc := hincreasing _ _ hlt
      omega
    · have hposEq : trace.position (Fin.cast hsteps.symm a) =
          trace.position (Fin.cast hsteps.symm c) := Fin.ext heq
      exact (ne_of_lt hac) (by
        have hcastEq := hpositionInjective hposEq
        apply Fin.ext
        simpa using congrArg (fun x => x.val) hcastEq)
  have hpositionBelowRev (a : Fin b.val) : positionBelow a = a.rev := by
    have hmono : StrictMono (fun q : Fin b.val => (positionBelow q).rev) := by
      intro q r hqr
      exact Fin.rev_lt_rev.mpr (hpositionBelowAnti hqr)
    have hid := congrFun hmono.eq_id a
    exact Fin.rev_eq_iff.mp hid
  have hpositionReverse : ∀ a : Fin trace.steps,
      (trace.position a).val + a.val + 1 = b.val := by
    intro a
    have hrev := hpositionBelowRev (Fin.cast hsteps a)
    have hval := congrArg Fin.val hrev
    simp [positionBelow] at hval
    omega
  have htraceGamma (a : Fin trace.steps) :
      trace.gamma a = gamma (trace.position a) := by
    apply Option.some.inj
    exact (trace.gammaField a).symm.trans (by
      rw [trace.slotIdentity]
      exact hgamma (trace.position a))
  have htraceDelta (a : Fin trace.steps) :
      trace.delta a = delta (trace.position a) := by
    apply Option.some.inj
    exact (trace.deltaField a).symm.trans (by
      rw [trace.slotIdentity]
      exact hdelta (trace.position a))
  have hgammaDeltaNe (q : Fin (p + 1)) : gamma q ≠ delta q := by
    have hconsGamma :
        (Fin.cons (gamma 0) delta : Fin (p + 2) → Fin k) q.castSucc =
          gamma q := by
      refine Fin.cases ?_ (fun r => ?_) q
      · simp
      · rw [show (Fin.succ r).castSucc = r.castSucc.succ by
          apply Fin.ext
          rfl]
        rw [Fin.cons_succ]
        exact (hchain r).symm
    have hconsDelta :
        (Fin.cons (gamma 0) delta : Fin (p + 2) → Fin k) q.succ =
          delta q := by simp
    intro heq
    have hindexEq : q.castSucc = q.succ :=
      hdistinct (hconsGamma.trans (heq.trans hconsDelta.symm))
    exact (ne_of_lt Fin.castSucc_lt_succ) hindexEq
  have htraceColorsNe (a : Fin trace.steps) :
      trace.gamma a ≠ trace.delta a := by
    rw [htraceGamma, htraceDelta]
    exact hgammaDeltaNe (trace.position a)
  have htraceProper (n : Fin (trace.steps + 1)) :
      IsProperEdgeColoring G (trace.coloring n) :=
    (hinvariant.1 n).1
  have hstepData (a : Fin trace.steps) := hinvariant.2.1 a
  have hvertexOfComponentEdge (a : Fin trace.steps) {v : V} {f : E}
      (hfComponent : Sum.inr f ∈
        TwoColorComponent G (trace.coloring a.castSucc)
          (trace.gamma a) (trace.delta a) (Sum.inl u))
      (hvf : Incident G v f)
      (hfColor : trace.coloring a.castSucc f = some (trace.gamma a) ∨
        trace.coloring a.castSucc f = some (trace.delta a)) :
      Sum.inl v ∈ TwoColorComponent G (trace.coloring a.castSucc)
        (trace.gamma a) (trace.delta a) (Sum.inl u) := by
    change (TwoColorIncidenceGraph G (trace.coloring a.castSucc)
        (trace.gamma a) (trace.delta a)).connectedComponentMk
          (Sum.inr f) =
      (TwoColorIncidenceGraph G (trace.coloring a.castSucc)
        (trace.gamma a) (trace.delta a)).connectedComponentMk (Sum.inl u)
      at hfComponent
    change (TwoColorIncidenceGraph G (trace.coloring a.castSucc)
        (trace.gamma a) (trace.delta a)).connectedComponentMk
          (Sum.inl v) =
      (TwoColorIncidenceGraph G (trace.coloring a.castSucc)
        (trace.gamma a) (trace.delta a)).connectedComponentMk (Sum.inl u)
    have hadj : (TwoColorIncidenceGraph G (trace.coloring a.castSucc)
        (trace.gamma a) (trace.delta a)).Adj (Sum.inl v) (Sum.inr f) := by
      simpa [TwoColorIncidenceGraph] using And.intro hvf hfColor
    exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
      hadj).trans hfComponent
  have hcomponentEdgeOfVertex (a : Fin trace.steps) {v : V} {f : E}
      (hvComponent : Sum.inl v ∈
        TwoColorComponent G (trace.coloring a.castSucc)
          (trace.gamma a) (trace.delta a) (Sum.inl u))
      (hvf : Incident G v f)
      (hfColor : trace.coloring a.castSucc f = some (trace.gamma a) ∨
        trace.coloring a.castSucc f = some (trace.delta a)) :
      Sum.inr f ∈ TwoColorComponent G (trace.coloring a.castSucc)
        (trace.gamma a) (trace.delta a) (Sum.inl u) := by
    change (TwoColorIncidenceGraph G (trace.coloring a.castSucc)
        (trace.gamma a) (trace.delta a)).connectedComponentMk
          (Sum.inl v) =
      (TwoColorIncidenceGraph G (trace.coloring a.castSucc)
        (trace.gamma a) (trace.delta a)).connectedComponentMk (Sum.inl u)
      at hvComponent
    change (TwoColorIncidenceGraph G (trace.coloring a.castSucc)
        (trace.gamma a) (trace.delta a)).connectedComponentMk
          (Sum.inr f) =
      (TwoColorIncidenceGraph G (trace.coloring a.castSucc)
        (trace.gamma a) (trace.delta a)).connectedComponentMk (Sum.inl u)
    have hadj : (TwoColorIncidenceGraph G (trace.coloring a.castSucc)
        (trace.gamma a) (trace.delta a)).Adj (Sum.inr f) (Sum.inl v) := by
      simpa [TwoColorIncidenceGraph] using And.intro hvf hfColor
    exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
      hadj).trans hvComponent
  have hfixedOutsideComponent (a : Fin trace.steps) {v : V}
      (hvOutside : Sum.inl v ∉
        TwoColorComponent G (trace.coloring a.castSucc)
          (trace.gamma a) (trace.delta a) (Sum.inl u))
      {f : E} (hvf : Incident G v f) :
      trace.coloring a.succ f = trace.coloring a.castSucc f := by
    rw [trace.transition]
    by_cases hfComponent : Sum.inr f ∈
        TwoColorComponent G (trace.coloring a.castSucc)
          (trace.gamma a) (trace.delta a) (Sum.inl u)
    · by_cases hfg : trace.coloring a.castSucc f = some (trace.gamma a)
      · exact False.elim (hvOutside
          (hvertexOfComponentEdge a hfComponent hvf (Or.inl hfg)))
      · by_cases hfd : trace.coloring a.castSucc f = some (trace.delta a)
        · exact False.elim (hvOutside
            (hvertexOfComponentEdge a hfComponent hvf (Or.inr hfd)))
        · simp [TwoColorComponentSwap, hfComponent, hfg, hfd]
    · simp [TwoColorComponentSwap, hfComponent]
  have hmissingFixedOutside (a : Fin trace.steps) {v : V}
      (hvOutside : Sum.inl v ∉
        TwoColorComponent G (trace.coloring a.castSucc)
          (trace.gamma a) (trace.delta a) (Sum.inl u)) :
      MissingColors G (trace.coloring a.succ) v =
        MissingColors G (trace.coloring a.castSucc) v := by
    apply Finset.ext
    intro c
    simp only [MissingColors, Finset.mem_sdiff, Finset.mem_univ, true_and,
      PresentColors, Finset.mem_filter]
    constructor
    · intro hc hold
      rcases hold with ⟨f, hvf, hfc⟩
      exact hc ⟨f, hvf, (hfixedOutsideComponent a hvOutside hvf).trans hfc⟩
    · intro hc hnew
      rcases hnew with ⟨f, hvf, hfc⟩
      exact hc ⟨f, hvf, (hfixedOutsideComponent a hvOutside hvf).symm.trans hfc⟩
  have hunaffectedValue (a : Fin trace.steps) (f : E) (c : Fin k)
      (hcg : c ≠ trace.gamma a) (hcd : c ≠ trace.delta a) :
      trace.coloring a.succ f = some c ↔
        trace.coloring a.castSucc f = some c := by
    rw [trace.transition]
    by_cases hfComponent : Sum.inr f ∈
        TwoColorComponent G (trace.coloring a.castSucc)
          (trace.gamma a) (trace.delta a) (Sum.inl u)
    · by_cases hfg : trace.coloring a.castSucc f = some (trace.gamma a)
      · simp [TwoColorComponentSwap, hfComponent, hfg, hcg.symm, hcd.symm]
      · by_cases hfd : trace.coloring a.castSucc f = some (trace.delta a)
        · simp [TwoColorComponentSwap, hfComponent, hfd,
            (htraceColorsNe a).symm, hcg.symm, hcd.symm]
        · simp [TwoColorComponentSwap, hfComponent, hfg, hfd]
    · simp [TwoColorComponentSwap, hfComponent]
  have hmissingFixedInternal (a : Fin trace.steps) (v : V)
      (hvComponent : Sum.inl v ∈
        TwoColorComponent G (trace.coloring a.castSucc)
          (trace.gamma a) (trace.delta a) (Sum.inl u))
      (hgammaPresent : trace.gamma a ∈
        PresentColors G (trace.coloring a.castSucc) v)
      (hdeltaPresent : trace.delta a ∈
        PresentColors G (trace.coloring a.castSucc) v) :
      MissingColors G (trace.coloring a.succ) v =
        MissingColors G (trace.coloring a.castSucc) v := by
    have hgammaNew : trace.gamma a ∈
        PresentColors G (trace.coloring a.succ) v := by
      simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
        at hdeltaPresent ⊢
      obtain ⟨f, hvf, hfdelta⟩ := hdeltaPresent
      have hfComponent := hcomponentEdgeOfVertex a hvComponent hvf (Or.inr hfdelta)
      refine ⟨f, hvf, ?_⟩
      rw [trace.transition]
      simp [TwoColorComponentSwap, hfComponent, hfdelta,
        (htraceColorsNe a).symm]
    have hdeltaNew : trace.delta a ∈
        PresentColors G (trace.coloring a.succ) v := by
      simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
        at hgammaPresent ⊢
      obtain ⟨f, hvf, hfgamma⟩ := hgammaPresent
      have hfComponent := hcomponentEdgeOfVertex a hvComponent hvf (Or.inl hfgamma)
      refine ⟨f, hvf, ?_⟩
      rw [trace.transition]
      simp [TwoColorComponentSwap, hfComponent, hfgamma]
    apply Finset.ext
    intro c
    by_cases hcg : c = trace.gamma a
    · subst c
      have hold : trace.gamma a ∉
          MissingColors G (trace.coloring a.castSucc) v := by
        simpa [MissingColors] using hgammaPresent
      have hnew : trace.gamma a ∉
          MissingColors G (trace.coloring a.succ) v := by
        simpa [MissingColors] using hgammaNew
      simp [hold, hnew]
    · by_cases hcd : c = trace.delta a
      · subst c
        have hold : trace.delta a ∉
            MissingColors G (trace.coloring a.castSucc) v := by
          simpa [MissingColors] using hdeltaPresent
        have hnew : trace.delta a ∉
            MissingColors G (trace.coloring a.succ) v := by
          simpa [MissingColors] using hdeltaNew
        simp [hold, hnew]
      · simp only [MissingColors, Finset.mem_sdiff, Finset.mem_univ,
          true_and, PresentColors, Finset.mem_filter]
        constructor
        · intro hc hold
          rcases hold with ⟨f, hvf, hfc⟩
          exact hc ⟨f, hvf, (hunaffectedValue a f c hcg hcd).mpr hfc⟩
        · intro hc hnew
          rcases hnew with ⟨f, hvf, hfc⟩
          exact hc ⟨f, hvf, (hunaffectedValue a f c hcg hcd).mp hfc⟩
  have hswapMakesGammaMissing (a : Fin trace.steps) :
      trace.gamma a ∈ MissingColors G (trace.coloring a.succ) u := by
    have hdeltaMissing := hstepData a |>.2.1
    have huComponent : Sum.inl u ∈
        TwoColorComponent G (trace.coloring a.castSucc)
          (trace.gamma a) (trace.delta a) (Sum.inl u) := rfl
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    intro hgammaNew
    simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
      at hgammaNew
    obtain ⟨f, huf, hfnew⟩ := hgammaNew
    by_cases hfComponent : Sum.inr f ∈
        TwoColorComponent G (trace.coloring a.castSucc)
          (trace.gamma a) (trace.delta a) (Sum.inl u)
    · have hfold : trace.coloring a.castSucc f = some (trace.delta a) := by
        by_cases hfg : trace.coloring a.castSucc f = some (trace.gamma a)
        · rw [trace.transition] at hfnew
          have : trace.delta a = trace.gamma a := by
            simpa [TwoColorComponentSwap, hfComponent, hfg] using hfnew
          exact False.elim ((htraceColorsNe a) this.symm)
        · by_cases hfd : trace.coloring a.castSucc f = some (trace.delta a)
          · exact hfd
          · rw [trace.transition] at hfnew
            have : trace.coloring a.castSucc f = some (trace.gamma a) := by
              simpa [TwoColorComponentSwap, hfComponent, hfg, hfd] using hfnew
            exact False.elim (hfg this)
      have hdeltaNotPresent : trace.delta a ∉
          PresentColors G (trace.coloring a.castSucc) u := by
        simpa [MissingColors] using hdeltaMissing
      exact hdeltaNotPresent (by
        simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨f, huf, hfold⟩)
    · have hfold : trace.coloring a.castSucc f = some (trace.gamma a) := by
        rw [trace.transition] at hfnew
        simpa [TwoColorComponentSwap, hfComponent] using hfnew
      exact hfComponent
        (hcomponentEdgeOfVertex a huComponent huf (Or.inl hfold))
  have hpresentOfNonSubsingleton (a : Fin trace.steps) (v : V)
      (hnontrivial : ¬ Set.Subsingleton
        ((TwoColorIncidenceGraph G (trace.coloring a.castSucc)
          (trace.gamma a) (trace.delta a)).neighborSet (Sum.inl v))) :
      trace.gamma a ∈ PresentColors G (trace.coloring a.castSucc) v ∧
        trace.delta a ∈ PresentColors G (trace.coloring a.castSucc) v := by
    have colorPresent (c d : Fin k) (hcd : c ≠ d)
        (hc : c = trace.gamma a ∧ d = trace.delta a ∨
          c = trace.delta a ∧ d = trace.gamma a) :
        c ∈ PresentColors G (trace.coloring a.castSucc) v := by
      by_contra hcMissing
      apply hnontrivial
      intro x hx y hy
      cases x with
      | inl w =>
          simp [SimpleGraph.mem_neighborSet, TwoColorIncidenceGraph] at hx
      | inr f =>
          cases y with
          | inl w =>
              simp [SimpleGraph.mem_neighborSet, TwoColorIncidenceGraph] at hy
          | inr g =>
              have hxf := hx
              have hyg := hy
              simp [SimpleGraph.mem_neighborSet, TwoColorIncidenceGraph] at hxf hyg
              rcases hxf with ⟨hvf, hfc⟩
              rcases hyg with ⟨hvg, hgc⟩
              have hnotC (e : E) (hve : Incident G v e) :
                  trace.coloring a.castSucc e ≠ some c := by
                intro hec
                apply hcMissing
                simp only [PresentColors, Finset.mem_filter, Finset.mem_univ,
                  true_and]
                exact ⟨e, hve, hec⟩
              have hfd : trace.coloring a.castSucc f = some d := by
                rcases hc with hc | hc
                · rcases hc with ⟨rfl, rfl⟩
                  exact hfc.resolve_left (hnotC f hvf)
                · rcases hc with ⟨rfl, rfl⟩
                  exact hfc.resolve_right (hnotC f hvf)
              have hgd : trace.coloring a.castSucc g = some d := by
                rcases hc with hc | hc
                · rcases hc with ⟨rfl, rfl⟩
                  exact hgc.resolve_left (hnotC g hvg)
                · rcases hc with ⟨rfl, rfl⟩
                  exact hgc.resolve_right (hnotC g hvg)
              by_cases hfg : f = g
              · subst g
                rfl
              · exact False.elim
                  ((htraceProper a.castSucc) hfg ⟨v, hvf, hvg⟩ hfd hgd)
    refine ⟨?_, ?_⟩
    · exact colorPresent (trace.gamma a) (trace.delta a)
        (htraceColorsNe a) (Or.inl ⟨rfl, rfl⟩)
    · exact colorPresent (trace.delta a) (trace.gamma a)
        (htraceColorsNe a).symm (Or.inr ⟨rfl, rfl⟩)
  have htraceStored (a : Fin trace.steps) :
      ett.series.data.stored (trace.slot a).succ =
        {trace.gamma a, trace.delta a} := by
    rw [trace.slotIdentity, hstored, htraceGamma, htraceDelta]
  have hslotProcessed (a : Fin trace.steps) :
      trace.slot a ∈ ExtensionBaseCaseOneIndices ett p indices b := by
    rw [← trace.enumerates]
    exact Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩
  have hvertexInitialSegment {A B : TreeSequence G e0}
      (hAB : TreeSequenceInitialSegment A B) {v : V}
      (hv : v ∈ TreeSequenceVertexSet A) :
      v ∈ TreeSequenceVertexSet B := by
    simp only [TreeSequenceVertexSet, Finset.mem_image] at hv ⊢
    obtain ⟨i, -, hi⟩ := hv
    obtain ⟨hlen, hvertices, -⟩ := hAB
    refine ⟨Fin.castLE (Nat.succ_le_succ hlen) i, Finset.mem_univ _, ?_⟩
    exact (hvertices i).trans hi
  have hbeforeMemberAndNe {A : TreeSequence G e0} {v w : V}
      (hv : v ∈ TreeSequenceVertexSet A)
      (hw : w ∈ TreeVerticesBefore A v hv) :
      w ∈ TreeSequenceVertexSet A ∧ w ≠ v := by
    unfold TreeVerticesBefore at hw
    obtain ⟨hwA, i, j, hiw, hjv, hij⟩ := Finset.mem_filter.mp hw
    refine ⟨hwA, ?_⟩
    intro hwv
    have hijEq : i = j := A.vertex_injective
      (hiw.trans (hwv.trans hjv.symm))
    omega
  have hprefixColorsNotMissing (a : Fin trace.steps) {v : V}
      (hv : v ∈ TreeVerticesBefore TjPrime u huPrime) :
      trace.gamma a ∉ MissingColors G rho1 v ∧
        trace.delta a ∉ MissingColors G rho1 v := by
    have exclude (c : Fin k) (hc : c ∈
        ett.series.data.stored (trace.slot a).succ) :
        c ∉ MissingColors G rho1 v := by
      intro hmissing
      have hleft : c ∈
          (TreeVerticesBefore TjPrime u huPrime).biUnion
            (fun w => MissingColors G rho1 w) :=
        Finset.mem_biUnion.mpr ⟨v, hv, hmissing⟩
      have hright : c ∈
          (ExtensionBaseCaseOneIndices ett p indices b).biUnion
            (fun t => ett.series.data.stored t.succ) :=
        Finset.mem_biUnion.mpr ⟨trace.slot a, hslotProcessed a, hc⟩
      have hinter := Finset.mem_inter.mpr ⟨hleft, hright⟩
      rw [hprefixAvoids] at hinter
      simpa using hinter
    rw [htraceStored] at exclude
    exact ⟨exclude (trace.gamma a) (by simp),
      exclude (trace.delta a) (by simp)⟩
  have hmissingPreserved : ∀ n : Fin (trace.steps + 1), ∀ v : V,
      v ∈ TreeSequenceVertexSet
            (ett.series.data.tree jSlot.succ.castSucc) ∪
          TreeVerticesBefore TjPrime u huPrime →
      MissingColors G (trace.coloring n) v = MissingColors G rho1 v := by
    intro n
    induction n using Fin.induction with
    | zero =>
        intro v hv
        rw [trace.initialColoring]
    | succ a ih =>
        intro v hv
        rcases Finset.mem_union.mp hv with hvTj | hvPrefix
        · by_cases hvTerminal : v = terminalSupport
          · subst v
            by_cases hvComponent : Sum.inl terminalSupport ∈
                TwoColorComponent G (trace.coloring a.castSucc)
                  (trace.gamma a) (trace.delta a) (Sum.inl u)
            · have hnontrivial := (hstepData a).2.2.2.2.1 hvComponent
              obtain ⟨hgammaPresent, hdeltaPresent⟩ :=
                hpresentOfNonSubsingleton a terminalSupport hnontrivial
              exact (hmissingFixedInternal a terminalSupport hvComponent
                hgammaPresent hdeltaPresent).trans
                  (ih terminalSupport (Finset.mem_union_left _ hvTj))
            · exact (hmissingFixedOutside a hvComponent).trans
                (ih terminalSupport (Finset.mem_union_left _ hvTj))
          · have hvOutside : Sum.inl v ∉
                TwoColorComponent G (trace.coloring a.castSucc)
                  (trace.gamma a) (trace.delta a) (Sum.inl u) := by
              intro hvComponent
              have hvSlot := hvertexInitialSegment (hstepData a).1 hvTj
              exact hvTerminal ((hstepData a).2.2.2.1 v hvSlot hvComponent)
            exact (hmissingFixedOutside a hvOutside).trans
              (ih v (Finset.mem_union_left _ hvTj))
        · by_cases hvComponent : Sum.inl v ∈
              TwoColorComponent G (trace.coloring a.castSucc)
                (trace.gamma a) (trace.delta a) (Sum.inl u)
          · obtain ⟨hgammaRho1, hdeltaRho1⟩ :=
              hprefixColorsNotMissing a hvPrefix
            have hcurrent := ih v (Finset.mem_union_right _ hvPrefix)
            have hgammaCurrent : trace.gamma a ∉
                MissingColors G (trace.coloring a.castSucc) v := by
              rw [hcurrent]
              exact hgammaRho1
            have hdeltaCurrent : trace.delta a ∉
                MissingColors G (trace.coloring a.castSucc) v := by
              rw [hcurrent]
              exact hdeltaRho1
            have hgammaPresent : trace.gamma a ∈
                PresentColors G (trace.coloring a.castSucc) v := by
              simpa [MissingColors] using hgammaCurrent
            have hdeltaPresent : trace.delta a ∈
                PresentColors G (trace.coloring a.castSucc) v := by
              simpa [MissingColors] using hdeltaCurrent
            exact (hmissingFixedInternal a v hvComponent hgammaPresent
              hdeltaPresent).trans hcurrent
          · exact (hmissingFixedOutside a hvComponent).trans
              (ih v (Finset.mem_union_right _ hvPrefix))
  have hbeforeEdgesPreserved : ∀ n : Fin (trace.steps + 1), ∀ f : E,
      (∃ w ∈ TreeVerticesBefore
          (ett.series.data.tree jSlot.succ.castSucc) terminalSupport
          (by
            rw [← hterminalAt]
            simp [TreeSequenceVertexSet]),
        Incident G w f) →
      trace.coloring n f = rho1 f := by
    intro n
    induction n using Fin.induction with
    | zero =>
        intro f hf
        rw [trace.initialColoring]
    | succ a ih =>
        intro f hf
        obtain ⟨w, hwBefore, hwf⟩ := hf
        have hwData := hbeforeMemberAndNe
          (v := terminalSupport)
          (by
            rw [← hterminalAt]
            simp [TreeSequenceVertexSet]) hwBefore
        have hwOutside : Sum.inl w ∉
            TwoColorComponent G (trace.coloring a.castSucc)
              (trace.gamma a) (trace.delta a) (Sum.inl u) := by
          intro hwComponent
          have hwSlot := hvertexInitialSegment (hstepData a).1 hwData.1
          exact hwData.2 ((hstepData a).2.2.2.1 w hwSlot hwComponent)
        exact (hfixedOutsideComponent a hwOutside hwf).trans
          (ih f ⟨w, hwBefore, hwf⟩)
  have hstableOutput : StableColoringBeforeVertex
      (ett.series.data.tree jSlot.succ.castSucc) terminalSupport
      (by
        rw [← hterminalAt]
        simp [TreeSequenceVertexSet])
      C (ett.series.data.coloring jSlot.castSucc)
        (trace.coloring (Fin.last trace.steps)) := by
    unfold StableColoringBeforeVertex at hbaseStable ⊢
    constructor
    · intro f hfIncident hfControlled
      exact (hbeforeEdgesPreserved (Fin.last trace.steps) f hfIncident).trans
        (hbaseStable.1 f hfIncident hfControlled)
    · intro w hwBefore
      have hwTj := (hbeforeMemberAndNe
        (v := terminalSupport)
        (by
          rw [← hterminalAt]
          simp [TreeSequenceVertexSet]) hwBefore).1
      exact (hmissingPreserved (Fin.last trace.steps) w
        (Finset.mem_union_left _ hwTj)).trans (hbaseStable.2 w hwBefore)
  have hstageEdgeFixedStep (a : Fin trace.steps)
      (q : Fin (ett.series.data.tree jSlot.succ.castSucc).length) :
      trace.coloring a.succ
          ((ett.series.data.tree jSlot.succ.castSucc).edge q) =
        trace.coloring a.castSucc
          ((ett.series.data.tree jSlot.succ.castSucc).edge q) := by
    let S := ett.series.data.tree jSlot.succ.castSucc
    change trace.coloring a.succ (S.edge q) =
      trace.coloring a.castSucc (S.edge q)
    obtain ⟨i, hi⟩ := S.attaches q
    let r : Fin (S.length + 1) := Fin.castLT i
      (Nat.lt_trans i.isLt (Nat.succ_lt_succ q.isLt))
    have hnewIncident : Incident G (S.vertex q.succ) (S.edge q) := by
      unfold Incident
      rw [hi]
      simp
    have holdIncident : Incident G (S.vertex r) (S.edge q) := by
      unfold Incident
      rw [hi]
      simp [r]
    have hverticesNe : S.vertex q.succ ≠ S.vertex r := by
      intro heq
      have hindexEq := S.vertex_injective heq
      have hvalEq := congrArg (fun x => x.val) hindexEq
      simp [r] at hvalEq
      omega
    have hnewS : S.vertex q.succ ∈ TreeSequenceVertexSet S := by
      simp [TreeSequenceVertexSet]
    have holdS : S.vertex r ∈ TreeSequenceVertexSet S := by
      simp [TreeSequenceVertexSet]
    have hnewSlot := hvertexInitialSegment (hstepData a).1 hnewS
    have holdSlot := hvertexInitialSegment (hstepData a).1 holdS
    rw [trace.transition]
    by_cases hfComponent : Sum.inr (S.edge q) ∈
        TwoColorComponent G (trace.coloring a.castSucc)
          (trace.gamma a) (trace.delta a) (Sum.inl u)
    · by_cases hfg : trace.coloring a.castSucc (S.edge q) =
          some (trace.gamma a)
      · have hnewComponent := hvertexOfComponentEdge a hfComponent
          hnewIncident (Or.inl hfg)
        have holdComponent := hvertexOfComponentEdge a hfComponent
          holdIncident (Or.inl hfg)
        have hnewTerminal := (hstepData a).2.2.2.1 _ hnewSlot hnewComponent
        have holdTerminal := (hstepData a).2.2.2.1 _ holdSlot holdComponent
        exact False.elim (hverticesNe (hnewTerminal.trans holdTerminal.symm))
      · by_cases hfd : trace.coloring a.castSucc (S.edge q) =
            some (trace.delta a)
        · have hnewComponent := hvertexOfComponentEdge a hfComponent
            hnewIncident (Or.inr hfd)
          have holdComponent := hvertexOfComponentEdge a hfComponent
            holdIncident (Or.inr hfd)
          have hnewTerminal := (hstepData a).2.2.2.1 _ hnewSlot hnewComponent
          have holdTerminal := (hstepData a).2.2.2.1 _ holdSlot holdComponent
          exact False.elim (hverticesNe (hnewTerminal.trans holdTerminal.symm))
        · simp [TwoColorComponentSwap, hfComponent, hfg, hfd]
    · simp [TwoColorComponentSwap, hfComponent]
  have hstageEdgesPreserved : ∀ n : Fin (trace.steps + 1),
      ∀ q : Fin (ett.series.data.tree jSlot.succ.castSucc).length,
      trace.coloring n
          ((ett.series.data.tree jSlot.succ.castSucc).edge q) =
        rho1 ((ett.series.data.tree jSlot.succ.castSucc).edge q) := by
    intro n
    induction n using Fin.induction with
    | zero =>
        intro q
        rw [trace.initialColoring]
    | succ a ih =>
        intro q
        exact (hstageEdgeFixedStep a q).trans (ih q)
  have hfinalGammaMissing : gamma 0 ∈
      MissingColors G (trace.coloring (Fin.last trace.steps)) u := by
    by_cases hzero : trace.steps = 0
    · have hbzero : b.val = 0 := by omega
      have hb : b = 0 := Fin.ext hbzero
      have hlastZero : (Fin.last trace.steps : Fin (trace.steps + 1)) = 0 := by
        apply Fin.ext
        simp [hzero]
      rw [hlastZero, trace.initialColoring, ← hb]
      exact hselected
    · have hpositive : 0 < trace.steps := Nat.pos_of_ne_zero hzero
      let a : Fin trace.steps := ⟨trace.steps - 1, by omega⟩
      have hpositionZero : trace.position a = 0 := by
        apply Fin.ext
        change (trace.position a).val = 0
        have hreverse := hpositionReverse a
        have haSucc : a.val + 1 = trace.steps := by
          simp [a]
          omega
        have hsum : (trace.position a).val + trace.steps = b.val := by
          omega
        have hbval : b.val = trace.steps := hsteps.symm
        apply Nat.add_right_cancel (m := trace.steps)
        simpa using hsum.trans hbval
      have hgammaA : trace.gamma a = gamma 0 := by
        rw [htraceGamma, hpositionZero]
      have hlast : a.succ = (Fin.last trace.steps : Fin (trace.steps + 1)) := by
        apply Fin.ext
        simp [a]
        omega
      rw [← hgammaA, ← hlast]
      exact hswapMakesGammaMissing a
  have hinitialSegmentTrans {A B D : TreeSequence G e0}
      (hAB : TreeSequenceInitialSegment A B)
      (hBD : TreeSequenceInitialSegment B D) :
      TreeSequenceInitialSegment A D := by
    obtain ⟨hlenAB, hverticesAB, hedgesAB⟩ := hAB
    obtain ⟨hlenBD, hverticesBD, hedgesBD⟩ := hBD
    refine ⟨hlenAB.trans hlenBD, ?_, ?_⟩
    · intro i
      rw [show Fin.castLE (Nat.succ_le_succ (hlenAB.trans hlenBD)) i =
          Fin.castLE (Nat.succ_le_succ hlenBD)
            (Fin.castLE (Nat.succ_le_succ hlenAB) i) by
        apply Fin.ext
        rfl]
      rw [hverticesBD, hverticesAB]
    · intro q
      rw [show Fin.castLE (hlenAB.trans hlenBD) q =
          Fin.castLE hlenBD (Fin.castLE hlenAB q) by
        apply Fin.ext
        rfl]
      rw [hedgesBD, hedgesAB]
  have hsequenceInitialSegment {A B : TreeSequence G e0}
      (hreach : TashkinovAugmentationSequence rho1 A B) :
      TreeSequenceInitialSegment A B := by
    unfold TashkinovAugmentationSequence at hreach
    induction hreach using Relation.ReflTransGen.head_induction_on with
    | refl =>
        refine ⟨Nat.le_refl _, ?_, ?_⟩
        · intro i
          rfl
        · intro q
          rfl
    | @head A D hstep htail ih =>
        exact hinitialSegmentTrans hstep.2.1 ih
  have haugmentationEdgeMissing {B : TreeSequence G e0}
      (hreach : TashkinovAugmentationSequence rho1 seed B) :
      ∀ a : Fin B.length, seed.length ≤ a.val →
        ∃ i : Fin (B.length + 1), i.val ≤ a.val ∧
          ∃ c : Fin k, rho1 (B.edge a) = some c ∧
            c ∈ MissingColors G rho1 (B.vertex i) := by
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
          obtain ⟨i, hi, c, hcol, hmiss⟩ :=
            hstep old (by simpa [old] using ha)
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
          rw [show B.edge last =
              B.edge (Fin.cast hlen.symm (Fin.last A.length)) by
            congr 1
            apply Fin.ext
            simpa [last] using hnew]
          rw [hcolor]
          rw [TreeMissingColors] at hmissing
          obtain ⟨w, hw, hwm⟩ := Finset.mem_biUnion.mp hmissing
          simp only [TreeSequenceVertexSet, Finset.mem_image] at hw
          obtain ⟨i, -, hwi⟩ := hw
          refine ⟨Fin.castLE (Nat.succ_le_succ hinit.1) i, ?_, cnew,
            rfl, ?_⟩
          · change i.val ≤ a.val
            omega
          · rw [hinit.2.1, hwi]
            exact hwm
  refine ⟨hstableOutput, ?_, hfinalGammaMissing⟩
  constructor
  · intro v hv
    exact hmissingPreserved (Fin.last trace.steps) v hv
  · intro f hf
    rcases hf with hfStage | hfPrefix
    · obtain ⟨q, hq⟩ := hfStage
      rw [← hq]
      exact hstageEdgesPreserved (Fin.last trace.steps) q
    · obtain ⟨q, z, hzu, hqz, hqf⟩ := hfPrefix
      subst f
      by_cases hqSeed : q.val < seed.length
      · have hsegment := hsequenceInitialSegment hclosure.1
        let qSeed : Fin seed.length := ⟨q.val, hqSeed⟩
        have hqCast : Fin.castLE hsegment.1 qSeed = q := by
          apply Fin.ext
          rfl
        have hinherited : TjPrime.edge q = seed.edge qSeed := by
          rw [← hqCast, hsegment.2.2]
        have hseedLength : seed.length = terminalPosition.val := by
          rw [hseed]
          rfl
        have hqStageLt : q.val <
            (ett.series.data.tree jSlot.succ.castSucc).length := by
          have hterminalLe : terminalPosition.val ≤
              (ett.series.data.tree jSlot.succ.castSucc).length :=
            Nat.le_of_lt_succ terminalPosition.isLt
          omega
        let qStage : Fin
            (ett.series.data.tree jSlot.succ.castSucc).length :=
          ⟨q.val, hqStageLt⟩
        subst seed
        have hedgeEq : TjPrime.edge q =
            (ett.series.data.tree jSlot.succ.castSucc).edge qStage :=
          hinherited.trans (by rfl)
        rw [hedgeEq]
        exact hstageEdgesPreserved (Fin.last trace.steps) qStage
      · have hqAfterSeed : seed.length ≤ q.val := Nat.le_of_not_gt hqSeed
        obtain ⟨i, hiq, c, hcolor, hmissing⟩ :=
          haugmentationEdgeMissing hclosure.1 q hqAfterSeed
        have hiBefore : TjPrime.vertex i ∈
            TreeVerticesBefore TjPrime u huPrime := by
          unfold TreeVerticesBefore
          apply Finset.mem_filter.mpr
          constructor
          · simp [TreeSequenceVertexSet]
          · exact ⟨i, z, rfl, hzu, lt_of_le_of_lt hiq hqz⟩
        have hcAvoids (a : Fin trace.steps) :
            c ≠ trace.gamma a ∧ c ≠ trace.delta a := by
          obtain ⟨hgammaNotMissing, hdeltaNotMissing⟩ :=
            hprefixColorsNotMissing a hiBefore
          constructor
          · intro hcg
            apply hgammaNotMissing
            rw [← hcg]
            exact hmissing
          · intro hcd
            apply hdeltaNotMissing
            rw [← hcd]
            exact hmissing
        have hcolorPreserved : ∀ n : Fin (trace.steps + 1),
            trace.coloring n (TjPrime.edge q) = some c := by
          intro n
          induction n using Fin.induction with
          | zero =>
              rw [trace.initialColoring]
              exact hcolor
          | succ a ih =>
              exact (hunaffectedValue a (TjPrime.edge q) c
                (hcAvoids a).1 (hcAvoids a).2).mpr ih
        exact (hcolorPreserved (Fin.last trace.steps)).trans hcolor.symm
