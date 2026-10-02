import Tablet.ExtensionBaseClaimMissingColors
import Tablet.ExtensionBaseActiveIndices
import Tablet.ExtensionBaseRestorationIndices
import Tablet.ExtensionBaseRestorationInvariant
import Tablet.ExtensionBaseRestorationTrace
import Tablet.ExtensionBaseSupportClass
import Tablet.ExtensionBaseSupportClassColors
import Tablet.MissingColors
import Tablet.PresentColors
import Tablet.TreeSequenceInitialSegment
import Tablet.TreeSequenceVertexSet
import Tablet.TwoColorComponent
import Tablet.TwoColorComponentSwap
import Tablet.TwoColorIncidenceGraph
import Tablet.TwoColorNontrivialPathComponent

-- [TABLET NODE: ExtensionBaseClaim43MissingColors]
theorem ExtensionBaseClaim43MissingColors {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    {input : PartialEdgeColoring E k} {T : TreeSequence G e0}
    {generating : PartialEdgeColoring E k}
    (ett : ExtendedTashkinovTree G k e0 input T generating)
    (terminalSupport : V)
    (hterminalSupport : terminalSupport ∈ TreeSequenceVertexSet T)
    (jSlot q : Fin ett.rounds) (sigmaN phiJ : PartialEdgeColoring E k)
    (hterminalJ : terminalSupport ∈ TreeSequenceVertexSet
      (ett.series.data.tree jSlot.succ.castSucc))
    (trace : ExtensionBaseRestorationTrace ett terminalSupport
      hterminalSupport sigmaN)
    (hinvariant : ExtensionBaseRestorationInvariant ett terminalSupport
      hterminalSupport jSlot q sigmaN trace)
    (hunsupported : ∀ v : V,
      v ∈ TreeSequenceVertexSet
          (ett.series.data.tree jSlot.succ.castSucc) →
      (∀ r : Fin ett.rounds,
        r ∈ ExtensionBaseActiveIndices ett terminalSupport hterminalSupport →
        ett.series.data.chosenVertex r.succ ≠ some v) →
      MissingColors G sigmaN v = MissingColors G phiJ v)
    (hclassPrepared : ∀ w : V,
      w ∈ TreeSequenceVertexSet
          (ett.series.data.tree jSlot.succ.castSucc) →
      w ≠ terminalSupport →
      (∃ t : Fin ett.rounds,
        t ∈ ExtensionBaseRestorationIndices ett terminalSupport
            hterminalSupport ∧
        ett.series.data.chosenVertex t.succ = some w) →
      ∃ p : ℕ, ∃ indices : Fin (p + 1) → Fin ett.rounds,
        ∃ gamma delta : Fin (p + 1) → Fin k,
          (∀ a b, a.val < b.val →
            (indices a).val < (indices b).val) ∧
          (∀ r : Fin ett.rounds,
            r ∈ ExtensionBaseSupportClass ett terminalSupport
                hterminalSupport w ↔
              ∃ a : Fin (p + 1), indices a = r) ∧
          (∀ a, ett.series.data.gamma (indices a).succ = some (gamma a)) ∧
          (∀ a, ett.series.data.delta (indices a).succ = some (delta a)) ∧
          (∀ a : Fin p, gamma a.succ = delta a.castSucc) ∧
          Function.Injective (Fin.cons (gamma 0) delta) ∧
          MissingColors G phiJ w =
            (MissingColors G sigmaN w \ {delta (Fin.last p)}) ∪
              {gamma 0}) :
    (∀ v : V,
      v ∈ (TreeSequenceVertexSet
          (ett.series.data.tree jSlot.succ.castSucc)).erase
            terminalSupport →
      MissingColors G (trace.coloring (Fin.last trace.steps)) v =
        MissingColors G phiJ v) ∧
    MissingColors G (trace.coloring (Fin.last trace.steps))
        terminalSupport =
      MissingColors G sigmaN terminalSupport := by
-- BODY
  classical
  have vertexTransfer : ∀ (A B : TreeSequence G e0),
      TreeSequenceInitialSegment A B → ∀ v,
        v ∈ TreeSequenceVertexSet A → v ∈ TreeSequenceVertexSet B := by
    intro A B hAB v hv
    rcases hAB with ⟨hlen, hvertex, hedge⟩
    unfold TreeSequenceVertexSet at hv ⊢
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hv ⊢
    obtain ⟨i, rfl⟩ := hv
    exact ⟨Fin.castLE (Nat.succ_le_succ hlen) i, hvertex i⟩
  have edgeOutside : ∀ (a : Fin trace.steps) (v : V),
      v ∈ TreeSequenceVertexSet
          (ett.series.data.tree jSlot.succ.castSucc) →
      v ≠ trace.support a → ∀ f : E, Incident G v f →
      Sum.inr f ∉ TwoColorComponent G (trace.coloring a.castSucc)
        (trace.gamma a) (trace.delta a) (Sum.inl (trace.support a)) := by
    intro a v hv hvSupport f hvf hf
    have stepInvariant := hinvariant.2.1 a
    rcases stepInvariant.2.2 with
      ⟨segment, supportInTree, deltaMissing, pathComponent,
        exactIntersection, remaining⟩
    have hvCurrent : v ∈ TreeSequenceVertexSet
        (ett.series.data.tree (trace.slot a).succ.castSucc) :=
      vertexTransfer _ _ segment v hv
    have endpoint : Sum.inl v ∈ TwoColorComponent G
        (trace.coloring a.castSucc) (trace.gamma a) (trace.delta a)
        (Sum.inl (trace.support a)) := by
      let H := TwoColorIncidenceGraph G (trace.coloring a.castSucc)
        (trace.gamma a) (trace.delta a)
      have edgeSupport : Sum.inr f ∈ H.support := by
        apply SimpleGraph.mem_support_of_reachable
          (G := H) (u := Sum.inr f) (v := Sum.inl (trace.support a))
        · simp
        · exact SimpleGraph.ConnectedComponent.eq.mp hf
      obtain ⟨x, hx⟩ := H.mem_support.mp edgeSupport
      have active : trace.coloring a.castSucc f = some (trace.gamma a) ∨
          trace.coloring a.castSucc f = some (trace.delta a) := by
        cases x with
        | inl x => exact hx.2
        | inr x => simpa [H, TwoColorIncidenceGraph] using hx
      have adjacent : H.Adj (Sum.inl v) (Sum.inr f) := by
        simp [H, TwoColorIncidenceGraph, hvf, active]
      change H.connectedComponentMk (Sum.inl v) =
        H.connectedComponentMk (Sum.inl (trace.support a))
      exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
        adjacent).trans hf
    exact hvSupport ((exactIntersection v hvCurrent).mp endpoint)
  have offSupportStep : ∀ (a : Fin trace.steps) (v : V),
      v ∈ TreeSequenceVertexSet
          (ett.series.data.tree jSlot.succ.castSucc) →
      v ≠ trace.support a →
      MissingColors G (trace.coloring a.succ) v =
        MissingColors G (trace.coloring a.castSucc) v := by
    intro a v hv hvSupport
    have fixed : ∀ f : E, Incident G v f →
        trace.coloring a.succ f = trace.coloring a.castSucc f := by
      intro f hvf
      rw [trace.transition]
      simp [TwoColorComponentSwap, edgeOutside a v hv hvSupport f hvf]
    apply Finset.ext
    intro c
    simp only [MissingColors, Finset.mem_sdiff, Finset.mem_univ, true_and]
    simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and,
      not_exists, not_and]
    constructor
    · intro hc f hvf hcolor
      apply hc f hvf
      rw [fixed f hvf]
      exact hcolor
    · intro hc f hvf hcolor
      apply hc f hvf
      rw [← fixed f hvf]
      exact hcolor
  have rootExchange : ∀ (a : Fin trace.steps),
      MissingColors G (trace.coloring a.succ) (trace.support a) =
        (MissingColors G (trace.coloring a.castSucc) (trace.support a) \
          {trace.delta a}) ∪ {trace.gamma a} := by
    intro a
    have stepInvariant := hinvariant.2.1 a
    rcases stepInvariant.2.2 with
      ⟨segment, supportInTree, deltaMissing, pathComponent,
        exactIntersection, remaining⟩
    let phi := trace.coloring a.castSucc
    let gamma := trace.gamma a
    let delta := trace.delta a
    let v := trace.support a
    have deltaNotPresent : delta ∉ PresentColors G phi v := by
      simpa [MissingColors] using deltaMissing
    have gammaPresent : gamma ∈ PresentColors G phi v := by
      obtain ⟨f, hf⟩ := pathComponent.2
      let H := TwoColorIncidenceGraph G phi gamma delta
      have rootSupport : Sum.inl v ∈ H.support := by
        apply SimpleGraph.mem_support_of_reachable
          (G := H) (u := Sum.inl v) (v := Sum.inr f)
        · simp
        · exact SimpleGraph.ConnectedComponent.eq.mp hf.symm
      obtain ⟨x, hx⟩ := H.mem_support.mp rootSupport
      cases x with
      | inl x => simp [H, TwoColorIncidenceGraph] at hx
      | inr e =>
          have hxe : Incident G v e ∧
              (phi e = some gamma ∨ phi e = some delta) := by
            simpa [H, TwoColorIncidenceGraph] using hx
          rcases hxe with ⟨hve, hcolor | hcolor⟩
          · simp only [PresentColors, Finset.mem_filter, Finset.mem_univ,
              true_and]
            exact ⟨e, hve, hcolor⟩
          · exact (deltaNotPresent (by
              simp only [PresentColors, Finset.mem_filter, Finset.mem_univ,
                true_and]
              exact ⟨e, hve, hcolor⟩)).elim
    have gammaNeDelta : gamma ≠ delta := by
      intro h
      apply deltaNotPresent
      simpa [h] using gammaPresent
    have edgeMember : ∀ e : E, Incident G v e →
        (phi e = some gamma ∨ phi e = some delta) →
        Sum.inr e ∈ TwoColorComponent G phi gamma delta (Sum.inl v) := by
      intro e hve hcolor
      apply SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
      simp [TwoColorComponent, TwoColorIncidenceGraph, hve, hcolor]
    have presentStep : ∀ c : Fin k,
        c ∈ PresentColors G
            (TwoColorComponentSwap G phi gamma delta (Sum.inl v)) v ↔
          c = delta ∨ (c ≠ gamma ∧ c ∈ PresentColors G phi v) := by
      intro c
      simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨e, hve, hec⟩
        by_cases hcomp : Sum.inr e ∈
            TwoColorComponent G phi gamma delta (Sum.inl v)
        · by_cases hgamma : phi e = some gamma
          · have value := hec
            simp [TwoColorComponentSwap, hcomp, hgamma, gammaNeDelta] at value
            exact Or.inl value.symm
          · by_cases hdelta : phi e = some delta
            · exact (deltaNotPresent (by
                simp only [PresentColors, Finset.mem_filter, Finset.mem_univ,
                  true_and]
                exact ⟨e, hve, hdelta⟩)).elim
            · right
              have value := hec
              simp [TwoColorComponentSwap, hcomp, hgamma, hdelta] at value
              refine ⟨?_, ⟨e, hve, value⟩⟩
              intro hc
              apply hgamma
              simpa [hc] using value
        · right
          have value := hec
          simp [TwoColorComponentSwap, hcomp] at value
          refine ⟨?_, ⟨e, hve, value⟩⟩
          intro hc
          apply hcomp
          apply edgeMember e hve
          left
          simpa [hc] using value
      · rintro (rfl | ⟨hcGamma, ⟨e, hve, hec⟩⟩)
        · obtain ⟨e, hve, heGamma⟩ := by
            simpa [PresentColors] using gammaPresent
          refine ⟨e, hve, ?_⟩
          simp [TwoColorComponentSwap,
            edgeMember e hve (Or.inl heGamma), heGamma, gammaNeDelta]
        · refine ⟨e, hve, ?_⟩
          by_cases hgamma : phi e = some gamma
          · exact False.elim (hcGamma (Option.some.inj (hec.symm.trans hgamma)))
          · by_cases hdelta : phi e = some delta
            · exact False.elim (deltaNotPresent (by
                simp only [PresentColors, Finset.mem_filter, Finset.mem_univ,
                  true_and]
                exact ⟨e, hve, hdelta⟩))
            · simp [TwoColorComponentSwap, hgamma, hdelta]
              exact hec
    have exchange : MissingColors G
        (TwoColorComponentSwap G phi gamma delta (Sum.inl v)) v =
          (MissingColors G phi v \ {delta}) ∪ {gamma} := by
      apply Finset.ext
      intro c
      simp only [MissingColors, Finset.mem_sdiff, Finset.mem_union,
        Finset.mem_singleton, Finset.mem_univ, true_and]
      rw [presentStep]
      by_cases hcDelta : c = delta <;>
        by_cases hcGamma : c = gamma <;>
          simp [hcDelta, hcGamma, gammaNeDelta, gammaNeDelta.symm]
    rw [trace.transition]
    exact exchange
  have preservedWhenOff : ∀ (v : V),
      v ∈ TreeSequenceVertexSet
          (ett.series.data.tree jSlot.succ.castSucc) →
      (∀ a : Fin trace.steps, trace.support a ≠ v) →
      MissingColors G (trace.coloring (Fin.last trace.steps)) v =
        MissingColors G sigmaN v := by
    intro v hv hOff
    have inductionClaim : ∀ n : ℕ, (hn : n ≤ trace.steps) →
        MissingColors G
            (trace.coloring ⟨n, Nat.lt_succ_of_le hn⟩) v =
          MissingColors G sigmaN v := by
      intro n hn
      induction n with
      | zero =>
          simpa using (congrArg (fun phi => MissingColors G phi v)
            trace.initialColoring)
      | succ n ih =>
          let a : Fin trace.steps := ⟨n, Nat.lt_of_succ_le hn⟩
          have hprevious := ih (Nat.le_of_succ_le hn)
          have hstep := offSupportStep a v hv (Ne.symm (hOff a))
          have hcast : a.castSucc =
              (⟨n, Nat.lt_succ_of_le (Nat.le_of_succ_le hn)⟩ :
                Fin (trace.steps + 1)) := by
            apply Fin.ext
            rfl
          have hsucc : a.succ =
              (⟨n + 1, Nat.lt_succ_of_le hn⟩ :
                Fin (trace.steps + 1)) := by
            apply Fin.ext
            rfl
          rw [hcast, hsucc] at hstep
          exact hstep.trans hprevious
    simpa [Fin.last] using inductionClaim trace.steps le_rfl
  have terminalOff : ∀ a : Fin trace.steps,
      trace.support a ≠ terminalSupport := by
    intro a hsupport
    have hrestoration := (hinvariant.2.1 a).1
    have hparts := Finset.mem_sdiff.mp hrestoration
    apply hparts.2
    unfold ExtensionBaseSupportClass
    simp only [Finset.mem_filter]
    refine ⟨hparts.1, ?_⟩
    simpa [hsupport] using trace.chosenVertex a
  constructor
  · intro v hvErase
    have hv := (Finset.mem_erase.mp hvErase).2
    have hvTerminal : v ≠ terminalSupport := by
      exact (Finset.mem_erase.mp hvErase).1
    by_cases hsupported : ∃ r : Fin ett.rounds,
        r ∈ ExtensionBaseActiveIndices ett terminalSupport hterminalSupport ∧
          ett.series.data.chosenVertex r.succ = some v
    · obtain ⟨r, hrActive, hrVertex⟩ := hsupported
      have hrRestoration : r ∈ ExtensionBaseRestorationIndices ett
          terminalSupport hterminalSupport := by
        unfold ExtensionBaseRestorationIndices
        apply Finset.mem_sdiff.mpr
        refine ⟨hrActive, ?_⟩
        unfold ExtensionBaseSupportClass
        simp only [Finset.mem_filter, hrActive, true_and]
        intro hterminalVertex
        have : v = terminalSupport := by
          apply Option.some.inj
          exact hrVertex.symm.trans hterminalVertex
        exact hvTerminal this
      obtain ⟨p, indices, gamma, delta, hincreasing, hclass,
          hgamma, hdelta, hchain, hinjective, hprepared⟩ :=
        hclassPrepared v hv hvTerminal ⟨r, hrRestoration, hrVertex⟩
      sorry
    · have hOff : ∀ a : Fin trace.steps, trace.support a ≠ v := by
        intro a hsupport
        have hrestoration := (hinvariant.2.1 a).1
        have hactive := (Finset.mem_sdiff.mp hrestoration).1
        apply hsupported
        refine ⟨trace.slot a, hactive, ?_⟩
        simpa [hsupport] using trace.chosenVertex a
      exact (preservedWhenOff v hv hOff).trans
        (hunsupported v hv (by
          intro r hrActive hrVertex
          exact hsupported ⟨r, hrActive, hrVertex⟩))
  · exact preservedWhenOff terminalSupport hterminalJ terminalOff
