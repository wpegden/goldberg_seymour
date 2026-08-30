import Tablet.ExtendedTashkinovTree
import Tablet.ExtensionBaseRestorationInvariant
import Tablet.ExtensionBaseRestorationTrace
import Tablet.Incident
import Tablet.MissingColors
import Tablet.PresentColors
import Tablet.StableColoringBeforeVertex
import Tablet.TashkinovSeries
import Tablet.TashkinovSeriesStep
import Tablet.TreeSequence
import Tablet.TreeSequenceInitialSegment
import Tablet.TreeSequenceVertexSet
import Tablet.TreeVertexOrder
import Tablet.TreeVerticesBefore
import Tablet.TwoColorComponent
import Tablet.TwoColorComponentSwap
import Tablet.TwoColorIncidenceGraph

-- [TABLET NODE: ExtensionBaseClaim43Stability]
theorem ExtensionBaseClaim43Stability {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    {input : PartialEdgeColoring E k} {T : TreeSequence G e0}
    {generating : PartialEdgeColoring E k}
    (ett : ExtendedTashkinovTree G k e0 input T generating)
    (terminalSupport : V)
    (hterminalSupport : terminalSupport ∈ TreeSequenceVertexSet T)
    (jSlot q : Fin ett.rounds) (sigmaN phiJ : PartialEdgeColoring E k)
    (C : Finset (Fin k))
    (hterminalJ : terminalSupport ∈ TreeSequenceVertexSet
      (ett.series.data.tree jSlot.succ.castSucc))
    (trace : ExtensionBaseRestorationTrace ett terminalSupport
      hterminalSupport sigmaN)
    (hinvariant : ExtensionBaseRestorationInvariant ett terminalSupport
      hterminalSupport jSlot q sigmaN trace)
    (hsigmaStable : StableColoringBeforeVertex T terminalSupport
      hterminalSupport C phiJ sigmaN) :
    StableColoringBeforeVertex T terminalSupport hterminalSupport C phiJ
      (trace.coloring (Fin.last trace.steps)) := by
-- BODY
  classical
  letI : DecidableEq V := Classical.decEq V
  have segmentTrans : ∀ A B D : TreeSequence G e0,
      TreeSequenceInitialSegment A B → TreeSequenceInitialSegment B D →
      TreeSequenceInitialSegment A D := by
    intro A B D hab hbd
    rcases hab with ⟨hlab, vab, eab⟩
    rcases hbd with ⟨hlbd, vbd, ebd⟩
    refine ⟨le_trans hlab hlbd, ?_, ?_⟩
    · intro i
      calc
        D.vertex (Fin.castLE (Nat.succ_le_succ (le_trans hlab hlbd)) i) =
            B.vertex (Fin.castLE (Nat.succ_le_succ hlab) i) := by
              simpa using vbd (Fin.castLE (Nat.succ_le_succ hlab) i)
        _ = A.vertex i := vab i
    · intro i
      calc
        D.edge (Fin.castLE (le_trans hlab hlbd) i) =
            B.edge (Fin.castLE hlab i) := by
              simpa using ebd (Fin.castLE hlab i)
        _ = A.edge i := eab i
  have storedToFinal :
      TreeSequenceInitialSegment
        (ett.series.data.tree jSlot.succ.castSucc)
        (ett.series.data.tree ⟨ett.rounds, by omega⟩) := by
    have stepSegment : ∀ i : Fin (ett.rounds + 1), 0 < i.val →
        TreeSequenceInitialSegment (ett.series.data.tree i.castSucc)
          (ett.series.data.tree i.succ) := by
      intro i
      have ordered : ∀ h : TashkinovSeriesStep G k ett.rounds e0 input
          ett.series.data i, i ≠ 0 →
          TreeSequenceInitialSegment (ett.series.data.tree i.castSucc)
            (ett.series.data.tree i.succ) := by
        intro h hi
        cases h with
        | initial => exact (hi rfl).elim
        | SE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => assumption
        | PE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => assumption
        | RE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => assumption
      intro hi
      apply ordered (ett.series.certified i)
      intro hz
      subst i
      simp at hi
    have chain : ∀ n : ℕ, (hn : jSlot.val + 1 + n ≤ ett.rounds) →
        TreeSequenceInitialSegment
          (ett.series.data.tree ⟨jSlot.val + 1, by omega⟩)
          (ett.series.data.tree ⟨jSlot.val + 1 + n, by omega⟩) := by
      intro n hn
      induction n with
      | zero =>
          simpa using (show TreeSequenceInitialSegment
            (ett.series.data.tree ⟨jSlot.val + 1, by omega⟩)
            (ett.series.data.tree ⟨jSlot.val + 1, by omega⟩) from
            ⟨le_rfl, (by intro i; rfl), (by intro i; rfl)⟩)
      | succ n ih =>
          have hn' : jSlot.val + 1 + n ≤ ett.rounds := by omega
          have hidx : jSlot.val + n + 1 < ett.rounds + 1 := by omega
          have prev := stepSegment
            (⟨jSlot.val + n + 1, hidx⟩ : Fin (ett.rounds + 1)) (by simp)
          have prev' : TreeSequenceInitialSegment
              (ett.series.data.tree ⟨jSlot.val + 1 + n, by omega⟩)
              (ett.series.data.tree ⟨jSlot.val + 1 + (n + 1), by omega⟩) := by
            simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using prev
          exact segmentTrans _ _ _ (ih hn') prev'
    have bound : jSlot.val + 1 + (ett.rounds - (jSlot.val + 1)) ≤ ett.rounds := by omega
    have startEq : (⟨jSlot.val + 1, by omega⟩ : Fin (ett.rounds + 2)) =
        jSlot.succ.castSucc := by ext; simp
    rw [← startEq]
    have hle : jSlot.val + 1 ≤ ett.rounds := by omega
    have ending :
        (⟨jSlot.val + 1 + (ett.rounds - (jSlot.val + 1)), by omega⟩ :
      Fin (ett.rounds + 2)) = ⟨ett.rounds, by omega⟩ := by
      apply Fin.ext
      change jSlot.val + 1 + (ett.rounds - (jSlot.val + 1)) = ett.rounds
      omega
    have result := chain (ett.rounds - (jSlot.val + 1)) bound
    rw [ending] at result
    exact result
  let Tj := ett.series.data.tree jSlot.succ.castSucc
  have storedToT : TreeSequenceInitialSegment Tj T := by
    exact segmentTrans _ _ _ storedToFinal ett.abovePenultimate
  have beforeInTj : ∀ w : V, w ∈ TreeVerticesBefore T terminalSupport
      hterminalSupport → w ∈ TreeSequenceVertexSet Tj := by
    dsimp [Tj]
    intro w hw
    unfold TreeVerticesBefore at hw
    rcases Finset.mem_filter.mp hw with ⟨hwT, horder⟩
    rcases horder with ⟨iw, iv, wiw, viv, hi⟩
    rcases Finset.mem_image.mp hwT with ⟨iwT, -, iwEq⟩
    have hterminalJ' : terminalSupport ∈
        TreeSequenceVertexSet (ett.series.data.tree jSlot.castSucc.succ) := by
      simpa using hterminalJ
    rcases Finset.mem_image.mp hterminalJ' with ⟨qv, -, qEq⟩
    dsimp [Tj] at storedToT
    rcases storedToT with ⟨hlen, entries, edges⟩
    let qT : Fin (T.length + 1) :=
      Fin.castLE (Nat.succ_le_succ hlen) qv
    have qTval : T.vertex qT = terminalSupport := by
      exact (entries qv).trans qEq
    have ivEq : iv = qT := by
      apply T.vertex_injective
      rw [qTval, viv]
    have iwTEq : iwT = iw := by
      apply T.vertex_injective
      exact iwEq.trans wiw.symm
    have orderT : iwT.val < qv.val := by
      have hh := hi
      rw [← iwTEq, ivEq] at hh
      simpa [qT] using hh
    have ilen : iwT.val < Tj.length + 1 := by
      change iwT.val < (ett.series.data.tree jSlot.castSucc.succ).length + 1
      omega
    let iT : Fin (Tj.length + 1) := ⟨iwT.val, ilen⟩
    apply Finset.mem_image.mpr
    refine ⟨iT, Finset.mem_univ _, ?_⟩
    have sameIndex : (Fin.castLE (Nat.succ_le_succ hlen) iT) = iw := by
      apply Fin.ext
      simp [iT, iwTEq]
    calc
      (ett.series.data.tree jSlot.castSucc.succ).vertex iT =
          T.vertex (Fin.castLE (Nat.succ_le_succ hlen) iT) :=
        (entries iT).symm
      _ = T.vertex iw := by rw [sameIndex]
      _ = w := wiw
  have noCycle : ∀ u v : V, TreeVertexOrder T u v →
      TreeVertexOrder T v u → False := by
    intro u v huv hvu
    rcases huv with ⟨i, j, hi, hj, hij⟩
    rcases hvu with ⟨i', j', hi', hj', hji⟩
    have ei : i = j' := T.vertex_injective (hi.trans hj'.symm)
    have ej : j = i' := T.vertex_injective (hj.trans hi'.symm)
    omega
  have currentVertex : ∀ a : Fin trace.steps, ∀ w : V,
      w ∈ TreeVerticesBefore T terminalSupport hterminalSupport →
      w ∈ TreeSequenceVertexSet
        (ett.series.data.tree (trace.slot a).succ.castSucc) := by
    intro a w hw
    have stepInvariant := hinvariant.2.1 a
    rcases stepInvariant.2.2 with ⟨segment, supportInTree, deltaMissing,
      pathComponent, exactIntersection, remaining⟩
    have wj := beforeInTj w hw
    rcases segment with ⟨hlen, entries, edges⟩
    apply Finset.mem_image.mpr
    rcases Finset.mem_image.mp wj with ⟨i, -, hi⟩
    refine ⟨Fin.castLE (Nat.succ_le_succ hlen) i, Finset.mem_univ _, ?_⟩
    simpa using (entries i).trans hi
  have edgeOutside : ∀ a : Fin trace.steps, ∀ w : V,
      w ∈ TreeVerticesBefore T terminalSupport hterminalSupport →
      ∀ f : E, Incident G w f →
      Sum.inr f ∉ TwoColorComponent G (trace.coloring a.castSucc)
        (trace.gamma a) (trace.delta a) (Sum.inl (trace.support a)) := by
    intro a w hw f hwf hf
    have stepInvariant := hinvariant.2.1 a
    rcases stepInvariant.2.2 with ⟨segment, supportInTree, deltaMissing,
      pathComponent, exactIntersection, remaining⟩
    have win := currentVertex a w hw
    have wne : w ≠ trace.support a := by
      intro heq
      apply noCycle w terminalSupport
      · have hwo := hw
        unfold TreeVerticesBefore at hwo
        exact (Finset.mem_filter.mp hwo).2
      · simpa [heq] using stepInvariant.2.1
    have endpoint : Sum.inl w ∈ TwoColorComponent G
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
      have adj : H.Adj (Sum.inl w) (Sum.inr f) := by
        simp [H, TwoColorIncidenceGraph, hwf, active]
      change H.connectedComponentMk (Sum.inl w) =
        H.connectedComponentMk (Sum.inl (trace.support a))
      exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
        adj).trans hf
    exact wne ((exactIntersection w win).mp endpoint)
  have preserved : ∀ n : ℕ, (hn : n ≤ trace.steps) → ∀ f : E,
      (∃ w ∈ TreeVerticesBefore T terminalSupport hterminalSupport,
        Incident G w f) →
      trace.coloring ⟨n, Nat.lt_succ_of_le hn⟩ f = sigmaN f := by
    intro n hn
    induction n with
    | zero =>
        intro f hf
        simpa using congrFun trace.initialColoring f
    | succ n ih =>
        intro f hf
        let a : Fin trace.steps := ⟨n, Nat.lt_of_succ_le hn⟩
        have hfall := hf
        have hkeep := hf
        obtain ⟨w, hw, hwf⟩ := hkeep
        have ho := edgeOutside a w hw f hwf
        have tr := congrFun (trace.transition a) f
        have unchanged : TwoColorComponentSwap G (trace.coloring a.castSucc)
              (trace.gamma a) (trace.delta a) (Sum.inl (trace.support a)) f =
            trace.coloring a.castSucc f := by
          simp [TwoColorComponentSwap, ho]
        have prev : trace.coloring a.castSucc f = sigmaN f := by
          have he : a.castSucc =
              ⟨n, Nat.lt_succ_of_le (Nat.le_of_succ_le hn)⟩ := by
            apply Fin.ext
            simp [a]
          rw [he]
          exact ih (Nat.le_of_succ_le hn) f hfall
        have next : trace.coloring a.succ f = sigmaN f := by
          rw [tr, unchanged, prev]
        have he : (⟨n + 1, Nat.lt_succ_of_le hn⟩ : Fin (trace.steps + 1)) =
            a.succ := by
          apply Fin.ext
          simp [a]
        rw [he]
        exact next
  have finalPreserved : ∀ f : E,
      (∃ w ∈ TreeVerticesBefore T terminalSupport hterminalSupport,
        Incident G w f) →
      trace.coloring (Fin.last trace.steps) f = sigmaN f := by
    intro f hf
    simpa [Fin.last] using preserved trace.steps le_rfl f hf
  unfold StableColoringBeforeVertex at hsigmaStable ⊢
  constructor
  · intro f hf hcol
    have hfall := hf
    rcases hf with ⟨w, hw, hwf⟩
    rw [finalPreserved f ⟨w, hw, hwf⟩]
    exact hsigmaStable.1 f hfall hcol
  · intro w hw
    have missingEq : MissingColors G
        (trace.coloring (Fin.last trace.steps)) w = MissingColors G sigmaN w := by
      apply Finset.ext
      intro c
      simp [MissingColors, PresentColors]
      constructor
      · intro hc f hwf hfc
        apply hc f hwf
        rw [← finalPreserved f ⟨w, hw, hwf⟩] at hfc
        exact hfc
      · intro hc f hwf hfc
        apply hc f hwf
        rw [finalPreserved f ⟨w, hw, hwf⟩] at hfc
        exact hfc
    exact missingEq.trans (hsigmaStable.2 w hw)
