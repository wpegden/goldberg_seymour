import Tablet.ETTFirstAppearanceIndex
import Tablet.ExtendedTashkinovLadderStage
import Tablet.ExtendedTashkinovTree
import Tablet.ExtensionBaseActiveIndices
import Tablet.ExtensionRulesPEFirstAppearanceBound
import Tablet.HkuUnsupportedVertexColors
import Tablet.TashkinovSeries
import Tablet.TashkinovSeriesStep
import Tablet.TreeMissingColors
import Tablet.TreeSequenceInitialSegment
import Tablet.TreeSequenceInitialSegmentVertexSetSubset
import Tablet.TreeSequenceVertexSet

-- [TABLET NODE: ExtensionBaseLeastActiveDeltaTransport]
theorem ExtensionBaseLeastActiveDeltaTransport {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    {input : PartialEdgeColoring E k} {T : TreeSequence G e0}
    {generating : PartialEdgeColoring E k}
    (ett : ExtendedTashkinovTree G k e0 input T generating)
    (terminalSupport : V)
    (hterminalSupport : terminalSupport ∈ TreeSequenceVertexSet T)
    (q : Fin ett.rounds) (hqTerminal : q.val + 1 = ett.rounds)
    (hqKind : ett.series.data.kind q.succ =
      some TashkinovExtensionKind.PE)
    (hqVertex : ett.series.data.chosenVertex q.succ = some terminalSupport)
    (jSlot : Fin ett.rounds)
    (hjSlot : jSlot.val + 1 =
      ETTFirstAppearanceIndex ett terminalSupport hterminalSupport)
    (hpair : ∀ (s t : Fin ett.rounds) (vs vt : V)
      (hvsFinal : vs ∈ TreeSequenceVertexSet T)
      (hvtFinal : vt ∈ TreeSequenceVertexSet T)
      (deltaT : Fin k),
      s ∈ ExtensionBaseActiveIndices ett terminalSupport hterminalSupport →
      t ∈ ExtensionBaseActiveIndices ett terminalSupport hterminalSupport →
      s.val ≤ t.val →
      ett.series.data.chosenVertex s.succ = some vs →
      ett.series.data.chosenVertex t.succ = some vt →
      ett.series.data.delta t.succ = some deltaT →
      deltaT ∉ TreeMissingColors (ett.series.data.coloring s.castSucc)
        (ett.series.data.tree s.succ.castSucc)) :
    ∀ (t : Fin ett.rounds) (vt : V)
      (hvtFinal : vt ∈ TreeSequenceVertexSet T) (deltaT : Fin k),
      t ∈ ExtensionBaseActiveIndices ett terminalSupport hterminalSupport →
      ett.series.data.chosenVertex t.succ = some vt →
      ett.series.data.delta t.succ = some deltaT →
      deltaT ∉ TreeMissingColors (ett.series.data.coloring jSlot.castSucc)
        (ett.series.data.tree jSlot.succ.castSucc) := by
-- BODY
  classical
  let series := ett.series
  have nextSegment (i : Fin ett.rounds) :
      TreeSequenceInitialSegment (series.data.tree i.succ.castSucc)
        (series.data.tree i.succ.succ) := by
    have step := series.certified i.succ
    generalize hz : i.succ = z at step
    cases step with
    | initial triple seedLength initialColoring initialStored initialEdges
        initialKind initialVertex initialOutside initialDelta initialGamma
        initialClosure =>
        have hv := congrArg Fin.val hz
        simp at hv
    | SE r previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed noRevisiting choice seriesAlternative
        currentColoring currentStored currentEdges currentKind currentVertex
        currentOutside currentDelta currentGamma adjoined adjoinedExactly
        closedExtension orderedExtension strictExtension =>
        have hri : r = i := by
          apply Fin.ext
          have hv := congrArg Fin.val hz
          simp at hv ⊢
          omega
        subst r
        exact orderedExtension
    | PE r previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed noRevisiting choice seriesAlternativeFails
        gamma gammaRule secondStable secondStableProper
        secondStableOneUncolored secondStableRelation exitWitness
        currentColoring currentProper currentOneUncolored currentStored
        currentEdges currentKind currentVertex currentOutside currentDelta
        currentGamma closedExtension orderedExtension strictExtension =>
        have hri : r = i := by
          apply Fin.ext
          have hv := congrArg Fin.val hz
          simp at hv ⊢
          omega
        subst r
        exact orderedExtension
    | RE r previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed available currentColoring currentStored
        currentEdges currentKind currentVertex currentOutside currentDelta
        currentGamma adjoined adjoinedExactly closedExtension orderedExtension
        strictExtension =>
        have hri : r = i := by
          apply Fin.ext
          have hv := congrArg Fin.val hz
          simp at hv ⊢
          omega
        subst r
        exact orderedExtension
  have segmentRefl (A : TreeSequence G e0) :
      TreeSequenceInitialSegment A A :=
    ⟨le_rfl, by intro i; rfl, by intro i; rfl⟩
  have segmentTrans {A B C : TreeSequence G e0}
      (hAB : TreeSequenceInitialSegment A B)
      (hBC : TreeSequenceInitialSegment B C) :
      TreeSequenceInitialSegment A C := by
    obtain ⟨hABlen, hABv, hABe⟩ := hAB
    obtain ⟨hBClen, hBCv, hBCe⟩ := hBC
    refine ⟨hABlen.trans hBClen, ?_, ?_⟩
    · intro i
      calc
        C.vertex (Fin.castLE (Nat.succ_le_succ (hABlen.trans hBClen)) i) =
            B.vertex (Fin.castLE (Nat.succ_le_succ hABlen) i) := by
              simpa only [Fin.castLE] using
                hBCv (Fin.castLE (Nat.succ_le_succ hABlen) i)
        _ = A.vertex i := hABv i
    · intro i
      calc
        C.edge (Fin.castLE (hABlen.trans hBClen) i) =
            B.edge (Fin.castLE hABlen i) := by
              simpa only [Fin.castLE] using hBCe (Fin.castLE hABlen i)
        _ = A.edge i := hABe i
  have stageSegment : ∀ (a b : Fin ett.rounds), a.val ≤ b.val →
      TreeSequenceInitialSegment (series.data.tree a.succ.castSucc)
        (series.data.tree b.succ.castSucc) := by
    intro a b hab
    have claim : ∀ (n : ℕ), a.val ≤ n → n < ett.rounds →
        ∀ r : Fin ett.rounds, r.val = n →
          TreeSequenceInitialSegment (series.data.tree a.succ.castSucc)
            (series.data.tree r.succ.castSucc) := by
      intro n han
      induction n, han using Nat.le_induction with
      | base =>
          intro hn r hr
          have hra : r = a := by apply Fin.ext; omega
          subst r
          exact segmentRefl _
      | succ n hn ih =>
          intro hrounds r hr
          let p : Fin ett.rounds := ⟨n, by omega⟩
          have hprev := ih (by omega) p rfl
          have hnext := nextSegment p
          have htree : p.succ.succ = r.succ.castSucc := by
            apply Fin.ext
            simp [p, hr]
          rw [htree] at hnext
          exact segmentTrans hprev hnext
    exact claim b.val hab b.isLt b rfl
  have qBound : ETTFirstAppearanceIndex ett terminalSupport
      hterminalSupport ≤ q.val + 1 :=
    ExtensionRulesPEFirstAppearanceBound G k e0 input T generating ett q
      terminalSupport hqKind hqVertex hterminalSupport
  have qActive : q ∈ ExtensionBaseActiveIndices ett terminalSupport
      hterminalSupport := by
    simp [ExtensionBaseActiveIndices]
    exact ⟨qBound, hqKind, terminalSupport, hqVertex,
      hterminalSupport, le_rfl⟩
  let active := ExtensionBaseActiveIndices ett terminalSupport hterminalSupport
  have activeNonempty : active.Nonempty := ⟨q, qActive⟩
  let s0 : Fin ett.rounds := active.min' activeNonempty
  have hs0Active : s0 ∈ active := Finset.min'_mem active activeNonempty
  have hs0Least : ∀ r : Fin ett.rounds, r ∈ active → s0.val ≤ r.val := by
    intro r hr
    exact Fin.le_iff_val_le_val.mp (Finset.min'_le active r hr)
  have hs0Data := hs0Active
  simp [active, ExtensionBaseActiveIndices] at hs0Data
  obtain ⟨hs0Lower, hs0Kind, vs0, hs0Vertex, hvs0Final,
    hvs0First⟩ := hs0Data
  have hjleS0 : jSlot.val ≤ s0.val := by omega
  have hjleQ : jSlot.val ≤ q.val := by omega
  have jFinalSegment : TreeSequenceInitialSegment
      (series.data.tree jSlot.succ.castSucc) T := by
    have hjq := stageSegment jSlot q hjleQ
    have htree : q.succ.castSucc = (⟨ett.rounds, by omega⟩ :
        Fin (ett.rounds + 2)) := by
      apply Fin.ext
      simp
      exact hqTerminal
    rw [htree] at hjq
    exact segmentTrans hjq ett.abovePenultimate
  have jFinalSubset := TreeSequenceInitialSegmentVertexSetSubset jFinalSegment
  have firstBound : ∀ (x : V)
      (hxFinal : x ∈ TreeSequenceVertexSet T),
      x ∈ TreeSequenceVertexSet
          (series.data.tree jSlot.succ.castSucc) →
        ETTFirstAppearanceIndex ett x hxFinal ≤ jSlot.val + 1 := by
    intro x hxFinal hxJ
    unfold ETTFirstAppearanceIndex
    dsimp
    have hmem : jSlot.castSucc ∈
        Finset.univ.filter (fun i : Fin (ett.rounds + 1) =>
          x ∈ TreeSequenceVertexSet
            (ExtendedTashkinovLadderStage ett i)) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      simpa [ExtendedTashkinovLadderStage, Fin.lastCases_castSucc, series]
        using hxJ
    have hle := Finset.min'_le
      (Finset.univ.filter (fun i : Fin (ett.rounds + 1) =>
        x ∈ TreeSequenceVertexSet (ExtendedTashkinovLadderStage ett i)))
      jSlot.castSucc hmem
    have hnat := Fin.le_iff_val_le_val.mp hle
    rw [Fin.val_castSucc] at hnat
    convert Nat.succ_le_succ hnat using 1 <;>
      simp only [Fin.val_castSucc, Nat.succ_eq_add_one] <;>
      try { exact proof_irrel_heq } <;>
      try { congr }
  intro t vt hvtFinal deltaT htActive htVertex htDelta
  have hs0leT := hs0Least t (by simpa [active] using htActive)
  have hs0Exclusion : deltaT ∉
      TreeMissingColors (series.data.coloring s0.castSucc)
        (series.data.tree s0.succ.castSucc) := by
    exact hpair s0 t vs0 vt hvs0Final hvtFinal deltaT
      (by simpa [active] using hs0Active) htActive hs0leT hs0Vertex
      htVertex htDelta
  by_cases hjEq : jSlot.val = s0.val
  · have hindices : jSlot = s0 := Fin.ext hjEq
    simpa [series, hindices] using hs0Exclusion
  · have hjlt : jSlot.val < s0.val := lt_of_le_of_ne hjleS0 hjEq
    let before : Fin ett.rounds := ⟨s0.val - 1, by omega⟩
    have hbeforeSucc : before.succ = s0.castSucc := by
      apply Fin.ext
      simp [before]
      omega
    have hjBefore : jSlot.val ≤ before.val := by
      simp [before]
      omega
    intro hmissingJ
    simp only [TreeMissingColors, Finset.mem_biUnion] at hmissingJ
    obtain ⟨x, hxJ, hxMissingJ⟩ := hmissingJ
    have hxFinal := jFinalSubset hxJ
    have hxFirst := firstBound x hxFinal hxJ
    have hunused : ∀ r : Fin ett.rounds,
        jSlot.val ≤ r.val → r.val ≤ before.val →
        ¬ (series.data.kind r.succ = some TashkinovExtensionKind.PE ∧
          series.data.chosenVertex r.succ = some x) := by
      intro r hjr hrb hrPE
      have hrActive : r ∈ ExtensionBaseActiveIndices ett terminalSupport
          hterminalSupport := by
        simp [ExtensionBaseActiveIndices]
        refine ⟨?_, hrPE.1, x, hrPE.2, hxFinal, ?_⟩
        · omega
        · calc
            ETTFirstAppearanceIndex ett x hxFinal ≤ jSlot.val + 1 := hxFirst
            _ = ETTFirstAppearanceIndex ett terminalSupport
                hterminalSupport := hjSlot
      have hs0r := hs0Least r (by simpa [active] using hrActive)
      have hrBefore : r.val ≤ s0.val - 1 := by
        simpa [before] using hrb
      omega
    have hxEq := HkuUnsupportedVertexColors G k ett.rounds e0 input series
      before jSlot x hjBefore hxJ hunused
    apply hs0Exclusion
    simp only [TreeMissingColors, Finset.mem_biUnion]
    have hxS0 := TreeSequenceInitialSegmentVertexSetSubset
      (stageSegment jSlot s0 hjleS0) hxJ
    refine ⟨x, hxS0, ?_⟩
    rw [← hbeforeSucc]
    rw [← hxEq]
    exact hxMissingJ

