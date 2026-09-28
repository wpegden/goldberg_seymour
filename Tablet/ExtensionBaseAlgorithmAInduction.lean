import Tablet.DefectiveVertex
import Tablet.ExtensionBaseAlgorithmAColorState
import Tablet.ExtensionBaseAlgorithmASingleStep
import Tablet.ExtensionBaseActiveIndices
import Tablet.ExtensionBaseRestorationIndices
import Tablet.ExtensionBaseRestorationInvariant
import Tablet.ExtensionBaseRestorationTrace
import Tablet.ExtensionBaseSupportClass
import Tablet.IsOneEdgeUncolored
import Tablet.IsProperEdgeColoring
import Tablet.StrongInterchangeabilityKempePreserved
import Tablet.TashkinovSeries
import Tablet.TashkinovSeriesStep

-- [TABLET NODE: ExtensionBaseAlgorithmAInduction]
theorem ExtensionBaseAlgorithmAInduction {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    {input : PartialEdgeColoring E k} {T : TreeSequence G e0}
    {generating : PartialEdgeColoring E k}
    (ett : ExtendedTashkinovTree G k e0 input T generating)
    (terminalSupport : V)
    (hterminalSupport : terminalSupport ∈ TreeSequenceVertexSet T)
    (jSlot q : Fin ett.rounds) (sigmaN : PartialEdgeColoring E k)
    (hqVertex : ett.series.data.chosenVertex q.succ = some terminalSupport)
    (hsigmaProper : IsProperEdgeColoring G sigmaN)
    (hsigmaOne : IsOneEdgeUncolored sigmaN e0)
    (hterminalBefore : ∀ (t : Fin ett.rounds) (vt : V),
      t ∈ ExtensionBaseRestorationIndices ett terminalSupport
          hterminalSupport →
      ett.series.data.chosenVertex t.succ = some vt →
      TreeVertexOrder T terminalSupport vt)
    (hjInitial : ∀ t : Fin ett.rounds,
      t ∈ ExtensionBaseRestorationIndices ett terminalSupport
          hterminalSupport →
      TreeSequenceInitialSegment
        (ett.series.data.tree jSlot.succ.castSucc)
        (ett.series.data.tree t.succ.castSucc))
    (hinitialSI : ∀ (t : Fin ett.rounds) (vt : V)
      (gammaT deltaT : Fin k),
      t ∈ ExtensionBaseActiveIndices ett terminalSupport hterminalSupport →
      t ≠ q →
      ett.series.data.chosenVertex t.succ = some vt →
      ett.series.data.gamma t.succ = some gammaT →
      ett.series.data.delta t.succ = some deltaT →
      ETTStrongInterchangeable ett t vt sigmaN gammaT deltaT)
    (hpairOverlap : ∀ (s t : Fin ett.rounds) (vs vt : V)
      (gammaS deltaS gammaT deltaT : Fin k),
      s ∈ ExtensionBaseActiveIndices ett terminalSupport
          hterminalSupport →
      t ∈ ExtensionBaseActiveIndices ett terminalSupport
          hterminalSupport →
      s.val < t.val →
      ett.series.data.chosenVertex s.succ = some vs →
      ett.series.data.chosenVertex t.succ = some vt →
      ett.series.data.gamma s.succ = some gammaS →
      ett.series.data.delta s.succ = some deltaS →
      ett.series.data.gamma t.succ = some gammaT →
      ett.series.data.delta t.succ = some deltaT →
      ((({gammaS, deltaS} : Finset (Fin k)) ∩ {gammaT, deltaT}).Nonempty ↔
          vs = vt ∧
          ¬ ∃ r : Fin ett.rounds,
            r ∈ ExtensionBaseSupportClass ett terminalSupport
                hterminalSupport vs ∧
            s.val < r.val ∧ r.val < t.val ∧
            ett.series.data.chosenVertex r.succ = some vs) ∧
      ((({gammaS, deltaS} : Finset (Fin k)) ∩ {gammaT, deltaT}).Nonempty →
        ({gammaS, deltaS} : Finset (Fin k)) ∩ {gammaT, deltaT} =
            {gammaT} ∧
          ({gammaS, deltaS} : Finset (Fin k)) ∩ {gammaT, deltaT} =
            {deltaS}))
    (trace : ExtensionBaseRestorationTrace ett terminalSupport
      hterminalSupport sigmaN)
    (hcolorState : ∀ a : Fin trace.steps,
      trace.delta a ∈
          MissingColors G (trace.coloring a.castSucc) (trace.support a) ∧
        trace.gamma a ∈
          PresentColors G (trace.coloring a.castSucc) (trace.support a)) :
    ExtensionBaseRestorationInvariant ett terminalSupport hterminalSupport
      jSlot q sigmaN trace := by
-- BODY
  classical
  unfold ExtensionBaseRestorationInvariant
  let L := ExtensionBaseRestorationIndices ett terminalSupport hterminalSupport
  have slot_mem (a : Fin trace.steps) : trace.slot a ∈ L := by
    change trace.slot a ∈ ExtensionBaseRestorationIndices ett terminalSupport hterminalSupport
    rw [← trace.enumerates]
    exact Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩
  have slot_active (a : Fin trace.steps) :
      trace.slot a ∈ ExtensionBaseActiveIndices ett terminalSupport hterminalSupport := by
    exact (Finset.mem_sdiff.mp (slot_mem a)).1
  have slot_not_class (a : Fin trace.steps) :
      trace.slot a ∉ ExtensionBaseSupportClass ett terminalSupport
        hterminalSupport terminalSupport := by
    have hm : trace.slot a ∈
        ExtensionBaseRestorationIndices ett terminalSupport hterminalSupport := by
      exact slot_mem a
    exact (Finset.mem_sdiff.mp hm).2
  have slot_tree (a : Fin trace.steps) :
      trace.support a ∈ TreeSequenceVertexSet
        (ett.series.data.tree (trace.slot a).succ.castSucc) := by
    have ha := slot_active a
    unfold ExtensionBaseActiveIndices at ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
    have hkind : ett.series.data.kind (trace.slot a).succ =
        some TashkinovExtensionKind.PE := ha.2.1
    have hc := ett.series.certified (trace.slot a).succ
    generalize hn : (trace.slot a).succ = n at hc
    cases hc with
    | PE i previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed noRevisiting choice seriesAlternative
        gamma gammaRule secondStable secondStableProper
        secondStableOneUncolored secondStableRelation exitWitness
        currentColoring currentProper currentOneUncolored currentStored
        currentEdges currentKind currentVertex currentOutside currentDelta
        currentGamma closedExtension orderedExtension strictExtension =>
      have hv := choice.vertexDefective.1
      have heqIndex : i = trace.slot a := by
        apply Fin.ext
        have hh := congrArg Fin.val hn
        simp at hh ⊢
        omega
      have heq : choice.vertex = trace.support a := by
        apply Option.some.inj
        have hcv : ett.series.data.chosenVertex (trace.slot a).succ =
            some choice.vertex := by simpa [heqIndex] using currentVertex
        exact hcv.symm.trans (trace.chosenVertex a)
      simpa [heqIndex, heq] using hv
    | initial => simp_all
    | SE =>
      simp_all
    | RE =>
      simp_all
  have slot_ne_q (a : Fin trace.steps) : trace.slot a ≠ q := by
    intro heq
    apply slot_not_class a
    unfold ExtensionBaseSupportClass
    simp only [Finset.mem_filter]
    constructor
    · exact slot_active a
    · simpa [heq, trace.chosenVertex a, hqVertex]
  have state : ∀ n : Fin (trace.steps + 1),
      (IsProperEdgeColoring G (trace.coloring n) ∧
        IsOneEdgeUncolored (trace.coloring n) e0) ∧
      (∀ s : Fin ett.rounds, ∀ vs : V, ∀ gammaS deltaS : Fin k,
        s ∈ ExtensionBaseActiveIndices ett terminalSupport hterminalSupport →
        s ≠ q →
        (∀ b : Fin trace.steps, b.val < n.val → trace.slot b ≠ s) →
        ett.series.data.chosenVertex s.succ = some vs →
        ett.series.data.gamma s.succ = some gammaS →
        ett.series.data.delta s.succ = some deltaS →
        ETTStrongInterchangeable ett s vs (trace.coloring n) gammaS deltaS) := by
    intro n
    induction n using Fin.induction with
    | zero =>
        refine ⟨?_, ?_⟩
        · simpa [trace.initialColoring] using And.intro hsigmaProper hsigmaOne
        · intro s vs gammaS deltaS hs hq hnot hvs hgs hds
          rw [trace.initialColoring]
          exact hinitialSI s vs gammaS deltaS hs hq hvs hgs hds
    | succ a ih =>
        rcases ih with ⟨hgood, hsurvivor⟩
        have hsi : ETTStrongInterchangeable ett (trace.slot a)
            (trace.support a) (trace.coloring a.castSucc)
            (trace.gamma a) (trace.delta a) := by
          apply hsurvivor (trace.slot a) (trace.support a)
            (trace.gamma a) (trace.delta a) (slot_active a) (slot_ne_q a)
          · intro b hb
            have hd := trace.strictlyDescending b a hb
            intro he
            rw [he] at hd
            exact (Nat.lt_irrefl _ hd)
          · exact trace.chosenVertex a
          · exact trace.gammaField a
          · exact trace.deltaField a
        have hcs := hcolorState a
        have hstep := ExtensionBaseAlgorithmASingleStep ett (trace.slot a)
          (trace.support a) (trace.coloring a.castSucc) (trace.gamma a)
          (trace.delta a) hgood.1 hgood.2 hsi (slot_tree a) hcs.1 hcs.2
        have hgoodNext :
            IsProperEdgeColoring G (trace.coloring a.succ) ∧
              IsOneEdgeUncolored (trace.coloring a.succ) e0 := by
          rw [trace.transition a]
          exact hstep.2.2
        refine ⟨hgoodNext, ?_⟩
        intro s vs gammaS deltaS hs hq hnot hvs hgs hds
        have hsOld : ETTStrongInterchangeable ett s vs
            (trace.coloring a.castSucc) gammaS deltaS := by
          apply hsurvivor s vs gammaS deltaS hs hq
          intro b hb
          by_cases hba : b.val < a.val
          · exact hnot b (by change b.val < a.val + 1; omega)
          · have hb' : b.val < a.val := by simpa using hb
            have hbeq : b.val = a.val := by omega
            have hbaeq : b = a := Fin.ext hbeq
            exact hnot b (by change b.val < a.val + 1; omega)
          · exact hvs
          · exact hgs
          · exact hds
        have hrelative : vs ≠ trace.support a ∨ s.val < (trace.slot a).val := by
          by_cases hvsup : vs ≠ trace.support a
          · exact Or.inl hvsup
          · right
            have hvEq : vs = trace.support a := Classical.not_not.mp hvsup
            have hsL : s ∈ L := by
              change s ∈ ExtensionBaseRestorationIndices ett terminalSupport hterminalSupport
              apply Finset.mem_sdiff.mpr
              refine ⟨hs, ?_⟩
              intro hclass
              have hclass' : s ∈ ExtensionBaseActiveIndices ett terminalSupport
                  hterminalSupport ∧
                  ett.series.data.chosenVertex s.succ = some terminalSupport := by
                simpa [ExtensionBaseSupportClass] using hclass
              have hterm := hclass'.2
              have hvterm : vs = terminalSupport := Option.some.inj (hvs.symm.trans hterm)
              have hcur : trace.support a ≠ terminalSupport := by
                intro heq
                apply slot_not_class a
                unfold ExtensionBaseSupportClass
                simp only [Finset.mem_filter]
                exact ⟨slot_active a, by simpa [heq] using trace.chosenVertex a⟩
              exact hcur (hvEq.symm.trans hvterm)
            have himage : s ∈ Finset.univ.image trace.slot := by
              rw [trace.enumerates]
              exact hsL
            rcases Finset.mem_image.mp himage with ⟨c, -, hcs⟩
            have hac : a.val < c.val := by
              by_contra hle
              have hca : c.val < a.succ.val := by simp; omega
              exact hnot c (by simpa using hca) hcs
            have hd := trace.strictlyDescending a c hac
            simpa [hcs] using hd
        have hdisj : vs ≠ trace.support a →
            Disjoint ({gammaS, deltaS} : Finset (Fin k))
              {trace.gamma a, trace.delta a} := by
          intro hneSupport
          refine Finset.disjoint_left.2 ?_
          intro color hleft hright
          have hinter :
              (({gammaS, deltaS} : Finset (Fin k)) ∩
                {trace.gamma a, trace.delta a}).Nonempty :=
            ⟨color, Finset.mem_inter.mpr ⟨hleft, hright⟩⟩
          by_cases hst : s.val < (trace.slot a).val
          · have hor := hpairOverlap s (trace.slot a) vs (trace.support a)
              gammaS deltaS (trace.gamma a) (trace.delta a) hs
              (slot_active a) hst hvs (trace.chosenVertex a) hgs hds
              (trace.gammaField a) (trace.deltaField a)
            have heq := (hor.1.mp hinter).1
            exact hneSupport heq
          · have hneq : s ≠ trace.slot a := by
              intro heq
              have hna : a.val < a.succ.val := by simp
              have hslot := hnot a hna
              exact hslot heq.symm
            have hts : (trace.slot a).val < s.val := by
              have hv : s.val ≠ (trace.slot a).val := by
                intro he
                apply hneq
                exact Fin.ext he
              omega
            have hor := hpairOverlap (trace.slot a) s (trace.support a) vs
              (trace.gamma a) (trace.delta a) gammaS deltaS
              (slot_active a) hs hts (trace.chosenVertex a) hvs
              (trace.gammaField a) (trace.deltaField a) hgs hds
            have hinter' :
                (({trace.gamma a, trace.delta a} : Finset (Fin k)) ∩
                  {gammaS, deltaS}).Nonempty := by
              simpa [Finset.inter_comm] using hinter
            have heq := (hor.1.mp hinter').1
            exact hneSupport heq.symm
        have hp := StrongInterchangeabilityKempePreserved ett s
          (trace.slot a) vs (trace.support a) gammaS deltaS
          (trace.gamma a) (trace.delta a) (trace.coloring a.castSucc)
          (Sum.inl (trace.support a)) hgood.1 hgood.2 hgs hds
          (trace.gammaField a) (trace.deltaField a)
          hrelative hdisj hstep.1 hsi hsOld
        rw [trace.transition a]
        exact hp.2.2
  refine ⟨?_, ?_, ?_⟩
  · intro a
    exact (state a).1
  · intro a
    rcases state a.castSucc with ⟨hgood, hsurvivor⟩
    have hsi := hsurvivor (trace.slot a) (trace.support a)
      (trace.gamma a) (trace.delta a) (slot_active a) (slot_ne_q a)
      (by
        intro b hb hbeq
        have hd := trace.strictlyDescending b a hb
        rw [hbeq] at hd
        exact Nat.lt_irrefl _ hd) (trace.chosenVertex a) (trace.gammaField a)
      (trace.deltaField a)
    have hs := hcolorState a
    have hstep := ExtensionBaseAlgorithmASingleStep ett (trace.slot a)
      (trace.support a) (trace.coloring a.castSucc) (trace.gamma a)
      (trace.delta a) hgood.1 hgood.2 hsi (slot_tree a) hs.1 hs.2
    refine ⟨slot_mem a, hterminalBefore (trace.slot a) (trace.support a)
      (slot_mem a) (trace.chosenVertex a),
      hjInitial (trace.slot a) (by exact slot_mem a), slot_tree a, hs.1,
      hstep.1, hstep.2.1, ?_⟩
    intro s vs gammaS deltaS hsA hq hnot hvs hgs hds
    exact (state a.succ).2 s vs gammaS deltaS hsA hq (by
      intro b hb
      apply hnot b
      exact Nat.le_of_lt_succ (by simpa using hb)) hvs hgs hds
  · intro s vs gammaS deltaS hs hq hnot hvs hgs hds
    exact (state (Fin.last trace.steps)).2 s vs gammaS deltaS hs hq (by
      intro a ha
      exact hnot a) hvs hgs hds
