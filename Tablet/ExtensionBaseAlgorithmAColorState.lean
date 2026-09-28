import Tablet.ETTStrongInterchangeable
import Tablet.ExtensionBaseActiveIndices
import Tablet.ExtensionBaseRestorationIndices
import Tablet.ExtensionBaseRestorationTrace
import Tablet.ExtensionBaseSupportClass
import Tablet.MissingColors
import Tablet.PresentColors
import Tablet.TashkinovSeries
import Tablet.TashkinovSeriesStep
import Tablet.TwoColorComponent
import Tablet.TwoColorComponentSwap
import Tablet.TwoColorIncidenceGraph

-- [TABLET NODE: ExtensionBaseAlgorithmAColorState]
theorem ExtensionBaseAlgorithmAColorState {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    {input : PartialEdgeColoring E k} {T : TreeSequence G e0}
    {generating : PartialEdgeColoring E k}
    (ett : ExtendedTashkinovTree G k e0 input T generating)
    (terminalSupport : V)
    (hterminalSupport : terminalSupport ∈ TreeSequenceVertexSet T)
    (q : Fin ett.rounds) (sigmaN : PartialEdgeColoring E k)
    (hqVertex : ett.series.data.chosenVertex q.succ = some terminalSupport)
    (trace : ExtensionBaseRestorationTrace ett terminalSupport
      hterminalSupport sigmaN)
    (hinitialSI : ∀ (t : Fin ett.rounds) (vt : V)
      (gammaT deltaT : Fin k),
      t ∈ ExtensionBaseActiveIndices ett terminalSupport hterminalSupport →
      t ≠ q →
      ett.series.data.chosenVertex t.succ = some vt →
      ett.series.data.gamma t.succ = some gammaT →
      ett.series.data.delta t.succ = some deltaT →
      ETTStrongInterchangeable ett t vt sigmaN gammaT deltaT)
    (hclassMissing : ∀ (w : V) (t : Fin ett.rounds) (deltaT : Fin k),
      ExtensionBaseSupportClass ett terminalSupport hterminalSupport w ⊆
          ExtensionBaseRestorationIndices ett terminalSupport
            hterminalSupport →
      t ∈ ExtensionBaseSupportClass ett terminalSupport
          hterminalSupport w →
      (∀ s : Fin ett.rounds,
        s ∈ ExtensionBaseSupportClass ett terminalSupport
            hterminalSupport w →
        s.val ≤ t.val) →
      ett.series.data.delta t.succ = some deltaT →
      MissingColors G sigmaN w ∩
          (ExtensionBaseSupportClass ett terminalSupport hterminalSupport w).biUnion
            (fun s => ett.series.data.stored s.succ) = {deltaT})
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
            {deltaS})) :
    ∀ a : Fin trace.steps,
      trace.delta a ∈
          MissingColors G (trace.coloring a.castSucc) (trace.support a) ∧
        trace.gamma a ∈
          PresentColors G (trace.coloring a.castSucc) (trace.support a) := by
-- BODY
  classical
  letI : DecidableEq V := Classical.decEq V
  let L := ExtensionBaseRestorationIndices ett terminalSupport hterminalSupport
  let A := ExtensionBaseActiveIndices ett terminalSupport hterminalSupport
  let S := ExtensionBaseSupportClass ett terminalSupport hterminalSupport
  have slot_mem (a : Fin trace.steps) : trace.slot a ∈ L := by
    change trace.slot a ∈
      ExtensionBaseRestorationIndices ett terminalSupport hterminalSupport
    rw [← trace.enumerates]
    exact Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩
  have slot_active (a : Fin trace.steps) : trace.slot a ∈ A := by
    exact (Finset.mem_sdiff.mp (slot_mem a)).1
  have slot_not_terminal_class (a : Fin trace.steps) :
      trace.slot a ∉ S terminalSupport := by
    exact (Finset.mem_sdiff.mp (slot_mem a)).2
  have support_ne_terminal (a : Fin trace.steps) :
      trace.support a ≠ terminalSupport := by
    intro h
    apply slot_not_terminal_class a
    simp only [S, ExtensionBaseSupportClass, Finset.mem_filter]
    exact ⟨slot_active a, by simpa [h] using trace.chosenVertex a⟩
  have slot_ne_q (a : Fin trace.steps) : trace.slot a ≠ q := by
    intro h
    apply support_ne_terminal a
    apply Option.some.inj
    have hcv := trace.chosenVertex a
    rw [h] at hcv
    exact hcv.symm.trans hqVertex
  have pair_ne (a : Fin trace.steps) : trace.gamma a ≠ trace.delta a := by
    exact (hinitialSI (trace.slot a) (trace.support a) (trace.gamma a)
      (trace.delta a) (slot_active a) (slot_ne_q a)
      (trace.chosenVertex a) (trace.gammaField a) (trace.deltaField a)).1
  have stored_pair (a : Fin trace.steps) :
      ett.series.data.stored (trace.slot a).succ =
        {trace.gamma a, trace.delta a} := by
    have ha := slot_active a
    simp only [A, ExtensionBaseActiveIndices, Finset.mem_filter,
      Finset.mem_univ, true_and] at ha
    have hkind := ha.2.1
    have cert := ett.series.certified (trace.slot a).succ
    generalize hj : (trace.slot a).succ = j at cert
    cases cert with
    | initial => simp_all
    | SE => simp_all
    | RE => simp_all
    | PE i previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed noRevisiting choice seriesAlternativeFails
        gamma gammaRule secondStable secondStableProper
        secondStableOneUncolored secondStableRelation exitWitness
        currentColoring currentProper currentOneUncolored currentStored
        currentEdges currentKind currentVertex currentOutside currentDelta
        currentGamma closedExtension orderedExtension strictExtension =>
      have hi : i = trace.slot a := by
        apply Fin.ext
        have := congrArg Fin.val hj
        simp at this ⊢
        omega
      subst i
      have hg : gamma = trace.gamma a := by
        apply Option.some.inj
        exact currentGamma.symm.trans (trace.gammaField a)
      have hd : choice.color = trace.delta a := by
        apply Option.some.inj
        exact currentDelta.symm.trans (trace.deltaField a)
      simpa [hg, hd, Finset.pair_comm] using currentStored
  have trace_injective : Function.Injective trace.slot := by
    intro a b h
    apply Fin.ext
    by_contra hab
    rcases lt_or_gt_of_ne hab with hab | hab
    · have hd := trace.strictlyDescending a b hab
      rw [h] at hd
      exact (Nat.lt_irrefl _ hd)
    · have hd := trace.strictlyDescending b a hab
      rw [h] at hd
      exact (Nat.lt_irrefl _ hd)
  have class_subset (a : Fin trace.steps) : S (trace.support a) ⊆ L := by
    intro s hs
    apply Finset.mem_sdiff.mpr
    have hsA : s ∈ A := (Finset.mem_filter.mp hs).1
    refine ⟨hsA, ?_⟩
    intro hsTerm
    have hsSupport : ett.series.data.chosenVertex s.succ =
        some (trace.support a) := (Finset.mem_filter.mp hs).2
    have hsTerminal : ett.series.data.chosenVertex s.succ =
        some terminalSupport := (Finset.mem_filter.mp hsTerm).2
    exact support_ne_terminal a (Option.some.inj (hsSupport.symm.trans hsTerminal))
  have support_eq_of_slot_eq {a b : Fin trace.steps}
      (h : trace.slot a = trace.slot b) : trace.support a = trace.support b := by
    apply Option.some.inj
    rw [← trace.chosenVertex a, h, trace.chosenVertex b]
  have index_between {a b : Fin trace.steps} (hab : a.val < b.val)
      {r : Fin ett.rounds} (hrL : r ∈ L)
      (hlow : (trace.slot b).val < r.val)
      (hhigh : r.val < (trace.slot a).val) :
      ∃ c : Fin trace.steps, a.val < c.val ∧ c.val < b.val ∧ trace.slot c = r := by
    have hrImage : r ∈ Finset.univ.image trace.slot := by
      rw [trace.enumerates]
      exact hrL
    rcases Finset.mem_image.mp hrImage with ⟨c, -, hc⟩
    refine ⟨c, ?_, ?_, hc⟩
    · by_contra hca
      have hca' : c.val < a.val ∨ c = a := by
        have : c.val ≤ a.val := by omega
        exact (lt_or_eq_of_le this).imp_right Fin.ext
      rcases hca' with hca' | rfl
      · have hd := trace.strictlyDescending c a hca'
        rw [hc] at hd
        omega
      · rw [hc] at hhigh
        omega
    · by_contra hbc
      have hbc' : b.val < c.val ∨ c = b := by
        have : b.val ≤ c.val := by omega
        exact (lt_or_eq_of_le this).imp_right (fun h => Fin.ext h.symm)
      rcases hbc' with hbc' | rfl
      · have hd := trace.strictlyDescending b c hbc'
        rw [hc] at hd
        omega
      · rw [hc] at hlow
        omega
  have pair_relation (a b : Fin trace.steps) (hab : a.val < b.val) :
      ((({trace.gamma b, trace.delta b} : Finset (Fin k)) ∩
          {trace.gamma a, trace.delta a}).Nonempty ↔
        trace.support b = trace.support a ∧
          ¬ ∃ c : Fin trace.steps,
            a.val < c.val ∧ c.val < b.val ∧
              trace.support c = trace.support a) ∧
      ((({trace.gamma b, trace.delta b} : Finset (Fin k)) ∩
          {trace.gamma a, trace.delta a}).Nonempty →
        ({trace.gamma b, trace.delta b} : Finset (Fin k)) ∩
            {trace.gamma a, trace.delta a} = {trace.gamma a} ∧
        ({trace.gamma b, trace.delta b} : Finset (Fin k)) ∩
            {trace.gamma a, trace.delta a} = {trace.delta b}) := by
    have hslot := trace.strictlyDescending a b hab
    have raw := hpairOverlap (trace.slot b) (trace.slot a)
      (trace.support b) (trace.support a) (trace.gamma b) (trace.delta b)
      (trace.gamma a) (trace.delta a) (slot_active b) (slot_active a)
      hslot (trace.chosenVertex b) (trace.chosenVertex a)
      (trace.gammaField b) (trace.deltaField b) (trace.gammaField a)
      (trace.deltaField a)
    refine ⟨?_, raw.2⟩
    rw [raw.1]
    constructor
    · rintro ⟨hsupport, hnone⟩
      refine ⟨hsupport, ?_⟩
      rintro ⟨c, hac, hcb, hcs⟩
      apply hnone
      refine ⟨trace.slot c, ?_, ?_, ?_, ?_⟩
      · simp only [S, ExtensionBaseSupportClass, Finset.mem_filter]
        exact ⟨slot_active c, by simpa [hcs, hsupport] using trace.chosenVertex c⟩
      · exact trace.strictlyDescending c b hcb
      · exact trace.strictlyDescending a c hac
      · simpa [hcs, hsupport] using trace.chosenVertex c
    · rintro ⟨hsupport, hnone⟩
      refine ⟨hsupport, ?_⟩
      rintro ⟨r, hrClass, hrLow, hrHigh, hrChosen⟩
      have hrL := class_subset b hrClass
      rcases index_between hab hrL hrLow hrHigh with ⟨c, hac, hcb, hc⟩
      apply hnone
      refine ⟨c, hac, hcb, ?_⟩
      apply Option.some.inj
      rw [← trace.chosenVertex c, hc]
      simpa [hsupport] using hrChosen
  have swap_color_iff (phi : PartialEdgeColoring E k) (alpha beta c : Fin k)
      (z : Sum V E) (hca : c ≠ alpha) (hcb : c ≠ beta) (e : E) :
      TwoColorComponentSwap G phi alpha beta z e = some c ↔
        phi e = some c := by
    unfold TwoColorComponentSwap
    by_cases he : Sum.inr e ∈ TwoColorComponent G phi alpha beta z
    · simp only [if_pos he]
      by_cases ha : phi e = some alpha
      · rw [if_pos ha]
        constructor
        · intro h
          exact False.elim (hcb (Option.some.inj h).symm)
        · intro h
          exact False.elim (hca (Option.some.inj (ha.symm.trans h)).symm)
      · by_cases hb : phi e = some beta
        · rw [if_neg ha, if_pos hb]
          constructor
          · intro h
            exact False.elim (hca (Option.some.inj h).symm)
          · intro h
            exact False.elim (hcb (Option.some.inj (hb.symm.trans h)).symm)
        · simp [ha, hb]
    · simp [he]
  have swap_present_iff (phi : PartialEdgeColoring E k)
      (alpha beta c : Fin k) (z : Sum V E) (v : V)
      (hca : c ≠ alpha) (hcb : c ≠ beta) :
      c ∈ PresentColors G (TwoColorComponentSwap G phi alpha beta z) v ↔
        c ∈ PresentColors G phi v := by
    simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor <;> rintro ⟨e, he, hc⟩
    · exact ⟨e, he, (swap_color_iff phi alpha beta c z hca hcb e).mp hc⟩
    · exact ⟨e, he, (swap_color_iff phi alpha beta c z hca hcb e).mpr hc⟩
  have swap_missing_iff (phi : PartialEdgeColoring E k)
      (alpha beta c : Fin k) (z : Sum V E) (v : V)
      (hca : c ≠ alpha) (hcb : c ≠ beta) :
      c ∈ MissingColors G (TwoColorComponentSwap G phi alpha beta z) v ↔
        c ∈ MissingColors G phi v := by
    simp only [MissingColors, Finset.mem_sdiff, Finset.mem_univ, true_and,
      swap_present_iff phi alpha beta c z v hca hcb]
  have root_swap_gamma_missing (phi : PartialEdgeColoring E k)
      (gamma delta : Fin k) (w : V) (hne : gamma ≠ delta)
      (hdelta : delta ∈ MissingColors G phi w) :
      gamma ∈ MissingColors G
        (TwoColorComponentSwap G phi gamma delta (Sum.inl w)) w := by
    have hdeltaNot : delta ∉ PresentColors G phi w :=
      (Finset.mem_sdiff.mp hdelta).2
    rw [MissingColors, Finset.mem_sdiff]
    refine ⟨Finset.mem_univ _, ?_⟩
    simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
    rintro ⟨e, heIncident, heColor⟩
    by_cases heComp : Sum.inr e ∈
        TwoColorComponent G phi gamma delta (Sum.inl w)
    · unfold TwoColorComponentSwap at heColor
      rw [if_pos heComp] at heColor
      by_cases heGamma : phi e = some gamma
      · rw [if_pos heGamma] at heColor
        exact hne (Option.some.inj heColor).symm
      · by_cases heDelta : phi e = some delta
        · apply hdeltaNot
          simp only [PresentColors, Finset.mem_filter, Finset.mem_univ,
            true_and]
          exact ⟨e, heIncident, heDelta⟩
        · rw [if_neg heGamma, if_neg heDelta] at heColor
          exact heGamma heColor
    · have heGamma : phi e = some gamma := by
        simpa [TwoColorComponentSwap, heComp] using heColor
      apply heComp
      let H := TwoColorIncidenceGraph G phi gamma delta
      have hadj : H.Adj (Sum.inl w) (Sum.inr e) := by
        simpa [H, TwoColorIncidenceGraph] using
          And.intro heIncident (Or.inl heGamma)
      change H.connectedComponentMk (Sum.inr e) =
        H.connectedComponentMk (Sum.inl w)
      exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
        hadj).symm
  have slot_class (a : Fin trace.steps) : trace.slot a ∈ S (trace.support a) := by
    simp only [S, ExtensionBaseSupportClass, Finset.mem_filter]
    exact ⟨slot_active a, trace.chosenVertex a⟩
  have initial_state (b : Fin trace.steps) :
      trace.gamma b ∈ PresentColors G sigmaN (trace.support b) ∧
      ((∀ c : Fin trace.steps, c.val < b.val →
          trace.support c ≠ trace.support b) →
        trace.delta b ∈ MissingColors G sigmaN (trace.support b)) := by
    let C := Finset.univ.filter fun c : Fin trace.steps =>
      trace.support c = trace.support b
    have hbC : b ∈ C := by simp [C]
    let m : Fin trace.steps := C.min' ⟨b, hbC⟩
    have hmC : m ∈ C := Finset.min'_mem C ⟨b, hbC⟩
    have hmSupport : trace.support m = trace.support b :=
      (Finset.mem_filter.mp hmC).2
    have hmle : m.val ≤ b.val := by
      simpa using Finset.min'_le C b hbC
    have hmhead : ∀ c : Fin trace.steps, c.val < m.val →
        trace.support c ≠ trace.support m := by
      intro c hcm hcs
      have hcC : c ∈ C := by
        simp only [C, Finset.mem_filter, Finset.mem_univ, true_and]
        exact hcs.trans hmSupport
      have hmc : m.val ≤ c.val := by
        simpa using Finset.min'_le C c hcC
      omega
    have hgreatest :
        ∀ s : Fin ett.rounds, s ∈ S (trace.support b) →
          s.val ≤ (trace.slot m).val := by
      intro s hs
      have hsL := class_subset b hs
      have hsImage : s ∈ Finset.univ.image trace.slot := by
        rw [trace.enumerates]
        exact hsL
      rcases Finset.mem_image.mp hsImage with ⟨c, -, hc⟩
      have hcsupport : trace.support c = trace.support b := by
        have hsChosen := (Finset.mem_filter.mp hs).2
        apply Option.some.inj
        rw [← trace.chosenVertex c, hc]
        exact hsChosen
      rcases lt_trichotomy c.val m.val with hcm | hcm | hmc
      · exact False.elim (hmhead c hcm (hcsupport.trans hmSupport.symm))
      · have hceq : c = m := Fin.ext hcm
        subst c
        exact Nat.le_of_eq (congrArg Fin.val hc.symm)
      · have hd := trace.strictlyDescending m c hmc
        simpa [hc] using Nat.le_of_lt hd
    have hmClass : trace.slot m ∈ S (trace.support b) := by
      simpa [hmSupport] using slot_class m
    have hinter :=
      hclassMissing (trace.support b) (trace.slot m) (trace.delta m)
        (class_subset b) hmClass hgreatest (trace.deltaField m)
    have hgammaUnion : trace.gamma b ∈
        (S (trace.support b)).biUnion
          (fun s => ett.series.data.stored s.succ) := by
      rw [Finset.mem_biUnion]
      refine ⟨trace.slot b, slot_class b, ?_⟩
      rw [stored_pair b]
      simp
    have hdeltaUnion : trace.delta m ∈
        (S (trace.support b)).biUnion
          (fun s => ett.series.data.stored s.succ) := by
      rw [Finset.mem_biUnion]
      refine ⟨trace.slot m, hmClass, ?_⟩
      rw [stored_pair m]
      simp
    have hgammaNe : trace.gamma b ≠ trace.delta m := by
      intro heq
      rcases lt_or_eq_of_le hmle with hmb | hmb
      · have rel := pair_relation m b hmb
        have hnonempty : (({trace.gamma b, trace.delta b} :
            Finset (Fin k)) ∩ {trace.gamma m, trace.delta m}).Nonempty := by
          refine ⟨trace.gamma b, ?_⟩
          simp [heq]
        have hmem : trace.gamma b ∈ ({trace.delta b} : Finset (Fin k)) := by
          rw [← (rel.2 hnonempty).2]
          simp [heq]
        exact pair_ne b (by simpa using hmem)
      · have hmb' : m = b := Fin.ext hmb
        rw [hmb'] at heq
        exact pair_ne b heq
    have hgammaPresent : trace.gamma b ∈ PresentColors G sigmaN
        (trace.support b) := by
      by_contra hnot
      have hmissing : trace.gamma b ∈ MissingColors G sigmaN
          (trace.support b) := by
        simp only [MissingColors, Finset.mem_sdiff, Finset.mem_univ, true_and]
        exact hnot
      have hmem : trace.gamma b ∈
          MissingColors G sigmaN (trace.support b) ∩
            (S (trace.support b)).biUnion
              (fun s => ett.series.data.stored s.succ) :=
        Finset.mem_inter.mpr ⟨hmissing, hgammaUnion⟩
      rw [hinter] at hmem
      exact hgammaNe (by simpa using hmem)
    refine ⟨hgammaPresent, ?_⟩
    intro hhead
    have hmb : m = b := by
      apply Fin.ext
      apply Nat.le_antisymm hmle
      by_contra hnot
      have hlt : m.val < b.val := by omega
      exact hhead m hlt hmSupport
    rw [hmb] at hinter
    have hmem : trace.delta b ∈
        MissingColors G sigmaN (trace.support b) ∩
          (S (trace.support b)).biUnion
            (fun s => ett.series.data.stored s.succ) := by
      rw [hinter]
      simp
    exact (Finset.mem_inter.mp hmem).1
  have state : ∀ n : Fin (trace.steps + 1),
      ∀ b : Fin trace.steps, n.val ≤ b.val →
        trace.gamma b ∈ PresentColors G (trace.coloring n) (trace.support b) ∧
        ((∀ c : Fin trace.steps, n.val ≤ c.val → c.val < b.val →
            trace.support c ≠ trace.support b) →
          trace.delta b ∈ MissingColors G (trace.coloring n) (trace.support b)) := by
    intro n
    induction n using Fin.induction with
    | zero =>
        intro b hb
        have hs := initial_state b
        rw [trace.initialColoring]
        refine ⟨hs.1, ?_⟩
        intro hhead
        apply hs.2
        intro c hcb
        exact hhead c (by simp) hcb
    | succ a ih =>
        intro b hab
        have hab' : a.val < b.val := by
          change a.val + 1 ≤ b.val at hab
          omega
        have old := ih b (by
          change a.val ≤ b.val
          omega)
        have rel := pair_relation a b hab'
        have hgammaOutside : trace.gamma b ≠ trace.gamma a ∧
            trace.gamma b ≠ trace.delta a := by
          constructor <;> intro heq
          · have hnonempty : (({trace.gamma b, trace.delta b} :
                Finset (Fin k)) ∩ {trace.gamma a, trace.delta a}).Nonempty := by
              refine ⟨trace.gamma b, ?_⟩
              simp [heq]
            have hmem : trace.gamma b ∈
                ({trace.delta b} : Finset (Fin k)) := by
              rw [← (rel.2 hnonempty).2]
              simp [heq]
            exact pair_ne b (by simpa using hmem)
          · have hnonempty : (({trace.gamma b, trace.delta b} :
                Finset (Fin k)) ∩ {trace.gamma a, trace.delta a}).Nonempty := by
              refine ⟨trace.gamma b, ?_⟩
              simp [heq]
            have hmem : trace.gamma b ∈
                ({trace.delta b} : Finset (Fin k)) := by
              rw [← (rel.2 hnonempty).2]
              simp [heq]
            exact pair_ne b (by simpa using hmem)
        have hgammaNext : trace.gamma b ∈
            PresentColors G (trace.coloring a.succ) (trace.support b) := by
          rw [trace.transition a]
          exact (swap_present_iff (trace.coloring a.castSucc)
            (trace.gamma a) (trace.delta a) (trace.gamma b)
            (Sum.inl (trace.support a)) (trace.support b)
            hgammaOutside.1 hgammaOutside.2).mpr old.1
        refine ⟨hgammaNext, ?_⟩
        intro hhead
        by_cases hsupport : trace.support b = trace.support a
        · have hnone : ¬ ∃ c : Fin trace.steps,
              a.val < c.val ∧ c.val < b.val ∧
                trace.support c = trace.support a := by
            rintro ⟨c, hac, hcb, hcs⟩
            exact hhead c (by change a.val + 1 ≤ c.val; omega) hcb
              (hcs.trans hsupport.symm)
          have hnonempty : (({trace.gamma b, trace.delta b} :
              Finset (Fin k)) ∩ {trace.gamma a, trace.delta a}).Nonempty := by
            rw [rel.1]
            exact ⟨hsupport, hnone⟩
          have hchain : trace.gamma a = trace.delta b := by
            have hsingle : ({trace.gamma a} : Finset (Fin k)) =
                {trace.delta b} := (rel.2 hnonempty).1.symm.trans
              (rel.2 hnonempty).2
            simpa using hsingle
          have hcurrent := ih a (le_refl a.val)
          have hdeltaA : trace.delta a ∈
              MissingColors G (trace.coloring a.castSucc) (trace.support a) := by
            apply hcurrent.2
            intro c hac hca
            change a.val ≤ c.val at hac
            omega
          have hgammaAfter := root_swap_gamma_missing
            (trace.coloring a.castSucc) (trace.gamma a) (trace.delta a)
            (trace.support a) (pair_ne a) hdeltaA
          rw [trace.transition a]
          simpa [hsupport, hchain] using hgammaAfter
        · have hheadOld : ∀ c : Fin trace.steps,
              a.val ≤ c.val → c.val < b.val →
                trace.support c ≠ trace.support b := by
            intro c hac hcb hcs
            by_cases hca : c = a
            · subst c
              exact hsupport hcs.symm
            · apply hhead c
              · change a.val + 1 ≤ c.val
                omega
              · exact hcb
              · exact hcs
          have hdeltaOld := old.2 hheadOld
          have hinterEmpty :
              ({trace.gamma b, trace.delta b} : Finset (Fin k)) ∩
                {trace.gamma a, trace.delta a} = ∅ := by
            apply Finset.not_nonempty_iff_eq_empty.mp
            rw [rel.1]
            simp [hsupport]
          have hdeltaOutside : trace.delta b ≠ trace.gamma a ∧
              trace.delta b ≠ trace.delta a := by
            constructor <;> intro heq
            · have : trace.delta b ∈
                  ({trace.gamma b, trace.delta b} : Finset (Fin k)) ∩
                    {trace.gamma a, trace.delta a} := by
                simp [heq]
              rw [hinterEmpty] at this
              simp at this
            · have : trace.delta b ∈
                  ({trace.gamma b, trace.delta b} : Finset (Fin k)) ∩
                    {trace.gamma a, trace.delta a} := by
                simp [heq]
              rw [hinterEmpty] at this
              simp at this
          rw [trace.transition a]
          exact (swap_missing_iff (trace.coloring a.castSucc)
            (trace.gamma a) (trace.delta a) (trace.delta b)
            (Sum.inl (trace.support a)) (trace.support b)
            hdeltaOutside.1 hdeltaOutside.2).mpr hdeltaOld
  intro a
  have hs := state a.castSucc a (le_refl a.val)
  refine ⟨?_, hs.1⟩
  apply hs.2
  intro c hac hca
  change a.val ≤ c.val at hac
  omega
