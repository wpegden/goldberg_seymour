import Tablet.ExtensionBaseSupportClass
import Tablet.ExtensionBaseSupportClassColors
import Tablet.TashkinovSeries
import Tablet.TashkinovSeriesStep

-- [TABLET NODE: ExtensionBaseSameSupportStoredPairOverlap]
theorem ExtensionBaseSameSupportStoredPairOverlap {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    {input : PartialEdgeColoring E k} {T : TreeSequence G e0}
    {generating : PartialEdgeColoring E k}
    (ett : ExtendedTashkinovTree G k e0 input T generating)
    (terminalSupport : V)
    (hterminalSupport : terminalSupport ∈ TreeSequenceVertexSet T)
    (q : Fin ett.rounds) (hqTerminal : q.val + 1 = ett.rounds)
    (w : V)
    (hw : w ∈ TreeSequenceVertexSet
      (ett.series.data.tree q.succ.castSucc))
    (p : ℕ) (indices : Fin (p + 1) → Fin ett.rounds)
    (hincreasing : ∀ a b, a.val < b.val →
      (indices a).val < (indices b).val)
    (hclass : ∀ r : Fin ett.rounds,
      r ∈ ExtensionBaseSupportClass ett terminalSupport hterminalSupport w ↔
        ∃ a : Fin (p + 1), indices a = r)
    (henumerates : ∀ r : Fin ett.rounds,
      (r.val ≤ q.val ∧
        ett.series.data.kind r.succ = some TashkinovExtensionKind.PE ∧
        ett.series.data.chosenVertex r.succ = some w) ↔
      ∃ a : Fin (p + 1), indices a = r)
    (hdeltaAvoidsEarlierGamma : ∀ (a b : Fin (p + 1))
      (gammaA deltaB : Fin k), a.val ≤ b.val →
      ett.series.data.gamma (indices a).succ = some gammaA →
      ett.series.data.delta (indices b).succ = some deltaB →
      deltaB ≠ gammaA)
    (s t : Fin ett.rounds)
    (hsClass : s ∈ ExtensionBaseSupportClass ett terminalSupport
      hterminalSupport w)
    (htClass : t ∈ ExtensionBaseSupportClass ett terminalSupport
      hterminalSupport w)
    (hst : s.val < t.val)
    (gammaS deltaS gammaT deltaT : Fin k)
    (hsGamma : ett.series.data.gamma s.succ = some gammaS)
    (hsDelta : ett.series.data.delta s.succ = some deltaS)
    (htGamma : ett.series.data.gamma t.succ = some gammaT)
    (htDelta : ett.series.data.delta t.succ = some deltaT) :
    ((ett.series.data.stored s.succ ∩
        ett.series.data.stored t.succ).Nonempty ↔
      ¬ ∃ r : Fin ett.rounds,
        r ∈ ExtensionBaseSupportClass ett terminalSupport
          hterminalSupport w ∧
        s.val < r.val ∧ r.val < t.val) ∧
    ((ett.series.data.stored s.succ ∩
        ett.series.data.stored t.succ).Nonempty →
      ett.series.data.stored s.succ ∩
          ett.series.data.stored t.succ = {gammaT} ∧
        ett.series.data.stored s.succ ∩
          ett.series.data.stored t.succ = {deltaS}) := by
-- BODY
  classical
  have slotFacts : ∀ a : Fin (p + 1),
      ∃ ga da : Fin k,
        ett.series.data.gamma (indices a).succ = some ga ∧
        ett.series.data.delta (indices a).succ = some da ∧
        ett.series.data.stored (indices a).succ = {da, ga} := by
    intro a
    have hr := (henumerates (indices a)).2 ⟨a, rfl⟩
    rcases hr with ⟨hle, hkind, hvertex⟩
    let z := (indices a).succ
    generalize hzi : (indices a).succ = z at hkind hvertex ⊢
    have hstep := ett.series.certified z
    cases hstep with
    | initial triple seedLength initialColoring initialStored initialEdges
        initialKind initialVertex initialOutside initialDelta initialGamma
        initialClosure =>
        simp [initialKind] at hkind
    | SE i previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed noRevisiting choice seriesAlternative
        currentColoring currentStored currentEdges currentKind currentVertex
        currentOutside currentDelta currentGamma adjoined adjoinedExactly
        closedExtension orderedExtension strictExtension =>
        simp [currentKind] at hkind
    | PE i previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed noRevisiting choice seriesAlternativeFails
        ga gammaRule secondStable secondStableProper secondStableOneUncolored
        secondStableRelation exitWitness currentColoring currentProper
        currentOneUncolored currentStored currentEdges currentKind currentVertex
        currentOutside currentDelta currentGamma closedExtension
        orderedExtension strictExtension =>
        exact ⟨ga, choice.color, currentGamma, currentDelta, currentStored⟩
    | RE i previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed available currentColoring currentStored
        currentEdges currentKind currentVertex currentOutside currentDelta
        currentGamma adjoined adjoinedExactly closedExtension orderedExtension
        strictExtension =>
        simp [currentKind] at hkind
  let gamma : Fin (p + 1) → Fin k := fun a => Classical.choose (slotFacts a)
  let delta : Fin (p + 1) → Fin k := fun a =>
    Classical.choose (Classical.choose_spec (slotFacts a))
  have hgamma : ∀ a, ett.series.data.gamma (indices a).succ = some (gamma a) := by
    intro a
    exact (Classical.choose_spec (Classical.choose_spec (slotFacts a))).1
  have hdelta : ∀ a, ett.series.data.delta (indices a).succ = some (delta a) := by
    intro a
    exact (Classical.choose_spec (Classical.choose_spec (slotFacts a))).2.1
  have hstored : ∀ a, ett.series.data.stored (indices a).succ =
      {delta a, gamma a} := by
    intro a
    exact (Classical.choose_spec (Classical.choose_spec (slotFacts a))).2.2
  have colors := ExtensionBaseSupportClassColors ett terminalSupport
    hterminalSupport q hqTerminal w hw p indices hincreasing hclass henumerates
    gamma delta hgamma hdelta (by
      intro x y hxy
      exact hdeltaAvoidsEarlierGamma x y (gamma x) (delta y) hxy
        (hgamma x) (hdelta y))
  have hsa : ∃ a : Fin (p + 1), indices a = s := (hclass s).1 hsClass
  have hta : ∃ a : Fin (p + 1), indices a = t := (hclass t).1 htClass
  rcases hsa with ⟨a, ha⟩
  rcases hta with ⟨b, hb⟩
  have hab : a.val < b.val := by
    have hst' : (indices a).val < (indices b).val := by simpa [ha, hb] using hst
    by_contra hn
    have hba : b.val ≤ a.val := Nat.le_of_not_gt hn
    rcases lt_or_eq_of_le hba with hlt | heq
    · exact (not_lt_of_ge (Nat.le_of_lt (hincreasing b a hlt)) hst').elim
    · have hab' : b = a := Fin.ext heq
      subst b
      exact (Nat.lt_irrefl _ hst').elim
  have hgap :
      (∃ r : Fin ett.rounds, r ∈ ExtensionBaseSupportClass ett
          terminalSupport hterminalSupport w ∧
        s.val < r.val ∧ r.val < t.val) ↔ a.val + 1 < b.val := by
    constructor
    · rintro ⟨r, hr, hsr, hrt⟩
      rcases (hclass r).1 hr with ⟨c, hc⟩
      have hsr' : (indices a).val < (indices c).val := by simpa [ha, hc] using hsr
      have hrt' : (indices c).val < (indices b).val := by simpa [hc, hb] using hrt
      have hac : a.val < c.val := by
        by_contra hn
        have hle : c.val ≤ a.val := Nat.le_of_not_gt hn
        rcases lt_or_eq_of_le hle with hlt | heq
        · exact (not_lt_of_ge (Nat.le_of_lt (hincreasing c a hlt)) hsr').elim
        · have hac' : c = a := Fin.ext heq
          subst c
          exact (Nat.lt_irrefl _ hsr').elim
      have hcb : c.val < b.val := by
        by_contra hn
        have hle : b.val ≤ c.val := Nat.le_of_not_gt hn
        rcases lt_or_eq_of_le hle with hlt | heq
        · exact (not_lt_of_ge (Nat.le_of_lt (hincreasing b c hlt)) hrt').elim
        · have hbc' : b = c := Fin.ext heq
          subst b
          exact (Nat.lt_irrefl _ hrt').elim
      omega
    · intro hgap
      let c : Fin (p + 1) := ⟨a.val + 1, by omega⟩
      have hac : a.val < c.val := by simp [c]
      have hcb : c.val < b.val := by simpa [c] using hgap
      refine ⟨indices c, (hclass _).2 ⟨c, rfl⟩, ?_, ?_⟩
      · rw [← ha]
        exact hincreasing a c hac
      · rw [← hb]
        exact hincreasing c b hcb
  have pairS : ett.series.data.stored s.succ = {delta a, gamma a} := by
    simpa [ha] using hstored a
  have pairT : ett.series.data.stored t.succ = {delta b, gamma b} := by
    simpa [hb] using hstored b
  have hgammaDelta : ∀ c : Fin p, gamma c.succ = delta c.castSucc :=
    colors.1
  have hinjective := colors.2
  have gammaCode : ∀ c : Fin (p + 1),
      gamma c = (Fin.cons (gamma 0) delta : Fin (p + 2) → Fin k)
        (⟨c.val, Nat.lt_succ_of_lt c.isLt⟩ : Fin (p + 2)) := by
    intro c
    refine Fin.cases ?_ (fun d => ?_) c
    · rfl
    · have hd := hgammaDelta d
      have hi : (⟨d.val + 1, Nat.lt_succ_of_lt (Nat.succ_lt_succ d.isLt)⟩ : Fin (p + 2)) =
          d.succ.castSucc := by
        apply Fin.ext
        rfl
      change gamma d.succ = delta d.castSucc
      exact hd
  have deltaCode : ∀ c : Fin (p + 1),
      delta c = (Fin.cons (gamma 0) delta : Fin (p + 2) → Fin k)
        (⟨c.val + 1, Nat.succ_lt_succ c.isLt⟩ : Fin (p + 2)) := by
    intro c
    rfl
  have pairDisjoint : a.val + 1 < b.val →
      Disjoint ({delta a, gamma a} : Finset (Fin k)) {delta b, gamma b} := by
    intro hgap'
    rw [Finset.disjoint_left]
    intro x hxa hxb
    have hxa' : x = delta a ∨ x = gamma a := by simpa using hxa
    have hxb' : x = delta b ∨ x = gamma b := by simpa using hxb
    rcases hxa' with hxa' | hxa' <;> rcases hxb' with hxb' | hxb'
    · subst x
      have he : (Fin.cons (gamma 0) delta : Fin (p + 2) → Fin k) a.succ =
          (Fin.cons (gamma 0) delta : Fin (p + 2) → Fin k) b.succ :=
        (deltaCode a).symm.trans (hxb'.trans (deltaCode b))
      have hv := congrArg Fin.val (hinjective he)
      simp at hv
      omega
    · subst x
      have he : (Fin.cons (gamma 0) delta : Fin (p + 2) → Fin k) a.succ =
          (Fin.cons (gamma 0) delta : Fin (p + 2) → Fin k) b.castSucc :=
        (deltaCode a).symm.trans (hxb'.trans (gammaCode b))
      have hv := congrArg Fin.val (hinjective he)
      simp at hv
      omega
    · subst x
      have he : (Fin.cons (gamma 0) delta : Fin (p + 2) → Fin k) a.castSucc =
          (Fin.cons (gamma 0) delta : Fin (p + 2) → Fin k) b.succ :=
        (gammaCode a).symm.trans (hxb'.trans (deltaCode b))
      have hv := congrArg Fin.val (hinjective he)
      simp at hv
      omega
    · subst x
      have he : (Fin.cons (gamma 0) delta : Fin (p + 2) → Fin k) a.castSucc =
          (Fin.cons (gamma 0) delta : Fin (p + 2) → Fin k) b.castSucc :=
        (gammaCode a).symm.trans (hxb'.trans (gammaCode b))
      have hv := congrArg Fin.val (hinjective he)
      simp at hv
      omega
  rw [pairS, pairT]
  have fieldsS : gamma a = gammaS ∧ delta a = deltaS := by
    have hg : ett.series.data.gamma (indices a).succ =
        ett.series.data.gamma s.succ := congrArg ett.series.data.gamma (congrArg Fin.succ ha)
    have hd : ett.series.data.delta (indices a).succ =
        ett.series.data.delta s.succ := congrArg ett.series.data.delta (congrArg Fin.succ ha)
    constructor
    · exact (Option.some.inj (hsGamma.symm.trans (hg.symm.trans (hgamma a)))).symm
    · exact (Option.some.inj (hsDelta.symm.trans (hd.symm.trans (hdelta a)))).symm
  have fieldsT : gamma b = gammaT ∧ delta b = deltaT := by
    have hg : ett.series.data.gamma (indices b).succ =
        ett.series.data.gamma t.succ := congrArg ett.series.data.gamma (congrArg Fin.succ hb)
    have hd : ett.series.data.delta (indices b).succ =
        ett.series.data.delta t.succ := congrArg ett.series.data.delta (congrArg Fin.succ hb)
    constructor
    · exact (Option.some.inj (htGamma.symm.trans (hg.symm.trans (hgamma b)))).symm
    · exact (Option.some.inj (htDelta.symm.trans (hd.symm.trans (hdelta b)))).symm
  by_cases hadj : a.val + 1 = b.val
  · have hb' : b.val = a.val + 1 := hadj.symm
    have hadjColor : gamma b = delta a := by
      let c : Fin p := ⟨a.val, by omega⟩
      have hc := hgammaDelta c
      have hcb : c.succ = b := by
        apply Fin.ext
        simp [c, hb']
      have hca : c.castSucc = a := by apply Fin.ext; rfl
      rw [← hcb, ← hca]
      exact hc
    have hno : ¬ ∃ r : Fin ett.rounds, r ∈ ExtensionBaseSupportClass ett
        terminalSupport hterminalSupport w ∧ s.val < r.val ∧ r.val < t.val := by
      intro hr
      exact (by omega : ¬ (a.val + 1 < b.val)) (hgap.mp hr)
    have hnot : delta b ≠ gamma a := by
      intro he
      exact hdeltaAvoidsEarlierGamma a b (gamma a) (delta b) hab.le
        (hgamma a) (hdelta b) he
    constructor
    · constructor
      · intro _
        exact hno
      · intro _
        exact ⟨gamma b, by simp [hadjColor]⟩
    · intro _
      have hgt : gammaT = delta a := fieldsT.1.symm.trans hadjColor
      have hds : deltaS = delta a := fieldsS.2.symm
      constructor
      · rw [hgt]
        ext x
        simp [hadjColor, hnot]
      · rw [hds]
        ext x
        simp [hadjColor, hnot]
  · have hgap' : a.val + 1 < b.val := by omega
    have hd := pairDisjoint hgap'
    have hex : ∃ r : Fin ett.rounds, r ∈ ExtensionBaseSupportClass ett
        terminalSupport hterminalSupport w ∧ s.val < r.val ∧ r.val < t.val :=
      hgap.mpr hgap'
    have hfalse : ¬ Finset.Nonempty ({delta a, gamma a} ∩ {delta b, gamma b}) := by
      intro h
      rcases h with ⟨x, hx⟩
      exact (Finset.disjoint_left.mp hd) (Finset.mem_inter.mp hx).1
        (Finset.mem_inter.mp hx).2
    constructor
    · constructor
      · intro h
        exact fun _ => hfalse h
      · intro h
        exact (h hex).elim
    · intro h
      exact (hfalse h).elim
