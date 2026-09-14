import Tablet.BoundaryEdges
import Tablet.InternalEdges
import Tablet.RevisitingExtensionCertificate
import Tablet.TashkinovSeries
import Tablet.TashkinovSeriesStep
import Tablet.TreeSequenceInitialSegmentVertexSetSubset
import Tablet.TwoColorCycle
import Tablet.TwoColorIncidenceGraph

open scoped Sym2

-- [TABLET NODE: EarlierPECycleFirstNonrevisitingInternal]
theorem EarlierPECycleFirstNonrevisitingInternal {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k rounds : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k)
    (series : TashkinovSeries G k rounds e0 input)
    (r : Fin rounds) (hrEarlier : r.succ ≠ Fin.last rounds)
    (gamma delta : Fin k)
    (hkindr : series.data.kind r.succ = some TashkinovExtensionKind.PE)
    (hgammar : series.data.gamma r.succ = some gamma)
    (hdeltar : series.data.delta r.succ = some delta)
    (cycle : TwoColorCycle G (series.data.coloring r.succ) gamma delta)
    (hmeets : ∃ v ∈ TreeSequenceVertexSet
        (series.data.tree r.succ.castSucc),
      Sum.inl v ∈ cycle.walk.support)
    (hterminal : series.data.kind (Fin.last rounds) =
      some TashkinovExtensionKind.PE) :
    ∃ p : Fin rounds,
      r.val < p.val ∧
      (series.data.kind p.succ = some TashkinovExtensionKind.SE ∨
        series.data.kind p.succ = some TashkinovExtensionKind.PE) ∧
      (∀ j : Fin rounds, r.val < j.val → j.val < p.val →
        series.data.kind j.succ = some TashkinovExtensionKind.RE) ∧
      series.data.coloring p.castSucc = series.data.coloring r.succ ∧
      ∀ f : E, Sum.inr f ∈ cycle.walk.support →
        f ∈ InternalEdges G
          (TreeSequenceVertexSet (series.data.tree p.succ.castSucc)) := by
-- BODY
  classical
  have hrTerminalLt : r.val + 1 < rounds := by
    have hrle : r.val + 1 ≤ rounds := by omega
    have hrne : r.val + 1 ≠ rounds := by
      intro h
      apply hrEarlier
      apply Fin.ext
      simpa using h
    omega
  let terminalIndex : Fin rounds := ⟨rounds - 1, by omega⟩
  have terminalIndexSucc : terminalIndex.succ = Fin.last rounds := by
    apply Fin.ext
    simp [terminalIndex]
    omega
  let candidates : Finset (Fin rounds) := Finset.univ.filter fun q =>
    r.val < q.val ∧
      series.data.kind q.succ ≠ some TashkinovExtensionKind.RE
  have terminalMem : terminalIndex ∈ candidates := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, by simp [terminalIndex]; omega, ?_⟩
    rw [terminalIndexSucc, hterminal]
    simp
  have candidatesNonempty : candidates.Nonempty := ⟨terminalIndex, terminalMem⟩
  let p : Fin rounds := candidates.min' candidatesNonempty
  have pMem : p ∈ candidates := Finset.min'_mem candidates candidatesNonempty
  have hrp : r.val < p.val := (Finset.mem_filter.mp pMem).2.1
  have pNotRE : series.data.kind p.succ ≠
      some TashkinovExtensionKind.RE := (Finset.mem_filter.mp pMem).2.2
  have betweenRE : ∀ j : Fin rounds, r.val < j.val → j.val < p.val →
      series.data.kind j.succ = some TashkinovExtensionKind.RE := by
    intro j hrj hjp
    by_contra hjNot
    have hjMem : j ∈ candidates := Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, hrj, hjNot⟩
    have hpj : p ≤ j := Finset.min'_le candidates j hjMem
    omega
  have pKind : series.data.kind p.succ = some TashkinovExtensionKind.SE ∨
      series.data.kind p.succ = some TashkinovExtensionKind.PE := by
    generalize hpSlot : p.succ = slot at pNotRE ⊢
    cases series.certified slot with
    | initial triple seedLength initialColoring initialStored initialEdges
        initialKind initialVertex initialOutside initialDelta initialGamma initialClosure =>
      exact (Fin.succ_ne_zero p hpSlot).elim
    | SE i previousProper previousOneUncolored previousClosed previousNotStronglyClosed
        noRevisiting choice seriesAlternative currentColoring currentStored currentEdges
        currentKind currentVertex currentOutside currentDelta currentGamma adjoined
        adjoinedExactly closedExtension orderedExtension strictExtension =>
      exact Or.inl (by simpa [hpSlot] using currentKind)
    | PE i previousProper previousOneUncolored previousClosed previousNotStronglyClosed
        noRevisiting choice seriesAlternativeFails actualGamma gammaRule secondStable
        secondStableProper secondStableOneUncolored secondStableRelation exitWitness
        currentColoring currentProper currentOneUncolored currentStored currentEdges
        currentKind currentVertex currentOutside currentDelta currentGamma closedExtension
        orderedExtension strictExtension =>
      exact Or.inr (by simpa [hpSlot] using currentKind)
    | RE i previousProper previousOneUncolored previousClosed previousNotStronglyClosed
        available currentColoring currentStored currentEdges currentKind currentVertex
        currentOutside currentDelta currentGamma adjoined adjoinedExactly closedExtension
        orderedExtension strictExtension =>
      exact False.elim (pNotRE (by simpa [hpSlot] using currentKind))
  have reColoring : ∀ j : Fin rounds,
      series.data.kind j.succ = some TashkinovExtensionKind.RE →
      series.data.coloring j.succ = series.data.coloring j.castSucc := by
    intro j hjKind
    generalize hjSlot : j.succ = slot at hjKind ⊢
    cases series.certified slot with
    | initial triple seedLength initialColoring initialStored initialEdges
        initialKind initialVertex initialOutside initialDelta initialGamma initialClosure =>
      exact (Fin.succ_ne_zero j hjSlot).elim
    | SE i previousProper previousOneUncolored previousClosed previousNotStronglyClosed
        noRevisiting choice seriesAlternative currentColoring currentStored currentEdges
        currentKind currentVertex currentOutside currentDelta currentGamma adjoined
        adjoinedExactly closedExtension orderedExtension strictExtension =>
      have : some TashkinovExtensionKind.SE = some TashkinovExtensionKind.RE :=
        currentKind.symm.trans (by simpa [hjSlot] using hjKind)
      cases this
    | PE i previousProper previousOneUncolored previousClosed previousNotStronglyClosed
        noRevisiting choice seriesAlternativeFails actualGamma gammaRule secondStable
        secondStableProper secondStableOneUncolored secondStableRelation exitWitness
        currentColoring currentProper currentOneUncolored currentStored currentEdges
        currentKind currentVertex currentOutside currentDelta currentGamma closedExtension
        orderedExtension strictExtension =>
      have : some TashkinovExtensionKind.PE = some TashkinovExtensionKind.RE :=
        currentKind.symm.trans (by simpa [hjSlot] using hjKind)
      cases this
    | RE i previousProper previousOneUncolored previousClosed previousNotStronglyClosed
        available currentColoring currentStored currentEdges currentKind currentVertex
        currentOutside currentDelta currentGamma adjoined adjoinedExactly closedExtension
        orderedExtension strictExtension =>
      have hi : i = j := by
        apply Fin.ext
        have := congrArg Fin.val hjSlot
        simp only [Fin.val_succ] at this
        omega
      subst i
      simpa [hjSlot] using currentColoring
  have coloringAlong : ∀ n : ℕ, r.val + 1 ≤ n → n ≤ p.val →
      ∀ q : Fin (rounds + 1), q.val = n →
        series.data.coloring q = series.data.coloring r.succ := by
    intro n hrn
    induction n, hrn using Nat.le_induction with
    | base =>
      intro hnp q hq
      have hqr : q = r.succ := by
        apply Fin.ext
        simp only [Fin.val_succ]
        omega
      simpa [hqr]
    | succ n hn ih =>
      intro hnp q hq
      have hnltp : n < p.val := by omega
      have hnr : r.val < n := by omega
      let j : Fin rounds := ⟨n, by omega⟩
      have hjKind := betweenRE j (by simpa [j]) (by simpa [j])
      have hjColor := reColoring j hjKind
      have hqSucc : q = j.succ := by
        apply Fin.ext
        simp [j, hq]
      have hjCast : j.castSucc.val = n := by simp [j]
      calc
        series.data.coloring q = series.data.coloring j.succ := by rw [hqSucc]
        _ = series.data.coloring j.castSucc := hjColor
        _ = series.data.coloring r.succ := ih (by omega) j.castSucc hjCast
  have pColoring : series.data.coloring p.castSucc =
      series.data.coloring r.succ := by
    exact coloringAlong p.val (by omega) (by omega) p.castSucc rfl
  let cycleP : TwoColorCycle G (series.data.coloring p.castSucc) gamma delta :=
    pColoring.symm ▸ cycle
  have transportedCycleSupport : ∀ (phi psi : PartialEdgeColoring E k)
      (h : phi = psi) (c : TwoColorCycle G psi gamma delta),
      (h.symm ▸ c).walk.support = c.walk.support := by
    intro phi psi h c
    cases h
    rfl
  have cyclePSupport : cycleP.walk.support = cycle.walk.support := by
    exact transportedCycleSupport _ _ pColoring cycle
  have stepVertexSubset : ∀ j : Fin rounds,
      TreeSequenceVertexSet (series.data.tree j.succ.castSucc) ⊆
        TreeSequenceVertexSet (series.data.tree j.succ.succ) := by
    intro j
    generalize hjSlot : j.succ = slot
    cases series.certified slot with
    | initial triple seedLength initialColoring initialStored initialEdges
        initialKind initialVertex initialOutside initialDelta initialGamma initialClosure =>
      exact (Fin.succ_ne_zero j hjSlot).elim
    | SE i previousProper previousOneUncolored previousClosed previousNotStronglyClosed
        noRevisiting choice seriesAlternative currentColoring currentStored currentEdges
        currentKind currentVertex currentOutside currentDelta currentGamma adjoined
        adjoinedExactly closedExtension orderedExtension strictExtension =>
      have hi : i = j := by
        apply Fin.ext
        have := congrArg Fin.val hjSlot
        simp only [Fin.val_succ] at this
        omega
      subst i
      exact TreeSequenceInitialSegmentVertexSetSubset (by simpa [hjSlot] using orderedExtension)
    | PE i previousProper previousOneUncolored previousClosed previousNotStronglyClosed
        noRevisiting choice seriesAlternativeFails actualGamma gammaRule secondStable
        secondStableProper secondStableOneUncolored secondStableRelation exitWitness
        currentColoring currentProper currentOneUncolored currentStored currentEdges
        currentKind currentVertex currentOutside currentDelta currentGamma closedExtension
        orderedExtension strictExtension =>
      have hi : i = j := by
        apply Fin.ext
        have := congrArg Fin.val hjSlot
        simp only [Fin.val_succ] at this
        omega
      subst i
      exact TreeSequenceInitialSegmentVertexSetSubset (by simpa [hjSlot] using orderedExtension)
    | RE i previousProper previousOneUncolored previousClosed previousNotStronglyClosed
        available currentColoring currentStored currentEdges currentKind currentVertex
        currentOutside currentDelta currentGamma adjoined adjoinedExactly closedExtension
        orderedExtension strictExtension =>
      have hi : i = j := by
        apply Fin.ext
        have := congrArg Fin.val hjSlot
        simp only [Fin.val_succ] at this
        omega
      subst i
      exact TreeSequenceInitialSegmentVertexSetSubset (by simpa [hjSlot] using orderedExtension)
  have treeAlong : ∀ n : ℕ, r.val ≤ n → n ≤ p.val →
      ∀ q : Fin rounds, q.val = n →
        TreeSequenceVertexSet (series.data.tree r.succ.castSucc) ⊆
          TreeSequenceVertexSet (series.data.tree q.succ.castSucc) := by
    intro n hrn
    induction n, hrn using Nat.le_induction with
    | base =>
      intro hnp q hq
      have hqr : q = r := by apply Fin.ext; omega
      simpa [hqr]
    | succ n hn ih =>
      intro hnp q hq
      let prev : Fin rounds := ⟨n, by omega⟩
      have hprev := ih (by omega) prev rfl
      have hstep := stepVertexSubset prev
      have htree : prev.succ.succ = q.succ.castSucc := by
        apply Fin.ext
        simp [prev, hq]
      simpa [htree] using Set.Subset.trans hprev hstep
  have treeSubset : TreeSequenceVertexSet (series.data.tree r.succ.castSucc) ⊆
      TreeSequenceVertexSet (series.data.tree p.succ.castSucc) :=
    treeAlong p.val (by omega) (by omega) p rfl
  have pNoRevisiting : ¬ Nonempty
      (RevisitingExtensionCertificate series.data p.castSucc) := by
    generalize hpSlot : p.succ = slot
    cases series.certified slot with
    | initial triple seedLength initialColoring initialStored initialEdges
        initialKind initialVertex initialOutside initialDelta initialGamma initialClosure =>
      exact (Fin.succ_ne_zero p hpSlot).elim
    | SE i previousProper previousOneUncolored previousClosed previousNotStronglyClosed
        noRevisiting choice seriesAlternative currentColoring currentStored currentEdges
        currentKind currentVertex currentOutside currentDelta currentGamma adjoined
        adjoinedExactly closedExtension orderedExtension strictExtension =>
      have hi : i = p := by
        apply Fin.ext
        have := congrArg Fin.val hpSlot
        simp only [Fin.val_succ] at this
        omega
      subst i
      simpa using noRevisiting
    | PE i previousProper previousOneUncolored previousClosed previousNotStronglyClosed
        noRevisiting choice seriesAlternativeFails actualGamma gammaRule secondStable
        secondStableProper secondStableOneUncolored secondStableRelation exitWitness
        currentColoring currentProper currentOneUncolored currentStored currentEdges
        currentKind currentVertex currentOutside currentDelta currentGamma closedExtension
        orderedExtension strictExtension =>
      have hi : i = p := by
        apply Fin.ext
        have := congrArg Fin.val hpSlot
        simp only [Fin.val_succ] at this
        omega
      subst i
      simpa using noRevisiting
    | RE i previousProper previousOneUncolored previousClosed previousNotStronglyClosed
        available currentColoring currentStored currentEdges currentKind currentVertex
        currentOutside currentDelta currentGamma adjoined adjoinedExactly closedExtension
        orderedExtension strictExtension =>
      have hRE : series.data.kind p.succ = some TashkinovExtensionKind.RE := by
        simpa [hpSlot] using currentKind
      exact False.elim (pNotRE hRE)
  refine ⟨p, hrp, pKind, betweenRE, pColoring, ?_⟩
  intro f hfCycle
  by_contra hfNotInternal
  have hfCycleP : Sum.inr f ∈ cycleP.walk.support := by
    rw [cyclePSupport]
    exact hfCycle
  have edgeIdentity : ∀ {z : Sym2 V} {a b : V}, a ∈ z → b ∈ z → a ≠ b →
      z = s(a, b) := by
    intro z a b ha hb hab
    induction z using Sym2.inductionOn with
    | _ c d =>
      simp only [Sym2.mem_iff] at ha hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp_all
  let edgeCycle := cycleP.walk.rotate (Sum.inr f) hfCycleP
  have edgeCycleIsCycle : edgeCycle.IsCycle := by
    exact cycleP.isCycle.rotate hfCycleP
  have edgeCycleLength : 3 ≤ edgeCycle.length := edgeCycleIsCycle.three_le_length
  have firstAdj := edgeCycle.adj_getVert_succ (i := 0) (by omega)
  have firstVertex : ∃ a : V, edgeCycle.getVert 1 = Sum.inl a := by
    cases hfirst : edgeCycle.getVert 1 with
    | inl a => exact ⟨a, rfl⟩
    | inr e =>
      exfalso
      rw [edgeCycle.getVert_zero, hfirst] at firstAdj
      simpa [TwoColorIncidenceGraph] using firstAdj
  obtain ⟨a, ha⟩ := firstVertex
  have hfa : Incident G a f := by
    rw [edgeCycle.getVert_zero, ha] at firstAdj
    simpa [edgeCycle, TwoColorIncidenceGraph] using firstAdj.1
  have lastAdj := edgeCycle.adj_getVert_succ
    (i := edgeCycle.length - 1) (by omega)
  have lastVertex : ∃ b : V,
      edgeCycle.getVert (edgeCycle.length - 1) = Sum.inl b := by
    cases hlast : edgeCycle.getVert (edgeCycle.length - 1) with
    | inl b => exact ⟨b, rfl⟩
    | inr e =>
      exfalso
      have hidx : edgeCycle.length - 1 + 1 = edgeCycle.length := by omega
      rw [hidx, edgeCycle.getVert_length, hlast] at lastAdj
      simpa [TwoColorIncidenceGraph] using lastAdj
  obtain ⟨b, hb⟩ := lastVertex
  have hfb : Incident G b f := by
    have hidx : edgeCycle.length - 1 + 1 = edgeCycle.length := by omega
    rw [hidx, edgeCycle.getVert_length, hb] at lastAdj
    simpa [edgeCycle, TwoColorIncidenceGraph] using lastAdj.1
  have hab : a ≠ b := by
    intro habEq
    apply edgeCycleIsCycle.snd_ne_penultimate
    rw [show edgeCycle.snd = Sum.inl a by simpa using ha]
    rw [show edgeCycle.penultimate = Sum.inl b by simpa using hb]
    exact congrArg Sum.inl habEq
  have hfEndsAB : G.ends f = s(a, b) :=
    edgeIdentity (by simpa [Incident] using hfa) (by simpa [Incident] using hfb) hab
  let currentTree := TreeSequenceVertexSet (series.data.tree p.succ.castSucc)
  have outsideOnCycle : ∃ y : V, y ∉ currentTree ∧ Sum.inl y ∈ cycleP.walk.support := by
    by_cases haCurrent : a ∈ currentTree
    · have hbOutside : b ∉ currentTree := by
        intro hbCurrent
        apply hfNotInternal
        simp only [InternalEdges, Finset.mem_filter, Finset.mem_univ, true_and]
        intro v hv
        have hvEnds : v ∈ G.ends f := by simpa [Incident] using hv
        rw [hfEndsAB] at hvEnds
        rcases (by simpa only [Sym2.mem_iff] using hvEnds) with rfl | rfl
        · exact haCurrent
        · exact hbCurrent
      refine ⟨b, hbOutside, ?_⟩
      apply (cycleP.walk.mem_support_rotate_iff (Sum.inr f) hfCycleP).mp
      change Sum.inl b ∈ edgeCycle.support
      rw [← hb]
      exact edgeCycle.getVert_mem_support (edgeCycle.length - 1)
    · refine ⟨a, haCurrent, ?_⟩
      apply (cycleP.walk.mem_support_rotate_iff (Sum.inr f) hfCycleP).mp
      change Sum.inl a ∈ edgeCycle.support
      rw [← ha]
      exact edgeCycle.getVert_mem_support 1
  obtain ⟨v0, hv0Earlier, hv0Cycle⟩ := hmeets
  have hv0CycleP : Sum.inl v0 ∈ cycleP.walk.support := by
    rw [cyclePSupport]
    exact hv0Cycle
  have hv0Current : v0 ∈ currentTree := treeSubset hv0Earlier
  obtain ⟨outsideVertex, outsideVertexNotCurrent, outsideVertexCycle⟩ := outsideOnCycle
  let rootedCycle := cycleP.walk.rotate (Sum.inl v0) hv0CycleP
  have rootedIsCycle : rootedCycle.IsCycle := cycleP.isCycle.rotate hv0CycleP
  have outsideVertexRooted : Sum.inl outsideVertex ∈ rootedCycle.support := by
    apply (cycleP.walk.mem_support_rotate_iff (Sum.inl v0) hv0CycleP).mpr
    exact outsideVertexCycle
  let outsideIndices : Finset (Fin (rootedCycle.length + 1)) :=
    Finset.univ.filter fun i => ∃ v : V,
      rootedCycle.getVert i.val = Sum.inl v ∧ v ∉ currentTree
  have outsideIndicesNonempty : outsideIndices.Nonempty := by
    obtain ⟨n, hn, hnle⟩ :=
      SimpleGraph.Walk.mem_support_iff_exists_getVert.mp outsideVertexRooted
    let i : Fin (rootedCycle.length + 1) := ⟨n, by omega⟩
    refine ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    exact ⟨outsideVertex, by simpa [i] using hn, outsideVertexNotCurrent⟩
  let firstOutside : Fin (rootedCycle.length + 1) :=
    outsideIndices.min' outsideIndicesNonempty
  have firstOutsideSpec : ∃ y : V,
      rootedCycle.getVert firstOutside.val = Sum.inl y ∧ y ∉ currentTree :=
    (Finset.mem_filter.mp
      (Finset.min'_mem outsideIndices outsideIndicesNonempty)).2
  obtain ⟨y, hyAt, hyOutside⟩ := firstOutsideSpec
  have beforeFirstOutside : ∀ i : Fin (rootedCycle.length + 1),
      i.val < firstOutside.val → ∀ v : V,
        rootedCycle.getVert i.val = Sum.inl v → v ∈ currentTree := by
    intro i hi v hv
    by_contra hvOutside
    have hiMem : i ∈ outsideIndices := Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, ⟨v, hv, hvOutside⟩⟩
    have hmin := Finset.min'_le outsideIndices i hiMem
    omega
  have firstOutsidePositive : 0 < firstOutside.val := by
    by_contra hnot
    have hiZero : firstOutside.val = 0 := by omega
    have hyv0 : y = v0 := by
      apply Sum.inl.inj
      calc
        Sum.inl y = rootedCycle.getVert firstOutside.val := hyAt.symm
        _ = rootedCycle.getVert 0 := by rw [hiZero]
        _ = Sum.inl v0 := rootedCycle.getVert_zero
    exact hyOutside (hyv0.symm ▸ hv0Current)
  have firstOutsideLt : firstOutside.val < rootedCycle.length := by
    by_contra hnot
    have hiLast : firstOutside.val = rootedCycle.length := by
      have := firstOutside.isLt
      omega
    have hyv0 : y = v0 := by
      apply Sum.inl.inj
      calc
        Sum.inl y = rootedCycle.getVert firstOutside.val := hyAt.symm
        _ = rootedCycle.getVert rootedCycle.length := by rw [hiLast]
        _ = Sum.inl v0 := rootedCycle.getVert_length
    exact hyOutside (hyv0.symm ▸ hv0Current)
  have firstOutsideNotOne : firstOutside.val ≠ 1 := by
    intro hiOne
    have hAdj := rootedCycle.adj_getVert_succ (i := 0) (by omega)
    have hyOne : rootedCycle.getVert 1 = Sum.inl y := by
      simpa [hiOne] using hyAt
    rw [rootedCycle.getVert_zero, hyOne] at hAdj
    simpa [TwoColorIncidenceGraph] using hAdj
  have firstOutsideAtLeastTwo : 2 ≤ firstOutside.val := by omega
  have crossingAdj := rootedCycle.adj_getVert_succ
    (i := firstOutside.val - 1) (by omega)
  have crossingIndex : firstOutside.val - 1 + 1 = firstOutside.val := by omega
  have crossingEdge : ∃ g : E,
      rootedCycle.getVert (firstOutside.val - 1) = Sum.inr g := by
    cases hnode : rootedCycle.getVert (firstOutside.val - 1) with
    | inl v =>
      exfalso
      rw [crossingIndex, hyAt, hnode] at crossingAdj
      simpa [TwoColorIncidenceGraph] using crossingAdj
    | inr g => exact ⟨g, rfl⟩
  obtain ⟨g, hgAt⟩ := crossingEdge
  have hgy : Incident G y g := by
    rw [crossingIndex, hyAt, hgAt] at crossingAdj
    simpa [TwoColorIncidenceGraph] using crossingAdj.1
  have beforeCrossingAdj := rootedCycle.adj_getVert_succ
    (i := firstOutside.val - 2) (by omega)
  have beforeCrossingIndex : firstOutside.val - 2 + 1 =
      firstOutside.val - 1 := by omega
  have insideVertex : ∃ x : V,
      rootedCycle.getVert (firstOutside.val - 2) = Sum.inl x := by
    cases hnode : rootedCycle.getVert (firstOutside.val - 2) with
    | inl x => exact ⟨x, rfl⟩
    | inr e =>
      exfalso
      rw [beforeCrossingIndex, hgAt, hnode] at beforeCrossingAdj
      simpa [TwoColorIncidenceGraph] using beforeCrossingAdj
  obtain ⟨x, hxAt⟩ := insideVertex
  have hxCurrent : x ∈ currentTree := by
    apply beforeFirstOutside
      (⟨firstOutside.val - 2, Nat.lt_succ_of_le
        ((Nat.sub_le _ _).trans (Nat.le_of_lt firstOutsideLt))⟩ :
          Fin (rootedCycle.length + 1))
      (show firstOutside.val - 2 < firstOutside.val by omega) x
    simpa using hxAt
  have hxg : Incident G x g := by
    rw [beforeCrossingIndex, hgAt, hxAt] at beforeCrossingAdj
    simpa [TwoColorIncidenceGraph] using beforeCrossingAdj.1
  have hxy : x ≠ y := by
    intro h
    exact hyOutside (h ▸ hxCurrent)
  have hgEnds : G.ends g = s(x, y) :=
    edgeIdentity (by simpa [Incident] using hxg) (by simpa [Incident] using hgy) hxy
  have hgBoundary : g ∈ BoundaryEdges G currentTree := by
    simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨x, hxCurrent, y, hyOutside, hgEnds⟩
  have hgRooted : Sum.inr g ∈ rootedCycle.support := by
    rw [← hgAt]
    exact rootedCycle.getVert_mem_support (firstOutside.val - 1)
  have hgCycleP : Sum.inr g ∈ cycleP.walk.support := by
    apply (cycleP.walk.mem_support_rotate_iff (Sum.inl v0) hv0CycleP).mp
    exact hgRooted
  have hyCycleP : Sum.inl y ∈ cycleP.walk.support := by
    apply (cycleP.walk.mem_support_rotate_iff (Sum.inl v0) hv0CycleP).mp
    rw [← hyAt]
    exact rootedCycle.getVert_mem_support firstOutside.val
  let returnPrefix := rootedCycle.takeUntil (Sum.inr g) hgRooted
  let returnPath := returnPrefix.reverse
  have returnPrefixPath : returnPrefix.IsPath :=
    rootedIsCycle.isPath_takeUntil hgRooted
  have returnPathIsPath : returnPath.IsPath := returnPrefixPath.reverse
  have returnPrefixPositive : 0 < returnPrefix.length := by
    by_contra hnot
    have hzero : returnPrefix.length = 0 := by omega
    have hget := rootedCycle.getVert_length_takeUntil hgRooted
    rw [hzero, rootedCycle.getVert_zero] at hget
    cases hget
  have returnPrefixLength : returnPrefix.length = firstOutside.val - 1 := by
    have hprefixLe := rootedCycle.length_takeUntil_le_length hgRooted
    apply rootedIsCycle.getVert_injOn
      (by simp only [Set.mem_ofPred_eq]; exact ⟨returnPrefixPositive, hprefixLe⟩)
      (by simp only [Set.mem_ofPred_eq]; constructor <;> omega)
    calc
      rootedCycle.getVert returnPrefix.length = Sum.inr g :=
        rootedCycle.getVert_length_takeUntil hgRooted
      _ = rootedCycle.getVert (firstOutside.val - 1) := hgAt.symm
  have returnPathOnCycle : ∀ z ∈ returnPath.support,
      z ∈ cycleP.walk.support := by
    intro z hz
    have hzPrefix : z ∈ returnPrefix.support := by
      simpa [returnPath, SimpleGraph.Walk.support_reverse] using hz
    have hzRooted := rootedCycle.support_takeUntil_subset_support hgRooted hzPrefix
    exact (cycleP.walk.mem_support_rotate_iff (Sum.inl v0) hv0CycleP).mp hzRooted
  have returnPathInternal : ∀ v, Sum.inl v ∈ returnPath.support →
      v ∈ currentTree := by
    intro v hv
    have hvPrefix : Sum.inl v ∈ returnPrefix.support := by
      simpa [returnPath, SimpleGraph.Walk.support_reverse] using hv
    obtain ⟨m, hm, hmle⟩ :=
      SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hvPrefix
    have hmRooted : rootedCycle.getVert m = Sum.inl v := by
      rw [← rootedCycle.getVert_takeUntil hgRooted hmle]
      exact hm
    have hmFirst : m < firstOutside.val := by
      rw [returnPrefixLength] at hmle
      omega
    apply beforeFirstOutside
      (⟨m, by omega⟩ : Fin (rootedCycle.length + 1)) hmFirst v hmRooted
  have interveningForCertificate : ∀ j : Fin (rounds + 1),
      0 < j.val → r.succ.val < j.val → j.val ≤ p.castSucc.val →
        series.data.kind j = some TashkinovExtensionKind.RE := by
    intro j hjPositive hrj hjp
    simp only [Fin.val_succ, Fin.val_castSucc] at hrj hjp
    let q : Fin rounds := ⟨j.val - 1, by omega⟩
    have hqSucc : q.succ = j := by
      apply Fin.ext
      simp [q]
      omega
    rw [← hqSucc]
    apply betweenRE q
    · simp [q]
      omega
    · simp [q]
      omega
  have cert : RevisitingExtensionCertificate series.data p.castSucc := {
    earlier := r.succ
    earlierPositive := by simp
    earlierAtMost := by simp; omega
    earlierPE := hkindr
    interveningRevisiting := interveningForCertificate
    gamma := gamma
    delta := delta
    earlierGamma := hgammar
    earlierDelta := hdeltar
    cycle := cycleP
    meetsEarlier := by
      exact ⟨v0, hv0Earlier, hv0CycleP⟩
    leavesCurrent := by
      exact ⟨y, by simpa [currentTree] using hyOutside,
        hyCycleP⟩
    edge := g
    edgeOnCycle := hgCycleP
    edgeBoundary := by simpa [currentTree] using hgBoundary
    insideEndpoint := x
    outsideEndpoint := y
    insideInCurrent := by simpa [currentTree] using hxCurrent
    outsideNotCurrent := by simpa [currentTree] using hyOutside
    edgeEnds := hgEnds
    returnVertex := v0
    returnInEarlier := hv0Earlier
    returnPath := returnPath
    returnPathIsPath := returnPathIsPath
    returnPathOnCycle := returnPathOnCycle
    returnPathInternal := by
      intro v hv
      simpa [currentTree] using returnPathInternal v hv
  }
  exact pNoRevisiting ⟨cert⟩
