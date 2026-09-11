import Mathlib.Data.Finset.Sort
import Tablet.HkuUnsupportedVertexColors
import Tablet.MaximumDefectiveChoice
import Tablet.MaximumDegree
import Tablet.MissingColorsNonemptyOfMaximumDegree
import Tablet.ParallelExtensionColor
import Tablet.SupportingPEColorChain
import Tablet.SupportingPEMissingTransport
import Tablet.StableColoring
import Tablet.TashkinovSeries
import Tablet.TashkinovSeriesStep
import Tablet.TreeSequenceInitialSegment
import Tablet.TreeSequenceVertexSet

open scoped Sym2

-- [TABLET NODE: ParallelExtensionColorExists]
theorem ParallelExtensionColorExists {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k rounds : Nat) (e0 : E)
    (input : PartialEdgeColoring E k)
    (series : TashkinovSeries G k rounds e0 input)
    (i : Fin (rounds + 1))
    (choice : MaximumDefectiveChoice G e0 (series.data.tree i.succ)
      (TashkinovStoredColors series.data i) (series.data.coloring i))
    (hdegree : MaximumDegree G + 1 ≤ k) :
    exists gamma : Fin k,
      ParallelExtensionColor series.data i choice.selected choice.vertex gamma := by
-- BODY
  classical
  by_cases history : exists h : Fin (rounds + 1),
      0 < h.val ∧ h.val ≤ i.val ∧
      series.data.kind h = some TashkinovExtensionKind.PE ∧
      series.data.chosenVertex h = some choice.vertex
  · obtain ⟨someSlot, somePositive, someLe, someKind, someVertex⟩ := history
    have iPositive : 0 < i.val := lt_of_lt_of_le somePositive someLe
    let q : Fin rounds := i.pred (Fin.ne_of_gt iPositive)
    have qSucc : q.succ = i := Fin.succ_pred i (Fin.ne_of_gt iPositive)
    let supports : Finset (Fin rounds) := Finset.univ.filter fun j =>
      j.val ≤ q.val ∧
      series.data.kind j.succ = some TashkinovExtensionKind.PE ∧
      series.data.chosenVertex j.succ = some choice.vertex
    let someRound : Fin rounds := someSlot.pred (Fin.ne_of_gt somePositive)
    have someRoundSucc : someRound.succ = someSlot :=
      Fin.succ_pred someSlot (Fin.ne_of_gt somePositive)
    have someRoundMem : someRound ∈ supports := by
      simp only [supports, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · have values : q.val + 1 = i.val := congrArg Fin.val qSucc
        have roundValues : someRound.val + 1 = someSlot.val :=
          congrArg Fin.val someRoundSucc
        omega
      · simpa [someRoundSucc] using And.intro someKind someVertex
    have supportsNonempty : supports.Nonempty := ⟨someRound, someRoundMem⟩
    let p := supports.card - 1
    have supportsCard : supports.card = p + 1 := by
      have cardPositive : 0 < supports.card := Finset.card_pos.mpr supportsNonempty
      dsimp [p]
      omega
    let indices : Fin (p + 1) → Fin rounds :=
      supports.orderEmbOfFin supportsCard
    have indicesIncreasing : forall a b, a.val < b.val →
        (indices a).val < (indices b).val := by
      intro a b hab
      exact (supports.orderEmbOfFin supportsCard).strictMono hab
    have indicesEnumerate : forall j : Fin rounds,
        (j.val ≤ q.val ∧
          series.data.kind j.succ = some TashkinovExtensionKind.PE ∧
          series.data.chosenVertex j.succ = some choice.vertex) ↔
        exists a : Fin (p + 1), indices a = j := by
      intro j
      constructor
      · intro hj
        have hjmem : j ∈ supports := by
          simpa only [supports, Finset.mem_filter, Finset.mem_univ, true_and]
            using hj
        have hjrange : j ∈ Set.range (supports.orderEmbOfFin supportsCard) := by
          rw [Finset.range_orderEmbOfFin]
          exact hjmem
        simpa only [Set.mem_range, indices] using hjrange
      · rintro ⟨a, rfl⟩
        have hmem := Finset.orderEmbOfFin_mem supports supportsCard a
        simpa only [supports, Finset.mem_filter, Finset.mem_univ, true_and,
          indices] using hmem
    have vertexTransfer : forall (A B : TreeSequence G e0),
        TreeSequenceInitialSegment A B → forall x,
          x ∈ TreeSequenceVertexSet A → x ∈ TreeSequenceVertexSet B := by
      intro A B hAB x hx
      rcases hAB with ⟨hlen, hvertices, _⟩
      simp only [TreeSequenceVertexSet, Finset.mem_image] at hx ⊢
      obtain ⟨a, _, rfl⟩ := hx
      exact ⟨Fin.castLE (Nat.succ_le_succ hlen) a, Finset.mem_univ _,
        hvertices a⟩
    have peFields : forall j : Fin rounds,
        series.data.kind j.succ = some TashkinovExtensionKind.PE →
        series.data.chosenVertex j.succ = some choice.vertex →
        exists d g,
          series.data.delta j.succ = some d ∧
          series.data.gamma j.succ = some g ∧
          choice.vertex ∈ TreeSequenceVertexSet
            (series.data.tree j.succ.castSucc) ∧
          TreeSequenceInitialSegment (series.data.tree j.succ.castSucc)
            (series.data.tree j.succ.succ) := by
      intro j hkind hvertex
      generalize targetEq : j.succ = target
      cases series.certified target with
      | initial triple seedLength initialColoring initialStored initialEdges
          initialKind initialVertex initialOutside initialDelta initialGamma
          initialClosure =>
        exact (Fin.succ_ne_zero j targetEq).elim
      | SE r previousProper previousOneUncolored previousClosed
          previousNotStronglyClosed noRevisiting selected seriesAlternative
          currentColoring currentStored currentEdges currentKind currentVertex
          currentOutside currentDelta currentGamma adjoined adjoinedExactly
          closedExtension orderedExtension strictExtension =>
        have values := congrArg Fin.val targetEq
        simp at values
        have rEq : r = j := by apply Fin.ext; omega
        subst r
        rw [currentKind] at hkind
        simp at hkind
      | RE r previousProper previousOneUncolored previousClosed
          previousNotStronglyClosed available currentColoring currentStored
          currentEdges currentKind currentVertex currentOutside currentDelta
          currentGamma adjoined adjoinedExactly closedExtension orderedExtension
          strictExtension =>
        have values := congrArg Fin.val targetEq
        simp at values
        have rEq : r = j := by apply Fin.ext; omega
        subst r
        rw [currentKind] at hkind
        simp at hkind
      | PE r previousProper previousOneUncolored previousClosed
          previousNotStronglyClosed noRevisiting selected seriesAlternativeFails
          gamma gammaRule secondStable secondStableProper
          secondStableOneUncolored secondStableRelation exitWitness
          currentColoring currentProper currentOneUncolored currentStored
          currentEdges currentKind currentVertex currentOutside currentDelta
          currentGamma closedExtension orderedExtension strictExtension =>
        have values := congrArg Fin.val targetEq
        simp at values
        have rEq : r = j := by apply Fin.ext; omega
        subst r
        have vertexEq : selected.vertex = choice.vertex :=
          Option.some.inj (currentVertex.symm.trans hvertex)
        exact ⟨selected.color, gamma, currentDelta, currentGamma,
          by simpa [vertexEq] using selected.vertexDefective.1,
          orderedExtension⟩
    have seriesVertexLater : forall a b : Fin rounds, a.val ≤ b.val →
        forall x, x ∈ TreeSequenceVertexSet
          (series.data.tree a.succ.castSucc) →
        x ∈ TreeSequenceVertexSet (series.data.tree b.succ.castSucc) := by
      intro a b hab x hxa
      induction distance : b.val - a.val using Nat.strong_induction_on
          generalizing a b with
      | h n ih =>
        by_cases equal : a.val = b.val
        · have : a = b := Fin.ext equal
          simpa [this] using hxa
        · have stepLe : a.val + 1 ≤ b.val := by omega
          let mid : Fin rounds := ⟨a.val + 1, by omega⟩
          have midVal : mid.val = a.val + 1 := rfl
          have nextSegment : TreeSequenceInitialSegment
              (series.data.tree a.succ.castSucc)
              (series.data.tree a.succ.succ) := by
            generalize targetEq : a.succ = target
            cases series.certified target with
            | initial triple seedLength initialColoring initialStored initialEdges
                initialKind initialVertex initialOutside initialDelta initialGamma
                initialClosure => exact (Fin.succ_ne_zero a targetEq).elim
            | SE r previousProper previousOneUncolored previousClosed
                previousNotStronglyClosed noRevisiting selected seriesAlternative
                currentColoring currentStored currentEdges currentKind currentVertex
                currentOutside currentDelta currentGamma adjoined adjoinedExactly
                closedExtension orderedExtension strictExtension =>
              have values := congrArg Fin.val targetEq
              simp at values
              have rEq : r = a := by apply Fin.ext; omega
              simpa [rEq] using orderedExtension
            | RE r previousProper previousOneUncolored previousClosed
                previousNotStronglyClosed available currentColoring currentStored
                currentEdges currentKind currentVertex currentOutside currentDelta
                currentGamma adjoined adjoinedExactly closedExtension orderedExtension
                strictExtension =>
              have values := congrArg Fin.val targetEq
              simp at values
              have rEq : r = a := by apply Fin.ext; omega
              simpa [rEq] using orderedExtension
            | PE r previousProper previousOneUncolored previousClosed
                previousNotStronglyClosed noRevisiting selected seriesAlternativeFails
                gamma gammaRule secondStable secondStableProper
                secondStableOneUncolored secondStableRelation exitWitness
                currentColoring currentProper currentOneUncolored currentStored
                currentEdges currentKind currentVertex currentOutside currentDelta
                currentGamma closedExtension orderedExtension strictExtension =>
              have values := congrArg Fin.val targetEq
              simp at values
              have rEq : r = a := by apply Fin.ext; omega
              simpa [rEq] using orderedExtension
          have hxm : x ∈ TreeSequenceVertexSet
              (series.data.tree mid.succ.castSucc) := by
            have treeEq : mid.succ.castSucc = a.succ.succ := by
              apply Fin.ext
              simp [mid]
            rw [treeEq]
            exact vertexTransfer _ _ nextSegment x hxa
          have hrest := ih (b.val - mid.val) (by omega) mid b (by omega) hxm
            (by simp)
          exact hrest
    obtain ⟨deltaLast, gammaLast, deltaLastEq, gammaLastEq,
        lastVertex, lastSegment⟩ := peFields (indices (Fin.last p))
      ((indicesEnumerate (indices (Fin.last p))).2 ⟨Fin.last p, rfl⟩).2.1
      ((indicesEnumerate (indices (Fin.last p))).2 ⟨Fin.last p, rfl⟩).2.2
    obtain ⟨deltaFirst, gammaFirst, deltaFirstEq, gammaFirstEq,
        firstVertex, firstSegment⟩ := peFields (indices 0)
      ((indicesEnumerate (indices 0)).2 ⟨0, rfl⟩).2.1
      ((indicesEnumerate (indices 0)).2 ⟨0, rfl⟩).2.2
    have lastLeQ : (indices (Fin.last p)).val ≤ q.val :=
      ((indicesEnumerate (indices (Fin.last p))).2 ⟨Fin.last p, rfl⟩).1
    have currentTreeVertex : choice.vertex ∈ TreeSequenceVertexSet
        (series.data.tree q.succ.castSucc) :=
      seriesVertexLater (indices (Fin.last p)) q lastLeQ choice.vertex lastVertex
    have transport := SupportingPEMissingTransport G k rounds p e0 input series q
      choice.vertex currentTreeVertex indices indicesIncreasing indicesEnumerate
      gammaFirst deltaLast gammaFirstEq deltaLastEq
    have deltaMissingAfterLast : deltaLast ∈ MissingColors G
        (series.data.coloring (indices (Fin.last p)).succ) choice.vertex := by
      rw [transport.2]
      simp
    let lastSlot : Fin (rounds + 1) := (indices (Fin.last p)).succ
    have lastSlotLe : lastSlot.val ≤ i.val := by
      have values := congrArg Fin.val qSucc
      simp at values
      simp [lastSlot]
      omega
    have deltaMissingCurrent : deltaLast ∈
        MissingColors G (series.data.coloring i) choice.vertex := by
      by_cases same : lastSlot.val = i.val
      · have slotEq : lastSlot = i := Fin.ext same
        simpa [lastSlot, slotEq] using deltaMissingAfterLast
      · have strict : lastSlot.val < i.val := lt_of_le_of_ne lastSlotLe same
        let start : Fin rounds := ⟨lastSlot.val, by omega⟩
        have startTreeVertex : choice.vertex ∈ TreeSequenceVertexSet
            (series.data.tree start.succ.castSucc) := by
          have treeEq : start.succ.castSucc =
              (indices (Fin.last p)).succ.succ := by
            apply Fin.ext
            simp [start, lastSlot]
          rw [treeEq]
          exact vertexTransfer _ _ lastSegment choice.vertex lastVertex
        have noLater : forall j : Fin rounds,
            start.val ≤ j.val → j.val ≤ q.val →
            ¬ (series.data.kind j.succ = some TashkinovExtensionKind.PE ∧
              series.data.chosenVertex j.succ = some choice.vertex) := by
          intro j hjStart hjq hpe
          have jIn : j ∈ supports := by
            simp only [supports, Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨hjq, hpe⟩
          have jRange : j ∈ Set.range (supports.orderEmbOfFin supportsCard) := by
            rw [Finset.range_orderEmbOfFin]
            exact jIn
          obtain ⟨a, ha⟩ := jRange
          have aLe : a ≤ Fin.last p := Fin.le_last a
          have embLe := (supports.orderEmbOfFin supportsCard).monotone aLe
          rw [ha] at embLe
          have jLeLast : j.val ≤ (indices (Fin.last p)).val := by
            change j.val ≤ (supports.orderEmbOfFin supportsCard (Fin.last p)).val
            change j ≤ supports.orderEmbOfFin supportsCard (Fin.last p) at embLe
            exact embLe
          simp [start, lastSlot] at hjStart
          omega
        have unchanged := HkuUnsupportedVertexColors G k rounds e0 input series q
          start choice.vertex (by simp [start, q]; omega) startTreeVertex noLater
        have startColorEq : start.castSucc = lastSlot := by
          apply Fin.ext
          rfl
        rw [startColorEq, qSucc] at unchanged
        exact unchanged ▸ (by simpa [lastSlot] using deltaMissingAfterLast)
    have deltaMissingSelected : deltaLast ∈
        MissingColors G choice.selected choice.vertex := by
      rw [choice.selectedStable.2 choice.vertex choice.vertexDefective.1]
      exact deltaMissingCurrent
    refine ⟨deltaLast, deltaMissingSelected, Or.inl ?_⟩
    refine ⟨lastSlot, by simp [lastSlot], lastSlotLe, ?_, ?_, ?_, ?_⟩
    · simpa [lastSlot] using
        ((indicesEnumerate (indices (Fin.last p))).2 ⟨Fin.last p, rfl⟩).2.1
    · simpa [lastSlot] using
        ((indicesEnumerate (indices (Fin.last p))).2 ⟨Fin.last p, rfl⟩).2.2
    · simpa [lastSlot] using deltaLastEq
    · intro j hjPositive hjLe hjKind hjVertex
      let r : Fin rounds := j.pred (Fin.ne_of_gt hjPositive)
      have rSucc : r.succ = j := Fin.succ_pred j (Fin.ne_of_gt hjPositive)
      have rLeQ : r.val ≤ q.val := by
        have qValues := congrArg Fin.val qSucc
        have rValues := congrArg Fin.val rSucc
        simp at qValues rValues
        omega
      have rIn : r ∈ supports := by
        simp only [supports, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨rLeQ, by simpa [rSucc] using And.intro hjKind hjVertex⟩
      have rRange : r ∈ Set.range (supports.orderEmbOfFin supportsCard) := by
        rw [Finset.range_orderEmbOfFin]
        exact rIn
      obtain ⟨a, ha⟩ := rRange
      have embLe := (supports.orderEmbOfFin supportsCard).monotone
        (Fin.le_last a)
      rw [ha] at embLe
      have rLeLast : r.val ≤ (indices (Fin.last p)).val := by
        change r.val ≤ (supports.orderEmbOfFin supportsCard (Fin.last p)).val
        change r ≤ supports.orderEmbOfFin supportsCard (Fin.last p) at embLe
        exact embLe
      have rValues := congrArg Fin.val rSucc
      simp [lastSlot] at rValues ⊢
      omega
  · obtain ⟨gamma, hgamma⟩ :=
      MissingColorsNonemptyOfMaximumDegree G choice.selected hdegree choice.vertex
    refine ⟨gamma, hgamma, Or.inr ?_⟩
    intro h hpositive hle hkind heq
    exact history ⟨h, hpositive, hle, hkind, heq⟩
