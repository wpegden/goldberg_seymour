import Tablet.BoundaryColorEdges
import Tablet.BoundaryEdges
import Tablet.ColoredVertexSetClosed
import Tablet.ColoredVertexSetElementary
import Tablet.HierarchyBase
import Tablet.HkuParallelBoundaryStructure
import Tablet.OrderedTreeUnion
import Tablet.TashkinovAugmentation
import Tablet.TashkinovAugmentationSequence
import Tablet.TashkinovClosure
import Tablet.TashkinovSeries
import Tablet.TashkinovSeriesStep
import Tablet.TreeColorSetClosed
import Tablet.TreeMissingColors
import Tablet.TreeSequenceInitialSegment
import Tablet.TreeSequencePrefix
import Tablet.TreeSequenceVertexSet
import Tablet.TreeVertexOrder

-- [TABLET NODE: ParallelCommonMissingClosed]
theorem ParallelCommonMissingClosed {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (generating phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T generating)
    (hpositive : 0 < ett.rounds)
    (base : HierarchyBase ett phi)
    (hphi : phi = ett.series.data.coloring (Fin.last ett.rounds))
    (hPE : ett.series.data.kind (Fin.last ett.rounds) =
      some TashkinovExtensionKind.PE)
    (hlowerElementary :
      let q : Fin ett.rounds := ⟨ett.rounds - 1, by omega⟩
      ColoredVertexSetElementary G
        (ett.series.data.coloring q.castSucc)
        (TreeSequenceVertexSet
          (ett.series.data.tree (Fin.last ett.rounds).castSucc))) :
    let Tn := ett.series.data.tree (Fin.last ett.rounds).castSucc
    TreeColorSetClosed G phi base.core
      (TreeMissingColors phi Tn ∩ TreeMissingColors phi base.closure) := by
-- BODY
  classical
  let n : Fin (ett.rounds + 1) := Fin.last ett.rounds
  let Tn := ett.series.data.tree n.castSucc
  have hq : 0 < ett.rounds := hpositive
  let q : Fin ett.rounds := ⟨ett.rounds - 1, by omega⟩
  have hsucc : q.succ = n := by
    apply Fin.ext
    simp only [Fin.succ_mk, Fin.last, q, n]
    omega
  generalize target_eq : q.succ = target
  cases ett.series.certified target with
  | PE ci previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternativeFails
      gamma gammaRule secondStable secondStableProper secondStableOneUncolored
      secondStableRelation exitWitness currentColoring currentProper
      currentOneUncolored currentStored currentEdges currentKind currentVertex
      currentOutside currentDelta currentGamma closedExtension orderedExtension
      strictExtension =>
    have hci : ci = q := by
      apply Fin.ext
      have hv := congrArg Fin.val target_eq
      simp at hv
      omega
    subst ci
    have hboundary := HkuParallelBoundaryStructure G k ett.rounds e0 input ett.series q
      choice.edge choice.color gamma choice.vertex
      (by simpa using currentKind) (by simpa using currentEdges)
      (by simpa using currentDelta) (by simpa using currentGamma)
      (by simpa using currentVertex)
    have hTn : Tn = ett.series.data.tree q.succ.castSucc := by
      simpa [Tn] using congrArg
        (fun z : Fin (ett.rounds + 1) => ett.series.data.tree z.castSucc) hsucc.symm
    have hchoice : choice.vertex = Tn.vertex base.supportPosition := by
      have hp := (base.parallel hPE).1
      change ett.series.data.chosenVertex n =
        some (Tn.vertex base.supportPosition) at hp
      rw [← hsucc] at hp
      have hc : ett.series.data.chosenVertex q.succ = some choice.vertex := currentVertex
      exact Option.some.inj (hc.symm.trans hp)
    have hindex : q.succ = Fin.last ett.rounds := by
      simpa [n] using hsucc
    have helem : ColoredVertexSetElementary G
        (ett.series.data.coloring q.castSucc)
        (TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc)) := by
      unfold ColoredVertexSetElementary at hlowerElementary ⊢
      have hqsucc : q.succ = Fin.last ett.rounds := by
        apply Fin.ext
        simp [q]
        omega
      rw [hqsucc]
      intro u hu v hv huv
      exact hlowerElementary hu hv huv
    have initialVertices : ∀ {A B : TreeSequence G e0},
        TreeSequenceInitialSegment A B →
          TreeSequenceVertexSet A ⊆ TreeSequenceVertexSet B := by
      intro A B hab x hx
      unfold TreeSequenceVertexSet at hx ⊢
      simp only [Finset.mem_image] at hx ⊢
      obtain ⟨i, hi, rfl⟩ := hx
      obtain ⟨hlen, hvertices, hedges⟩ := hab
      refine ⟨Fin.castLE (Nat.succ_le_succ hlen) i, Finset.mem_univ _, ?_⟩
      exact hvertices i
    have prefixClosure : TashkinovClosure phi
        (TreeSequencePrefix Tn base.supportPosition.val base.supportPositive
          (Nat.le_of_lt_succ base.supportPosition.isLt)) base.closure := by
      exact (base.parallel hPE).2.1
    have vertexReach : ∀ {A B : TreeSequence G e0},
        TashkinovAugmentationSequence phi A B →
          TreeSequenceVertexSet A ⊆ TreeSequenceVertexSet B := by
      intro A B hab
      unfold TashkinovAugmentationSequence at hab
      induction hab using Relation.ReflTransGen.head_induction_on with
      | refl => exact Finset.Subset.rfl
      | @head A B hstep htail ih =>
        intro x hx
        obtain ⟨hlen, hvertices, hedges⟩ := hstep.2.1
        apply ih
        apply initialVertices hstep.2.1
        exact hx
    have prefixInClosure : TreeSequenceVertexSet
        (TreeSequencePrefix Tn base.supportPosition.val base.supportPositive
          (Nat.le_of_lt_succ base.supportPosition.isLt)) ⊆
        TreeSequenceVertexSet base.closure := vertexReach prefixClosure.1
    obtain ⟨orderedUnion⟩ := (base.parallel hPE).2.2
    have coreVertices : TreeSequenceVertexSet base.core =
        TreeSequenceVertexSet Tn ∪ TreeSequenceVertexSet base.closure := by
      rw [← orderedUnion.vertexSet]
    have hclosed : ColoredVertexSetClosed G phi
        (TreeSequenceVertexSet base.closure) := prefixClosure.2
    have hX : TreeSequenceVertexSet Tn ⊆
        TreeSequenceVertexSet base.core := by
      rw [coreVertices]
      exact Finset.subset_union_left
    have hY : TreeSequenceVertexSet base.closure ⊆
        TreeSequenceVertexSet base.core := by
      rw [coreVertices]
      exact Finset.subset_union_right
    have hpreVertex : ∀ {w : V}, TreeVertexOrder Tn w
        (Tn.vertex base.supportPosition) → w ∈ TreeSequenceVertexSet base.closure := by
      intro w hw
      obtain ⟨i, j, hi, hj, hij⟩ := hw
      have hj' : j = base.supportPosition := Tn.vertex_injective hj
      subst j
      have hi' : i.val < base.supportPosition.val := hij
      apply prefixInClosure
      unfold TreeSequenceVertexSet
      simp only [Finset.mem_image]
      let i' : Fin (base.supportPosition.val + 1) := ⟨i.val, by omega⟩
      refine ⟨i', Finset.mem_univ _, ?_⟩
      simpa [TreeSequencePrefix, i'] using hi
    unfold TreeColorSetClosed
    dsimp
    intro alpha halpha
    obtain ⟨halphaX, halphaY⟩ := Finset.mem_inter.mp halpha
    have alphaMissing : ∃ y : V, y ∈ TreeSequenceVertexSet base.closure ∧
        alpha ∈ MissingColors G phi y := by
      unfold TreeMissingColors at halphaY
      exact Finset.mem_biUnion.mp halphaY
    obtain ⟨y, hy, hymiss⟩ := alphaMissing
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro g hg
    have hg' : g ∈ BoundaryEdges G (TreeSequenceVertexSet base.core) ∧
        phi g = some alpha := by
      simpa [BoundaryColorEdges] using hg
    obtain ⟨hb, hcolor⟩ := hg'
    have hb' : ∃ u ∈ TreeSequenceVertexSet base.core, ∃ v ∉
        TreeSequenceVertexSet base.core, G.ends g = s(u, v) := by
      simpa [BoundaryEdges] using hb
    obtain ⟨p, hp, r, hr, hends⟩ := hb'
    by_cases hpY : p ∈ TreeSequenceVertexSet base.closure
    · have hrY : r ∉ TreeSequenceVertexSet base.closure := by
        intro hrY
        apply hr
        exact hY hrY
      have hbY : g ∈ BoundaryEdges G (TreeSequenceVertexSet base.closure) :=
        by
          simpa [BoundaryEdges] using
            (show ∃ u ∈ TreeSequenceVertexSet base.closure, ∃ v ∉
                TreeSequenceVertexSet base.closure, G.ends g = s(u, v) from
              ⟨p, hpY, r, hrY, hends⟩)
      have hcgY : g ∈ BoundaryColorEdges G phi
          (TreeSequenceVertexSet base.closure) alpha := by
        simp [BoundaryColorEdges, hbY, hcolor]
      have hnot := hclosed hbY hy hcolor
      exact (hnot (by simpa [MissingColors] using hymiss)).elim
    · have hpX : p ∈ TreeSequenceVertexSet Tn := by
        have : p ∈ TreeSequenceVertexSet Tn ∪
            TreeSequenceVertexSet base.closure := by
          rw [← coreVertices]
          exact hp
        exact Finset.mem_union.mp this |>.resolve_right hpY
      have hrX : r ∉ TreeSequenceVertexSet Tn := by
        intro hrX
        apply hr
        exact hX hrX
      have hbX : g ∈ BoundaryEdges G (TreeSequenceVertexSet Tn) :=
        by
          simpa [BoundaryEdges] using
            (show ∃ u ∈ TreeSequenceVertexSet Tn, ∃ v ∉
                TreeSequenceVertexSet Tn, G.ends g = s(u, v) from
              ⟨p, hpX, r, hrX, hends⟩)
      have hcgX : g ∈ BoundaryColorEdges G phi
          (TreeSequenceVertexSet Tn) alpha := by
        simp [BoundaryColorEdges, hbX, hcolor]
      have hcgX' := hcgX
      rw [hphi, ← hindex, hTn] at hcgX'
      have hworderT : ∀ {w : V},
          TreeVertexOrder (ett.series.data.tree q.succ.castSucc) w choice.vertex →
          TreeVertexOrder Tn w (Tn.vertex base.supportPosition) := by
        intro w hw
        simpa [hTn, hchoice] using hw
      by_cases halphaDelta : alpha = choice.color
      · subst alpha
        obtain ⟨w, hworder, hincident⟩ := hboundary.2.1 g hcgX'
        have hwX : w ∈ TreeSequenceVertexSet Tn := by
          have hworder' := hworderT hworder
          unfold TreeVertexOrder at hworder'
          obtain ⟨i, j, hi, hj, hij⟩ := hworder'
          unfold TreeSequenceVertexSet
          simp only [Finset.mem_image]
          exact ⟨i, Finset.mem_univ _, hi⟩
        have hwY : w ∈ TreeSequenceVertexSet base.closure := by
          apply hpreVertex
          exact hworderT hworder
        have hwends : w = p ∨ w = r := by
          change w ∈ G.ends g at hincident
          rw [hends] at hincident
          simpa using hincident
        cases hwends with
        | inl hwp => exact hpY (hwp ▸ hwY)
        | inr hwr => exact hr (hY (hwr ▸ hwY))
      · have halphaX' := halphaX
        rw [hphi, ← hindex] at halphaX'
        have hempty := hboundary.2.2 helem alpha halphaX' halphaDelta
        rw [hempty] at hcgX'
        simpa using hcgX'
  | initial triple seedLength initialColoring initialStored initialEdges
      initialKind initialVertex initialOutside initialDelta initialGamma
      initialClosure =>
    exact (Fin.succ_ne_zero q target_eq).elim
  | SE ci previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternative
      currentColoring currentStored currentEdges currentKind currentVertex
      currentOutside currentDelta currentGamma adjoined adjoinedExactly
      closedExtension orderedExtension strictExtension =>
    have hv := congrArg Fin.val target_eq
    simp at hv
    have hci : ci = q := by ext; omega
    subst ci
    change ett.series.data.kind n = some TashkinovExtensionKind.PE at hPE
    rw [← hsucc] at hPE
    rw [currentKind] at hPE
    simp at hPE
  | RE ci previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed available currentColoring currentStored
      currentEdges currentKind currentVertex currentOutside currentDelta
      currentGamma adjoined adjoinedExactly closedExtension orderedExtension
      strictExtension =>
    have hv := congrArg Fin.val target_eq
    simp at hv
    have hci : ci = q := by ext; omega
    subst ci
    change ett.series.data.kind n = some TashkinovExtensionKind.PE at hPE
    rw [← hsucc] at hPE
    rw [currentKind] at hPE
    simp at hPE
  all_goals contradiction
