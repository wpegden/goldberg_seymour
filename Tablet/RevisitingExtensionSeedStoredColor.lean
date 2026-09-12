import Tablet.BoundaryEdges
import Tablet.ColoredVertexSetClosed
import Tablet.RevisitingExtensionCertificate
import Tablet.TashkinovSeriesStep
import Tablet.TashkinovStoredColors
import Tablet.TreeMissingColors
import Tablet.TwoColorIncidenceGraph

-- [TABLET NODE: RevisitingExtensionSeedStoredColor]
theorem RevisitingExtensionSeedStoredColor {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k rounds : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k)
    (data : TashkinovSeriesData G k rounds e0)
    (j : Fin (rounds + 1))
    (hstep : TashkinovSeriesStep G k rounds e0 input data j)
    (hkind : data.kind j = some TashkinovExtensionKind.RE)
    (f : E) (hedges : data.connectingEdges j = {f})
    (beta : Fin k) (hcolor : data.coloring j f = some beta) :
    beta ∈ TashkinovStoredColors data j := by
-- BODY
  classical
  generalize hj : j = j' at hstep hkind hedges hcolor ⊢
  cases hstep with
  | initial triple seedLength initialColoring initialStored initialEdges
      initialKind initialVertex initialOutside initialDelta initialGamma
      initialClosure =>
      rw [initialKind] at hkind
      simp at hkind
  | SE i previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternative
      currentColoring currentStored currentEdges currentKind currentVertex
      currentOutside currentDelta currentGamma adjoined adjoinedExactly
      closedExtension orderedExtension strictExtension =>
      rw [currentKind] at hkind
      simp at hkind
  | PE i previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternativeFails
      gamma gammaRule secondStable secondStableProper
      secondStableOneUncolored secondStableRelation exitWitness
      currentColoring currentProper currentOneUncolored currentStored
      currentEdges currentKind currentVertex currentOutside currentDelta
      currentGamma closedExtension orderedExtension strictExtension =>
      rw [currentKind] at hkind
      simp at hkind
  | RE i previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed available currentColoring currentStored
      currentEdges currentKind currentVertex currentOutside currentDelta
      currentGamma adjoined adjoinedExactly closedExtension orderedExtension
      strictExtension =>
      have hf : f = available.edge := by
        have hm : f ∈ data.connectingEdges i.succ := by
          rw [hedges]
          simp
        rw [currentEdges] at hm
        simpa using hm
      subst f
      have hpathNonempty : ¬ available.returnPath.Nil := by
        intro hnil
        have hzero : available.returnPath.length = 0 :=
          SimpleGraph.Walk.length_eq_zero_iff.mpr hnil
        have heq := available.returnPath.eq_of_length_eq_zero hzero
        exact Sum.inr_ne_inl heq
      have hadj := available.returnPath.adj_snd hpathNonempty
      have hedgeColor : data.coloring i.castSucc available.edge =
          some available.gamma ∨
          data.coloring i.castSucc available.edge = some available.delta := by
        cases hsnd : available.returnPath.snd with
        | inl v =>
            rw [hsnd] at hadj
            exact hadj.2
        | inr g =>
            rw [hsnd] at hadj
            simp [TwoColorIncidenceGraph] at hadj
      have hbeta : beta = available.gamma ∨ beta = available.delta := by
        rw [currentColoring] at hcolor
        rcases hedgeColor with hgamma | hdelta
        · exact Or.inl (Option.some.inj (hcolor.symm.trans hgamma))
        · exact Or.inr (Option.some.inj (hcolor.symm.trans hdelta))
      have hnotTree : beta ∉ TreeMissingColors
          (data.coloring i.succ) (data.tree i.succ.castSucc) := by
        intro hmissing
        simp only [TreeMissingColors, Finset.mem_biUnion] at hmissing
        rcases hmissing with ⟨v, hv, hvmissing⟩
        apply previousClosed available.edgeBoundary hv
        · rw [currentColoring] at hcolor
          exact hcolor
        · rw [currentColoring] at hvmissing
          exact hvmissing
      unfold TashkinovStoredColors
      simp only [Fin.val_succ, Nat.succ_ne_zero, ↓reduceIte,
        Finset.mem_sdiff, Finset.mem_biUnion, Finset.mem_univ, true_and]
      refine ⟨⟨i.succ, ?_⟩, hnotTree⟩
      rcases hbeta with hbeta | hbeta <;>
        simp [Fin.val_succ, currentStored, hbeta]
