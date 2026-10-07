import Tablet.BoundaryColorEdges
import Tablet.BoundaryEdges
import Tablet.BoundaryMissingColorAugmentation
import Tablet.CorrespondingExtendedTashkinovTree
import Tablet.GoodHierarchy
import Tablet.HierarchyFirstMissingPosition
import Tablet.HierarchyStarredStage
import Tablet.HierarchyStoredColorsAt
import Tablet.TashkinovAugmentation
import Tablet.TashkinovExtensionKind
import Tablet.TashkinovHierarchy
import Tablet.TreeColorSetMinusClosed
import Tablet.TreeMissingColors
import Tablet.TreeSequence

-- [TABLET NODE: AlgorithmFiveFiveParallelStrictGrowth]
theorem AlgorithmFiveFiveParallelStrictGrowth {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (generating phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T generating)
    (J : TreeSequence G e0)
    (corrJ : CorrespondingExtendedTashkinovTree G k e0 ett phi J)
    (baseJ : HierarchyBase corrJ.replacementETT phi)
    (KJ : TashkinovHierarchy corrJ.replacementETT baseJ)
    (goodJ : GoodHierarchy KJ)
    (hzero : KJ.dividerCount = 0)
    (hPE : ett.series.data.kind (Fin.last ett.rounds) =
      some TashkinovExtensionKind.PE)
    (hJcore : J = baseJ.core)
    (m : ℕ) (U : TreeSequence G e0)
    (hUlength : U.length = J.length + m)
    (hzeroEndpoint : m = 0 → U = J)
    (hmaximal : ∀ W : TreeSequence G e0,
      TashkinovAugmentation phi U W →
      (∀ eta : Fin k,
        eta ∈ HierarchyStoredColorsAt KJ (Fin.last KJ.dividerCount) →
        Disjoint (goodJ.gamma (Fin.last KJ.dividerCount) eta)
          (Finset.univ.filter fun c =>
            ∃ r : Fin W.length,
              (HierarchyStarredStage KJ
                (Fin.last KJ.dividerCount)).length ≤ r.val ∧
              r.val < min (HierarchyFirstMissingPosition phi W eta).val
                W.length ∧
              phi (W.edge r) = some c)) →
      False) :
    J.length < U.length := by
-- BODY
  classical
  have hpeReplacement :
      corrJ.replacementETT.series.data.kind
          (Fin.last corrJ.replacementETT.rounds) =
        some TashkinovExtensionKind.PE := by
    rcases corrJ with ⟨replacementInput, replacementSeries, replacementETT,
      rungAgreement, seriesPresentation, finalGeneratingColoring,
      ladderTreesAgree, storedColorsAgree, connectingEdgesAgree,
      extensionKindsAgree, replacementProper, replacementOneUncolored,
      replacementStable⟩
    cases replacementETT with
    | mk rounds roundsPositive replacementData above strict below generating =>
      cases rungAgreement
      have seriesSame : replacementData = replacementSeries :=
        eq_of_heq seriesPresentation
      cases seriesSame
      exact (extensionKindsAgree (Fin.last ett.rounds)).trans hPE
  have hnot := (goodJ.parallelBase hpeReplacement).1
  have hlast : Fin.last KJ.dividerCount = 0 := by
    apply Fin.ext
    simp [hzero]
  have hstar :
      HierarchyStarredStage KJ (Fin.last KJ.dividerCount) = J := by
    rw [hlast]
    simp [HierarchyStarredStage, hJcore]
  let C := (HierarchyStoredColorsAt KJ 0).biUnion (goodJ.gamma 0)
  have hnotC : ¬ TreeColorSetMinusClosed G phi baseJ.core C := by
    simpa [C] using hnot
  change ¬ TreeColorSetClosed G phi baseJ.core
      (TreeMissingColors phi baseJ.core \ C) at hnotC
  simp only [TreeColorSetClosed] at hnotC
  push_neg at hnotC
  rcases hnotC with ⟨c, hc, hboundary⟩
  have hcJ : c ∈ TreeMissingColors phi J := by
    have := (Finset.mem_sdiff.mp hc).1
    simpa [hJcore] using this
  have hcOutside : c ∉ C := (Finset.mem_sdiff.mp hc).2
  obtain ⟨f, hf⟩ := hboundary
  have hcolor : phi f = some c :=
    (Finset.mem_filter.mp (show f ∈ BoundaryColorEdges G phi
      (TreeSequenceVertexSet baseJ.core) c from hf)).2
  have hboundaryJ :
      f ∈ BoundaryColorEdges G phi (TreeSequenceVertexSet J) c := by
    simpa [hJcore] using hf
  obtain ⟨W, hAdjoin, hAugment, _⟩ :=
    BoundaryMissingColorAugmentation G k e0 phi J c f hboundaryJ hcJ
  rcases hAdjoin with ⟨hlen, hInitial, hLastEdge⟩
  have hwindow : ∀ eta : Fin k,
      Finset.univ.filter (fun d =>
        ∃ r : Fin W.length,
          (HierarchyStarredStage KJ
              (Fin.last KJ.dividerCount)).length ≤ r.val ∧
          r.val < min (HierarchyFirstMissingPosition phi W eta).val
              W.length ∧
          phi (W.edge r) = some d) ⊆ {c} := by
    intro eta d hd
    rcases (Finset.mem_filter.mp hd).2 with ⟨r, hrlo, hrhi, hphi⟩
    have hrval : r.val = J.length := by
      rw [hstar] at hrlo
      have hrlt : r.val < W.length := lt_of_lt_of_le hrhi (min_le_right _ _)
      omega
    have hr : r = Fin.cast hlen.symm (Fin.last J.length) := by
      apply Fin.ext
      simp [hlen, hrval]
    rw [hr, hLastEdge] at hphi
    have hcolor' : phi f = some c := hcolor
    rw [hcolor'] at hphi
    exact Finset.mem_singleton.mpr (Option.some.inj hphi.symm)
  have hdisjoint : ∀ eta : Fin k,
      eta ∈ HierarchyStoredColorsAt KJ (Fin.last KJ.dividerCount) →
      Disjoint (goodJ.gamma (Fin.last KJ.dividerCount) eta)
        (Finset.univ.filter fun d =>
          ∃ r : Fin W.length,
            (HierarchyStarredStage KJ
                (Fin.last KJ.dividerCount)).length ≤ r.val ∧
            r.val < min (HierarchyFirstMissingPosition phi W eta).val
                W.length ∧
            phi (W.edge r) = some d) := by
    intro eta heta
    apply Finset.disjoint_left.mpr
    intro d hdGamma hdWindow
    rw [hlast] at hdGamma
    have hdC : d ∈ C := by
      apply Finset.mem_biUnion.mpr
      refine ⟨eta, ?_, hdGamma⟩
      simpa [hlast] using heta
    have hdc : d = c := Finset.mem_singleton.mp (hwindow eta hdWindow)
    subst d
    exact hcOutside hdC
  by_contra hstrict
  have hm : m = 0 := by omega
  have hUeq := hzeroEndpoint hm
  exact hmaximal W (by simpa [hUeq] using hAugment) hdisjoint
