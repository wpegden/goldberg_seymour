import Tablet.ElementaryClosedNoninterchangeableExitPair
import Tablet.GoodHierarchyPrefixRepackage
import Tablet.HierarchyStarredStage
import Tablet.HierarchyStoredColorsAt
import Tablet.HierarchyTerminalStoredColors
import Tablet.Step1ExitLegPresentation
import Tablet.TreeSequence
import Tablet.TreeVertexOrder

-- [TABLET NODE: Step1ExitLegPresentationExists]
theorem Step1ExitLegPresentationExists {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (hMP : MaximumProperty ett)
    (hproper : IsProperEdgeColoring G phi)
    (hone : IsOneEdgeUncolored phi e0)
    (base : HierarchyBase ett phi)
    (H : TashkinovHierarchy ett base) (good : GoodHierarchy H)
    (hfewer : ∀ {input' : PartialEdgeColoring E k}
      {T' : TreeSequence G e0}
      {generating' : PartialEdgeColoring E k}
      (other : ExtendedTashkinovTree G k e0 input' T' generating'),
      other.rounds = ett.rounds → MaximumProperty other →
      ∀ (base' : HierarchyBase other generating')
        (K : TashkinovHierarchy other base'),
        GoodHierarchy K → K.dividerCount < H.dividerCount →
        ColoredVertexSetElementary G generating'
          (TreeSequenceVertexSet T'))
    (hlarge : 2 * ett.rounds + 11 ≤
      (TreeMissingColors phi
        (ett.series.data.tree (Fin.last ett.rounds).castSucc)).card)
    (i : Fin H.dividerCount) (alpha beta : Fin k)
    (halpha : alpha ∈ TreeMissingColors phi (H.stage i.succ.castSucc))
    (hne : alpha ≠ beta)
    (hclosed : TreeColorSetClosed G phi
      (H.stage i.succ.castSucc) {alpha})
    (hnot : ¬ TreeInterchangeable G
      (H.stage i.succ.castSucc) phi alpha beta) :
    Nonempty (Step1ExitLegPresentation G k e0 ett.rounds H.dividerCount) := by
-- BODY
  let r : Fin (H.dividerCount + 1) := i.succ
  have hr : 1 ≤ r.val := by
    dsimp [r]
    omega
  obtain ⟨ettPrefix, mpPrefix, roundsPrefix, seriesPrefix, basePrefix,
    corePrefix, closurePrefix, positionPrefix, HP, countPrefix, stagesPrefix,
    dividersPrefix, goodPrefix, gammaPrefix, terminalPrefix⟩ :=
    GoodHierarchyPrefixRepackage G k e0 input T phi phi ett hMP base H good r hr
  have fewer : HP.dividerCount < H.dividerCount := by
    rw [countPrefix]
    omega
  have elementary : ColoredVertexSetElementary G phi
      (TreeSequenceVertexSet (H.stage r.castSucc)) := by
    exact hfewer ettPrefix roundsPrefix mpPrefix basePrefix HP goodPrefix fewer
  have pair := ElementaryClosedNoninterchangeableExitPair G
      (H.stage r.castSucc) phi hproper elementary alpha beta hne halpha hclosed hnot
  rcases pair with ⟨a1, b1, a2, b2, P1, P2, f1, f2,
    exit1, exit2, disjoint12, outsideDistinct, treeDistinct,
    boundary1, boundary2, incident1, incident2, support1, support2⟩
  let orderedA1 := a1
  let orderedB1 := b1
  let orderedP1 := P1
  let orderedF1 := f1
  let orderedExit1 := exit1
  let orderedBoundary1 := boundary1
  let orderedIncident1 := incident1
  let orderedSupport1 := support1
  let orderedA2 := a2
  let orderedB2 := b2
  let orderedP2 := P2
  let orderedF2 := f2
  let orderedExit2 := exit2
  let orderedBoundary2 := boundary2
  let orderedIncident2 := incident2
  let orderedSupport2 := support2
  have orderOr : TreeVertexOrder (H.stage r.castSucc) b1 b2 ∨
      TreeVertexOrder (H.stage r.castSucc) b2 b1 := by
    simp only [TreeExitPath] at exit1 exit2
    have hmem1 := exit1.2.2.2.1
    have hmem2 := exit2.2.2.2.1
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ,
      true_and] at hmem1 hmem2
    rcases hmem1 with ⟨x, hxb1⟩
    rcases hmem2 with ⟨y, hyb2⟩
    have hxy : x ≠ y := by
      intro hxy
      apply treeDistinct
      rw [← hxb1, ← hyb2, hxy]
    rcases lt_or_gt_of_ne hxy with hlt | hgt
    · left
      exact ⟨x, y, hxb1, hyb2, hlt⟩
    · right
      exact ⟨y, x, hyb2, hxb1, hgt⟩
  rcases orderOr with orderForward | orderReverse
  · refine ⟨{
    input := input
    T := H.stage r.castSucc
    phi := phi
    ett := ettPrefix
    base := basePrefix
    hierarchy := HP
    good := goodPrefix
    rounds_eq := roundsPrefix
    maximum := mpPrefix
    divider_lt := fewer
    proper := hproper
    oneUncolored := hone
    large := by
      let oldPackage : Sigma (fun n : ℕ =>
          TashkinovSeries G k n e0 input) := ⟨ett.rounds, ett.series⟩
      let newPackage : Sigma (fun n : ℕ =>
          TashkinovSeries G k n e0 input) :=
        ⟨ettPrefix.rounds, ettPrefix.series⟩
      have packageEq : oldPackage = newPackage := by
        exact Sigma.ext roundsPrefix.symm seriesPrefix.symm
      have transferred :
          2 * newPackage.1 + 11 ≤
            (TreeMissingColors phi
              (newPackage.2.data.tree (Fin.last newPackage.1).castSucc)).card := by
        rw [← packageEq]
        exact hlarge
      simpa [oldPackage, newPackage] using transferred
    terminalMinusClosed := by
      have rawStoredEq :
          (TashkinovStoredColors ettPrefix.series.data
              (Fin.last ettPrefix.rounds) \
            TreeMissingColors phi (H.stage r.castSucc)) =
          (TashkinovStoredColors ett.series.data
              (Fin.last ett.rounds) \
            TreeMissingColors phi (H.stage r.castSucc)) := by
        let oldPackage : Sigma (fun n : ℕ =>
            TashkinovSeries G k n e0 input) := ⟨ett.rounds, ett.series⟩
        let newPackage : Sigma (fun n : ℕ =>
            TashkinovSeries G k n e0 input) :=
          ⟨ettPrefix.rounds, ettPrefix.series⟩
        have hraw := congrArg (fun z =>
            (TashkinovStoredColors z.2.data (Fin.last z.1) \
              TreeMissingColors phi (H.stage r.castSucc)))
          (show oldPackage = newPackage from
            Sigma.ext roundsPrefix.symm seriesPrefix.symm)
        simpa [oldPackage, newPackage] using hraw.symm
      have terminalStoredEq : HierarchyTerminalStoredColors HP =
          HierarchyStoredColorsAt H r := by
        have hstar : HierarchyStarredStage H r = H.stage r.castSucc := by
          dsimp [HierarchyStarredStage, r]
        simpa [HierarchyTerminalStoredColors, HierarchyStoredColorsAt,
          hstar] using rawStoredEq
      have lastGammaEq : goodPrefix.gamma (Fin.last HP.dividerCount) =
          good.gamma ⟨r.val - 1, by omega⟩ := by
        have hcount : HP.dividerCount + 1 = r.val := by omega
        have hidx : Fin.last HP.dividerCount =
            Fin.cast hcount.symm ⟨r.val - 1, by omega⟩ := by
          apply Fin.ext
          simp [countPrefix]
        funext eta
        have hg := (gammaPrefix ⟨r.val - 1, by omega⟩).2 eta
        rw [hidx]
        exact hg
      rw [terminalStoredEq, lastGammaEq]
      exact terminalPrefix
    a := alpha
    b := beta
    a_ne_b := hne
    aMissing := halpha
    aClosed := hclosed
    a1 := orderedA1
    b1 := orderedB1
    a2 := orderedA2
    b2 := orderedB2
    P1 := orderedP1
    P2 := orderedP2
    exit1 := orderedExit1
    exit2 := orderedExit2
    disjoint12 := disjoint12
    outsideDistinct := outsideDistinct
    treeDistinct := treeDistinct
    treeOrder := orderForward
    f1 := orderedF1
    f2 := orderedF2
    boundary1 := orderedBoundary1
    boundary2 := orderedBoundary2
    incident1 := orderedIncident1
    incident2 := orderedIncident2
    support1 := orderedSupport1
    support2 := orderedSupport2
  }⟩
  · refine ⟨{
    input := input
    T := H.stage r.castSucc
    phi := phi
    ett := ettPrefix
    base := basePrefix
    hierarchy := HP
    good := goodPrefix
    rounds_eq := roundsPrefix
    maximum := mpPrefix
    divider_lt := fewer
    proper := hproper
    oneUncolored := hone
    large := by
      let oldPackage : Sigma (fun n : ℕ =>
          TashkinovSeries G k n e0 input) := ⟨ett.rounds, ett.series⟩
      let newPackage : Sigma (fun n : ℕ =>
          TashkinovSeries G k n e0 input) :=
        ⟨ettPrefix.rounds, ettPrefix.series⟩
      have packageEq : oldPackage = newPackage := by
        exact Sigma.ext roundsPrefix.symm seriesPrefix.symm
      have transferred :
          2 * newPackage.1 + 11 ≤
            (TreeMissingColors phi
              (newPackage.2.data.tree (Fin.last newPackage.1).castSucc)).card := by
        rw [← packageEq]
        exact hlarge
      simpa [oldPackage, newPackage] using transferred
    terminalMinusClosed := by
      have rawStoredEq :
          (TashkinovStoredColors ettPrefix.series.data
              (Fin.last ettPrefix.rounds) \
            TreeMissingColors phi (H.stage r.castSucc)) =
          (TashkinovStoredColors ett.series.data
              (Fin.last ett.rounds) \
            TreeMissingColors phi (H.stage r.castSucc)) := by
        let oldPackage : Sigma (fun n : ℕ =>
            TashkinovSeries G k n e0 input) := ⟨ett.rounds, ett.series⟩
        let newPackage : Sigma (fun n : ℕ =>
            TashkinovSeries G k n e0 input) :=
          ⟨ettPrefix.rounds, ettPrefix.series⟩
        have hraw := congrArg (fun z =>
            (TashkinovStoredColors z.2.data (Fin.last z.1) \
              TreeMissingColors phi (H.stage r.castSucc)))
          (show oldPackage = newPackage from
            Sigma.ext roundsPrefix.symm seriesPrefix.symm)
        simpa [oldPackage, newPackage] using hraw.symm
      have terminalStoredEq : HierarchyTerminalStoredColors HP =
          HierarchyStoredColorsAt H r := by
        have hstar : HierarchyStarredStage H r = H.stage r.castSucc := by
          dsimp [HierarchyStarredStage, r]
        simpa [HierarchyTerminalStoredColors, HierarchyStoredColorsAt,
          hstar] using rawStoredEq
      have lastGammaEq : goodPrefix.gamma (Fin.last HP.dividerCount) =
          good.gamma ⟨r.val - 1, by omega⟩ := by
        have hcount : HP.dividerCount + 1 = r.val := by omega
        have hidx : Fin.last HP.dividerCount =
            Fin.cast hcount.symm ⟨r.val - 1, by omega⟩ := by
          apply Fin.ext
          simp [countPrefix]
        funext eta
        have hg := (gammaPrefix ⟨r.val - 1, by omega⟩).2 eta
        rw [hidx]
        exact hg
      rw [terminalStoredEq, lastGammaEq]
      exact terminalPrefix
    a := alpha
    b := beta
    a_ne_b := hne
    aMissing := halpha
    aClosed := hclosed
    a1 := a2
    b1 := b2
    a2 := a1
    b2 := b1
    P1 := P2
    P2 := P1
    exit1 := exit2
    exit2 := exit1
    disjoint12 := by
      intro x hx
      intro hbad
      exact (disjoint12 x hbad) hx
    outsideDistinct := outsideDistinct.symm
    treeDistinct := treeDistinct.symm
    treeOrder := orderReverse
    f1 := f2
    f2 := f1
    boundary1 := boundary2
    boundary2 := boundary1
    incident1 := incident2
    incident2 := incident1
    support1 := support2
    support2 := support1
  }⟩
