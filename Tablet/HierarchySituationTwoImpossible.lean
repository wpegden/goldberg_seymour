import Tablet.HierarchyCounterexampleTailAtLeastTwo
import Tablet.HierarchyCounterexampleTerminalCommonMissing
import Tablet.ExtendedTashkinovTree
import Tablet.HierarchyFullTailLength
import Tablet.HierarchyFullTailPrefix
import Tablet.HierarchyMinimumCounterexampleContext
import Tablet.HierarchyPathNumber
import Tablet.HierarchyReplacementPresentation
import Tablet.HierarchySituationTwoCaseOneData
import Tablet.HierarchySituationTwoCaseOneTwoData
import Tablet.HierarchySituationTwoCaseThreeData
import Tablet.HierarchySituationTwoCaseThreeNormalization
import Tablet.HierarchySituationTwoCaseThreeNormalizedData
import Tablet.HierarchySituationTwoCaseThreeOneData
import Tablet.HierarchySituationTwoCaseThreeTwoData
import Tablet.HierarchySituationTwoCaseTwoData
import Tablet.HierarchySituationTwoCaseTwoTwoData
import Tablet.HierarchySituationTwoCommonTailData
import Tablet.HierarchySituationTwoSubcaseOneOne
import Tablet.HierarchySituationTwoSubcaseOneTwo
import Tablet.HierarchySituationTwoSubcaseThreeOne
import Tablet.HierarchySituationTwoSubcaseThreeTwo
import Tablet.HierarchySituationTwoSubcaseTwoOne
import Tablet.HierarchySituationTwoSubcaseTwoTwo
import Tablet.HierarchyStoredColorsAt
import Tablet.HierarchyStarredStage
import Tablet.Incident
import Tablet.MissingColors
import Tablet.TashkinovAugmentation
import Tablet.TashkinovAugmentationSequence
import Tablet.TashkinovAugmentationSequenceRestrict
import Tablet.TashkinovClosure
import Tablet.TashkinovSeries
import Tablet.TashkinovSeriesStep
import Tablet.TreeSequence
import Tablet.TreeSequenceInitialSegment
import Tablet.TreeMissingColors

-- [TABLET NODE: HierarchySituationTwoImpossible]
theorem HierarchySituationTwoImpossible {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi)
    (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext
      G k e0 input T phi ett base C)
    (hsituation :
      HierarchyPathNumber C.hierarchy = HierarchyFullTailLength C) :
    False := by
-- BODY
  classical
  have htail : 2 ≤ T.length -
      (HierarchyStarredStage C.hierarchy
        (Fin.last C.hierarchy.dividerCount)).length := by
    exact HierarchyCounterexampleTailAtLeastTwo G k e0 input T phi ett base C
      ctx.proper ctx.oneEdgeUncolored ctx.lowerRung ctx.fewerDividers
      ctx.lexicographicMinimality ctx.largeMissingSet
  have hApos : 1 ≤ (HierarchyStarredStage C.hierarchy
      (Fin.last C.hierarchy.dividerCount)).length := by
    exact (HierarchyStarredStage C.hierarchy
      (Fin.last C.hierarchy.dividerCount)).positive
  have hTtwo : 2 ≤ T.length := by omega
  let lastEdgeIndex : Fin T.length := ⟨T.length - 1, by omega⟩
  let penultimateVertexIndex : Fin (T.length + 1) :=
    ⟨T.length - 1, by omega⟩
  let terminalVertexIndex : Fin (T.length + 1) := Fin.last T.length
  have hlastPos : lastEdgeIndex.val + 1 = T.length := by
    dsimp [lastEdgeIndex]
    omega
  have hpenPos : penultimateVertexIndex.val + 1 = T.length := by
    dsimp [penultimateVertexIndex]
    omega
  have htermPos : terminalVertexIndex.val = T.length := by
    simp [terminalVertexIndex]
  have hlastNeFirst : lastEdgeIndex ≠ (⟨0, T.positive⟩ : Fin T.length) := by
    intro h
    have : lastEdgeIndex.val = 0 := congrArg Fin.val h
    simp [lastEdgeIndex] at this
    omega
  have hedgeNe : T.edge lastEdgeIndex ≠ e0 := by
    intro he
    apply hlastNeFirst
    apply T.edge_injective
    simpa [T.first_edge] using he
  obtain ⟨theta, htheta⟩ := ctx.oneEdgeUncolored.2 _ hedgeNe
  let hcommon : HierarchySituationTwoCommonTailData
      G k e0 input T phi ett base C ctx := by
    refine ⟨htail, hsituation, lastEdgeIndex, penultimateVertexIndex,
      terminalVertexIndex, hlastPos, hpenPos, htermPos, ?_, theta, htheta⟩
    · intro hinc
      obtain ⟨i, hi⟩ := T.attaches lastEdgeIndex
      let ii : Fin (T.length + 1) := i.castLT (by omega)
      have hmem : T.vertex penultimateVertexIndex ∈
          s(T.vertex lastEdgeIndex.succ, T.vertex ii) := by
        change T.vertex penultimateVertexIndex ∈ G.ends (T.edge lastEdgeIndex) at hinc
        rw [hi] at hinc
        simpa [ii] using hinc
      have hcases := (Sym2.mem_iff.mp hmem)
      rcases hcases with hcase | hcase
      · have hv : T.vertex penultimateVertexIndex =
            T.vertex lastEdgeIndex.succ := hcase
        have hi' : penultimateVertexIndex = lastEdgeIndex.succ :=
          T.vertex_injective hv
        have hv' := congrArg Fin.val hi'
        simp [penultimateVertexIndex, lastEdgeIndex] at hv'
      · have hv : T.vertex penultimateVertexIndex = T.vertex ii := hcase
        have hi' : penultimateVertexIndex = ii := T.vertex_injective hv
        have hv' := congrArg Fin.val hi'
        have hlast : i.val < T.length := by omega
        dsimp [ii] at hi'
        dsimp [penultimateVertexIndex] at hv'
        have hii : ii = penultimateVertexIndex := hi'.symm
        have hends : G.ends (T.edge lastEdgeIndex) =
            s(T.vertex lastEdgeIndex.succ, T.vertex ii) := by
          simpa [ii] using hi
        have htarget : G.ends (T.edge lastEdgeIndex) =
            s(T.vertex penultimateVertexIndex,
              T.vertex terminalVertexIndex) := by
          rw [hends, hii]
          have hv : T.vertex lastEdgeIndex.succ =
              T.vertex terminalVertexIndex := by
            apply congrArg T.vertex
            apply Fin.ext
            simp [lastEdgeIndex, terminalVertexIndex]
            omega
          rw [hv]
          exact Sym2.eq_swap
        let H := C.hierarchy
        let A := HierarchyStarredStage H (Fin.last H.dividerCount)
        let ell := T.length - A.length
        let candidates := (Finset.Icc 1 ell).filter fun j =>
          ∀ r : Fin T.length, A.length + j ≤ r.val →
            G.ends (T.edge r) = s(T.vertex r.castSucc, T.vertex r.succ)
        have htailA : 2 ≤ T.length - A.length := by
          simpa [A, H] using htail
        have hAle : A.length ≤ T.length := by omega
        have hsum : A.length + ell = T.length :=
          Nat.add_sub_of_le hAle
        have hell : ell = T.length - A.length := rfl
        have hmem : ell - 1 ∈ candidates := by
          apply Finset.mem_filter.mpr
          refine ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
          intro r hr
          have hrval : r.val = T.length - 1 := by
            omega
          have heq : r = lastEdgeIndex := by
            apply Fin.ext
            simp [lastEdgeIndex, hrval]
          rw [heq]
          have hv₁ : T.vertex lastEdgeIndex.castSucc =
              T.vertex penultimateVertexIndex := by
            apply congrArg T.vertex
            apply Fin.ext
            simp [lastEdgeIndex, penultimateVertexIndex]
          have hv₂ : T.vertex lastEdgeIndex.succ =
              T.vertex terminalVertexIndex := by
            apply congrArg T.vertex
            apply Fin.ext
            simp [lastEdgeIndex, terminalVertexIndex]
            omega
          rw [hv₁, hv₂]
          exact htarget
        have hne : candidates.Nonempty := ⟨ell - 1, hmem⟩
        have hmin : candidates.min' hne ≤ ell - 1 :=
          Finset.min'_le candidates (ell - 1) hmem
        have hpath : HierarchyPathNumber C.hierarchy = candidates.min' hne := by
          simp [HierarchyPathNumber, H, A, ell, candidates, dif_pos hne]
        have heq : candidates.min' hne = ell := by
          calc
            candidates.min' hne = HierarchyPathNumber C.hierarchy := hpath.symm
            _ = HierarchyFullTailLength C := hsituation
            _ = ell := by rfl
        omega
  obtain ⟨alpha, halphaTree, halphaTerm⟩ :=
    HierarchyCounterexampleTerminalCommonMissing G k e0 input T phi ett base C
      ctx.proper ctx.oneEdgeUncolored ctx.lowerRung ctx.fewerDividers
      ctx.lexicographicMinimality ctx.largeMissingSet
  have halphaFinal : alpha ∈ MissingColors G phi
      (T.vertex terminalVertexIndex) := by
    simpa [terminalVertexIndex] using halphaTerm
  have hidxPen : hcommon.penultimateVertexIndex = penultimateVertexIndex := by rfl
  have hidxTerm : hcommon.terminalVertexIndex = terminalVertexIndex := by rfl
  by_cases hpen : alpha ∈ MissingColors G phi
      (T.vertex penultimateVertexIndex)
  · by_cases hstored : alpha ∈ HierarchyStoredColorsAt C.hierarchy
        (Fin.last C.hierarchy.dividerCount)
    · have hcard := C.good.twoColors (Fin.last C.hierarchy.dividerCount)
          alpha hstored
      obtain ⟨gammaOne, gammaTwo, hdistinct, hpair⟩ :=
        Finset.card_eq_two.mp hcard
      by_cases hmissing : theta ∈ MissingColors G phi
          (T.vertex penultimateVertexIndex)
      · let D : HierarchySituationTwoCaseOneTwoData
            G k e0 input T phi ett base C ctx :=
          ⟨hcommon, alpha, gammaOne, gammaTwo,
            (by simpa [hidxPen] using hpen),
            (by simpa [hidxTerm] using halphaFinal),
            hstored, by simpa using hpair, hdistinct, hmissing⟩
        exact HierarchySituationTwoSubcaseOneTwo
          G k e0 input T phi ett base C ctx D
      · let tail : HierarchySituationTwoTailData
            G k e0 input T phi ett base C ctx :=
          ⟨htail, hsituation, lastEdgeIndex, penultimateVertexIndex,
            terminalVertexIndex, hlastPos, hpenPos, htermPos,
            (by simpa using hcommon.lastEdgeNotIncidentPenultimate), theta,
            htheta, (by simpa [hidxPen] using hmissing)⟩
        let D : HierarchySituationTwoCaseOneData
            G k e0 input T phi ett base C ctx :=
          ⟨tail, alpha, gammaOne, gammaTwo, hpen, halphaFinal,
            hstored, by simpa using hpair, hdistinct⟩
        exact HierarchySituationTwoSubcaseOneOne
          G k e0 input T phi ett base C ctx D
    · by_cases hmissing : theta ∈ MissingColors G phi
          (T.vertex penultimateVertexIndex)
      · let D : HierarchySituationTwoCaseTwoTwoData
            G k e0 input T phi ett base C ctx :=
          ⟨hcommon, alpha, (by simpa [hidxPen] using hpen),
            (by simpa [hidxTerm] using halphaFinal), hstored,
            (by simpa [hidxPen] using hmissing)⟩
        exact HierarchySituationTwoSubcaseTwoTwo
          G k e0 input T phi ett base C ctx D
      · let tail : HierarchySituationTwoTailData
            G k e0 input T phi ett base C ctx :=
          ⟨htail, hsituation, lastEdgeIndex, penultimateVertexIndex,
            terminalVertexIndex, hlastPos, hpenPos, htermPos,
            (by simpa using hcommon.lastEdgeNotIncidentPenultimate), theta,
            htheta, (by simpa [hidxPen] using hmissing)⟩
        let D : HierarchySituationTwoCaseTwoData
            G k e0 input T phi ett base C ctx :=
          ⟨tail, alpha, hpen, halphaFinal, hstored⟩
        exact HierarchySituationTwoSubcaseTwoOne
          G k e0 input T phi ett base C ctx D
  · let Bplus := HierarchyFullTailPrefix C (HierarchyFullTailLength C - 1)
    have hB : alpha ∈ TreeMissingColors phi Bplus := by
      simpa [Bplus, HierarchyFullTailPrefix, HierarchyFullTailLength] using halphaTree
    simp [TreeMissingColors, TreeSequenceVertexSet] at hB
    obtain ⟨a, ha⟩ := hB
    have hBlen : Bplus.length = T.length - 1 := by
      change min ((HierarchyStarredStage C.hierarchy
        (Fin.last C.hierarchy.dividerCount)).length +
        (HierarchyFullTailLength C - 1)) T.length = T.length - 1
      have hA := (HierarchyStarredStage C.hierarchy
        (Fin.last C.hierarchy.dividerCount)).positive
      have hEll : HierarchyFullTailLength C = T.length -
          (HierarchyStarredStage C.hierarchy
            (Fin.last C.hierarchy.dividerCount)).length := by rfl
      rw [hEll]
      omega
    let earlierVertexIndex : Fin (T.length + 1) :=
      ⟨a.val, by have ha' := a.isLt; omega⟩
    have haMissing : alpha ∈ MissingColors G phi
        (T.vertex earlierVertexIndex) := by
      convert ha using 1
      apply congrArg (fun v => MissingColors G phi v)
      apply congrArg T.vertex
      apply Fin.ext
      rfl
    have hbefore : earlierVertexIndex.val < penultimateVertexIndex.val := by
      have hlt : earlierVertexIndex.val < T.length := by
        dsimp [earlierVertexIndex]
        have ha' := a.isLt
        omega
      have hne : earlierVertexIndex ≠ penultimateVertexIndex := by
        intro he
        apply hpen
        simpa [he] using haMissing
      have hle : earlierVertexIndex.val ≤ penultimateVertexIndex.val := by
        dsimp [penultimateVertexIndex]
        omega
      omega
    let D : HierarchySituationTwoCaseThreeData
        G k e0 input T phi ett base C ctx :=
      ⟨hcommon, alpha, (by simpa [hidxTerm] using halphaFinal),
        earlierVertexIndex, (by simpa using hbefore), haMissing⟩
    obtain ⟨P, hP⟩ := HierarchySituationTwoCaseThreeNormalization
      G k e0 input T phi ett base C ctx D
    obtain ⟨N⟩ := hP
    by_cases hmissing : N.theta ∈ MissingColors G P.coloring
        (T.vertex N.penultimateVertexIndex)
    · exact HierarchySituationTwoSubcaseThreeTwo
        G k e0 P.corresponding.replacementInput T P.coloring
        P.corresponding.replacementETT P.replacementBase P.counterexample
        P.minimumContext
        ⟨N, hmissing⟩
    · exact HierarchySituationTwoSubcaseThreeOne
        G k e0 P.corresponding.replacementInput T P.coloring
        P.corresponding.replacementETT P.replacementBase P.counterexample
        P.minimumContext
        ⟨N, hmissing⟩
