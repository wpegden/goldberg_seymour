import Tablet.ClosedColorExitPathBoundaryEdge
import Tablet.CorrespondingExtendedTashkinovTree
import Tablet.ElementaryClosedExitPairExtendsTriple
import Tablet.Step1ExitLegMinimum
import Tablet.Step1ExitLegPresentation
import Tablet.TreeExitPath
import Tablet.TreeSequence
import Tablet.TreeSequenceVertexSet
import Tablet.TreeVertexOrder

-- [TABLET NODE: Step1ExitLegMinimumExists]
theorem Step1ExitLegMinimumExists {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (n q : ℕ)
    (hfamily : Nonempty (Step1ExitLegPresentation G k e0 n q))
    (helementary : ∀ P : Step1ExitLegPresentation G k e0 n q,
      ColoredVertexSetElementary G P.phi (TreeSequenceVertexSet P.T)) :
    Nonempty (Step1ExitLegMinimum G k e0 n q) := by
-- BODY
  classical
  let DividerRealized (m : ℕ) : Prop :=
    ∃ P : Step1ExitLegPresentation G k e0 n q,
      P.hierarchy.dividerCount = m
  have hDividerRealized : ∃ m, DividerRealized m := by
    rcases hfamily with ⟨P⟩
    exact ⟨P.hierarchy.dividerCount, P, rfl⟩
  let d0 := Nat.find hDividerRealized
  have hd0_spec : DividerRealized d0 := Nat.find_spec hDividerRealized
  have hd0_min {P : Step1ExitLegPresentation G k e0 n q} :
      d0 ≤ P.hierarchy.dividerCount := by
    exact Nat.find_min' hDividerRealized ⟨P, rfl⟩

  let ThirdPackage (P : Step1ExitLegPresentation G k e0 n q)
      (a3 b3 : V)
      (P3 : (TwoColorIncidenceGraph G P.phi P.a P.b).Walk
        (Sum.inl a3) (Sum.inl b3))
      (f3 : E) : Prop :=
    TreeExitPath P.T P.phi P.a P.b a3 b3 P3 ∧
      (∀ x, x ∈ P.P1.support → x ∉ P3.support) ∧
      (∀ x, x ∈ P.P2.support → x ∉ P3.support) ∧
      P.a1 ≠ a3 ∧ P.a2 ≠ a3 ∧
      P.b1 ≠ b3 ∧ P.b2 ≠ b3 ∧
      f3 ∈ BoundaryColorEdges G P.phi
        (TreeSequenceVertexSet P.T) P.b ∧
      Incident G b3 f3 ∧ Sum.inr f3 ∈ P3.support

  let SecondaryRealized (s : ℕ) : Prop :=
    ∃ P : Step1ExitLegPresentation G k e0 n q,
      P.hierarchy.dividerCount = d0 ∧
      ((s = 0 ∧ P.b ∈ TreeMissingColors P.phi P.T) ∨
        (P.b ∉ TreeMissingColors P.phi P.T ∧
          ∃ (a3 b3 : V)
            (P3 : (TwoColorIncidenceGraph G P.phi P.a P.b).Walk
              (Sum.inl a3) (Sum.inl b3))
            (f3 : E),
            ThirdPackage P a3 b3 P3 f3 ∧
              s = 1 + P.P1.length + P.P2.length + P3.length))

  have hSecondaryRealized : ∃ s, SecondaryRealized s := by
    rcases hd0_spec with ⟨P, hPdiv⟩
    by_cases hb : P.b ∈ TreeMissingColors P.phi P.T
    · exact ⟨0, P, hPdiv, Or.inl ⟨rfl, hb⟩⟩
    · obtain ⟨a3, b3, P3, f3, hP3, h13, h23, ha31, ha32, hb31,
          hb32, hf3, hif3, hsf3⟩ :=
        ElementaryClosedExitPairExtendsTriple G P.T P.phi P.proper
          (helementary P) P.a P.b P.a_ne_b P.aMissing P.aClosed hb
          P.a1 P.b1 P.a2 P.b2 P.P1 P.P2 P.exit1 P.exit2
          P.disjoint12 P.outsideDistinct P.treeDistinct
      refine ⟨1 + P.P1.length + P.P2.length + P3.length, P, hPdiv,
        Or.inr ⟨hb, a3, b3, P3, f3, ?_, rfl⟩⟩
      exact ⟨hP3, h13, h23, ha31.symm, ha32.symm, hb31.symm,
        hb32.symm, hf3, hif3, hsf3⟩

  let s0 := Nat.find hSecondaryRealized
  have hs0_spec : SecondaryRealized s0 := Nat.find_spec hSecondaryRealized
  have hs0_min {s : ℕ} (hs : SecondaryRealized s) : s0 ≤ s :=
    Nat.find_min' hSecondaryRealized hs

  let PrimaryMinimal (S : Step1ExitLegPresentation G k e0 n q) : Prop :=
    ∀ (sigma : PartialEdgeColoring E k) (U : TreeSequence G e0)
      (corr : CorrespondingExtendedTashkinovTree G k e0 S.ett sigma U),
      IsProperEdgeColoring G sigma → IsOneEdgeUncolored sigma e0 →
      StableColoring
        (S.ett.series.data.tree (Fin.last S.ett.rounds).castSucc)
        (TashkinovStoredColors S.ett.series.data (Fin.last S.ett.rounds))
        S.phi sigma →
      MaximumProperty corr.replacementETT →
      ∀ (baseU : HierarchyBase corr.replacementETT sigma)
        (L : TashkinovHierarchy corr.replacementETT baseU)
        (goodU : GoodHierarchy L),
        L.dividerCount < S.hierarchy.dividerCount →
        2 * corr.replacementETT.rounds + 11 ≤
          (TreeMissingColors sigma
            (corr.replacementETT.series.data.tree
              (Fin.last corr.replacementETT.rounds).castSucc)).card →
        TreeColorSetMinusClosed G sigma U
          ((HierarchyTerminalStoredColors L).biUnion
            (goodU.gamma (Fin.last L.dividerCount))) →
        ∀ (c d : Fin k), c ≠ d →
          c ∈ TreeMissingColors sigma U →
          TreeColorSetClosed G sigma U {c} →
          ∀ (u1 v1 u2 v2 : V)
            (Q1 : (TwoColorIncidenceGraph G sigma c d).Walk
              (Sum.inl u1) (Sum.inl v1))
            (Q2 : (TwoColorIncidenceGraph G sigma c d).Walk
              (Sum.inl u2) (Sum.inl v2)),
            TreeExitPath U sigma c d u1 v1 Q1 →
            TreeExitPath U sigma c d u2 v2 Q2 →
            (∀ x, x ∈ Q1.support → x ∉ Q2.support) →
            u1 ≠ u2 → False

  have primaryFor (S : Step1ExitLegPresentation G k e0 n q)
      (hSdiv : S.hierarchy.dividerCount = d0) : PrimaryMinimal S := by
    dsimp only [PrimaryMinimal]
    intro sigma U corr hproper hone _hstable hmaximum baseU L goodU
      hdiv hlarge hminus c d hcne hcmissing hcclosed u1 v1 u2 v2 Q1 Q2
      hQ1 hQ2 hdisjoint hu12
    obtain ⟨f1, hf1, hif1, hsf1⟩ :=
      ClosedColorExitPathBoundaryEdge G U sigma c d hcclosed u1 v1 Q1 hQ1
    obtain ⟨f2, hf2, hif2, hsf2⟩ :=
      ClosedColorExitPathBoundaryEdge G U sigma c d hcclosed u2 v2 Q2 hQ2
    have hv12 : v1 ≠ v2 := by
      intro hv
      apply hdisjoint (Sum.inl v1) Q1.end_mem_support
      simpa [hv] using Q2.end_mem_support
    have hv1mem : v1 ∈ TreeSequenceVertexSet U := hQ1.2.2.2.1
    have hv2mem : v2 ∈ TreeSequenceVertexSet U := hQ2.2.2.2.1
    have hv1pos : ∃ i : Fin (U.length + 1), U.vertex i = v1 := by
      simpa [TreeSequenceVertexSet] using hv1mem
    have hv2pos : ∃ i : Fin (U.length + 1), U.vertex i = v2 := by
      simpa [TreeSequenceVertexSet] using hv2mem
    obtain ⟨i1, hi1⟩ := hv1pos
    obtain ⟨i2, hi2⟩ := hv2pos
    have hi12 : i1 ≠ i2 := by
      intro h
      apply hv12
      exact hi1.symm.trans ((congrArg U.vertex h).trans hi2)
    have hrounds : corr.replacementETT.rounds = n :=
      corr.rungAgreement.trans S.rounds_eq
    have hdividerLtQ : L.dividerCount < q := by
      exact lt_trans hdiv S.divider_lt
    have hreverse : ∀ x, x ∈ Q2.support → x ∉ Q1.support := by
      intro x hx2 hx1
      exact hdisjoint x hx1 hx2
    by_cases horder : i1.val < i2.val
    · let R : Step1ExitLegPresentation G k e0 n q :=
        { input := corr.replacementInput
          T := U
          phi := sigma
          ett := corr.replacementETT
          base := baseU
          hierarchy := L
          good := goodU
          rounds_eq := hrounds
          maximum := hmaximum
          divider_lt := hdividerLtQ
          proper := hproper
          oneUncolored := hone
          large := hlarge
          terminalMinusClosed := hminus
          a := c
          b := d
          a_ne_b := hcne
          aMissing := hcmissing
          aClosed := hcclosed
          a1 := u1
          b1 := v1
          a2 := u2
          b2 := v2
          P1 := Q1
          P2 := Q2
          exit1 := hQ1
          exit2 := hQ2
          disjoint12 := hdisjoint
          outsideDistinct := hu12
          treeDistinct := hv12
          treeOrder := ⟨i1, i2, hi1, hi2, horder⟩
          f1 := f1
          f2 := f2
          boundary1 := hf1
          boundary2 := hf2
          incident1 := hif1
          incident2 := hif2
          support1 := hsf1
          support2 := hsf2 }
      have hmin := hd0_min (P := R)
      dsimp only [R] at hmin
      omega
    · have horder' : i2.val < i1.val := by omega
      let R : Step1ExitLegPresentation G k e0 n q :=
        { input := corr.replacementInput
          T := U
          phi := sigma
          ett := corr.replacementETT
          base := baseU
          hierarchy := L
          good := goodU
          rounds_eq := hrounds
          maximum := hmaximum
          divider_lt := hdividerLtQ
          proper := hproper
          oneUncolored := hone
          large := hlarge
          terminalMinusClosed := hminus
          a := c
          b := d
          a_ne_b := hcne
          aMissing := hcmissing
          aClosed := hcclosed
          a1 := u2
          b1 := v2
          a2 := u1
          b2 := v1
          P1 := Q2
          P2 := Q1
          exit1 := hQ2
          exit2 := hQ1
          disjoint12 := hreverse
          outsideDistinct := hu12.symm
          treeDistinct := hv12.symm
          treeOrder := ⟨i2, i1, hi2, hi1, horder'⟩
          f1 := f2
          f2 := f1
          boundary1 := hf2
          boundary2 := hf1
          incident1 := hif2
          incident2 := hif1
          support1 := hsf2
          support2 := hsf1 }
      have hmin := hd0_min (P := R)
      dsimp only [R] at hmin
      omega

  let SecondaryMinimal (S : Step1ExitLegPresentation G k e0 n q)
      {a3 b3 : V}
      (P3 : (TwoColorIncidenceGraph G S.phi S.a S.b).Walk
        (Sum.inl a3) (Sum.inl b3)) : Prop :=
    ∀ (sigma : PartialEdgeColoring E k) (U : TreeSequence G e0)
      (corr : CorrespondingExtendedTashkinovTree G k e0 S.ett sigma U),
      IsProperEdgeColoring G sigma → IsOneEdgeUncolored sigma e0 →
      StableColoring
        (S.ett.series.data.tree (Fin.last S.ett.rounds).castSucc)
        (TashkinovStoredColors S.ett.series.data (Fin.last S.ett.rounds))
        S.phi sigma →
      MaximumProperty corr.replacementETT →
      ∀ (baseU : HierarchyBase corr.replacementETT sigma)
        (L : TashkinovHierarchy corr.replacementETT baseU)
        (goodU : GoodHierarchy L),
        L.dividerCount = S.hierarchy.dividerCount →
        2 * corr.replacementETT.rounds + 11 ≤
          (TreeMissingColors sigma
            (corr.replacementETT.series.data.tree
              (Fin.last corr.replacementETT.rounds).castSucc)).card →
        TreeColorSetMinusClosed G sigma U
          ((HierarchyTerminalStoredColors L).biUnion
            (goodU.gamma (Fin.last L.dividerCount))) →
        ∀ (c d : Fin k), c ≠ d →
          c ∈ TreeMissingColors sigma U →
          TreeColorSetClosed G sigma U {c} →
          ∀ (u1 v1 u2 v2 : V)
            (Q1 : (TwoColorIncidenceGraph G sigma c d).Walk
              (Sum.inl u1) (Sum.inl v1))
            (Q2 : (TwoColorIncidenceGraph G sigma c d).Walk
              (Sum.inl u2) (Sum.inl v2)),
            TreeExitPath U sigma c d u1 v1 Q1 →
            TreeExitPath U sigma c d u2 v2 Q2 →
            (∀ x, x ∈ Q1.support → x ∉ Q2.support) →
            u1 ≠ u2 →
            (d ∈ TreeMissingColors sigma U ∨
              (d ∉ TreeMissingColors sigma U ∧
                ∃ (u3 v3 : V)
                  (Q3 : (TwoColorIncidenceGraph G sigma c d).Walk
                    (Sum.inl u3) (Sum.inl v3)),
                  TreeExitPath U sigma c d u3 v3 Q3 ∧
                  (∀ x, x ∈ Q1.support → x ∉ Q3.support) ∧
                  (∀ x, x ∈ Q2.support → x ∉ Q3.support) ∧
                  u1 ≠ u3 ∧ u2 ≠ u3 ∧
                  Q1.length + Q2.length + Q3.length <
                    S.P1.length + S.P2.length + P3.length)) →
            False

  have secondaryFor (S : Step1ExitLegPresentation G k e0 n q)
      (hSdiv : S.hierarchy.dividerCount = d0)
      {a3 b3 : V}
      (P3 : (TwoColorIncidenceGraph G S.phi S.a S.b).Walk
        (Sum.inl a3) (Sum.inl b3))
      (hvalue : s0 = 1 + S.P1.length + S.P2.length + P3.length) :
      SecondaryMinimal S P3 := by
    dsimp only [SecondaryMinimal]
    intro sigma U corr hproper hone _hstable hmaximum baseU L goodU
      hdiv hlarge hminus c d hcne hcmissing hcclosed u1 v1 u2 v2 Q1 Q2
      hQ1 hQ2 hdisjoint hu12 hshorter
    obtain ⟨f1, hf1, hif1, hsf1⟩ :=
      ClosedColorExitPathBoundaryEdge G U sigma c d hcclosed u1 v1 Q1 hQ1
    obtain ⟨f2, hf2, hif2, hsf2⟩ :=
      ClosedColorExitPathBoundaryEdge G U sigma c d hcclosed u2 v2 Q2 hQ2
    have hv12 : v1 ≠ v2 := by
      intro hv
      apply hdisjoint (Sum.inl v1) Q1.end_mem_support
      simpa [hv] using Q2.end_mem_support
    have hv1mem : v1 ∈ TreeSequenceVertexSet U := hQ1.2.2.2.1
    have hv2mem : v2 ∈ TreeSequenceVertexSet U := hQ2.2.2.2.1
    have hv1pos : ∃ i : Fin (U.length + 1), U.vertex i = v1 := by
      simpa [TreeSequenceVertexSet] using hv1mem
    have hv2pos : ∃ i : Fin (U.length + 1), U.vertex i = v2 := by
      simpa [TreeSequenceVertexSet] using hv2mem
    obtain ⟨i1, hi1⟩ := hv1pos
    obtain ⟨i2, hi2⟩ := hv2pos
    have hi12 : i1 ≠ i2 := by
      intro h
      apply hv12
      exact hi1.symm.trans ((congrArg U.vertex h).trans hi2)
    have hrounds : corr.replacementETT.rounds = n :=
      corr.rungAgreement.trans S.rounds_eq
    have hdividerLtQ : L.dividerCount < q := by
      rw [hdiv]
      exact S.divider_lt
    have hreverse : ∀ x, x ∈ Q2.support → x ∉ Q1.support := by
      intro x hx2 hx1
      exact hdisjoint x hx1 hx2
    by_cases horder : i1.val < i2.val
    · let R : Step1ExitLegPresentation G k e0 n q :=
        { input := corr.replacementInput
          T := U
          phi := sigma
          ett := corr.replacementETT
          base := baseU
          hierarchy := L
          good := goodU
          rounds_eq := hrounds
          maximum := hmaximum
          divider_lt := hdividerLtQ
          proper := hproper
          oneUncolored := hone
          large := hlarge
          terminalMinusClosed := hminus
          a := c
          b := d
          a_ne_b := hcne
          aMissing := hcmissing
          aClosed := hcclosed
          a1 := u1
          b1 := v1
          a2 := u2
          b2 := v2
          P1 := Q1
          P2 := Q2
          exit1 := hQ1
          exit2 := hQ2
          disjoint12 := hdisjoint
          outsideDistinct := hu12
          treeDistinct := hv12
          treeOrder := ⟨i1, i2, hi1, hi2, horder⟩
          f1 := f1
          f2 := f2
          boundary1 := hf1
          boundary2 := hf2
          incident1 := hif1
          incident2 := hif2
          support1 := hsf1
          support2 := hsf2 }
      have hRdiv : R.hierarchy.dividerCount = d0 := by
        dsimp only [R]
        exact hdiv.trans hSdiv
      rcases hshorter with hdmissing | ⟨hdpresent, u3, v3, Q3, hQ3,
          h13, h23, hu13, hu23, hlength⟩
      · have hreal : SecondaryRealized 0 := by
          refine ⟨R, hRdiv, Or.inl ⟨rfl, ?_⟩⟩
          simpa [R] using hdmissing
        have hmin := hs0_min hreal
        omega
      · obtain ⟨f3, hf3, hif3, hsf3⟩ :=
          ClosedColorExitPathBoundaryEdge G U sigma c d hcclosed
            u3 v3 Q3 hQ3
        have hv13 : v1 ≠ v3 := by
          intro hv
          apply h13 (Sum.inl v1) Q1.end_mem_support
          simpa [hv] using Q3.end_mem_support
        have hv23 : v2 ≠ v3 := by
          intro hv
          apply h23 (Sum.inl v2) Q2.end_mem_support
          simpa [hv] using Q3.end_mem_support
        have hreal : SecondaryRealized
            (1 + Q1.length + Q2.length + Q3.length) := by
          refine ⟨R, hRdiv, Or.inr ⟨?_, u3, v3, Q3, f3, ?_, ?_⟩⟩
          · simpa [R] using hdpresent
          · exact ⟨hQ3, h13, h23, hu13, hu23, hv13, hv23,
              hf3, hif3, hsf3⟩
          · rfl
        have hmin := hs0_min hreal
        omega
    · have horder' : i2.val < i1.val := by omega
      let R : Step1ExitLegPresentation G k e0 n q :=
        { input := corr.replacementInput
          T := U
          phi := sigma
          ett := corr.replacementETT
          base := baseU
          hierarchy := L
          good := goodU
          rounds_eq := hrounds
          maximum := hmaximum
          divider_lt := hdividerLtQ
          proper := hproper
          oneUncolored := hone
          large := hlarge
          terminalMinusClosed := hminus
          a := c
          b := d
          a_ne_b := hcne
          aMissing := hcmissing
          aClosed := hcclosed
          a1 := u2
          b1 := v2
          a2 := u1
          b2 := v1
          P1 := Q2
          P2 := Q1
          exit1 := hQ2
          exit2 := hQ1
          disjoint12 := hreverse
          outsideDistinct := hu12.symm
          treeDistinct := hv12.symm
          treeOrder := ⟨i2, i1, hi2, hi1, horder'⟩
          f1 := f2
          f2 := f1
          boundary1 := hf2
          boundary2 := hf1
          incident1 := hif2
          incident2 := hif1
          support1 := hsf2
          support2 := hsf1 }
      have hRdiv : R.hierarchy.dividerCount = d0 := by
        dsimp only [R]
        exact hdiv.trans hSdiv
      rcases hshorter with hdmissing | ⟨hdpresent, u3, v3, Q3, hQ3,
          h13, h23, hu13, hu23, hlength⟩
      · have hreal : SecondaryRealized 0 := by
          refine ⟨R, hRdiv, Or.inl ⟨rfl, ?_⟩⟩
          simpa [R] using hdmissing
        have hmin := hs0_min hreal
        omega
      · obtain ⟨f3, hf3, hif3, hsf3⟩ :=
          ClosedColorExitPathBoundaryEdge G U sigma c d hcclosed
            u3 v3 Q3 hQ3
        have hv13 : v1 ≠ v3 := by
          intro hv
          apply h13 (Sum.inl v1) Q1.end_mem_support
          simpa [hv] using Q3.end_mem_support
        have hv23 : v2 ≠ v3 := by
          intro hv
          apply h23 (Sum.inl v2) Q2.end_mem_support
          simpa [hv] using Q3.end_mem_support
        have hreal : SecondaryRealized
            (1 + Q1.length + Q2.length + Q3.length) := by
          refine ⟨R, hRdiv, Or.inr ⟨?_, u3, v3, Q3, f3, ?_, ?_⟩⟩
          · simpa [R] using hdpresent
          · exact ⟨hQ3, h23, h13, hu23, hu13, hv23, hv13,
              hf3, hif3, hsf3⟩
          · dsimp only [R]
            omega
        have hmin := hs0_min hreal
        omega

  have finishPositive (S : Step1ExitLegPresentation G k e0 n q)
      (hSdiv : S.hierarchy.dividerCount = d0)
      {a3 b3 : V}
      (P3 : (TwoColorIncidenceGraph G S.phi S.a S.b).Walk
        (Sum.inl a3) (Sum.inl b3))
      (f3 : E)
      (hbnot : S.b ∉ TreeMissingColors S.phi S.T)
      (hP3 : TreeExitPath S.T S.phi S.a S.b a3 b3 P3)
      (h13 : ∀ x, x ∈ S.P1.support → x ∉ P3.support)
      (h23 : ∀ x, x ∈ S.P2.support → x ∉ P3.support)
      (ha13 : S.a1 ≠ a3) (ha23 : S.a2 ≠ a3)
      (hb13 : S.b1 ≠ b3) (hb23 : S.b2 ≠ b3)
      (horder : TreeVertexOrder S.T S.b2 b3)
      (hf3 : f3 ∈ BoundaryColorEdges G S.phi
        (TreeSequenceVertexSet S.T) S.b)
      (hif3 : Incident G b3 f3) (hsf3 : Sum.inr f3 ∈ P3.support)
      (hvalue : s0 = 1 + S.P1.length + S.P2.length + P3.length) :
      Nonempty (Step1ExitLegMinimum G k e0 n q) := by
    refine ⟨{
      selected := S
      elementary := helementary S
      primaryMinimal := primaryFor S hSdiv
      secondary := Or.inr ⟨hbnot, a3, b3, P3, f3, hP3, h13, h23,
        ha13, ha23, hb13, hb23, horder, hf3, hif3, hsf3,
        secondaryFor S hSdiv P3 hvalue⟩ }⟩

  rcases hs0_spec with ⟨P, hPdiv, hzero | hpositive⟩
  · refine ⟨{
        selected := P
        elementary := helementary P
        primaryMinimal := primaryFor P hPdiv
        secondary := Or.inl ?_ }⟩
    exact hzero.2
  · rcases hpositive with ⟨hbnot, a3, b3, P3, f3, hthird, hvalue⟩
    dsimp only [ThirdPackage] at hthird
    rcases hthird with ⟨hP3, h13, h23, ha13, ha23, hb13, hb23,
      hf3, hif3, hsf3⟩
    have h31 : ∀ x, x ∈ P3.support → x ∉ P.P1.support := by
      intro x hx3 hx1
      exact h13 x hx1 hx3
    have h32 : ∀ x, x ∈ P3.support → x ∉ P.P2.support := by
      intro x hx3 hx2
      exact h23 x hx2 hx3
    have h21 : ∀ x, x ∈ P.P2.support → x ∉ P.P1.support := by
      intro x hx2 hx1
      exact P.disjoint12 x hx1 hx2
    have hb1mem : P.b1 ∈ TreeSequenceVertexSet P.T := P.exit1.2.2.2.1
    have hb2mem : P.b2 ∈ TreeSequenceVertexSet P.T := P.exit2.2.2.2.1
    have hb3mem : b3 ∈ TreeSequenceVertexSet P.T := hP3.2.2.2.1
    have hb1pos : ∃ i : Fin (P.T.length + 1), P.T.vertex i = P.b1 := by
      simpa [TreeSequenceVertexSet] using hb1mem
    have hb2pos : ∃ i : Fin (P.T.length + 1), P.T.vertex i = P.b2 := by
      simpa [TreeSequenceVertexSet] using hb2mem
    have hb3pos : ∃ i : Fin (P.T.length + 1), P.T.vertex i = b3 := by
      simpa [TreeSequenceVertexSet] using hb3mem
    obtain ⟨i1, hi1⟩ := hb1pos
    obtain ⟨i2, hi2⟩ := hb2pos
    obtain ⟨i3, hi3⟩ := hb3pos
    rcases P.treeOrder with ⟨j1, j2, hj1, hj2, hj12⟩
    have hi1j1 : i1 = j1 :=
      P.T.vertex_injective (hi1.trans hj1.symm)
    have hi2j2 : i2 = j2 :=
      P.T.vertex_injective (hi2.trans hj2.symm)
    have hi12 : i1.val < i2.val := by omega
    have hi31ne : i3.val ≠ i1.val := by
      intro h
      have heq : i3 = i1 := Fin.ext h
      apply hb13
      exact hi1.symm.trans ((congrArg P.T.vertex heq.symm).trans hi3)
    have hi32ne : i3.val ≠ i2.val := by
      intro h
      have heq : i3 = i2 := Fin.ext h
      apply hb23
      exact hi2.symm.trans ((congrArg P.T.vertex heq.symm).trans hi3)
    by_cases hi31 : i3.val < i1.val
    · let S : Step1ExitLegPresentation G k e0 n q :=
        { input := P.input
          T := P.T
          phi := P.phi
          ett := P.ett
          base := P.base
          hierarchy := P.hierarchy
          good := P.good
          rounds_eq := P.rounds_eq
          maximum := P.maximum
          divider_lt := P.divider_lt
          proper := P.proper
          oneUncolored := P.oneUncolored
          large := P.large
          terminalMinusClosed := P.terminalMinusClosed
          a := P.a
          b := P.b
          a_ne_b := P.a_ne_b
          aMissing := P.aMissing
          aClosed := P.aClosed
          a1 := a3
          b1 := b3
          a2 := P.a1
          b2 := P.b1
          P1 := P3
          P2 := P.P1
          exit1 := hP3
          exit2 := P.exit1
          disjoint12 := h31
          outsideDistinct := ha13.symm
          treeDistinct := hb13.symm
          treeOrder := ⟨i3, i1, hi3, hi1, hi31⟩
          f1 := f3
          f2 := P.f1
          boundary1 := hf3
          boundary2 := P.boundary1
          incident1 := hif3
          incident2 := P.incident1
          support1 := hsf3
          support2 := P.support1 }
      apply finishPositive S (by simpa [S] using hPdiv)
        P.P2 P.f2
      · simpa [S] using hbnot
      · exact P.exit2
      · exact h32
      · exact P.disjoint12
      · exact ha23.symm
      · exact P.outsideDistinct
      · exact hb23.symm
      · exact P.treeDistinct
      · exact ⟨i1, i2, hi1, hi2, hi12⟩
      · exact P.boundary2
      · exact P.incident2
      · exact P.support2
      · dsimp only [S]
        omega
    · have hi13 : i1.val < i3.val := by omega
      by_cases hi32 : i3.val < i2.val
      · let S : Step1ExitLegPresentation G k e0 n q :=
          { input := P.input
            T := P.T
            phi := P.phi
            ett := P.ett
            base := P.base
            hierarchy := P.hierarchy
            good := P.good
            rounds_eq := P.rounds_eq
            maximum := P.maximum
            divider_lt := P.divider_lt
            proper := P.proper
            oneUncolored := P.oneUncolored
            large := P.large
            terminalMinusClosed := P.terminalMinusClosed
            a := P.a
            b := P.b
            a_ne_b := P.a_ne_b
            aMissing := P.aMissing
            aClosed := P.aClosed
            a1 := P.a1
            b1 := P.b1
            a2 := a3
            b2 := b3
            P1 := P.P1
            P2 := P3
            exit1 := P.exit1
            exit2 := hP3
            disjoint12 := h13
            outsideDistinct := ha13
            treeDistinct := hb13
            treeOrder := ⟨i1, i3, hi1, hi3, hi13⟩
            f1 := P.f1
            f2 := f3
            boundary1 := P.boundary1
            boundary2 := hf3
            incident1 := P.incident1
            incident2 := hif3
            support1 := P.support1
            support2 := hsf3 }
        apply finishPositive S (by simpa [S] using hPdiv)
          P.P2 P.f2
        · simpa [S] using hbnot
        · exact P.exit2
        · exact P.disjoint12
        · exact h32
        · exact P.outsideDistinct
        · exact ha23.symm
        · exact P.treeDistinct
        · exact hb23.symm
        · exact ⟨i3, i2, hi3, hi2, hi32⟩
        · exact P.boundary2
        · exact P.incident2
        · exact P.support2
        · dsimp only [S]
          omega
      · have hi23 : i2.val < i3.val := by omega
        exact finishPositive P hPdiv P3 f3 hbnot hP3 h13 h23
          ha13 ha23 hb13 hb23 ⟨i2, i3, hi2, hi3, hi23⟩
          hf3 hif3 hsf3 hvalue
