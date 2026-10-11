import Tablet.P2880_T1_SplitSwapData
import Tablet.GoodHierarchyTerminalPrefixRepackage
import Tablet.HierarchyLEMStable
import Tablet.HierarchySplitter
import Tablet.Td
import Tablet.MaximumPropertyTransport
import Tablet.HierarchyFirstMissingPositionPrefixCutoff
import Tablet.P2752_T2_TerminalStoredColors
import Tablet.TreeSequenceInitialSegmentVertexSetSubset
import Tablet.TashkinovAugmentationSequenceInitialSegment
import Tablet.GoodHierarchySameDividerTransport
import Tablet.GoodHierarchySameDividerReconstruction
import Tablet.CorrespondingExtendedTashkinovTreeTransTrees

-- [TABLET NODE: P2880_T1_OutsidePrefixBranch]
theorem P2880_T1_OutsidePrefixBranch
    {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : Nat) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi)
    (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext
      G k e0 input T phi ett base C)
    (P : HierarchyReplacementPresentation
      G k e0 input T phi ett base C ctx)
    (alpha beta : Fin k) (sigma : PartialEdgeColoring E k)
    (S : P2880_T1_SplitSwapData G k e0 input T phi ett base C ctx P
      alpha beta sigma)
    (hneither : ¬ (
      let H := P.counterexample.hierarchy
      let q := Fin.last H.dividerCount
      let m := P.corresponding.replacementETT
      let n := Fin.last m.rounds
      let A := HierarchyStarredStage H q
      let Tnq := H.stage ⟨H.dividerCount, by omega⟩
      let Tn := m.series.data.tree n.castSucc
      let Dn := TashkinovStoredColors m.series.data n
      let qualifies := fun (a b : Fin k) =>
        (0 < H.dividerCount ∧ a ∈ TreeMissingColors P.coloring Tnq) ∨
        (H.dividerCount = 0 ∧
          (a ∈ TreeMissingColors P.coloring Tn ∨
            (a ∈ TreeMissingColors P.coloring A ∧ a ∉ Dn ∧ b ∉ Dn)))
      qualifies alpha beta ∨ qualifies beta alpha)) :
    ∃ corr : CorrespondingExtendedTashkinovTree G k e0
        P.corresponding.replacementETT sigma T,
      MaximumProperty corr.replacementETT ∧
      ∃ newBase : HierarchyBase corr.replacementETT sigma,
        ∃ K : TashkinovHierarchy corr.replacementETT newBase,
          ∃ good : GoodHierarchy K,
            SameGoodHierarchy P.counterexample.good good := by
-- BODY
  classical
  let X := HierarchyFullTailPrefix C (HierarchyPathNumber C.hierarchy - 1)
  let m := P.corresponding.replacementETT
  let H := P.counterexample.hierarchy
  let q := Fin.last H.dividerCount
  have hprefix := GoodHierarchyTerminalPrefixRepackage G k e0
    P.corresponding.replacementInput T P.coloring P.coloring m P.maximum
    P.replacementBase H P.counterexample.good X S.splitAboveStar.1
    S.splitAboveStar.2 S.splitInFull
  obtain ⟨ettX, hMPX, hroundX, hseriesX, baseX, hcoreX, hclosureX,
    hsuppX, HX, hcountX, hstagesX, hpositionsX, goodX, hcolorsX⟩ := hprefix
  have hrecolorX : OutsideKempeRecoloring X P.coloring sigma alpha beta := by
    refine ⟨S.distinct, {Sum.inl (T.vertex (Fin.last T.length))}, ?_, ?_⟩
    · intro z hz v hv
      simp only [Finset.mem_singleton] at hz
      subst z
      intro hvX
      exact S.splitOutside v hvX hv
    · intro f
      have hswap := S.swapped
      rw [hswap]
      simp [TwoColorComponentSwap]
  have hlowerX : ∀ {input' : PartialEdgeColoring E k}
      {T' : TreeSequence G e0} {generating' : PartialEdgeColoring E k}
      (lower : ExtendedTashkinovTree G k e0 input' T' generating'),
      0 < lower.rounds → lower.rounds < ettX.rounds →
      MaximumProperty lower →
      ColoredVertexSetElementary G generating' (TreeSequenceVertexSet T') ∧
        (let n : Fin (lower.rounds + 1) := Fin.last lower.rounds
         let Tnext := lower.series.data.tree (Fin.last (lower.rounds + 1))
         ∀ sigma : PartialEdgeColoring E k,
           IsProperEdgeColoring G sigma → IsOneEdgeUncolored sigma e0 →
           StableColoring Tnext (TashkinovStoredColors lower.series.data n)
             (lower.series.data.coloring n) sigma →
           ∀ alpha beta : Fin k,
             alpha ∈ TreeMissingColors sigma Tnext ∨
               beta ∈ TreeMissingColors sigma Tnext →
             TreeInterchangeable G Tnext sigma alpha beta) ∧
        ((∀ (q : Fin lower.rounds) (v : V),
          lower.series.data.kind q.succ = some TashkinovExtensionKind.PE →
          lower.series.data.chosenVertex q.succ = some v →
          ∀ (hvFinal : v ∈ TreeSequenceVertexSet T')
            (j : Fin (lower.rounds + 1)),
          ETTFirstAppearanceIndex lower v hvFinal = j.val + 1 →
          ∀ sigma : PartialEdgeColoring E k,
            IsProperEdgeColoring G sigma → IsOneEdgeUncolored sigma e0 →
            StableColoring (lower.series.data.tree q.succ.castSucc)
              (TashkinovStoredColors lower.series.data q.succ)
              (lower.series.data.coloring q.succ) sigma →
            StableColoringBeforeVertex T' v hvFinal
              (TashkinovStoredColors lower.series.data j)
              (lower.series.data.coloring j) sigma ∧
              (0 < j.val → StableColoring (lower.series.data.tree j.castSucc)
                (TashkinovStoredColors lower.series.data j)
                (lower.series.data.coloring j) sigma)) ∧
          ∀ (q r : Fin lower.rounds) (vq vr : V),
            q ≠ r → vq ≠ vr →
            lower.series.data.kind q.succ = some TashkinovExtensionKind.PE →
            lower.series.data.kind r.succ = some TashkinovExtensionKind.PE →
            lower.series.data.chosenVertex q.succ = some vq →
            lower.series.data.chosenVertex r.succ = some vr →
            ∀ (hvq : vq ∈ TreeSequenceVertexSet T')
              (hvr : vr ∈ TreeSequenceVertexSet T'),
            ETTFirstAppearanceIndex lower vq hvq =
              ETTFirstAppearanceIndex lower vr hvr →
            Disjoint (lower.series.data.stored q.succ)
              (lower.series.data.stored r.succ)) ∧
        (let n : Fin (lower.rounds + 1) := Fin.last lower.rounds
         let Tn := lower.series.data.tree n.castSucc
         ∀ (v : V) (gamma delta : Fin k),
           lower.series.data.kind n = some TashkinovExtensionKind.PE →
           lower.series.data.chosenVertex n = some v →
           lower.series.data.gamma n = some gamma →
           lower.series.data.delta n = some delta →
           ∀ sigma : PartialEdgeColoring E k,
             IsProperEdgeColoring G sigma → IsOneEdgeUncolored sigma e0 →
             StableColoring Tn (TashkinovStoredColors lower.series.data n)
               (lower.series.data.coloring n) sigma →
             ∀ w, w ∈ TreeSequenceVertexSet Tn →
               (Sum.inl w ∈ TwoColorComponent G sigma gamma delta
                 (Sum.inl v) ↔ w = v)) ∧
        (let n : Fin (lower.rounds + 1) := Fin.last lower.rounds
         let Tn := lower.series.data.tree n.castSucc
         ∀ sigma : PartialEdgeColoring E k,
           IsProperEdgeColoring G sigma → IsOneEdgeUncolored sigma e0 →
           StableColoring Tn (TashkinovStoredColors lower.series.data n)
             (lower.series.data.coloring n) sigma →
           ∀ delta : Fin k,
             DefectiveColor G sigma (TreeSequenceVertexSet Tn) delta →
             ∀ v, BoundaryColorVertex G sigma (TreeSequenceVertexSet Tn)
                 delta v →
               (∃ w, BoundaryColorVertex G sigma
                   (TreeSequenceVertexSet Tn) delta w ∧ TreeVertexOrder Tn w v) →
               ∀ (hvFinal : v ∈ TreeSequenceVertexSet T')
                 (q : Fin lower.rounds) (vi : V),
                 (lower.series.data.kind q.succ =
                     some TashkinovExtensionKind.PE ∨
                   lower.series.data.kind q.succ =
                     some TashkinovExtensionKind.SE) →
                 lower.series.data.chosenVertex q.succ = some vi →
                 ETTFirstAppearanceIndex lower v hvFinal ≤ q.val + 1 →
                 (v = vi ∨ TreeVertexOrder T' v vi)) ∧
        (let n : Fin (lower.rounds + 1) := Fin.last lower.rounds
         let Tn := lower.series.data.tree n.castSucc
         ∀ sigma : PartialEdgeColoring E k,
           IsProperEdgeColoring G sigma → IsOneEdgeUncolored sigma e0 →
           StableColoring Tn (TashkinovStoredColors lower.series.data n)
             (lower.series.data.coloring n) sigma → ModColoring lower sigma) := by
    intro input' T' generating' lower hpos hlt hmax
    have hlt' : lower.rounds < m.rounds := by
      rw [← hroundX]
      exact hlt
    exact P.minimumContext.lowerRung lower hpos hlt' hmax
  have hlem := HierarchyLEMStable G k e0 P.corresponding.replacementInput X
    P.coloring sigma ettX hMPX (by
      simpa [hroundX] using P.counterexample.positive)
    hlowerX baseX HX goodX P.minimumContext.proper
    P.minimumContext.oneEdgeUncolored alpha beta hrecolorX
  rcases hlem with ⟨hsigmaProper, hsigmaOne, hstableX, hinvariantX,
    corrX, hmaximumX, baseSigmaX, KX, goodSigmaX, hsameX, hclosedX⟩
  let n := Fin.last m.rounds
  let Tn := m.series.data.tree n.castSucc
  let Dn := TashkinovStoredColors m.series.data n
  have segmentTrans {A B C : TreeSequence G e0}
      (hAB : TreeSequenceInitialSegment A B)
      (hBC : TreeSequenceInitialSegment B C) :
      TreeSequenceInitialSegment A C := by
    rcases hAB with ⟨hab, hvab, heab⟩
    rcases hBC with ⟨hbc, hvbc, hebc⟩
    refine ⟨le_trans hab hbc, ?_, ?_⟩
    · intro i
      calc
        C.vertex (Fin.castLE (Nat.succ_le_succ hbc)
            (Fin.castLE (Nat.succ_le_succ hab) i)) =
            B.vertex (Fin.castLE (Nat.succ_le_succ hab) i) :=
          hvbc (Fin.castLE (Nat.succ_le_succ hab) i)
        _ = A.vertex i := hvab i
    · intro i
      calc
        C.edge (Fin.castLE hbc (Fin.castLE hab i)) = B.edge (Fin.castLE hab i) :=
          hebc _
        _ = A.edge i := heab i
  have hTnCore : TreeSequenceInitialSegment Tn P.replacementBase.core := by
    change TreeSequenceInitialSegment Tn P.replacementBase.core
    by_cases hpe : m.series.data.kind n = some TashkinovExtensionKind.PE
    · obtain ⟨_, _, ⟨u⟩⟩ := P.replacementBase.parallel hpe
      exact u.leftSegment
    · rw [P.replacementBase.nonparallel hpe]
      exact ⟨le_rfl, (by intro i; rfl), (by intro i; rfl)⟩
  have hTnX : TreeSequenceInitialSegment Tn X :=
    segmentTrans hTnCore S.coreInSplit
  have hTnXvertices : TreeSequenceVertexSet Tn ⊆ TreeSequenceVertexSet X :=
    TreeSequenceInitialSegmentVertexSetSubset hTnX
  have hstableTn : StableColoring Tn Dn
      P.coloring sigma := by
    constructor
    · intro f hf hcontrol
      rcases hf with ⟨v, hv, hinc⟩
      exact S.incidentFixed v (hTnXvertices hv) f hinc
    · intro v hv
      exact hstableX.2 v (hTnXvertices hv)
  have hstableTn' : StableColoring Tn Dn
      (m.series.data.coloring n) sigma := by
    have hcolor : m.series.data.coloring n = P.coloring := by
      simpa [n, m] using m.generatingColoring.symm
    rw [hcolor]
    exact hstableTn
  have hmod : ModColoring m sigma :=
    Td G k e0 P.corresponding.replacementInput T P.coloring m P.maximum
      P.counterexample.positive P.minimumContext.lowerRung sigma hsigmaProper
      hsigmaOne hstableTn'
  have hroute :
      (m.series.data.kind n = some TashkinovExtensionKind.PE ∧
        TashkinovAugmentationSequence sigma Tn T) ∨
      ((m.series.data.kind n = some TashkinovExtensionKind.SE ∨
          m.series.data.kind n = some TashkinovExtensionKind.RE) ∧
        ∃ f : E, ∃ seed : TreeSequence G e0,
          m.series.data.connectingEdges n = {f} ∧
          TreeSequenceAdjoinEdge Tn f seed ∧
          TashkinovAugmentationSequence sigma seed T) := by
    rcases S.prefixRoute with hp | hs
    · left
      refine ⟨hp.1, ?_⟩
      exact Relation.ReflTransGen.trans hp.2 S.newSuffix
    · right
      refine ⟨hs.1, ?_⟩
      obtain ⟨f, seed, hconn, hadjoin, hseq⟩ := hs.2
      exact ⟨f, seed, hconn, hadjoin,
        Relation.ReflTransGen.trans hseq S.newSuffix⟩
  have hNT : TreeSequenceInitialSegment Tn T := by
    have hi : (⟨m.rounds, by omega⟩ : Fin (m.rounds + 2)) = n.castSucc := by
      apply Fin.ext
      rfl
    change TreeSequenceInitialSegment
      (m.series.data.tree n.castSucc) T
    rw [← hi]
    exact m.abovePenultimate
  have hNstrict : Tn.length < T.length := by
    have hi : (⟨m.rounds, by omega⟩ : Fin (m.rounds + 2)) = n.castSucc := by
      apply Fin.ext
      rfl
    change (m.series.data.tree n.castSucc).length < T.length
    rw [← hi]
    exact m.strictAbovePenultimate
  let seriesCast := P.corresponding.rungAgreement.symm ▸
    P.corresponding.replacementSeries
  have hseriesCast : HEq seriesCast P.corresponding.replacementSeries := by
    have typeLink :
        TashkinovSeries G k ett.rounds e0 P.corresponding.replacementInput =
          TashkinovSeries G k m.rounds e0 P.corresponding.replacementInput :=
      congrArg (fun r => TashkinovSeries G k r e0
        P.corresponding.replacementInput) P.corresponding.rungAgreement.symm
    simpa [seriesCast] using
      (cast_heq typeLink P.corresponding.replacementSeries)
  have hsourceSeries : m.series = seriesCast := by
    exact eq_of_heq (HEq.trans P.corresponding.seriesPresentation
      hseriesCast.symm)
  have castColor : ∀ {r s : Nat} (h : r = s)
      (ser : TashkinovSeries G k s e0 P.corresponding.replacementInput)
      (i : Fin (r + 1)),
      (h.symm ▸ ser).data.coloring i =
        ser.data.coloring (Fin.cast (congrArg (fun z => z + 1) h) i) := by
    intro r s h ser i
    cases h
    rfl
  let corrMX : CorrespondingExtendedTashkinovTree G k e0 m P.coloring X := {
    replacementInput := P.corresponding.replacementInput
    replacementSeries := m.series
    replacementETT := ettX
    rungAgreement := hroundX
    seriesPresentation := hseriesX
    finalGeneratingColoring := m.generatingColoring
    ladderTreesAgree := by intro i; rfl
    storedColorsAgree := by intro i; rfl
    connectingEdgesAgree := by intro i; rfl
    extensionKindsAgree := by intro i; rfl
    replacementProper := by
      intro i
      rw [hsourceSeries]
      rw [castColor P.corresponding.rungAgreement
        P.corresponding.replacementSeries i]
      exact P.corresponding.replacementProper
        (Fin.cast (congrArg (fun r => r + 1)
          P.corresponding.rungAgreement) i)
    replacementOneUncolored := by
      intro i
      rw [hsourceSeries]
      rw [castColor P.corresponding.rungAgreement
        P.corresponding.replacementSeries i]
      exact P.corresponding.replacementOneUncolored
        (Fin.cast (congrArg (fun r => r + 1)
          P.corresponding.rungAgreement) i)
    replacementStable := by
      intro i
      constructor
      · intro f hf h
        rfl
      · intro v hv
        rfl }
  obtain ⟨corrPrefix, hinputPrefix, hseriesPrefix, hETTPrefix⟩ :=
    CorrespondingExtendedTashkinovTreeTransTrees G k e0
      P.corresponding.replacementInput T X X P.coloring P.coloring sigma m
      corrMX corrX
  have transportETT {I J : PartialEdgeColoring E k} (h : I = J)
      {F : ExtendedTashkinovTree G k e0 I X sigma}
      {F' : ExtendedTashkinovTree G k e0 J X sigma} (hf : HEq F F') :
      F = h.symm ▸ F' := by
    cases h
    exact eq_of_heq hf
  have transportPrefixPackage {I J : PartialEdgeColoring E k} (h : I = J)
      {F : ExtendedTashkinovTree G k e0 I X sigma}
      {F' : ExtendedTashkinovTree G k e0 J X sigma} (hf : HEq F F')
      (b : HierarchyBase F' sigma) (K : TashkinovHierarchy F' b)
      (good : GoodHierarchy K) (hsame : SameGoodHierarchy goodX good) :
      ∃ b' : HierarchyBase F sigma,
        ∃ K' : TashkinovHierarchy F b',
          ∃ good' : GoodHierarchy K', SameGoodHierarchy goodX good' := by
    cases h
    have heq : F = F' := eq_of_heq hf
    cases heq
    exact ⟨b, K, good, hsame⟩
  have prefixPackage :
      ∃ b : HierarchyBase corrPrefix.replacementETT sigma,
        ∃ K : TashkinovHierarchy corrPrefix.replacementETT b,
          ∃ good : GoodHierarchy K,
            SameGoodHierarchy goodX good := by
    exact transportPrefixPackage hinputPrefix hETTPrefix
      baseSigmaX KX goodSigmaX hsameX
  obtain ⟨basePrefix, KPrefix, goodPrefix, samePrefix⟩ := prefixPackage
  have hkindX : ettX.series.data.kind (Fin.last ettX.rounds) =
      m.series.data.kind n := by
    let seriesCastX := hroundX ▸ ettX.series
    have hcastX : HEq seriesCastX ettX.series := by
      have typeLink := congrArg (fun r => TashkinovSeries G k r e0
        P.corresponding.replacementInput) hroundX
      simpa [seriesCastX] using cast_heq typeLink ettX.series
    have heqX : seriesCastX = m.series := eq_of_heq (HEq.trans hcastX hseriesX)
    have hkind := congrArg
      (fun s : TashkinovSeries G k m.rounds e0
        P.corresponding.replacementInput => s.data.kind n) heqX
    have castKind {r s : ℕ} (h : r = s)
        (ser : TashkinovSeries G k r e0 P.corresponding.replacementInput)
        (i : Fin (s + 1)) :
        (h ▸ ser).data.kind i =
          ser.data.kind (Fin.cast (congrArg (fun z => z + 1) h.symm) i) := by
      cases h
      rfl
    have hindex : Fin.cast (congrArg (fun z => z + 1) hroundX.symm) n =
        Fin.last ettX.rounds := by
      apply Fin.ext
      simp [n]
    have hkindCast : seriesCastX.data.kind n =
        ettX.series.data.kind (Fin.last ettX.rounds) := by
      rw [castKind hroundX ettX.series n, hindex]
    exact hkindCast.symm.trans hkind
  have hfull :
      ∃ corr : CorrespondingExtendedTashkinovTree G k e0 m sigma T,
        MaximumProperty corr.replacementETT ∧
        ∃ newBase : HierarchyBase corr.replacementETT sigma,
          ∃ K : TashkinovHierarchy corr.replacementETT newBase,
            newBase.closure = basePrefix.closure ∧ SameHierarchyStages H K := by
    by_cases hpe : m.series.data.kind n =
        some TashkinovExtensionKind.PE
    · rcases hroute with ⟨_, hbuilt⟩ | hnonpe
      · have hbaseParallel := P.replacementBase.parallel hpe
        rcases hbaseParallel with ⟨_, _, ⟨union⟩⟩
        have hcoreVertices :
            TreeSequenceVertexSet P.replacementBase.core ⊆
              TreeSequenceVertexSet X :=
          TreeSequenceInitialSegmentVertexSetSubset S.coreInSplit
        have hclosureVertices :
            TreeSequenceVertexSet P.replacementBase.closure ⊆
              TreeSequenceVertexSet X := by
          intro v hv
          apply hcoreVertices
          rw [union.vertexSet]
          exact Finset.mem_union_right _ hv
        have hcombined : CombinedStableColoring Tn
            P.replacementBase.closure Dn P.coloring sigma := by
          constructor
          · exact hstableTn
          · constructor
            · intro f hf _
              rcases hf with ⟨v, hv, hinc⟩
              exact S.incidentFixed v (hclosureVertices hv) f hinc
            · intro v hv
              exact hstableX.2 v (hclosureVertices hv)
        have hsplit := HierarchySplitter G k e0
          P.corresponding.replacementInput T P.coloring sigma m P.maximum
          P.counterexample.positive P.minimumContext.lowerRung
          P.replacementBase H hpe P.minimumContext.proper
          P.minimumContext.oneEdgeUncolored hsigmaProper hsigmaOne
          hcombined hbuilt
        rcases hsplit with ⟨corr, hmaximum, newBase, K, hsame⟩
        have hclosure : newBase.closure = basePrefix.closure := by
          have hclFull := hsame.2.2.2.2.2 hpe
          have hclPrefix := samePrefix.1.2.2.2.2.2 (hkindX.trans hpe)
          exact hclFull.symm.trans (hclosureX.symm.trans hclPrefix)
        exact ⟨corr, hmaximum, newBase, K, hclosure, hsame⟩
      · rcases hnonpe.1 with hse | hre
        · have heq : some TashkinovExtensionKind.SE =
              some TashkinovExtensionKind.PE := hse.symm.trans hpe
          cases heq
        · have heq : some TashkinovExtensionKind.RE =
              some TashkinovExtensionKind.PE := hre.symm.trans hpe
          cases heq
    · rcases hroute with hpeRoute | hnonpeRoute
      · exact False.elim (hpe hpeRoute.1)
      · rcases hnonpeRoute with ⟨hkind, f, seed, hconn, hadjoin, hbuilt⟩
        obtain ⟨corr⟩ := hmod.2.2 T hNT hNstrict
          (Or.inr ⟨hkind, f, seed, hconn, hadjoin, hbuilt⟩)
        have hmaximum : MaximumProperty corr.replacementETT :=
          MaximumPropertyTransport G k e0 m sigma hmod T corr P.maximum
        let replacementSeries : TashkinovSeries G k corr.replacementETT.rounds
            e0 corr.replacementInput :=
          cast (congrArg (fun r => TashkinovSeries G k r e0
            corr.replacementInput) corr.rungAgreement.symm)
            corr.replacementSeries
        have castTree {a b : ℕ} (h : a = b)
            (s : TashkinovSeries G k a e0 corr.replacementInput)
            (i : Fin (b + 2)) :
            (cast (congrArg (fun r => TashkinovSeries G k r e0
              corr.replacementInput) h) s).data.tree i =
              s.data.tree (Fin.cast (congrArg (fun r => r + 2) h.symm) i) := by
          cases h
          rfl
        have castKind {a b : ℕ} (h : a = b)
            (s : TashkinovSeries G k a e0 corr.replacementInput)
            (i : Fin (b + 1)) :
            (cast (congrArg (fun r => TashkinovSeries G k r e0
              corr.replacementInput) h) s).data.kind i =
              s.data.kind (Fin.cast (congrArg (fun r => r + 1) h.symm) i) := by
          cases h
          rfl
        have hseries : corr.replacementETT.series = replacementSeries := by
          exact ((cast_eq_iff_heq
            (e := congrArg (fun r => TashkinovSeries G k r e0
              corr.replacementInput) corr.rungAgreement.symm)
            (a := corr.replacementSeries)
            (a' := corr.replacementETT.series)).2
            corr.seriesPresentation.symm).symm
        let terminalIndex : Fin corr.replacementETT.rounds :=
          Fin.cast corr.rungAgreement.symm
            ⟨m.rounds - 1, by have hp := m.roundsPositive; omega⟩
        have htree : corr.replacementETT.series.data.tree
            terminalIndex.succ.castSucc = Tn := by
          rw [hseries]
          calc
            replacementSeries.data.tree terminalIndex.succ.castSucc =
                corr.replacementSeries.data.tree
                  (Fin.cast (congrArg (fun r => r + 2) corr.rungAgreement)
                    terminalIndex.succ.castSucc) := by
              simpa [replacementSeries] using
                castTree corr.rungAgreement.symm corr.replacementSeries
                  terminalIndex.succ.castSucc
            _ = m.series.data.tree n.castSucc := by
              convert corr.ladderTreesAgree
                (Fin.cast corr.rungAgreement terminalIndex) using 1
              · congr 1
              · congr 1
                apply Fin.ext
                have hp : m.rounds - 1 + 1 = m.rounds := by
                  exact Nat.sub_add_cancel (by have := m.roundsPositive; omega)
                simp [terminalIndex, hp, corr.rungAgreement, n]
        have hkindEq : ∀ i : Fin (corr.replacementETT.rounds + 1),
            corr.replacementETT.series.data.kind i =
              m.series.data.kind (Fin.cast
                (congrArg (fun r => r + 1) corr.rungAgreement) i) := by
          intro i
          rw [hseries]
          exact (castKind corr.rungAgreement.symm corr.replacementSeries i).trans
            (corr.extensionKindsAgree
              (Fin.cast (congrArg (fun r => r + 1) corr.rungAgreement) i))
        have htreeFinal : corr.replacementETT.series.data.tree
            (Fin.last corr.replacementETT.rounds).castSucc = Tn := by
          have hi : (Fin.last corr.replacementETT.rounds).castSucc =
              terminalIndex.succ.castSucc := by
            apply Fin.ext
            have hp : m.rounds - 1 + 1 = m.rounds := by
              exact Nat.sub_add_cancel (by have := m.roundsPositive; omega)
            simp [terminalIndex, hp, corr.rungAgreement]
          rw [hi]
          exact htree
        have hkindP : m.series.data.kind (Fin.last m.rounds) ≠
              some TashkinovExtensionKind.PE := by
          intro hp
          rcases hkind with hse | hre
          · rw [hp] at hse
            cases hse
          · rw [hp] at hre
            cases hre
        let newBase : HierarchyBase corr.replacementETT sigma := {
          core := Tn
          closure := basePrefix.closure
          supportPosition := Fin.cast
            (congrArg (fun U : TreeSequence G e0 => U.length + 1)
              htreeFinal.symm) P.replacementBase.supportPosition
          supportPositive := P.replacementBase.supportPositive
          terminalMissingColors := by rfl
          parallel := by
            dsimp
            intro hp
            have hk := hkindEq (Fin.last corr.replacementETT.rounds)
            have hs : m.series.data.kind n =
                some TashkinovExtensionKind.PE := by
              simpa [corr.rungAgreement] using hk.symm.trans hp
            rcases hkind with hse | hre
            · rw [hs] at hse
              cases hse
            · rw [hs] at hre
              cases hre
          nonparallel := by
            dsimp
            intro hn
            have hc := P.replacementBase.nonparallel hkindP
            simpa [htreeFinal] using hc }
        let K : TashkinovHierarchy corr.replacementETT newBase := {
          dividerCount := H.dividerCount
          stage := H.stage
          baseStage := by simpa [htreeFinal] using H.baseStage
          terminalStage := H.terminalStage
          nested := H.nested
          strict := H.strict
          dividerPosition := H.dividerPosition
          dividerPositive := H.dividerPositive
          dividerIncreasing := H.dividerIncreasing
          dividerStage := H.dividerStage
          coreInsideFirst := by
            have hcoreEq : Tn = P.replacementBase.core := by
              have h := P.replacementBase.nonparallel hkindP
              simpa [m, Tn, n] using h.symm
            simpa [newBase] using hcoreEq ▸ H.coreInsideFirst }
        have hsame : SameHierarchyStages H K := by
          dsimp [SameHierarchyStages, K, newBase]
          have hcoreEq : Tn = P.replacementBase.core := by
            have h := P.replacementBase.nonparallel hkindP
            simpa [m, Tn, n] using h.symm
          refine ⟨hcoreEq.symm, rfl, heq_of_eq rfl, heq_of_eq rfl, ?_, ?_⟩
          · constructor <;> intro hp
            · have hk := hkindEq (Fin.last corr.replacementETT.rounds)
              have hs : corr.replacementETT.series.data.kind
                  (Fin.last corr.replacementETT.rounds) =
                  m.series.data.kind n := by
                simpa [corr.rungAgreement] using hk
              exact hs ▸ hp
            · have hk := hkindEq (Fin.last corr.replacementETT.rounds)
              have hs : corr.replacementETT.series.data.kind
                  (Fin.last corr.replacementETT.rounds) =
                  m.series.data.kind n := by
                simpa [corr.rungAgreement] using hk
              exact hs.symm ▸ hp
          · intro hp
            rcases hkind with hse | hre
            · have he : TashkinovExtensionKind.SE = TashkinovExtensionKind.PE :=
                Option.some.inj (hse.symm.trans hp)
              cases he
            · have he : TashkinovExtensionKind.RE = TashkinovExtensionKind.PE :=
                Option.some.inj (hre.symm.trans hp)
              cases he
        exact ⟨corr, hmaximum, newBase, K, rfl, hsame⟩
  rcases hfull with ⟨corrFull, hmaximumFull, baseFull, KFull, hclosure, hsameFull⟩
  have hcoreFull : baseFull.core = basePrefix.core := by
    have hprefixCore := samePrefix.1.1
    have hfullCore := hsameFull.1
    exact hfullCore.symm.trans (hcoreX.symm.trans hprefixCore)
  have hfullRoute : TashkinovAugmentationSequence sigma X T := S.newSuffix
  obtain ⟨Ktransport, hcountTransport, hstagesTransport, hpositionsTransport⟩ :=
    GoodHierarchySameDividerReconstruction G k e0
      P.corresponding.replacementInput T P.coloring sigma m X T
      corrPrefix basePrefix KPrefix corrFull baseFull hcoreFull hfullRoute
  have havoid : ∀ eta : Fin k,
      eta ∈ HierarchyStoredColorsAt KPrefix (Fin.last KPrefix.dividerCount) →
      Disjoint (goodPrefix.gamma (Fin.last KPrefix.dividerCount) eta)
        (Finset.univ.filter fun c => ∃ r : Fin T.length,
        (HierarchyStarredStage KPrefix (Fin.last KPrefix.dividerCount)).length ≤ r.val ∧
          r.val < min (HierarchyFirstMissingPosition sigma T eta).val T.length ∧
          sigma (T.edge r) = some c) := by
    intro eta heta
    let qX : Fin (HX.dividerCount + 1) := Fin.last HX.dividerCount
    let qP : Fin (KPrefix.dividerCount + 1) := Fin.last KPrefix.dividerCount
    have hcountXP : HX.dividerCount = KPrefix.dividerCount := samePrefix.1.2.1
    rcases samePrefix.2 with ⟨hcountGood, hsameGamma⟩
    have hidxXP : Fin.cast (congrArg (fun z : ℕ => z + 1) hcountGood) qX = qP := by
      apply Fin.ext
      simp [qX, qP]
    have hstoreXP : HierarchyStoredColorsAt HX qX =
        HierarchyStoredColorsAt KPrefix qP := by
      simpa [qX, qP, hidxXP] using (hsameGamma qX).1
    have hetaX : eta ∈ HierarchyStoredColorsAt HX qX := by
      rw [hstoreXP]
      exact heta
    have hidxXH : Fin.cast (congrArg (fun z : ℕ => z + 1) hcountX) qX = q := by
      apply Fin.ext
      simp [qX, q, Fin.val_cast]
    have hstoreOld : eta ∈ HierarchyStoredColorsAt H q := by
      have hx := (hcolorsX qX).1
      rw [hidxXH] at hx
      rw [← hx]
      exact hetaX
    have hgammaOldPrefix : P.counterexample.good.gamma q eta =
        goodPrefix.gamma qP eta := by
      have hx := (hcolorsX qX).2.2 eta
      have hp := hsameGamma qX
      simpa [q, qX, qP, hidxXH, hidxXP] using hx.1.symm.trans (hp.2 eta hetaX)
    have stageAt {a b : ℕ} (h : a = b)
        (f : Fin (a + 2) → TreeSequence G e0)
        (g : Fin (b + 2) → TreeSequence G e0) (hfg : HEq f g)
        (j : Fin (b + 2)) : f (Fin.cast (congrArg (fun d => d + 2) h.symm) j) = g j := by
      cases h
      simpa using congrFun (eq_of_heq hfg) j
    let index (j : Fin (HX.dividerCount + 1)) :
        Fin (KPrefix.dividerCount + 1) :=
      Fin.cast (congrArg (fun d : ℕ => d + 1) hcountXP) j
    have stageEq (j : Fin (HX.dividerCount + 1)) :
        HX.stage j.castSucc = KPrefix.stage (index j).castSucc := by
      have hs := stageAt hcountXP HX.stage KPrefix.stage
        samePrefix.1.2.2.1 (index j).castSucc
      convert hs using 1 <;> congr 1 <;> apply Fin.ext <;> simp [index]
    have hstarXP' (j : Fin (HX.dividerCount + 1)) :
        HierarchyStarredStage HX j = HierarchyStarredStage KPrefix (index j) := by
      refine Fin.cases ?_ (fun i => ?_) j
      · simpa [HierarchyStarredStage, index] using samePrefix.1.1
      · have hs := stageEq i.succ
        simpa [HierarchyStarredStage, index] using hs
    have hstarXP : HierarchyStarredStage KPrefix qP =
        HierarchyStarredStage HX qX := by
      have hs := hstarXP' qX
      simpa [index, qX, qP, hidxXP] using hs.symm
    have hstarOld : HierarchyStarredStage KPrefix qP =
        HierarchyStarredStage H q := by
      have hx := (hstagesX qX).2
      have hidx : Fin.cast (congrArg (fun z : ℕ => z + 1) hcountX) qX = q := hidxXH
      exact hstarXP.trans (hx.trans (by simpa [hidx]))
    apply Finset.disjoint_left.mpr
    intro c hcG hcSeg
    rcases (Finset.mem_filter.mp hcSeg).2 with ⟨r, hlo, hhi, hcol⟩
    by_cases haffected : alpha ∈ P.counterexample.good.gamma q eta ∨
        beta ∈ P.counterexample.good.gamma q eta
    · have hcut := S.gammaCutoff eta hstoreOld haffected
      have hfirst := S.storedFirst eta hstoreOld
      have hrX : r.val < X.length := by
        have hlt := (lt_min_iff.mp hhi).1
        have hle : (HierarchyFirstMissingPosition sigma T eta).val ≤ X.length := by
          rw [hfirst]
          exact hcut
        exact lt_of_lt_of_le hlt hle
      have hprefixCut := HierarchyFirstMissingPositionPrefixCutoff sigma X T
        S.splitInFull eta X.length le_rfl
      let rX : Fin X.length := ⟨r.val, hrX⟩
      have hidx : (Fin.castLE (by have hlen := S.splitInFull.1; omega) rX) = r := by
        apply Fin.ext
        rfl
      have hedge : T.edge r = X.edge rX := by
        have he := S.splitInFull.2.2 rX
        rw [hidx] at he
        exact he.symm
      have hhiX : r.val < min (HierarchyFirstMissingPosition sigma X eta).val X.length := by
        rw [hprefixCut]
        exact (lt_min_iff).2 ⟨(lt_min_iff.mp hhi).1, hrX⟩
      have hsegX : c ∈ HierarchySegmentColors KPrefix qP eta := by
        unfold HierarchySegmentColors
        have hterm : KPrefix.stage qP.succ = X := by
          simpa [qP] using KPrefix.terminalStage
        rw [hterm]
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨rX, ?_, hhiX, ?_⟩
        · simpa [rX, qP] using hlo
        · rw [← hedge]
          exact hcol
      have havo := goodPrefix.avoidance qP eta heta hcG
      exact (Finset.mem_sdiff.mp havo).2 hsegX
    · have hgammaMem : c ∈ P.counterexample.good.gamma q eta := by
        rw [hgammaOldPrefix]
        exact hcG
      have hcnotAlpha : c ≠ alpha := by
        intro he
        apply haffected
        exact Or.inl (he ▸ hgammaMem)
      have hcnotBeta : c ≠ beta := by
        intro he
        apply haffected
        exact Or.inr (he ▸ hgammaMem)
      have hcolOld : P.coloring (T.edge r) = some c := by
        rw [S.swapped] at hcol
        unfold TwoColorComponentSwap at hcol
        split_ifs at hcol with hmem ha hb
        · exact False.elim (hcnotBeta (Option.some.inj hcol).symm)
        · exact False.elim (hcnotAlpha (Option.some.inj hcol).symm)
        · exact hcol
        · exact hcol
      have hltOld : r.val < (HierarchyFirstMissingPosition P.coloring T eta).val := by
        have hlt := (lt_min_iff.mp hhi).1
        rw [S.storedFirst eta hstoreOld] at hlt
        exact hlt
      have hsegOld : c ∈ HierarchySegmentColors H q eta := by
        unfold HierarchySegmentColors
        have hterm : H.stage q.succ = T := by
          convert H.terminalStage using 1
          apply congrArg H.stage
          apply Fin.ext
          simp [q]
        rw [hterm]
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨r, ?_, ?_, hcolOld⟩
        · rw [← hstarOld]
          exact hlo
        · exact (lt_min_iff.mpr ⟨hltOld, r.isLt⟩)
      have havo := P.counterexample.good.avoidance q eta hstoreOld hgammaMem
      exact (Finset.mem_sdiff.mp havo).2 hsegOld
  obtain ⟨goodFull, hsamePrefixFull⟩ :=
    GoodHierarchySameDividerTransport G k e0
      P.corresponding.replacementInput T P.coloring sigma m X T
      corrPrefix basePrefix KPrefix goodPrefix corrFull baseFull
      hcoreFull hclosure Ktransport hcountTransport hstagesTransport
      hfullRoute havoid
  have hsameFinal : SameGoodHierarchy P.counterexample.good goodFull := by
    let hcountGood := samePrefix.2.choose
    let hcountFinal : H.dividerCount = Ktransport.dividerCount :=
      hcountX.symm.trans (hcountGood.trans hcountTransport.symm)
    have stageAt {a b : ℕ} (h : a = b)
        (f : Fin (a + 2) → TreeSequence G e0)
        (g : Fin (b + 2) → TreeSequence G e0) (hfg : HEq f g)
        (j : Fin (b + 2)) :
        f (Fin.cast (congrArg (fun z => z + 2) h.symm) j) = g j := by
      cases h
      simpa using congrFun (eq_of_heq hfg) j
    have positionValueAt {a b : ℕ} (h : a = b)
        (f : Fin a → Fin (X.length + 1))
        (g : Fin b → Fin (X.length + 1)) (hfg : HEq f g)
        (j : Fin b) :
        (f (Fin.cast (congrArg (fun z => z) h.symm) j)).val = (g j).val := by
      cases h
      simpa using congrArg Fin.val (congrFun (eq_of_heq hfg) j)
    have hierarchyStageHEq {a b : ℕ} (h : a = b)
        (f : Fin (a + 2) → TreeSequence G e0)
        (g : Fin (b + 2) → TreeSequence G e0)
        (hmid : ∀ i : Fin (a + 1),
          f i.castSucc = g
            (Fin.cast (congrArg (fun z => z + 1) h) i).castSucc)
        (hlast : f (Fin.last (a + 1)) = g (Fin.last (b + 1))) :
        HEq f g := by
      cases h
      apply heq_of_eq
      funext j
      refine Fin.lastCases hlast (fun i => ?_) j
      simpa using hmid i
    have positionFamilyHEq {a b : ℕ} (h : a = b)
        (f : Fin a → Fin (T.length + 1))
        (g : Fin b → Fin (T.length + 1))
        (hmid : ∀ i : Fin a, f i = g (Fin.cast h i)) : HEq f g := by
      cases h
      apply heq_of_eq
      funext i
      exact hmid i
    have hstageMiddle (i : Fin (H.dividerCount + 1)) :
        H.stage i.castSucc = Ktransport.stage
          (Fin.cast (congrArg (fun z => z + 1) hcountFinal) i).castSucc := by
      let ix := Fin.cast (congrArg (fun z => z + 1) hcountX.symm) i
      let ip := Fin.cast (congrArg (fun z => z + 1) hcountGood) ix
      let iu := Fin.cast (congrArg (fun z => z + 1) hcountTransport.symm) ip
      have hx := (hstagesX ix).1
      have hp := stageAt hcountGood HX.stage KPrefix.stage
        samePrefix.1.2.2.1 ip.castSucc
      have hu := (hstagesTransport iu).1
      calc
        H.stage i.castSucc = HX.stage ix.castSucc := by
          convert hx.symm using 1 <;> congr 1 <;> apply congrArg H.stage <;>
            apply Fin.ext <;> simp [ix]
        _ = KPrefix.stage ip.castSucc := by
          convert hp using 1 <;> congr 1 <;> apply congrArg HX.stage <;>
            apply Fin.ext <;> simp [ip]
        _ = Ktransport.stage iu.castSucc := by
          convert hu.symm using 1 <;> congr 1 <;> apply congrArg Ktransport.stage <;>
            apply Fin.ext <;> simp [iu]
    have hstageFinal : HEq H.stage Ktransport.stage := by
      apply hierarchyStageHEq hcountFinal H.stage Ktransport.stage
        hstageMiddle
      rw [H.terminalStage, Ktransport.terminalStage]
    have hpositionMiddle (i : Fin (H.dividerCount)) :
        (H.dividerPosition i).val =
          (Ktransport.dividerPosition
            (Fin.cast (congrArg (fun z => z) hcountFinal) i)).val := by
      let ix := Fin.cast hcountX.symm i
      let ip := Fin.cast hcountGood ix
      let iu := Fin.cast hcountTransport.symm ip
      have hp := positionValueAt hcountGood HX.dividerPosition
        KPrefix.dividerPosition samePrefix.1.2.2.2.1 ip
      calc
        (H.dividerPosition i).val = (HX.dividerPosition ix).val := by
          have hidx : Fin.cast hcountX ix = i := by
            apply Fin.ext
            simp [ix]
          have hx := hpositionsX ix
          rw [hidx] at hx
          exact hx.symm
        _ = (KPrefix.dividerPosition ip).val := hp
        _ = (Ktransport.dividerPosition iu).val := by
          have hidx : Fin.cast hcountTransport iu = ip := by
            apply Fin.ext
            simp [iu]
          have hu := hpositionsTransport iu
          rw [hidx] at hu
          exact hu.symm
    have hpositionFinal : HEq H.dividerPosition Ktransport.dividerPosition := by
      apply positionFamilyHEq hcountFinal H.dividerPosition
        Ktransport.dividerPosition
      intro i
      apply Fin.ext
      exact hpositionMiddle i
    have hsameStages : SameHierarchyStages H Ktransport := by
      unfold SameHierarchyStages
      dsimp only
      refine ⟨hsameFull.1, hcountFinal, hstageFinal,
        hpositionFinal, ?_, ?_⟩
      · exact hsameFull.2.2.2.2.1
      · intro hp
        exact hsameFull.2.2.2.2.2 hp
    unfold SameGoodHierarchy
    refine ⟨hsameStages, hcountFinal, ?_⟩
    intro j
    let jX := Fin.cast (congrArg (fun z => z + 1) hcountX.symm) j
    let jP := Fin.cast (congrArg (fun z => z + 1) hcountGood) jX
    let jU := Fin.cast (congrArg (fun z => z + 1) hcountTransport.symm) jP
    have hx := hcolorsX jX
    have hp := samePrefix.2.choose_spec jX
    have hu := hstagesTransport jU
    have hjX : Fin.cast (congrArg (fun z => z + 1) hcountX) jX = j := by
      apply Fin.ext
      simp [jX]
    have hjU : Fin.cast (congrArg (fun z => z + 1) hcountTransport) jU = jP := by
      apply Fin.ext
      simp [jU]
    refine ⟨?_, ?_⟩
    · calc
        HierarchyStoredColorsAt H j = HierarchyStoredColorsAt HX jX := by
          rw [← hjX]
          exact hx.1.symm
        _ = HierarchyStoredColorsAt KPrefix jP := hp.1
        _ = HierarchyStoredColorsAt Ktransport jU := by
          rw [← hjU]
          exact hu.2.2.1.symm
    · intro eta heta
      have hgamma := (hx.2.2 eta).1
      rw [hjX] at hgamma
      calc
        P.counterexample.good.gamma j eta = goodX.gamma jX eta :=
          hgamma.symm
        _ = goodPrefix.gamma jP eta := hp.2 eta (by rw [hx.1]; exact heta)
        _ = goodFull.gamma jU eta := by
          rw [← hjU]
          exact (hsamePrefixFull jU eta).symm
  exact ⟨corrFull, hmaximumFull, baseFull, Ktransport, goodFull, hsameFinal⟩
