import Tablet.BoundaryColorVertex
import Tablet.BoundaryEdges
import Tablet.ColoredVertexSetElementary
import Tablet.CorrespondingExtendedTashkinovTree
import Tablet.DefectiveColor
import Tablet.DefectiveVertex
import Tablet.ETTFirstAppearanceIndex
import Tablet.ExtendedTashkinovTree
import Tablet.GoodHierarchy
import Tablet.GoodHierarchyPrefixRepackage
import Tablet.GoodHierarchyReservedDisjoint
import Tablet.GoodHierarchyTerminalPrefixRepackage
import Tablet.HierarchyBase
import Tablet.HierarchyFirstMissingPosition
import Tablet.HierarchySegmentColors
import Tablet.HierarchyStarredStage
import Tablet.HierarchyStoredColorsAt
import Tablet.IsOneEdgeUncolored
import Tablet.IsProperEdgeColoring
import Tablet.MaximumDefectiveChoice
import Tablet.MaximumProperty
import Tablet.MaximumPropertyTransport
import Tablet.MissingColors
import Tablet.ModColoring
import Tablet.OrderedTreeUnion
import Tablet.StableColoring
import Tablet.StableColoringBeforeVertex
import Tablet.TashkinovAugmentation
import Tablet.TashkinovAugmentationSequence
import Tablet.TashkinovClosure
import Tablet.TashkinovExtensionKind
import Tablet.TashkinovHierarchy
import Tablet.TashkinovSeries
import Tablet.TashkinovSeriesStep
import Tablet.TashkinovStoredColors
import Tablet.Td
import Tablet.TreeColorSetMinusClosed
import Tablet.TreeIncidentEdge
import Tablet.TreeInterchangeable
import Tablet.TreeMissingColors
import Tablet.TreeSequence
import Tablet.TreeSequenceAdjoinEdge
import Tablet.TreeSequenceInitialSegment
import Tablet.TreeSequenceVertexSet
import Tablet.TreeVertexOrder
import Tablet.TwoColorComponent
import Tablet.PresentColors
import Tablet.TashkinovAugmentationSequenceRestrict
import Tablet.TashkinovAugmentationSequenceInitialSegment
import Tablet.TashkinovAugmentationSequenceColoringTransport
import Tablet.TreeSequenceInitialSegmentVertexSetSubset
import Tablet.HierarchyFirstMissingPositionPrefixCutoff

-- [TABLET NODE: Step1CaseTwoOutsidePrefixHierarchy]
lemma Step1CaseTwoOutsidePrefixHierarchy {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (hMP : MaximumProperty ett) (hpositive : 0 < ett.rounds)
    (hlower : ∀ {input' : PartialEdgeColoring E k}
      {T' : TreeSequence G e0}
      {generating' : PartialEdgeColoring E k}
      (lower : ExtendedTashkinovTree G k e0 input' T' generating'),
      0 < lower.rounds → lower.rounds < ett.rounds → MaximumProperty lower →
      ColoredVertexSetElementary G generating'
          (TreeSequenceVertexSet T') ∧
        (let n : Fin (lower.rounds + 1) := Fin.last lower.rounds
         let Tnext : TreeSequence G e0 :=
           lower.series.data.tree (Fin.last (lower.rounds + 1))
         ∀ sigma : PartialEdgeColoring E k,
           IsProperEdgeColoring G sigma → IsOneEdgeUncolored sigma e0 →
           StableColoring Tnext
             (TashkinovStoredColors lower.series.data n)
             (lower.series.data.coloring n) sigma →
           ∀ alpha beta : Fin k,
             (alpha ∈ TreeMissingColors sigma Tnext ∨
               beta ∈ TreeMissingColors sigma Tnext) →
             TreeInterchangeable G Tnext sigma alpha beta) ∧
        (((∀ (q : Fin lower.rounds) (v : V),
          lower.series.data.kind q.succ =
              some TashkinovExtensionKind.PE →
          lower.series.data.chosenVertex q.succ = some v →
          ∀ hvFinal : v ∈ TreeSequenceVertexSet T',
          ∀ j : Fin (lower.rounds + 1),
            ETTFirstAppearanceIndex lower v hvFinal = j.val + 1 →
            ∀ sigma : PartialEdgeColoring E k,
              IsProperEdgeColoring G sigma →
              IsOneEdgeUncolored sigma e0 →
              StableColoring
                (lower.series.data.tree q.succ.castSucc)
                (TashkinovStoredColors lower.series.data q.succ)
                (lower.series.data.coloring q.succ) sigma →
              StableColoringBeforeVertex T' v hvFinal
                  (TashkinovStoredColors lower.series.data j)
                  (lower.series.data.coloring j) sigma ∧
                (0 < j.val →
                  StableColoring (lower.series.data.tree j.castSucc)
                    (TashkinovStoredColors lower.series.data j)
                    (lower.series.data.coloring j) sigma)) ∧
          ∀ (q r : Fin lower.rounds) (vq vr : V),
            q ≠ r → vq ≠ vr →
            lower.series.data.kind q.succ =
                some TashkinovExtensionKind.PE →
            lower.series.data.kind r.succ =
                some TashkinovExtensionKind.PE →
            lower.series.data.chosenVertex q.succ = some vq →
            lower.series.data.chosenVertex r.succ = some vr →
            ∀ (hvq : vq ∈ TreeSequenceVertexSet T')
              (hvr : vr ∈ TreeSequenceVertexSet T'),
              ETTFirstAppearanceIndex lower vq hvq =
                  ETTFirstAppearanceIndex lower vr hvr →
              Disjoint (lower.series.data.stored q.succ)
                (lower.series.data.stored r.succ)) ∧
        (let n : Fin (lower.rounds + 1) := Fin.last lower.rounds
         let Tn : TreeSequence G e0 :=
           lower.series.data.tree n.castSucc
         ∀ (v : V) (gamma delta : Fin k),
           lower.series.data.kind n = some TashkinovExtensionKind.PE →
           lower.series.data.chosenVertex n = some v →
           lower.series.data.gamma n = some gamma →
           lower.series.data.delta n = some delta →
           ∀ sigma : PartialEdgeColoring E k,
             IsProperEdgeColoring G sigma →
             IsOneEdgeUncolored sigma e0 →
             StableColoring Tn
               (TashkinovStoredColors lower.series.data n)
               (lower.series.data.coloring n) sigma →
             ∀ w, w ∈ TreeSequenceVertexSet Tn →
               (Sum.inl w ∈ TwoColorComponent G sigma gamma delta
                   (Sum.inl v) ↔ w = v)) ∧
        (let n : Fin (lower.rounds + 1) := Fin.last lower.rounds
         let Tn : TreeSequence G e0 :=
           lower.series.data.tree n.castSucc
         ∀ sigma : PartialEdgeColoring E k,
           IsProperEdgeColoring G sigma → IsOneEdgeUncolored sigma e0 →
           StableColoring Tn
             (TashkinovStoredColors lower.series.data n)
             (lower.series.data.coloring n) sigma →
           ∀ (delta : Fin k),
             DefectiveColor G sigma (TreeSequenceVertexSet Tn) delta →
             ∀ (v : V),
               BoundaryColorVertex G sigma (TreeSequenceVertexSet Tn)
                   delta v →
               (∃ w, BoundaryColorVertex G sigma
                   (TreeSequenceVertexSet Tn) delta w ∧
                 TreeVertexOrder Tn w v) →
               ∀ (hvFinal : v ∈ TreeSequenceVertexSet T')
                 (q : Fin lower.rounds) (vi : V),
                 (lower.series.data.kind q.succ =
                      some TashkinovExtensionKind.PE ∨
                    lower.series.data.kind q.succ =
                      some TashkinovExtensionKind.SE) →
                 lower.series.data.chosenVertex q.succ = some vi →
                 ETTFirstAppearanceIndex lower v hvFinal ≤ q.val + 1 →
                 v = vi ∨ TreeVertexOrder T' v vi) ∧
        (let n : Fin (lower.rounds + 1) := Fin.last lower.rounds
         let Tn : TreeSequence G e0 :=
           lower.series.data.tree n.castSucc
         ∀ sigma : PartialEdgeColoring E k,
           IsProperEdgeColoring G sigma → IsOneEdgeUncolored sigma e0 →
           StableColoring Tn
             (TashkinovStoredColors lower.series.data n)
             (lower.series.data.coloring n) sigma →
           ModColoring lower sigma)))
    (base : HierarchyBase ett phi)
    (H : TashkinovHierarchy ett base) (good : GoodHierarchy H)
    (hlarge : 2 * ett.rounds + 11 ≤
      (TreeMissingColors phi
        (ett.series.data.tree (Fin.last ett.rounds).castSucc)).card)
    (hElementary : ColoredVertexSetElementary G phi
      (TreeSequenceVertexSet T))
    (beta gamma : Fin k) (hbeta : beta ∉ TreeMissingColors phi T)
    (mu : PartialEdgeColoring E k)
    (hgammaBeta : gamma ≠ beta)
    (hproperMu : IsProperEdgeColoring G mu)
    (honeMu : IsOneEdgeUncolored mu e0)
    (hstable : StableColoring
      (ett.series.data.tree (Fin.last ett.rounds).castSucc)
      (TashkinovStoredColors ett.series.data (Fin.last ett.rounds))
      phi mu)
    (Bminus C : TreeSequence G e0)
    (hfixed : ∀ e, TreeIncidentEdge Bminus e → mu e = phi e)
    (hmissingFixed : ∀ v, v ∈ TreeSequenceVertexSet Bminus →
      MissingColors G mu v = MissingColors G phi v)
    (hgammaOld : gamma ∈ MissingColors G phi
      (C.vertex (Fin.last C.length)))
    (hbetaNew : beta ∈ MissingColors G mu
      (C.vertex (Fin.last C.length)))
    (f₃ : E) (hif₃ : Incident G (C.vertex (Fin.last C.length)) f₃)
    (hgammaEdge : mu f₃ = some gamma)
    (hotherMissing : ∀ v, v ∈ TreeSequenceVertexSet C → ∀ eta,
      eta ≠ gamma → eta ≠ beta →
      (eta ∈ MissingColors G mu v ↔ eta ∈ MissingColors G phi v))
    (hgammaReserved : gamma ∉ (HierarchyStoredColorsAt H
      (Fin.last H.dividerCount)).biUnion
        (good.gamma (Fin.last H.dividerCount)))
    (hAB : TreeSequenceInitialSegment
      (HierarchyStarredStage H (Fin.last H.dividerCount)) Bminus)
    (hBCstrict : Bminus.length < C.length)
    (hCT : TreeSequenceInitialSegment C T)
    (hBC : ∃ g, TreeSequenceAdjoinEdge Bminus g C) :
    ∃ (corrC : CorrespondingExtendedTashkinovTree G k e0 ett mu C)
      (baseC : HierarchyBase corrC.replacementETT mu)
      (KC : TashkinovHierarchy corrC.replacementETT baseC)
      (goodC : GoodHierarchy KC),
      ModColoring ett mu ∧
      MaximumProperty corrC.replacementETT ∧
      ((ett.series.data.kind (Fin.last ett.rounds) =
          some TashkinovExtensionKind.PE ∧
          TashkinovAugmentationSequence mu
            (ett.series.data.tree (Fin.last ett.rounds).castSucc) C) ∨
        ((ett.series.data.kind (Fin.last ett.rounds) =
              some TashkinovExtensionKind.SE ∨
            ett.series.data.kind (Fin.last ett.rounds) =
              some TashkinovExtensionKind.RE) ∧
          ∃ (f : E) (seed : TreeSequence G e0),
            ett.series.data.connectingEdges (Fin.last ett.rounds) = {f} ∧
            TreeSequenceAdjoinEdge
              (ett.series.data.tree (Fin.last ett.rounds).castSucc) f seed ∧
            TashkinovAugmentationSequence mu seed C)) ∧
      KC.dividerCount = H.dividerCount ∧
      2 * corrC.replacementETT.rounds + 11 ≤
        (TreeMissingColors mu
          (corrC.replacementETT.series.data.tree
            (Fin.last corrC.replacementETT.rounds).castSucc)).card ∧
      gamma ∉ (HierarchyStoredColorsAt KC
        (Fin.last KC.dividerCount)).biUnion
          (goodC.gamma (Fin.last KC.dividerCount)) ∧
      beta ∉ (HierarchyStoredColorsAt KC
        (Fin.last KC.dividerCount)).biUnion
          (goodC.gamma (Fin.last KC.dividerCount)) := by
-- BODY
  classical
  have segRefl (S : TreeSequence G e0) : TreeSequenceInitialSegment S S :=
    ⟨le_rfl, fun _ => rfl, fun _ => rfl⟩
  have segTrans {S U W : TreeSequence G e0}
      (hSU : TreeSequenceInitialSegment S U)
      (hUW : TreeSequenceInitialSegment U W) :
      TreeSequenceInitialSegment S W := by
    refine ⟨le_trans hSU.1 hUW.1, ?_, ?_⟩
    · intro i
      exact (hUW.2.1 (Fin.castLE (Nat.succ_le_succ hSU.1) i)).trans
        (hSU.2.1 i)
    · intro i
      exact (hUW.2.2 (Fin.castLE hSU.1 i)).trans (hSU.2.2 i)
  have commonPrefix {S U W : TreeSequence G e0}
      (hSW : TreeSequenceInitialSegment S W)
      (hUW : TreeSequenceInitialSegment U W) (hlen : S.length ≤ U.length) :
      TreeSequenceInitialSegment S U := by
    refine ⟨hlen, ?_, ?_⟩
    · intro i
      exact (hUW.2.1 (Fin.castLE (Nat.succ_le_succ hlen) i)).symm.trans
        (hSW.2.1 i)
    · intro i
      exact (hUW.2.2 (Fin.castLE hlen i)).symm.trans (hSW.2.2 i)
  have stageSegment : ∀ (a d : ℕ) (hbound : a + d ≤ H.dividerCount + 1),
      TreeSequenceInitialSegment (H.stage ⟨a, by omega⟩)
        (H.stage ⟨a + d, by omega⟩) := by
    intro a d
    induction d with
    | zero => intro h; exact segRefl _
    | succ d ih =>
      intro h
      exact segTrans (ih (by omega)) (H.nested ⟨a + d, by omega⟩)
  let A := HierarchyStarredStage H (Fin.last H.dividerCount)
  let Tn := ett.series.data.tree (Fin.last ett.rounds).castSucc
  have lastZero (h : H.dividerCount = 0) : A = base.core := by
    simp [A, HierarchyStarredStage, h, Fin.last]
  have lastPositive (h : H.dividerCount ≠ 0) :
      A = H.stage ⟨H.dividerCount, by omega⟩ := by
    unfold A HierarchyStarredStage
    obtain hz | ⟨i, hi⟩ := Fin.eq_zero_or_eq_succ (Fin.last H.dividerCount)
    · exact False.elim (h (by simpa using congrArg Fin.val hz))
    · rw [hi, Fin.cases_succ]
      congr 1
      apply Fin.ext
      simpa using (congrArg Fin.val hi).symm
  have coreToA : TreeSequenceInitialSegment base.core A := by
    by_cases h : H.dividerCount = 0
    · rw [lastZero h]; exact segRefl _
    · rw [lastPositive h]
      have hs := stageSegment 1 (H.dividerCount - 1) (by omega)
      have he : 1 + (H.dividerCount - 1) = H.dividerCount := by omega
      have hs' : TreeSequenceInitialSegment (H.stage ⟨1, by omega⟩)
          (H.stage ⟨H.dividerCount, by omega⟩) := by simpa only [he] using hs
      exact segTrans H.coreInsideFirst hs'
  have TnToCore : TreeSequenceInitialSegment Tn base.core := by
    by_cases hp : ett.series.data.kind (Fin.last ett.rounds) =
        some TashkinovExtensionKind.PE
    · obtain ⟨_, _, ⟨u⟩⟩ := base.parallel hp
      exact u.leftSegment
    · rw [base.nonparallel hp]; exact segRefl _
  have coreToB := segTrans coreToA hAB
  have TnToB := segTrans TnToCore coreToB
  obtain ⟨g, hattach⟩ := hBC
  obtain ⟨hlenC, hBtoC, hg⟩ := hattach
  have TnToC := segTrans TnToB hBtoC
  have TnStrictC : Tn.length < C.length := lt_of_le_of_lt TnToB.1 hBCstrict
  have stageToB (j : Fin (H.dividerCount + 1)) :
      TreeSequenceInitialSegment (H.stage j.castSucc) Bminus := by
    by_cases h : H.dividerCount = 0
    · have hj : j.castSucc = (0 : Fin (H.dividerCount + 2)) :=
        Fin.ext (by have := j.isLt; simp only [Fin.val_castSucc, Fin.val_zero]; omega)
      rw [hj, H.baseStage]
      exact TnToB
    · have hs := stageSegment j.val (H.dividerCount - j.val) (by omega)
      have he : j.val + (H.dividerCount - j.val) = H.dividerCount := by omega
      have hs' : TreeSequenceInitialSegment (H.stage j.castSucc)
          (H.stage ⟨H.dividerCount, by omega⟩) := by
        convert hs using 1
        · apply congrArg H.stage; apply Fin.ext; rfl
        · apply congrArg H.stage; apply Fin.ext; exact he.symm
      exact segTrans hs' (by rw [← lastPositive h]; exact hAB)
  have starredToB (j : Fin (H.dividerCount + 1)) :
      TreeSequenceInitialSegment (HierarchyStarredStage H j) Bminus := by
    refine Fin.cases coreToB (fun i => ?_) j
    exact stageToB i.succ
  have vertexMem (S : TreeSequence G e0) (i : Fin (S.length + 1)) :
      S.vertex i ∈ TreeSequenceVertexSet S := by
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨i, rfl⟩
  have fixedC (j : Fin C.length) : mu (C.edge j) = phi (C.edge j) := by
    obtain ⟨i, hi⟩ := C.attaches j
    let ib : Fin (Bminus.length + 1) := ⟨i.val, by have := i.isLt; have := j.isLt; omega⟩
    have hv : C.vertex (Fin.castLT i
        (Nat.lt_trans i.isLt (Nat.succ_lt_succ j.isLt))) = Bminus.vertex ib := by
      exact hBtoC.2.1 ib
    apply hfixed
    refine ⟨Bminus.vertex ib, vertexMem _ _, ?_⟩
    change Bminus.vertex ib ∈ G.ends (C.edge j)
    rw [hi, hv]
    exact Sym2.mem_mk_right _ _
  have missingEq (S : TreeSequence G e0)
      (hS : TreeSequenceVertexSet S ⊆ TreeSequenceVertexSet Bminus) :
      TreeMissingColors mu S = TreeMissingColors phi S := by
    unfold TreeMissingColors
    apply Finset.biUnion_congr rfl
    intro v hv
    exact hmissingFixed v (hS hv)
  have hmod : ModColoring ett mu :=
    Td G k e0 input T phi ett hMP hpositive hlower mu hproperMu honeMu
      (by simpa [ett.generatingColoring] using hstable)
  have terminalRoute :
      (ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.PE ∧
        TashkinovAugmentationSequence mu Tn C) ∨
      ((ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.SE ∨
        ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.RE) ∧
        ∃ (f : E) (seed : TreeSequence G e0),
          ett.series.data.connectingEdges (Fin.last ett.rounds) = {f} ∧
          TreeSequenceAdjoinEdge Tn f seed ∧
          TashkinovAugmentationSequence mu seed C) := by
    have hCF := segTrans hCT ett.belowFinal
    have transport (S : TreeSequence G e0)
        (hSF : TashkinovAugmentationSequence phi S
          (ett.series.data.tree (Fin.last (ett.rounds + 1))))
        (hSC : TreeSequenceInitialSegment S C) :
        TashkinovAugmentationSequence mu S C := by
      exact TashkinovAugmentationSequenceColoringTransport phi mu S Bminus C
        (TashkinovAugmentationSequenceRestrict phi S C _ hSF hSC hCF)
        hBtoC hlenC (fun j _ => fixedC j) hmissingFixed
    have step := ett.series.certified (Fin.last ett.rounds)
    generalize hi : Fin.last ett.rounds = i at step
    cases step with
    | initial => have hv := congrArg Fin.val hi; simp at hv; omega
    | SE q _ _ _ _ _ choice _ coloring stored edges kind vertex outside delta gamma
        seed adjoin closure ordered strict =>
      have hq : q.succ = Fin.last ett.rounds := hi.symm
      have hlast : q.succ.succ = Fin.last (ett.rounds + 1) :=
        Fin.ext (by
          have hv := congrArg Fin.val hq
          simp only [Fin.val_succ, Fin.val_last] at hv ⊢
          omega)
      have hroute : TashkinovAugmentationSequence phi seed
          (ett.series.data.tree (Fin.last (ett.rounds + 1))) := by
        simpa [hq, hlast, ← ett.generatingColoring] using closure.1
      have hseedC : TreeSequenceInitialSegment seed C :=
        commonPrefix (TashkinovAugmentationSequenceInitialSegment phi _ _ hroute)
          hCF (by
            obtain ⟨ha, _, _⟩ := adjoin
            rw [hq] at ha
            change seed.length = Tn.length + 1 at ha
            omega)
      refine Or.inr ⟨Or.inl (by simpa [hq] using kind), choice.edge, seed,
        by simpa [hq] using edges, by simpa [Tn, hq] using adjoin,
        transport seed hroute hseedC⟩
    | PE q _ _ _ _ _ choice _ gamma _ second _ _ _ exit coloring proper one stored
        edges kind vertex outside delta gammaEq closure ordered strict =>
      have hq : q.succ = Fin.last ett.rounds := hi.symm
      have hlast : q.succ.succ = Fin.last (ett.rounds + 1) :=
        Fin.ext (by
          have hv := congrArg Fin.val hq
          simp only [Fin.val_succ, Fin.val_last] at hv ⊢
          omega)
      refine Or.inl ⟨by simpa [hq] using kind, transport Tn ?_ TnToC⟩
      simpa [Tn, hq, hlast, ← ett.generatingColoring] using closure.1
    | RE q _ _ _ _ available coloring stored edges kind vertex outside delta gamma
        seed adjoin closure ordered strict =>
      have hq : q.succ = Fin.last ett.rounds := hi.symm
      have hlast : q.succ.succ = Fin.last (ett.rounds + 1) :=
        Fin.ext (by
          have hv := congrArg Fin.val hq
          simp only [Fin.val_succ, Fin.val_last] at hv ⊢
          omega)
      have hroute : TashkinovAugmentationSequence phi seed
          (ett.series.data.tree (Fin.last (ett.rounds + 1))) := by
        simpa [hq, hlast, ← ett.generatingColoring] using closure.1
      have hseedC : TreeSequenceInitialSegment seed C :=
        commonPrefix (TashkinovAugmentationSequenceInitialSegment phi _ _ hroute)
          hCF (by
            obtain ⟨ha, _, _⟩ := adjoin
            rw [hq] at ha
            change seed.length = Tn.length + 1 at ha
            omega)
      refine Or.inr ⟨Or.inr (by simpa [hq] using kind), available.edge, seed,
        by simpa [hq] using edges, by simpa [Tn, hq] using adjoin,
        transport seed hroute hseedC⟩
  obtain ⟨corrC⟩ := hmod.2.2 C TnToC TnStrictC terminalRoute
  have hMPC := MaximumPropertyTransport G k e0 ett mu hmod C corrC hMP
  refine ⟨corrC, ?_⟩
  have peSupport {r : ℕ} {inp : PartialEdgeColoring E k}
      (s : TashkinovSeries G k r e0 inp) (q : Fin r)
      (hp : s.data.kind q.succ = some TashkinovExtensionKind.PE) :
      ∃ v u f, s.data.chosenVertex q.succ = some v ∧
        s.data.connectingEdges q.succ = {f} ∧
        v ∈ TreeSequenceVertexSet (s.data.tree q.succ.castSucc) ∧
        u ∉ TreeSequenceVertexSet (s.data.tree q.succ.castSucc) ∧
        G.ends f = s(v, u) := by
    have step := s.certified q.succ
    generalize hi : q.succ = i at step
    cases step with
    | initial _ _ _ _ _ kind =>
      rw [hi, kind] at hp; cases hp
    | SE j _ _ _ _ _ choice _ coloring stored edges kind =>
      rw [hi, kind] at hp; cases hp
    | RE j _ _ _ _ available coloring stored edges kind =>
      rw [hi, kind] at hp; cases hp
    | PE j _ _ _ _ _ choice _ gamma _ second _ _ _ exit coloring proper one stored
        edges kind vertex outside delta gammaEq closure ordered strict =>
      simpa only [hi] using
        (show ∃ v u f, s.data.chosenVertex j.succ = some v ∧
          s.data.connectingEdges j.succ = {f} ∧
          v ∈ TreeSequenceVertexSet (s.data.tree j.succ.castSucc) ∧
          u ∉ TreeSequenceVertexSet (s.data.tree j.succ.castSucc) ∧
          G.ends f = s(v, u) from
          ⟨choice.vertex, choice.otherEndpoint, choice.edge, vertex, edges,
            choice.vertexDefective.1, choice.otherOutside, choice.edgeEnds⟩)
  rcases corrC with ⟨newInput, newSeries, newETT, hr, hs, hgen, htrees, hstored,
    hedges, hkinds, hproper, hone, hstableSeries⟩
  cases newETT with
  | mk r rp series above strict below gen =>
    cases hr
    have heq : series = newSeries := eq_of_heq hs
    cases heq
    let rep : ExtendedTashkinovTree G k e0 newInput C mu :=
      ⟨ett.rounds, rp, newSeries, above, strict, below, gen⟩
    let q : Fin ett.rounds := ⟨ett.rounds - 1, by omega⟩
    have hq : q.succ = Fin.last ett.rounds := Fin.ext (by simp [q]; omega)
    have htree : newSeries.data.tree (Fin.last ett.rounds).castSucc = Tn := by
      simpa only [hq, Tn] using htrees q
    have hkind := hkinds (Fin.last ett.rounds)
    have chosenAgree (hp : ett.series.data.kind (Fin.last ett.rounds) =
        some TashkinovExtensionKind.PE) :
        newSeries.data.chosenVertex (Fin.last ett.rounds) =
          ett.series.data.chosenVertex (Fin.last ett.rounds) := by
      obtain ⟨v, u, f, hv, hf, hvin, huout, hends⟩ :=
        peSupport ett.series q (by simpa [hq] using hp)
      obtain ⟨v', u', f', hv', hf', hvin', huout', hends'⟩ :=
        peSupport newSeries q (by simpa [hq] using hkind.trans hp)
      have hedge : f' = f := by
        have hh := hedges q.succ
        rw [hf', hf] at hh
        simpa using hh
      have hvEq : v' = v := by
        rcases Sym2.eq_iff.mp (hends'.symm.trans (hedge ▸ hends)) with h | h
        · exact h.1
        · have hin : v ∈ TreeSequenceVertexSet (newSeries.data.tree q.succ.castSucc) := by
            simpa [hq, htree, Tn] using hvin
          exact False.elim (huout' (h.2 ▸ hin))
      simpa [hq] using hv'.trans ((congrArg some hvEq).trans hv.symm)
    have closureVertices (hp : ett.series.data.kind (Fin.last ett.rounds) =
        some TashkinovExtensionKind.PE) :
        TreeSequenceVertexSet base.closure ⊆ TreeSequenceVertexSet Bminus := by
      obtain ⟨_, _, ⟨u⟩⟩ := base.parallel hp
      intro v hv
      apply TreeSequenceInitialSegmentVertexSetSubset coreToB
      rw [u.vertexSet]
      exact Finset.mem_union_right _ hv
    -- The closure need not be an ordered prefix of the core.
    have closureMu (hp : ett.series.data.kind (Fin.last ett.rounds) =
        some TashkinovExtensionKind.PE) :
        TashkinovClosure mu
          (TreeSequencePrefix Tn base.supportPosition.val base.supportPositive
            (Nat.le_of_lt_succ base.supportPosition.isLt)) base.closure := by
      have hc := (base.parallel hp).2.1
      have sub := closureVertices hp
      have transport {S : TreeSequence G e0}
          (route : TashkinovAugmentationSequence phi S base.closure) :
          TashkinovAugmentationSequence mu S base.closure := by
        unfold TashkinovAugmentationSequence at route ⊢
        induction route using Relation.ReflTransGen.head_induction_on with
        | refl => exact Relation.ReflTransGen.refl
        | @head S U step tail ih =>
          have hUR := TashkinovAugmentationSequenceInitialSegment phi U base.closure tail
          have hUV := TreeSequenceInitialSegmentVertexSetSubset hUR
          obtain ⟨hlen, hSU, c, hcolor, hmiss⟩ := step
          refine Relation.ReflTransGen.head ⟨hlen, hSU, c, ?_, ?_⟩ ih
          · let j : Fin U.length := Fin.cast hlen.symm (Fin.last S.length)
            obtain ⟨i, hi⟩ := U.attaches j
            have hiB : TreeIncidentEdge Bminus (U.edge j) := by
              refine ⟨U.vertex j.succ, sub (hUV (vertexMem _ _)), ?_⟩
              change U.vertex j.succ ∈ G.ends (U.edge j)
              rw [hi]; exact Sym2.mem_mk_left _ _
            exact (hfixed (U.edge j) hiB).trans hcolor
          · unfold TreeMissingColors at hmiss ⊢
            obtain ⟨v, hv, hvc⟩ := Finset.mem_biUnion.mp hmiss
            refine Finset.mem_biUnion.mpr ⟨v, hv, ?_⟩
            rw [hmissingFixed v
              (sub (hUV (TreeSequenceInitialSegmentVertexSetSubset hSU hv)))]
            exact hvc
      refine ⟨transport hc.1, ?_⟩
      intro e c v he hv hcolor hmiss
      have hb := he
      simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and] at hb
      obtain ⟨u, hu, w, hw, hends⟩ := hb
      have hiB : TreeIncidentEdge Bminus e := by
        refine ⟨u, sub hu, ?_⟩
        change u ∈ G.ends e
        rw [hends]; exact Sym2.mem_mk_left _ _
      apply hc.2 he hv ((hfixed e hiB).symm.trans hcolor)
      rw [← hmissingFixed v (sub hv)]
      exact hmiss
    let pos : Fin ((newSeries.data.tree (Fin.last ett.rounds).castSucc).length + 1) :=
      Fin.cast (congrArg (fun S : TreeSequence G e0 => S.length + 1) htree.symm)
        base.supportPosition
    let baseC : HierarchyBase rep mu :=
      { core := base.core
        closure := base.closure
        supportPosition := pos
        supportPositive := by simpa [pos] using base.supportPositive
        terminalMissingColors := rfl
        parallel := by
          dsimp only [rep]
          intro hp
          have hpOld := hkind.symm.trans hp
          obtain ⟨hv, hc, hu⟩ := base.parallel hpOld
          refine ⟨?_, ?_, ?_⟩
          · rw [chosenAgree hpOld]
            have hvertex : (newSeries.data.tree (Fin.last ett.rounds).castSucc).vertex pos =
                Tn.vertex base.supportPosition := by
              dsimp [pos]
              generalize ht : newSeries.data.tree (Fin.last ett.rounds).castSucc = S at htree ⊢
              cases htree
              rfl
            rw [hvertex]; exact hv
          · simpa [pos, htree] using closureMu hpOld
          · simpa [htree] using hu
        nonparallel := by
          dsimp only [rep]
          intro hp
          exact (base.nonparallel (fun h => hp (hkind.trans h))).trans htree.symm }
    refine ⟨baseC, ?_⟩
    let stageC : Fin (H.dividerCount + 2) → TreeSequence G e0 :=
      fun j => if j.val = H.dividerCount + 1 then C else H.stage j
    have stageOld (j : Fin (H.dividerCount + 2)) (hj : j.val ≤ H.dividerCount) :
        stageC j = H.stage j := by
      exact if_neg (show j.val ≠ H.dividerCount + 1 by omega)
    have stageLast : stageC (Fin.last (H.dividerCount + 1)) = C := by
      simp only [stageC, Fin.val_last, ite_true]
    have divBound (i : Fin H.dividerCount) : (H.dividerPosition i).val ≤ C.length := by
      have hl := congrArg TreeSequence.length (H.dividerStage i)
      change (H.stage ⟨i.val + 1, by omega⟩).length = (H.dividerPosition i).val at hl
      have hs := stageToB i.succ
      rw [← hl]
      exact le_trans hs.1 hBtoC.1
    let KC : TashkinovHierarchy rep baseC :=
      { dividerCount := H.dividerCount
        stage := stageC
        baseStage := by
          rw [stageOld 0 (by simp), H.baseStage]
          exact htree.symm
        terminalStage := stageLast
        nested := by
          intro j
          rw [stageOld j.castSucc (by have := j.isLt; simp; omega)]
          by_cases hj : j.val = H.dividerCount
          · have he : j.succ = Fin.last (H.dividerCount + 1) := Fin.ext (by simp; omega)
            rw [he, stageLast]
            exact segTrans (stageToB j) hBtoC
          · rw [stageOld j.succ (by simp; have := j.isLt; omega)]
            exact H.nested j
        strict := by
          intro j
          rw [stageOld j.castSucc (by have := j.isLt; simp; omega)]
          by_cases hj : j.val = H.dividerCount
          · have he : j.succ = Fin.last (H.dividerCount + 1) := Fin.ext (by simp; omega)
            rw [he, stageLast]
            exact lt_of_le_of_lt (stageToB j).1 hBCstrict
          · rw [stageOld j.succ (by simp; have := j.isLt; omega)]
            exact H.strict j
        dividerPosition := fun i => ⟨(H.dividerPosition i).val, Nat.lt_succ_of_le (divBound i)⟩
        dividerPositive := H.dividerPositive
        dividerIncreasing := H.dividerIncreasing
        dividerStage := by
          intro i
          rw [stageOld ⟨i.val + 1, by omega⟩
            (by change i.val + 1 ≤ H.dividerCount; omega), H.dividerStage i]
          rw [TreeSequencePrefix, TreeSequencePrefix]
          congr 1
          · funext x
            exact hCT.2.1 (Fin.castLE (Nat.succ_le_succ (divBound i)) x)
          · funext x
            exact hCT.2.2 (Fin.castLE (divBound i) x)
        coreInsideFirst := by
          by_cases hd : H.dividerCount = 0
          · have he : (⟨1, by omega⟩ : Fin (H.dividerCount + 2)) =
                Fin.last (H.dividerCount + 1) := Fin.ext (by simp; omega)
            rw [he, stageLast]
            exact segTrans coreToB hBtoC
          · rw [stageOld ⟨1, by omega⟩ (by change 1 ≤ H.dividerCount; omega)]
            exact H.coreInsideFirst }
    have ordinaryEq (j : Fin (H.dividerCount + 1)) :
        KC.stage j.castSucc = H.stage j.castSucc :=
      stageOld j.castSucc (Nat.le_of_lt_succ j.isLt)
    have starredEq (j : Fin (H.dividerCount + 1)) :
        HierarchyStarredStage KC j = HierarchyStarredStage H j := by
      refine Fin.cases rfl (fun i => ordinaryEq i.succ) j
    have terminalMissing : TreeMissingColors mu Tn = TreeMissingColors phi Tn :=
      missingEq Tn (TreeSequenceInitialSegmentVertexSetSubset TnToB)
    have storedEq : TashkinovStoredColors newSeries.data (Fin.last ett.rounds) =
        TashkinovStoredColors ett.series.data (Fin.last ett.rounds) := by
      unfold TashkinovStoredColors
      simp only [hstored, ← hgen, ← ett.generatingColoring, htree, terminalMissing]
      rfl
    have indexedStoredEq (j : Fin (H.dividerCount + 1)) :
        HierarchyStoredColorsAt KC j = HierarchyStoredColorsAt H j := by
      change TashkinovStoredColors newSeries.data (Fin.last ett.rounds) \
          TreeMissingColors mu (HierarchyStarredStage KC j) =
        TashkinovStoredColors ett.series.data (Fin.last ett.rounds) \
          TreeMissingColors phi (HierarchyStarredStage H j)
      rw [storedEq, starredEq, missingEq _
        (TreeSequenceInitialSegmentVertexSetSubset (starredToB j))]
    have stageMissingEq (j : Fin (H.dividerCount + 1)) :
        HierarchyStageMissingColors KC j = HierarchyStageMissingColors H j := by
      refine Fin.cases ?_ (fun i => ?_) j
      · change TreeMissingColors mu (newSeries.data.tree (Fin.last ett.rounds).castSucc) =
          TreeMissingColors phi Tn
        rw [htree, terminalMissing]
      · change TreeMissingColors mu (KC.stage i.succ.castSucc) =
          TreeMissingColors phi (H.stage i.succ.castSucc)
        rw [ordinaryEq]
        exact missingEq _ (TreeSequenceInitialSegmentVertexSetSubset (stageToB i.succ))
    refine ⟨KC, ?_⟩
    -- Changing missingness only at the final position leaves the capped cutoff unchanged.
    have cutoffEq (eta : Fin k) :
        (HierarchyFirstMissingPosition mu C eta).val =
          (HierarchyFirstMissingPosition phi C eta).val := by
      have h (i : Fin (C.length + 1)) (hi : i.val < C.length) :
          eta ∈ MissingColors G mu (C.vertex i) ↔
            eta ∈ MissingColors G phi (C.vertex i) := by
        let ib : Fin (Bminus.length + 1) := ⟨i.val, by omega⟩
        have hv : C.vertex i = Bminus.vertex ib := hBtoC.2.1 ib
        rw [hv, hmissingFixed _ (vertexMem _ _)]
      let dm : Finset (Fin (C.length + 1)) :=
        Finset.univ.filter fun i => eta ∈ MissingColors G mu (C.vertex i)
      let dp : Finset (Fin (C.length + 1)) :=
        Finset.univ.filter fun i => eta ∈ MissingColors G phi (C.vertex i)
      change (if h : dm.Nonempty then dm.min' h else Fin.last C.length).val =
        (if h : dp.Nonempty then dp.min' h else Fin.last C.length).val
      by_cases hm : dm.Nonempty
      · rw [dif_pos hm]
        by_cases hp : dp.Nonempty
        · rw [dif_pos hp]
          apply Nat.le_antisymm
          · by_cases hj : (dp.min' hp).val < C.length
            · have hi : dp.min' hp ∈ dm := Finset.mem_filter.mpr
                ⟨Finset.mem_univ _, (h _ hj).mpr
                  ((Finset.mem_filter.mp (Finset.min'_mem dp hp)).2)⟩
              exact Finset.min'_le dm _ hi
            · have := (dm.min' hm).isLt; omega
          · by_cases hj : (dm.min' hm).val < C.length
            · have hi : dm.min' hm ∈ dp := Finset.mem_filter.mpr
                ⟨Finset.mem_univ _, (h _ hj).mp
                  ((Finset.mem_filter.mp (Finset.min'_mem dm hm)).2)⟩
              exact Finset.min'_le dp _ hi
            · have := (dp.min' hp).isLt; omega
        · rw [dif_neg hp]
          have hb : ¬(dm.min' hm).val < C.length := by
            intro hj
            apply hp
            exact ⟨dm.min' hm, Finset.mem_filter.mpr
              ⟨Finset.mem_univ _, (h _ hj).mp
                ((Finset.mem_filter.mp (Finset.min'_mem dm hm)).2)⟩⟩
          have := (dm.min' hm).isLt
          simp only [Fin.val_last]; omega
      · rw [dif_neg hm]
        by_cases hp : dp.Nonempty
        · rw [dif_pos hp]
          have hb : ¬(dp.min' hp).val < C.length := by
            intro hj
            apply hm
            exact ⟨dp.min' hp, Finset.mem_filter.mpr
              ⟨Finset.mem_univ _, (h _ hj).mpr
                ((Finset.mem_filter.mp (Finset.min'_mem dp hp)).2)⟩⟩
          have := (dp.min' hp).isLt
          simp only [Fin.val_last]; omega
        · rw [dif_neg hp]
    have nextPrefix (j : Fin (H.dividerCount + 1)) :
        TreeSequenceInitialSegment (KC.stage j.succ) (H.stage j.succ) ∧
          TreeSequenceInitialSegment (KC.stage j.succ) C := by
      change TreeSequenceInitialSegment (stageC j.succ) (H.stage j.succ) ∧
        TreeSequenceInitialSegment (stageC j.succ) C
      by_cases hj : j.val = H.dividerCount
      · have he : j.succ = Fin.last (H.dividerCount + 1) := Fin.ext (by simp; omega)
        rw [he, stageLast, H.terminalStage]
        exact ⟨hCT, segRefl C⟩
      · rw [stageOld j.succ (by simp; have := j.isLt; omega)]
        exact ⟨segRefl _, segTrans (stageToB ⟨j.val + 1, by omega⟩) hBtoC⟩
    have segmentSubset (j : Fin (H.dividerCount + 1)) (eta : Fin k) :
        HierarchySegmentColors KC j eta ⊆ HierarchySegmentColors H j eta := by
      have hUW := (nextPrefix j).1
      have hUC := (nextPrefix j).2
      have hcut : min (HierarchyFirstMissingPosition mu C eta).val
          (KC.stage j.succ).length =
          min (HierarchyFirstMissingPosition phi T eta).val
            (KC.stage j.succ).length := by
        rw [cutoffEq eta]
        exact HierarchyFirstMissingPositionPrefixCutoff phi C T hCT eta _ hUC.1
      intro c hc
      simp only [HierarchySegmentColors, Finset.mem_filter, Finset.mem_univ,
        true_and] at hc ⊢
      obtain ⟨r, hlo, hhi, hcol⟩ := hc
      refine ⟨Fin.castLE hUW.1 r, ?_, ?_, ?_⟩
      · simpa only [starredEq, Fin.val_castLE] using hlo
      · have hr : r.val < (HierarchyFirstMissingPosition phi T eta).val := by
          rw [hcut] at hhi
          exact lt_of_lt_of_le hhi (Nat.min_le_left _ _)
        exact lt_min hr (Fin.castLE hUW.1 r).isLt
      · rw [hUW.2.2 r]
        have hf := fixedC (Fin.castLE hUC.1 r)
        rw [hUC.2.2 r] at hf
        exact hf.symm.trans hcol
    have boundaryFixed (S : TreeSequence G e0)
        (hS : TreeSequenceVertexSet S ⊆ TreeSequenceVertexSet Bminus)
        (e : E) (he : e ∈ BoundaryEdges G (TreeSequenceVertexSet S)) :
        mu e = phi e := by
      simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and] at he
      obtain ⟨v, hv, w, hw, hends⟩ := he
      apply hfixed
      refine ⟨v, hS hv, ?_⟩
      change v ∈ G.ends e
      rw [hends]; exact Sym2.mem_mk_left _ _
    have minusEq (S : TreeSequence G e0)
        (hS : TreeSequenceVertexSet S ⊆ TreeSequenceVertexSet Bminus)
        (D : Finset (Fin k)) :
        TreeColorSetMinusClosed G mu S D ↔ TreeColorSetMinusClosed G phi S D := by
      have hb (c : Fin k) : BoundaryColorEdges G mu (TreeSequenceVertexSet S) c =
          BoundaryColorEdges G phi (TreeSequenceVertexSet S) c := by
        ext e
        simp only [BoundaryColorEdges, Finset.mem_filter]
        exact and_congr_right (fun he => by rw [boundaryFixed S hS e he])
      unfold TreeColorSetMinusClosed TreeColorSetClosed
      rw [missingEq S hS]
      simp only [hb]
    have refreshEq (i : Fin H.dividerCount) :
        ((TreeSequenceVertexSet (KC.stage i.succ.castSucc) \
          TreeSequenceVertexSet (HierarchyStarredStage KC i.castSucc)).biUnion
            fun v => MissingColors G mu v) =
        ((TreeSequenceVertexSet (H.stage i.succ.castSucc) \
          TreeSequenceVertexSet (HierarchyStarredStage H i.castSucc)).biUnion
            fun v => MissingColors G phi v) := by
      rw [ordinaryEq, starredEq]
      apply Finset.biUnion_congr rfl
      intro v hv
      exact hmissingFixed v (TreeSequenceInitialSegmentVertexSetSubset
        (stageToB i.succ) (Finset.mem_sdiff.mp hv).1)
    let goodC : GoodHierarchy KC :=
      { gamma := good.gamma
        twoColors := by
          intro j eta he
          exact good.twoColors j eta (indexedStoredEq j ▸ he)
        avoidance := by
          intro j eta he c hc
          have hav := good.avoidance j eta (indexedStoredEq j ▸ he) hc
          refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
          · rw [stageMissingEq]; exact (Finset.mem_sdiff.mp hav).1
          · intro hs
            exact (Finset.mem_sdiff.mp hav).2 (segmentSubset j eta hs)
        disjointPairs := by
          intro j eta theta he ht hne
          exact good.disjointPairs j eta theta (indexedStoredEq j ▸ he)
            (indexedStoredEq j ▸ ht) hne
        uniqueRefresh := by
          intro i
          simpa only [indexedStoredEq, refreshEq] using good.uniqueRefresh i
        parallelBase := by
          dsimp only
          intro hp
          have hpOld := hkind.symm.trans hp
          have hold := good.parallelBase hpOld
          change ¬TreeColorSetMinusClosed G mu base.core
              ((HierarchyStoredColorsAt KC 0).biUnion (good.gamma 0)) ∧
            4 ≤ ((TreeMissingColors mu (newSeries.data.tree (Fin.last ett.rounds).castSucc) ∩
              TreeMissingColors mu base.closure) \
                (HierarchyStoredColorsAt KC 0).biUnion (good.gamma 0)).card
          rw [indexedStoredEq, minusEq _ (TreeSequenceInitialSegmentVertexSetSubset coreToB),
            htree, terminalMissing, missingEq _ (closureVertices hpOld)]
          exact hold
        minusClosed := by
          intro i
          rw [ordinaryEq, indexedStoredEq,
            minusEq _ (TreeSequenceInitialSegmentVertexSetSubset (stageToB i.succ))]
          exact good.minusClosed i }
    refine ⟨goodC, hmod, hMPC, terminalRoute, rfl, ?_, ?_, ?_⟩
    · change 2 * ett.rounds + 11 ≤
        (TreeMissingColors mu (newSeries.data.tree (Fin.last ett.rounds).castSucc)).card
      rw [htree, terminalMissing]
      exact hlarge
    · change gamma ∉ (HierarchyStoredColorsAt KC (Fin.last H.dividerCount)).biUnion
        (good.gamma (Fin.last H.dividerCount))
      rw [indexedStoredEq]
      exact hgammaReserved
    · change beta ∉ (HierarchyStoredColorsAt KC (Fin.last H.dividerCount)).biUnion
        (good.gamma (Fin.last H.dividerCount))
      rw [indexedStoredEq]
      intro hb
      obtain ⟨eta, he, hbe⟩ := Finset.mem_biUnion.mp hb
      have hm := (GoodHierarchyReservedDisjoint good (Fin.last H.dividerCount)).1 eta he hbe
      obtain ⟨v, hv, hbv⟩ := Finset.mem_biUnion.mp hm
      apply hbeta
      exact Finset.mem_biUnion.mpr ⟨v,
        TreeSequenceInitialSegmentVertexSetSubset
          (segTrans (segTrans (starredToB _) hBtoC) hCT) hv, hbv⟩
