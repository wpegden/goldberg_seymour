import Tablet.CertifiedETTRestriction
import Tablet.ColoredVertexSetElementary
import Tablet.ExtendedTashkinovTree
import Tablet.GoodHierarchy
import Tablet.GoodHierarchyPrefixRepackage
import Tablet.GoodHierarchyTerminalPrefixRepackage
import Tablet.HierarchyBase
import Tablet.HierarchyCounterexample
import Tablet.HierarchyCounterexampleLess
import Tablet.HierarchyCounterexampleMeasure
import Tablet.HierarchyPathNumber
import Tablet.HierarchyStarredStage
import Tablet.IsOneEdgeUncolored
import Tablet.IsProperEdgeColoring
import Tablet.MaximumDefectiveChoice
import Tablet.MaximumProperty
import Tablet.ModColoring
import Tablet.OrderedTreeUnion
import Tablet.ParallelClosureUnionElementary
import Tablet.StableColoring
import Tablet.TashkinovHierarchy
import Tablet.TashkinovSeries
import Tablet.TashkinovSeriesStep
import Tablet.TashkinovStoredColors
import Tablet.TechnicalTheoremBase
import Tablet.TreeInterchangeable
import Tablet.TreeMissingColors
import Tablet.TreeSequenceInitialSegment
import Tablet.TreeSequencePrefix
import Tablet.TreeSequenceVertexSet

-- [TABLET NODE: HierarchyCounterexamplePenultimateElementary]
theorem HierarchyCounterexamplePenultimateElementary {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi)
    (C : HierarchyCounterexample base)
    (hproper : IsProperEdgeColoring G phi)
    (hone : IsOneEdgeUncolored phi e0)
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
        ((∀ (q : Fin lower.rounds) (v : V),
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
           ModColoring lower sigma))
    (hfewer : ∀ {input' : PartialEdgeColoring E k}
      {T' : TreeSequence G e0}
      {generating' : PartialEdgeColoring E k}
      (other : ExtendedTashkinovTree G k e0 input' T' generating'),
      other.rounds = ett.rounds → MaximumProperty other →
      ∀ (base' : HierarchyBase other generating')
        (K : TashkinovHierarchy other base'),
        GoodHierarchy K → K.dividerCount < C.hierarchy.dividerCount →
        ColoredVertexSetElementary G generating'
          (TreeSequenceVertexSet T'))
    (hminimal : ∀ {input' : PartialEdgeColoring E k}
      {T' : TreeSequence G e0}
      {generating' : PartialEdgeColoring E k}
      {other : ExtendedTashkinovTree G k e0 input' T' generating'}
      {base' : HierarchyBase other generating'}
      (C' : HierarchyCounterexample base'),
      other.rounds = ett.rounds →
      C'.hierarchy.dividerCount = C.hierarchy.dividerCount →
      ¬ HierarchyCounterexampleLess
        (HierarchyCounterexampleMeasure C')
        (HierarchyCounterexampleMeasure C))
    (hlarge :
      let n : Fin (ett.rounds + 1) := Fin.last ett.rounds
      let Tn := ett.series.data.tree n.castSucc
      2 * ett.rounds + 11 ≤ (TreeMissingColors phi Tn).card) :
    let H := C.hierarchy
    let A := HierarchyStarredStage H (Fin.last H.dividerCount)
    let ell := T.length - A.length
    let Ty := TreeSequencePrefix T
      (min (A.length + (ell - 1)) T.length)
      (by have hA := A.positive; have hT := T.positive; omega)
      (Nat.min_le_right _ _)
    ColoredVertexSetElementary G phi (TreeSequenceVertexSet Ty) := by
-- BODY
  classical
  dsimp only
  let H := C.hierarchy
  let A := HierarchyStarredStage H (Fin.last H.dividerCount)
  let ell := T.length - A.length
  let Ty := TreeSequencePrefix T
      (min (A.length + (ell - 1)) T.length)
      (by have hA := A.positive; have hT := T.positive; omega)
      (Nat.min_le_right _ _)
  have hAstage : ∀ hq : 0 < H.dividerCount,
      A = H.stage ⟨H.dividerCount, by omega⟩ := by
    intro hq
    have hlast : (Fin.last H.dividerCount : Fin (H.dividerCount + 1)) =
        (⟨H.dividerCount - 1, by omega⟩ : Fin H.dividerCount).succ := by
      apply Fin.ext
      simp
      omega
    dsimp [A, HierarchyStarredStage]
    rw [hlast]
    simp only [Fin.cases]
    apply congrArg H.stage
    apply Fin.ext
    simp
    omega
  let finalIndex : Fin (ett.rounds + 1) := Fin.last ett.rounds
  have hfinalIndex : finalIndex ≠ 0 := by
    intro hz
    have := congrArg Fin.val hz
    simp [finalIndex] at this
    have hn := C.positive
    omega
  have qzeroCore : H.dividerCount = 0 →
      ColoredVertexSetElementary G phi (TreeSequenceVertexSet A) := by
    intro hq
    have hA : A = base.core := by
      simp [A, H, HierarchyStarredStage, Fin.last, Fin.cases, hq]
    rw [hA]
    have transportElementary {rho sigma : PartialEdgeColoring E k}
        {X : TreeSequence G e0}
        (hmiss : ∀ v, v ∈ TreeSequenceVertexSet X →
          MissingColors G sigma v = MissingColors G rho v)
        (he : ColoredVertexSetElementary G rho (TreeSequenceVertexSet X)) :
        ColoredVertexSetElementary G sigma (TreeSequenceVertexSet X) := by
      intro u hu v hv huv
      rw [hmiss u hu, hmiss v hv]
      exact he hu hv huv
    have hcert := ett.series.certified finalIndex
    generalize indexEquation : finalIndex = index at hcert hfinalIndex
    cases hcert with
    | initial triple seedLength initialColoring initialStored initialEdges initialKind
        initialVertex initialOutside initialDelta initialGamma initialClosure =>
        exact (hfinalIndex (by simpa using indexEquation.symm)).elim
    | PE i previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed noRevisiting choice seriesAlternativeFails gamma gammaRule
        secondStable secondStableProper secondStableOneUncolored secondStableRelation exitWitness
        currentColoring currentProper currentOneUncolored currentStored currentEdges currentKind
        currentVertex currentOutside currentDelta currentGamma closedExtension orderedExtension
        strictExtension =>
        have currentKind' : ett.series.data.kind finalIndex =
            some TashkinovExtensionKind.PE := by
          simpa [indexEquation] using currentKind
        have hkind : ett.series.data.kind (Fin.last ett.rounds) =
            some TashkinovExtensionKind.PE := by simpa [finalIndex] using currentKind'
        have hstable : StableColoring
            (ett.series.data.tree (Fin.last ett.rounds).castSucc)
            (TashkinovStoredColors ett.series.data (Fin.last ett.rounds))
            phi phi := by
          simp [StableColoring]
        have hstable' : StableColoring
            (ett.series.data.tree (Fin.last ett.rounds).castSucc)
            (TashkinovStoredColors ett.series.data (Fin.last ett.rounds))
            (ett.series.data.coloring (Fin.last ett.rounds)) phi := by
          simpa [ett.generatingColoring] using hstable
        intro u hu v hv huv
        exact (ParallelClosureUnionElementary G k e0 input T phi ett
          C.maximum C.positive hlower hkind phi hproper hone hstable base (u := u)) hu hv huv
    | SE i previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed noRevisiting choice seriesAlternative currentColoring
        currentStored currentEdges currentKind currentVertex currentOutside currentDelta
        currentGamma adjoined adjoinedExactly closedExtension orderedExtension strictExtension =>
        have currentKind' : ett.series.data.kind finalIndex =
            some TashkinovExtensionKind.SE := by
          simpa [indexEquation] using currentKind
        have currentColoring' : ett.series.data.coloring finalIndex =
            choice.selected := by
          simpa [indexEquation] using currentColoring
        have htree : base.core =
            ett.series.data.tree (Fin.last ett.rounds).castSucc :=
          base.nonparallel (by
            intro hk
            rw [currentKind'] at hk
            cases hk)
        rw [htree]
        have hprev : ColoredVertexSetElementary G
            (ett.series.data.coloring i.castSucc)
            (TreeSequenceVertexSet (ett.series.data.tree i.succ.castSucc)) := by
          have hi : i.succ = Fin.last ett.rounds := by
            apply Fin.ext
            have hz := congrArg Fin.val indexEquation
            simp [finalIndex] at hz ⊢
            omega
          intro u hu v hv huv
          by_cases honeRound : ett.rounds = 1
          · have htech : ColoredVertexSetElementary G
                (ett.series.data.coloring 0)
                (TreeSequenceVertexSet (ett.series.data.tree ⟨1, by omega⟩)) :=
              (TechnicalTheoremBase G k ett.rounds e0 input ett.series).1
            have hi : i = ⟨0, by omega⟩ := by apply Fin.ext; omega
            have hu' : u ∈ TreeSequenceVertexSet
                (ett.series.data.tree ⟨1, by omega⟩) := by simpa [hi, honeRound] using hu
            have hv' : v ∈ TreeSequenceVertexSet
                (ett.series.data.tree ⟨1, by omega⟩) := by simpa [hi, honeRound] using hv
            have hci : i.castSucc = (0 : Fin (ett.rounds + 1)) := by
              apply Fin.ext
              have hz := congrArg Fin.val hi
              simp at hz ⊢
              omega
            rw [hci]
            exact htech hu' hv' huv
          · have hres := CertifiedETTRestriction G k e0 input T phi ett C.maximum
              (ett.rounds - 1) (by omega) (by omega)
            rcases hres with ⟨restricted, restrictedRounds, restrictedMaximum,
              restrictedTrees, restrictedData⟩
            have hl : ColoredVertexSetElementary G
                (ett.series.data.coloring i.castSucc)
                (TreeSequenceVertexSet (ett.series.data.tree (Fin.last ett.rounds).castSucc)) := by
              have hlow : ∀ {u}, u ∈ TreeSequenceVertexSet
                  (ett.series.data.tree
                    (⟨ett.rounds - 1 + 1, by omega⟩ : Fin (ett.rounds + 2))) →
                  ∀ {v}, v ∈ TreeSequenceVertexSet
                    (ett.series.data.tree
                      (⟨ett.rounds - 1 + 1, by omega⟩ : Fin (ett.rounds + 2))) →
                  u ≠ v → Disjoint
                    (MissingColors G
                      (ett.series.data.coloring
                        (⟨ett.rounds - 1, by omega⟩ : Fin (ett.rounds + 1))) u)
                    (MissingColors G
                      (ett.series.data.coloring
                        (⟨ett.rounds - 1, by omega⟩ : Fin (ett.rounds + 1))) v) := by
                intro u hu v hv huv
                exact (hlower (lower := restricted) (by omega) (by omega) restrictedMaximum).1 hu hv huv
              have hc : (⟨ett.rounds - 1, by omega⟩ : Fin (ett.rounds + 1)) = i.castSucc := by
                apply Fin.ext
                have hz := congrArg Fin.val indexEquation
                simp [finalIndex] at hz ⊢
                omega
              have ht : (⟨ett.rounds - 1 + 1, by omega⟩ : Fin (ett.rounds + 2)) =
                  (Fin.last ett.rounds).castSucc := by
                apply Fin.ext
                simp
                omega
              rw [hc, ht] at hlow
              intro u hu v hv huv
              exact hlow (u := u) hu hv huv
            have hu' : u ∈ TreeSequenceVertexSet
                (ett.series.data.tree (Fin.last ett.rounds).castSucc) := by simpa [hi] using hu
            have hv' : v ∈ TreeSequenceVertexSet
                (ett.series.data.tree (Fin.last ett.rounds).castSucc) := by simpa [hi] using hv
            exact hl hu' hv' huv
        have hmiss : ∀ v, v ∈ TreeSequenceVertexSet
            (ett.series.data.tree i.succ.castSucc) →
            MissingColors G choice.selected v =
              MissingColors G (ett.series.data.coloring i.castSucc) v := by
          intro v hv
          exact choice.selectedStable.2 v hv
        have hsel : ColoredVertexSetElementary G choice.selected
            (TreeSequenceVertexSet (ett.series.data.tree i.succ.castSucc)) :=
          transportElementary hmiss hprev
        have hi := congrArg Fin.val indexEquation
        simp [finalIndex] at hi
        have hidx : i.succ = Fin.last ett.rounds := by
          apply Fin.ext
          simp [finalIndex] at hi ⊢
          omega
        intro u hu v hv huv
        have hu' : u ∈ TreeSequenceVertexSet
            (ett.series.data.tree i.succ.castSucc) := by simpa [hidx] using hu
        have hv' : v ∈ TreeSequenceVertexSet
            (ett.series.data.tree i.succ.castSucc) := by simpa [hidx] using hv
        rw [ett.generatingColoring, currentColoring']
        exact hsel hu' hv' huv
    | RE i previousProper previousOneUncolored previousClosed previousNotStronglyClosed available
        currentColoring currentStored currentEdges currentKind currentVertex currentOutside
        currentDelta currentGamma adjoined adjoinedExactly closedExtension orderedExtension
        strictExtension =>
        have currentKind' : ett.series.data.kind finalIndex =
            some TashkinovExtensionKind.RE := by
          simpa [indexEquation] using currentKind
        have currentColoring' : ett.series.data.coloring finalIndex =
            ett.series.data.coloring i.castSucc := by
          simpa [indexEquation] using currentColoring
        have htree : base.core =
            ett.series.data.tree (Fin.last ett.rounds).castSucc :=
          base.nonparallel (by
            intro hk
            rw [currentKind'] at hk
            cases hk)
        rw [htree]
        have hprev : ColoredVertexSetElementary G
            (ett.series.data.coloring i.castSucc)
            (TreeSequenceVertexSet (ett.series.data.tree i.succ.castSucc)) := by
          have hi : i.succ = Fin.last ett.rounds := by
            apply Fin.ext
            have hz := congrArg Fin.val indexEquation
            simp [finalIndex] at hz ⊢
            omega
          intro u hu v hv huv
          by_cases honeRound : ett.rounds = 1
          · have htech : ColoredVertexSetElementary G
                (ett.series.data.coloring 0)
                (TreeSequenceVertexSet (ett.series.data.tree ⟨1, by omega⟩)) :=
              (TechnicalTheoremBase G k ett.rounds e0 input ett.series).1
            have hi : i = ⟨0, by omega⟩ := by apply Fin.ext; omega
            have hu' : u ∈ TreeSequenceVertexSet
                (ett.series.data.tree ⟨1, by omega⟩) := by simpa [hi, honeRound] using hu
            have hv' : v ∈ TreeSequenceVertexSet
                (ett.series.data.tree ⟨1, by omega⟩) := by simpa [hi, honeRound] using hv
            have hci : i.castSucc = (0 : Fin (ett.rounds + 1)) := by
              apply Fin.ext
              have hz := congrArg Fin.val hi
              simp at hz ⊢
              omega
            rw [hci]
            exact htech hu' hv' huv
          · have hres := CertifiedETTRestriction G k e0 input T phi ett C.maximum
              (ett.rounds - 1) (by omega) (by omega)
            rcases hres with ⟨restricted, restrictedRounds, restrictedMaximum,
              restrictedTrees, restrictedData⟩
            have hl : ColoredVertexSetElementary G
                (ett.series.data.coloring i.castSucc)
                (TreeSequenceVertexSet (ett.series.data.tree (Fin.last ett.rounds).castSucc)) := by
              have hlow : ∀ {u}, u ∈ TreeSequenceVertexSet
                  (ett.series.data.tree
                    (⟨ett.rounds - 1 + 1, by omega⟩ : Fin (ett.rounds + 2))) →
                  ∀ {v}, v ∈ TreeSequenceVertexSet
                    (ett.series.data.tree
                      (⟨ett.rounds - 1 + 1, by omega⟩ : Fin (ett.rounds + 2))) →
                  u ≠ v → Disjoint
                    (MissingColors G
                      (ett.series.data.coloring
                        (⟨ett.rounds - 1, by omega⟩ : Fin (ett.rounds + 1))) u)
                    (MissingColors G
                      (ett.series.data.coloring
                        (⟨ett.rounds - 1, by omega⟩ : Fin (ett.rounds + 1))) v) := by
                intro u hu v hv huv
                exact (hlower (lower := restricted) (by omega) (by omega) restrictedMaximum).1 hu hv huv
              have hc : (⟨ett.rounds - 1, by omega⟩ : Fin (ett.rounds + 1)) = i.castSucc := by
                apply Fin.ext
                have hz := congrArg Fin.val indexEquation
                simp [finalIndex] at hz ⊢
                omega
              have ht : (⟨ett.rounds - 1 + 1, by omega⟩ : Fin (ett.rounds + 2)) =
                  (Fin.last ett.rounds).castSucc := by
                apply Fin.ext
                simp
                omega
              rw [hc, ht] at hlow
              intro u hu v hv huv
              exact hlow (u := u) hu hv huv
            have hu' : u ∈ TreeSequenceVertexSet
                (ett.series.data.tree (Fin.last ett.rounds).castSucc) := by simpa [hi] using hu
            have hv' : v ∈ TreeSequenceVertexSet
                (ett.series.data.tree (Fin.last ett.rounds).castSucc) := by simpa [hi] using hv
            exact hl hu' hv' huv
        intro u hu v hv huv
        have hi := congrArg Fin.val indexEquation
        simp [finalIndex] at hi
        have hidx : i.succ = Fin.last ett.rounds := by
          apply Fin.ext
          simp [finalIndex] at hi ⊢
          omega
        have hu' : u ∈ TreeSequenceVertexSet
            (ett.series.data.tree i.succ.castSucc) := by simpa [hidx] using hu
        have hv' : v ∈ TreeSequenceVertexSet
            (ett.series.data.tree i.succ.castSucc) := by simpa [hidx] using hv
        have hcur : phi = ett.series.data.coloring i.castSucc := by
          calc
            phi = ett.series.data.coloring (Fin.last ett.rounds) := by
              simpa [ett.generatingColoring, finalIndex]
            _ = ett.series.data.coloring i.castSucc := currentColoring'
        rw [hcur]
        exact hprev hu' hv' huv
  have segmentRefl (X : TreeSequence G e0) : TreeSequenceInitialSegment X X :=
    ⟨le_rfl, (by intro i; rfl), (by intro i; rfl)⟩
  have segmentTrans {X Y Z : TreeSequence G e0}
      (hXY : TreeSequenceInitialSegment X Y)
      (hYZ : TreeSequenceInitialSegment Y Z) :
      TreeSequenceInitialSegment X Z := by
    rcases hXY with ⟨hxy, vxy, exy⟩
    rcases hYZ with ⟨hyz, vyz, eyz⟩
    refine ⟨le_trans hxy hyz, ?_, ?_⟩
    · intro i
      have hm := vyz (Fin.castLE (Nat.succ_le_succ hxy) i)
      simpa using hm.trans (vxy i)
    · intro i
      have hm := eyz (Fin.castLE hxy i)
      simpa using hm.trans (exy i)
  have stageSegment : ∀ (a d : ℕ), (hbound : a + d ≤ H.dividerCount + 1) →
      TreeSequenceInitialSegment (H.stage ⟨a, by omega⟩)
        (H.stage ⟨a + d, by omega⟩) := by
    intro a d hbound
    induction d with
    | zero => simpa using segmentRefl (H.stage ⟨a, by omega⟩)
    | succ d ih =>
      have hp := ih (by omega)
      have hn := H.nested ⟨a + d, by omega⟩
      have hn' : TreeSequenceInitialSegment (H.stage ⟨a+d, by omega⟩)
          (H.stage ⟨a+(d+1), by omega⟩) := by
        simpa [Nat.add_assoc] using hn
      exact segmentTrans hp hn'
  have aSegment : TreeSequenceInitialSegment A T := by
    by_cases hq : H.dividerCount = 0
    · have hc := H.coreInsideFirst
      have hi : (⟨1, by omega⟩ : Fin (H.dividerCount + 2)) =
          Fin.last (H.dividerCount + 1) := by
        apply Fin.ext
        simp [hq]
      have ht : H.stage ⟨1, by omega⟩ = T := by
        rw [hi]
        exact H.terminalStage
      have hc' : TreeSequenceInitialSegment base.core T := by
        convert hc using 1
        exact ht.symm
      simpa [A, H, HierarchyStarredStage, Fin.last, hq] using hc'
    · have hs := stageSegment H.dividerCount 1 (by omega)
      have hA : A = H.stage ⟨H.dividerCount, by omega⟩ := hAstage (by omega)
      have hT : H.stage ⟨H.dividerCount + 1, by omega⟩ = T := by
        convert H.terminalStage using 1
        apply congrArg H.stage
        apply Fin.ext
        rfl
      rw [hA]
      simpa [hA, hT] using hs
  have prefixEqOfSegment {X Y : TreeSequence G e0}
      (hXY : TreeSequenceInitialSegment X Y) :
      X = TreeSequencePrefix Y X.length X.positive hXY.1 := by
    cases X with
    | mk lx px vx ex vix eix fx ax =>
      cases Y with
      | mk ly py vy ey vyiy eiy fy ay =>
        rw [TreeSequence.mk.injEq]
        refine ⟨rfl, ?_, ?_⟩
        · apply heq_of_eq
          funext i
          simpa [TreeSequencePrefix] using (hXY.2.1 i).symm
        · apply heq_of_eq
          funext i
          simpa [TreeSequencePrefix] using (hXY.2.2 i).symm
  have prefixFull (X : TreeSequence G e0) :
      TreeSequencePrefix X X.length X.positive le_rfl = X := by
    symm
    exact prefixEqOfSegment (segmentRefl X)
  have hAlen : A.length ≤ T.length := aSegment.1
  change ColoredVertexSetElementary G phi (TreeSequenceVertexSet Ty)
  by_cases hzero : ell = 0
  · have hlen : A.length = T.length := by dsimp [ell] at hzero; omega
    have hTy : Ty = T := by
      have hmin : min (A.length + (ell - 1)) T.length = T.length := by
        dsimp [ell] at hzero ⊢
        omega
      simpa [Ty, hmin] using prefixFull T
    rw [hTy]
    have hq : H.dividerCount = 0 := by
      by_contra hn
      have hs := H.strict (Fin.last H.dividerCount)
      have hA : A = H.stage (Fin.last H.dividerCount).castSucc := by
        calc
          A = H.stage ⟨H.dividerCount, by omega⟩ := hAstage (by omega)
          _ = H.stage (Fin.last H.dividerCount).castSucc := by
            apply congrArg H.stage
            apply Fin.ext
            simp
      have hT : H.stage (Fin.last H.dividerCount).succ = T := by
        simpa using H.terminalStage
      rw [hT] at hs
      rw [← hA] at hs
      dsimp [ell] at hzero
      omega
    have hc : ColoredVertexSetElementary G phi
        (TreeSequenceVertexSet A) := qzeroCore hq
    have hAT : A = T := by
      have hp : A = TreeSequencePrefix T T.length T.positive le_rfl := by
        simpa [hlen] using (prefixEqOfSegment aSegment)
      exact hp.trans (prefixFull T)
    rename_i u
    intro hu v hv huv
    have setEq : TreeSequenceVertexSet A = TreeSequenceVertexSet T :=
      congrArg TreeSequenceVertexSet hAT
    have huA : u ∈ TreeSequenceVertexSet A :=
      Eq.mp (congrArg (fun s : Finset V => u ∈ s) setEq.symm) hu
    have hvA : v ∈ TreeSequenceVertexSet A :=
      Eq.mp (congrArg (fun s : Finset V => v ∈ s) setEq.symm) hv
    exact hc huA hvA huv
  by_cases honeTail : ell = 1
  · have hTy : Ty = A := by
      dsimp [Ty]
      have hmin : min (A.length + (ell - 1)) T.length = A.length := by
        dsimp [ell] at honeTail ⊢
        omega
      have hp := (prefixEqOfSegment aSegment).symm
      simpa [hmin] using hp
    rw [hTy]
    by_cases hq : H.dividerCount = 0
    · exact qzeroCore hq
    · have hr : (1 : ℕ) ≤ H.dividerCount := by omega
      obtain ⟨ep, hmp, hrounds, hseries, bp, hbc, hcl, hsp, hp, hcount,
        hstages, hpositions, goodp, hcolors, hclosed⟩ :=
        GoodHierarchyPrefixRepackage G k e0 input T phi phi ett C.maximum base H C.good
          ⟨H.dividerCount, by omega⟩ hr
      have hrval : (⟨H.dividerCount, by omega⟩ : Fin (H.dividerCount + 1)).val =
          H.dividerCount := rfl
      have hdiv : hp.dividerCount < C.hierarchy.dividerCount := by
        change hp.dividerCount < H.dividerCount
        rw [hcount, hrval]
        have hqpos : 0 < H.dividerCount := Nat.pos_of_ne_zero hq
        omega
      have hA : A = H.stage ⟨H.dividerCount, by omega⟩ := hAstage (by omega)
      rw [hA]
      exact hfewer ep hrounds hmp bp hp goodp hdiv
  · have htail : 2 ≤ ell := by omega
    have hBlen : Ty.length + 1 = T.length := by
      change min (A.length + (ell - 1)) T.length + 1 = T.length
      dsimp [ell] at htail ⊢
      omega
    have hAless : A.length < Ty.length := by
      change A.length < min (A.length + (ell - 1)) T.length
      dsimp [ell] at htail ⊢
      omega
    have prefixSegment {X : TreeSequence G e0} {q : ℕ}
        (hq : 1 ≤ q) (hqt : q ≤ X.length) :
        TreeSequenceInitialSegment (TreeSequencePrefix X q hq hqt) X := by
      refine ⟨hqt, ?_, ?_⟩
      · intro i
        rfl
      · intro i
        rfl
    have hBT : TreeSequenceInitialSegment Ty T := by
      exact prefixSegment (by omega) (by exact Nat.min_le_right _ _)
    have hAB : TreeSequenceInitialSegment A Ty := by
      have hATeq : A = TreeSequencePrefix T A.length A.positive hAlen :=
        prefixEqOfSegment aSegment
      rw [hATeq]
      have hqB : A.length ≤ Ty.length := by omega
      have hp := prefixSegment (X := Ty) (q := A.length) A.positive hqB
      convert hp using 1 <;> rfl
    have hABstrict : A.length < Ty.length := hAless
    by_cases helementary : ColoredVertexSetElementary G phi (TreeSequenceVertexSet Ty)
    · exact helementary
    · have hnot := helementary
      obtain ⟨ettB, hmpB, hroundB, hseriesB, baseB, hcoreB, hclosureB,
        hsupportB, HB, hcountB, hstagesB, hpositionsB, goodB, hgoodDataB⟩ :=
        GoodHierarchyTerminalPrefixRepackage G k e0 input T phi phi ett C.maximum
          base H C.good Ty hAB hABstrict hBT
      let CB : HierarchyCounterexample baseB :=
        { positive := by simpa [hroundB] using C.positive
          hierarchy := HB
          good := goodB
          maximum := hmpB
          notElementary := hnot }
      have hless : HierarchyCounterexampleLess
          (HierarchyCounterexampleMeasure CB)
          (HierarchyCounterexampleMeasure C) := by
        unfold HierarchyCounterexampleLess HierarchyCounterexampleMeasure
        dsimp [CB]
        have hstar : HierarchyStarredStage HB (Fin.last HB.dividerCount) = A := by
          have hs := (hstagesB (Fin.last HB.dividerCount)).2
          simpa [hcountB, A] using hs
        have htailB : Ty.length -
            (HierarchyStarredStage HB (Fin.last HB.dividerCount)).length = ell - 1 := by
          rw [hstar]
          dsimp [ell] at hBlen ⊢
          omega
        let candidateH := (Finset.Icc 1 ell).filter fun j =>
          ∀ r : Fin T.length, A.length + j ≤ r.val →
            G.ends (T.edge r) = s(T.vertex r.castSucc, T.vertex r.succ)
        let candidateB := (Finset.Icc 1 (ell - 1)).filter fun j =>
          ∀ r : Fin Ty.length,
            A.length + j ≤ r.val →
              G.ends (Ty.edge r) = s(Ty.vertex r.castSucc, Ty.vertex r.succ)
        have pathH : HierarchyPathNumber H =
            if h : candidateH.Nonempty then candidateH.min' h else ell := by
          simp [HierarchyPathNumber, candidateH, A, ell]
        have pathB : HierarchyPathNumber HB =
            if h : candidateB.Nonempty then candidateB.min' h else ell - 1 := by
          have htailDef : Ty.length - A.length = ell - 1 := by
            dsimp [ell] at hBlen ⊢
            omega
          simp [HierarchyPathNumber, candidateB, hstar, htailB, htailDef, ell]
        have candidateHFull : ell ∈ candidateH := by
          simp only [candidateH, Finset.mem_filter, Finset.mem_Icc]
          refine ⟨⟨by omega, by omega⟩, ?_⟩
          intro r hr
          have hr' : A.length + ell ≤ T.length := by
            dsimp [ell]
            omega
          omega
        have candidateBFull : ell - 1 ∈ candidateB := by
          simp only [candidateB, Finset.mem_filter, Finset.mem_Icc]
          refine ⟨⟨by omega, by omega⟩, ?_⟩
          intro r hr
          have hr' : A.length + (ell - 1) ≤ Ty.length := by
            dsimp [Ty]
            omega
          omega
        have transferCandidate {j : ℕ} (hj : j ∈ candidateH) (hjlt : j < ell) :
            j ∈ candidateB := by
          rcases (Finset.mem_filter.mp hj) with ⟨hjI, hjP⟩
          apply Finset.mem_filter.mpr
          refine ⟨?_, ?_⟩
          · exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hjI).1, by omega⟩
          · intro r hr
            let rT : Fin T.length := ⟨r.val, by omega⟩
            have hp := hjP rT (by omega)
            have hev := hBT.2.2 r
            have hv0 := hBT.2.1 r.castSucc
            have hv1 := hBT.2.1 r.succ
            have hri : (Fin.castLE hBT.1 r : Fin T.length) = rT := by
              apply Fin.ext
              rfl
            rw [← hev, ← hv0, ← hv1]
            rw [hri]
            exact hp
        have pathLE : HierarchyPathNumber HB ≤ HierarchyPathNumber H := by
          by_cases hNH : candidateH.Nonempty
          · rw [pathH, dif_pos hNH]
            by_cases hEq : candidateH.min' hNH = ell
            · rw [pathB, dif_pos ⟨ell - 1, candidateBFull⟩]
              exact (Finset.min'_le candidateB (ell - 1) candidateBFull).trans (by omega)
            · have hmem := Finset.min'_mem candidateH hNH
              have hle := Finset.min'_le candidateH _ hmem
              have hleFull := Finset.min'_le candidateH ell candidateHFull
              have hlt : candidateH.min' hNH < ell := by omega
              rw [pathB, dif_pos ⟨candidateH.min' hNH,
                transferCandidate hmem hlt⟩]
              exact Finset.min'_le candidateB _
                (transferCandidate hmem hlt)
          · rw [pathH, dif_neg hNH]
            rw [pathB, dif_pos ⟨ell - 1, candidateBFull⟩]
            exact le_trans (Finset.min'_le candidateB (ell - 1) candidateBFull) (by omega)
        by_cases hlt : HierarchyPathNumber HB < HierarchyPathNumber H
        · exact Or.inl hlt
        · right
          have heq : HierarchyPathNumber HB = HierarchyPathNumber H := by omega
          refine ⟨heq, ?_⟩
          have hstage : HB.stage ⟨HB.dividerCount, by omega⟩ =
              H.stage ⟨H.dividerCount, by omega⟩ := by
            have hs := (hstagesB (Fin.last HB.dividerCount)).1
            have hiH : (⟨H.dividerCount, by omega⟩ : Fin (H.dividerCount + 2)) =
                (Fin.cast (congrArg (fun n : ℕ => n + 1) hcountB)
                  (Fin.last HB.dividerCount)).castSucc := by
              apply Fin.ext
              simp [hcountB]
            have hiB : (⟨HB.dividerCount, by omega⟩ : Fin (HB.dividerCount + 2)) =
                (Fin.last HB.dividerCount).castSucc := by
              apply Fin.ext
              rfl
            rw [hiB, hiH]
            exact hs
          rw [hstage]
          have hsle : (H.stage ⟨H.dividerCount, by omega⟩).length ≤ Ty.length := by
            have hn := HB.nested (Fin.last HB.dividerCount)
            have ht := HB.terminalStage
            have hnext : HB.stage (Fin.last HB.dividerCount).succ = Ty := by
              convert ht using 1 <;> apply congrArg HB.stage <;>
                apply Fin.ext <;> rfl
            have hle := hn.1
            rw [hnext] at hle
            have hle' : (HB.stage ⟨HB.dividerCount, by omega⟩).length ≤ Ty.length := by
              have hi : (⟨HB.dividerCount, by omega⟩ : Fin (HB.dividerCount + 2)) =
                  (Fin.last HB.dividerCount).castSucc := by
                apply Fin.ext
                rfl
              simpa [hi] using hle
            have hlenStage := congrArg TreeSequence.length hstage
            rw [hlenStage] at hle'
            exact hle'
          change Ty.length - (H.stage ⟨H.dividerCount, by omega⟩).length <
            T.length - (H.stage ⟨H.dividerCount, by omega⟩).length
          rw [← hBlen]
          omega
      exact False.elim ((hminimal CB hroundB hcountB) hless)
