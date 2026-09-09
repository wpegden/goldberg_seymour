import Tablet.BoundaryColorVertex
import Tablet.ColoredVertexSetElementary
import Tablet.DefectiveColor
import Tablet.Degree
import Tablet.ETTFirstAppearanceIndex
import Tablet.GoodHierarchy
import Tablet.HierarchyBase
import Tablet.HierarchyCounterexample
import Tablet.HierarchyCounterexampleLess
import Tablet.HierarchyCounterexampleMeasure
import Tablet.HierarchyCounterexamplePathNumberBounds
import Tablet.HierarchyCounterexamplePenultimateElementary
import Tablet.HierarchyCounterexampleTailAtLeastTwo
import Tablet.HierarchyFullTailLength
import Tablet.HierarchyMinimumCounterexampleContext
import Tablet.HierarchySituationOneImpossible
import Tablet.HierarchySituationTwoImpossible
import Tablet.HierarchySituationThreeImpossible
import Tablet.IsOneEdgeUncolored
import Tablet.IsProperEdgeColoring
import Tablet.KTriple
import Tablet.MaximumDefectiveChoice
import Tablet.MaximumDegree
import Tablet.MaximumProperty
import Tablet.MissingColors
import Tablet.ModColoring
import Tablet.PresentColors
import Tablet.StableColoring
import Tablet.StableColoringBeforeVertex
import Tablet.TashkinovExtensionKind
import Tablet.TashkinovHierarchy
import Tablet.TashkinovOrder
import Tablet.TashkinovSeries
import Tablet.TashkinovSeriesStep
import Tablet.TashkinovStoredColors
import Tablet.TreeInterchangeable
import Tablet.TreeMissingColors
import Tablet.TreeSequence
import Tablet.TreeSequenceVertexSet
import Tablet.TreeVertexOrder
import Tablet.TwoColorComponent

-- [TABLET NODE: GoodHierarchyElementaryLarge]
theorem GoodHierarchyElementaryLarge {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : Nat) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (hMP : MaximumProperty ett)
    (base : HierarchyBase ett phi)
    (H : TashkinovHierarchy ett base)
    (hgood : GoodHierarchy H)
    (hlower : forall {input' : PartialEdgeColoring E k}
      {T' : TreeSequence G e0}
      {generating' : PartialEdgeColoring E k}
      (lower : ExtendedTashkinovTree G k e0 input' T' generating'),
      0 < lower.rounds -> lower.rounds < ett.rounds -> MaximumProperty lower ->
      ColoredVertexSetElementary G generating'
          (TreeSequenceVertexSet T') ∧
        (let n : Fin (lower.rounds + 1) := Fin.last lower.rounds
         let Tnext : TreeSequence G e0 :=
           lower.series.data.tree (Fin.last (lower.rounds + 1))
         forall sigma : PartialEdgeColoring E k,
           IsProperEdgeColoring G sigma -> IsOneEdgeUncolored sigma e0 ->
           StableColoring Tnext
             (TashkinovStoredColors lower.series.data n)
             (lower.series.data.coloring n) sigma ->
           forall alpha beta : Fin k,
             (alpha ∈ TreeMissingColors sigma Tnext ∨
               beta ∈ TreeMissingColors sigma Tnext) ->
             TreeInterchangeable G Tnext sigma alpha beta) ∧
        ((forall (q : Fin lower.rounds) (v : V),
          lower.series.data.kind q.succ =
              some TashkinovExtensionKind.PE ->
          lower.series.data.chosenVertex q.succ = some v ->
          forall hvFinal : v ∈ TreeSequenceVertexSet T',
          forall j : Fin (lower.rounds + 1),
            ETTFirstAppearanceIndex lower v hvFinal = j.val + 1 ->
            forall sigma : PartialEdgeColoring E k,
              IsProperEdgeColoring G sigma ->
              IsOneEdgeUncolored sigma e0 ->
              StableColoring
                (lower.series.data.tree q.succ.castSucc)
                (TashkinovStoredColors lower.series.data q.succ)
                (lower.series.data.coloring q.succ) sigma ->
              StableColoringBeforeVertex T' v hvFinal
                  (TashkinovStoredColors lower.series.data j)
                  (lower.series.data.coloring j) sigma ∧
                (0 < j.val ->
                  StableColoring (lower.series.data.tree j.castSucc)
                    (TashkinovStoredColors lower.series.data j)
                    (lower.series.data.coloring j) sigma)) ∧
          forall (q r : Fin lower.rounds) (vq vr : V),
            q ≠ r -> vq ≠ vr ->
            lower.series.data.kind q.succ =
                some TashkinovExtensionKind.PE ->
            lower.series.data.kind r.succ =
                some TashkinovExtensionKind.PE ->
            lower.series.data.chosenVertex q.succ = some vq ->
            lower.series.data.chosenVertex r.succ = some vr ->
            forall (hvq : vq ∈ TreeSequenceVertexSet T')
              (hvr : vr ∈ TreeSequenceVertexSet T'),
              ETTFirstAppearanceIndex lower vq hvq =
                  ETTFirstAppearanceIndex lower vr hvr ->
              Disjoint (lower.series.data.stored q.succ)
                (lower.series.data.stored r.succ)) ∧
        (let n : Fin (lower.rounds + 1) := Fin.last lower.rounds
         let Tn : TreeSequence G e0 :=
           lower.series.data.tree n.castSucc
         forall (v : V) (gamma delta : Fin k),
           lower.series.data.kind n = some TashkinovExtensionKind.PE ->
           lower.series.data.chosenVertex n = some v ->
           lower.series.data.gamma n = some gamma ->
           lower.series.data.delta n = some delta ->
           forall sigma : PartialEdgeColoring E k,
             IsProperEdgeColoring G sigma ->
             IsOneEdgeUncolored sigma e0 ->
             StableColoring Tn
               (TashkinovStoredColors lower.series.data n)
               (lower.series.data.coloring n) sigma ->
             forall w, w ∈ TreeSequenceVertexSet Tn ->
               (Sum.inl w ∈ TwoColorComponent G sigma gamma delta
                   (Sum.inl v) ↔ w = v)) ∧
        (let n : Fin (lower.rounds + 1) := Fin.last lower.rounds
         let Tn : TreeSequence G e0 :=
           lower.series.data.tree n.castSucc
         forall sigma : PartialEdgeColoring E k,
           IsProperEdgeColoring G sigma -> IsOneEdgeUncolored sigma e0 ->
           StableColoring Tn
             (TashkinovStoredColors lower.series.data n)
             (lower.series.data.coloring n) sigma ->
           forall (delta : Fin k),
             DefectiveColor G sigma (TreeSequenceVertexSet Tn) delta ->
             forall (v : V),
               BoundaryColorVertex G sigma (TreeSequenceVertexSet Tn)
                   delta v ->
               (exists w, BoundaryColorVertex G sigma
                   (TreeSequenceVertexSet Tn) delta w ∧
                 TreeVertexOrder Tn w v) ->
               forall (hvFinal : v ∈ TreeSequenceVertexSet T')
                 (q : Fin lower.rounds) (vi : V),
                 (lower.series.data.kind q.succ =
                      some TashkinovExtensionKind.PE ∨
                    lower.series.data.kind q.succ =
                      some TashkinovExtensionKind.SE) ->
                 lower.series.data.chosenVertex q.succ = some vi ->
                 ETTFirstAppearanceIndex lower v hvFinal ≤ q.val + 1 ->
                 v = vi ∨ TreeVertexOrder T' v vi) ∧
        (let n : Fin (lower.rounds + 1) := Fin.last lower.rounds
         let Tn : TreeSequence G e0 :=
           lower.series.data.tree n.castSucc
         forall sigma : PartialEdgeColoring E k,
           IsProperEdgeColoring G sigma -> IsOneEdgeUncolored sigma e0 ->
           StableColoring Tn
             (TashkinovStoredColors lower.series.data n)
             (lower.series.data.coloring n) sigma ->
           ModColoring lower sigma))
    (hcurrent : forall {input' : PartialEdgeColoring E k}
      {T' : TreeSequence G e0}
      {generating' : PartialEdgeColoring E k}
      (current : ExtendedTashkinovTree G k e0 input' T' generating'),
      current.rounds = ett.rounds -> MaximumProperty current ->
      ((forall (q : Fin current.rounds) (v : V),
        current.series.data.kind q.succ =
            some TashkinovExtensionKind.PE ->
        current.series.data.chosenVertex q.succ = some v ->
        forall hvFinal : v ∈ TreeSequenceVertexSet T',
        forall j : Fin (current.rounds + 1),
          ETTFirstAppearanceIndex current v hvFinal = j.val + 1 ->
          forall sigma : PartialEdgeColoring E k,
            IsProperEdgeColoring G sigma ->
            IsOneEdgeUncolored sigma e0 ->
            StableColoring
              (current.series.data.tree q.succ.castSucc)
              (TashkinovStoredColors current.series.data q.succ)
              (current.series.data.coloring q.succ) sigma ->
            StableColoringBeforeVertex T' v hvFinal
                (TashkinovStoredColors current.series.data j)
                (current.series.data.coloring j) sigma ∧
              (0 < j.val ->
                StableColoring (current.series.data.tree j.castSucc)
                  (TashkinovStoredColors current.series.data j)
                  (current.series.data.coloring j) sigma)) ∧
        forall (q r : Fin current.rounds) (vq vr : V),
          q ≠ r -> vq ≠ vr ->
          current.series.data.kind q.succ =
              some TashkinovExtensionKind.PE ->
          current.series.data.kind r.succ =
              some TashkinovExtensionKind.PE ->
          current.series.data.chosenVertex q.succ = some vq ->
          current.series.data.chosenVertex r.succ = some vr ->
          forall (hvq : vq ∈ TreeSequenceVertexSet T')
            (hvr : vr ∈ TreeSequenceVertexSet T'),
            ETTFirstAppearanceIndex current vq hvq =
                ETTFirstAppearanceIndex current vr hvr ->
            Disjoint (current.series.data.stored q.succ)
              (current.series.data.stored r.succ)) ∧
      (let n : Fin (current.rounds + 1) := Fin.last current.rounds
       let Tn : TreeSequence G e0 := current.series.data.tree n.castSucc
       forall (v : V) (gamma delta : Fin k),
         current.series.data.kind n = some TashkinovExtensionKind.PE ->
         current.series.data.chosenVertex n = some v ->
         current.series.data.gamma n = some gamma ->
         current.series.data.delta n = some delta ->
         forall sigma : PartialEdgeColoring E k,
           IsProperEdgeColoring G sigma ->
           IsOneEdgeUncolored sigma e0 ->
           StableColoring Tn
             (TashkinovStoredColors current.series.data n)
             (current.series.data.coloring n) sigma ->
           forall w, w ∈ TreeSequenceVertexSet Tn ->
             (Sum.inl w ∈ TwoColorComponent G sigma gamma delta
                 (Sum.inl v) ↔ w = v)) ∧
      (let n : Fin (current.rounds + 1) := Fin.last current.rounds
       let Tn : TreeSequence G e0 := current.series.data.tree n.castSucc
       forall sigma : PartialEdgeColoring E k,
         IsProperEdgeColoring G sigma -> IsOneEdgeUncolored sigma e0 ->
         StableColoring Tn
           (TashkinovStoredColors current.series.data n)
           (current.series.data.coloring n) sigma ->
         forall (delta : Fin k),
           DefectiveColor G sigma (TreeSequenceVertexSet Tn) delta ->
           forall (v : V),
             BoundaryColorVertex G sigma (TreeSequenceVertexSet Tn)
                 delta v ->
             (exists w, BoundaryColorVertex G sigma
                 (TreeSequenceVertexSet Tn) delta w ∧
               TreeVertexOrder Tn w v) ->
             forall (hvFinal : v ∈ TreeSequenceVertexSet T')
               (q : Fin current.rounds) (vi : V),
               (current.series.data.kind q.succ =
                    some TashkinovExtensionKind.PE ∨
                  current.series.data.kind q.succ =
                    some TashkinovExtensionKind.SE) ->
               current.series.data.chosenVertex q.succ = some vi ->
               ETTFirstAppearanceIndex current v hvFinal ≤ q.val + 1 ->
               v = vi ∨ TreeVertexOrder T' v vi) ∧
      (let n : Fin (current.rounds + 1) := Fin.last current.rounds
       let Tn : TreeSequence G e0 := current.series.data.tree n.castSucc
       forall sigma : PartialEdgeColoring E k,
         IsProperEdgeColoring G sigma -> IsOneEdgeUncolored sigma e0 ->
         StableColoring Tn
           (TashkinovStoredColors current.series.data n)
           (current.series.data.coloring n) sigma ->
         ModColoring current sigma))
    (hlargeOrder : 11 ≤ TashkinovOrder G)
    (hlarge : forall {input' : PartialEdgeColoring E k}
      {T' : TreeSequence G e0}
      {generating' : PartialEdgeColoring E k}
      (current : ExtendedTashkinovTree G k e0 input' T' generating'),
      current.rounds = ett.rounds -> MaximumProperty current ->
      forall (base' : HierarchyBase current generating')
        (K : TashkinovHierarchy current base'),
        GoodHierarchy K ->
        let n : Fin (current.rounds + 1) := Fin.last current.rounds
        let Tn := current.series.data.tree n.castSucc
        2 * current.rounds + 11 ≤
          (TreeMissingColors generating' Tn).card) :
    ColoredVertexSetElementary G phi (TreeSequenceVertexSet T) := by
-- BODY
  classical
  induction hq : H.dividerCount using Nat.strong_induction_on
      generalizing input T phi ett base H hgood with
  | h q ih =>
    by_contra hne
    let counter : HierarchyCounterexample base :=
      { positive := ett.roundsPositive
        hierarchy := H
        good := hgood
        maximum := hMP
        notElementary := hne }
    have finalProperties : IsProperEdgeColoring G phi ∧
        IsOneEdgeUncolored phi e0 := by
      have hr : 1 ≤ ett.rounds := ett.roundsPositive
      let q : Fin ett.rounds := ⟨ett.rounds - 1, by omega⟩
      have qlast : q.succ = Fin.last ett.rounds := by
        apply Fin.ext
        simp [q]
        omega
      generalize targetEq : q.succ = target
      cases ett.series.certified target with
      | initial triple seedLength initialColoring initialStored initialEdges
          initialKind initialVertex initialOutside initialDelta initialGamma
          initialClosure => exact (Fin.succ_ne_zero q targetEq).elim
      | SE i previousProper previousOneUncolored previousClosed
          previousNotStronglyClosed noRevisiting choice seriesAlternative
          currentColoring currentStored currentEdges currentKind currentVertex
          currentOutside currentDelta currentGamma adjoined adjoinedExactly
          closedExtension orderedExtension strictExtension =>
          have hi : i = q := by
            apply Fin.ext
            have hv := congrArg Fin.val targetEq
            simp at hv
            omega
          subst i
          have hgen : phi = ett.series.data.coloring q.succ := by
            calc
              phi = ett.series.data.coloring (Fin.last ett.rounds) := ett.generatingColoring
              _ = ett.series.data.coloring q.succ := congrArg _ qlast.symm
          simpa [hgen, currentColoring] using
            And.intro choice.selectedProper choice.selectedOneUncolored
      | PE i previousProper previousOneUncolored previousClosed
          previousNotStronglyClosed noRevisiting choice seriesAlternativeFails
          gamma gammaRule secondStable secondStableProper secondStableOneUncolored
          secondStableRelation exitWitness currentColoring currentProper
          currentOneUncolored currentStored currentEdges currentKind currentVertex
          currentOutside currentDelta currentGamma closedExtension orderedExtension
          strictExtension =>
          have hi : i = q := by
            apply Fin.ext
            have hv := congrArg Fin.val targetEq
            simp at hv
            omega
          subst i
          have hgen : phi = ett.series.data.coloring q.succ := by
            calc
              phi = ett.series.data.coloring (Fin.last ett.rounds) := ett.generatingColoring
              _ = ett.series.data.coloring q.succ := congrArg _ qlast.symm
          simpa [hgen] using And.intro currentProper currentOneUncolored
      | RE i previousProper previousOneUncolored previousClosed
          previousNotStronglyClosed available currentColoring currentStored
          currentEdges currentKind currentVertex currentOutside currentDelta
          currentGamma adjoined adjoinedExactly closedExtension orderedExtension
          strictExtension =>
          have hi : i = q := by
            apply Fin.ext
            have hv := congrArg Fin.val targetEq
            simp at hv
            omega
          subst i
          have hgen : phi = ett.series.data.coloring q.succ := by
            calc
              phi = ett.series.data.coloring (Fin.last ett.rounds) := ett.generatingColoring
              _ = ett.series.data.coloring q.succ := congrArg _ qlast.symm
          simpa [hgen, currentColoring] using
            And.intro previousProper previousOneUncolored
    have proper : IsProperEdgeColoring G phi := finalProperties.1
    have oneEdge : IsOneEdgeUncolored phi e0 := finalProperties.2
    let candidate : ℕ → ℕ → Prop := fun a b =>
      ∃ (input' : PartialEdgeColoring E k) (T' : TreeSequence G e0)
        (generating' : PartialEdgeColoring E k)
        (other : ExtendedTashkinovTree G k e0 input' T' generating')
        (base' : HierarchyBase other generating')
        (C' : HierarchyCounterexample base'),
        other.rounds = ett.rounds ∧
        C'.hierarchy.dividerCount = q ∧
        HierarchyCounterexampleMeasure C' = (a, b)
    have candidateExists : ∃ a b, candidate a b := by
      refine ⟨(HierarchyCounterexampleMeasure counter).1,
        (HierarchyCounterexampleMeasure counter).2, ?_⟩
      exact ⟨input, T, phi, ett, base, counter, rfl, by
        simpa [counter] using hq, rfl⟩
    have firstExists : ∃ a, ∃ b, candidate a b := candidateExists
    let first : ℕ := Nat.find firstExists
    have firstSpec : ∃ b, candidate first b := Nat.find_spec firstExists
    let second : ℕ := Nat.find firstSpec
    have secondSpec : candidate first second := Nat.find_spec firstSpec
    obtain ⟨inputMin, TMin, generatingMin, ettMin, baseMin, CMin,
      roundsMin, dividerMin, measureMin⟩ := secondSpec
    have minCounter : HierarchyCounterexample baseMin := CMin
    have minMinimal : ∀ {input' : PartialEdgeColoring E k}
        {T' : TreeSequence G e0}
        {generating' : PartialEdgeColoring E k}
        {other : ExtendedTashkinovTree G k e0 input' T' generating'}
        {base' : HierarchyBase other generating'}
        (C' : HierarchyCounterexample base'),
        other.rounds = ettMin.rounds →
        C'.hierarchy.dividerCount = CMin.hierarchy.dividerCount →
        ¬ HierarchyCounterexampleLess
          (HierarchyCounterexampleMeasure C')
          (HierarchyCounterexampleMeasure CMin) := by
      intro input' T' generating' other base' C' hround hdiv
      unfold HierarchyCounterexampleLess
      rw [measureMin] at ⊢
      have hroundQ : other.rounds = ett.rounds := hround.trans roundsMin
      have hdivQ : C'.hierarchy.dividerCount = q := hdiv.trans dividerMin
      by_cases hfirst : (HierarchyCounterexampleMeasure C').1 < first
      · have firstWitness : ∃ b, candidate
            (HierarchyCounterexampleMeasure C').1 b := by
            exact ⟨(HierarchyCounterexampleMeasure C').2,
              ⟨input', T', generating', other, base', C', hroundQ, hdivQ, rfl⟩⟩
        have := Nat.find_min' firstExists firstWitness
        omega
      · by_cases heq : (HierarchyCounterexampleMeasure C').1 = first
        · by_cases hsecond : (HierarchyCounterexampleMeasure C').2 < second
          · have := Nat.find_min' firstSpec (show candidate first
                (HierarchyCounterexampleMeasure C').2 from by
                exact ⟨input', T', generating', other, base', C', hroundQ, hdivQ,
                  Prod.ext heq rfl⟩)
            omega
          · omega
        · omega
    have certifiedProperties : ∀ {input' : PartialEdgeColoring E k}
        {T' : TreeSequence G e0} {generating' : PartialEdgeColoring E k}
        (other : ExtendedTashkinovTree G k e0 input' T' generating'),
        IsProperEdgeColoring G generating' ∧
        IsOneEdgeUncolored generating' e0 := by
      intro input' T' generating' other
      have hr : 1 ≤ other.rounds := other.roundsPositive
      let q : Fin other.rounds := ⟨other.rounds - 1, by omega⟩
      have qlast : q.succ = Fin.last other.rounds := by
        apply Fin.ext
        simp [q]
        omega
      generalize targetEq : q.succ = target
      cases other.series.certified target with
      | initial triple seedLength initialColoring initialStored initialEdges
          initialKind initialVertex initialOutside initialDelta initialGamma initialClosure =>
          exact (Fin.succ_ne_zero q targetEq).elim
      | SE i previousProper previousOneUncolored previousClosed previousNotStronglyClosed
          noRevisiting choice seriesAlternative currentColoring currentStored currentEdges currentKind
          currentVertex currentOutside currentDelta currentGamma adjoined adjoinedExactly
          closedExtension orderedExtension strictExtension =>
          have hi : i = q := by
            apply Fin.ext
            have hv := congrArg Fin.val targetEq
            simp at hv
            omega
          subst i
          have hgen : generating' = other.series.data.coloring q.succ := by
            calc
              generating' = other.series.data.coloring (Fin.last other.rounds) := other.generatingColoring
              _ = other.series.data.coloring q.succ := congrArg _ qlast.symm
          simpa [hgen, currentColoring] using
            And.intro choice.selectedProper choice.selectedOneUncolored
      | PE i previousProper previousOneUncolored previousClosed previousNotStronglyClosed
          noRevisiting choice seriesAlternativeFails gamma gammaRule secondStable secondStableProper
          secondStableOneUncolored secondStableRelation exitWitness currentColoring currentProper
          currentOneUncolored currentStored currentEdges currentKind currentVertex currentOutside
          currentDelta currentGamma closedExtension orderedExtension strictExtension =>
          have hi : i = q := by
            apply Fin.ext
            have hv := congrArg Fin.val targetEq
            simp at hv
            omega
          subst i
          have hgen : generating' = other.series.data.coloring q.succ := by
            calc
              generating' = other.series.data.coloring (Fin.last other.rounds) := other.generatingColoring
              _ = other.series.data.coloring q.succ := congrArg _ qlast.symm
          simpa [hgen] using And.intro currentProper currentOneUncolored
      | RE i previousProper previousOneUncolored previousClosed previousNotStronglyClosed available
          currentColoring currentStored currentEdges currentKind currentVertex currentOutside
          currentDelta currentGamma adjoined adjoinedExactly closedExtension orderedExtension
          strictExtension =>
          have hi : i = q := by
            apply Fin.ext
            have hv := congrArg Fin.val targetEq
            simp at hv
            omega
          subst i
          have hgen : generating' = other.series.data.coloring q.succ := by
            calc
              generating' = other.series.data.coloring (Fin.last other.rounds) := other.generatingColoring
              _ = other.series.data.coloring q.succ := congrArg _ qlast.symm
          simpa [hgen, currentColoring] using
            And.intro previousProper previousOneUncolored
    have ctx : HierarchyMinimumCounterexampleContext
        G k e0 inputMin TMin generatingMin ettMin baseMin CMin := by
      refine { proper := ?_, oneEdgeUncolored := ?_, lowerRung := ?_, fewerDividers := ?_, lexicographicMinimality := ?_, largeMissingSet := ?_ }
      · exact (certifiedProperties ettMin).1
      · exact (certifiedProperties ettMin).2
      · intro input' T' generating' lower positiveLower lowerLess maximumLower
        exact @hlower _ _ _ lower positiveLower (by omega) maximumLower
      · intro input' T' generating' other hround hmax base' K good less
        have lowerOther := fun {input'' : PartialEdgeColoring E k}
            {T'' : TreeSequence G e0} {generating'' : PartialEdgeColoring E k}
            (lower : ExtendedTashkinovTree G k e0 input'' T'' generating'')
            (hp : 0 < lower.rounds) (hl : lower.rounds < other.rounds)
            (hm : MaximumProperty lower) =>
          @hlower _ _ _ lower hp (by omega) hm
        have currentOther := fun {input'' : PartialEdgeColoring E k}
            {T'' : TreeSequence G e0} {generating'' : PartialEdgeColoring E k}
            (current : ExtendedTashkinovTree G k e0 input'' T'' generating'')
            (heq : current.rounds = other.rounds) (hm : MaximumProperty current) =>
          hcurrent current (by omega) hm
        have largeOther := fun {input'' : PartialEdgeColoring E k}
            {T'' : TreeSequence G e0} {generating'' : PartialEdgeColoring E k}
            (current : ExtendedTashkinovTree G k e0 input'' T'' generating'')
            (heq : current.rounds = other.rounds) (hm : MaximumProperty current)
            (base'' : HierarchyBase current generating'')
            (K'' : TashkinovHierarchy current base'') (good'' : GoodHierarchy K'') =>
          hlarge current (by omega) hm base'' K'' good''
        unfold ColoredVertexSetElementary
        intro u hu v hv huv
        exact (ih K.dividerCount (by omega) (input := input') (T := T')
          (phi := generating') (ett := other) hmax (base := base') (H := K)
          (hgood := good) lowerOther currentOther largeOther (by rfl)) hu hv huv
      · exact minMinimal
      · exact hlarge ettMin roundsMin CMin.maximum baseMin CMin.hierarchy CMin.good
    have missing : ∀ (mu : PartialEdgeColoring E k),
        IsProperEdgeColoring G mu → IsOneEdgeUncolored mu e0 →
        ∀ v : V, (MissingColors G mu v).Nonempty := by
      intro mu hmu hmuone v
      have triple : KTriple G k e0 input := by
        have step := ett.series.certified 0
        cases step with
        | initial triple => exact triple
      have degreeBound : MaximumDegree G + 1 ≤ k := triple.2.2.1
      have presentBound : ∀ w : V, (PresentColors G mu w).card ≤ Degree G w := by
        intro w
        have chooseEdge (c : {c : Fin k // c ∈ PresentColors G mu w}) :
            ∃ e, Incident G w e ∧ mu e = some c.1 := by
          simpa [PresentColors] using c.property
        let select : {c : Fin k // c ∈ PresentColors G mu w} →
            {e : E // Incident G w e} := fun c =>
          ⟨Classical.choose (chooseEdge c), (Classical.choose_spec (chooseEdge c)).1⟩
        have selectColor : ∀ c, mu (select c).1 = some c.1 := by
          intro c
          exact (Classical.choose_spec (chooseEdge c)).2
        have injective : Function.Injective select := by
          intro a b hab
          apply Subtype.ext
          apply Option.some.inj
          calc
            some (a : Fin k) = mu (select a).1 := (selectColor a).symm
            _ = mu (select b).1 := by rw [hab]
            _ = some (b : Fin k) := selectColor b
        letI : Fintype {c : Fin k // c ∈ PresentColors G mu w} := Fintype.ofFinite _
        have cardBound := Fintype.card_le_of_injective select injective
        change (PresentColors G mu w).card ≤
          (Finset.univ.filter (fun e => Incident G w e)).card
        simpa [Fintype.card_subtype] using cardBound
      have degreeBoundAt : ∀ w : V, Degree G w ≤ MaximumDegree G := by
        intro w
        unfold MaximumDegree
        exact Finset.le_max' _ _ (Finset.mem_insert.mpr (Or.inr
          (Finset.mem_image.mpr ⟨w, by simp⟩)))
      by_contra missingEmpty
      have empty : MissingColors G mu v = ∅ :=
        Finset.not_nonempty_iff_eq_empty.mp missingEmpty
      have allPresent : PresentColors G mu v = Finset.univ := by
        apply Finset.eq_univ_of_forall
        intro c
        by_contra absent
        have memMissing : c ∈ MissingColors G mu v := by
          simp [MissingColors, absent]
        simpa [empty] using memMissing
      have paletteBound : k ≤ (PresentColors G mu v).card := by
          rw [allPresent, Finset.card_univ]
          simp only [Fintype.card_fin]
          exact le_rfl
      have presentDegree := presentBound v
      have degreeAt := degreeBoundAt v
      omega
    have lower := HierarchyCounterexampleTailAtLeastTwo G k e0 inputMin TMin generatingMin ettMin baseMin CMin
      ctx.proper ctx.oneEdgeUncolored ctx.lowerRung ctx.fewerDividers
      ctx.lexicographicMinimality ctx.largeMissingSet
    dsimp at lower
    have pathBounds := HierarchyCounterexamplePathNumberBounds G k e0 inputMin TMin generatingMin
      ettMin baseMin CMin ctx.proper ctx.oneEdgeUncolored ctx.lowerRung ctx.fewerDividers
      ctx.lexicographicMinimality ctx.largeMissingSet
    dsimp at pathBounds
    have pathAtLeast : 1 ≤ HierarchyPathNumber CMin.hierarchy := pathBounds.1
    have pathAtMost : HierarchyPathNumber CMin.hierarchy ≤
        HierarchyFullTailLength CMin := pathBounds.2
    by_cases onePath : HierarchyPathNumber CMin.hierarchy = 1
    · exact HierarchySituationOneImpossible G k e0 inputMin TMin generatingMin
        ettMin baseMin CMin ctx onePath missing
    · by_cases fullPath : HierarchyPathNumber CMin.hierarchy = HierarchyFullTailLength CMin
      · exact HierarchySituationTwoImpossible G k e0 inputMin TMin generatingMin
          ettMin baseMin CMin ctx fullPath
      · have pathLower : 2 ≤ HierarchyPathNumber CMin.hierarchy := by omega
        have pathUpper : HierarchyPathNumber CMin.hierarchy < HierarchyFullTailLength CMin := by omega
        exact HierarchySituationThreeImpossible G k e0 inputMin TMin generatingMin
          ettMin baseMin CMin ctx pathLower pathUpper missing
