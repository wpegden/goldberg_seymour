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
  sorry
