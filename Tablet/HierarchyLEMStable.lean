import Tablet.BoundaryColorEdges
import Tablet.BoundaryEdges
import Tablet.ExtendedTashkinovTree
import Tablet.HierarchyBase
import Tablet.HierarchyOutsideKempeStable
import Tablet.HierarchySplitter
import Tablet.HierarchyTerminalStoredColors
import Tablet.MaximumPropertyTransport
import Tablet.ModColoring
import Tablet.OutsideKempeGoodHierarchy
import Tablet.OutsideKempeRecoloringStable
import Tablet.SameGoodHierarchy
import Tablet.SameHierarchyStages
import Tablet.StableColoring
import Tablet.TashkinovAugmentation
import Tablet.TashkinovAugmentationSequence
import Tablet.TashkinovClosure
import Tablet.TashkinovHierarchy
import Tablet.TashkinovSeries
import Tablet.TashkinovSeriesStep
import Tablet.Td
import Tablet.TreeColorSetClosed
import Tablet.TreeColorSetMinusClosed
import Tablet.TreeIncidentEdge
import Tablet.TreeMissingColors
import Tablet.TreeSequenceAdjoinEdge
import Tablet.TreeSequenceInitialSegment
import Tablet.TreeSequenceVertexSet

-- [TABLET NODE: HierarchyLEMStable]
theorem HierarchyLEMStable {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi sigma : PartialEdgeColoring E k)
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
    (base : HierarchyBase ett phi) (H : TashkinovHierarchy ett base)
    (good : GoodHierarchy H)
    (hproper : IsProperEdgeColoring G phi)
    (hone : IsOneEdgeUncolored phi e0)
    (alpha beta : Fin k)
    (hrecolor : OutsideKempeRecoloring T phi sigma alpha beta) :
    let n : Fin (ett.rounds + 1) := Fin.last ett.rounds
    let Dn := TashkinovStoredColors ett.series.data n
    IsProperEdgeColoring G sigma ∧ IsOneEdgeUncolored sigma e0 ∧
    StableColoring T Dn phi sigma ∧ TreeColoringInvariant T phi sigma ∧
    ∃ corr : CorrespondingExtendedTashkinovTree G k e0 ett sigma T,
      MaximumProperty corr.replacementETT ∧
      ∃ baseSigma : HierarchyBase corr.replacementETT sigma,
        ∃ K : TashkinovHierarchy corr.replacementETT baseSigma,
          ∃ goodSigma : GoodHierarchy K,
            SameGoodHierarchy good goodSigma ∧
            (TreeColorSetMinusClosed G phi T
                ((HierarchyTerminalStoredColors H).biUnion
                  (good.gamma (Fin.last H.dividerCount))) →
              TreeColorSetMinusClosed G sigma T
                ((HierarchyTerminalStoredColors H).biUnion
                  (good.gamma (Fin.last H.dividerCount)))) := by
-- BODY
  dsimp
  have hstable := HierarchyOutsideKempeStable G k e0 input T phi sigma ett base H
    hproper hone alpha beta hrecolor
  have hdetail := OutsideKempeRecoloringStable G e0 T
    (TashkinovStoredColors ett.series.data (Fin.last ett.rounds)) phi sigma alpha beta
    hproper hone hrecolor
  rcases hstable with ⟨hsigma, honeSigma, hstab, hinv, hcomb⟩
  rcases hdetail with ⟨_, _, _, _, hfixed⟩
  have hsegOuter : TreeSequenceInitialSegment
      (ett.series.data.tree (Fin.last ett.rounds).castSucc) T := by
    have segmentTrans {A B C : TreeSequence G e0}
        (hAB : TreeSequenceInitialSegment A B)
        (hBC : TreeSequenceInitialSegment B C) :
        TreeSequenceInitialSegment A C := by
      rcases hAB with ⟨hab, hvab, heab⟩
      rcases hBC with ⟨hbc, hvbc, hebc⟩
      refine ⟨le_trans hab hbc, ?_, ?_⟩
      · intro i
        have hmid := hvbc (Fin.castLE (Nat.succ_le_succ hab) i)
        simpa using hmid.trans (hvab i)
      · intro i
        have hmid := hebc (Fin.castLE hab i)
        simpa using hmid.trans (heab i)
    exact ett.abovePenultimate
  have hsub : TreeSequenceVertexSet
      (ett.series.data.tree (Fin.last ett.rounds).castSucc) ⊆
      TreeSequenceVertexSet T := by
    rcases hsegOuter with ⟨hlen, hvertex, hedge⟩
    intro v hv
    classical
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and] at hv ⊢
    rcases hv with ⟨i, rfl⟩
    let j : Fin (T.length + 1) := Fin.castLE (m := T.length + 1)
      (Nat.succ_le_succ hlen) i
    refine ⟨j, ?_⟩
    exact hvertex i
  have hinc : ∀ f, TreeIncidentEdge
      (ett.series.data.tree (Fin.last ett.rounds).castSucc) f →
      TreeIncidentEdge T f := by
    intro f hf
    rcases hf with ⟨v, hv, hi⟩
    exact ⟨v, hsub hv, hi⟩
  have segmentCombine : ∀ {A B C : TreeSequence G e0},
      TreeSequenceInitialSegment A B →
      TreeSequenceInitialSegment B C →
      TreeSequenceInitialSegment A C := by
    intro A B C hAB hBC
    rcases hAB with ⟨hab, hvab, heab⟩
    rcases hBC with ⟨hbc, hvbc, hebc⟩
    refine ⟨le_trans hab hbc, ?_, ?_⟩
    · intro i
      simpa using (hvbc (Fin.castLE (Nat.succ_le_succ hab) i)).trans (hvab i)
    · intro i
      simpa using (hebc (Fin.castLE hab i)).trans (heab i)
  have commonSegment : ∀ {A B C : TreeSequence G e0},
      TreeSequenceInitialSegment A C →
      TreeSequenceInitialSegment B C → B.length ≤ A.length →
      TreeSequenceInitialSegment B A := by
    intro A B C hAC hBC hBA
    rcases hAC with ⟨hac, hvac, heac⟩
    rcases hBC with ⟨hbc, hvbc, hebc⟩
    refine ⟨hBA, ?_, ?_⟩
    · intro i
      calc
        A.vertex (Fin.castLE (Nat.succ_le_succ hBA) i) =
            C.vertex (Fin.castLE (Nat.succ_le_succ hac)
              (Fin.castLE (Nat.succ_le_succ hBA) i)) :=
          (hvac _).symm
        _ = C.vertex (Fin.castLE (Nat.succ_le_succ hbc) i) := by congr 1
        _ = B.vertex i := hvbc i
    · intro i
      calc
        A.edge (Fin.castLE hBA i) =
            C.edge (Fin.castLE hac (Fin.castLE hBA i)) := (heac _).symm
        _ = C.edge (Fin.castLE hbc i) := by congr 1
        _ = B.edge i := hebc i
  have hladder : StableColoring
      (ett.series.data.tree (Fin.last ett.rounds).castSucc)
      (TashkinovStoredColors ett.series.data (Fin.last ett.rounds))
      (ett.series.data.coloring (Fin.last ett.rounds)) sigma := by
    have hgen : ett.series.data.coloring (Fin.last ett.rounds) = phi :=
      ett.generatingColoring.symm
    constructor
    · intro f hf hx
      simpa [hgen] using hfixed f (hinc f hf)
    · intro v hv
      simpa [hgen] using hstab.2 v (hsub hv)
  have restrictSequence : ∀ (coloring : PartialEdgeColoring E k)
      (A B C : TreeSequence G e0),
      TashkinovAugmentationSequence coloring A C →
      TreeSequenceInitialSegment A B →
      TreeSequenceInitialSegment B C →
      TashkinovAugmentationSequence coloring A B := by
    intro coloring A B C hseq hAB hBC
    have equalTrees : ∀ {X Y : TreeSequence G e0},
        TreeSequenceInitialSegment X Y → X.length = Y.length → X = Y := by
      intro X Y hXY hlen
      rcases hXY with ⟨hle, hv, he⟩
      cases X with
      | mk lx px vx ex vix eix fx ax =>
        cases Y with
        | mk ly py vy ey viy eiy fy ay =>
          simp only at hlen
          subst ly
          rw [TreeSequence.mk.injEq]
          refine ⟨rfl, ?_, ?_⟩
          · apply heq_of_eq
            funext i
            simpa only [Fin.castLE] using (hv i).symm
          · apply heq_of_eq
            funext i
            simpa only [Fin.castLE] using (he i).symm
    have commonExtension : ∀ {X Y Z : TreeSequence G e0},
        TreeSequenceInitialSegment X Z →
        TreeSequenceInitialSegment Y Z →
        Y.length ≤ X.length → TreeSequenceInitialSegment Y X := by
      intro X Y Z hXZ hYZ hYX
      rcases hXZ with ⟨hx, hvx, hex⟩
      rcases hYZ with ⟨hy, hvy, hey⟩
      refine ⟨hYX, ?_, ?_⟩
      · intro i
        calc
          X.vertex (Fin.castLE (Nat.succ_le_succ hYX) i) =
              Z.vertex (Fin.castLE (Nat.succ_le_succ hx)
                (Fin.castLE (Nat.succ_le_succ hYX) i)) :=
            (hvx (Fin.castLE (Nat.succ_le_succ hYX) i)).symm
          _ = Z.vertex (Fin.castLE (Nat.succ_le_succ hy) i) := by
            congr 1
          _ = Y.vertex i := hvy i
      · intro i
        calc
          X.edge (Fin.castLE hYX i) =
              Z.edge (Fin.castLE hx (Fin.castLE hYX i)) :=
            (hex (Fin.castLE hYX i)).symm
          _ = Z.edge (Fin.castLE hy i) := by congr 1
          _ = Y.edge i := hey i
    unfold TashkinovAugmentationSequence at hseq ⊢
    induction hseq generalizing B with
    | refl =>
        have hlen : B.length = A.length :=
          Nat.le_antisymm hBC.1 hAB.1
        have heq : B = A := equalTrees hBC hlen
        subst B
        exact Relation.ReflTransGen.refl
    | @tail X C hAX hXC ih =>
        rcases hXC with ⟨hlen, hinit, hcolor⟩
        by_cases hBA : B.length ≤ X.length
        · exact ih B hAB (commonExtension hinit hBC hBA)
        · have hBlen : B.length = C.length := by
            rcases hBC with ⟨hBCle, _, _⟩
            omega
          have heq : B = C := equalTrees hBC hBlen
          subst B
          exact Relation.ReflTransGen.tail hAX ⟨hlen, hinit, hcolor⟩
  have transportSequence : ∀ {A : TreeSequence G e0},
      TashkinovAugmentationSequence phi A T →
      TashkinovAugmentationSequence sigma A T := by
    intro A hseq
    have vertexTransfer : ∀ {X Y : TreeSequence G e0},
        TashkinovAugmentation phi X Y →
        ∀ v, v ∈ TreeSequenceVertexSet X → v ∈ TreeSequenceVertexSet Y := by
      intro X Y hstep v hv
      rcases hstep.2.1 with ⟨_, hvertices, _⟩
      unfold TreeSequenceVertexSet at hv ⊢
      simp only [Finset.mem_image] at hv ⊢
      rcases hv with ⟨i, hi, rfl⟩
      refine ⟨Fin.castLE (Nat.succ_le_succ hstep.2.1.1) i, ?_, ?_⟩
      · exact Finset.mem_univ _
      · exact hvertices i
    have vertexInclusion : ∀ {X Y : TreeSequence G e0},
        TashkinovAugmentationSequence phi X Y →
        ∀ v, v ∈ TreeSequenceVertexSet X → v ∈ TreeSequenceVertexSet Y := by
      intro X Y hxy
      unfold TashkinovAugmentationSequence at hxy
      induction hxy using Relation.ReflTransGen.head_induction_on with
      | refl => intro v hv; exact hv
      | head hstep htail ih =>
        intro v hv
        rcases hstep with ⟨hlen, hsegment, c, hcolor, hmiss⟩
        exact ih v (vertexTransfer ⟨hlen, hsegment, c, hcolor, hmiss⟩ v hv)
    have segmentVertices : ∀ {X Y : TreeSequence G e0},
        TreeSequenceInitialSegment X Y →
        ∀ v, v ∈ TreeSequenceVertexSet X → v ∈ TreeSequenceVertexSet Y := by
      intro X Y hxy v hv
      rcases hxy with ⟨hbound, hvertices, hedges⟩
      unfold TreeSequenceVertexSet at hv ⊢
      simp only [Finset.mem_image] at hv ⊢
      rcases hv with ⟨i, hi, rfl⟩
      exact ⟨Fin.castLE (Nat.succ_le_succ hbound) i, Finset.mem_univ _,
        hvertices i⟩
    unfold TashkinovAugmentationSequence at hseq ⊢
    induction hseq using Relation.ReflTransGen.head_induction_on with
    | refl => exact Relation.ReflTransGen.refl
    | @head X Y hstep htail ih =>
      have htailVertex := vertexInclusion htail
      rcases hstep with ⟨hlen, hsegment, c, hcolor, hmiss⟩
      refine Relation.ReflTransGen.head ?_ ih
      refine ⟨hlen, hsegment, c, ?_, ?_⟩
      · let hlast : Fin Y.length := Fin.cast hlen.symm (Fin.last X.length)
        have hcolor' : phi (Y.edge hlast) = some c := by
          dsimp [hlast]
          exact hcolor
        have hinc : TreeIncidentEdge T (Y.edge hlast) := by
          rcases Y.attaches hlast with ⟨i, hi⟩
          refine ⟨Y.vertex hlast.succ, ?_, ?_⟩
          · apply htailVertex
            simp [TreeSequenceVertexSet]
          · change Y.vertex hlast.succ ∈ G.ends (Y.edge hlast)
            rw [hi]
            exact Sym2.mem_mk_left _ _
        have heq := hstab.1 _ hinc
          ⟨c, Finset.mem_union_left _ (by
            unfold TreeMissingColors at hmiss ⊢
            rcases Finset.mem_biUnion.mp hmiss with ⟨v, hv, hvc⟩
            have hvY : v ∈ TreeSequenceVertexSet Y :=
              segmentVertices hsegment v hv
            exact Finset.mem_biUnion.mpr ⟨v, htailVertex v hvY, hvc⟩), hcolor'⟩
        exact heq.trans hcolor'
      · unfold TreeMissingColors at hmiss ⊢
        rcases Finset.mem_biUnion.mp hmiss with ⟨v, hv, hvc⟩
        have hvY : v ∈ TreeSequenceVertexSet Y := segmentVertices hsegment v hv
        refine Finset.mem_biUnion.mpr ⟨v, hv, ?_⟩
        rw [hstab.2 v (htailVertex v hvY)]
        exact hvc
  have sequenceSegment : ∀ {A B : TreeSequence G e0},
      TashkinovAugmentationSequence phi A B →
      TreeSequenceInitialSegment A B := by
    intro A B hseq
    unfold TashkinovAugmentationSequence at hseq
    induction hseq using Relation.ReflTransGen.head_induction_on with
    | refl => exact ⟨le_rfl, by intro i; rfl, by intro i; rfl⟩
    | @head X Y hstep htail ih =>
      rcases hstep with ⟨hlen, hsegment, c, hcolor, hmiss⟩
      rcases ih with ⟨hfirst, hvfirst, hefirst⟩
      refine ⟨le_trans hsegment.1 hfirst, ?_, ?_⟩
      · intro i
        simpa using (hvfirst (Fin.castLE (m := Y.length + 1)
            (Nat.succ_le_succ hsegment.1) i)).trans
          (hsegment.2.1 i)
      · intro i
        simpa using (hefirst (Fin.castLE (m := Y.length) hsegment.1 i)).trans
          (hsegment.2.2 i)
  have eligible :
      (ett.series.data.kind (Fin.last ett.rounds) =
          some TashkinovExtensionKind.PE ∧
        TashkinovAugmentationSequence sigma
          (ett.series.data.tree (Fin.last ett.rounds).castSucc) T) ∨
      ((ett.series.data.kind (Fin.last ett.rounds) =
            some TashkinovExtensionKind.SE ∨
          ett.series.data.kind (Fin.last ett.rounds) =
            some TashkinovExtensionKind.RE) ∧
        ∃ f seed,
          ett.series.data.connectingEdges (Fin.last ett.rounds) = {f} ∧
            TreeSequenceAdjoinEdge
              (ett.series.data.tree (Fin.last ett.rounds).castSucc) f seed ∧
            TashkinovAugmentationSequence sigma seed T) := by
      have hstep := ett.series.certified (Fin.last ett.rounds)
      generalize hindex : Fin.last ett.rounds = index at hstep
      cases hstep with
    | initial triple seedLength initialColoring initialStored initialEdges
        initialKind initialVertex initialOutside initialDelta initialGamma initialClosure =>
        have hz : (Fin.last ett.rounds : Fin (ett.rounds + 1)) = 0 := hindex
        have hr : ett.rounds = 0 := by
          have := congrArg Fin.val hz
          simpa using this
        omega
      | SE i previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed noRevisiting choice seriesAlternative
        currentColoring currentStored currentEdges currentKind currentVertex
        currentOutside currentDelta currentGamma adjoined adjoinedExactly
        closedExtension orderedExtension strictExtension =>
        have hindex2 : (Fin.last (ett.rounds + 1) : Fin (ett.rounds + 1 + 1)) =
            i.succ.succ := by
          apply Fin.ext
          have hv := congrArg Fin.val hindex
          simp at hv ⊢
          omega
        right
        refine ⟨Or.inl currentKind, choice.edge, adjoined, currentEdges,
          adjoinedExactly, ?_⟩
        have hold : TashkinovAugmentationSequence phi adjoined
            (ett.series.data.tree i.succ.succ) := by
          simpa [← hindex, ett.generatingColoring] using closedExtension.1
        have hab : TreeSequenceInitialSegment adjoined T := by
          have ha := sequenceSegment hold
          have hc : TreeSequenceInitialSegment T
              (ett.series.data.tree i.succ.succ) := by
            have hh := ett.belowFinal
            rw [hindex2] at hh
            exact hh
          rcases adjoinedExactly with ⟨hlen, hinit, hedge⟩
          have hstrict := ett.strictAbovePenultimate
          have hstrict' :
              (ett.series.data.tree i.succ.castSucc).length < T.length := by
            have hi : i.succ.castSucc = (Fin.last ett.rounds).castSucc := by
              apply Fin.ext
              simp [hindex]
            rw [hi]
            have hj : (Fin.last ett.rounds).castSucc =
                (⟨ett.rounds, by omega⟩ : Fin (ett.rounds + 2)) := by
              apply Fin.ext
              rfl
            rw [hj]
            exact hstrict
          exact commonSegment hc ha (by
            rcases hsegOuter with ⟨hbound, _, _⟩
            omega)
        exact transportSequence (restrictSequence phi adjoined T
          (ett.series.data.tree i.succ.succ) hold hab (by
            have hh := ett.belowFinal
            rw [hindex2] at hh
            exact hh))
      | PE i previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed noRevisiting choice seriesAlternativeFails
        gamma gammaRule secondStable secondStableProper secondStableOneUncolored
        secondStableRelation exitWitness currentColoring currentProper
        currentOneUncolored currentStored currentEdges currentKind currentVertex
        currentOutside currentDelta currentGamma closedExtension orderedExtension strictExtension =>
        have hindex2 : (Fin.last (ett.rounds + 1) : Fin (ett.rounds + 1 + 1)) =
            i.succ.succ := by
          apply Fin.ext
          have hv := congrArg Fin.val hindex
          simp only [Fin.val_last, Fin.val_succ] at hv ⊢
          omega
        left
        refine ⟨currentKind, ?_⟩
        have hold : TashkinovAugmentationSequence phi
            (ett.series.data.tree i.succ.castSucc)
            (ett.series.data.tree i.succ.succ) := by
          simpa [← hindex, ett.generatingColoring] using closedExtension.1
        have hseg : TreeSequenceInitialSegment
            (ett.series.data.tree i.succ.castSucc) T := by
          have hh := hsegOuter
          rw [hindex] at hh
          exact hh
        have hfinal : TreeSequenceInitialSegment T
            (ett.series.data.tree i.succ.succ) := by
          have hh := ett.belowFinal
          rw [hindex2] at hh
          exact hh
        have hpart := restrictSequence phi
            (ett.series.data.tree i.succ.castSucc) T
            (ett.series.data.tree i.succ.succ) hold hseg hfinal
        exact transportSequence (by simpa [hindex] using hpart)
      | RE i previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed available currentColoring currentStored
        currentEdges currentKind currentVertex currentOutside currentDelta
        currentGamma adjoined adjoinedExactly closedExtension orderedExtension
        strictExtension =>
        have hindex2 : (Fin.last (ett.rounds + 1) : Fin (ett.rounds + 1 + 1)) =
            i.succ.succ := by
          apply Fin.ext
          have hv := congrArg Fin.val hindex
          simp only [Fin.val_last, Fin.val_succ] at hv ⊢
          omega
        right
        refine ⟨Or.inr currentKind, available.edge, adjoined, currentEdges,
          adjoinedExactly, ?_⟩
        have hold : TashkinovAugmentationSequence phi adjoined
            (ett.series.data.tree i.succ.succ) := by
          simpa [← hindex, ett.generatingColoring] using closedExtension.1
        have hab : TreeSequenceInitialSegment adjoined T := by
          have ha := sequenceSegment hold
          have hc : TreeSequenceInitialSegment T
              (ett.series.data.tree i.succ.succ) := by
            have hh := ett.belowFinal
            rw [hindex2] at hh
            exact hh
          rcases adjoinedExactly with ⟨hlen, hinit, hedge⟩
          have hstrict := ett.strictAbovePenultimate
          have hstrict' :
              (ett.series.data.tree i.succ.castSucc).length < T.length := by
            have hi : i.succ.castSucc = (Fin.last ett.rounds).castSucc := by
              apply Fin.ext
              simp [hindex]
            rw [hi]
            have hj : (Fin.last ett.rounds).castSucc =
                (⟨ett.rounds, by omega⟩ : Fin (ett.rounds + 2)) := by
              apply Fin.ext
              rfl
            rw [hj]
            exact hstrict
          exact commonSegment hc ha (by
            rcases hsegOuter with ⟨hbound, _, _⟩
            omega)
        exact transportSequence (restrictSequence phi adjoined T
          (ett.series.data.tree i.succ.succ) hold hab (by
            have hh := ett.belowFinal
            rw [hindex2] at hh
            exact hh))
  have hmod : ModColoring ett sigma := Td G k e0 input T phi ett hMP
    hpositive hlower sigma hsigma honeSigma hladder
  have hcand := hmod.2.2 T hsegOuter ett.strictAbovePenultimate eligible
  rcases hcand with ⟨corr⟩
  have hmax : MaximumProperty corr.replacementETT :=
    MaximumPropertyTransport G k e0 ett sigma hmod T corr hMP
  let replacementSeries : TashkinovSeries G k corr.replacementETT.rounds e0
      corr.replacementInput :=
    cast (congrArg (fun n => TashkinovSeries G k n e0 corr.replacementInput)
      corr.rungAgreement.symm) corr.replacementSeries
  have castStored {a b : ℕ} (h : a = b)
      (s : TashkinovSeries G k a e0 corr.replacementInput)
      (i : Fin (b + 1)) :
      (cast (congrArg (fun n => TashkinovSeries G k n e0 corr.replacementInput) h)
        s).data.stored i = s.data.stored (Fin.cast (congrArg (fun n => n + 1) h.symm) i) := by
    cases h
    rfl
  have castKind {a b : ℕ} (h : a = b)
      (s : TashkinovSeries G k a e0 corr.replacementInput)
      (i : Fin (b + 1)) :
      (cast (congrArg (fun n => TashkinovSeries G k n e0 corr.replacementInput) h)
        s).data.kind i = s.data.kind (Fin.cast (congrArg (fun n => n + 1) h.symm) i) := by
    cases h
    rfl
  have castTree {a b : ℕ} (h : a = b)
      (s : TashkinovSeries G k a e0 corr.replacementInput)
      (i : Fin (b + 2)) :
      (cast (congrArg (fun n => TashkinovSeries G k n e0 corr.replacementInput) h)
        s).data.tree i = s.data.tree (Fin.cast (congrArg (fun n => n + 2) h.symm) i) := by
    cases h
    rfl
  have hseries : corr.replacementETT.series = replacementSeries := by
    exact ((cast_eq_iff_heq
      (e := congrArg (fun n => TashkinovSeries G k n e0 corr.replacementInput)
        corr.rungAgreement.symm)
      (a := corr.replacementSeries) (a' := corr.replacementETT.series)).2
      corr.seriesPresentation.symm).symm
  let terminalIndex : Fin corr.replacementETT.rounds :=
    Fin.cast corr.rungAgreement.symm
      ⟨ett.rounds - 1, by have hp := ett.roundsPositive; omega⟩
  have htree : corr.replacementETT.series.data.tree terminalIndex.succ.castSucc =
      ett.series.data.tree (Fin.last ett.rounds).castSucc := by
    rw [hseries]
    calc
      replacementSeries.data.tree terminalIndex.succ.castSucc =
          corr.replacementSeries.data.tree
            (Fin.cast (congrArg (fun n => n + 2) corr.rungAgreement)
              terminalIndex.succ.castSucc) :=
        by simpa [replacementSeries] using
          (castTree corr.rungAgreement.symm corr.replacementSeries
            terminalIndex.succ.castSucc)
      _ = ett.series.data.tree (Fin.last ett.rounds).castSucc := by
        convert corr.ladderTreesAgree (Fin.cast corr.rungAgreement terminalIndex) using 1
        · congr 1
        · congr 1
          apply Fin.ext
          simp [terminalIndex]
          omega
  have hstored : ∀ i : Fin (corr.replacementETT.rounds + 1),
      corr.replacementETT.series.data.stored i = ett.series.data.stored
        (Fin.cast (congrArg (fun n => n + 1) corr.rungAgreement) i) := by
    intro i
    rw [hseries]
    exact (castStored corr.rungAgreement.symm corr.replacementSeries i).trans
      (corr.storedColorsAgree (Fin.cast (congrArg (fun n => n + 1)
        corr.rungAgreement) i))
  have hkindEq : ∀ i : Fin (corr.replacementETT.rounds + 1),
      corr.replacementETT.series.data.kind i = ett.series.data.kind
        (Fin.cast (congrArg (fun n => n + 1) corr.rungAgreement) i) := by
    intro i
    rw [hseries]
    exact (castKind corr.rungAgreement.symm corr.replacementSeries i).trans
      (corr.extensionKindsAgree (Fin.cast (congrArg (fun n => n + 1)
        corr.rungAgreement) i))
  have htreeFinal : corr.replacementETT.series.data.tree
      (Fin.last corr.replacementETT.rounds).castSucc =
      ett.series.data.tree (Fin.last ett.rounds).castSucc := by
    have hi : (Fin.last corr.replacementETT.rounds).castSucc =
        terminalIndex.succ.castSucc := by
      apply Fin.ext
      simp [terminalIndex]
      have hr : corr.replacementETT.rounds = ett.rounds := corr.rungAgreement
      omega
    rw [hi]
    exact htree
  have hgoodData : ∃ corrFinal : CorrespondingExtendedTashkinovTree G k e0 ett sigma T,
      ∃ hmaxFinal : MaximumProperty corrFinal.replacementETT,
      ∃ baseSigma : HierarchyBase corrFinal.replacementETT sigma,
      ∃ K : TashkinovHierarchy corrFinal.replacementETT baseSigma,
        ∃ goodSigma : GoodHierarchy K,
          SameGoodHierarchy good goodSigma := by
    by_cases hpe : ett.series.data.kind (Fin.last ett.rounds) =
        some TashkinovExtensionKind.PE
    · have hsplit := HierarchySplitter G k e0 input T phi sigma ett hMP
          hpositive hlower base H hpe hproper hone hsigma honeSigma
          (hcomb hpe) (by
            rcases eligible with h | h
            · exact h.2
            · rcases h.1 with hs | hr
              · exfalso
                rw [hpe] at hs
                cases hs
              · exfalso
                rw [hpe] at hr
                cases hr)
      rcases hsplit with ⟨corr', hmax', baseSigma, K, hsame⟩
      have hg : ∃ goodSigma : GoodHierarchy K,
          SameGoodHierarchy good goodSigma :=
        OutsideKempeGoodHierarchy G k e0 T phi sigma
          ett corr'.replacementETT base baseSigma H K hsame good
          hproper hone alpha beta hrecolor corr'.rungAgreement.symm
          (by
            intro i
            have hs : corr'.replacementETT.series =
                cast (congrArg (fun n => TashkinovSeries G k n e0
                  corr'.replacementInput) corr'.rungAgreement.symm)
                  corr'.replacementSeries := by
              exact ((cast_eq_iff_heq
                (e := congrArg (fun n => TashkinovSeries G k n e0
                  corr'.replacementInput) corr'.rungAgreement.symm)
                (a := corr'.replacementSeries)
                (a' := corr'.replacementETT.series)).2
                corr'.seriesPresentation.symm).symm
            rw [hs]
            have hc := corr'.storedColorsAgree i
            have castStep {a b : ℕ} (h : a = b)
                (s : TashkinovSeries G k a e0 corr'.replacementInput)
                (j : Fin (b + 1)) :
                (cast (congrArg (fun n => TashkinovSeries G k n e0
                  corr'.replacementInput) h) s).data.stored j =
                  s.data.stored (Fin.cast (congrArg (fun n => n + 1) h.symm) j) := by
              cases h
              rfl
            exact hc.symm.trans
              (castStep corr'.rungAgreement.symm corr'.replacementSeries
                (Fin.cast (congrArg (fun n => n + 1) corr'.rungAgreement.symm) i)).symm)
      rcases hg with ⟨goodSigma, hsg⟩
      exact ⟨corr', hmax', baseSigma, K, goodSigma, hsg⟩
    · let baseSigma : HierarchyBase corr.replacementETT sigma :=
        { core := base.core
          closure := base.closure
          supportPosition := Fin.cast (congrArg (fun X => X.length + 1)
            htreeFinal.symm) base.supportPosition
          supportPositive := base.supportPositive
          terminalMissingColors := by rfl
          parallel := by
            dsimp
            intro hp
            have hnot := hkindEq (Fin.last corr.replacementETT.rounds)
            have hk : corr.replacementETT.series.data.kind
                (Fin.last corr.replacementETT.rounds) =
                ett.series.data.kind (Fin.last ett.rounds) := by
              simpa [corr.rungAgreement] using hnot
            exfalso
            exact hpe (by simpa [hk] using hp)
          nonparallel := by
            dsimp
            intro hn
            have hc := base.nonparallel hpe
            simpa [htreeFinal] using hc }
      let K : TashkinovHierarchy corr.replacementETT baseSigma :=
        { dividerCount := H.dividerCount
          stage := H.stage
          baseStage := by simpa [htreeFinal] using H.baseStage
          terminalStage := H.terminalStage
          nested := H.nested
          strict := H.strict
          dividerPosition := H.dividerPosition
          dividerPositive := H.dividerPositive
          dividerIncreasing := H.dividerIncreasing
          dividerStage := H.dividerStage
          coreInsideFirst := by simpa [baseSigma] using H.coreInsideFirst }
      have hsame : SameHierarchyStages H K := by
        dsimp [SameHierarchyStages, K, baseSigma]
        refine ⟨rfl, rfl, heq_of_eq rfl, heq_of_eq rfl, ?_, ?_⟩
        · constructor <;> intro h
          · have hnot := hkindEq (Fin.last corr.replacementETT.rounds)
            have hk : corr.replacementETT.series.data.kind
                (Fin.last corr.replacementETT.rounds) =
                ett.series.data.kind (Fin.last ett.rounds) := by
              simpa [corr.rungAgreement] using hnot
            exact hk ▸ h
          · have hnot := hkindEq (Fin.last corr.replacementETT.rounds)
            have hk : corr.replacementETT.series.data.kind
                (Fin.last corr.replacementETT.rounds) =
                ett.series.data.kind (Fin.last ett.rounds) := by
              simpa [corr.rungAgreement] using hnot
            exact hk.symm ▸ h
        · intro hp
          exact False.elim (hpe hp)
      have hg := OutsideKempeGoodHierarchy G k e0 T phi sigma
          ett corr.replacementETT base baseSigma H K hsame good
          hproper hone alpha beta hrecolor corr.rungAgreement.symm (by
            intro i
            exact (hstored (Fin.cast (congrArg (fun n => n + 1)
              corr.rungAgreement.symm) i)).symm)
      rcases hg with ⟨goodSigma, hsg⟩
      exact ⟨corr, hmax, baseSigma, K, goodSigma, hsg⟩
  rcases hgoodData with ⟨corrFinal, hmaxFinal, baseSigma, K, goodSigma, hsg⟩
  refine ⟨hsigma, honeSigma, hstab, hinv, corrFinal, hmaxFinal, baseSigma, K,
    goodSigma, hsg, ?_⟩
  intro hclosed
  unfold TreeColorSetMinusClosed at hclosed ⊢
  have missingEq : TreeMissingColors phi T = TreeMissingColors sigma T := by
    ext c
    simp only [TreeMissingColors, Finset.mem_biUnion]
    constructor <;> rintro ⟨v, hv, hc⟩
    · exact ⟨v, hv, (Finset.ext_iff.mp (hstab.2 v hv) c).mpr hc⟩
    · exact ⟨v, hv, (Finset.ext_iff.mp (hstab.2 v hv) c).mp hc⟩
  rw [missingEq] at hclosed
  intro alpha ha
  have hc := hclosed alpha ha
  rw [Finset.eq_empty_iff_forall_notMem] at hc ⊢
  intro f hf
  simp only [BoundaryColorEdges, Finset.mem_filter] at hf
  have hbase : f ∈ BoundaryEdges G (TreeSequenceVertexSet T) := hf.1
  have hi : TreeIncidentEdge T f := by
    unfold BoundaryEdges at hbase
    simp only [Finset.mem_filter] at hbase
    rcases hbase with ⟨_, ⟨u, hu, v, hv, he⟩⟩
    refine ⟨u, hu, ?_⟩
    change u ∈ G.ends f
    rw [he]
    exact Sym2.mem_mk_left _ _
  have hphi : phi f = some alpha := by
    exact (hfixed f hi).symm ▸ hf.2
  apply hc f
  simp only [BoundaryColorEdges, Finset.mem_filter]
  exact ⟨hbase, hphi⟩
