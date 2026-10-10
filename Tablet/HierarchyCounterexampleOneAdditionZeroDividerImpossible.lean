import Tablet.ChangeLemma
import Tablet.ClosedSetTwoColorComponentAvoidance
import Tablet.CertifiedETTRestriction
import Tablet.ColoredVertexSetClosed
import Tablet.ColoredVertexSetElementary
import Tablet.CombinedStableColoring
import Tablet.CorrespondingExtendedTashkinovTree
import Tablet.ExtendedTashkinovTree
import Tablet.GoodHierarchy
import Tablet.HierarchyBase
import Tablet.HierarchyCounterexample
import Tablet.HierarchyCounterexampleLess
import Tablet.HierarchyCounterexampleMeasure
import Tablet.HierarchyLEMStable
import Tablet.HierarchyNonparallelFirstEdge
import Tablet.HierarchyStarredStage
import Tablet.HierarchyWeaklyStable
import Tablet.IsProperEdgeColoring
import Tablet.InterchangePECommonMissingClosed
import Tablet.MaximumDefectiveChoice
import Tablet.MaximumProperty
import Tablet.MissingColors
import Tablet.MissingColorIncidenceEndpoint
import Tablet.ModColoring
import Tablet.ParallelCommonMissingClosed
import Tablet.ParallelExtensionColor
import Tablet.RevisitingExtensionCertificate
import Tablet.StableChange
import Tablet.StableColoring
import Tablet.TashkinovAugmentation
import Tablet.TashkinovAugmentationSequence
import Tablet.TashkinovAugmentationSequenceInitialSegment
import Tablet.TashkinovAugmentationSequenceRestrict
import Tablet.TashkinovAugmentationSequenceSuffix
import Tablet.TashkinovClosure
import Tablet.TashkinovHierarchy
import Tablet.TashkinovSeries
import Tablet.TashkinovSeriesStep
import Tablet.TashkinovStoredColors
import Tablet.Td
import Tablet.TechnicalTheoremBase
import Tablet.TreeColorSetClosed
import Tablet.TreeInterchangeable
import Tablet.TreeMissingColors
import Tablet.TreeSequence
import Tablet.TreeSequenceAdjoinEdge
import Tablet.TreeSequenceInitialSegment
import Tablet.TreeSequenceInitialSegmentVertexSetSubset
import Tablet.TreeSequencePrefix
import Tablet.TreeSequenceVertexSet
import Tablet.TwoColorComponent
import Tablet.TwoColorComponentSpanningPath
import Tablet.TwoColorComponentSwap
import Tablet.TwoColorComponentSwapMissingBehavior
import Tablet.TwoColorComponentSwapProper
import Tablet.TwoColorCycle
import Tablet.TwoColorIncidenceDegreeAtMostTwo
import Tablet.TwoColorPathComponent
import Tablet.interchange

-- [TABLET NODE: HierarchyCounterexampleOneAdditionZeroDividerImpossible]
theorem HierarchyCounterexampleOneAdditionZeroDividerImpossible
    {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E]
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
      2 * ett.rounds + 11 ≤ (TreeMissingColors phi Tn).card)
    (honeAddition :
      let H := C.hierarchy
      let A := HierarchyStarredStage H (Fin.last H.dividerCount)
      T.length - A.length = 1)
    (hprefixElementary :
      let H := C.hierarchy
      let A := HierarchyStarredStage H (Fin.last H.dividerCount)
      let ell := T.length - A.length
      let Ty := TreeSequencePrefix T
        (min (A.length + (ell - 1)) T.length)
        (by have hA := A.positive; have hT := T.positive; omega)
        (Nat.min_le_right _ _)
      ColoredVertexSetElementary G phi (TreeSequenceVertexSet Ty))
    (hzero : C.hierarchy.dividerCount = 0) : False := by
-- BODY
  classical
  let H := C.hierarchy
  let A := base.core
  let n : Fin (ett.rounds + 1) := Fin.last ett.rounds
  let Tn := ett.series.data.tree n.castSucc
  let y := T.vertex (Fin.last T.length)
  have hstar : HierarchyStarredStage H (Fin.last H.dividerCount) = A := by
    have hz : Fin.last H.dividerCount = (0 : Fin (H.dividerCount + 1)) := by
      apply Fin.ext
      exact hzero
    rw [hz]
    rfl
  have hfirst : H.stage ⟨1, by omega⟩ = T := by
    have hi : (⟨1, by omega⟩ : Fin (H.dividerCount + 2)) =
        Fin.last (H.dividerCount + 1) := by
      apply Fin.ext
      simp only [Fin.val_last]
      change 1 = C.hierarchy.dividerCount + 1
      omega
    rw [hi]
    exact H.terminalStage
  have hAT : TreeSequenceInitialSegment A T := by
    simpa only [hfirst] using H.coreInsideFirst
  have hlen : T.length = A.length + 1 := by
    change T.length - (HierarchyStarredStage H (Fin.last H.dividerCount)).length = 1
      at honeAddition
    rw [hstar] at honeAddition
    have := hAT.1
    omega
  have prefixMem : ∀ {v : V}, v ∈ TreeSequenceVertexSet T →
      v ≠ y → v ∈ TreeSequenceVertexSet A := by
    intro v hv hne
    obtain ⟨i, -, hi⟩ := (@Finset.mem_image _ _ (Classical.decEq V)).mp hv
    have hival : i.val < T.length := by
      by_contra hn
      have hiLast : i = Fin.last T.length := by
        apply Fin.ext
        simp only [Fin.val_last]
        omega
      exact hne (hi.symm.trans (congrArg T.vertex hiLast))
    let j : Fin (A.length + 1) := ⟨i.val, by omega⟩
    have hji : Fin.castLE (Nat.succ_le_succ hAT.1) j = i := by
      apply Fin.ext
      rfl
    apply (@Finset.mem_image _ _ (Classical.decEq V)).mpr
    refine ⟨j, Finset.mem_univ _, ?_⟩
    exact (hAT.2.1 j).symm.trans (by simpa only [hji] using hi)
  have hyNot : y ∉ TreeSequenceVertexSet A := by
    intro hy
    obtain ⟨i, -, hi⟩ := (@Finset.mem_image _ _ (Classical.decEq V)).mp hy
    have hidx := T.vertex_injective ((hAT.2.1 i).trans hi)
    have hv := congrArg Fin.val hidx
    simp only [Fin.val_castLE, Fin.val_last] at hv
    have := i.isLt
    omega
  have hAElementary : ColoredVertexSetElementary G phi (TreeSequenceVertexSet A) := by
    let p := min (A.length + ((T.length - A.length) - 1)) T.length
    have hp : p = A.length := by dsimp [p]; omega
    let P := TreeSequencePrefix T p
      (by have := A.positive; dsimp [p]; omega) (Nat.min_le_right _ _)
    have hP : ColoredVertexSetElementary G phi (TreeSequenceVertexSet P) := by
      have hp := @hprefixElementary
      dsimp only at hp
      simp only [show HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount) = A
        from hstar] at hp
      exact @hp
    have hvertices : TreeSequenceVertexSet A ⊆ TreeSequenceVertexSet P := by
      intro v hv
      obtain ⟨i, -, hi⟩ := (@Finset.mem_image _ _ (Classical.decEq V)).mp hv
      let j : Fin (p + 1) := ⟨i.val, by rw [hp]; exact i.isLt⟩
      apply (@Finset.mem_image _ _ (Classical.decEq V)).mpr
      refine ⟨j, Finset.mem_univ _, ?_⟩
      change T.vertex (Fin.castLE _ j) = v
      have hji : Fin.castLE (Nat.succ_le_succ (Nat.min_le_right _ _)) j =
          Fin.castLE (Nat.succ_le_succ hAT.1) i := by
        apply Fin.ext
        rfl
      rw [hji]
      exact (hAT.2.1 i).trans hi
    intro u hu v hv huv
    exact hP (hvertices hu) (hvertices hv) huv
  obtain ⟨alpha, hAlphaA, hAlphaY⟩ : ∃ alpha : Fin k,
      alpha ∈ TreeMissingColors phi A ∧ alpha ∈ MissingColors G phi y := by
    by_contra hnone
    have hn : ∀ alpha, alpha ∈ TreeMissingColors phi A →
        alpha ∉ MissingColors G phi y := by
      intro alpha ha hy
      exact hnone ⟨alpha, ha, hy⟩
    apply C.notElementary
    intro u hu v hv huv
    by_cases huy : u = y
    · have hvA := prefixMem hv (by intro hvy; exact huv (huy.trans hvy.symm))
      apply Finset.disjoint_left.mpr
      intro alpha hau hav
      exact hn alpha (Finset.mem_biUnion.mpr ⟨v, hvA, hav⟩) (huy ▸ hau)
    · have huA := prefixMem hu huy
      by_cases hvy : v = y
      · apply Finset.disjoint_left.mpr
        intro alpha hau hav
        exact hn alpha (Finset.mem_biUnion.mpr ⟨u, huA, hau⟩) (hvy ▸ hav)
      · exact hAElementary huA (prefixMem hv hvy) huv
  have outsideEndpoint (f : E) (u v : V)
      (hu : u ∈ TreeSequenceVertexSet A) (hv : v ∉ TreeSequenceVertexSet A)
      (hends : G.ends f = Sym2.mk u v)
      (hf : T.edge ⟨A.length, by omega⟩ = f) : y = v := by
    obtain ⟨i, hi⟩ := T.attaches ⟨A.length, by omega⟩
    have hyIncident : Incident G y f := by
      unfold Incident
      rw [← hf, hi]
      have hlast : (⟨A.length, by omega⟩ : Fin T.length).succ =
          Fin.last T.length := by
        apply Fin.ext
        simp only [Fin.val_succ, Fin.val_last]
        omega
      simp only [hlast, y, Sym2.mem_iff, true_or]
    have hyCases : y = u ∨ y = v := by
      simpa only [Incident, hends, Sym2.mem_iff] using hyIncident
    exact hyCases.resolve_left (by intro hyu; exact hyNot (by simpa only [hyu] using hu))
  have commonPrefix {X Y Z : TreeSequence G e0}
      (hXZ : TreeSequenceInitialSegment X Z)
      (hYZ : TreeSequenceInitialSegment Y Z) (hXY : X.length ≤ Y.length) :
      TreeSequenceInitialSegment X Y := by
    refine ⟨hXY, ?_, ?_⟩
    · intro j
      have hx := hXZ.2.1 j
      have hy := hYZ.2.1 (Fin.castLE (Nat.succ_le_succ hXY) j)
      exact hy.symm.trans (by simpa only [Fin.castLE] using hx)
    · intro j
      have hx := hXZ.2.2 j
      have hy := hYZ.2.2 (Fin.castLE hXY j)
      exact hy.symm.trans (by simpa only [Fin.castLE] using hx)
  have equalTrees {X Y : TreeSequence G e0}
      (hXY : TreeSequenceInitialSegment X Y) (hl : X.length = Y.length) : X = Y := by
    cases X with
    | mk lx px vx ex vix eix fx ax =>
      cases Y with
      | mk ly py vy ey viy eiy fy ay =>
        simp only at hl
        subst ly
        rw [TreeSequence.mk.injEq]
        refine ⟨rfl, ?_, ?_⟩
        · apply heq_of_eq
          funext j
          simpa only [Fin.castLE] using (hXY.2.1 j).symm
        · apply heq_of_eq
          funext j
          simpa only [Fin.castLE] using (hXY.2.2 j).symm
  have leaf (psi : PartialEdgeColoring E k) (a b : Fin k)
      (hp : IsProperEdgeColoring G psi) (u : V)
      (hm : a ∈ MissingColors G psi u ∨ b ∈ MissingColors G psi u) :
      Set.Subsingleton ((TwoColorIncidenceGraph G psi a b).neighborSet (Sum.inl u)) := by
    by_cases hab : a = b
    · subst b
      have ha : a ∈ MissingColors G psi u := hm.elim id id
      have hn : a ∉ PresentColors G psi u := by simpa [MissingColors] using ha
      intro z hz w hw
      exfalso
      cases z with
      | inl z => simpa [TwoColorIncidenceGraph] using hz
      | inr f =>
        have hf : Incident G u f ∧ psi f = some a := by
          simpa [TwoColorIncidenceGraph] using hz
        exact hn (by simpa [PresentColors] using
          (show ∃ e, Incident G u e ∧ psi e = some a from ⟨f, hf⟩))
    · letI : Fintype ((TwoColorIncidenceGraph G psi a b).neighborSet (Sum.inl u)) :=
        Fintype.ofFinite _
      have hd : (TwoColorIncidenceGraph G psi a b).degree (Sum.inl u) ≤ 1 := by
        rcases hm with hm | hm
        · exact MissingColorIncidenceEndpoint G psi a b hab hp u hm
        · have hd := MissingColorIncidenceEndpoint G psi b a (Ne.symm hab) hp u hm
          have hgraph : TwoColorIncidenceGraph G psi b a = TwoColorIncidenceGraph G psi a b := by
            ext z w
            cases z <;> cases w <;> simp [TwoColorIncidenceGraph, or_comm]
          rw [hgraph] at hd
          exact hd
      rw [← SimpleGraph.card_neighborSet_eq_degree] at hd
      have hsub := Fintype.card_le_one_iff.mp hd
      intro z hz w hw
      exact congrArg Subtype.val (hsub ⟨z, hz⟩ ⟨w, hw⟩)
  have selfMem (psi : PartialEdgeColoring E k) (a b : Fin k) (u : V) :
      Sum.inl u ∈ TwoColorComponent G psi a b (Sum.inl u) :=
    SimpleGraph.ConnectedComponent.eq.mpr (SimpleGraph.Reachable.refl _)
  have cycleEndpoint (psi : PartialEdgeColoring E k) (a b : Fin k)
      (cycle : TwoColorCycle G psi a b) (f : E) (u v : V)
      (hends : G.ends f = Sym2.mk u v)
      (hf : Sum.inr f ∈ cycle.walk.support) :
      Sum.inl v ∈ cycle.walk.support := by
    let p := cycle.walk.rotate (Sum.inr f) hf
    have hp : p.IsCycle := cycle.isCycle.rotate hf
    have adjacent (z : Sum V E)
        (hz : (TwoColorIncidenceGraph G psi a b).Adj (Sum.inr f) z) :
        z = Sum.inl u ∨ z = Sum.inl v := by
      cases z with
      | inr e => exact hz.elim
      | inl w =>
        have hw : w = u ∨ w = v := by
          simpa only [Incident, hends, Sym2.mem_iff] using hz.1
        exact hw.elim (fun h => Or.inl (congrArg Sum.inl h))
          (fun h => Or.inr (congrArg Sum.inl h))
    have hs := adjacent p.snd (p.adj_snd hp.not_nil)
    have ht := adjacent p.penultimate (p.adj_penultimate hp.not_nil).symm
    by_contra hv
    have hsMem : p.snd ∈ cycle.walk.support := by
      apply (cycle.walk.mem_support_rotate_iff (Sum.inr f) hf).mp
      exact List.mem_of_mem_tail (p.snd_mem_tail_support hp.not_nil)
    have htMem : p.penultimate ∈ cycle.walk.support := by
      apply (cycle.walk.mem_support_rotate_iff (Sum.inr f) hf).mp
      exact List.mem_of_mem_dropLast (p.penultimate_mem_dropLast_support hp.not_nil)
    have hs' : p.snd = Sum.inl u := hs.resolve_right (by intro h; exact hv (h ▸ hsMem))
    have ht' : p.penultimate = Sum.inl u := ht.resolve_right (by intro h; exact hv (h ▸ htMem))
    exact hp.snd_ne_penultimate (hs'.trans ht'.symm)
  have cycleMissing (psi : PartialEdgeColoring E k) (a b : Fin k)
      (hp : IsProperEdgeColoring G psi) (cycle : TwoColorCycle G psi a b)
      (v : V) (hv : Sum.inl v ∈ cycle.walk.support)
      (hm : a ∈ MissingColors G psi v ∨ b ∈ MissingColors G psi v) : False := by
    let p := cycle.walk.rotate (Sum.inl v) hv
    have hcy : p.IsCycle := cycle.isCycle.rotate hv
    exact hcy.snd_ne_penultimate
      (leaf psi a b hp v hm (p.adj_snd hcy.not_nil)
        (p.adj_penultimate hcy.not_nil).symm)
  have outsideCommon (psi : PartialEdgeColoring E k) (a b : Fin k)
      (hab : a ≠ b) (hp : IsProperEdgeColoring G psi)
      (hi : TreeInterchangeable G A psi a b)
      (ha : a ∈ TreeMissingColors psi A) (hb : b ∈ TreeMissingColors psi A)
      (hym : a ∈ MissingColors G psi y ∨ b ∈ MissingColors G psi y) :
      ∀ v ∈ TreeSequenceVertexSet A,
        Sum.inl v ∉ TwoColorComponent G psi a b (Sum.inl y) := by
    let I := TwoColorIncidenceGraph G psi a b
    obtain ⟨u, hu, hum⟩ := Finset.mem_biUnion.mp ha
    obtain ⟨w, hw, hwm⟩ := Finset.mem_biUnion.mp hb
    have huPath : TwoColorPathComponent G psi a b (Sum.inl u) :=
      ⟨hab, Sum.inl u, selfMem psi a b u, leaf psi a b hp u (Or.inl hum)⟩
    have hwPath : TwoColorPathComponent G psi a b (Sum.inl w) :=
      ⟨hab, Sum.inl w, selfMem psi a b w, leaf psi a b hp w (Or.inr hwm)⟩
    have hyPath : TwoColorPathComponent G psi a b (Sum.inl y) :=
      ⟨hab, Sum.inl y, selfMem psi a b y, leaf psi a b hp y hym⟩
    have huw := hi _ _ huPath hwPath
      ⟨u, hu, selfMem psi a b u⟩ ⟨w, hw, selfMem psi a b w⟩
    intro v hv hvC
    have hyu := hi _ _ hyPath huPath ⟨v, hv, hvC⟩ ⟨u, hu, selfMem psi a b u⟩
    have hyC : Sum.inl y ∈ TwoColorComponent G psi a b (Sum.inl u) := by
      rw [← hyu]
      exact selfMem psi a b y
    by_cases heq : u = w
    · have hbU : b ∈ MissingColors G psi u := by simpa only [heq] using hwm
      have hempty : I.neighborSet (Sum.inl u) = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro z hz
        cases z with
        | inl z => simpa [I, TwoColorIncidenceGraph] using hz
        | inr e =>
          have he : Incident G u e ∧ (psi e = some a ∨ psi e = some b) := hz
          have hna : a ∉ PresentColors G psi u := by simpa [MissingColors] using hum
          have hnb : b ∉ PresentColors G psi u := by simpa [MissingColors] using hbU
          rcases he.2 with hec | hec
          · exact hna (by simpa [PresentColors] using
              (show ∃ e, Incident G u e ∧ psi e = some a from ⟨e, he.1, hec⟩))
          · exact hnb (by simpa [PresentColors] using
              (show ∃ e, Incident G u e ∧ psi e = some b from ⟨e, he.1, hec⟩))
      have hreach : I.Reachable (Sum.inl y) (Sum.inl u) :=
        SimpleGraph.ConnectedComponent.exact hyC
      exact SimpleGraph.not_reachable_of_neighborSet_right_eq_empty
        (by intro he; exact hyNot (by simpa only [Sum.inl.inj he] using hu)) hempty hreach
    · obtain ⟨s, t, p, hpPath, hsupp⟩ :=
        TwoColorComponentSpanningPath G psi a b hp (Sum.inl u)
      have endpoint (r : V)
          (hr : Sum.inl r ∈ TwoColorComponent G psi a b (Sum.inl u))
          (hm : a ∈ MissingColors G psi r ∨ b ∈ MissingColors G psi r) :
          Sum.inl r = s ∨ Sum.inl r = t := by
        have hrp : Sum.inl r ∈ p.support := by
          change Sum.inl r ∈ {x | x ∈ p.support}
          rw [hsupp]
          exact hr
        by_contra hn
        push_neg at hn
        exact (hpPath.isTrail.not_mem_support_of_subsingleton_neighborSet
          hn.1 hn.2 (leaf psi a b hp r hm)) hrp
      have huend := endpoint u (selfMem psi a b u) (Or.inl hum)
      have hwend := endpoint w (by rw [huw]; exact selfMem psi a b w) (Or.inr hwm)
      have hyend := endpoint y hyC hym
      have hyu : y ≠ u := by rintro rfl; exact hyNot hu
      have hyw : y ≠ w := by rintro rfl; exact hyNot hw
      rcases huend with hus | hut <;> rcases hwend with hws | hwt <;>
        rcases hyend with hys | hyt
      all_goals first
        | exact heq (Sum.inl.inj (hus.trans hws.symm))
        | exact heq (Sum.inl.inj (hut.trans hwt.symm))
        | exact hyu (Sum.inl.inj (hys.trans hus.symm))
        | exact hyu (Sum.inl.inj (hyt.trans hut.symm))
        | exact hyw (Sum.inl.inj (hys.trans hws.symm))
        | exact hyw (Sum.inl.inj (hyt.trans hwt.symm))
  have outsideSwap (a b : Fin k) (hab : a ≠ b)
      (havoid : ∀ v ∈ TreeSequenceVertexSet A,
        Sum.inl v ∉ TwoColorComponent G phi a b (Sum.inl y)) :
      let sigma := TwoColorComponentSwap G phi a b (Sum.inl y)
      IsProperEdgeColoring G sigma ∧ IsOneEdgeUncolored sigma e0 ∧
        (∀ f, TreeIncidentEdge A f → sigma f = phi f) ∧
        (∀ v ∈ TreeSequenceVertexSet A,
          MissingColors G sigma v = MissingColors G phi v) := by
    dsimp only
    have hfixed (f : E) (hf : TreeIncidentEdge A f) :
        TwoColorComponentSwap G phi a b (Sum.inl y) f = phi f := by
      obtain ⟨v, hv, hvf⟩ := hf
      by_cases he : Sum.inr f ∈ TwoColorComponent G phi a b (Sum.inl y)
      · by_cases hc : phi f = some a ∨ phi f = some b
        · have hadj : (TwoColorIncidenceGraph G phi a b).Adj (Sum.inl v) (Sum.inr f) :=
            ⟨hvf, hc⟩
          have hc' := SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj
          have hvC : Sum.inl v ∈ TwoColorComponent G phi a b (Sum.inl y) :=
            hc'.trans he
          exact (havoid v hv hvC).elim
        · simp only [not_or] at hc
          simp [TwoColorComponentSwap, he, hc.1, hc.2]
      · simp [TwoColorComponentSwap, he]
    refine ⟨TwoColorComponentSwapProper G phi a b hab hproper (Sum.inl y), ?_,
      hfixed, ?_⟩
    · have hnone (f : E) : TwoColorComponentSwap G phi a b (Sum.inl y) f = none ↔ phi f = none := by
        by_cases hc : Sum.inr f ∈ TwoColorComponent G phi a b (Sum.inl y)
        · by_cases ha : phi f = some a
          · simp [TwoColorComponentSwap, hc, ha]
          · by_cases hb : phi f = some b
            · simp [TwoColorComponentSwap, hc, ha, hb, Ne.symm hab]
            · simp [TwoColorComponentSwap, hc, ha, hb]
        · simp [TwoColorComponentSwap, hc]
      constructor
      · exact (hnone e0).mpr hone.1
      · intro f hfe
        obtain ⟨c, hc⟩ := hone.2 f hfe
        cases hs : TwoColorComponentSwap G phi a b (Sum.inl y) f with
        | none =>
          exfalso
          have hn : phi f ≠ none := by rw [hc]; simp
          exact hn ((hnone f).mp hs)
        | some d => exact ⟨d, rfl⟩
    · intro v hv
      exact (TwoColorComponentSwapMissingBehavior G phi a b hab hproper (Sum.inl y)).1
        v (havoid v hv)
  have hnPositive : 0 < n.val := C.positive
  have cert := ett.series.certified n
  generalize hslot : n = slot at cert
  cases cert with
  | initial triple seedLength initialColoring initialStored initialEdges
      initialKind initialVertex initialOutside initialDelta initialGamma initialClosure =>
    have hv := congrArg Fin.val hslot
    simp only [Fin.val_zero] at hv
    omega
  | SE i previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternative
      currentColoring currentStored currentEdges currentKind currentVertex
      currentOutside currentDelta currentGamma adjoined adjoinedExactly
      closedExtension orderedExtension strictExtension =>
    have hkind : ett.series.data.kind n = some TashkinovExtensionKind.SE := by
      rw [hslot]
      exact currentKind
    have hcore : A = Tn := base.nonparallel (by rw [hkind]; decide)
    have hphi : phi = choice.selected := ett.generatingColoring.trans
      (by change ett.series.data.coloring n = choice.selected
          rw [hslot]; exact currentColoring)
    have hedges : ett.series.data.connectingEdges n = {choice.edge} := by
      rw [hslot]
      exact currentEdges
    obtain ⟨r, hr, hedge⟩ := HierarchyNonparallelFirstEdge H choice.edge
      (Or.inl hkind) hedges
    have hedgeT : T.edge ⟨A.length, by omega⟩ = choice.edge := by
      have hcore' : A = ett.series.data.tree (Fin.last ett.rounds).castSucc := hcore
      have hr' : r.val = A.length := by simpa only [← hcore'] using hr
      have hentry : ∃ s : Fin T.length, s.val = A.length ∧ T.edge s = choice.edge := by
        have hh : ∃ s : Fin (H.stage ⟨1, by omega⟩).length, s.val = A.length ∧
            (H.stage ⟨1, by omega⟩).edge s = choice.edge := ⟨r, hr', hedge⟩
        rw [hfirst] at hh
        exact hh
      obtain ⟨s, hs, he⟩ := hentry
      have hs' : s = ⟨A.length, by omega⟩ := Fin.ext hs
      simpa only [hs'] using he
    have htree : A = ett.series.data.tree i.succ.castSucc := by
      simpa only [Tn, hslot] using hcore
    have hy : y = choice.otherEndpoint := outsideEndpoint choice.edge
      choice.vertex choice.otherEndpoint
      (by rw [htree]; exact choice.vertexDefective.1)
      (by rw [htree]; exact choice.otherOutside) choice.edgeEnds hedgeT
    have hstable : StableColoring (ett.series.data.tree i.succ.castSucc)
        (insert choice.color (TashkinovStoredColors ett.series.data i.castSucc))
        choice.selected phi := by
      exact ⟨fun f _ _ => congrArg (fun psi => psi f) hphi,
        fun v _ => congrArg (fun psi => MissingColors G psi v) hphi⟩
    have hdisjoint := seriesAlternative phi hproper hone hstable
    exact Finset.disjoint_left.mp hdisjoint
      (by simpa only [hy] using hAlphaY) (by simpa only [htree] using hAlphaA)
  | RE i previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed available currentColoring currentStored
      currentEdges currentKind currentVertex currentOutside currentDelta
      currentGamma adjoined adjoinedExactly closedExtension orderedExtension strictExtension =>
    have hRE : ett.series.data.kind n = some TashkinovExtensionKind.RE := by
      rw [hslot]
      exact currentKind
    have hcore : A = Tn := base.nonparallel (by rw [hRE]; decide)
    have hphi : phi = ett.series.data.coloring i.castSucc :=
      ett.generatingColoring.trans (by
        change ett.series.data.coloring n = ett.series.data.coloring i.castSucc
        rw [hslot]; exact currentColoring)
    have htree : A = ett.series.data.tree i.succ.castSucc := by
      simpa only [Tn, hslot] using hcore
    have hedges : ett.series.data.connectingEdges n = {available.edge} := by
      rw [hslot]
      exact currentEdges
    obtain ⟨r, hr, hedge⟩ := HierarchyNonparallelFirstEdge H available.edge
      (Or.inr hRE) hedges
    have hedgeT : T.edge ⟨A.length, by omega⟩ = available.edge := by
      have hcore' : A = ett.series.data.tree (Fin.last ett.rounds).castSucc := hcore
      have hr' : r.val = A.length := by simpa only [← hcore'] using hr
      obtain ⟨s, hs, he⟩ : ∃ s : Fin T.length,
          s.val = A.length ∧ T.edge s = available.edge := by
        have hh : ∃ s : Fin (H.stage ⟨1, by omega⟩).length, s.val = A.length ∧
            (H.stage ⟨1, by omega⟩).edge s = available.edge := ⟨r, hr', hedge⟩
        rw [hfirst] at hh
        exact hh
      simpa only [show s = ⟨A.length, by omega⟩ from Fin.ext hs] using he
    have hy : y = available.outsideEndpoint := outsideEndpoint available.edge
      available.insideEndpoint available.outsideEndpoint
      (by rw [htree]; exact available.insideInCurrent)
      (by rw [htree]; exact available.outsideNotCurrent) available.edgeEnds hedgeT
    have hstart : available.delta ∈ TreeMissingColors
        (ett.series.data.coloring available.earlier)
        (ett.series.data.tree available.earlier.succ) := by
      have hkind := available.earlierPE
      have hd := available.earlierDelta
      have certH := ett.series.certified available.earlier
      generalize hh : available.earlier = h at certH
      cases certH with
      | initial triple seedLength initialColoring initialStored initialEdges
          initialKind initialVertex initialOutside initialDelta initialGamma initialClosure =>
        rw [hh, initialKind] at hkind
        simp at hkind
      | SE j pp po pc pn nr choice alt cc cs ce ck cv co cd cg ad ae cl oe st =>
        rw [hh, ck] at hkind
        simp at hkind
      | RE j pp po pc pn av cc cs ce ck cv co cd cg ad ae cl oe st =>
        rw [hh, ck] at hkind
        simp at hkind
      | PE j pp po pc pn nr choice alt gamma gr second sp so sr ew
          cc cp cu cs ce ck cv co cd cg cl oe st =>
        have hdelta : choice.color = available.delta := by
          rw [hh, cd] at hd
          exact Option.some.inj hd
        have hgammaMissing : gamma ∈ MissingColors G second choice.vertex := by
          rw [sr.2 choice.vertex choice.vertexDefective.1]
          exact gr.1
        have hchoiceColor : second choice.edge = some choice.color :=
          (sr.1 choice.edge ⟨choice.vertex, choice.vertexDefective.1, choice.edgeIncident⟩
            ⟨choice.color, Finset.mem_union_right _ (Finset.mem_insert_self _ _),
              choice.edgeColor⟩).trans choice.edgeColor
        have hne : gamma ≠ choice.color := by
          intro heq
          have hn : gamma ∉ PresentColors G second choice.vertex := by
            simpa [MissingColors] using hgammaMissing
          exact hn (by simp [PresentColors]; exact
            ⟨choice.edge, choice.edgeIncident, by simpa only [heq] using hchoiceColor⟩)
        have hm := (TwoColorComponentSwapMissingBehavior G second gamma choice.color hne sp
          (Sum.inl choice.vertex)).2.1 choice.vertex (selfMem second gamma choice.color choice.vertex)
            hgammaMissing
        rw [cc]
        apply Finset.mem_biUnion.mpr
        refine ⟨choice.vertex, TreeSequenceInitialSegmentVertexSetSubset oe
          choice.vertexDefective.1, ?_⟩
        simpa only [hdelta] using hm
    have transport : ∀ m : ℕ, available.earlier.val ≤ m → m ≤ i.val →
        ∀ j : Fin (ett.rounds + 1), j.val = m →
          available.delta ∈ TreeMissingColors (ett.series.data.coloring j)
            (ett.series.data.tree j.succ) := by
      intro m hm
      induction m, hm using Nat.le_induction with
      | base =>
        intro hmi j hj
        have heq : j = available.earlier := Fin.ext hj
        simpa only [heq] using hstart
      | succ m hm ih =>
        intro hmi j hj
        let p : Fin (ett.rounds + 1) := ⟨m, by have := i.isLt; omega⟩
        have hprev := ih (by omega) p rfl
        have hjkind := available.interveningRevisiting j (by omega) (by omega) (by
          change j.val ≤ i.val
          omega)
        have certJ := ett.series.certified j
        generalize hjSlot : j = js at certJ
        cases certJ with
        | initial triple seedLength initialColoring initialStored initialEdges
            initialKind initialVertex initialOutside initialDelta initialGamma initialClosure =>
          rw [hjSlot, initialKind] at hjkind
          simp at hjkind
        | SE q pp po pc pn nr choice alt cc cs ce ck cv co cd cg ad ae cl oe st =>
          rw [hjSlot, ck] at hjkind
          simp at hjkind
        | PE q pp po pc pn nr choice alt gamma gr second sp so sr ew
            cc cp cu cs ce ck cv co cd cg cl oe st =>
          rw [hjSlot, ck] at hjkind
          simp at hjkind
        | RE q pp po pc pn av cc cs ce ck cv co cd cg ad ae cl oe st =>
          have hqp : q.castSucc = p := by
            apply Fin.ext
            have hh := congrArg Fin.val hjSlot
            simp only [Fin.val_succ] at hh
            dsimp [p]
            omega
          have hqpTree : p.succ = q.succ.castSucc := by
            apply Fin.ext
            have := congrArg Fin.val hqp
            simp only [Fin.val_succ, Fin.val_castSucc] at this ⊢
            omega
          rw [cc]
          obtain ⟨v, hv, hvm⟩ := Finset.mem_biUnion.mp hprev
          apply Finset.mem_biUnion.mpr
          refine ⟨v, TreeSequenceInitialSegmentVertexSetSubset oe
            (by simpa only [hqpTree] using hv), ?_⟩
          simpa only [hqp] using hvm
    have hDeltaA : available.delta ∈ TreeMissingColors phi A := by
      have hm := transport i.val available.earlierAtMost (le_rfl) i.castSucc rfl
      have hiTree : i.castSucc.succ = i.succ.castSucc := by apply Fin.ext; rfl
      simpa only [hphi, htree, hiTree] using hm
    have hcycleY : Sum.inl y ∈ available.cycle.walk.support := by
      have hy' := cycleEndpoint (ett.series.data.coloring i.castSucc)
        available.gamma available.delta available.cycle available.edge
        available.insideEndpoint available.outsideEndpoint available.edgeEnds
        available.edgeOnCycle
      simpa only [hy] using hy'
    by_cases hda : available.delta = alpha
    · exact cycleMissing (ett.series.data.coloring i.castSucc)
        available.gamma available.delta previousProper available.cycle y hcycleY
        (Or.inr (by simpa only [hda, hphi] using hAlphaY))
    have hclosed : ColoredVertexSetClosed G phi (TreeSequenceVertexSet A) := by
      intro f c v hf hv hfc hm
      have hf' : f ∈ BoundaryEdges G
          (TreeSequenceVertexSet (ett.series.data.tree i.succ.castSucc)) := by
        simpa only [htree] using hf
      have hv' : v ∈ TreeSequenceVertexSet (ett.series.data.tree i.succ.castSucc) := by
        simpa only [htree] using hv
      exact previousClosed hf' hv' (by simpa only [hphi] using hfc)
        (by simpa only [hphi] using hm)
    obtain ⟨u, hu, huDelta⟩ := Finset.mem_biUnion.mp hDeltaA
    obtain ⟨v, hv, hvAlpha⟩ := Finset.mem_biUnion.mp hAlphaA
    have havoid := (ClosedSetTwoColorComponentAvoidance G phi available.delta alpha
      (TreeSequenceVertexSet A) y u v hclosed hyNot hu hv huDelta hvAlpha).1
    let sigma := TwoColorComponentSwap G phi available.delta alpha (Sum.inl y)
    obtain ⟨hsigmaProper, hsigmaOne, hfixed, hmissing⟩ := outsideSwap available.delta alpha hda havoid
    have hDeltaY : available.delta ∈ MissingColors G sigma y :=
      (TwoColorComponentSwapMissingBehavior G phi available.delta alpha hda hproper
        (Sum.inl y)).2.2.1 y (selfMem phi available.delta alpha y) hAlphaY
    have hsigmaStable : StableColoring Tn (TashkinovStoredColors ett.series.data n)
        phi sigma := by
      rw [← hcore]
      exact ⟨fun f hf hc => hfixed f hf, hmissing⟩
    have hmod := Td G k e0 input T phi ett C.maximum C.positive hlower sigma
      hsigmaProper hsigmaOne (by simpa only [← ett.generatingColoring] using hsigmaStable)
    have hadjoinedFinal := TashkinovAugmentationSequenceInitialSegment
      (ett.series.data.coloring i.succ) _ _ closedExtension.1
    have hfinal : i.succ.succ = Fin.last (ett.rounds + 1) := by
      apply Fin.ext
      have hh := congrArg Fin.val hslot
      simp only [n, Fin.val_last, Fin.val_succ] at hh ⊢
      omega
    rw [hfinal] at hadjoinedFinal
    have hadjoinedLen : adjoined.length = T.length := by
      have := adjoinedExactly.1
      rw [← htree] at this
      omega
    have hadjoinedT : adjoined = T := equalTrees
      (commonPrefix hadjoinedFinal ett.belowFinal (by omega)) hadjoinedLen
    have hseed : TreeSequenceAdjoinEdge Tn available.edge T := by
      simpa only [Tn, hslot, hadjoinedT] using adjoinedExactly
    obtain ⟨corr⟩ := hmod.2.2 T (by
        change TreeSequenceInitialSegment Tn T
        rw [← hcore]; exact hAT)
      (by change Tn.length < T.length; rw [← hcore]; omega)
      (Or.inr ⟨Or.inr hRE, available.edge, T, hedges, hseed, Relation.ReflTransGen.refl⟩)
    have hRepKind := (corr.extensionKindsAgree n).trans hRE
    have hRepEdges := (corr.connectingEdgesAgree n).trans hedges
    have hRepDelta : available.delta ∈ corr.replacementSeries.data.stored n := by
      rw [corr.storedColorsAgree, hslot, currentStored]
      simp
    have repCert := corr.replacementSeries.certified n
    generalize hRepSlot : n = repSlot at repCert
    cases repCert with
    | initial triple seedLength initialColoring initialStored initialEdges
        initialKind initialVertex initialOutside initialDelta initialGamma initialClosure =>
      rw [hRepSlot, initialKind] at hRepKind
      simp at hRepKind
    | SE q pp po pc pn nr choice alt cc cs ce ck cv co cd cg ad ae cl oe st =>
      rw [hRepSlot, ck] at hRepKind
      simp at hRepKind
    | PE q pp po pc pn nr choice alt gamma gr second sp so sr ew
        cc cp cu cs ce ck cv co cd cg cl oe st =>
      rw [hRepSlot, ck] at hRepKind
      simp at hRepKind
    | RE q pp po pc pn av cc cs ce ck cv co cd cg ad ae cl oe st =>
      have hf : av.edge = available.edge := by
        have hh : av.edge ∈ corr.replacementSeries.data.connectingEdges n := by
          rw [hRepSlot, ce]
          simp
        rw [hRepEdges] at hh
        exact Finset.mem_singleton.mp hh
      have hcolor : sigma = corr.replacementSeries.data.coloring q.castSucc :=
        corr.finalGeneratingColoring.trans (by
          change corr.replacementSeries.data.coloring n =
            corr.replacementSeries.data.coloring q.castSucc
          rw [hRepSlot]; exact cc)
      have hcyEdge : Sum.inr available.edge ∈ av.cycle.walk.support := by
        simpa only [hf] using av.edgeOnCycle
      have hcyY : Sum.inl y ∈ av.cycle.walk.support := by
        have hh := cycleEndpoint (corr.replacementSeries.data.coloring q.castSucc)
          av.gamma av.delta av.cycle available.edge
          available.insideEndpoint available.outsideEndpoint available.edgeEnds hcyEdge
        simpa only [hy] using hh
      rw [hRepSlot, cs] at hRepDelta
      have hpair : available.delta = av.delta ∨ available.delta = av.gamma := by
        simpa only [Finset.mem_insert, Finset.mem_singleton] using hRepDelta
      apply cycleMissing (corr.replacementSeries.data.coloring q.castSucc)
        av.gamma av.delta pp av.cycle y hcyY
      rcases hpair with hd | hg
      · exact Or.inr (by simpa only [← hd, hcolor] using hDeltaY)
      · exact Or.inl (by simpa only [← hg, hcolor] using hDeltaY)
  | PE i previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternativeFails
      gamma gammaRule secondStable secondStableProper secondStableOneUncolored
      secondStableRelation exitWitness currentColoring currentProper
      currentOneUncolored currentStored currentEdges currentKind currentVertex
      currentOutside currentDelta currentGamma closedExtension orderedExtension strictExtension =>
    have hPE : ett.series.data.kind n = some TashkinovExtensionKind.PE := by
      rw [hslot]
      exact currentKind
    obtain ⟨union⟩ := (base.parallel hPE).2.2
    have hTnA : TreeSequenceInitialSegment Tn A := union.leftSegment
    have hTnFinal : TashkinovAugmentationSequence phi Tn
        (ett.series.data.tree (Fin.last (ett.rounds + 1))) := by
      have hphi : phi = ett.series.data.coloring i.succ := by
        simpa only [n, hslot] using ett.generatingColoring
      have hfinal : i.succ.succ = Fin.last (ett.rounds + 1) := by
        apply Fin.ext
        have hh := congrArg Fin.val hslot
        simp only [n, Fin.val_last, Fin.val_succ] at hh ⊢
        omega
      simpa only [Tn, hslot, hfinal, ← hphi] using closedExtension.1
    have hTnT : TreeSequenceInitialSegment Tn T :=
      commonPrefix (TashkinovAugmentationSequenceInitialSegment phi _ _ hTnFinal)
        ett.belowFinal (le_trans hTnA.1 hAT.1)
    have hrouteT : TashkinovAugmentationSequence phi Tn T :=
      TashkinovAugmentationSequenceRestrict phi _ _ _ hTnFinal hTnT ett.belowFinal
    have hrouteA : TashkinovAugmentationSequence phi A T :=
      TashkinovAugmentationSequenceSuffix phi _ _ _ hrouteT hTnA hAT
    have hstep : TashkinovAugmentation phi A T := by
      have oneStep (X : TreeSequence G e0) (hXT : TashkinovAugmentationSequence phi X T) :
          T.length = X.length + 1 → TashkinovAugmentation phi X T := by
        unfold TashkinovAugmentationSequence at hXT
        induction hXT using Relation.ReflTransGen.head_induction_on with
        | refl => intro h; omega
        | @head X B hXB hBT ih =>
          intro h
          have hBTseg := TashkinovAugmentationSequenceInitialSegment phi B T hBT
          have hBlen : B.length = T.length := by
            have := hXB.1
            have := hBTseg.1
            omega
          have hB := equalTrees hBTseg hBlen
          subst B
          exact hXB
      exact oneStep A hrouteA hlen
    obtain ⟨hstepLen, hstepSegment, beta, hBetaEdge, hBetaA⟩ := hstep
    let f := T.edge ⟨A.length, by omega⟩
    have hBetaF : phi f = some beta := by
      convert hBetaEdge using 2
      apply congrArg T.edge
      apply Fin.ext
      rfl
    have hfy : Incident G y f := by
      obtain ⟨j, hj⟩ := T.attaches ⟨A.length, by omega⟩
      change y ∈ G.ends f
      rw [hj]
      have hi : (⟨A.length, by omega⟩ : Fin T.length).succ = Fin.last T.length := by
        apply Fin.ext
        simp only [Fin.val_succ, Fin.val_last]
        omega
      simp [hi, y]
    have hAlphaBeta : alpha ≠ beta := by
      intro heq
      have hn : alpha ∉ PresentColors G phi y := by simpa [MissingColors] using hAlphaY
      exact hn (by simp [PresentColors]; exact ⟨f, hfy, by simpa only [heq] using hBetaF⟩)
    let M := ((TreeMissingColors phi Tn ∩ TreeMissingColors phi base.closure) \
      (HierarchyStoredColorsAt H 0).biUnion (C.good.gamma 0))
    have hMcard : 4 ≤ M.card := (C.good.parallelBase hPE).2
    obtain ⟨theta, htM, htAvoid⟩ : ∃ theta ∈ M, theta ∉ ({alpha, beta} : Finset (Fin k)) := by
      apply Finset.exists_mem_notMem_of_card_lt_card
      have habcard : ({alpha, beta} : Finset (Fin k)).card ≤ 2 := by
        calc
          ({alpha, beta} : Finset (Fin k)).card ≤ ({beta} : Finset (Fin k)).card + 1 :=
            Finset.card_insert_le _ _
          _ = 2 := by simp
      omega
    have hThetaAlpha : theta ≠ alpha := by intro he; exact htAvoid (by simp [he])
    have hThetaBeta : theta ≠ beta := by intro he; exact htAvoid (by simp [he])
    have hThetaTn : theta ∈ TreeMissingColors phi Tn :=
      (Finset.mem_inter.mp (Finset.mem_sdiff.mp htM).1).1
    have hThetaR : theta ∈ TreeMissingColors phi base.closure :=
      (Finset.mem_inter.mp (Finset.mem_sdiff.mp htM).1).2
    have hThetaA : theta ∈ TreeMissingColors phi A := by
      obtain ⟨u, hu, hum⟩ := Finset.mem_biUnion.mp hThetaTn
      exact Finset.mem_biUnion.mpr
        ⟨u, TreeSequenceInitialSegmentVertexSetSubset hTnA hu, hum⟩
    have hstablePhi : CombinedStableColoring Tn base.closure
        (TashkinovStoredColors ett.series.data n) phi phi :=
      ⟨⟨fun _ _ _ => rfl, fun _ _ => rfl⟩,
        ⟨fun _ _ _ => rfl, fun _ _ => rfl⟩⟩
    have hThetaClosed := InterchangePECommonMissingClosed G k e0 input T phi phi
      ett C.maximum C.positive hlower hPE base hproper hone hstablePhi theta hThetaTn hThetaR
    have hInter := (interchange G k e0 input T phi phi ett C.maximum C.positive
      hlower hPE base hproper hone hstablePhi theta alpha).2.2.1 hThetaA hThetaClosed
    have havoid := outsideCommon phi theta alpha hThetaAlpha hproper
      hInter hThetaA hAlphaA (Or.inr hAlphaY)
    let sigma := TwoColorComponentSwap G phi theta alpha (Sum.inl y)
    obtain ⟨hsigmaProper, hsigmaOne, hfixed, hmissing⟩ :=
      outsideSwap theta alpha hThetaAlpha havoid
    have hThetaY : theta ∈ MissingColors G sigma y :=
      (TwoColorComponentSwapMissingBehavior G phi theta alpha hThetaAlpha
        hproper (Sum.inl y)).2.2.1 y (selfMem phi theta alpha y) hAlphaY
    have hmissingA : TreeMissingColors sigma A = TreeMissingColors phi A := by
      unfold TreeMissingColors
      apply Finset.biUnion_congr rfl
      intro v hv
      exact hmissing v hv
    have hRsub : TreeSequenceVertexSet base.closure ⊆ TreeSequenceVertexSet A := by
      rw [union.vertexSet]
      exact Finset.subset_union_right
    have stableOn (X : TreeSequence G e0) (D : Finset (Fin k))
        (hX : TreeSequenceVertexSet X ⊆ TreeSequenceVertexSet A) :
        StableColoring X D phi sigma := by
      constructor
      · intro e he hc
        obtain ⟨v, hv, hve⟩ := he
        exact hfixed e ⟨v, hX hv, hve⟩
      · intro v hv
        exact hmissing v (hX hv)
    have hsigmaStable : CombinedStableColoring Tn base.closure
        (TashkinovStoredColors ett.series.data n) phi sigma :=
      ⟨stableOn Tn _ (TreeSequenceInitialSegmentVertexSetSubset hTnA),
        stableOn base.closure ∅ hRsub⟩
    have hThetaTnSigma : theta ∈ TreeMissingColors sigma Tn := by
      obtain ⟨u, hu, hum⟩ := Finset.mem_biUnion.mp hThetaTn
      exact Finset.mem_biUnion.mpr ⟨u, hu, by
        rw [hsigmaStable.1.2 u hu]; exact hum⟩
    have hThetaRSigma : theta ∈ TreeMissingColors sigma base.closure := by
      obtain ⟨u, hu, hum⟩ := Finset.mem_biUnion.mp hThetaR
      exact Finset.mem_biUnion.mpr ⟨u, hu, by
        rw [hsigmaStable.2.2 u hu]; exact hum⟩
    have hThetaClosedSigma := InterchangePECommonMissingClosed G k e0 input T phi sigma
      ett C.maximum C.positive hlower hPE base hsigmaProper hsigmaOne hsigmaStable
      theta hThetaTnSigma hThetaRSigma
    have hThetaASigma : theta ∈ TreeMissingColors sigma A := by rwa [hmissingA]
    have hBetaASigma : beta ∈ TreeMissingColors sigma A := by rwa [hmissingA]
    have hInterSigma := (interchange G k e0 input T phi sigma ett C.maximum C.positive
      hlower hPE base hsigmaProper hsigmaOne hsigmaStable theta beta).2.2.1
      hThetaASigma hThetaClosedSigma
    have havoidSigma := outsideCommon sigma theta beta hThetaBeta hsigmaProper
      hInterSigma hThetaASigma hBetaASigma (Or.inl hThetaY)
    obtain ⟨j, hj⟩ := T.attaches ⟨A.length, by omega⟩
    let u := T.vertex (Fin.castLT j (Nat.lt_trans j.isLt
      (Nat.succ_lt_succ (show A.length < T.length by omega))))
    have huA : u ∈ TreeSequenceVertexSet A := by
      apply prefixMem
      · exact (@Finset.mem_image _ _ (Classical.decEq V)).mpr ⟨_, Finset.mem_univ _, rfl⟩
      · intro huy
        have hidx := congrArg Fin.val (T.vertex_injective huy)
        have hjLt := j.isLt
        simp only [Fin.val_castLT, Fin.val_last] at hidx
        omega
    have huf : Incident G u f := by
      change u ∈ G.ends f
      rw [hj]
      exact Sym2.mem_mk_right _ _
    have hSigmaF : sigma f = some beta :=
      (hfixed f ⟨u, huA, huf⟩).trans hBetaF
    have hyAdj : (TwoColorIncidenceGraph G sigma theta beta).Adj (Sum.inl y) (Sum.inr f) :=
      ⟨hfy, Or.inr hSigmaF⟩
    have huAdj : (TwoColorIncidenceGraph G sigma theta beta).Adj (Sum.inl u) (Sum.inr f) :=
      ⟨huf, Or.inr hSigmaF⟩
    have huC : Sum.inl u ∈ TwoColorComponent G sigma theta beta (Sum.inl y) :=
      (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj huAdj).trans
        (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hyAdj).symm
    exact havoidSigma u huA huC
