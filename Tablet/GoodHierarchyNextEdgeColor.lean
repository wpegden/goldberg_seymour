import Tablet.BoundaryColorEdges
import Tablet.BoundaryEdges
import Tablet.ExtendedTashkinovTree
import Tablet.GoodHierarchy
import Tablet.HierarchyFirstMissingPosition
import Tablet.HierarchySegmentColors
import Tablet.HierarchyStarredStage
import Tablet.HierarchyStoredColorsAt
import Tablet.TashkinovAugmentation
import Tablet.TashkinovAugmentationSequence
import Tablet.TashkinovClosure
import Tablet.TashkinovHierarchy
import Tablet.TashkinovSeries
import Tablet.TashkinovSeriesStep
import Tablet.TreeColorSetClosed
import Tablet.TreeColorSetMinusClosed
import Tablet.TreeMissingColors
import Tablet.TreeSequence
import Tablet.TreeSequenceAdjoinEdge
import Tablet.TreeSequenceInitialSegment
import Tablet.TreeSequenceVertexSet

-- [TABLET NODE: GoodHierarchyNextEdgeColor]
theorem GoodHierarchyNextEdgeColor {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    {input : PartialEdgeColoring E k} {T : TreeSequence G e0}
    {phi : PartialEdgeColoring E k}
    {ett : ExtendedTashkinovTree G k e0 input T phi}
    {base : HierarchyBase ett phi} {H : TashkinovHierarchy ett base}
    (good : GoodHierarchy H) (i : Fin H.dividerCount) :
    let current := H.stage i.succ.castSucc
    let next := H.stage i.succ.succ
    ∃ r : Fin next.length, ∃ alpha eta : Fin k,
      r.val = current.length ∧
      phi (next.edge r) = some alpha ∧
      eta ∈ HierarchyStoredColorsAt H i.succ ∧
      alpha ∈ good.gamma i.castSucc eta ∧
      alpha ∉ good.gamma i.succ eta := by
-- BODY
  dsimp
  have segmentTrans : ∀ {A B C : TreeSequence G e0},
      TreeSequenceInitialSegment A B → TreeSequenceInitialSegment B C →
      TreeSequenceInitialSegment A C := by
    intro A B C hab hbc
    rcases hab with ⟨hab, hvab, heab⟩
    rcases hbc with ⟨hbc, hvbc, hebc⟩
    refine ⟨hab.trans hbc, ?_, ?_⟩
    · intro j
      calc
        C.vertex (Fin.castLE (Nat.succ_le_succ (hab.trans hbc)) j) =
            C.vertex (Fin.castLE (Nat.succ_le_succ hbc)
              (Fin.castLE (Nat.succ_le_succ hab) j)) := by congr 2
        _ = B.vertex (Fin.castLE (Nat.succ_le_succ hab) j) := hvbc _
        _ = A.vertex j := hvab j
    · intro j
      calc
        C.edge (Fin.castLE (hab.trans hbc) j) =
            C.edge (Fin.castLE hbc (Fin.castLE hab j)) := by congr 2
        _ = B.edge (Fin.castLE hab j) := hebc _
        _ = A.edge j := heab j
  have segmentVertex : ∀ {A B : TreeSequence G e0},
      TreeSequenceInitialSegment A B →
      ∀ v, v ∈ TreeSequenceVertexSet A → v ∈ TreeSequenceVertexSet B := by
    intro A B hab v hv
    rcases hab with ⟨hlen, hvab, hedges⟩
    simp only [TreeSequenceVertexSet, Finset.mem_image] at hv ⊢
    rcases hv with ⟨j, hj, rfl⟩
    exact ⟨Fin.castLE (Nat.succ_le_succ hlen) j, Finset.mem_univ _, hvab j⟩
  have segmentEdge : ∀ {A B : TreeSequence G e0},
      ∀ (hab : TreeSequenceInitialSegment A B), ∀ j : Fin A.length,
      B.edge (Fin.castLE hab.1 j) = A.edge j := by
    intro A B hab j
    exact hab.2.2 j
  have reachVertex : ∀ {A B : TreeSequence G e0} {psi : PartialEdgeColoring E k},
      TashkinovAugmentationSequence psi A B →
      ∀ v, v ∈ TreeSequenceVertexSet A → v ∈ TreeSequenceVertexSet B := by
    intro A B psi hreach
    unfold TashkinovAugmentationSequence at hreach
    induction hreach using Relation.ReflTransGen.head_induction_on with
    | refl => exact fun v hv => hv
    | @head A B hstep htail ih =>
        intro v hv
        exact ih v (segmentVertex hstep.2.1 v hv)
  have closureRestrict : ∀ {A B C : TreeSequence G e0}
      {psi : PartialEdgeColoring E k},
      TashkinovAugmentationSequence psi A C →
      TreeSequenceInitialSegment A B → TreeSequenceInitialSegment B C →
      TashkinovAugmentationSequence psi A B := by
    intro A B C psi hreach hab hbc
    unfold TashkinovAugmentationSequence at hreach ⊢
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
            funext j
            simpa only [Fin.castLE] using (hv j).symm
          · apply heq_of_eq
            funext j
            simpa only [Fin.castLE] using (he j).symm
    have commonExtension : ∀ {X Y Z : TreeSequence G e0},
        TreeSequenceInitialSegment X Z →
        TreeSequenceInitialSegment Y Z → Y.length ≤ X.length →
        TreeSequenceInitialSegment Y X := by
      intro X Y Z hXZ hYZ hYX
      rcases hXZ with ⟨hx, hvx, hex⟩
      rcases hYZ with ⟨hy, hvy, hey⟩
      refine ⟨hYX, ?_, ?_⟩
      · intro j
        calc
          X.vertex (Fin.castLE (Nat.succ_le_succ hYX) j) =
              Z.vertex (Fin.castLE (Nat.succ_le_succ hx)
                (Fin.castLE (Nat.succ_le_succ hYX) j)) := (hvx _).symm
          _ = Z.vertex (Fin.castLE (Nat.succ_le_succ hy) j) := by congr 1
          _ = Y.vertex j := hvy j
      · intro j
        calc
          X.edge (Fin.castLE hYX j) =
              Z.edge (Fin.castLE hx (Fin.castLE hYX j)) := (hex _).symm
          _ = Z.edge (Fin.castLE hy j) := by congr 1
          _ = Y.edge j := hey j
    induction hreach generalizing B with
    | refl =>
        have hlen : B.length = A.length := Nat.le_antisymm hbc.1 hab.1
        have htree : B = A := equalTrees hbc hlen
        subst B
        exact Relation.ReflTransGen.refl
    | @tail X C hAX hXC ih =>
        rcases hXC with ⟨hlen, hinit, hcolor⟩
        by_cases hshort : B.length ≤ X.length
        · exact ih (B := B) hab (commonExtension hinit hbc hshort)
        · have hsame : B.length = C.length := by
            have hBCle := hbc.1
            have hgt : X.length < B.length := Nat.lt_of_not_ge hshort
            omega
          have htree : B = C := equalTrees hbc hsame
          subst B
          exact Relation.ReflTransGen.tail hAX ⟨hlen, hinit, hcolor⟩
  have stageToTerminal : ∀ j : Fin (H.dividerCount + 2),
      TreeSequenceInitialSegment (H.stage j) T := by
    intro j
    exact Fin.reverseInduction (motive := fun q =>
      TreeSequenceInitialSegment (H.stage q) T)
      (by rw [H.terminalStage]; exact ⟨le_rfl, (by intro q; rfl), (by intro q; rfl)⟩) (by
        intro q hq
        exact segmentTrans (H.nested q) hq) j
  have stageFromZero : ∀ j : Fin (H.dividerCount + 2),
      TreeSequenceInitialSegment (H.stage 0) (H.stage j) := by
    intro j
    induction j using Fin.induction with
    | zero =>
        exact ⟨Nat.le_refl _, by intro q; rfl, by intro q; rfl⟩
    | succ j ih =>
        exact segmentTrans ih (H.nested j)
  have reachSegment : ∀ {A B : TreeSequence G e0} {psi : PartialEdgeColoring E k},
      TashkinovAugmentationSequence psi A B →
      TreeSequenceInitialSegment A B := by
    intro A B psi hreach
    unfold TashkinovAugmentationSequence at hreach
    induction hreach using Relation.ReflTransGen.head_induction_on with
    | refl =>
        exact ⟨Nat.le_refl _, by intro q; rfl, by intro q; rfl⟩
    | @head A B hstep htail ih =>
        exact segmentTrans hstep.2.1 ih
  have stageOneTo : ∀ j : Fin H.dividerCount,
      TreeSequenceInitialSegment (H.stage 1)
        (H.stage ⟨j.val + 1, by omega⟩) := by
    intro j
    let top : Fin (H.dividerCount + 1) := ⟨j.val, by omega⟩
    have chain : ∀ n : Fin (H.dividerCount + 1),
        TreeSequenceInitialSegment (H.stage 1) (H.stage n.succ) := by
      intro n
      induction n using Fin.induction with
      | zero => exact ⟨le_rfl, by intro z; rfl, by intro z; rfl⟩
      | succ n ih => exact segmentTrans ih (H.nested n.succ)
    simpa [top] using chain top
  have commonExtension : ∀ {X Y Z : TreeSequence G e0},
      TreeSequenceInitialSegment X Z → TreeSequenceInitialSegment Y Z →
      Y.length ≤ X.length → TreeSequenceInitialSegment Y X := by
    intro X Y Z hXZ hYZ hYX
    rcases hXZ with ⟨hx, hvx, hex⟩
    rcases hYZ with ⟨hy, hvy, hey⟩
    refine ⟨hYX, ?_, ?_⟩
    · intro j
      calc
        X.vertex (Fin.castLE (Nat.succ_le_succ hYX) j) =
            Z.vertex (Fin.castLE (Nat.succ_le_succ hx)
              (Fin.castLE (Nat.succ_le_succ hYX) j)) := (hvx _).symm
        _ = Z.vertex (Fin.castLE (Nat.succ_le_succ hy) j) := by congr 1
        _ = Y.vertex j := hvy j
    · intro j
      calc
        X.edge (Fin.castLE hYX j) =
            Z.edge (Fin.castLE hx (Fin.castLE hYX j)) := (hex _).symm
        _ = Z.edge (Fin.castLE hy j) := by congr 1
        _ = Y.edge j := hey j
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
          funext j
          simpa only [Fin.castLE] using (hv j).symm
        · apply heq_of_eq
          funext j
          simpa only [Fin.castLE] using (he j).symm
  have crossing : ∀ {S Z A : TreeSequence G e0}
      {psi : PartialEdgeColoring E k},
      TashkinovAugmentationSequence psi S Z →
      S.length ≤ A.length → TreeSequenceInitialSegment A Z →
      A.length < Z.length →
      ∃ X Y, TashkinovAugmentation psi X Y ∧ X.length = A.length ∧
        TreeSequenceInitialSegment X A ∧ TreeSequenceInitialSegment Y Z := by
    intro S Z A psi hseq
    induction hseq using Relation.ReflTransGen.head_induction_on with
    | refl =>
        intro hle hAZ hlt
        omega
    | @head S X hstep htail ih =>
        intro hle hAZ hlt
        rcases hstep with ⟨hinc, hinit, hc⟩
        have hSZ : TreeSequenceInitialSegment S Z :=
          segmentTrans hinit (reachSegment
            (show TashkinovAugmentationSequence psi X Z from htail))
        have htailSeg : TreeSequenceInitialSegment X Z :=
          reachSegment (show TashkinovAugmentationSequence psi X Z from htail)
        by_cases hAS : A.length = S.length
        · have hSA : TreeSequenceInitialSegment S A :=
            commonExtension hAZ hSZ (by omega)
          exact ⟨S, X, ⟨hinc, hinit, hc⟩, hAS.symm, hSA, htailSeg⟩
        · have hSXle : X.length ≤ A.length := by
            have hslt : S.length < A.length := Nat.lt_of_le_of_ne hle
              (fun h => hAS h.symm)
            omega
          exact ih hSXle hAZ hlt
  have finish : ∀ {S U A B : TreeSequence G e0}
      {psi : PartialEdgeColoring E k},
      TashkinovClosure psi S U →
      TreeSequenceInitialSegment S A →
      TreeSequenceInitialSegment A U →
      TreeSequenceInitialSegment B U →
      A.length < B.length →
      psi = phi →
      A = H.stage i.succ.castSucc →
      B = H.stage i.succ.succ →
      ∃ r : Fin B.length, ∃ alpha eta : Fin k,
        r.val = A.length ∧ psi (B.edge r) = some alpha ∧
        eta ∈ HierarchyStoredColorsAt H i.succ ∧
        alpha ∈ good.gamma i.castSucc eta ∧
        alpha ∉ good.gamma i.succ eta := by
    intro S U A B psi hclosure hSA hAU hBU hlt hpsi hAeq hBeq
    have hSL : S.length ≤ A.length := hSA.1
    have hseq : TashkinovAugmentationSequence psi S U := hclosure.1
    have hltU : A.length < U.length := Nat.lt_of_lt_of_le hlt hBU.1
    obtain ⟨X, Y, haug, hXlen, hXA, hYU⟩ :=
      crossing hseq hSL hAU hltU
    have hXAeq : X = A := equalTrees hXA hXlen
    subst X
    rcases haug with ⟨hyl, hyinit, c, hcolor, hmiss⟩
    have hYB : TreeSequenceInitialSegment Y B := by
      apply commonExtension hBU hYU
      omega
    let jnew : Fin Y.length := Fin.cast hyl.symm (Fin.last A.length)
    have hnew : B.edge (Fin.castLE hYB.1 jnew) = Y.edge jnew := by
      exact hYB.2.2 _
    have hcolor' : phi (B.edge (Fin.castLE hYB.1 jnew)) = some c := by
      rw [hnew, ← hpsi]
      exact hcolor
    have hmiss' : c ∈ TreeMissingColors phi A := by
      simpa [hpsi] using hmiss
    let reserved := (HierarchyStoredColorsAt H i.succ).biUnion (good.gamma i.castSucc)
    have hboundary : B.edge (Fin.castLE hYB.1 jnew) ∈
        BoundaryColorEdges G phi (TreeSequenceVertexSet A) c := by
      simp only [BoundaryColorEdges, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨?_, hcolor'⟩
      unfold BoundaryEdges
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      obtain ⟨v, hv⟩ := Y.attaches jnew
      have hvle : v.val ≤ A.length := by
        simp [jnew, hyl] at *
        omega
      let vY : Fin (Y.length + 1) := ⟨v.val, by omega⟩
      let av : Fin (A.length + 1) := ⟨v.val, by omega⟩
      rcases hyinit with ⟨hylen, hyvertices, hyedges⟩
      have hvold : Y.vertex vY = A.vertex av := by
        have hindex : vY = Fin.castLE (Nat.succ_le_succ hylen) av := by
          apply Fin.ext
          simp only [Fin.val_castLE, Fin.val_mk]
          rfl
        rw [hindex]
        exact hyvertices av
      have hnewout : Y.vertex jnew.succ ∉ TreeSequenceVertexSet A := by
        intro hx
        simp only [TreeSequenceVertexSet, Finset.mem_image] at hx
        obtain ⟨a, ha, hxa⟩ := hx
        have hsame := Y.vertex_injective (hxa.symm.trans
          (hyvertices a).symm)
        have hindex := congrArg Fin.val hsame
        simp only [Fin.coe_castLE] at hindex
        simp [jnew] at hindex
        omega
      refine ⟨Y.vertex vY, ?_,
        Y.vertex jnew.succ, hnewout, ?_⟩
      · simp only [TreeSequenceVertexSet, Finset.mem_image]
        exact ⟨av, by simp, hvold.symm⟩
      · rw [hnew]
        have hvindex : vY = v.castLT (by omega) := by
          apply Fin.ext
          simp only [Fin.val_castLT, Fin.val_mk]
          rfl
        rw [hvindex]
        simpa [Sym2.eq_swap] using hv
    have hc : c ∈ reserved := by
      by_contra hnot
      have hminus : c ∈ TreeMissingColors phi A \ reserved :=
        Finset.mem_sdiff.mpr ⟨hmiss', hnot⟩
      have hempty := good.minusClosed i c
        (by simpa [hAeq, reserved, Finset.mem_biUnion] using hminus)
      have hb := hboundary
      rw [hAeq] at hb
      rw [hempty] at hb
      simpa using hb
    obtain ⟨eta, heta, hceta⟩ := Finset.mem_biUnion.mp hc
    have hnotnew : c ∉ good.gamma i.succ eta := by
      intro hnewgamma
      have hetaMissing : eta ∉ TreeMissingColors phi A := by
        intro hm
        have hstar : HierarchyStarredStage H i.succ = A := by
          simp [HierarchyStarredStage, hAeq]
        exact (Finset.mem_sdiff.mp
          (by simpa [HierarchyStoredColorsAt, hstar] using heta)).2 hm
      have hfirst : A.length <
          (HierarchyFirstMissingPosition phi T eta).val := by
        classical
        have hAT : TreeSequenceInitialSegment A T := by
          rw [hAeq]
          exact stageToTerminal i.succ.castSucc
        have hBT : TreeSequenceInitialSegment B T := by
          rw [hBeq]
          exact stageToTerminal i.succ.succ
        unfold HierarchyFirstMissingPosition
        dsimp
        let candidates : Finset (Fin (T.length + 1)) :=
          Finset.univ.filter fun z => eta ∈ MissingColors G phi (T.vertex z)
        change (if h : candidates.Nonempty then candidates.min' h else
          Fin.last T.length).val > A.length
        split
        · by_contra hn
          have hle : (candidates.min' ‹_›).val ≤ A.length := Nat.le_of_not_gt hn
          let aidx : Fin (A.length + 1) :=
            ⟨(candidates.min' ‹_›).val, by omega⟩
          have hv := hAT.2.1
            aidx
          have hm : eta ∈ TreeMissingColors phi A := by
            unfold TreeMissingColors
            simp only [Finset.mem_biUnion]
            have hcm := Finset.mem_filter.mp
              (Finset.min'_mem candidates ‹_›)
            refine ⟨T.vertex (candidates.min' ‹_›), ?_, hcm.2⟩
            have hv' : T.vertex (candidates.min' ‹_›) = A.vertex aidx := by
              rw [← hv]
              apply congrArg T.vertex
              apply Fin.ext
              simp [aidx]
            rw [hv']
            simp [TreeSequenceVertexSet]
          exact hetaMissing hm
        · simp
          have hlt : A.length < B.length := hlt
          have hle : B.length ≤ T.length := hBT.1
          omega
      have hav := good.avoidance i.succ eta
        (by simpa [HierarchyStoredColorsAt] using heta)
      have hstar : HierarchyStarredStage H i.succ = A := by
        simp [HierarchyStarredStage, hAeq]
      have hseg : c ∈ HierarchySegmentColors H i.succ eta := by
        simp only [HierarchySegmentColors, Finset.mem_filter, Finset.mem_univ, true_and]
        have hYBstage : TreeSequenceInitialSegment Y (H.stage i.succ.succ) := by
          simpa [hBeq] using hYB
        have hcolorStage :
            phi ((H.stage i.succ.succ).edge (Fin.castLE hYBstage.1 jnew)) = some c := by
          subst B
          exact hcolor'
        refine ⟨Fin.castLE hYBstage.1 jnew, ?_, ?_, hcolorStage⟩
        · simpa [hstar, jnew]
        · have hb : A.length < (H.stage i.succ.succ).length := by
            simpa [hAeq, hBeq] using H.strict i.succ
          simpa [jnew, hBeq, Nat.min_eq_left, hfirst, hb]
      exact (Finset.mem_sdiff.mp (hav hnewgamma)).2 hseg
    refine ⟨Fin.castLE hYB.1 jnew, c, eta, ?_, ?_, heta, ?_, hnotnew⟩
    · rfl
    · simpa [hpsi] using hcolor'
    · exact hceta
  have hr : 1 ≤ ett.rounds := ett.roundsPositive
  let q : Fin ett.rounds := ⟨ett.rounds - 1, by omega⟩
  have qlast : q.succ = Fin.last ett.rounds := by
    apply Fin.ext
    simp [q]
    omega
  have qterminal : q.succ.succ = Fin.last (ett.rounds + 1) := by
    apply Fin.ext
    have hq := congrArg Fin.val qlast
    simp at hq ⊢
    omega
  generalize target_eq : q.succ = target
  cases ett.series.certified target with
  | initial triple seedLength initialColoring initialStored initialEdges
      initialKind initialVertex initialOutside initialDelta initialGamma
      initialClosure => exact (Fin.succ_ne_zero q target_eq).elim
  | SE j previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternative
      currentColoring currentStored currentEdges currentKind currentVertex
      currentOutside currentDelta currentGamma adjoined adjoinedExactly
        closedExtension orderedExtension strictExtension =>
          have hjq : j = q := by
            apply Fin.ext
            have hv := congrArg Fin.val target_eq
            change q.val + 1 = j.val + 1 at hv
            exact (Nat.add_right_cancel hv).symm
          subst j
          rw [qterminal] at *
          have hseed :
              TreeSequenceInitialSegment adjoined (H.stage i.succ.castSucc) := by
            have hbase := stageFromZero i.succ.castSucc
            rw [H.baseStage] at hbase
            have hlen : adjoined.length ≤ (H.stage i.succ.castSucc).length := by
              have hstrict := H.strict (0 : Fin (H.dividerCount + 1))
              have hbaseLen := congrArg TreeSequence.length H.baseStage
              have hstage := (stageOneTo i).1
              have hadj := adjoinedExactly.1
              have hadjLen : adjoined.length = (H.stage 0).length + 1 := by
                simpa [H.baseStage, qlast] using hadj
              have hzero : (H.stage 0).length < (H.stage 1).length := by simpa using hstrict
              have hstage' : (H.stage 1).length ≤
                  (H.stage i.succ.castSucc).length := by
                have hi : i.castSucc.succ = i.succ.castSucc := by
                  apply Fin.ext
                  rfl
                rw [← hi]
                exact hstage
              omega
            exact commonExtension
              (segmentTrans (stageToTerminal i.succ.castSucc) ett.belowFinal)
              (segmentTrans (reachSegment closedExtension.1)
                ⟨le_rfl, by intro z; rfl, by intro z; rfl⟩) hlen
          have hfinalA := segmentTrans (stageToTerminal i.succ.castSucc) ett.belowFinal
          have hfinalB := segmentTrans (stageToTerminal i.succ.succ) ett.belowFinal
          have hcolorEq : ett.series.data.coloring q.succ = phi := by
            calc
              ett.series.data.coloring q.succ =
                  ett.series.data.coloring (Fin.last ett.rounds) := congrArg _ qlast
              _ = phi := ett.generatingColoring.symm
          have hi : i.castSucc.succ = i.succ.castSucc := by
            apply Fin.ext
            rfl
          have result := finish (psi := ett.series.data.coloring q.succ) closedExtension
            hseed hfinalA hfinalB (H.strict i.succ)
            hcolorEq rfl rfl
          simpa only [hi, hcolorEq] using result
  | PE j previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternativeFails
      gamma gammaRule secondStable secondStableProper secondStableOneUncolored
      secondStableRelation exitWitness currentColoring currentProper
      currentOneUncolored currentStored currentEdges currentKind currentVertex
      currentOutside currentDelta currentGamma closedExtension orderedExtension
        strictExtension =>
          have hjq : j = q := by
            apply Fin.ext
            have hv := congrArg Fin.val target_eq
            change q.val + 1 = j.val + 1 at hv
            exact (Nat.add_right_cancel hv).symm
          subst j
          rw [qterminal] at *
          have hseed :
              TreeSequenceInitialSegment
                (ett.series.data.tree q.succ.castSucc) (H.stage i.succ.castSucc) := by
            have hbase := stageFromZero i.succ.castSucc
            rw [H.baseStage] at hbase
            have hlen : (ett.series.data.tree q.succ.castSucc).length ≤
                (H.stage i.succ.castSucc).length := by
              simpa [qlast] using hbase.1
            exact commonExtension
              (segmentTrans (stageToTerminal i.succ.castSucc) ett.belowFinal)
              orderedExtension hlen
          have hfinalA := segmentTrans (stageToTerminal i.succ.castSucc) ett.belowFinal
          have hfinalB := segmentTrans (stageToTerminal i.succ.succ) ett.belowFinal
          have hcolorEq : ett.series.data.coloring q.succ = phi := by
            calc
              ett.series.data.coloring q.succ =
                  ett.series.data.coloring (Fin.last ett.rounds) := congrArg _ qlast
              _ = phi := ett.generatingColoring.symm
          have hi : i.castSucc.succ = i.succ.castSucc := by
            apply Fin.ext
            rfl
          have result := finish (psi := ett.series.data.coloring q.succ) closedExtension
            hseed hfinalA hfinalB (H.strict i.succ)
            hcolorEq rfl rfl
          simpa only [hi, hcolorEq] using result
  | RE j previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed available currentColoring currentStored
      currentEdges currentKind currentVertex currentOutside currentDelta
      currentGamma adjoined adjoinedExactly closedExtension orderedExtension
        strictExtension =>
          have hjq : j = q := by
            apply Fin.ext
            have hv := congrArg Fin.val target_eq
            change q.val + 1 = j.val + 1 at hv
            exact (Nat.add_right_cancel hv).symm
          subst j
          rw [qterminal] at *
          have hseed :
              TreeSequenceInitialSegment adjoined (H.stage i.succ.castSucc) := by
            have hbase := stageFromZero i.succ.castSucc
            rw [H.baseStage] at hbase
            have hlen : adjoined.length ≤ (H.stage i.succ.castSucc).length := by
              have hstrict := H.strict (0 : Fin (H.dividerCount + 1))
              have hadj := adjoinedExactly.1
              have hadjLen : adjoined.length = (H.stage 0).length + 1 := by
                simpa [H.baseStage, qlast] using hadj
              have hzero : (H.stage 0).length < (H.stage 1).length := by simpa using hstrict
              have hstage : (H.stage 1).length ≤
                  (H.stage i.succ.castSucc).length := by
                have hi : i.castSucc.succ = i.succ.castSucc := by
                  apply Fin.ext
                  rfl
                rw [← hi]
                exact (stageOneTo i).1
              omega
            exact commonExtension
              (segmentTrans (stageToTerminal i.succ.castSucc) ett.belowFinal)
              (segmentTrans (reachSegment closedExtension.1)
                ⟨le_rfl, by intro z; rfl, by intro z; rfl⟩) hlen
          have hfinalA := segmentTrans (stageToTerminal i.succ.castSucc) ett.belowFinal
          have hfinalB := segmentTrans (stageToTerminal i.succ.succ) ett.belowFinal
          have hcolorEq : ett.series.data.coloring q.succ = phi := by
            calc
              ett.series.data.coloring q.succ =
                  ett.series.data.coloring (Fin.last ett.rounds) := congrArg _ qlast
              _ = phi := ett.generatingColoring.symm
          have hi : i.castSucc.succ = i.succ.castSucc := by
            apply Fin.ext
            rfl
          have result := finish (psi := ett.series.data.coloring q.succ) closedExtension
            hseed hfinalA hfinalB (H.strict i.succ)
            hcolorEq rfl rfl
          simpa only [hi, hcolorEq] using result
