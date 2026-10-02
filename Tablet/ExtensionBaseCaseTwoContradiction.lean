import Tablet.ColoredVertexSetElementary
import Tablet.CorrespondingExtendedTashkinovTree
import Tablet.ExtensionBaseClaim45
import Tablet.InternalEdges
import Tablet.MaximumPropertyTransport
import Tablet.ModColoring
import Tablet.OrderedTreeUnionExists
import Tablet.StableColoring
import Tablet.StableColoringBeforeVertex
import Tablet.TashkinovAugmentation
import Tablet.TashkinovAugmentationSequence
import Tablet.TashkinovAugmentationSequenceInitialSegment
import Tablet.TashkinovAugmentationSequenceRestrict
import Tablet.TashkinovAugmentationSequenceSuffix
import Tablet.TashkinovClosureExists
import Tablet.TashkinovStoredColors
import Tablet.TreeSequenceAdjoinEdge
import Tablet.TreeSequenceInitialSegment
import Tablet.TreeSequenceInitialSegmentVertexSetSubset
import Tablet.TreeSequencePrefix
import Tablet.TreeSequenceVertexSet
import Tablet.TreeVerticesBefore

-- [TABLET NODE: ExtensionBaseCaseTwoContradiction]
theorem ExtensionBaseCaseTwoContradiction {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    {input : PartialEdgeColoring E k} {T : TreeSequence G e0}
    {generating : PartialEdgeColoring E k}
    (ett : ExtendedTashkinovTree G k e0 input T generating)
    {lowerInput : PartialEdgeColoring E k}
    {lowerTree : TreeSequence G e0}
    {lowerGenerating : PartialEdgeColoring E k}
    (lower : ExtendedTashkinovTree G k e0 lowerInput lowerTree
      lowerGenerating)
    (jSlot : Fin ett.rounds) (hjPositive : 1 ≤ jSlot.val)
    (Tjm1 Tj seed TjPrime : TreeSequence G e0)
    (phiJ rho1 rho3 : PartialEdgeColoring E k)
    (Dprev : Finset (Fin k))
    (terminalSupport u z : V) (beta gammaFirst deltaN : Fin k)
    (hterminalTj : terminalSupport ∈ TreeSequenceVertexSet Tj)
    (huPrime : u ∈ TreeSequenceVertexSet TjPrime)
    (hzTj : z ∈ TreeSequenceVertexSet Tj)
    (zPosition : Fin (Tj.length + 1))
    (uPosition : Fin (TjPrime.length + 1))
    (hzPosition : Tj.vertex zPosition = z)
    (huPosition : TjPrime.vertex uPosition = u)
    (hseedJ : TreeSequenceInitialSegment seed Tj)
    (hseedPrime : TreeSequenceInitialSegment seed TjPrime)
    (hseedTerminal : seed.vertex (Fin.last seed.length) = terminalSupport)
    (hseedAtMostZ : seed.length ≤ zPosition.val)
    (hseedBeforeU : seed.length < uPosition.val)
    (hterminalBeforeZ : terminalSupport ∈ TreeVerticesBefore Tj z hzTj)
    (huOutsideTj : u ∉ TreeSequenceVertexSet Tj)
    (hTjm1Stored :
      ett.series.data.tree jSlot.castSucc.castSucc = Tjm1)
    (hPhiJStored : ett.series.data.coloring jSlot.castSucc = phiJ)
    (hTjStored : ett.series.data.tree jSlot.succ.castSucc = Tj)
    (hDprevStored :
      TashkinovStoredColors ett.series.data jSlot.castSucc = Dprev)
    (hLowerRounds : lower.rounds = jSlot.val)
    (hLowerTree : lower.series.data.tree
      (Fin.last lower.rounds).castSucc = Tjm1)
    (hLowerColor : lower.series.data.coloring
      (Fin.last lower.rounds) = phiJ)
    (hLowerStored : TashkinovStoredColors lower.series.data
      (Fin.last lower.rounds) = Dprev)
    (hLowerKind : lower.series.data.kind (Fin.last lower.rounds) =
      ett.series.data.kind jSlot.castSucc)
    (hLowerConnecting : lower.series.data.connectingEdges
      (Fin.last lower.rounds) =
        ett.series.data.connectingEdges jSlot.castSucc)
    (hTjm1Before : TreeSequenceVertexSet Tjm1 ⊆
      TreeVerticesBefore Tj terminalSupport hterminalTj)
    (hseedBuild :
      (ett.series.data.kind jSlot.castSucc =
          some TashkinovExtensionKind.PE ∧
        TashkinovAugmentationSequence phiJ Tjm1 seed) ∨
      ((ett.series.data.kind jSlot.castSucc =
            some TashkinovExtensionKind.SE ∨
          ett.series.data.kind jSlot.castSucc =
            some TashkinovExtensionKind.RE) ∧
        ∃ (f : E) (adjoinSeed : TreeSequence G e0),
          ett.series.data.connectingEdges jSlot.castSucc = {f} ∧
            TreeSequenceAdjoinEdge Tjm1 f adjoinSeed ∧
            TashkinovAugmentationSequence phiJ adjoinSeed seed))
    (hTjAugmentation : TashkinovAugmentationSequence phiJ seed Tj)
    (hprimeClosure : TashkinovClosure rho1 seed TjPrime)
    (hprimeElementary : ColoredVertexSetElementary G rho1
      (TreeSequenceVertexSet TjPrime))
    (hMP : MaximumProperty ett)
    (hLowerMP : MaximumProperty lower)
    (hLowerI : ∀ (Tstar : TreeSequence G e0)
      (corr : CorrespondingExtendedTashkinovTree G k e0 lower rho3 Tstar),
      MaximumProperty corr.replacementETT →
        ColoredVertexSetElementary G rho3
          (TreeSequenceVertexSet Tstar))
    (hLowerVI : ∀ sigma : PartialEdgeColoring E k,
      IsProperEdgeColoring G sigma → IsOneEdgeUncolored sigma e0 →
      StableColoring Tjm1 Dprev phiJ sigma → ModColoring lower sigma)
    (hb2Missing : ∀ v : V,
      v ∈ (TreeSequenceVertexSet Tj).erase terminalSupport →
        MissingColors G rho1 v = MissingColors G phiJ v)
    (hb2Edges : ∀ a : Fin Tj.length,
      rho1 (Tj.edge a) = phiJ (Tj.edge a))
    (huniquezang : MissingColors G phiJ terminalSupport ⊆
      MissingColors G rho1 terminalSupport ∪ {gammaFirst})
    (hdeltaRho1 : deltaN ∈ MissingColors G rho1 terminalSupport)
    (hbetaU : beta ∈ MissingColors G rho1 u)
    (hrhoProper : IsProperEdgeColoring G rho3)
    (hrhoOne : IsOneEdgeUncolored rho3 e0)
    (hd1 : StableColoringBeforeVertex Tj terminalSupport hterminalTj
      Dprev phiJ rho3)
    (hd2Missing : ∀ v : V,
      v ∈ (((TreeVerticesBefore Tj z hzTj ∪ {z}) ∪
          (TreeVerticesBefore TjPrime u huPrime ∪ {u})).erase u).erase z →
        MissingColors G rho3 v = MissingColors G rho1 v)
    (hd2Edges : ∀ f : E,
      ((∃ a : Fin Tj.length, a.val < zPosition.val ∧ Tj.edge a = f) ∨
        (∃ a : Fin TjPrime.length,
          a.val < uPosition.val ∧ TjPrime.edge a = f)) →
      rho3 f = rho1 f)
    (hd2Delta : beta ∈ MissingColors G rho1 z →
      deltaN ∈ MissingColors G rho3 z)
    (hd2Z : z ∈ TreeVerticesBefore TjPrime u huPrime →
      MissingColors G rho3 z = MissingColors G rho1 z)
    (hd3 : gammaFirst ∈ MissingColors G rho3 u)
    (hzChoice : zPosition = Fin.last Tj.length ∨
      (zPosition.val < (Fin.last Tj.length).val ∧
        beta ∈ MissingColors G rho1 z)) : False := by
-- BODY
  classical
  have hstableLower : StableColoring Tjm1 Dprev phiJ rho3 := by
    unfold StableColoring
    constructor
    · intro f hfIncident hfControlled
      obtain ⟨v, hvTjm1, hvf⟩ := hfIncident
      have hvBefore : v ∈ TreeVerticesBefore Tj terminalSupport hterminalTj :=
        hTjm1Before hvTjm1
      apply hd1.1 f ⟨v, hvBefore, hvf⟩
      obtain ⟨c, hcControlled, hfc⟩ := hfControlled
      refine ⟨c, ?_, hfc⟩
      rcases Finset.mem_union.mp hcControlled with hcMissing | hcStored
      · apply Finset.mem_union_left
        unfold TreeMissingColors at hcMissing
        obtain ⟨w, hwTjm1, hcw⟩ := Finset.mem_biUnion.mp hcMissing
        exact Finset.mem_biUnion.mpr
          ⟨w, hTjm1Before hwTjm1, hcw⟩
      · exact Finset.mem_union_right _ hcStored
    · intro v hvTjm1
      exact hd1.2 v (hTjm1Before hvTjm1)
  have hmod : ModColoring lower rho3 :=
    hLowerVI rho3 hrhoProper hrhoOne hstableLower
  have segmentTrans {A B C : TreeSequence G e0}
      (hAB : TreeSequenceInitialSegment A B)
      (hBC : TreeSequenceInitialSegment B C) :
      TreeSequenceInitialSegment A C := by
    rcases hAB with ⟨hlenAB, hvertexAB, hedgeAB⟩
    rcases hBC with ⟨hlenBC, hvertexBC, hedgeBC⟩
    refine ⟨hlenAB.trans hlenBC, ?_, ?_⟩
    · intro i
      calc
        C.vertex (Fin.castLE
            (Nat.succ_le_succ (hlenAB.trans hlenBC)) i) =
            C.vertex (Fin.castLE (Nat.succ_le_succ hlenBC)
              (Fin.castLE (Nat.succ_le_succ hlenAB) i)) := by congr 1
        _ = B.vertex (Fin.castLE (Nat.succ_le_succ hlenAB) i) :=
          hvertexBC _
        _ = A.vertex i := hvertexAB i
    · intro i
      calc
        C.edge (Fin.castLE (hlenAB.trans hlenBC) i) =
            C.edge (Fin.castLE hlenBC (Fin.castLE hlenAB i)) := by congr 1
        _ = B.edge (Fin.castLE hlenAB i) := hedgeBC _
        _ = A.edge i := hedgeAB i
  have commonPrefix {A B C : TreeSequence G e0}
      (hAC : TreeSequenceInitialSegment A C)
      (hBC : TreeSequenceInitialSegment B C)
      (hlen : A.length ≤ B.length) :
      TreeSequenceInitialSegment A B := by
    rcases hAC with ⟨hlenAC, hvertexAC, hedgeAC⟩
    rcases hBC with ⟨hlenBC, hvertexBC, hedgeBC⟩
    refine ⟨hlen, ?_, ?_⟩
    · intro i
      calc
        B.vertex (Fin.castLE (Nat.succ_le_succ hlen) i) =
            C.vertex (Fin.castLE (Nat.succ_le_succ hlenBC)
              (Fin.castLE (Nat.succ_le_succ hlen) i)) :=
          (hvertexBC _).symm
        _ = C.vertex (Fin.castLE (Nat.succ_le_succ hlenAC) i) := by
          congr 1
        _ = A.vertex i := hvertexAC i
    · intro i
      calc
        B.edge (Fin.castLE hlen i) =
            C.edge (Fin.castLE hlenBC (Fin.castLE hlen i)) :=
          (hedgeBC _).symm
        _ = C.edge (Fin.castLE hlenAC i) := by congr 1
        _ = A.edge i := hedgeAC i
  have hseedVertexBefore (i : Fin (seed.length + 1))
      (hi : i.val < seed.length) :
      seed.vertex i ∈ TreeVerticesBefore Tj terminalSupport hterminalTj := by
    unfold TreeVerticesBefore
    apply Finset.mem_filter.mpr
    constructor
    · simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ,
        true_and]
      exact ⟨Fin.castLE (Nat.succ_le_succ hseedJ.1) i,
        hseedJ.2.1 i⟩
    · unfold TreeVertexOrder
      let p : Fin (Tj.length + 1) :=
        Fin.castLE (Nat.succ_le_succ hseedJ.1) i
      let q : Fin (Tj.length + 1) :=
        Fin.castLE (Nat.succ_le_succ hseedJ.1) (Fin.last seed.length)
      refine ⟨p, q, ?_, ?_, ?_⟩
      · exact hseedJ.2.1 i
      · exact (hseedJ.2.1 (Fin.last seed.length)).trans hseedTerminal
      · simpa [p, q] using hi
  have hsegmentVertexBefore {A : TreeSequence G e0}
      (hAseed : TreeSequenceInitialSegment A seed)
      (hAlen : A.length < seed.length) {v : V}
      (hvA : v ∈ TreeSequenceVertexSet A) :
      v ∈ TreeVerticesBefore Tj terminalSupport hterminalTj := by
    obtain ⟨hAseedLen, hAseedVertices, -⟩ := hAseed
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ,
      true_and] at hvA
    obtain ⟨i, rfl⟩ := hvA
    have hi : (Fin.castLE (Nat.succ_le_succ hAseedLen) i).val <
        seed.length := by
      change i.val < seed.length
      omega
    rw [← hAseedVertices i]
    exact hseedVertexBefore _ hi
  have transportStep {A B : TreeSequence G e0}
      (hstep : TashkinovAugmentation phiJ A B)
      (hBseed : TreeSequenceInitialSegment B seed) :
      TashkinovAugmentation rho3 A B := by
    rcases hstep with ⟨hlen, hAB, c, hcolor, hcMissing⟩
    have hAseed : TreeSequenceInitialSegment A seed := segmentTrans hAB hBseed
    have hAlen : A.length < seed.length :=
      lt_of_lt_of_le (by omega) hBseed.1
    have hcMissingRho : c ∈ TreeMissingColors rho3 A := by
      unfold TreeMissingColors at hcMissing ⊢
      obtain ⟨w, hwA, hcw⟩ := Finset.mem_biUnion.mp hcMissing
      refine Finset.mem_biUnion.mpr ⟨w, hwA, ?_⟩
      rw [hd1.2 w (hsegmentVertexBefore hAseed hAlen hwA)]
      exact hcw
    let added : Fin B.length := Fin.cast hlen.symm (Fin.last A.length)
    obtain ⟨q, hq⟩ := B.attaches added
    let oldPos : Fin (B.length + 1) :=
      Fin.castLT q (Nat.lt_trans q.isLt (Nat.succ_lt_succ added.isLt))
    have holdVal : oldPos.val < A.length + 1 := by
      dsimp [oldPos, added]
      simpa using q.isLt
    let oldA : Fin (A.length + 1) := ⟨oldPos.val, holdVal⟩
    have holdEq : B.vertex oldPos = A.vertex oldA := by
      have hcast : Fin.castLE (Nat.succ_le_succ hAB.1) oldA = oldPos := by
        apply Fin.ext
        rfl
      rw [← hcast]
      exact hAB.2.1 oldA
    have holdA : A.vertex oldA ∈ TreeSequenceVertexSet A := by
      simp [TreeSequenceVertexSet]
    have holdBefore : B.vertex oldPos ∈
        TreeVerticesBefore Tj terminalSupport hterminalTj := by
      rw [holdEq]
      exact hsegmentVertexBefore hAseed hAlen holdA
    have holdIncident : Incident G (B.vertex oldPos) (B.edge added) := by
      unfold Incident
      rw [hq]
      simp [oldPos]
    have haddedFixed : rho3 (B.edge added) = phiJ (B.edge added) := by
      apply hd1.1 (B.edge added) ⟨B.vertex oldPos, holdBefore, holdIncident⟩
      refine ⟨c, ?_, ?_⟩
      · apply Finset.mem_union_left
        unfold TreeMissingColors at hcMissing
        obtain ⟨w, hwA, hcw⟩ := Finset.mem_biUnion.mp hcMissing
        exact Finset.mem_biUnion.mpr
          ⟨w, hsegmentVertexBefore hAseed hAlen hwA, hcw⟩
      · exact hcolor
    refine ⟨hlen, hAB, c, ?_, hcMissingRho⟩
    change rho3 (B.edge added) = some c
    exact haddedFixed.trans hcolor
  have transportSeedRoute (S : TreeSequence G e0)
      (hroute : TashkinovAugmentationSequence phiJ S seed) :
      TashkinovAugmentationSequence rho3 S seed := by
    unfold TashkinovAugmentationSequence at hroute ⊢
    induction hroute using Relation.ReflTransGen.head_induction_on with
    | refl => exact Relation.ReflTransGen.refl
    | @head A B hAB hBseed ih =>
        have hBsegment : TreeSequenceInitialSegment B seed :=
          TashkinovAugmentationSequenceInitialSegment phiJ B seed hBseed
        exact Relation.ReflTransGen.head (transportStep hAB hBsegment) ih
  have hseedBuildRho :
      (ett.series.data.kind jSlot.castSucc =
          some TashkinovExtensionKind.PE ∧
        TashkinovAugmentationSequence rho3 Tjm1 seed) ∨
      ((ett.series.data.kind jSlot.castSucc =
            some TashkinovExtensionKind.SE ∨
          ett.series.data.kind jSlot.castSucc =
            some TashkinovExtensionKind.RE) ∧
        ∃ (f : E) (adjoinSeed : TreeSequence G e0),
          ett.series.data.connectingEdges jSlot.castSucc = {f} ∧
            TreeSequenceAdjoinEdge Tjm1 f adjoinSeed ∧
            TashkinovAugmentationSequence rho3 adjoinSeed seed) := by
    rcases hseedBuild with hparallel | hserial
    · exact Or.inl ⟨hparallel.1, transportSeedRoute Tjm1 hparallel.2⟩
    · rcases hserial with ⟨hkind, f, adjoinSeed, hconnecting,
          hadjoin, hroute⟩
      exact Or.inr ⟨hkind, f, adjoinSeed, hconnecting, hadjoin,
        transportSeedRoute adjoinSeed hroute⟩
  have huPositionPositive : 1 ≤ uPosition.val := by omega
  have huPositionBound : uPosition.val ≤ TjPrime.length :=
    Nat.lt_succ_iff.mp uPosition.isLt
  have hzPositionPositive : 1 ≤ zPosition.val :=
    seed.positive.trans hseedAtMostZ
  have hzPositionBound : zPosition.val ≤ Tj.length :=
    Nat.lt_succ_iff.mp zPosition.isLt
  let U : TreeSequence G e0 :=
    TreeSequencePrefix TjPrime uPosition.val huPositionPositive huPositionBound
  let Z : TreeSequence G e0 :=
    TreeSequencePrefix Tj zPosition.val hzPositionPositive hzPositionBound
  have hUPrime : TreeSequenceInitialSegment U TjPrime := by
    refine ⟨?_, ?_, ?_⟩
    · change uPosition.val ≤ TjPrime.length
      exact huPositionBound
    · intro i
      simp [U, TreeSequencePrefix]
    · intro i
      simp [U, TreeSequencePrefix]
  have hZTj : TreeSequenceInitialSegment Z Tj := by
    refine ⟨?_, ?_, ?_⟩
    · change zPosition.val ≤ Tj.length
      exact hzPositionBound
    · intro i
      simp [Z, TreeSequencePrefix]
    · intro i
      simp [Z, TreeSequencePrefix]
  have hseedU : TreeSequenceInitialSegment seed U := by
    apply commonPrefix hseedPrime hUPrime
    change seed.length ≤ uPosition.val
    omega
  have hseedZ : TreeSequenceInitialSegment seed Z := by
    apply commonPrefix hseedJ hZTj
    change seed.length ≤ zPosition.val
    exact hseedAtMostZ
  have hrouteRhoOneU : TashkinovAugmentationSequence rho1 seed U :=
    TashkinovAugmentationSequenceRestrict rho1 seed U TjPrime
      hprimeClosure.1 hseedU hUPrime
  have hprimeVertexBefore (i : Fin (TjPrime.length + 1))
      (hi : i.val < uPosition.val) :
      TjPrime.vertex i ∈ TreeVerticesBefore TjPrime u huPrime := by
    unfold TreeVerticesBefore
    apply Finset.mem_filter.mpr
    constructor
    · simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ,
        true_and]
      exact ⟨i, rfl⟩
    · unfold TreeVertexOrder
      exact ⟨i, uPosition, rfl, huPosition, hi⟩
  have hUsegmentVertexBefore {A : TreeSequence G e0}
      (hAU : TreeSequenceInitialSegment A U)
      (hAlen : A.length < U.length) {v : V}
      (hvA : v ∈ TreeSequenceVertexSet A) :
      v ∈ TreeVerticesBefore TjPrime u huPrime := by
    obtain ⟨hAULen, hAUVertices, -⟩ := hAU
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ,
      true_and] at hvA
    obtain ⟨i, rfl⟩ := hvA
    let iU : Fin (U.length + 1) :=
      Fin.castLE (Nat.succ_le_succ hAULen) i
    let iPrime : Fin (TjPrime.length + 1) :=
      Fin.castLE (Nat.succ_le_succ hUPrime.1) iU
    have hiPrime : iPrime.val < uPosition.val := by
      change i.val < uPosition.val
      have hUlen : U.length = uPosition.val := by simp [U, TreeSequencePrefix]
      omega
    rw [← hAUVertices i, ← hUPrime.2.1 iU]
    exact hprimeVertexBefore iPrime hiPrime
  have hbeforePrimeNeU {w : V}
      (hw : w ∈ TreeVerticesBefore TjPrime u huPrime) : w ≠ u := by
    unfold TreeVerticesBefore at hw
    obtain ⟨-, i, j, hiw, hju, hij⟩ := Finset.mem_filter.mp hw
    intro hwu
    have hijEq : i = j := TjPrime.vertex_injective
      (hiw.trans (hwu.trans hju.symm))
    omega
  have hbeforePrimeMissing (w : V)
      (hw : w ∈ TreeVerticesBefore TjPrime u huPrime) :
      MissingColors G rho3 w = MissingColors G rho1 w := by
    by_cases hwz : w = z
    · subst w
      exact hd2Z hw
    · apply hd2Missing w
      apply Finset.mem_erase.mpr
      refine ⟨hwz, Finset.mem_erase.mpr ⟨hbeforePrimeNeU hw, ?_⟩⟩
      apply Finset.mem_union_right
      exact Finset.mem_union_left _ hw
  have transportUStep {A B : TreeSequence G e0}
      (hstep : TashkinovAugmentation rho1 A B)
      (hBU : TreeSequenceInitialSegment B U) :
      TashkinovAugmentation rho3 A B := by
    rcases hstep with ⟨hlen, hAB, c, hcolor, hcMissing⟩
    have hAU : TreeSequenceInitialSegment A U := segmentTrans hAB hBU
    have hAlen : A.length < U.length :=
      lt_of_lt_of_le (by omega) hBU.1
    have hcMissingRho : c ∈ TreeMissingColors rho3 A := by
      unfold TreeMissingColors at hcMissing ⊢
      obtain ⟨w, hwA, hcw⟩ := Finset.mem_biUnion.mp hcMissing
      refine Finset.mem_biUnion.mpr ⟨w, hwA, ?_⟩
      rw [hbeforePrimeMissing w (hUsegmentVertexBefore hAU hAlen hwA)]
      exact hcw
    let added : Fin B.length := Fin.cast hlen.symm (Fin.last A.length)
    let addedU : Fin U.length := Fin.castLE hBU.1 added
    let addedPrime : Fin TjPrime.length := Fin.castLE hUPrime.1 addedU
    have haddedPosition : addedPrime.val < uPosition.val := by
      change A.length < uPosition.val
      have hUlen : U.length = uPosition.val := by simp [U, TreeSequencePrefix]
      omega
    have haddedIdentity : TjPrime.edge addedPrime = B.edge added := by
      exact (hUPrime.2.2 addedU).trans (hBU.2.2 added)
    have haddedFixed : rho3 (B.edge added) = rho1 (B.edge added) := by
      apply hd2Edges (B.edge added)
      exact Or.inr ⟨addedPrime, haddedPosition, haddedIdentity⟩
    refine ⟨hlen, hAB, c, ?_, hcMissingRho⟩
    change rho3 (B.edge added) = some c
    exact haddedFixed.trans hcolor
  have transportURoute (S : TreeSequence G e0)
      (hroute : TashkinovAugmentationSequence rho1 S U) :
      TashkinovAugmentationSequence rho3 S U := by
    unfold TashkinovAugmentationSequence at hroute ⊢
    induction hroute using Relation.ReflTransGen.head_induction_on with
    | refl => exact Relation.ReflTransGen.refl
    | @head A B hAB hBU ih =>
        have hBsegment : TreeSequenceInitialSegment B U :=
          TashkinovAugmentationSequenceInitialSegment rho1 B U hBU
        exact Relation.ReflTransGen.head (transportUStep hAB hBsegment) ih
  have hrouteRhoThreeU : TashkinovAugmentationSequence rho3 seed U :=
    transportURoute seed hrouteRhoOneU
  have hterminalNeZ : terminalSupport ≠ z := by
    unfold TreeVerticesBefore at hterminalBeforeZ
    obtain ⟨-, i, j, hit, hjz, hij⟩ :=
      Finset.mem_filter.mp hterminalBeforeZ
    intro htz
    have hijEq : i = j := Tj.vertex_injective
      (hit.trans (htz.trans hjz.symm))
    omega
  have hterminalNeU : terminalSupport ≠ u := by
    intro htu
    apply huOutsideTj
    rw [← htu]
    exact hterminalTj
  have hterminalMissingEq :
      MissingColors G rho3 terminalSupport =
        MissingColors G rho1 terminalSupport := by
    apply hd2Missing terminalSupport
    apply Finset.mem_erase.mpr
    refine ⟨hterminalNeZ, Finset.mem_erase.mpr ⟨hterminalNeU, ?_⟩⟩
    apply Finset.mem_union_left
    exact Finset.mem_union_left _ hterminalBeforeZ
  have hterminalInclusion : MissingColors G phiJ terminalSupport ⊆
      MissingColors G rho3 terminalSupport ∪ MissingColors G rho3 u := by
    intro c hc
    have hcCases := huniquezang hc
    rcases Finset.mem_union.mp hcCases with hcTerminal | hcGamma
    · apply Finset.mem_union_left
      rw [hterminalMissingEq]
      exact hcTerminal
    · apply Finset.mem_union_right
      have hcgamma : c = gammaFirst := Finset.mem_singleton.mp hcGamma
      simpa [hcgamma] using hd3
  have hbeforeZData {v : V}
      (hv : v ∈ TreeVerticesBefore Tj z hzTj) :
      v ∈ TreeSequenceVertexSet Tj ∧ v ≠ z := by
    unfold TreeVerticesBefore at hv
    obtain ⟨hvTj, i, j, hiv, hjz, hij⟩ := Finset.mem_filter.mp hv
    refine ⟨hvTj, ?_⟩
    intro hvz
    have hijEq : i = j := Tj.vertex_injective
      (hiv.trans (hvz.trans hjz.symm))
    omega
  have hbeforeZMissing (v : V)
      (hv : v ∈ TreeVerticesBefore Tj z hzTj)
      (hvTerminal : v ≠ terminalSupport) :
      MissingColors G rho3 v = MissingColors G phiJ v := by
    have hvData := hbeforeZData hv
    have hvU : v ≠ u := by
      intro hvu
      subst v
      exact huOutsideTj hvData.1
    have hRhoThreeOne :
        MissingColors G rho3 v = MissingColors G rho1 v := by
      apply hd2Missing v
      apply Finset.mem_erase.mpr
      refine ⟨hvData.2, Finset.mem_erase.mpr ⟨hvU, ?_⟩⟩
      apply Finset.mem_union_left
      exact Finset.mem_union_left _ hv
    exact hRhoThreeOne.trans
      (hb2Missing v (Finset.mem_erase.mpr ⟨hvTerminal, hvData.1⟩))
  obtain ⟨M, ⟨hunion⟩⟩ := OrderedTreeUnionExists U Z
  have huU : u ∈ TreeSequenceVertexSet U := by
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ,
      true_and]
    refine ⟨Fin.last U.length, ?_⟩
    change TjPrime.vertex (Fin.castLE (Nat.succ_le_succ huPositionBound)
      (Fin.last uPosition.val)) = u
    have hindex : Fin.castLE (Nat.succ_le_succ huPositionBound)
        (Fin.last uPosition.val) = uPosition := by
      apply Fin.ext
      rfl
    rw [hindex]
    exact huPosition
  have hrouteUM : TashkinovAugmentationSequence rho3 U M := by
    have hroutePhiZ : TashkinovAugmentationSequence phiJ seed Z :=
      TashkinovAugmentationSequenceRestrict phiJ seed Z Tj
        hTjAugmentation hseedZ hZTj
    have hleftSegment := hunion.leftSegment
    have hnewEntryFromRight := hunion.newEntryFromRight
    have heveryNewRightEntry := hunion.everyNewRightEntry
    have hrightOrder := hunion.rightOrder
    have prefixSegment (A : TreeSequence G e0) (q : Nat)
        (hq : 1 ≤ q) (hqA : q ≤ A.length) :
        TreeSequenceInitialSegment (TreeSequencePrefix A q hq hqA) A := by
      refine ⟨hqA, ?_, ?_⟩
      · intro i
        simp [TreeSequencePrefix]
      · intro i
        simp [TreeSequencePrefix]
    have prefixPrefix (A : TreeSequence G e0) (q : Nat)
        (hq : 1 ≤ q) (hqA : q + 1 ≤ A.length) :
        TreeSequenceInitialSegment
          (TreeSequencePrefix A q hq (Nat.le_trans (Nat.le_succ q) hqA))
          (TreeSequencePrefix A (q + 1) (by omega) hqA) := by
      refine ⟨Nat.le_succ q, ?_, ?_⟩
      · intro i
        change A.vertex _ = A.vertex _
        congr 1
      · intro i
        change A.edge _ = A.edge _
        congr 1
    have prefixSelf (A : TreeSequence G e0) :
        TreeSequencePrefix A A.length A.positive le_rfl = A := by
      cases A with
      | mk len pos vertex edge vinj einj first attach =>
        rw [TreeSequence.mk.injEq]
        refine ⟨rfl, ?_, ?_⟩
        · apply heq_of_eq
          funext i
          rfl
        · apply heq_of_eq
          funext i
          rfl
    have equalPrefixes {A B D : TreeSequence G e0}
        (hAD : TreeSequenceInitialSegment A D)
        (hBD : TreeSequenceInitialSegment B D)
        (hlen : A.length = B.length) : A = B := by
      rcases hAD with ⟨hlenAD, hvertexAD, hedgeAD⟩
      rcases hBD with ⟨hlenBD, hvertexBD, hedgeBD⟩
      cases A with
      | mk alen apos avertex aedge avinj aeinf afirst aattach =>
        cases B with
        | mk blen bpos bvertex bedge bvinj beinj bfirst battach =>
          simp only at hlen
          subst blen
          rw [TreeSequence.mk.injEq]
          refine ⟨rfl, ?_, ?_⟩
          · apply heq_of_eq
            funext i
            calc
              avertex i = D.vertex
                  (Fin.castLE (Nat.succ_le_succ hlenAD) i) :=
                (hvertexAD i).symm
              _ = D.vertex (Fin.castLE (Nat.succ_le_succ hlenBD) i) := by
                congr 1
              _ = bvertex i := hvertexBD i
          · apply heq_of_eq
            funext i
            calc
              aedge i = D.edge (Fin.castLE hlenAD i) := (hedgeAD i).symm
              _ = D.edge (Fin.castLE hlenBD i) := by congr 1
              _ = bedge i := hedgeBD i
    have prefixAtLeft :
        TreeSequencePrefix M U.length U.positive hleftSegment.1 = U := by
      apply equalPrefixes
        (prefixSegment M U.length U.positive hleftSegment.1)
        hleftSegment
      rfl
    have hseedZSegment : TreeSequenceInitialSegment seed Z :=
      TashkinovAugmentationSequenceInitialSegment phiJ seed Z hroutePhiZ
    have firstStep {A B : TreeSequence G e0}
        (hAB : TashkinovAugmentationSequence phiJ A B)
        (hlt : A.length < B.length) :
        ∃ C, TashkinovAugmentation phiJ A C ∧
          TashkinovAugmentationSequence phiJ C B := by
      unfold TashkinovAugmentationSequence at hAB ⊢
      induction hAB using Relation.ReflTransGen.head_induction_on with
      | refl => omega
      | @head A C hAC hCB ih => exact ⟨C, hAC, hCB⟩
    have replay : ∀ n (hnU : U.length ≤ n) (hnM : n ≤ M.length),
        TashkinovAugmentationSequence rho3 U
          (TreeSequencePrefix M n (Nat.le_trans U.positive hnU) hnM) := by
      intro n hnU hnM
      induction n, hnU using Nat.le_induction with
      | base =>
          simpa [prefixAtLeft] using
            (show TashkinovAugmentationSequence rho3 U U from
              Relation.ReflTransGen.refl)
      | @succ n hnU ih =>
          by_cases hnEq : n = M.length
          · omega
          have hnSuccM : n + 1 ≤ M.length := by omega
          have hnM' : n ≤ M.length := Nat.le_trans (Nat.le_succ n) hnSuccM
          have ih' := ih hnM'
          let X := TreeSequencePrefix M n
            (Nat.le_trans U.positive hnU) hnM'
          let Y := TreeSequencePrefix M (n + 1)
            (Nat.le_trans U.positive (Nat.le_trans hnU (Nat.le_succ n)))
            hnSuccM
          let j : Fin M.length := ⟨n, by omega⟩
          obtain ⟨i, hedgeMZ, hvertexMZ⟩ := hnewEntryFromRight j hnU
          have hrightOutside :
              Z.vertex i.succ ∉ TreeSequenceVertexSet U := by
            intro hmem
            simp only [TreeSequenceVertexSet, Finset.mem_image,
              Finset.mem_univ, true_and] at hmem
            obtain ⟨a, ha⟩ := hmem
            have hmvertex : M.vertex
                  (Fin.castLE (Nat.succ_le_succ hleftSegment.1) a) =
                U.vertex a := hleftSegment.2.1 a
            have heq : M.vertex j.succ =
                M.vertex (Fin.castLE (Nat.succ_le_succ hleftSegment.1) a) :=
              hvertexMZ.trans (ha.symm.trans hmvertex.symm)
            have hindex := congrArg Fin.val (M.vertex_injective heq)
            simp [j] at hindex
            omega
          have hiSeed : seed.length ≤ i.val := by
            by_contra hnot
            have hi : i.val < seed.length := Nat.lt_of_not_ge hnot
            let a : Fin (seed.length + 1) := ⟨i.val + 1, by omega⟩
            have hZSeedA : Z.vertex
                  (Fin.castLE (Nat.succ_le_succ hseedZSegment.1) a) =
                seed.vertex a := hseedZSegment.2.1 a
            apply hrightOutside
            simp only [TreeSequenceVertexSet, Finset.mem_image,
              Finset.mem_univ, true_and]
            refine ⟨Fin.castLE (Nat.succ_le_succ hseedU.1) a, ?_⟩
            have hia : Fin.castLE (Nat.succ_le_succ hseedZSegment.1) a =
                i.succ := Fin.ext (by simp [a])
            rw [hia] at hZSeedA
            exact (hseedU.2.1 a).trans hZSeedA.symm
          have hiZ : i.val < Z.length := i.isLt
          let ZX := TreeSequencePrefix Z i.val
            (Nat.le_trans seed.positive hiSeed) (Nat.le_of_lt hiZ)
          have hseedZX : TreeSequenceInitialSegment seed ZX := by
            refine ⟨hiSeed, ?_, ?_⟩
            · intro a
              change Z.vertex _ = seed.vertex a
              calc
                Z.vertex _ = Z.vertex
                    (Fin.castLE (Nat.succ_le_succ hseedZSegment.1) a) := by
                  congr 1
                _ = seed.vertex a := hseedZSegment.2.1 a
            · intro a
              change Z.edge _ = seed.edge a
              calc
                Z.edge _ = Z.edge (Fin.castLE hseedZSegment.1 a) := by
                  congr 1
                _ = seed.edge a := hseedZSegment.2.2 a
          have hZXZ : TreeSequenceInitialSegment ZX Z :=
            prefixSegment Z i.val (Nat.le_trans seed.positive hiSeed)
              (Nat.le_of_lt hiZ)
          have hsuffix : TashkinovAugmentationSequence phiJ ZX Z :=
            TashkinovAugmentationSequenceSuffix phiJ seed ZX Z
              hroutePhiZ hseedZX hZXZ
          have hZXlen : ZX.length = i.val := rfl
          obtain ⟨A, hZXA, hAZ⟩ := firstStep hsuffix (by omega)
          rcases hZXA with ⟨hlenA, hZXASegment, c, hcolorA, hmissingZX⟩
          have hAZSegment : TreeSequenceInitialSegment A Z :=
            TashkinovAugmentationSequenceInitialSegment phiJ A Z hAZ
          have hAi : A.length = i.val + 1 := by omega
          let ai : Fin A.length := ⟨i.val, by omega⟩
          have hcolorZ : phiJ (Z.edge i) = some c := by
            have haiLast : ai =
                Fin.cast hlenA.symm (Fin.last ZX.length) := by
              apply Fin.ext
              simp [ai, hZXlen]
            have hZai : Z.edge (Fin.castLE hAZSegment.1 ai) = A.edge ai :=
              hAZSegment.2.2 ai
            have hcast : Fin.castLE hAZSegment.1 ai = i := by
              apply Fin.ext
              simp [ai]
            rw [← hcast, hZai, haiLast]
            exact hcolorA
          have hleftX {v : V} (hvU : v ∈ TreeSequenceVertexSet U) :
              v ∈ TreeSequenceVertexSet X := by
            simp only [TreeSequenceVertexSet, Finset.mem_image,
              Finset.mem_univ, true_and] at hvU ⊢
            obtain ⟨b, hb⟩ := hvU
            refine ⟨Fin.castLE (Nat.succ_le_succ hnU) b, ?_⟩
            change M.vertex _ = v
            calc
              M.vertex _ = M.vertex
                  (Fin.castLE (Nat.succ_le_succ hleftSegment.1) b) := by
                congr 1
              _ = U.vertex b := hleftSegment.2.1 b
              _ = v := hb
          have hmissingX : c ∈ TreeMissingColors rho3 X := by
            unfold TreeMissingColors at hmissingZX ⊢
            obtain ⟨v, hvZX, hcMissing⟩ :=
              Finset.mem_biUnion.mp hmissingZX
            simp only [TreeSequenceVertexSet, Finset.mem_image,
              Finset.mem_univ, true_and] at hvZX
            obtain ⟨a, ha⟩ := hvZX
            have hcMissingV : c ∈ MissingColors G phiJ v := by
              simpa [ha] using hcMissing
            have hvX : v ∈ TreeSequenceVertexSet X := by
              by_cases hvU : v ∈ TreeSequenceVertexSet U
              · exact hleftX hvU
              · have haPos : 1 ≤ a.val := by
                  by_contra hzero
                  have haZero : a.val = 0 := by omega
                  let p0 : Fin (seed.length + 1) := ⟨0, by omega⟩
                  have hZp0 := hseedZSegment.2.1 p0
                  have hUp0 := hseedU.2.1 p0
                  apply hvU
                  simp only [TreeSequenceVertexSet, Finset.mem_image,
                    Finset.mem_univ, true_and]
                  refine ⟨Fin.castLE (Nat.succ_le_succ hseedU.1) p0, ?_⟩
                  have haZ : Z.vertex (Fin.castLE
                        (Nat.succ_le_succ (Nat.le_of_lt hiZ)) a) = v := by
                    simpa [ZX, TreeSequencePrefix] using ha
                  have ha0 : Fin.castLE
                        (Nat.succ_le_succ (Nat.le_of_lt hiZ)) a =
                      Fin.castLE (Nat.succ_le_succ hseedZSegment.1) p0 := by
                    apply Fin.ext
                    exact haZero
                  rw [ha0, hZp0] at haZ
                  exact hUp0.trans haZ
                let r : Fin Z.length := ⟨a.val - 1, by
                  have haLt : a.val < ZX.length + 1 := a.isLt
                  simp [ZX] at haLt
                  omega⟩
                have hrSucc : r.succ = Fin.castLE
                    (Nat.succ_le_succ (Nat.le_of_lt hiZ)) a := by
                  apply Fin.ext
                  exact Nat.sub_add_cancel haPos
                have hrv : Z.vertex r.succ = v := by
                  rw [hrSucc]
                  simpa [ZX, TreeSequencePrefix] using ha
                have hrOutside :
                    Z.vertex r.succ ∉ TreeSequenceVertexSet U := by
                  simpa [hrv] using hvU
                have hri : r.val < i.val := by
                  have haLt : a.val < ZX.length + 1 := a.isLt
                  simp [ZX, r] at haLt ⊢
                  omega
                obtain ⟨q, hqU, hedgeq, hvertexq⟩ :=
                  heveryNewRightEntry r hrOutside
                have hqn : q.val < n :=
                  hrightOrder r i hrOutside hrightOutside hri q j
                    hvertexq hvertexMZ
                simp only [TreeSequenceVertexSet, Finset.mem_image,
                  Finset.mem_univ, true_and]
                let qX : Fin (X.length + 1) := ⟨q.val + 1, by
                  change q.val + 1 < n + 1
                  omega⟩
                refine ⟨qX, ?_⟩
                rw [← hrv, ← hvertexq]
                change M.vertex _ = M.vertex q.succ
                congr 1
            by_cases hvTerminal : v = terminalSupport
            · have hcTerminalOld :
                  c ∈ MissingColors G phiJ terminalSupport := by
                rw [← hvTerminal]
                exact hcMissingV
              rcases Finset.mem_union.mp (hterminalInclusion hcTerminalOld) with
                hcTerminal | hcU
              · have hterminalX :
                    terminalSupport ∈ TreeSequenceVertexSet X := by
                  simpa [hvTerminal] using hvX
                exact Finset.mem_biUnion.mpr
                  ⟨terminalSupport, hterminalX, hcTerminal⟩
              · exact Finset.mem_biUnion.mpr ⟨u, hleftX huU, hcU⟩
            · have hvBefore : v ∈ TreeVerticesBefore Tj z hzTj := by
                unfold TreeVerticesBefore
                apply Finset.mem_filter.mpr
                let aZ : Fin (Z.length + 1) :=
                  Fin.castLE (Nat.succ_le_succ hZXZ.1) a
                let aTj : Fin (Tj.length + 1) :=
                  Fin.castLE (Nat.succ_le_succ hZTj.1) aZ
                have haTj : Tj.vertex aTj = v :=
                  (hZTj.2.1 aZ).trans ((hZXZ.2.1 a).trans ha)
                constructor
                · simp only [TreeSequenceVertexSet, Finset.mem_image,
                    Finset.mem_univ, true_and]
                  exact ⟨aTj, haTj⟩
                · unfold TreeVertexOrder
                  refine ⟨aTj, zPosition, haTj, hzPosition, ?_⟩
                  change a.val < zPosition.val
                  have haLt := a.isLt
                  have hiLt := i.isLt
                  simp [ZX, Z, TreeSequencePrefix] at haLt hiLt
                  omega
              refine Finset.mem_biUnion.mpr ⟨v, hvX, ?_⟩
              rw [hbeforeZMissing v hvBefore hvTerminal]
              exact hcMissingV
          have hXY : TashkinovAugmentation rho3 X Y := by
            have hlenXY : Y.length = X.length + 1 := by
              change n + 1 = n + 1
              rfl
            refine ⟨hlenXY, ?_, c, ?_, hmissingX⟩
            · simpa [X, Y] using prefixPrefix M n
                (Nat.le_trans U.positive hnU) hnSuccM
            · let iTj : Fin Tj.length := Fin.castLE hZTj.1 i
              have hiTj : iTj.val < zPosition.val := by
                change i.val < zPosition.val
                have hiLt := i.isLt
                simp [Z, TreeSequencePrefix] at hiLt
                exact hiLt
              have hedgeTj : Tj.edge iTj = Z.edge i := hZTj.2.2 i
              have hfixedZ : rho3 (Z.edge i) = phiJ (Z.edge i) := by
                calc
                  rho3 (Z.edge i) = rho1 (Z.edge i) :=
                    hd2Edges (Z.edge i) (Or.inl ⟨iTj, hiTj, hedgeTj⟩)
                  _ = phiJ (Z.edge i) := by
                    rw [← hedgeTj]
                    exact hb2Edges iTj
              have hcolorM : rho3 (M.edge j) = some c := by
                rw [hedgeMZ]
                exact hfixedZ.trans hcolorZ
              change rho3 (M.edge _) = some c
              convert hcolorM using 1
              apply congrArg rho3
              apply congrArg M.edge
              apply Fin.ext
              rfl
          change TashkinovAugmentationSequence rho3 U Y
          exact Relation.ReflTransGen.tail ih' hXY
    have hfull := replay M.length hleftSegment.1 le_rfl
    simpa [prefixSelf] using hfull
  obtain ⟨C, hclosureMC⟩ := TashkinovClosureExists rho3 M
  have hrouteUC : TashkinovAugmentationSequence rho3 U C :=
    Relation.ReflTransGen.trans hrouteUM hclosureMC.1
  have hrouteSeedC : TashkinovAugmentationSequence rho3 seed C :=
    Relation.ReflTransGen.trans hrouteRhoThreeU hrouteUC
  have hclosedC :
      ColoredVertexSetClosed G rho3 (TreeSequenceVertexSet C) :=
    hclosureMC.2
  have huM : u ∈ TreeSequenceVertexSet M := by
    rw [hunion.vertexSet]
    exact Finset.mem_union_left _ huU
  have hMCsegment : TreeSequenceInitialSegment M C :=
    TashkinovAugmentationSequenceInitialSegment rho3 M C hclosureMC.1
  have huC : u ∈ TreeSequenceVertexSet C :=
    TreeSequenceInitialSegmentVertexSetSubset hMCsegment huM
  have huNotTjm1 : u ∉ TreeSequenceVertexSet Tjm1 := by
    intro huLower
    exact huOutsideTj (Finset.mem_filter.mp (hTjm1Before huLower)).1
  have hTjm1C : TreeSequenceInitialSegment Tjm1 C := by
    rcases hseedBuildRho with hparallel | hserial
    · exact TashkinovAugmentationSequenceInitialSegment rho3 Tjm1 C
        (Relation.ReflTransGen.trans hparallel.2 hrouteSeedC)
    · rcases hserial with ⟨-, f, adjoinSeed, -, hadjoin, hroute⟩
      exact segmentTrans hadjoin.2.1
        (TashkinovAugmentationSequenceInitialSegment rho3 adjoinSeed C
          (Relation.ReflTransGen.trans hroute hrouteSeedC))
  have hTjm1StrictC : Tjm1.length < C.length := by
    have hsubset : TreeSequenceVertexSet Tjm1 ⊆ TreeSequenceVertexSet C :=
      TreeSequenceInitialSegmentVertexSetSubset hTjm1C
    have hstrictSet : TreeSequenceVertexSet Tjm1 < TreeSequenceVertexSet C :=
      Finset.ssubset_iff_subset_ne.mpr ⟨hsubset, by
        intro heq
        exact huNotTjm1 (heq.symm.subset huC)⟩
    have hcard := Finset.card_lt_card hstrictSet
    simpa [TreeSequenceVertexSet, Finset.card_image_of_injective,
      Tjm1.vertex_injective, C.vertex_injective] using hcard
  have hLowerEligible :
      ((lower.series.data.kind (Fin.last lower.rounds) =
            some TashkinovExtensionKind.PE ∧
          TashkinovAugmentationSequence rho3 Tjm1 C) ∨
        ((lower.series.data.kind (Fin.last lower.rounds) =
              some TashkinovExtensionKind.SE ∨
            lower.series.data.kind (Fin.last lower.rounds) =
              some TashkinovExtensionKind.RE) ∧
          ∃ (f : E) (adjoinSeed : TreeSequence G e0),
            lower.series.data.connectingEdges (Fin.last lower.rounds) = {f} ∧
              TreeSequenceAdjoinEdge Tjm1 f adjoinSeed ∧
              TashkinovAugmentationSequence rho3 adjoinSeed C)) := by
    rcases hseedBuildRho with hparallel | hserial
    · exact Or.inl ⟨hLowerKind.trans hparallel.1,
        Relation.ReflTransGen.trans hparallel.2 hrouteSeedC⟩
    · rcases hserial with ⟨hkind, f, adjoinSeed, hconnecting,
          hadjoin, hroute⟩
      exact Or.inr ⟨Or.imp (hLowerKind.trans) (hLowerKind.trans) hkind,
        f, adjoinSeed, hLowerConnecting.trans hconnecting, hadjoin,
        Relation.ReflTransGen.trans hroute hrouteSeedC⟩
  have hcorrNonempty :
      Nonempty (CorrespondingExtendedTashkinovTree G k e0 lower rho3 C) := by
    have hmod' := hmod
    unfold ModColoring at hmod'
    dsimp only at hmod'
    apply hmod'.2.2 C
    · rw [hLowerTree]
      exact hTjm1C
    · rw [hLowerTree]
      exact hTjm1StrictC
    · simpa [hLowerTree] using hLowerEligible
  obtain ⟨corr⟩ := hcorrNonempty
  have hreplacementMP : MaximumProperty corr.replacementETT :=
    MaximumPropertyTransport G k e0 lower rho3 hmod C corr hLowerMP
  have hCElementary :
      ColoredVertexSetElementary G rho3 (TreeSequenceVertexSet C) :=
    hLowerI C corr hreplacementMP
  have hstableAtSlot : StableColoring
      (ett.series.data.tree jSlot.castSucc.castSucc)
      (TashkinovStoredColors ett.series.data jSlot.castSucc)
      (ett.series.data.coloring jSlot.castSucc) rho3 := by
    rw [hTjm1Stored, hDprevStored, hPhiJStored]
    exact hstableLower
  have hbound : (TreeSequenceVertexSet C).card ≤
      (TreeSequenceVertexSet Tj).card := by
    have hMP' := hMP
    unfold MaximumProperty at hMP'
    have hstage := hMP'.2 jSlot.val hjPositive jSlot.isLt
    dsimp only at hstage
    have hidx : (⟨jSlot.val, by omega⟩ : Fin (ett.rounds + 1)) =
        jSlot.castSucc := by
      apply Fin.ext
      rfl
    have hnextIdx : (⟨jSlot.val + 1, by omega⟩ : Fin (ett.rounds + 2)) =
        jSlot.succ.castSucc := by
      apply Fin.ext
      rfl
    rw [hidx, hnextIdx] at hstage
    rcases hseedBuildRho with hparallel | hserial
    · have hclosureTjm1C : TashkinovClosure rho3 Tjm1 C :=
        ⟨Relation.ReflTransGen.trans hparallel.2 hrouteSeedC, hclosedC⟩
      have hraw := hstage rho3 Tjm1 C
        hrhoProper hrhoOne
        hstableAtSlot
        (by
          left
          refine ⟨?_, ?_⟩
          · exact hparallel.1
          · exact hTjm1Stored.symm)
        hclosureTjm1C
      simpa only [hTjStored] using hraw
    · rcases hserial with ⟨hkind, f, adjoinSeed, hconnecting,
          hadjoin, hroute⟩
      have hclosureAdjoinC : TashkinovClosure rho3 adjoinSeed C :=
        ⟨Relation.ReflTransGen.trans hroute hrouteSeedC, hclosedC⟩
      have hraw := hstage rho3 adjoinSeed C
        hrhoProper hrhoOne
        hstableAtSlot
        (by
          right
          refine ⟨?_, f, ?_, ?_⟩
          · exact hkind
          · exact hconnecting
          · rw [hTjm1Stored]
            exact hadjoin)
        hclosureAdjoinC
      simpa only [hTjStored] using hraw
  have hseedC : TreeSequenceInitialSegment seed C :=
    TashkinovAugmentationSequenceInitialSegment rho3 seed C hrouteSeedC
  have hterminalSeed : terminalSupport ∈ TreeSequenceVertexSet seed := by
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ,
      true_and]
    exact ⟨Fin.last seed.length, hseedTerminal⟩
  have hterminalC : terminalSupport ∈ TreeSequenceVertexSet C :=
    TreeSequenceInitialSegmentVertexSetSubset hseedC hterminalSeed
  have hZC : TreeSequenceVertexSet Z ⊆ TreeSequenceVertexSet C := by
    intro v hvZ
    have hvM : v ∈ TreeSequenceVertexSet M := by
      rw [hunion.vertexSet]
      exact Finset.mem_union_right _ hvZ
    exact TreeSequenceInitialSegmentVertexSetSubset hMCsegment hvM
  have hzZ : z ∈ TreeSequenceVertexSet Z := by
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ,
      true_and]
    refine ⟨Fin.last Z.length, ?_⟩
    change Tj.vertex (Fin.castLE (Nat.succ_le_succ hzPositionBound)
      (Fin.last zPosition.val)) = z
    have hindex : Fin.castLE (Nat.succ_le_succ hzPositionBound)
        (Fin.last zPosition.val) = zPosition := by
      apply Fin.ext
      rfl
    rw [hindex]
    exact hzPosition
  have hzC : z ∈ TreeSequenceVertexSet C := hZC hzZ
  rcases hzChoice with hzLast | hzEarlier
  · have hZlen : Z.length = Tj.length := by
      simp [Z, TreeSequencePrefix, hzLast]
    have hTjZ : TreeSequenceVertexSet Tj ⊆ TreeSequenceVertexSet Z := by
      intro v hv
      simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ,
        true_and] at hv ⊢
      obtain ⟨i, rfl⟩ := hv
      let iZ : Fin (Z.length + 1) := ⟨i.val, by omega⟩
      refine ⟨iZ, ?_⟩
      have hcast : Fin.castLE (Nat.succ_le_succ hZTj.1) iZ = i := by
        apply Fin.ext
        rfl
      rw [← hcast]
      exact hZTj.2.1 iZ
    have hTjC : TreeSequenceVertexSet Tj ⊆ TreeSequenceVertexSet C :=
      fun _ hv => hZC (hTjZ hv)
    have hstrict : TreeSequenceVertexSet Tj < TreeSequenceVertexSet C :=
      Finset.ssubset_iff_subset_ne.mpr ⟨hTjC, by
        intro heq
        exact huOutsideTj (heq.symm.subset huC)⟩
    exact (Nat.not_lt_of_ge hbound) (Finset.card_lt_card hstrict)
  · have hdeltaZ : deltaN ∈ MissingColors G rho3 z :=
      hd2Delta hzEarlier.2
    have hdeltaTerminal :
        deltaN ∈ MissingColors G rho3 terminalSupport := by
      rw [hterminalMissingEq]
      exact hdeltaRho1
    have hdisjoint := hCElementary hterminalC hzC hterminalNeZ
    exact (Finset.disjoint_left.mp hdisjoint) hdeltaTerminal hdeltaZ
