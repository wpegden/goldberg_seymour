import Tablet.BoundaryColorVertex
import Tablet.BoundaryColorEdges
import Tablet.BoundaryEdges
import Tablet.CertifiedETTRestriction
import Tablet.DefectiveEdge
import Tablet.DefectiveVertex
import Tablet.DefectiveColor
import Tablet.ETTFirstAppearanceIndex
import Tablet.ExtendedTashkinovTree
import Tablet.ExtendedTashkinovLadderStage
import Tablet.HkuMissingStoredMonotone
import Tablet.HkuUnsupportedVertexColors
import Tablet.IsOneEdgeUncolored
import Tablet.IsProperEdgeColoring
import Tablet.MaximumProperty
import Tablet.MaximumDefectiveChoice
import Tablet.SameColorSeriesPreserved
import Tablet.StableColoring
import Tablet.StableColoringBeforeVertex
import Tablet.TashkinovExtensionKind
import Tablet.TashkinovSeries
import Tablet.TashkinovSeriesStep
import Tablet.TashkinovStoredColors
import Tablet.TreeSequence
import Tablet.TreeIncidentEdge
import Tablet.TreeMissingColors
import Tablet.TreeSequenceInitialSegment
import Tablet.TreeSequenceInitialSegmentVertexSetSubset
import Tablet.TreeSequenceVertexSet
import Tablet.TreeVertexOrder
import Tablet.TreeVerticesBefore
import Tablet.sc2

-- [TABLET NODE: ExtensionRulesTerminalEarlierAppearance]
theorem ExtensionRulesTerminalEarlierAppearance {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (generating : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T generating)
    (hMP : MaximumProperty ett) (hpositive : 0 < ett.rounds)
    (hLowerFive : ∀ {T' : TreeSequence G e0}
      {generating' : PartialEdgeColoring E k}
      (lower : ExtendedTashkinovTree G k e0 input T' generating'),
      0 < lower.rounds → lower.rounds < ett.rounds → MaximumProperty lower →
      (let n : Fin (lower.rounds + 1) := Fin.last lower.rounds
       let Tn : TreeSequence G e0 := lower.series.data.tree n.castSucc
       ∀ sigma : PartialEdgeColoring E k,
         IsProperEdgeColoring G sigma → IsOneEdgeUncolored sigma e0 →
         StableColoring Tn (TashkinovStoredColors lower.series.data n)
           (lower.series.data.coloring n) sigma →
         ∀ (delta : Fin k),
           DefectiveColor G sigma (TreeSequenceVertexSet Tn) delta →
           ∀ (v : V),
             BoundaryColorVertex G sigma (TreeSequenceVertexSet Tn) delta v →
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
               v = vi ∨ TreeVertexOrder T' v vi))
    (v : V)
    (hkind : ett.series.data.kind (Fin.last ett.rounds) =
      some TashkinovExtensionKind.PE)
    (hvertex : ett.series.data.chosenVertex (Fin.last ett.rounds) = some v)
    (hvFinal : v ∈ TreeSequenceVertexSet T)
    (j : Fin (ett.rounds + 1))
    (hfirst : ETTFirstAppearanceIndex ett v hvFinal = j.val + 1)
    (hj : j.val + 1 < ett.rounds)
    (sigma : PartialEdgeColoring E k)
    (hproper : IsProperEdgeColoring G sigma)
    (hone : IsOneEdgeUncolored sigma e0)
    (hstable : StableColoring
      (ett.series.data.tree (Fin.last ett.rounds).castSucc)
      (TashkinovStoredColors ett.series.data (Fin.last ett.rounds))
      (ett.series.data.coloring (Fin.last ett.rounds)) sigma) :
    StableColoringBeforeVertex T v hvFinal
        (TashkinovStoredColors ett.series.data j)
        (ett.series.data.coloring j) sigma ∧
      (0 < j.val →
        StableColoring (ett.series.data.tree j.castSucc)
          (TashkinovStoredColors ett.series.data j)
          (ett.series.data.coloring j) sigma) := by
-- BODY
  classical
  letI : DecidableEq V := Classical.decEq V
  have segmentRefl (A : TreeSequence G e0) :
      TreeSequenceInitialSegment A A :=
    ⟨le_rfl, (by intro i; rfl), (by intro i; rfl)⟩
  have segmentTrans {A B C : TreeSequence G e0}
      (hAB : TreeSequenceInitialSegment A B)
      (hBC : TreeSequenceInitialSegment B C) :
      TreeSequenceInitialSegment A C := by
    rcases hAB with ⟨hab, hvab, heab⟩
    rcases hBC with ⟨hbc, hvbc, hebc⟩
    refine ⟨hab.trans hbc, ?_, ?_⟩
    · intro i
      have hmid := hvbc (Fin.castLE (Nat.succ_le_succ hab) i)
      exact (by simpa using hmid.trans (hvab i))
    · intro i
      have hmid := hebc (Fin.castLE hab i)
      exact (by simpa using hmid.trans (heab i))
  have stepSegment : ∀ i : Fin (ett.rounds + 1), 0 < i.val →
      TreeSequenceInitialSegment (ett.series.data.tree i.castSucc)
        (ett.series.data.tree i.succ) := by
    intro i hi
    have cert := ett.series.certified i
    cases cert with
    | initial => exact (by simpa using hi)
    | SE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => assumption
    | PE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => assumption
    | RE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => assumption
  have stageToStage : ∀ (a b : ℕ) (_ha : 1 ≤ a) (_hab : a ≤ b)
      (_hb : b ≤ ett.rounds),
      TreeSequenceInitialSegment
        (ett.series.data.tree ⟨a, by omega⟩)
        (ett.series.data.tree ⟨b, by omega⟩) := by
    intro a b ha hab hb
    have chain : ∀ (d : ℕ) (_hd : a + d ≤ b),
        TreeSequenceInitialSegment
          (ett.series.data.tree ⟨a, by omega⟩)
          (ett.series.data.tree ⟨a + d, by omega⟩) := by
      intro d hd
      induction d with
      | zero => simpa using segmentRefl (ett.series.data.tree ⟨a, by omega⟩)
      | succ d ih =>
          have hprev := ih (by omega)
          let idx : Fin (ett.rounds + 1) := ⟨a + d, by omega⟩
          have hone := stepSegment idx (by dsimp [idx]; omega)
          have hone' : TreeSequenceInitialSegment
              (ett.series.data.tree ⟨a + d, by omega⟩)
              (ett.series.data.tree ⟨a + (d + 1), by omega⟩) := by
            simpa [idx, Nat.add_assoc] using hone
          exact segmentTrans hprev hone'
    have hchain := chain (b - a) (by omega)
    convert hchain using 1 <;> apply congrArg ett.series.data.tree <;>
      apply Fin.ext <;> simp <;> omega
  have stageToT : ∀ (a : ℕ) (_ha : 1 ≤ a)
      (_hround : a ≤ ett.rounds),
      TreeSequenceInitialSegment (ett.series.data.tree ⟨a, by omega⟩) T := by
    intro a ha hround
    exact segmentTrans (stageToStage a ett.rounds ha hround le_rfl)
      ett.abovePenultimate
  have orderTransfer : ∀ {A B : TreeSequence G e0},
      TreeSequenceInitialSegment A B → ∀ u w,
        TreeVertexOrder A u w → TreeVertexOrder B u w := by
    intro A B hAB u w huw
    rcases hAB with ⟨hlen, hvertices, _⟩
    rcases huw with ⟨iu, iw, hu, hw, hi⟩
    exact ⟨Fin.castLE (Nat.succ_le_succ hlen) iu,
      Fin.castLE (Nat.succ_le_succ hlen) iw,
      (hvertices iu).trans hu, (hvertices iw).trans hw, hi⟩
  have orderRestrict : ∀ {A B : TreeSequence G e0},
      TreeSequenceInitialSegment A B → ∀ u w,
        u ∈ TreeSequenceVertexSet A → w ∈ TreeSequenceVertexSet A →
        TreeVertexOrder B u w → TreeVertexOrder A u w := by
    intro A B hAB u w huA hwA huw
    rcases hAB with ⟨hlen, hvertices, _⟩
    rcases Finset.mem_image.mp huA with ⟨iu, _, hiu⟩
    rcases Finset.mem_image.mp hwA with ⟨iw, _, hiw⟩
    rcases huw with ⟨ju, jw, hju, hjw, hjlt⟩
    have hjuEq : ju = Fin.castLE (Nat.succ_le_succ hlen) iu := by
      apply B.vertex_injective
      exact hju.trans ((hvertices iu).trans hiu).symm
    have hjwEq : jw = Fin.castLE (Nat.succ_le_succ hlen) iw := by
      apply B.vertex_injective
      exact hjw.trans ((hvertices iw).trans hiw).symm
    exact ⟨iu, iw, hiu, hiw, by rw [hjuEq, hjwEq] at hjlt; simpa using hjlt⟩
  have ladderStageEq : ∀
      {T' : TreeSequence G e0} {generating' : PartialEdgeColoring E k}
      (lower : ExtendedTashkinovTree G k e0 input T' generating')
      (s : ℕ) (hs : lower.rounds = s) (hsn : s < ett.rounds)
      (hdisplay : T' = ett.series.data.tree ⟨s + 1, by omega⟩)
      (htree : ∀ i : Fin (lower.rounds + 2),
        lower.series.data.tree i =
          ett.series.data.tree (Fin.castLE (by omega) i))
      (i : Fin (lower.rounds + 1)),
      ExtendedTashkinovLadderStage lower i =
        ExtendedTashkinovLadderStage ett ⟨i.val, by omega⟩ := by
    intro T' generating' lower s hs hsn hdisplay htree i
    refine Fin.lastCases ?_ (fun a => ?_) i
    · have hdisplay' : T' = ett.series.data.tree
          ⟨lower.rounds + 1, by omega⟩ := by
        simpa [hs] using hdisplay
      rw [show ExtendedTashkinovLadderStage lower
          (Fin.last lower.rounds) = T' by
        unfold ExtendedTashkinovLadderStage
        exact Fin.lastCases_last]
      have hidx : (⟨(Fin.last lower.rounds).val, by omega⟩ :
          Fin (ett.rounds + 1)) =
          (⟨lower.rounds, by omega⟩ : Fin ett.rounds).castSucc := by
        apply Fin.ext
        simp
      rw [hidx]
      rw [show ExtendedTashkinovLadderStage ett
          (⟨lower.rounds, by omega⟩ : Fin ett.rounds).castSucc =
          ett.series.data.tree
            (⟨lower.rounds, by omega⟩ : Fin ett.rounds).succ.castSucc by
        unfold ExtendedTashkinovLadderStage
        exact @Fin.lastCases_castSucc ett.rounds
          (fun _ : Fin (ett.rounds + 1) => TreeSequence G e0) T
          (fun j => ett.series.data.tree j.succ.castSucc)
          (⟨lower.rounds, by omega⟩ : Fin ett.rounds)]
      exact hdisplay'.trans (congrArg ett.series.data.tree (by
        apply Fin.ext
        simp))
    · rw [show ExtendedTashkinovLadderStage lower a.castSucc =
          lower.series.data.tree a.succ.castSucc by
        unfold ExtendedTashkinovLadderStage
        exact @Fin.lastCases_castSucc lower.rounds
          (fun _ : Fin (lower.rounds + 1) => TreeSequence G e0) T'
          (fun j => lower.series.data.tree j.succ.castSucc) a]
      have hidx : (⟨(a.castSucc).val, by omega⟩ : Fin (ett.rounds + 1)) =
          (⟨a.val, by omega⟩ : Fin ett.rounds).castSucc := by
        apply Fin.ext
        rfl
      rw [hidx]
      rw [show ExtendedTashkinovLadderStage ett
          (⟨a.val, by omega⟩ : Fin ett.rounds).castSucc =
          ett.series.data.tree
            (⟨a.val, by omega⟩ : Fin ett.rounds).succ.castSucc by
        unfold ExtendedTashkinovLadderStage
        exact @Fin.lastCases_castSucc ett.rounds
          (fun _ : Fin (ett.rounds + 1) => TreeSequence G e0) T
          (fun j => ett.series.data.tree j.succ.castSucc)
          (⟨a.val, by omega⟩ : Fin ett.rounds)]
      exact (htree a.succ.castSucc).trans (congrArg ett.series.data.tree (by
        apply Fin.ext
        rfl))
  have firstAppearanceEq : ∀
      {T' : TreeSequence G e0} {generating' : PartialEdgeColoring E k}
      (lower : ExtendedTashkinovTree G k e0 input T' generating')
      (s : ℕ) (hs : lower.rounds = s) (hsn : s < ett.rounds)
      (hdisplay : T' = ett.series.data.tree ⟨s + 1, by omega⟩)
      (htree : ∀ i : Fin (lower.rounds + 2),
        lower.series.data.tree i =
          ett.series.data.tree (Fin.castLE (by omega) i))
      (x : V) (hxLower : x ∈ TreeSequenceVertexSet T')
      (hxFinal : x ∈ TreeSequenceVertexSet T)
      (hbound : ETTFirstAppearanceIndex ett x hxFinal ≤ s),
      ETTFirstAppearanceIndex lower x hxLower =
        ETTFirstAppearanceIndex ett x hxFinal := by
    intro T' generating' lower s hs hsn hdisplay htree x hxLower hxFinal hbound
    have hladders := ladderStageEq lower s hs hsn hdisplay htree
    unfold ETTFirstAppearanceIndex at hbound ⊢
    dsimp at hbound ⊢
    let lowerCandidates : Finset (Fin (lower.rounds + 1)) :=
      Finset.univ.filter fun i =>
        x ∈ TreeSequenceVertexSet (ExtendedTashkinovLadderStage lower i)
    let fullCandidates : Finset (Fin (ett.rounds + 1)) :=
      Finset.univ.filter fun i =>
        x ∈ TreeSequenceVertexSet (ExtendedTashkinovLadderStage ett i)
    have hlowerNonempty : lowerCandidates.Nonempty := by
      refine ⟨Fin.last lower.rounds, ?_⟩
      simp only [lowerCandidates, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [show ExtendedTashkinovLadderStage lower
          (Fin.last lower.rounds) = T' by
        unfold ExtendedTashkinovLadderStage
        exact Fin.lastCases_last]
      exact hxLower
    have hfullNonempty : fullCandidates.Nonempty := by
      refine ⟨Fin.last ett.rounds, ?_⟩
      simp only [fullCandidates, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [show ExtendedTashkinovLadderStage ett
          (Fin.last ett.rounds) = T by
        unfold ExtendedTashkinovLadderStage
        exact Fin.lastCases_last]
      exact hxFinal
    let ml := lowerCandidates.min' hlowerNonempty
    let mf := fullCandidates.min' hfullNonempty
    have hmfBound : mf.val < lower.rounds + 1 := by
      have hb : mf.val + 1 ≤ s := by
        dsimp [mf]
        convert hbound using 1
      omega
    let mfLower : Fin (lower.rounds + 1) := ⟨mf.val, hmfBound⟩
    have hmfMem : mfLower ∈ lowerCandidates := by
      simp only [lowerCandidates, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hladders mfLower]
      have hmem := Finset.min'_mem fullCandidates hfullNonempty
      simpa [fullCandidates, mfLower] using hmem
    have hmlMemFull : (⟨ml.val, by omega⟩ : Fin (ett.rounds + 1)) ∈
        fullCandidates := by
      simp only [fullCandidates, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [← hladders ml]
      exact (Finset.mem_filter.mp
        (Finset.min'_mem lowerCandidates hlowerNonempty)).2
    have hleOne := Finset.min'_le lowerCandidates mfLower hmfMem
    have hleTwo := Finset.min'_le fullCandidates
      (⟨ml.val, by omega⟩ : Fin (ett.rounds + 1)) hmlMemFull
    have hvals : ml.val = mf.val := by
      apply le_antisymm
      · exact Fin.le_iff_val_le_val.mp hleOne
      · exact Fin.le_iff_val_le_val.mp hleTwo
    change (lowerCandidates.min' _).val + 1 =
      (fullCandidates.min' _).val + 1
    simpa [ml, mf] using congrArg (fun z : ℕ => z + 1) hvals
  let p : Fin ett.rounds := ⟨j.val, by omega⟩
  have hpj : p.castSucc = j := by
    apply Fin.ext
    rfl
  let A := ett.series.data.tree p.succ.castSucc
  have hvA : v ∈ TreeSequenceVertexSet A := by
    unfold ETTFirstAppearanceIndex at hfirst
    dsimp at hfirst
    let candidates : Finset (Fin (ett.rounds + 1)) :=
      Finset.univ.filter fun i =>
        v ∈ TreeSequenceVertexSet (ExtendedTashkinovLadderStage ett i)
    have hfinal : candidates.Nonempty := by
      refine ⟨Fin.last ett.rounds, ?_⟩
      simp only [candidates, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [show ExtendedTashkinovLadderStage ett
          (Fin.last ett.rounds) = T by
        unfold ExtendedTashkinovLadderStage
        exact Fin.lastCases_last]
      exact hvFinal
    have hminval : (candidates.min' hfinal).val = j.val := by
      dsimp [candidates] at hfirst ⊢
      omega
    have hmem := Finset.min'_mem candidates hfinal
    have hminEq : candidates.min' hfinal = p.castSucc := by
      apply Fin.ext
      simpa [p] using hminval
    rw [hminEq] at hmem
    have hstage : ExtendedTashkinovLadderStage ett p.castSucc = A := by
      unfold ExtendedTashkinovLadderStage A
      exact @Fin.lastCases_castSucc ett.rounds
        (fun _ : Fin (ett.rounds + 1) => TreeSequence G e0) T
        (fun a => ett.series.data.tree a.succ.castSucc) p
    simpa only [candidates, Finset.mem_filter, Finset.mem_univ, true_and,
      hstage] using hmem
  have hAT : TreeSequenceInitialSegment A T := by
    simpa [A, p] using stageToT (j.val + 1) (by omega) (by omega)
  let B := TreeVerticesBefore T v hvFinal
  have beforeInA : ∀ w : V, w ∈ B → w ∈ TreeSequenceVertexSet A := by
    intro w hw
    unfold B TreeVerticesBefore at hw
    rcases Finset.mem_filter.mp hw with
      ⟨hwT, iw, iv, hiw, hiv, hlt⟩
    rcases Finset.mem_image.mp hwT with ⟨iwT, _, hiwT⟩
    rcases Finset.mem_image.mp hvA with ⟨ivA, _, hivA⟩
    rcases hAT with ⟨hlen, hvertices, _⟩
    let ivT := Fin.castLE (Nat.succ_le_succ hlen) ivA
    have hivEq : iv = ivT := by
      apply T.vertex_injective
      exact hiv.trans ((hvertices ivA).trans hivA).symm
    have hiwEq : iwT = iw := by
      apply T.vertex_injective
      exact hiwT.trans hiw.symm
    have hiBound : iwT.val < A.length + 1 := by
      rw [hivEq, ← hiwEq] at hlt
      simp [ivT] at hlt
      omega
    let iwA : Fin (A.length + 1) := ⟨iwT.val, hiBound⟩
    apply Finset.mem_image.mpr
    refine ⟨iwA, Finset.mem_univ _, ?_⟩
    have hcast : Fin.castLE (Nat.succ_le_succ hlen) iwA = iwT := by
      apply Fin.ext
      rfl
    exact (hvertices iwA).symm.trans (by simpa [hcast] using hiwT)
  generalize htarget : Fin.last ett.rounds = target
  cases ett.series.certified target with
  | initial triple seedLength initialColoring initialStored initialEdges
      initialKind initialVertex initialOutside initialDelta initialGamma
      initialClosure =>
    have hz := congrArg Fin.val htarget
    simp at hz
    omega
  | SE ci previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternative
      currentColoring currentStored currentEdges currentKind currentVertex
      currentOutside currentDelta currentGamma adjoined adjoinedExactly
      closedExtension orderedExtension strictExtension =>
    have hbad : some TashkinovExtensionKind.SE =
        some TashkinovExtensionKind.PE :=
      currentKind.symm.trans (by simpa [htarget] using hkind)
    cases hbad
  | RE ci previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed available currentColoring currentStored
      currentEdges currentKind currentVertex currentOutside currentDelta
      currentGamma adjoined adjoinedExactly closedExtension orderedExtension
      strictExtension =>
    have hbad : some TashkinovExtensionKind.RE =
        some TashkinovExtensionKind.PE :=
      currentKind.symm.trans (by simpa [htarget] using hkind)
    cases hbad
  | PE ci previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternativeFails
      gamma gammaRule secondStable secondStableProper
      secondStableOneUncolored secondStableRelation exitWitness
      currentColoring currentProper currentOneUncolored currentStored
      currentEdges currentKind currentVertex currentOutside currentDelta
      currentGamma closedExtension orderedExtension strictExtension =>
    have hciLast : ci.succ = Fin.last ett.rounds := htarget.symm
    have hciVal : ci.val + 1 = ett.rounds := by
      have h := congrArg Fin.val hciLast
      simpa using h
    have hvchoice : choice.vertex = v :=
      Option.some.inj (currentVertex.symm.trans (by simpa [htarget] using hvertex))
    let r := ett.rounds - 1
    have hrPositive : 1 ≤ r := by
      dsimp [r]
      omega
    have hrBefore : r < ett.rounds := by
      dsimp [r]
      omega
    have hrCi : r = ci.val := by
      dsimp [r]
      omega
    obtain ⟨lower, hr, hmaxLower, htree, hdata⟩ :=
      CertifiedETTRestriction G k e0 input T generating ett hMP r
        hrPositive hrBefore
    let nLower : Fin (lower.rounds + 1) := Fin.last lower.rounds
    have hnCast : Fin.castLE (by omega) nLower = ci.castSucc := by
      apply Fin.ext
      simp [nLower, hr, hrCi]
    have hnTreeCast : Fin.castLE (by omega) nLower.castSucc =
        ci.castSucc.castSucc := by
      apply Fin.ext
      simp [nLower, hr, hrCi]
    let Tn := ett.series.data.tree ci.succ.castSucc
    let P := ett.series.data.tree ci.castSucc.castSucc
    have htreeIndex : ci.succ.castSucc =
        (⟨ett.rounds, by omega⟩ : Fin (ett.rounds + 2)) := by
      apply Fin.ext
      simpa using hciVal
    have hTnT : TreeSequenceInitialSegment Tn T := by
      change TreeSequenceInitialSegment
        (ett.series.data.tree ci.succ.castSucc) T
      rw [htreeIndex]
      exact ett.abovePenultimate
    have hciPositive : 0 < ci.val := by omega
    have hPTn : TreeSequenceInitialSegment P Tn := by
      have hs := stepSegment ci.castSucc (by simpa using hciPositive)
      simpa [P, Tn] using hs
    have hAP : TreeSequenceInitialSegment A P := by
      have hs := stageToStage (j.val + 1) ci.val (by omega) (by omega) (by omega)
      convert hs using 1 <;> congr 1 <;> apply Fin.ext <;> simp [A, P, p]
    have hvP : v ∈ TreeSequenceVertexSet P :=
      TreeSequenceInitialSegmentVertexSetSubset hAP hvA
    have hvTn : v ∈ TreeSequenceVertexSet Tn :=
      TreeSequenceInitialSegmentVertexSetSubset hPTn hvP
    have hvLower : v ∈ TreeSequenceVertexSet
        (ett.series.data.tree ⟨r + 1, by omega⟩) := by
      have hidx : (⟨r + 1, by omega⟩ : Fin (ett.rounds + 2)) =
          ci.succ.castSucc := by
        apply Fin.ext
        simp [hrCi]
      simpa [hidx, Tn] using hvTn
    have hfirstEq := firstAppearanceEq lower r hr hrBefore rfl htree v
      hvLower hvFinal (by rw [hfirst]; omega)
    have hfirstLower : ETTFirstAppearanceIndex lower v hvLower = j.val + 1 := by
      rw [hfirstEq, hfirst]
    rcases hdata nLower with
      ⟨hnColor, hnRawStored, hnEdges, hnKind, hnVertex, hnOutside,
        hnDelta, hnGamma, hnStored, hnCert⟩
    have hnColor' : lower.series.data.coloring nLower =
        ett.series.data.coloring ci.castSucc := by
      rw [hnColor, hnCast]
    have hnStored' : TashkinovStoredColors lower.series.data nLower =
        TashkinovStoredColors ett.series.data ci.castSucc := by
      rw [hnStored, hnCast]
    have hnTree' : lower.series.data.tree nLower.castSucc = P := by
      rw [htree nLower.castSucc, hnTreeCast]
    have oldMissingIntoTn : TreeMissingColors
        (ett.series.data.coloring ci.castSucc) P ⊆
        TreeMissingColors (ett.series.data.coloring ci.castSucc) Tn := by
      intro c hc
      simp only [TreeMissingColors, Finset.mem_biUnion] at hc ⊢
      rcases hc with ⟨x, hx, hc⟩
      exact ⟨x, TreeSequenceInitialSegmentVertexSetSubset hPTn hx, hc⟩
    have selectedStableP : StableColoring P
        (TashkinovStoredColors ett.series.data ci.castSucc)
        (ett.series.data.coloring ci.castSucc) choice.selected := by
      constructor
      · intro f hf hcolor
        rcases hcolor with ⟨c, hc, hcf⟩
        apply choice.selectedStable.1 f
        · rcases hf with ⟨x, hx, hxf⟩
          exact ⟨x, TreeSequenceInitialSegmentVertexSetSubset hPTn hx, hxf⟩
        · refine ⟨c, ?_, hcf⟩
          rcases Finset.mem_union.mp hc with hc | hc
          · exact Finset.mem_union.mpr (Or.inl (oldMissingIntoTn hc))
          · exact Finset.mem_union.mpr (Or.inr hc)
      · intro x hx
        exact choice.selectedStable.2 x
          (TreeSequenceInitialSegmentVertexSetSubset hPTn hx)
    have hstableLower : StableColoring
        (lower.series.data.tree nLower.castSucc)
        (TashkinovStoredColors lower.series.data nLower)
        (lower.series.data.coloring nLower) choice.selected := by
      rw [hnTree', hnStored', hnColor']
      exact selectedStableP
    rcases choice.edgeDefective with ⟨delta, hdeltaDefective, hedgeDelta⟩
    have hdelta : delta = choice.color := by
      have hc := (Finset.mem_filter.mp hedgeDelta).2
      exact Option.some.inj (hc.symm.trans choice.edgeColor)
    have hcard : 1 < (BoundaryColorEdges G choice.selected
        (TreeSequenceVertexSet Tn) delta).card := by
      have hc : 2 ≤ (BoundaryColorEdges G choice.selected
          (TreeSequenceVertexSet Tn) delta).card := by
        simpa [DefectiveColor, Tn] using hdeltaDefective
      omega
    obtain ⟨g, hgDelta, hgne⟩ :=
      Finset.exists_mem_ne hcard choice.edge
    have hgBoundary : g ∈ BoundaryEdges G (TreeSequenceVertexSet Tn) :=
      (Finset.mem_filter.mp hgDelta).1
    have hgColor : choice.selected g = some choice.color := by
      have hc := (Finset.mem_filter.mp hgDelta).2
      simpa [hdelta] using hc
    have hgBoundaryData : ∃ w ∈ TreeSequenceVertexSet Tn,
        ∃ z ∉ TreeSequenceVertexSet Tn, G.ends g = s(w, z) := by
      simpa only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and]
        using hgBoundary
    obtain ⟨w, hwTn, z, hzTn, hgEnds⟩ := hgBoundaryData
    have hwg : Incident G w g := by
      simp [Incident, hgEnds]
    have hwDefective : DefectiveVertex G choice.selected
        (TreeSequenceVertexSet Tn) w := by
      refine ⟨hwTn, g, ?_, hwg⟩
      exact ⟨delta, by simpa [Tn] using hdeltaDefective,
        by simpa [Tn] using hgDelta⟩
    have hwChoice := choice.maximal choice.selected w choice.selectedProper
      choice.selectedOneUncolored choice.selectedStable (by simpa [Tn] using hwDefective)
    have hwne : w ≠ choice.vertex := by
      intro heq
      have hadj : AdjacentEdges G choice.edge g :=
        ⟨choice.vertex, choice.edgeIncident, heq ▸ hwg⟩
      exact choice.selectedProper hgne.symm hadj choice.edgeColor hgColor
    have hwOrderN : TreeVertexOrder Tn w choice.vertex := by
      simpa [Tn] using hwChoice.resolve_left hwne
    have hwOrderT : TreeVertexOrder T w v := by
      simpa [hvchoice] using orderTransfer hTnT w choice.vertex hwOrderN
    have hwB : w ∈ B := by
      apply Finset.mem_filter.mpr
      exact ⟨TreeSequenceInitialSegmentVertexSetSubset hTnT hwTn, hwOrderT⟩
    have hwP : w ∈ TreeSequenceVertexSet P :=
      TreeSequenceInitialSegmentVertexSetSubset hAP (beforeInA w hwB)
    have hzP : z ∉ TreeSequenceVertexSet P := by
      intro hz
      exact hzTn (TreeSequenceInitialSegmentVertexSetSubset hPTn hz)
    have hotherP : choice.otherEndpoint ∉ TreeSequenceVertexSet P := by
      intro hx
      exact choice.otherOutside
        (TreeSequenceInitialSegmentVertexSetSubset hPTn hx)
    have hedgeP : choice.edge ∈ BoundaryColorEdges G choice.selected
        (TreeSequenceVertexSet P) choice.color := by
      simp only [BoundaryColorEdges, Finset.mem_filter]
      refine ⟨?_, choice.edgeColor⟩
      simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨v, hvP, choice.otherEndpoint, hotherP, by simpa [hvchoice] using choice.edgeEnds⟩
    have hgP : g ∈ BoundaryColorEdges G choice.selected
        (TreeSequenceVertexSet P) choice.color := by
      simp only [BoundaryColorEdges, Finset.mem_filter]
      refine ⟨?_, hgColor⟩
      simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨w, hwP, z, hzP, hgEnds⟩
    have hdefectiveP : DefectiveColor G choice.selected
        (TreeSequenceVertexSet P) choice.color := by
      unfold DefectiveColor
      have hc : 1 < (BoundaryColorEdges G choice.selected
          (TreeSequenceVertexSet P) choice.color).card :=
        Finset.one_lt_card.mpr ⟨choice.edge, hedgeP, g, hgP, hgne.symm⟩
      omega
    have hvBoundaryP : BoundaryColorVertex G choice.selected
        (TreeSequenceVertexSet P) choice.color v := by
      exact ⟨hvP, choice.edge, hedgeP, by simpa [hvchoice] using choice.edgeIncident⟩
    have hwBoundaryP : BoundaryColorVertex G choice.selected
        (TreeSequenceVertexSet P) choice.color w :=
      ⟨hwP, g, hgP, hwg⟩
    have hdefectiveLower : DefectiveColor G choice.selected
        (TreeSequenceVertexSet (lower.series.data.tree nLower.castSucc))
        choice.color := by
      rw [hnTree']
      exact hdefectiveP
    have hvBoundaryLower : BoundaryColorVertex G choice.selected
        (TreeSequenceVertexSet (lower.series.data.tree nLower.castSucc))
        choice.color v := by
      rw [hnTree']
      exact hvBoundaryP
    have hwBoundaryLower : BoundaryColorVertex G choice.selected
        (TreeSequenceVertexSet (lower.series.data.tree nLower.castSucc))
        choice.color w := by
      rw [hnTree']
      exact hwBoundaryP
    have hwOrderLower : TreeVertexOrder
        (lower.series.data.tree nLower.castSucc) w v := by
      rw [hnTree']
      apply orderRestrict hPTn w v hwP hvP
      simpa [hvchoice] using hwOrderN
    have hlowerFive := hLowerFive lower (by omega) (by omega) hmaxLower
      choice.selected choice.selectedProper choice.selectedOneUncolored
      hstableLower choice.color hdefectiveLower v hvBoundaryLower
      ⟨w, hwBoundaryLower, hwOrderLower⟩
    have orderAsymm : ∀ {x y : V}, TreeVertexOrder T x y →
        ¬ (y = x ∨ TreeVertexOrder T y x) := by
      intro x y hxy hrev
      rcases hxy with ⟨ix, iy, hx, hy, hlt⟩
      rcases hrev with hEq | hyx
      · have hy' : T.vertex iy = x := hy.trans hEq
        have : ix = iy := T.vertex_injective (hx.trans hy'.symm)
        omega
      · rcases hyx with ⟨jy, jx, hy', hx', hrev⟩
        have hiy : iy = jy := T.vertex_injective (hy.trans hy'.symm)
        have hix : ix = jx := T.vertex_injective (hx.trans hx'.symm)
        omega
    have retainedOrder : ∀ (t : Fin ett.rounds) (vi : V),
        p.val ≤ t.val → t.val < ci.val →
        (ett.series.data.kind t.succ = some TashkinovExtensionKind.PE ∨
          ett.series.data.kind t.succ = some TashkinovExtensionKind.SE) →
        ett.series.data.chosenVertex t.succ = some vi →
        v = vi ∨ TreeVertexOrder T v vi := by
      intro t vi hpt htci hkindT hvertexT
      let tLower : Fin lower.rounds := ⟨t.val, by omega⟩
      have htCast : Fin.castLE (by omega) tLower.succ = t.succ := by
        apply Fin.ext
        rfl
      rcases hdata tLower.succ with
        ⟨_, _, _, htKind, htVertex, _, _, _, _, _⟩
      have hkindLower :
          lower.series.data.kind tLower.succ = some TashkinovExtensionKind.PE ∨
            lower.series.data.kind tLower.succ = some TashkinovExtensionKind.SE := by
        rw [htKind, htCast]
        exact hkindT
      have hvertexLower : lower.series.data.chosenVertex tLower.succ = some vi := by
        rw [htVertex, htCast]
        exact hvertexT
      have hresult := hlowerFive hvLower tLower vi hkindLower hvertexLower
        (calc
          ETTFirstAppearanceIndex lower v hvLower = j.val + 1 := hfirstLower
          _ ≤ tLower.val + 1 := by dsimp [tLower, p] at ⊢ hpt; omega)
      rcases hresult with rfl | horder
      · exact Or.inl rfl
      · have hdisplay : ett.series.data.tree ⟨r + 1, by omega⟩ = Tn := by
          apply congrArg ett.series.data.tree
          apply Fin.ext
          change r + 1 = ci.val + 1
          rw [hrCi]
        rw [hdisplay] at horder
        exact Or.inr (orderTransfer hTnT v vi horder)
    have unsupportedBefore : ∀ (x : V), x ∈ B → ∀ t : Fin ett.rounds,
        p.val ≤ t.val → t.val ≤ ci.val →
        ¬ (ett.series.data.kind t.succ = some TashkinovExtensionKind.PE ∧
          ett.series.data.chosenVertex t.succ = some x) := by
      intro x hx t hpt htci hsupport
      have hxOrder : TreeVertexOrder T x v := (Finset.mem_filter.mp hx).2
      by_cases heq : t = ci
      · subst t
        have hxv : x = v := Option.some.inj
          (hsupport.2.symm.trans (by simpa [hciLast] using hvertex))
        exact orderAsymm hxOrder (Or.inl hxv.symm)
      · have hord := retainedOrder t x hpt (by
          have hneval : t.val ≠ ci.val := fun h => heq (Fin.ext h)
          omega) (Or.inl hsupport.1) hsupport.2
        exact orderAsymm hxOrder hord
    have controlCarryNat : ∀ (n : ℕ), p.val ≤ n → n < ett.rounds →
        ∀ t : Fin ett.rounds, t.val = n →
        TreeMissingColors (ett.series.data.coloring p.castSucc) A ∪
              TashkinovStoredColors ett.series.data p.castSucc ⊆
          TreeMissingColors (ett.series.data.coloring t.succ)
              (ett.series.data.tree t.succ.castSucc) ∪
            TashkinovStoredColors ett.series.data t.succ := by
      intro n hpn
      induction n, hpn using Nat.le_induction with
      | base =>
          intro hn t ht
          have htp : t = p := by
            apply Fin.ext
            simpa using ht
          subst t
          simpa [A] using
            (HkuMissingStoredMonotone G k ett.rounds e0 input ett.series p).1
      | succ n hn ih =>
          intro hn t ht
          let prev : Fin ett.rounds := ⟨n, by omega⟩
          have hprev := ih (by omega) prev rfl
          have hexpand :=
            (HkuMissingStoredMonotone G k ett.rounds e0 input ett.series prev).2
          have hnext :=
            (HkuMissingStoredMonotone G k ett.rounds e0 input ett.series t).1
          have hcolor : t.castSucc = prev.succ := by
            apply Fin.ext
            simp [prev, ht]
          have htree : t.succ.castSucc = prev.succ.succ := by
            apply Fin.ext
            simp [prev, ht]
          intro c hc
          have hcExpanded := hexpand (hprev hc)
          rw [hcolor, htree] at hnext
          simpa only [htree] using hnext hcExpanded
    have controlCarry : ∀ (t : Fin ett.rounds), p.val ≤ t.val →
        TreeMissingColors (ett.series.data.coloring p.castSucc) A ∪
              TashkinovStoredColors ett.series.data p.castSucc ⊆
          TreeMissingColors (ett.series.data.coloring t.succ)
              (ett.series.data.tree t.succ.castSucc) ∪
            TashkinovStoredColors ett.series.data t.succ := by
      intro t hpt
      exact controlCarryNat t.val hpt t.isLt t rfl
    have hpci : p.val ≤ ci.val := by
      dsimp [p]
      omega
    have hATn : TreeSequenceInitialSegment A Tn := segmentTrans hAP hPTn
    have oldControlInA : ∀ c : Fin k,
        c ∈ (B.biUnion fun x =>
              MissingColors G (ett.series.data.coloring p.castSucc) x) ∪
            TashkinovStoredColors ett.series.data p.castSucc →
          c ∈ TreeMissingColors (ett.series.data.coloring p.castSucc) A ∪
            TashkinovStoredColors ett.series.data p.castSucc := by
      intro c hc
      rcases Finset.mem_union.mp hc with hc | hc
      · apply Finset.mem_union.mpr
        left
        simp only [Finset.mem_biUnion] at hc
        rcases hc with ⟨x, hx, hc⟩
        simp only [TreeMissingColors, Finset.mem_biUnion]
        exact ⟨x, beforeInA x hx, hc⟩
      · exact Finset.mem_union.mpr (Or.inr hc)
    have hstableN : StableColoring Tn
        (TashkinovStoredColors ett.series.data ci.succ)
        (ett.series.data.coloring ci.succ) sigma := by
      simpa [Tn, hciLast] using hstable
    have beforeMissingSeries : ∀ x : V, x ∈ B →
        MissingColors G (ett.series.data.coloring p.castSucc) x =
          MissingColors G (ett.series.data.coloring ci.succ) x := by
      intro x hx
      exact HkuUnsupportedVertexColors G k ett.rounds e0 input ett.series
        ci p x hpci (beforeInA x hx) (unsupportedBefore x hx)
    have exceptionImpossible : ∀ (f : E),
        (∃ x ∈ B, Incident G x f) →
        ¬ (∃ t : Fin ett.rounds, p.val ≤ t.val ∧ t.val ≤ ci.val ∧
          ett.series.data.kind t.succ = some TashkinovExtensionKind.PE ∧
          ett.series.data.connectingEdges t.succ = {f}) := by
      intro f hf hexception
      rcases hf with ⟨x, hx, hxf⟩
      rcases hexception with ⟨t, hpt, htci, htKind, htEdges⟩
      have cert := ett.series.certified t.succ
      generalize hslot : t.succ = slot at cert
      cases cert with
      | initial triple seedLength initialColoring initialStored initialEdges
          initialKind initialVertex initialOutside initialDelta initialGamma
          initialClosure =>
        exact (Fin.succ_ne_zero t hslot).elim
      | SE ti previousProper previousOneUncolored previousClosed
          previousNotStronglyClosed noRevisiting choiceT seriesAlternative
          currentColoring currentStored currentEdgesT currentKindT currentVertexT
          currentOutside currentDelta currentGamma adjoined adjoinedExactly
          closedExtension orderedExtension strictExtension =>
        have hbad : some TashkinovExtensionKind.SE =
            some TashkinovExtensionKind.PE :=
          currentKindT.symm.trans (by simpa [hslot] using htKind)
        cases hbad
      | RE ti previousProper previousOneUncolored previousClosed
          previousNotStronglyClosed available currentColoring currentStored
          currentEdgesT currentKindT currentVertexT currentOutside currentDelta
          currentGamma adjoined adjoinedExactly closedExtension orderedExtension
          strictExtension =>
        have hbad : some TashkinovExtensionKind.RE =
            some TashkinovExtensionKind.PE :=
          currentKindT.symm.trans (by simpa [hslot] using htKind)
        cases hbad
      | PE ti previousProper previousOneUncolored previousClosed
          previousNotStronglyClosed noRevisiting choiceT seriesAlternativeFails
          gammaT gammaRuleT secondStableT secondStableProperT
          secondStableOneUncoloredT secondStableRelationT exitWitnessT
          currentColoringT currentProperT currentOneUncoloredT currentStoredT
          currentEdgesT currentKindT currentVertexT currentOutsideT currentDeltaT
          currentGammaT closedExtensionT orderedExtensionT strictExtensionT =>
        have hti : ti = t := by
          apply Fin.ext
          have hv := congrArg Fin.val hslot
          simp at hv ⊢
          omega
        subst ti
        have hedgeEq : choiceT.edge = f := by
          apply Finset.singleton_inj.mp
          exact currentEdgesT.symm.trans (by simpa [hslot] using htEdges)
        have hAStage : TreeSequenceInitialSegment A
            (ett.series.data.tree t.succ.castSucc) := by
          have hs := stageToStage (j.val + 1) (t.val + 1)
            (by omega) (by dsimp [p] at hpt; omega) (by omega)
          convert hs using 1 <;> congr 1 <;> apply Fin.ext <;> simp [A, p]
        have hxStage : x ∈ TreeSequenceVertexSet
            (ett.series.data.tree t.succ.castSucc) :=
          TreeSequenceInitialSegmentVertexSetSubset hAStage (beforeInA x hx)
        have hxEnds : x = choiceT.vertex ∨ x = choiceT.otherEndpoint := by
          change x ∈ G.ends f at hxf
          rw [← hedgeEq, choiceT.edgeEnds] at hxf
          simpa using hxf
        have hxSupport : choiceT.vertex = x := by
          rcases hxEnds with hxv | hxo
          · exact hxv.symm
          · exact (choiceT.otherOutside (hxo ▸ hxStage)).elim
        apply unsupportedBefore x hx t hpt htci
        refine ⟨htKind, ?_⟩
        have hchosenT : ett.series.data.chosenVertex t.succ =
            some choiceT.vertex := by
          simpa [hslot] using currentVertexT
        exact hchosenT.trans (congrArg some hxSupport)
    have seriesEdgeEq : ∀ (f : E), (∃ x ∈ B, Incident G x f) →
        (∃ c ∈ (B.biUnion fun x =>
              MissingColors G (ett.series.data.coloring p.castSucc) x) ∪
            TashkinovStoredColors ett.series.data p.castSucc,
          ett.series.data.coloring p.castSucc f = some c) →
        ett.series.data.coloring ci.succ f =
          ett.series.data.coloring p.castSucc f := by
      intro f hf hcolor
      rcases hcolor with ⟨c, hc, hfc⟩
      have hfA : TreeIncidentEdge A f := by
        rcases hf with ⟨x, hx, hxf⟩
        exact ⟨x, beforeInA x hx, hxf⟩
      have hcA := oldControlInA c hc
      have hsame := SameColorSeriesPreserved G k ett.rounds e0 input
        ett.series p ci hpci f c (by simpa [A] using hfA) hfc
        (by simpa [A] using hcA)
      rcases hsame.1 with hkeep | hexception
      · exact hkeep
      · exact (exceptionImpossible f hf hexception).elim
    have beforeStable : StableColoringBeforeVertex T v hvFinal
        (TashkinovStoredColors ett.series.data p.castSucc)
        (ett.series.data.coloring p.castSucc) sigma := by
      unfold StableColoringBeforeVertex
      change (∀ f, (∃ x ∈ B, Incident G x f) → _ → _) ∧ _
      constructor
      · intro f hf hcolor
        rcases hcolor with ⟨c, hc, hfc⟩
        have hfN : TreeIncidentEdge Tn f := by
          rcases hf with ⟨x, hx, hxf⟩
          exact ⟨x, TreeSequenceInitialSegmentVertexSetSubset hATn
            (beforeInA x hx), hxf⟩
        have hcA := oldControlInA c hc
        have hcN := controlCarry ci hpci hcA
        have hcurrent := seriesEdgeEq f hf ⟨c, hc, hfc⟩
        have hsigma : sigma f = ett.series.data.coloring ci.succ f :=
          hstableN.1 f hfN ⟨c, hcN, hcurrent.trans hfc⟩
        exact hsigma.trans hcurrent
      · intro x hx
        have hxN := TreeSequenceInitialSegmentVertexSetSubset hATn
          (beforeInA x hx)
        exact (hstableN.2 x hxN).trans (beforeMissingSeries x hx).symm
    constructor
    · simpa [hpj] using beforeStable
    · intro hjPositive
      let Q := ett.series.data.tree p.castSucc.castSucc
      have hpPositive : 0 < p.val := by
        simpa [p] using hjPositive
      have hQA : TreeSequenceInitialSegment Q A := by
        have hs := stepSegment p.castSucc (by simpa using hpPositive)
        simpa [Q, A] using hs
      have hvNotQ : v ∉ TreeSequenceVertexSet Q := by
        intro hvQ
        let u : Fin ett.rounds := ⟨p.val - 1, by omega⟩
        have hup : u.succ = p.castSucc := by
          apply Fin.ext
          simp [u]
          exact Nat.sub_add_cancel hpPositive
        have hvStage : v ∈ TreeSequenceVertexSet
            (ExtendedTashkinovLadderStage ett u.castSucc) := by
          rw [show ExtendedTashkinovLadderStage ett u.castSucc =
              ett.series.data.tree u.succ.castSucc by
            unfold ExtendedTashkinovLadderStage
            exact @Fin.lastCases_castSucc ett.rounds
              (fun _ : Fin (ett.rounds + 1) => TreeSequence G e0) T
              (fun a => ett.series.data.tree a.succ.castSucc) u]
          rw [hup]
          exact hvQ
        have hbound : ETTFirstAppearanceIndex ett v hvFinal ≤ p.val := by
          unfold ETTFirstAppearanceIndex
          dsimp
          have hmem : u.castSucc ∈
              Finset.univ.filter
                (fun a : Fin (ett.rounds + 1) =>
                  v ∈ TreeSequenceVertexSet
                    (ExtendedTashkinovLadderStage ett a)) := by
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            exact hvStage
          have hle := Finset.min'_le
            (Finset.univ.filter
              (fun a : Fin (ett.rounds + 1) =>
                v ∈ TreeSequenceVertexSet
                  (ExtendedTashkinovLadderStage ett a))) u.castSucc hmem
          have hnat := Fin.le_iff_val_le_val.mp hle
          rw [Fin.val_castSucc] at hnat
          calc
            _ + 1 ≤ u.val + 1 := Nat.succ_le_succ hnat
            _ = p.val := by
              simp [u]
              exact Nat.sub_add_cancel hpPositive
        have hfirstP : ETTFirstAppearanceIndex ett v hvFinal = p.val + 1 := by
          simpa [p] using hfirst
        omega
      have qInBefore : ∀ x : V, x ∈ TreeSequenceVertexSet Q → x ∈ B := by
        intro x hx
        have hxA := TreeSequenceInitialSegmentVertexSetSubset hQA hx
        have hxT := TreeSequenceInitialSegmentVertexSetSubset hAT hxA
        apply Finset.mem_filter.mpr
        refine ⟨hxT, ?_⟩
        rcases hQA with ⟨hlen, hvertices, _⟩
        rcases Finset.mem_image.mp hx with ⟨ix, _, hix⟩
        rcases Finset.mem_image.mp hvA with ⟨iv, _, hiv⟩
        have hleniv : Q.length < iv.val := by
          by_contra hnot
          have hivBound : iv.val < Q.length + 1 := by omega
          let ivQ : Fin (Q.length + 1) := ⟨iv.val, hivBound⟩
          apply hvNotQ
          apply Finset.mem_image.mpr
          refine ⟨ivQ, Finset.mem_univ _, ?_⟩
          calc
            Q.vertex ivQ =
                A.vertex (Fin.castLE (Nat.succ_le_succ hlen) ivQ) :=
              (hvertices ivQ).symm
            _ = A.vertex iv := by
              congr 1
            _ = v := hiv
        have horderA : TreeVertexOrder A x v := by
          refine ⟨Fin.castLE (Nat.succ_le_succ hlen) ix, iv,
            (hvertices ix).trans hix, hiv, ?_⟩
          have hixBound : ix.val ≤ Q.length := by omega
          simp only [Fin.val_castLE]
          omega
        exact orderTransfer hAT x v horderA
      have stableQ : StableColoring Q
          (TashkinovStoredColors ett.series.data p.castSucc)
          (ett.series.data.coloring p.castSucc) sigma := by
        constructor
        · intro f hf hcolor
          rcases hf with ⟨x, hx, hxf⟩
          rcases hcolor with ⟨c, hc, hfc⟩
          apply beforeStable.1 f ⟨x, qInBefore x hx, hxf⟩
          refine ⟨c, ?_, hfc⟩
          rcases Finset.mem_union.mp hc with hc | hc
          · apply Finset.mem_union.mpr
            left
            simp only [TreeMissingColors, Finset.mem_biUnion] at hc
            rcases hc with ⟨z, hz, hzc⟩
            simp only [Finset.mem_biUnion]
            exact ⟨z, qInBefore z hz, hzc⟩
          · exact Finset.mem_union.mpr (Or.inr hc)
        · intro x hx
          exact beforeStable.2 x (qInBefore x hx)
      simpa [Q, hpj] using stableQ
