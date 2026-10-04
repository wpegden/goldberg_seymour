import Tablet.CertifiedETTRestriction
import Tablet.DefectiveVertex
import Tablet.IsOneEdgeUncolored
import Tablet.MaximumDefectiveChoice
import Tablet.MissingColors
import Tablet.ParallelExtensionColor
import Tablet.ParallelExtensionUndoStable
import Tablet.PresentColors
import Tablet.TechnicalInductionContext
import Tablet.TechnicalTheoremBase
import Tablet.TashkinovSeries
import Tablet.TashkinovSeriesStep
import Tablet.TreeInterchangeable
import Tablet.TreeMissingColors
import Tablet.TwoColorComponent
import Tablet.TwoColorComponentSwap
import Tablet.TwoColorComponentSwapProper
import Tablet.TwoColorIncidenceGraph
import Tablet.TwoColorPathComponent

-- [TABLET NODE: ParallelTerminalAwayInterchangeable]
theorem ParallelTerminalAwayInterchangeable {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (ctx : TechnicalInductionContext G k e0 ett.rounds)
    (hMP : MaximumProperty ett) (hpositive : 0 < ett.rounds)
    (hPE : ett.series.data.kind (Fin.last ett.rounds) =
      some TashkinovExtensionKind.PE)
    (sigma : PartialEdgeColoring E k)
    (hproper : IsProperEdgeColoring G sigma)
    (hone : IsOneEdgeUncolored sigma e0)
    (hstable : StableColoring
      (ett.series.data.tree (Fin.last ett.rounds).castSucc)
      (TashkinovStoredColors ett.series.data (Fin.last ett.rounds))
      phi sigma)
    (support : V) (gamma delta : Fin k)
    (hsupport : ett.series.data.chosenVertex (Fin.last ett.rounds) =
      some support)
    (hgamma : ett.series.data.gamma (Fin.last ett.rounds) = some gamma)
    (hdelta : ett.series.data.delta (Fin.last ett.rounds) = some delta) :
    let Tn := ett.series.data.tree (Fin.last ett.rounds).castSucc
    ∀ alpha beta : Fin k,
      alpha ∈ TreeMissingColors sigma Tn →
      beta ∈ TreeMissingColors sigma Tn →
      alpha ≠ gamma → alpha ≠ delta →
      beta ≠ gamma → beta ≠ delta →
      TreeInterchangeable G Tn sigma alpha beta := by
-- BODY
  classical
  dsimp only
  intro alpha beta hAlphaMissing hBetaMissing hAlphaGamma hAlphaDelta
    hBetaGamma hBetaDelta
  let terminal : Fin (ett.rounds + 1) := Fin.last ett.rounds
  let previous : Fin ett.rounds := ⟨ett.rounds - 1, by omega⟩
  have hPreviousSucc : previous.succ = terminal := by
    apply Fin.ext
    simp [previous, terminal]
    omega
  have hStableTerminal : StableColoring
      (ett.series.data.tree terminal.castSucc)
      (TashkinovStoredColors ett.series.data terminal)
      (ett.series.data.coloring terminal) sigma := by
    rw [← ett.generatingColoring]
    exact hstable
  have cert := ett.series.certified terminal
  generalize hslot : terminal = slot at cert
  cases cert with
  | initial triple seedLength initialColoring initialStored initialEdges
      initialKind initialVertex initialOutside initialDelta initialGamma
      initialClosure =>
    have hz := congrArg Fin.val hslot
    simp [terminal] at hz
    omega
  | SE ci previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternative
      currentColoring currentStored currentEdges currentKind currentVertex
      currentOutside currentDelta currentGamma adjoined adjoinedExactly
      closedExtension orderedExtension strictExtension =>
    have hterm := hPE
    change ett.series.data.kind terminal =
      some TashkinovExtensionKind.PE at hterm
    rw [hslot, currentKind] at hterm
    simp at hterm
  | RE ci previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed available currentColoring currentStored
      currentEdges currentKind currentVertex currentOutside currentDelta
      currentGamma adjoined adjoinedExactly closedExtension orderedExtension
      strictExtension =>
    have hterm := hPE
    change ett.series.data.kind terminal =
      some TashkinovExtensionKind.PE at hterm
    rw [hslot, currentKind] at hterm
    simp at hterm
  | PE ci previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternativeFails
      chosenGamma gammaRule secondStable secondStableProper
      secondStableOneUncolored secondStableRelation exitWitness
      currentColoring currentProper currentOneUncolored currentStored
      currentEdges currentKind currentVertex currentOutside currentDelta
      currentGamma closedExtension orderedExtension strictExtension =>
    have hci : ci = previous := by
      apply Fin.ext
      have hs := congrArg Fin.val hslot
      simp [terminal, previous] at hs ⊢
      omega
    subst ci
    have hTerminalEq : terminal = previous.succ := hslot
    have hLastEq : Fin.last ett.rounds = previous.succ := by
      simpa only [terminal] using hTerminalEq
    have hSupportEq : support = choice.vertex := by
      apply Option.some.inj
      exact hsupport.symm.trans (by
        rw [hLastEq]
        exact currentVertex)
    have hGammaEq : gamma = chosenGamma := by
      apply Option.some.inj
      exact hgamma.symm.trans (by
        rw [hLastEq]
        exact currentGamma)
    have hDeltaEq : delta = choice.color := by
      apply Option.some.inj
      exact hdelta.symm.trans (by
        rw [hLastEq]
        exact currentDelta)
    subst support
    subst gamma
    subst delta
    have hSupportTree : choice.vertex ∈ TreeSequenceVertexSet
        (ett.series.data.tree terminal.castSucc) := by
      simpa [hTerminalEq] using choice.vertexDefective.1
    have hGammaSecond : chosenGamma ∈ MissingColors G secondStable
        choice.vertex := by
      rw [secondStableRelation.2 choice.vertex choice.vertexDefective.1]
      exact gammaRule.1
    have hChoiceSecond : secondStable choice.edge = some choice.color := by
      have hfix := secondStableRelation.1 choice.edge
        ⟨choice.vertex, choice.vertexDefective.1, choice.edgeIncident⟩
        ⟨choice.color, Finset.mem_union_right _
          (Finset.mem_insert_self _ _), choice.edgeColor⟩
      exact hfix.trans choice.edgeColor
    have hGammaDelta : chosenGamma ≠ choice.color := by
      intro heq
      have hpresent : chosenGamma ∈ PresentColors G secondStable
          choice.vertex := by
        simp only [PresentColors, Finset.mem_filter, Finset.mem_univ,
          true_and]
        exact ⟨choice.edge, choice.edgeIncident, heq ▸ hChoiceSecond⟩
      have hnot : chosenGamma ∉ PresentColors G secondStable
          choice.vertex := by
        simpa [MissingColors] using hGammaSecond
      exact hnot hpresent
    have hComponent : ∀ w,
        w ∈ TreeSequenceVertexSet
            (ett.series.data.tree terminal.castSucc) →
        (Sum.inl w ∈ TwoColorComponent G sigma chosenGamma choice.color
            (Sum.inl choice.vertex) ↔ w = choice.vertex) := by
      exact ctx.currentFour ett rfl hMP choice.vertex chosenGamma choice.color
        hPE hsupport hgamma hdelta sigma hproper hone hStableTerminal
    obtain ⟨selected, recoveredSecond, hselectedProper, hselectedOne,
        hselectedStable, hrecoveredSecondProper, hrecoveredSecondOne,
        hrecoveredSecondStable, hcurrentSwap, hundoneSecond,
        hundoneSelected, hundonePrevious⟩ :=
      ParallelExtensionUndoStable G k ett.rounds e0 input ett.series previous
        choice.vertex chosenGamma choice.color
        (by simpa only [hPreviousSucc] using hPE)
        (by simpa only [hPreviousSucc] using hsupport)
        (by simpa only [hPreviousSucc] using hgamma)
        (by simpa only [hPreviousSucc] using hdelta)
        sigma hproper hone
        (by simpa only [hPreviousSucc] using hStableTerminal)
        (by simpa only [hPreviousSucc] using hSupportTree)
        (by simpa only [hPreviousSucc] using hComponent)
    let tau := TwoColorComponentSwap G sigma chosenGamma choice.color
      (Sum.inl choice.vertex)
    have hTauProper : IsProperEdgeColoring G tau := by
      exact TwoColorComponentSwapProper G sigma chosenGamma choice.color
        hGammaDelta hproper (Sum.inl choice.vertex)
    have hTauOne : IsOneEdgeUncolored tau e0 := by
      unfold IsOneEdgeUncolored
      constructor
      · by_cases he : Sum.inr e0 ∈
            TwoColorComponent G sigma chosenGamma choice.color
              (Sum.inl choice.vertex)
        · simp [tau, TwoColorComponentSwap, he, hone.1]
        · simp [tau, TwoColorComponentSwap, he, hone.1]
      · intro e he0
        obtain ⟨c, hc⟩ := hone.2 e he0
        by_cases he : Sum.inr e ∈
            TwoColorComponent G sigma chosenGamma choice.color
              (Sum.inl choice.vertex)
        · by_cases hcg : c = chosenGamma
          · exact ⟨choice.color, by
              simp [tau, TwoColorComponentSwap, he, hc, hcg]⟩
          · by_cases hcd : c = choice.color
            · exact ⟨chosenGamma, by
                simp [tau, TwoColorComponentSwap, he, hc, hcd,
                  hGammaDelta.symm]⟩
            · exact ⟨c, by
                simp [tau, TwoColorComponentSwap, he, hc, hcg, hcd]⟩
        · exact ⟨c, by simp [tau, TwoColorComponentSwap, he, hc]⟩
    have hTauStable : StableColoring
        (ett.series.data.tree terminal.castSucc)
        (TashkinovStoredColors ett.series.data previous.castSucc)
        (ett.series.data.coloring previous.castSucc) tau := by
      simpa [tau, hTerminalEq] using hundonePrevious
    have hOffPair (c : Fin k) (hcGamma : c ≠ chosenGamma)
        (hcDelta : c ≠ choice.color) (f : E) :
        tau f = some c ↔ sigma f = some c := by
      by_cases hf : Sum.inr f ∈
          TwoColorComponent G sigma chosenGamma choice.color
            (Sum.inl choice.vertex)
      · by_cases hfg : sigma f = some chosenGamma
        · simp [tau, TwoColorComponentSwap, hf, hfg, hcGamma.symm,
            hcDelta.symm]
        · by_cases hfd : sigma f = some choice.color
          · simp [tau, TwoColorComponentSwap, hf, hfd, hcGamma.symm,
              hcDelta.symm, hGammaDelta.symm]
          · simp [tau, TwoColorComponentSwap, hf, hfg, hfd]
      · simp [tau, TwoColorComponentSwap, hf]
    have hAlphaEdge : ∀ f, tau f = some alpha ↔ sigma f = some alpha :=
      hOffPair alpha hAlphaGamma hAlphaDelta
    have hBetaEdge : ∀ f, tau f = some beta ↔ sigma f = some beta :=
      hOffPair beta hBetaGamma hBetaDelta
    have hGraph : TwoColorIncidenceGraph G tau alpha beta =
        TwoColorIncidenceGraph G sigma alpha beta := by
      ext x y
      cases x <;> cases y <;>
        simp [TwoColorIncidenceGraph, hAlphaEdge, hBetaEdge]
    have hComponents (z : Sum V E) :
        TwoColorComponent G tau alpha beta z =
          TwoColorComponent G sigma alpha beta z := by
      unfold TwoColorComponent
      rw [hGraph]
    have hPaths (z : Sum V E) :
        TwoColorPathComponent G tau alpha beta z ↔
          TwoColorPathComponent G sigma alpha beta z := by
      simp only [TwoColorPathComponent]
      rw [hComponents z, hGraph]
    have hMissingVertex (c : Fin k) (hcGamma : c ≠ chosenGamma)
        (hcDelta : c ≠ choice.color) (v : V) :
        c ∈ MissingColors G tau v ↔ c ∈ MissingColors G sigma v := by
      simp only [MissingColors, Finset.mem_sdiff, Finset.mem_univ, true_and,
        PresentColors, Finset.mem_filter]
      simp_rw [hOffPair c hcGamma hcDelta]
    have hTreeMissing (c : Fin k) (hcGamma : c ≠ chosenGamma)
        (hcDelta : c ≠ choice.color) :
        c ∈ TreeMissingColors tau
            (ett.series.data.tree terminal.castSucc) ↔
          c ∈ TreeMissingColors sigma
            (ett.series.data.tree terminal.castSucc) := by
      simp only [TreeMissingColors, Finset.mem_biUnion]
      constructor
      · rintro ⟨v, hv, hc⟩
        exact ⟨v, hv, (hMissingVertex c hcGamma hcDelta v).mp hc⟩
      · rintro ⟨v, hv, hc⟩
        exact ⟨v, hv, (hMissingVertex c hcGamma hcDelta v).mpr hc⟩
    have hAlphaTau : alpha ∈ TreeMissingColors tau
        (ett.series.data.tree terminal.castSucc) :=
      (hTreeMissing alpha hAlphaGamma hAlphaDelta).mpr hAlphaMissing
    have hBetaTau : beta ∈ TreeMissingColors tau
        (ett.series.data.tree terminal.castSucc) :=
      (hTreeMissing beta hBetaGamma hBetaDelta).mpr hBetaMissing
    have hTauInterchangeable : TreeInterchangeable G
        (ett.series.data.tree terminal.castSucc) tau alpha beta := by
      by_cases hOne : ett.rounds = 1
      · have hbase := (TechnicalTheoremBase G k ett.rounds e0 input
            ett.series).2
        dsimp only at hbase
        have hTerminalOne : terminal.castSucc =
            (⟨1, by omega⟩ : Fin (ett.rounds + 2)) := by
          apply Fin.ext
          simp [terminal, hOne]
        have hPreviousZero : previous.castSucc =
            (0 : Fin (ett.rounds + 1)) := by
          apply Fin.ext
          simp [previous, hOne]
        have hstableBase : StableColoring
            (ett.series.data.tree ⟨1, by omega⟩)
            (TashkinovStoredColors ett.series.data 0)
            (ett.series.data.coloring 0) tau := by
          simpa only [hTerminalOne, hPreviousZero] using hTauStable
        have hinter := hbase tau hTauProper hTauOne hstableBase alpha beta
          (Or.inl (by simpa only [hTerminalOne] using hAlphaTau))
        simpa only [hTerminalOne] using hinter
      · have hrPositive : 1 ≤ ett.rounds - 1 := by omega
        have hrBefore : ett.rounds - 1 < ett.rounds := by omega
        obtain ⟨restricted, hRounds, hRestrictedMP, hTreeEq, hDataEq⟩ :=
          CertifiedETTRestriction G k e0 input T phi ett hMP
            (ett.rounds - 1) hrPositive hrBefore
        let lowerTerminal : Fin (restricted.rounds + 1) :=
          Fin.last restricted.rounds
        have hCastLower : Fin.castLE (by omega) lowerTerminal =
            previous.castSucc := by
          apply Fin.ext
          simp [lowerTerminal, previous, hRounds]
        have hLowerTree : restricted.series.data.tree
              (Fin.last (restricted.rounds + 1)) =
            ett.series.data.tree terminal.castSucc := by
          rw [hTreeEq]
          congr 1
          apply Fin.ext
          simp [terminal, hRounds]
          omega
        obtain ⟨hLowerColor, hLowerStoredRaw, hLowerEdges, hLowerKind,
            hLowerVertex, hLowerOutside, hLowerDelta, hLowerGamma,
            hLowerStored, hLowerCert⟩ := hDataEq lowerTerminal
        have hLowerColor' : restricted.series.data.coloring lowerTerminal =
            ett.series.data.coloring previous.castSucc := by
          simpa only [hCastLower] using hLowerColor
        have hLowerStored' :
            TashkinovStoredColors restricted.series.data lowerTerminal =
              TashkinovStoredColors ett.series.data previous.castSucc := by
          simpa only [hCastLower] using hLowerStored
        have hLowerStable : StableColoring
            (restricted.series.data.tree
              (Fin.last (restricted.rounds + 1)))
            (TashkinovStoredColors restricted.series.data lowerTerminal)
            (restricted.series.data.coloring lowerTerminal) tau := by
          rw [hLowerTree, hLowerStored', hLowerColor']
          exact hTauStable
        have hlower := ctx.lowerTwo restricted
          (by omega) (by omega) hRestrictedMP
        dsimp only at hlower
        have hinter := hlower tau hTauProper hTauOne hLowerStable alpha beta
          (Or.inl (by simpa only [hLowerTree] using hAlphaTau))
        simpa only [hLowerTree] using hinter
    intro z w hz hw hzTree hwTree
    have hzTau : TwoColorPathComponent G tau alpha beta z :=
      (hPaths z).mpr hz
    have hwTau : TwoColorPathComponent G tau alpha beta w :=
      (hPaths w).mpr hw
    have hzTreeTau : ∃ v ∈ TreeSequenceVertexSet
        (ett.series.data.tree terminal.castSucc),
        Sum.inl v ∈ TwoColorComponent G tau alpha beta z := by
      rcases hzTree with ⟨v, hv, hvz⟩
      exact ⟨v, hv, by simpa only [hComponents z] using hvz⟩
    have hwTreeTau : ∃ v ∈ TreeSequenceVertexSet
        (ett.series.data.tree terminal.castSucc),
        Sum.inl v ∈ TwoColorComponent G tau alpha beta w := by
      rcases hwTree with ⟨v, hv, hvw⟩
      exact ⟨v, hv, by simpa only [hComponents w] using hvw⟩
    have hinter := hTauInterchangeable z w hzTau hwTau hzTreeTau hwTreeTau
    rw [hComponents z, hComponents w] at hinter
    exact hinter
