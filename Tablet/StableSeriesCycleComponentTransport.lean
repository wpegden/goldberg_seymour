import Tablet.HkuMissingStoredMonotone
import Tablet.InternalEdges
import Tablet.IsProperEdgeColoring
import Tablet.SameColorSeriesPreserved
import Tablet.sc2
import Tablet.StableColoring
import Tablet.TashkinovSeries
import Tablet.TashkinovSeriesStep
import Tablet.TashkinovStoredColors
import Tablet.TwoColorComponent
import Tablet.TwoColorComponentCycle
import Tablet.TwoColorIncidenceGraph

-- [TABLET NODE: StableSeriesCycleComponentTransport]
theorem StableSeriesCycleComponentTransport {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : LooplessMultigraph V E} {k rounds : ℕ} {e0 : E}
    {input : PartialEdgeColoring E k}
    (series : TashkinovSeries G k rounds e0 input)
    (t epsilon terminal : Fin rounds) (gamma delta : Fin k)
    (htEpsilon : t.val < epsilon.val)
    (hepsilonTerminal : epsilon.val ≤ terminal.val)
    (htKind : series.data.kind t.succ =
      some TashkinovExtensionKind.PE)
    (htGamma : series.data.gamma t.succ = some gamma)
    (htDelta : series.data.delta t.succ = some delta)
    (hintervening : ∀ r : Fin rounds,
      t.val < r.val → r.val < epsilon.val →
      series.data.kind r.succ = some TashkinovExtensionKind.RE)
    (hterminalKind : series.data.kind terminal.succ =
      some TashkinovExtensionKind.PE)
    (sigma : PartialEdgeColoring E k)
    (hsigmaProper : IsProperEdgeColoring G sigma)
    (hsigmaOne : IsOneEdgeUncolored sigma e0)
    (hsigmaStable : StableColoring
      (series.data.tree terminal.succ.castSucc)
      (TashkinovStoredColors series.data terminal.succ)
      (series.data.coloring terminal.succ) sigma)
    (z : Sum V E)
    (hcycle : TwoColorComponentCycle G
      (series.data.coloring t.succ) gamma delta z)
    (hcontained : ∀ w : V,
      Sum.inl w ∈ TwoColorComponent G
        (series.data.coloring t.succ) gamma delta z →
      w ∈ TreeSequenceVertexSet
        (series.data.tree epsilon.succ.castSucc)) :
    TwoColorComponent G sigma gamma delta z =
        TwoColorComponent G (series.data.coloring t.succ) gamma delta z ∧
      TwoColorComponentCycle G sigma gamma delta z := by
-- BODY
  classical
  let oldColoring := series.data.coloring t.succ
  let terminalColoring := series.data.coloring terminal.succ
  let epsilonTree := series.data.tree epsilon.succ.castSucc
  let terminalTree := series.data.tree terminal.succ.castSucc
  let terminalStored := TashkinovStoredColors series.data terminal.succ
  let oldGraph := TwoColorIncidenceGraph G oldColoring gamma delta
  let terminalGraph := TwoColorIncidenceGraph G terminalColoring gamma delta
  let sigmaGraph := TwoColorIncidenceGraph G sigma gamma delta
  let oldComponent := TwoColorComponent G oldColoring gamma delta z
  let terminalComponent := TwoColorComponent G terminalColoring gamma delta z
  let sigmaComponent := TwoColorComponent G sigma gamma delta z

  have currentStoredControl (q : Fin rounds) (c : Fin k)
      (hc : c ∈ series.data.stored q.succ) :
      c ∈ TreeMissingColors (series.data.coloring q.succ)
            (series.data.tree q.succ.castSucc) ∪
          TashkinovStoredColors series.data q.succ := by
    by_cases hm : c ∈ TreeMissingColors (series.data.coloring q.succ)
        (series.data.tree q.succ.castSucc)
    · exact Finset.mem_union.mpr (Or.inl hm)
    · apply Finset.mem_union.mpr
      right
      unfold TashkinovStoredColors
      simp [hm]
      refine ⟨⟨q.succ, ?_⟩, ?_⟩
      · simpa using hc
      · simpa using hm

  have hpairControl : ∀ c : Fin k, c = gamma ∨ c = delta →
      c ∈ TreeMissingColors (series.data.coloring t.succ)
            (series.data.tree t.succ.castSucc) ∪
          TashkinovStoredColors series.data t.succ := by
    intro c hc
    have cert := series.certified t.succ
    generalize hslot : t.succ = slot at cert
    cases cert with
    | initial triple seedLength initialColoring initialStored initialEdges
        initialKind initialVertex initialOutside initialDelta initialGamma
        initialClosure =>
        exact (Fin.succ_ne_zero t hslot).elim
    | SE i previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed noRevisiting choice seriesAlternative
        currentColoring currentStored currentEdges currentKind currentVertex
        currentOutside currentDelta currentGamma adjoined adjoinedExactly
        closedExtension orderedExtension strictExtension =>
        have hi : i = t := by
          apply Fin.ext
          have := congrArg Fin.val hslot
          simp only [Fin.val_succ] at this
          omega
        subst i
        rw [currentKind] at htKind
        simp at htKind
    | PE i previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed noRevisiting choice seriesAlternativeFails
        actualGamma gammaRule secondStable secondStableProper
        secondStableOneUncolored secondStableRelation exitWitness
        currentColoring currentProper currentOneUncolored currentStored
        currentEdges currentKind currentVertex currentOutside currentDelta
        currentGamma closedExtension orderedExtension strictExtension =>
        have hi : i = t := by
          apply Fin.ext
          have := congrArg Fin.val hslot
          simp only [Fin.val_succ] at this
          omega
        subst i
        have hgamma : actualGamma = gamma :=
          Option.some.inj (currentGamma.symm.trans htGamma)
        have hdelta : choice.color = delta :=
          Option.some.inj (currentDelta.symm.trans htDelta)
        apply currentStoredControl t c
        rw [currentStored]
        rcases hc with rfl | rfl
        · simp [hgamma]
        · simp [hdelta]
    | RE i previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed available currentColoring currentStored
        currentEdges currentKind currentVertex currentOutside currentDelta
        currentGamma adjoined adjoinedExactly closedExtension orderedExtension
        strictExtension =>
        have hi : i = t := by
          apply Fin.ext
          have := congrArg Fin.val hslot
          simp only [Fin.val_succ] at this
          omega
        subst i
        rw [currentKind] at htKind
        simp at htKind

  have hgammaStart := hpairControl gamma (Or.inl rfl)
  have hdeltaStart := hpairControl delta (Or.inr rfl)

  have controlPrevious (c : Fin k)
      (hc : c ∈ TreeMissingColors (series.data.coloring t.succ)
            (series.data.tree t.succ.castSucc) ∪
          TashkinovStoredColors series.data t.succ) :
      ∀ n : ℕ, t.val + 1 ≤ n → n ≤ terminal.val →
        ∀ q : Fin rounds, q.val = n →
          c ∈ TreeMissingColors (series.data.coloring q.castSucc)
                (series.data.tree q.succ.castSucc) ∪
              TashkinovStoredColors series.data q.castSucc := by
    intro n htn
    induction n, htn using Nat.le_induction with
    | base =>
        intro hn q hq
        have hcolor : q.castSucc = t.succ := by
          apply Fin.ext
          simp only [Fin.val_castSucc, Fin.val_succ]
          omega
        have htree : q.succ.castSucc = t.succ.succ := by
          apply Fin.ext
          simp only [Fin.val_castSucc, Fin.val_succ]
          omega
        simpa [hcolor, htree] using
          (HkuMissingStoredMonotone G k rounds e0 input series t).2 hc
    | succ n hn ih =>
        intro hnterminal q hq
        let r : Fin rounds := ⟨n, by omega⟩
        have hold := ih (by omega) r rfl
        have hcurrent :=
          (HkuMissingStoredMonotone G k rounds e0 input series r).1 hold
        have hnext :=
          (HkuMissingStoredMonotone G k rounds e0 input series r).2 hcurrent
        have hcolor : q.castSucc = r.succ := by
          apply Fin.ext
          simp [r, hq]
        have htree : q.succ.castSucc = r.succ.succ := by
          apply Fin.ext
          simp [r, hq]
        simpa [hcolor, htree] using hnext

  have htTerminal : t.val < terminal.val := by omega
  have hgammaEpsilon : gamma ∈
      TreeMissingColors (series.data.coloring epsilon.castSucc) epsilonTree ∪
        TashkinovStoredColors series.data epsilon.castSucc := by
    simpa [epsilonTree] using
      controlPrevious gamma hgammaStart epsilon.val (by omega)
        hepsilonTerminal epsilon rfl
  have hdeltaEpsilon : delta ∈
      TreeMissingColors (series.data.coloring epsilon.castSucc) epsilonTree ∪
        TashkinovStoredColors series.data epsilon.castSucc := by
    simpa [epsilonTree] using
      controlPrevious delta hdeltaStart epsilon.val (by omega)
        hepsilonTerminal epsilon rfl
  have hgammaTerminalPrevious :=
    controlPrevious gamma hgammaStart terminal.val (by omega) le_rfl terminal rfl
  have hdeltaTerminalPrevious :=
    controlPrevious delta hdeltaStart terminal.val (by omega) le_rfl terminal rfl
  have hgammaTerminal : gamma ∈
      TreeMissingColors terminalColoring terminalTree ∪ terminalStored := by
    simpa [terminalColoring, terminalTree, terminalStored] using
      (HkuMissingStoredMonotone G k rounds e0 input series terminal).1
        hgammaTerminalPrevious
  have hdeltaTerminal : delta ∈
      TreeMissingColors terminalColoring terminalTree ∪ terminalStored := by
    simpa [terminalColoring, terminalTree, terminalStored] using
      (HkuMissingStoredMonotone G k rounds e0 input series terminal).1
        hdeltaTerminalPrevious

  have reColoring (r : Fin rounds)
      (hr : series.data.kind r.succ = some TashkinovExtensionKind.RE) :
      series.data.coloring r.succ = series.data.coloring r.castSucc := by
    have cert := series.certified r.succ
    generalize hslot : r.succ = slot at cert
    cases cert with
    | initial triple seedLength initialColoring initialStored initialEdges
        initialKind initialVertex initialOutside initialDelta initialGamma
        initialClosure =>
        exact (Fin.succ_ne_zero r hslot).elim
    | SE i previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed noRevisiting choice seriesAlternative
        currentColoring currentStored currentEdges currentKind currentVertex
        currentOutside currentDelta currentGamma adjoined adjoinedExactly
        closedExtension orderedExtension strictExtension =>
        have hi : i = r := by
          apply Fin.ext
          have := congrArg Fin.val hslot
          simp only [Fin.val_succ] at this
          omega
        subst i
        rw [currentKind] at hr
        simp at hr
    | PE i previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed noRevisiting choice seriesAlternativeFails
        actualGamma gammaRule secondStable secondStableProper
        secondStableOneUncolored secondStableRelation exitWitness
        currentColoring currentProper currentOneUncolored currentStored
        currentEdges currentKind currentVertex currentOutside currentDelta
        currentGamma closedExtension orderedExtension strictExtension =>
        have hi : i = r := by
          apply Fin.ext
          have := congrArg Fin.val hslot
          simp only [Fin.val_succ] at this
          omega
        subst i
        rw [currentKind] at hr
        simp at hr
    | RE i previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed available currentColoring currentStored
        currentEdges currentKind currentVertex currentOutside currentDelta
        currentGamma adjoined adjoinedExactly closedExtension orderedExtension
        strictExtension =>
        have hi : i = r := by
          apply Fin.ext
          have := congrArg Fin.val hslot
          simp only [Fin.val_succ] at this
          omega
        subst i
        simpa [hslot] using currentColoring

  have coloringAlong : ∀ n : ℕ, t.val + 1 ≤ n → n ≤ epsilon.val →
      ∀ q : Fin (rounds + 1), q.val = n →
        series.data.coloring q = oldColoring := by
    intro n htn
    induction n, htn using Nat.le_induction with
    | base =>
        intro hn q hq
        have hqeq : q = t.succ := by
          apply Fin.ext
          simp only [Fin.val_succ]
          omega
        simpa [oldColoring, hqeq]
    | succ n hn ih =>
        intro hnepsilon q hq
        have hnlt : n < epsilon.val := by omega
        have hnt : t.val < n := by omega
        let r : Fin rounds := ⟨n, by omega⟩
        have hrKind := hintervening r (by simpa [r]) (by simpa [r])
        have hrColor := reColoring r hrKind
        have hqeq : q = r.succ := by
          apply Fin.ext
          simp [r, hq]
        calc
          series.data.coloring q = series.data.coloring r.succ := by rw [hqeq]
          _ = series.data.coloring r.castSucc := hrColor
          _ = oldColoring := ih (by omega) r.castSucc rfl

  have hepsilonColoring :
      series.data.coloring epsilon.castSucc = oldColoring :=
    coloringAlong epsilon.val (by omega) le_rfl epsilon.castSucc rfl

  have stepSegment (r : Fin rounds) :
      TreeSequenceInitialSegment (series.data.tree r.succ.castSucc)
        (series.data.tree r.succ.succ) := by
    have cert := series.certified r.succ
    generalize hslot : r.succ = slot at cert
    cases cert with
    | initial triple seedLength initialColoring initialStored initialEdges
        initialKind initialVertex initialOutside initialDelta initialGamma
        initialClosure =>
        exact (Fin.succ_ne_zero r hslot).elim
    | SE i previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed noRevisiting choice seriesAlternative
        currentColoring currentStored currentEdges currentKind currentVertex
        currentOutside currentDelta currentGamma adjoined adjoinedExactly
        closedExtension orderedExtension strictExtension =>
        have hi : i = r := by
          apply Fin.ext
          have := congrArg Fin.val hslot
          simp only [Fin.val_succ] at this
          omega
        subst i
        simpa [hslot] using orderedExtension
    | PE i previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed noRevisiting choice seriesAlternativeFails
        actualGamma gammaRule secondStable secondStableProper
        secondStableOneUncolored secondStableRelation exitWitness
        currentColoring currentProper currentOneUncolored currentStored
        currentEdges currentKind currentVertex currentOutside currentDelta
        currentGamma closedExtension orderedExtension strictExtension =>
        have hi : i = r := by
          apply Fin.ext
          have := congrArg Fin.val hslot
          simp only [Fin.val_succ] at this
          omega
        subst i
        simpa [hslot] using orderedExtension
    | RE i previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed available currentColoring currentStored
        currentEdges currentKind currentVertex currentOutside currentDelta
        currentGamma adjoined adjoinedExactly closedExtension orderedExtension
        strictExtension =>
        have hi : i = r := by
          apply Fin.ext
          have := congrArg Fin.val hslot
          simp only [Fin.val_succ] at this
          omega
        subst i
        simpa [hslot] using orderedExtension

  have vertexTransfer {A B : TreeSequence G e0}
      (hAB : TreeSequenceInitialSegment A B) :
      TreeSequenceVertexSet A ⊆ TreeSequenceVertexSet B := by
    intro v hv
    simp only [TreeSequenceVertexSet, Finset.mem_image] at hv ⊢
    rcases hv with ⟨i, -, rfl⟩
    rcases hAB with ⟨hlen, hvertices, hedges⟩
    refine ⟨Fin.castLE (Nat.succ_le_succ hlen) i, Finset.mem_univ _, ?_⟩
    exact hvertices i

  have vertexToTerminal : TreeSequenceVertexSet epsilonTree ⊆
      TreeSequenceVertexSet terminalTree := by
    intro v hv
    have carry : ∀ n : ℕ, epsilon.val ≤ n → n ≤ terminal.val →
        ∀ q : Fin rounds, q.val = n →
          v ∈ TreeSequenceVertexSet (series.data.tree q.succ.castSucc) := by
      intro n hen
      induction n, hen using Nat.le_induction with
      | base =>
          intro hn q hq
          have hqeq : q = epsilon := by apply Fin.ext; omega
          simpa [epsilonTree, hqeq] using hv
      | succ n hn ih =>
          intro hnterminal q hq
          let r : Fin rounds := ⟨n, by omega⟩
          have hold := ih (by omega) r rfl
          have hnext := vertexTransfer (stepSegment r) hold
          have htree : q.succ.castSucc = r.succ.succ := by
            apply Fin.ext
            simp [r, hq]
          simpa [htree] using hnext
    simpa [terminalTree] using carry terminal.val hepsilonTerminal le_rfl terminal rfl

  have hterminalData : IsProperEdgeColoring G terminalColoring ∧
      IsOneEdgeUncolored terminalColoring e0 := by
    have cert := series.certified terminal.succ
    generalize hslot : terminal.succ = slot at cert
    cases cert with
    | initial triple seedLength initialColoring initialStored initialEdges
        initialKind initialVertex initialOutside initialDelta initialGamma
        initialClosure =>
        exact (Fin.succ_ne_zero terminal hslot).elim
    | SE i previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed noRevisiting choice seriesAlternative
        currentColoring currentStored currentEdges currentKind currentVertex
        currentOutside currentDelta currentGamma adjoined adjoinedExactly
        closedExtension orderedExtension strictExtension =>
        have hi : i = terminal := by
          apply Fin.ext
          have := congrArg Fin.val hslot
          simp only [Fin.val_succ] at this
          omega
        subst i
        rw [currentKind] at hterminalKind
        simp at hterminalKind
    | PE i previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed noRevisiting choice seriesAlternativeFails
        actualGamma gammaRule secondStable secondStableProper
        secondStableOneUncolored secondStableRelation exitWitness
        currentColoring currentProper currentOneUncolored currentStored
        currentEdges currentKind currentVertex currentOutside currentDelta
        currentGamma closedExtension orderedExtension strictExtension =>
        have hi : i = terminal := by
          apply Fin.ext
          have := congrArg Fin.val hslot
          simp only [Fin.val_succ] at this
          omega
        subst i
        exact ⟨by simpa [terminalColoring] using currentProper,
          by simpa [terminalColoring] using currentOneUncolored⟩
    | RE i previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed available currentColoring currentStored
        currentEdges currentKind currentVertex currentOutside currentDelta
        currentGamma adjoined adjoinedExactly closedExtension orderedExtension
        strictExtension =>
        have hi : i = terminal := by
          apply Fin.ext
          have := congrArg Fin.val hslot
          simp only [Fin.val_succ] at this
          omega
        subst i
        rw [currentKind] at hterminalKind
        simp at hterminalKind

  rcases hterminalData with ⟨hterminalProper, hterminalOne⟩
  rcases hcycle with ⟨cycle, hfull⟩

  have edgeOldActive (f : E) (hf : Sum.inr f ∈ cycle.walk.support) :
      oldColoring f = some gamma ∨ oldColoring f = some delta := by
    obtain ⟨node, -, hadj⟩ :=
      SimpleGraph.adj_of_mem_walk_support cycle.walk cycle.isCycle.not_nil hf
    cases node with
    | inl v =>
        have hdata : Incident G v f ∧
            (oldColoring f = some gamma ∨ oldColoring f = some delta) := by
          simpa [oldGraph, oldColoring, TwoColorIncidenceGraph] using hadj
        exact hdata.2
    | inr e =>
        simpa [oldGraph, oldColoring, TwoColorIncidenceGraph] using hadj

  have edgeIncidentEpsilon (f : E) (hf : Sum.inr f ∈ cycle.walk.support) :
      TreeIncidentEdge epsilonTree f := by
    obtain ⟨node, hnode, hadj⟩ :=
      SimpleGraph.adj_of_mem_walk_support cycle.walk cycle.isCycle.not_nil hf
    cases node with
    | inl v =>
        have hdata : Incident G v f ∧
            (oldColoring f = some gamma ∨ oldColoring f = some delta) := by
          simpa [oldGraph, oldColoring, TwoColorIncidenceGraph] using hadj
        have hvComponent : Sum.inl v ∈ oldComponent :=
          (hfull (Sum.inl v)).1 hnode
        exact ⟨v, hcontained v (by simpa [oldComponent, oldColoring] using hvComponent),
          hdata.1⟩
    | inr e =>
        simpa [oldGraph, oldColoring, TwoColorIncidenceGraph] using hadj

  have edgeInternalEpsilon (f : E)
      (hf : Sum.inr f ∈ cycle.walk.support) :
      f ∈ InternalEdges G (TreeSequenceVertexSet epsilonTree) := by
    have hfActive := edgeOldActive f hf
    simp only [InternalEdges, Finset.mem_filter, Finset.mem_univ, true_and]
    intro v hvf
    have hadj : oldGraph.Adj (Sum.inl v) (Sum.inr f) := by
      simpa [oldGraph, oldColoring, TwoColorIncidenceGraph] using ⟨hvf, hfActive⟩
    have hfComponent : Sum.inr f ∈ oldComponent := (hfull (Sum.inr f)).1 hf
    have hvComponent : Sum.inl v ∈ oldComponent := by
      change oldGraph.connectedComponentMk (Sum.inl v) =
        oldGraph.connectedComponentMk z
      exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
        hadj).trans hfComponent
    exact hcontained v (by simpa [oldComponent, oldColoring] using hvComponent)

  have edgeSeriesPreserved (f : E) (hf : Sum.inr f ∈ cycle.walk.support) :
      terminalColoring f = oldColoring f := by
    have hfIncident := edgeIncidentEpsilon f hf
    have hfInternal := edgeInternalEpsilon f hf
    rcases edgeOldActive f hf with hgamma | hdelta
    · have hepsilonGamma : series.data.coloring epsilon.castSucc f =
          some gamma := by
        rw [hepsilonColoring]
        exact hgamma
      have h := (SameColorSeriesPreserved G k rounds e0 input series
        epsilon terminal hepsilonTerminal f gamma hfIncident hepsilonGamma
        hgammaEpsilon).2 hfInternal
      have hterminal : terminalColoring f =
          series.data.coloring epsilon.castSucc f := by
        simpa [terminalColoring] using h
      exact hterminal.trans (congrFun hepsilonColoring f)
    · have hepsilonDelta : series.data.coloring epsilon.castSucc f =
          some delta := by
        rw [hepsilonColoring]
        exact hdelta
      have h := (SameColorSeriesPreserved G k rounds e0 input series
        epsilon terminal hepsilonTerminal f delta hfIncident hepsilonDelta
        hdeltaEpsilon).2 hfInternal
      have hterminal : terminalColoring f =
          series.data.coloring epsilon.castSucc f := by
        simpa [terminalColoring] using h
      exact hterminal.trans (congrFun hepsilonColoring f)

  have terminalEdgeTransfer : ∀ edge, edge ∈ cycle.walk.edges →
      edge ∈ terminalGraph.edgeSet := by
    intro edge hedge
    induction edge using Sym2.inductionOn with
    | _ a b =>
        have haSupport := cycle.walk.fst_mem_support_of_mem_edges hedge
        have hbSupport := cycle.walk.snd_mem_support_of_mem_edges hedge
        have habOld : oldGraph.Adj a b := by
          simpa [oldGraph] using cycle.walk.edges_subset_edgeSet hedge
        cases a with
        | inl v =>
            cases b with
            | inl w => simpa [oldGraph, TwoColorIncidenceGraph] using habOld
            | inr f =>
                have hdata : Incident G v f ∧
                    (oldColoring f = some gamma ∨ oldColoring f = some delta) := by
                  simpa [oldGraph, TwoColorIncidenceGraph] using habOld
                have hcolor := edgeSeriesPreserved f hbSupport
                simpa [terminalGraph, TwoColorIncidenceGraph, hcolor] using hdata
        | inr f =>
            cases b with
            | inl v =>
                have hdata : Incident G v f ∧
                    (oldColoring f = some gamma ∨ oldColoring f = some delta) := by
                  simpa [oldGraph, TwoColorIncidenceGraph] using habOld
                have hcolor := edgeSeriesPreserved f haSupport
                simpa [terminalGraph, TwoColorIncidenceGraph, hcolor] using hdata
            | inr g => simpa [oldGraph, TwoColorIncidenceGraph] using habOld

  let terminalWalk := cycle.walk.transfer terminalGraph terminalEdgeTransfer
  have hterminalCycle : terminalWalk.IsCycle :=
    cycle.isCycle.transfer terminalEdgeTransfer

  have terminalClosed : ∀ {a b : Sum V E},
      a ∈ cycle.walk.support → terminalGraph.Adj a b →
      b ∈ cycle.walk.support := by
    intro a b ha hab
    cases a with
    | inl v =>
        cases b with
        | inl w => simpa [terminalGraph, TwoColorIncidenceGraph] using hab
        | inr f =>
            have hfData : Incident G v f ∧
                (terminalColoring f = some gamma ∨
                  terminalColoring f = some delta) := by
              simpa [terminalGraph, TwoColorIncidenceGraph] using hab
            let rotated := cycle.walk.rotate (Sum.inl v) ha
            have hrotated : rotated.IsCycle := cycle.isCycle.rotate ha
            have hfirst : oldGraph.Adj (Sum.inl v) rotated.snd := by
              simpa [oldGraph] using rotated.adj_snd hrotated.not_nil
            have hlast : oldGraph.Adj (Sum.inl v) rotated.penultimate := by
              simpa [oldGraph] using
                (rotated.adj_penultimate hrotated.not_nil).symm
            cases hfirstNode : rotated.snd with
            | inl u =>
                rw [hfirstNode] at hfirst
                simpa [oldGraph, TwoColorIncidenceGraph] using hfirst
            | inr e1 =>
                rw [hfirstNode] at hfirst
                cases hlastNode : rotated.penultimate with
                | inl u =>
                    rw [hlastNode] at hlast
                    simpa [oldGraph, TwoColorIncidenceGraph] using hlast
                | inr e2 =>
                    rw [hlastNode] at hlast
                    have he1Data : Incident G v e1 ∧
                        (oldColoring e1 = some gamma ∨
                          oldColoring e1 = some delta) := by
                      simpa [oldGraph, TwoColorIncidenceGraph] using hfirst
                    have he2Data : Incident G v e2 ∧
                        (oldColoring e2 = some gamma ∨
                          oldColoring e2 = some delta) := by
                      simpa [oldGraph, TwoColorIncidenceGraph] using hlast
                    have hvComponent : Sum.inl v ∈ oldComponent :=
                      (hfull (Sum.inl v)).1 ha
                    have he1Component : Sum.inr e1 ∈ oldComponent := by
                      change oldGraph.connectedComponentMk (Sum.inr e1) =
                        oldGraph.connectedComponentMk z
                      exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
                        hfirst).symm.trans hvComponent
                    have he2Component : Sum.inr e2 ∈ oldComponent := by
                      change oldGraph.connectedComponentMk (Sum.inr e2) =
                        oldGraph.connectedComponentMk z
                      exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
                        hlast).symm.trans hvComponent
                    have he1Support := (hfull (Sum.inr e1)).2 he1Component
                    have he2Support := (hfull (Sum.inr e2)).2 he2Component
                    have he1Terminal : terminalColoring e1 = oldColoring e1 :=
                      edgeSeriesPreserved e1 he1Support
                    have he2Terminal : terminalColoring e2 = oldColoring e2 :=
                      edgeSeriesPreserved e2 he2Support
                    have he1Active : terminalColoring e1 = some gamma ∨
                        terminalColoring e1 = some delta := by
                      rw [he1Terminal]
                      exact he1Data.2
                    have he2Active : terminalColoring e2 = some gamma ∨
                        terminalColoring e2 = some delta := by
                      rw [he2Terminal]
                      exact he2Data.2
                    have he12 : e1 ≠ e2 := by
                      intro heq
                      apply hrotated.snd_ne_penultimate
                      rw [hfirstNode, hlastNode, heq]
                    have hmatch : f = e1 ∨ f = e2 := by
                      rcases hfData.2 with hfg | hfd
                      · rcases he1Active with he1g | he1d
                        · left
                          by_contra hne
                          exact (hterminalProper hne
                            ⟨v, hfData.1, he1Data.1⟩ hfg) he1g
                        · have he2g : terminalColoring e2 = some gamma :=
                            he2Active.resolve_right (by
                              intro he2d
                              exact (hterminalProper he12
                                ⟨v, he1Data.1, he2Data.1⟩ he1d) he2d)
                          right
                          by_contra hne
                          exact (hterminalProper hne
                            ⟨v, hfData.1, he2Data.1⟩ hfg) he2g
                      · rcases he1Active with he1g | he1d
                        · have he2d : terminalColoring e2 = some delta :=
                            he2Active.resolve_left (by
                              intro he2g
                              exact (hterminalProper he12
                                ⟨v, he1Data.1, he2Data.1⟩ he1g) he2g)
                          right
                          by_contra hne
                          exact (hterminalProper hne
                            ⟨v, hfData.1, he2Data.1⟩ hfd) he2d
                        · left
                          by_contra hne
                          exact (hterminalProper hne
                            ⟨v, hfData.1, he1Data.1⟩ hfd) he1d
                    rcases hmatch with rfl | rfl
                    · exact he1Support
                    · exact he2Support
    | inr e =>
        cases b with
        | inl v =>
            have hdata : Incident G v e ∧
                (terminalColoring e = some gamma ∨
                  terminalColoring e = some delta) := by
              simpa [terminalGraph, TwoColorIncidenceGraph] using hab
            have heActive := edgeOldActive e ha
            have hadjOld : oldGraph.Adj (Sum.inr e) (Sum.inl v) := by
              simpa [oldGraph, TwoColorIncidenceGraph] using ⟨hdata.1, heActive⟩
            have heComponent : Sum.inr e ∈ oldComponent :=
              (hfull (Sum.inr e)).1 ha
            have hvComponent : Sum.inl v ∈ oldComponent := by
              change oldGraph.connectedComponentMk (Sum.inl v) =
                oldGraph.connectedComponentMk z
              exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
                hadjOld).symm.trans heComponent
            exact (hfull (Sum.inl v)).2 hvComponent
        | inr f => simpa [terminalGraph, TwoColorIncidenceGraph] using hab

  have hzSupport : z ∈ cycle.walk.support := (hfull z).2 (by rfl)
  have terminalComponentSubset : terminalComponent ⊆
      {x | x ∈ cycle.walk.support} := by
    intro x hx
    change terminalGraph.connectedComponentMk x =
      terminalGraph.connectedComponentMk z at hx
    obtain ⟨walk⟩ := SimpleGraph.ConnectedComponent.exact hx.symm
    have propagate : ∀ {a b : Sum V E}, terminalGraph.Walk a b →
        a ∈ cycle.walk.support → b ∈ cycle.walk.support := by
      intro a b walk ha
      induction walk with
      | nil => exact ha
      | @cons a c b hac rest ih => exact ih (terminalClosed ha hac)
    exact propagate walk hzSupport

  have terminalSupportComponent : ∀ x : Sum V E,
      x ∈ cycle.walk.support → x ∈ terminalComponent := by
    intro x hx
    have hxWalk : x ∈ terminalWalk.support := by
      simpa [terminalWalk] using hx
    have hzWalk : z ∈ terminalWalk.support := by
      simpa [terminalWalk] using hzSupport
    have supportComponent : ∀ y : Sum V E, y ∈ terminalWalk.support →
        terminalGraph.connectedComponentMk y =
          terminalGraph.connectedComponentMk cycle.base := by
      intro y hy
      obtain ⟨i, hi, hiLe⟩ :=
        SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hy
      rw [← hi]
      exact (SimpleGraph.ConnectedComponent.sound
        (terminalWalk.take i).reachable).symm
    change terminalGraph.connectedComponentMk x =
      terminalGraph.connectedComponentMk z
    exact (supportComponent x hxWalk).trans (supportComponent z hzWalk).symm

  have hterminalFull : ∀ x : Sum V E,
      x ∈ cycle.walk.support ↔ x ∈ terminalComponent := by
    intro x
    exact ⟨terminalSupportComponent x, terminalComponentSubset (a := x)⟩

  have terminalTreeMissingEq :
      TreeMissingColors sigma terminalTree =
        TreeMissingColors terminalColoring terminalTree := by
    ext c
    simp only [TreeMissingColors, Finset.mem_biUnion]
    constructor
    · rintro ⟨v, hv, hvc⟩
      exact ⟨v, hv, by
        rw [hsigmaStable.2 v (by simpa [terminalTree] using hv)] at hvc
        simpa [terminalColoring] using hvc⟩
    · rintro ⟨v, hv, hvc⟩
      exact ⟨v, hv, by
        rw [← hsigmaStable.2 v (by simpa [terminalTree] using hv)] at hvc
        simpa [terminalColoring] using hvc⟩

  have hgammaSigma : gamma ∈
      TreeMissingColors sigma terminalTree ∪ terminalStored := by
    rw [terminalTreeMissingEq]
    exact hgammaTerminal
  have hdeltaSigma : delta ∈
      TreeMissingColors sigma terminalTree ∪ terminalStored := by
    rw [terminalTreeMissingEq]
    exact hdeltaTerminal

  let terminalSubtype : {psi : PartialEdgeColoring E k //
      IsProperEdgeColoring G psi ∧ IsOneEdgeUncolored psi e0} :=
    ⟨terminalColoring, hterminalProper, hterminalOne⟩
  let sigmaSubtype : {psi : PartialEdgeColoring E k //
      IsProperEdgeColoring G psi ∧ IsOneEdgeUncolored psi e0} :=
    ⟨sigma, hsigmaProper, hsigmaOne⟩
  have hsigmaReverse : StableColoring terminalTree terminalStored
      sigma terminalColoring := by
    have hforward : StableColoring terminalTree terminalStored
        terminalColoring sigma := by
      simpa [terminalTree, terminalStored, terminalColoring] using hsigmaStable
    have hforwardSubtype : StableColoring terminalTree terminalStored
        terminalSubtype.1 sigmaSubtype.1 := by
      simpa [terminalSubtype, sigmaSubtype] using hforward
    have hreverseSubtype :=
      (sc2 G e0 terminalTree terminalStored).symm hforwardSubtype
    simpa [terminalSubtype, sigmaSubtype] using hreverseSubtype

  have cycleVertexTerminalTree (v : V)
      (hv : Sum.inl v ∈ cycle.walk.support) :
      v ∈ TreeSequenceVertexSet terminalTree := by
    apply vertexToTerminal
    apply hcontained v
    exact (hfull (Sum.inl v)).1 hv

  have edgeIncidentTerminal (f : E)
      (hf : Sum.inr f ∈ cycle.walk.support) :
      TreeIncidentEdge terminalTree f := by
    rcases edgeIncidentEpsilon f hf with ⟨v, hv, hvf⟩
    exact ⟨v, vertexToTerminal hv, hvf⟩

  have edgeSigmaPreserved (f : E)
      (hf : Sum.inr f ∈ cycle.walk.support) :
      sigma f = terminalColoring f := by
    have hfIncident := edgeIncidentTerminal f hf
    have hfSeries := edgeSeriesPreserved f hf
    rcases edgeOldActive f hf with hgamma | hdelta
    · apply hsigmaStable.1 f (by simpa [terminalTree] using hfIncident)
      exact ⟨gamma, by simpa [terminalColoring, terminalTree, terminalStored]
        using hgammaTerminal, hfSeries.trans hgamma⟩
    · apply hsigmaStable.1 f (by simpa [terminalTree] using hfIncident)
      exact ⟨delta, by simpa [terminalColoring, terminalTree, terminalStored]
        using hdeltaTerminal, hfSeries.trans hdelta⟩

  have sigmaEdgeTransfer : ∀ edge, edge ∈ cycle.walk.edges →
      edge ∈ sigmaGraph.edgeSet := by
    intro edge hedge
    induction edge using Sym2.inductionOn with
    | _ a b =>
        have haSupport := cycle.walk.fst_mem_support_of_mem_edges hedge
        have hbSupport := cycle.walk.snd_mem_support_of_mem_edges hedge
        have habOld : oldGraph.Adj a b := by
          simpa [oldGraph] using cycle.walk.edges_subset_edgeSet hedge
        cases a with
        | inl v =>
            cases b with
            | inl w => simpa [oldGraph, TwoColorIncidenceGraph] using habOld
            | inr f =>
                have hdata : Incident G v f ∧
                    (oldColoring f = some gamma ∨ oldColoring f = some delta) := by
                  simpa [oldGraph, TwoColorIncidenceGraph] using habOld
                have hseries := edgeSeriesPreserved f hbSupport
                have hsigma := edgeSigmaPreserved f hbSupport
                simpa [sigmaGraph, TwoColorIncidenceGraph, hsigma, hseries] using hdata
        | inr f =>
            cases b with
            | inl v =>
                have hdata : Incident G v f ∧
                    (oldColoring f = some gamma ∨ oldColoring f = some delta) := by
                  simpa [oldGraph, TwoColorIncidenceGraph] using habOld
                have hseries := edgeSeriesPreserved f haSupport
                have hsigma := edgeSigmaPreserved f haSupport
                simpa [sigmaGraph, TwoColorIncidenceGraph, hsigma, hseries] using hdata
            | inr g => simpa [oldGraph, TwoColorIncidenceGraph] using habOld

  let sigmaWalk := cycle.walk.transfer sigmaGraph sigmaEdgeTransfer
  have hsigmaCycle : sigmaWalk.IsCycle := cycle.isCycle.transfer sigmaEdgeTransfer

  have sigmaClosed : ∀ {a b : Sum V E},
      a ∈ cycle.walk.support → sigmaGraph.Adj a b →
      b ∈ cycle.walk.support := by
    intro a b ha hab
    cases a with
    | inl v =>
        cases b with
        | inl w => simpa [sigmaGraph, TwoColorIncidenceGraph] using hab
        | inr f =>
            have hdata : Incident G v f ∧
                (sigma f = some gamma ∨ sigma f = some delta) := by
              simpa [sigmaGraph, TwoColorIncidenceGraph] using hab
            have hvTree := cycleVertexTerminalTree v ha
            rcases hdata.2 with hgamma | hdelta
            · have hreverse := hsigmaReverse.1 f
                ⟨v, hvTree, hdata.1⟩
                ⟨gamma, hgammaSigma, hgamma⟩
              apply terminalClosed ha
              simpa [terminalGraph, TwoColorIncidenceGraph, hreverse, hgamma]
                using hdata.1
            · have hreverse := hsigmaReverse.1 f
                ⟨v, hvTree, hdata.1⟩
                ⟨delta, hdeltaSigma, hdelta⟩
              apply terminalClosed ha
              simpa [terminalGraph, TwoColorIncidenceGraph, hreverse, hdelta]
                using hdata.1
    | inr e =>
        cases b with
        | inl v =>
            have hdata : Incident G v e ∧
                (sigma e = some gamma ∨ sigma e = some delta) := by
              simpa [sigmaGraph, TwoColorIncidenceGraph] using hab
            have hsigma := edgeSigmaPreserved e ha
            apply terminalClosed ha
            simpa [terminalGraph, TwoColorIncidenceGraph, ← hsigma] using hdata
        | inr f => simpa [sigmaGraph, TwoColorIncidenceGraph] using hab

  have sigmaComponentSubset : sigmaComponent ⊆
      {x | x ∈ cycle.walk.support} := by
    intro x hx
    change sigmaGraph.connectedComponentMk x = sigmaGraph.connectedComponentMk z at hx
    obtain ⟨walk⟩ := SimpleGraph.ConnectedComponent.exact hx.symm
    have propagate : ∀ {a b : Sum V E}, sigmaGraph.Walk a b →
        a ∈ cycle.walk.support → b ∈ cycle.walk.support := by
      intro a b walk ha
      induction walk with
      | nil => exact ha
      | @cons a c b hac rest ih => exact ih (sigmaClosed ha hac)
    exact propagate walk hzSupport

  have sigmaSupportComponent : ∀ x : Sum V E,
      x ∈ cycle.walk.support → x ∈ sigmaComponent := by
    intro x hx
    have hxWalk : x ∈ sigmaWalk.support := by
      simpa [sigmaWalk] using hx
    have hzWalk : z ∈ sigmaWalk.support := by
      simpa [sigmaWalk] using hzSupport
    have supportComponent : ∀ y : Sum V E, y ∈ sigmaWalk.support →
        sigmaGraph.connectedComponentMk y =
          sigmaGraph.connectedComponentMk cycle.base := by
      intro y hy
      obtain ⟨i, hi, hiLe⟩ :=
        SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hy
      rw [← hi]
      exact (SimpleGraph.ConnectedComponent.sound
        (sigmaWalk.take i).reachable).symm
    change sigmaGraph.connectedComponentMk x = sigmaGraph.connectedComponentMk z
    exact (supportComponent x hxWalk).trans (supportComponent z hzWalk).symm

  have hsigmaFull : ∀ x : Sum V E,
      x ∈ cycle.walk.support ↔ x ∈ sigmaComponent := by
    intro x
    exact ⟨sigmaSupportComponent x, sigmaComponentSubset (a := x)⟩

  have hcomponent : sigmaComponent = oldComponent := by
    ext x
    exact (hsigmaFull x).symm.trans (hfull x)
  refine ⟨by simpa [sigmaComponent, oldComponent, oldColoring] using hcomponent, ?_⟩
  refine ⟨⟨cycle.base, sigmaWalk, hsigmaCycle⟩, ?_⟩
  intro x
  change x ∈ sigmaWalk.support ↔ x ∈ TwoColorComponent G sigma gamma delta z
  rw [SimpleGraph.Walk.support_transfer]
  simpa [sigmaComponent] using hsigmaFull x
