import Tablet.AdjacentEdges
import Tablet.BoundaryColorEdges
import Tablet.BoundaryEdges
import Tablet.ColoredVertexSetClosed
import Tablet.ColoredVertexSetElementary
import Tablet.ETTStrongInterchangeable
import Tablet.ExtensionBaseCaseTwoObservation19
import Tablet.ExtensionBaseCaseTwoObservation20
import Tablet.ExtensionBaseCaseTwoObservation21
import Tablet.ExtensionBaseCaseTwoObservation23
import Tablet.ExtensionBaseSupportClass
import Tablet.Incident
import Tablet.InternalEdges
import Tablet.IsOneEdgeUncolored
import Tablet.IsProperEdgeColoring
import Tablet.MissingColors
import Tablet.LooplessMultigraph
import Tablet.OutsideTreeColorSwap
import Tablet.OutsideTreeColorSwapStable
import Tablet.StableColoringBeforeVertex
import Tablet.PresentColors
import Tablet.TashkinovAugmentation
import Tablet.TashkinovAugmentationSequence
import Tablet.TashkinovClosure
import Tablet.TreeMissingColors
import Tablet.TreeIncidentEdge
import Tablet.TreeSequence
import Tablet.TreeSequenceInitialSegment
import Tablet.TreeSequenceVertexSet
import Tablet.TreeVerticesBefore
import Tablet.TwoColorComponent
import Tablet.TwoColorComponentSwap
import Tablet.TwoColorComponentSwapProper
import Tablet.TwoColorIncidenceDegreeAtMostTwo
import Tablet.TwoColorIncidenceGraph

-- [TABLET NODE: ExtensionBaseClaim46]
theorem ExtensionBaseClaim46 {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    {input : PartialEdgeColoring E k} {T : TreeSequence G e0}
    {generating : PartialEdgeColoring E k}
    (ett : ExtendedTashkinovTree G k e0 input T generating)
    (terminalSlot preterminalSlot : Fin ett.rounds)
    (hterminalAtEnd : terminalSlot.val + 1 = ett.rounds)
    (hpreterminalOrder : preterminalSlot.val < terminalSlot.val)
    (terminalSupport : V)
    (hterminalSupport : terminalSupport ∈ TreeSequenceVertexSet T)
    (Tj Tn seed TjPrime : TreeSequence G e0)
    (phiJ phiN sigmaN rho1 : PartialEdgeColoring E k)
    (Dprev controlled restorationColors supportColors : Finset (Fin k))
    (gammaFirst gammaN deltaN : Fin k) (fN : E) (x : V)
    (p : (TwoColorIncidenceGraph G rho1 gammaN deltaN).Walk
      (Sum.inl terminalSupport) (Sum.inl x))
    (hphiNProper : IsProperEdgeColoring G phiN)
    (hphiNOne : IsOneEdgeUncolored phiN e0)
    (hsigmaProper : IsProperEdgeColoring G sigmaN)
    (hsigmaOne : IsOneEdgeUncolored sigmaN e0)
    (hrhoProper : IsProperEdgeColoring G rho1)
    (hrhoOne : IsOneEdgeUncolored rho1 e0)
    (hTjN : TreeSequenceInitialSegment Tj Tn)
    (hseedJ : TreeSequenceInitialSegment seed Tj)
    (hseedPrime : TreeSequenceInitialSegment seed TjPrime)
    (hseedTerminal : seed.vertex (Fin.last seed.length) = terminalSupport)
    (hterminalTj : terminalSupport ∈ TreeSequenceVertexSet Tj)
    (hterminalSeed : terminalSupport ∈ TreeSequenceVertexSet seed)
    (hclosure : TashkinovClosure rho1 seed TjPrime)
    (hprimeElementary : ColoredVertexSetElementary G rho1
      (TreeSequenceVertexSet TjPrime))
    (hcaseTwo : ∀ v : V,
      v ∈ (TreeSequenceVertexSet TjPrime).erase terminalSupport →
      MissingColors G rho1 v ∩ supportColors = ∅)
    (hterminalColors :
      MissingColors G rho1 terminalSupport ∩ supportColors = {deltaN})
    (hgammaSupport : gammaN ∈ supportColors)
    (hdeltaSupport : deltaN ∈ supportColors)
    (hgammaFirstSupport : gammaFirst ∈ supportColors)
    (hgammaDelta : gammaN ≠ deltaN)
    (hsigmaStable : StableColoring Tn controlled phiN sigmaN)
    (hgammaControlled : gammaN ∈ controlled)
    (hdeltaControlled : deltaN ∈ controlled)
    (hb3 : ∀ f : E, rho1 f ≠ sigmaN f →
      f ∉ InternalEdges G (TreeSequenceVertexSet Tj) ∧
        ∃ c d : Fin k, sigmaN f = some c ∧ rho1 f = some d ∧
          c ∈ restorationColors ∧ d ∈ restorationColors)
    (hgammaRestored : gammaN ∉ restorationColors)
    (hdeltaRestored : deltaN ∉ restorationColors)
    (hgammaBoundary :
      BoundaryColorEdges G phiN (TreeSequenceVertexSet Tn) gammaN = {fN})
    (hdeltaLocation : ∀ f ∈ BoundaryColorEdges G phiN
        (TreeSequenceVertexSet Tn) deltaN,
      ∃ w ∈ TreeSequenceVertexSet seed, Incident G w f)
    (hdeltaMissing : deltaN ∈ MissingColors G rho1 terminalSupport)
    (hpath : p.IsPath)
    (hcomponent : {y : Sum V E | y ∈ p.support} =
      TwoColorComponent G rho1 gammaN deltaN (Sum.inl terminalSupport))
    (hxOutside : x ∉
      TreeSequenceVertexSet Tn ∪ TreeSequenceVertexSet TjPrime)
    (htwoN : ∃ w ∈ TreeSequenceVertexSet Tn,
      w ≠ terminalSupport ∧ Sum.inl w ∈ p.support)
    (hfNterminal : Incident G terminalSupport fN)
    (hb1 : StableColoringBeforeVertex Tj terminalSupport hterminalTj
      Dprev phiJ rho1)
    (hb2Missing : ∀ v : V,
      v ∈ (TreeSequenceVertexSet Tj).erase terminalSupport →
      MissingColors G rho1 v = MissingColors G phiJ v)
    (hterminalInclusion : MissingColors G phiJ terminalSupport ⊆
      MissingColors G rho1 terminalSupport ∪ {gammaFirst})
    (haugmentation : TashkinovAugmentationSequence phiJ seed Tj)
    (hb2Edges : ∀ a : Fin Tj.length, seed.length ≤ a.val →
      rho1 (Tj.edge a) = phiJ (Tj.edge a))
    (hdeltaPhiJ : deltaN ∉ TreeMissingColors phiJ Tj)
    (hsupportSet : supportColors =
      (ExtensionBaseSupportClass ett terminalSupport
        hterminalSupport terminalSupport).biUnion
          (fun s => ett.series.data.stored s.succ))
    (hterminalClass : terminalSlot ∈ ExtensionBaseSupportClass ett
      terminalSupport hterminalSupport terminalSupport)
    (hpreterminalClass : preterminalSlot ∈
      (ExtensionBaseSupportClass ett terminalSupport
        hterminalSupport terminalSupport).erase terminalSlot)
    (hgammaIdentity : ett.series.data.delta preterminalSlot.succ = some gammaN)
    (hterminalGamma : ett.series.data.gamma terminalSlot.succ = some gammaN)
    (hterminalDelta : ett.series.data.delta terminalSlot.succ = some deltaN)
    (hb4 : ∀ (s : Fin ett.rounds) (gammaS deltaS : Fin k),
      s ∈ (ExtensionBaseSupportClass ett terminalSupport
          hterminalSupport terminalSupport).erase terminalSlot →
      ett.series.data.gamma s.succ = some gammaS →
      ett.series.data.delta s.succ = some deltaS →
      ETTStrongInterchangeable ett s terminalSupport rho1 gammaS deltaS)
    (hsupportColors : ∀ (s : Fin ett.rounds) (gammaS deltaS : Fin k),
      s ∈ (ExtensionBaseSupportClass ett terminalSupport
          hterminalSupport terminalSupport).erase terminalSlot →
      ett.series.data.gamma s.succ = some gammaS →
      ett.series.data.delta s.succ = some deltaS →
      gammaS ∈ supportColors ∧ deltaS ∈ supportColors)
    (hdeltaEarlier : ∀ (s : Fin ett.rounds) (gammaS deltaS : Fin k),
      s ∈ (ExtensionBaseSupportClass ett terminalSupport
          hterminalSupport terminalSupport).erase terminalSlot →
      ett.series.data.gamma s.succ = some gammaS →
      ett.series.data.delta s.succ = some deltaS →
      deltaN ≠ gammaS ∧ deltaN ≠ deltaS)
    (hsupportOrder : ∀ (s : Fin ett.rounds) (gammaS deltaS : Fin k),
      s ∈ (ExtensionBaseSupportClass ett terminalSupport
          hterminalSupport terminalSupport).erase terminalSlot →
      ett.series.data.gamma s.succ = some gammaS →
      ett.series.data.delta s.succ = some deltaS →
      ∀ v : V,
        v ∈ TreeSequenceVertexSet
            (ett.series.data.tree s.succ.castSucc) →
        v ≠ terminalSupport →
        ∀ w : V, Sum.inl w ∈
          TwoColorComponent G rho1 gammaS deltaS (Sum.inl v) →
          w ∈ TreeSequenceVertexSet Tn) :
    ∃ (u : V) (huPrime : u ∈ TreeSequenceVertexSet TjPrime)
      (huOutside : u ∉ TreeSequenceVertexSet Tn)
      (exitPath : (TwoColorIncidenceGraph G rho1 gammaN deltaN).Walk
        (Sum.inl x) (Sum.inl u)),
      exitPath.IsPath ∧ 2 ≤ exitPath.length ∧
      (∀ y : Sum V E, y ∈ exitPath.support → y ∈ p.support) ∧
      (∀ w : V,
        w ∈ TreeSequenceVertexSet Tn ∪ TreeSequenceVertexSet TjPrime →
        (Sum.inl w ∈ exitPath.support ↔ w = u)) ∧
      (∃ g ∈ BoundaryColorEdges G rho1
          (TreeSequenceVertexSet Tn ∪ TreeSequenceVertexSet TjPrime) gammaN,
        Incident G u g ∧ Sum.inr g ∈ exitPath.support) ∧
      ¬ Incident G u fN ∧
      ∀ beta : Fin k, beta ∈ MissingColors G rho1 u →
      ∃ (z : V) (hz : z ∈ TreeSequenceVertexSet Tj)
        (zPosition : Fin (Tj.length + 1)),
        Tj.vertex zPosition = z ∧ seed.length ≤ zPosition.val ∧
        ((seed.length < zPosition.val ∧
            beta ∈ MissingColors G rho1 z ∧
            ∀ r : Fin (Tj.length + 1),
              seed.length < r.val → r.val < zPosition.val →
              beta ∉ MissingColors G rho1 (Tj.vertex r)) ∨
          (zPosition = Fin.last Tj.length ∧
            ∀ r : Fin (Tj.length + 1), seed.length < r.val →
              beta ∉ MissingColors G rho1 (Tj.vertex r))) ∧
        (∀ w ∈ TreeVerticesBefore Tj z hz,
          beta ∉ MissingColors G rho1 w) ∧
        (∀ a : Fin Tj.length, seed.length ≤ a.val →
          a.val < zPosition.val → rho1 (Tj.edge a) ≠ some beta) ∧
        let rho0 := OutsideTreeColorSwap TjPrime rho1 beta deltaN
        let mu0 := TwoColorComponentSwap G rho0 gammaN beta (Sum.inl u)
        IsProperEdgeColoring G mu0 ∧ IsOneEdgeUncolored mu0 e0 ∧
        StableColoringBeforeVertex Tj terminalSupport hterminalTj
          Dprev phiJ mu0 ∧
        ((∀ v : V,
          v ∈ (((TreeVerticesBefore Tj z hz ∪ {z}) ∪
              (TreeVerticesBefore TjPrime u huPrime ∪ {u})).erase u).erase z →
          MissingColors G mu0 v = MissingColors G rho1 v) ∧
          (∀ f : E,
            ((∃ a : Fin Tj.length,
                seed.length ≤ a.val ∧ a.val < zPosition.val ∧
                  Tj.edge a = f) ∨
              (∃ (a : Fin TjPrime.length)
                (uPosition : Fin (TjPrime.length + 1)),
                TjPrime.vertex uPosition = u ∧ a.val < uPosition.val ∧
                  TjPrime.edge a = f)) →
            mu0 f = rho1 f) ∧
          (beta ∈ MissingColors G rho1 z →
            deltaN ∈ MissingColors G mu0 z) ∧
          (z ∈ TreeVerticesBefore TjPrime u huPrime →
            MissingColors G mu0 z = MissingColors G rho1 z)) ∧
        (ett.series.data.delta preterminalSlot.succ = some gammaN ∧
          gammaN ∈ MissingColors G mu0 u ∧
          beta ∉ MissingColors G mu0 u) ∧
        (∀ (s : Fin ett.rounds) (gammaS deltaS : Fin k),
          s ∈ (ExtensionBaseSupportClass ett terminalSupport
              hterminalSupport terminalSupport).erase terminalSlot →
          ett.series.data.gamma s.succ = some gammaS →
          ett.series.data.delta s.succ = some deltaS →
          ETTStrongInterchangeable ett s terminalSupport mu0 gammaS deltaS) ∧
        (((TreeSequenceVertexSet TjPrime).erase u).biUnion
            (fun v => MissingColors G mu0 v) ∩ supportColors = {deltaN} ∧
          MissingColors G mu0 terminalSupport ∩ supportColors = {deltaN} ∧
          ∀ a : Fin TjPrime.length, seed.length ≤ a.val →
            ∀ c : Fin k, c ∈ supportColors \ {deltaN} →
              mu0 (TjPrime.edge a) ≠ some c) := by
-- BODY
  classical
  have initial_subset {A B : TreeSequence G e0}
      (h : TreeSequenceInitialSegment A B) :
      TreeSequenceVertexSet A ⊆ TreeSequenceVertexSet B := by
    intro v hv
    simp only [TreeSequenceVertexSet, Finset.mem_image] at hv ⊢
    obtain ⟨i, hi, hvi⟩ := hv
    obtain ⟨hlen, hvertices, hedges⟩ := h
    exact ⟨Fin.castLE (Nat.succ_le_succ hlen) i, Finset.mem_univ _,
      (hvertices i).trans hvi⟩
  have initial_trans {A B C : TreeSequence G e0}
      (hAB : TreeSequenceInitialSegment A B)
      (hBC : TreeSequenceInitialSegment B C) :
      TreeSequenceInitialSegment A C := by
    obtain ⟨hABlen, hABvertices, hABedges⟩ := hAB
    obtain ⟨hBClen, hBCvertices, hBCedges⟩ := hBC
    refine ⟨hABlen.trans hBClen, ?_, ?_⟩
    · intro i
      calc
        C.vertex (Fin.castLE (Nat.succ_le_succ (hABlen.trans hBClen)) i) =
            C.vertex (Fin.castLE (Nat.succ_le_succ hBClen)
              (Fin.castLE (Nat.succ_le_succ hABlen) i)) := by
                congr 1
        _ = B.vertex (Fin.castLE (Nat.succ_le_succ hABlen) i) :=
          hBCvertices _
        _ = A.vertex i := hABvertices i
    · intro i
      calc
        C.edge (Fin.castLE (hABlen.trans hBClen) i) =
            C.edge (Fin.castLE hBClen (Fin.castLE hABlen i)) := by
              congr 1
        _ = B.edge (Fin.castLE hABlen i) := hBCedges _
        _ = A.edge i := hABedges i
  have hseedN : TreeSequenceInitialSegment seed Tn :=
    initial_trans hseedJ hTjN
  have hterminalN : terminalSupport ∈ TreeSequenceVertexSet Tn :=
    initial_subset hTjN hterminalTj
  have hterminalPrime : terminalSupport ∈ TreeSequenceVertexSet TjPrime :=
    initial_subset hseedPrime hterminalSeed
  have hboundaryFacts := ExtensionBaseCaseTwoObservation20
    Tn seed TjPrime phiN sigmaN rho1 controlled restorationColors
    gammaN deltaN fN terminalSupport hphiNProper hphiNOne
    hsigmaProper hsigmaOne hrhoProper hrhoOne hsigmaStable
    hgammaControlled hdeltaControlled
    (fun f hf => (hb3 f hf).2) hgammaRestored hdeltaRestored
    hgammaBoundary hdeltaLocation hseedN hseedTerminal hclosure
    hterminalSeed hdeltaMissing
  rcases hboundaryFacts with ⟨hgammaRho, hdeltaRho⟩
  obtain ⟨u, exitPath, huDiff, hexitPath, hexitLength,
      hexitSupport, hexitIntersection, hexitBoundary, huNotFN⟩ :=
    ExtensionBaseCaseTwoObservation21 Tn TjPrime rho1 gammaN deltaN
      fN terminalSupport x p hpath hcomponent hterminalN hterminalPrime
      hxOutside htwoN hgammaRho hdeltaRho hfNterminal
  have huPrime : u ∈ TreeSequenceVertexSet TjPrime :=
    (Finset.mem_sdiff.mp huDiff).1
  have huOutside : u ∉ TreeSequenceVertexSet Tn :=
    (Finset.mem_sdiff.mp huDiff).2
  refine ⟨u, huPrime, huOutside, exitPath, hexitPath, hexitLength,
    hexitSupport, hexitIntersection, hexitBoundary, huNotFN, ?_⟩
  intro beta hbeta
  have huTerminal : u ≠ terminalSupport := by
    intro hut
    apply huOutside
    simpa [hut] using hterminalN
  have huErase : u ∈ (TreeSequenceVertexSet TjPrime).erase terminalSupport :=
    Finset.mem_erase.mpr ⟨huTerminal, huPrime⟩
  have hbetaSupport : beta ∉ supportColors := by
    intro hbs
    have hbinter : beta ∈ MissingColors G rho1 u ∩ supportColors :=
      Finset.mem_inter.mpr ⟨hbeta, hbs⟩
    have hempty := hcaseTwo u huErase
    rw [hempty] at hbinter
    simpa using hbinter
  have hbetaGammaFirst : beta ≠ gammaFirst := by
    intro h
    exact hbetaSupport (h ▸ hgammaFirstSupport)
  have hbetaDelta : beta ≠ deltaN := by
    intro h
    exact hbetaSupport (h ▸ hdeltaSupport)
  have hbetaGamma : beta ≠ gammaN := by
    intro h
    exact hbetaSupport (h ▸ hgammaSupport)
  have hbetaTerminal : beta ∉ MissingColors G rho1 terminalSupport := by
    intro hbt
    have hd := hprimeElementary huPrime hterminalPrime huTerminal
    exact (Finset.disjoint_left.mp hd) hbeta hbt
  have huSeed : u ∉ TreeSequenceVertexSet seed := by
    intro hus
    exact huOutside (initial_subset hseedN hus)
  obtain ⟨z, hz, zPosition, hzPosition, hzAfter,
      hzChoice, hzBefore, hzEdges⟩ :=
    ExtensionBaseCaseTwoObservation23 Tj seed TjPrime phiJ rho1
      terminalSupport u beta gammaFirst hseedJ hseedPrime hseedTerminal
      huPrime huSeed hprimeElementary hbeta hterminalSeed hb2Missing
      hbetaTerminal hterminalInclusion hbetaGammaFirst haugmentation hb2Edges
  obtain ⟨hprimeMissing, hprimeEdges⟩ :=
    ExtensionBaseCaseTwoObservation19 rho1 seed TjPrime terminalSupport
      supportColors deltaN hclosure hterminalPrime hcaseTwo hterminalColors
  refine ⟨z, hz, zPosition, hzPosition, hzAfter, hzChoice, hzBefore,
    hzEdges, ?_⟩
  dsimp
  let rho0 := OutsideTreeColorSwap TjPrime rho1 beta deltaN
  let mu0 := TwoColorComponentSwap G rho0 gammaN beta (Sum.inl u)
  have hbetaTree : beta ∈ TreeMissingColors rho1 TjPrime := by
    unfold TreeMissingColors
    exact Finset.mem_biUnion.mpr ⟨u, huPrime, hbeta⟩
  have hdeltaTree : deltaN ∈ TreeMissingColors rho1 TjPrime := by
    unfold TreeMissingColors
    exact Finset.mem_biUnion.mpr ⟨terminalSupport, hterminalPrime,
      hdeltaMissing⟩
  have houtside := OutsideTreeColorSwapStable TjPrime supportColors rho1
    beta deltaN hrhoProper hrhoOne hclosure.2 hbetaTree hdeltaTree
    hbetaDelta
  change IsProperEdgeColoring G rho0 ∧ IsOneEdgeUncolored rho0 e0 ∧
      StableColoring TjPrime supportColors rho1 rho0 ∧
      ∀ f : E, TreeIncidentEdge TjPrime f → rho0 f = rho1 f at houtside
  rcases houtside with ⟨hrho0Proper, hrho0One, hrho0Stable, hrho0Fixed⟩
  have hgammaBeta : gammaN ≠ beta := Ne.symm hbetaGamma
  have hmu0Proper : IsProperEdgeColoring G mu0 :=
    TwoColorComponentSwapProper G rho0 gammaN beta hgammaBeta
      hrho0Proper (Sum.inl u)
  have hmu0One : IsOneEdgeUncolored mu0 e0 := by
    unfold IsOneEdgeUncolored at hrho0One ⊢
    constructor
    · simp [mu0, TwoColorComponentSwap, hrho0One.1]
    · intro f hfe
      obtain ⟨c, hc⟩ := hrho0One.2 f hfe
      have hne : mu0 f ≠ none := by
        by_cases hK : Sum.inr f ∈
            TwoColorComponent G rho0 gammaN beta (Sum.inl u)
        · by_cases hcg : c = gammaN
          · simp [mu0, TwoColorComponentSwap, hK, hc, hcg]
          · by_cases hcb : c = beta
            · simp [mu0, TwoColorComponentSwap, hK, hc, hcg, hcb,
                hgammaBeta, hbetaGamma]
            · simp [mu0, TwoColorComponentSwap, hK, hc, hcg, hcb]
        · simp [mu0, TwoColorComponentSwap, hK, hc]
      obtain ⟨d, hd⟩ := Option.ne_none_iff_exists.mp hne
      exact ⟨d, hd.symm⟩
  have hbetaRho0 : beta ∈ MissingColors G rho0 u := by
    rw [hrho0Stable.2 u huPrime]
    exact hbeta
  obtain ⟨g, hgBoundary, hug, hgExit⟩ := hexitBoundary
  have hgRho1 : rho1 g = some gammaN :=
    (Finset.mem_filter.mp hgBoundary).2
  have hgRho0 : rho0 g = some gammaN := by
    rw [hrho0Fixed g ⟨u, huPrime, hug⟩]
    exact hgRho1
  have hgComponent : Sum.inr g ∈
      TwoColorComponent G rho0 gammaN beta (Sum.inl u) := by
    change (TwoColorIncidenceGraph G rho0 gammaN beta).connectedComponentMk
        (Sum.inr g) =
      (TwoColorIncidenceGraph G rho0 gammaN beta).connectedComponentMk
        (Sum.inl u)
    have hadj : (TwoColorIncidenceGraph G rho0 gammaN beta).Adj
        (Sum.inl u) (Sum.inr g) := ⟨hug, Or.inl hgRho0⟩
    exact
      (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj).symm
  have hgMu0 : mu0 g = some beta := by
    simp [mu0, TwoColorComponentSwap, hgComponent, hgRho0,
      hgammaBeta, hbetaGamma]
  have hbetaMu0 : beta ∉ MissingColors G mu0 u := by
    intro hb
    have hbPresent : beta ∉ PresentColors G mu0 u := by
      simpa [MissingColors] using hb
    apply hbPresent
    simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨g, hug, hgMu0⟩
  have hgammaMu0 : gammaN ∈ MissingColors G mu0 u := by
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    intro hgPresent
    simp only [PresentColors, Finset.mem_filter, Finset.mem_univ,
      true_and] at hgPresent
    obtain ⟨f, huf, hfMu0⟩ := hgPresent
    by_cases hfComponent : Sum.inr f ∈
        TwoColorComponent G rho0 gammaN beta (Sum.inl u)
    · by_cases hfGamma : rho0 f = some gammaN
      · have : (some beta : Option (Fin k)) = some gammaN := by
          simpa [mu0, TwoColorComponentSwap, hfComponent, hfGamma,
            hgammaBeta, hbetaGamma] using hfMu0
        exact hbetaGamma (Option.some.inj this)
      · by_cases hfBeta : rho0 f = some beta
        · have hnotPresent : beta ∉ PresentColors G rho0 u := by
            simpa [MissingColors] using hbetaRho0
          exact hnotPresent (by
            simp only [PresentColors, Finset.mem_filter, Finset.mem_univ,
              true_and]
            exact ⟨f, huf, hfBeta⟩)
        · have : rho0 f = some gammaN := by
            simpa [mu0, TwoColorComponentSwap, hfComponent, hfGamma,
              hfBeta] using hfMu0
          exact hfGamma this
    · have hfRho0 : rho0 f = some gammaN := by
        simpa [mu0, TwoColorComponentSwap, hfComponent] using hfMu0
      have hadj : (TwoColorIncidenceGraph G rho0 gammaN beta).Adj
          (Sum.inl u) (Sum.inr f) := ⟨huf, Or.inl hfRho0⟩
      apply hfComponent
      change (TwoColorIncidenceGraph G rho0 gammaN beta).connectedComponentMk
          (Sum.inr f) =
        (TwoColorIncidenceGraph G rho0 gammaN beta).connectedComponentMk
          (Sum.inl u)
      exact
        (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj).symm
  have hE3 :
      ett.series.data.delta preterminalSlot.succ = some gammaN ∧
        gammaN ∈ MissingColors G mu0 u ∧
        beta ∉ MissingColors G mu0 u :=
    ⟨hgammaIdentity, hgammaMu0, hbetaMu0⟩
  refine ⟨hmu0Proper, hmu0One, ?_⟩
  sorry
