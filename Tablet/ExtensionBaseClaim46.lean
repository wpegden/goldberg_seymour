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
  have hcomponentExit :
      {y : Sum V E | y ∈ exitPath.support} =
        TwoColorComponent G rho0 gammaN beta (Sum.inl u) := by
    sorry
  have hcomponentIntersection : ∀ w : V,
      w ∈ TreeSequenceVertexSet Tn ∪ TreeSequenceVertexSet TjPrime →
      (Sum.inl w ∈ TwoColorComponent G rho0 gammaN beta (Sum.inl u) ↔
        w = u) := by
    intro w hw
    rw [← hcomponentExit]
    exact hexitIntersection w hw
  have component_edge_avoids : ∀ (w : V),
      w ∈ TreeSequenceVertexSet Tn ∪ TreeSequenceVertexSet TjPrime →
      w ≠ u → ∀ f : E, Incident G w f →
      Sum.inr f ∉ TwoColorComponent G rho0 gammaN beta (Sum.inl u) := by
    intro w hw hwu f hwf hf
    let H := TwoColorIncidenceGraph G rho0 gammaN beta
    have hfSupport : Sum.inr f ∈ H.support := by
      apply SimpleGraph.mem_support_of_reachable
        (G := H) (u := Sum.inr f) (v := Sum.inl u)
      · simp
      · exact SimpleGraph.ConnectedComponent.eq.mp hf
    obtain ⟨y, hy⟩ := H.mem_support.mp hfSupport
    have hfColor : rho0 f = some gammaN ∨ rho0 f = some beta := by
      cases y with
      | inl y => exact hy.2
      | inr y => simpa [H, TwoColorIncidenceGraph] using hy
    have hadj : H.Adj (Sum.inl w) (Sum.inr f) := by
      simpa [H, TwoColorIncidenceGraph] using And.intro hwf hfColor
    have hwComponent :
        Sum.inl w ∈ TwoColorComponent G rho0 gammaN beta (Sum.inl u) := by
      change H.connectedComponentMk (Sum.inl w) =
        H.connectedComponentMk (Sum.inl u)
      change H.connectedComponentMk (Sum.inr f) =
        H.connectedComponentMk (Sum.inl u) at hf
      exact
        (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj).trans hf
    exact hwu ((hcomponentIntersection w hw).mp hwComponent)
  have hmuRho0Fixed : ∀ (w : V),
      w ∈ TreeSequenceVertexSet Tn ∪ TreeSequenceVertexSet TjPrime →
      w ≠ u → ∀ f : E, Incident G w f → mu0 f = rho0 f := by
    intro w hw hwu f hwf
    have hf := component_edge_avoids w hw hwu f hwf
    simp [mu0, TwoColorComponentSwap, hf]
  have hmuRho1PrimeFixed : ∀ (w : V),
      w ∈ TreeSequenceVertexSet TjPrime → w ≠ u →
      ∀ f : E, Incident G w f → mu0 f = rho1 f := by
    intro w hw hwu f hwf
    rw [hmuRho0Fixed w (Finset.mem_union.mpr (Or.inr hw)) hwu f hwf]
    exact hrho0Fixed f ⟨w, hw, hwf⟩
  have missing_eq_of_incident_eq : ∀ (w : V),
      (∀ f : E, Incident G w f → mu0 f = rho1 f) →
      MissingColors G mu0 w = MissingColors G rho1 w := by
    intro w hfixed
    apply Finset.ext
    intro c
    simp only [MissingColors, Finset.mem_sdiff, Finset.mem_univ, true_and,
      PresentColors, Finset.mem_filter]
    constructor
    · intro hnew hold
      obtain ⟨f, hwf, hfc⟩ := hold
      exact hnew ⟨f, hwf, (hfixed f hwf).trans hfc⟩
    · intro hold hnew
      obtain ⟨f, hwf, hfc⟩ := hnew
      exact hold ⟨f, hwf, (hfixed f hwf).symm.trans hfc⟩
  have before_seed : ∀ w : V,
      w ∈ TreeVerticesBefore Tj terminalSupport hterminalTj →
      w ∈ TreeSequenceVertexSet seed := by
    intro w hw
    unfold TreeVerticesBefore at hw
    obtain ⟨hwJ, i, j, hiw, hjt, hij⟩ := Finset.mem_filter.mp hw
    obtain ⟨hlen, hvertices, hedges⟩ := hseedJ
    have hjLast : j = Fin.castLE (Nat.succ_le_succ hlen)
        (Fin.last seed.length) := by
      apply Tj.vertex_injective
      rw [hjt, hvertices, hseedTerminal]
    have hiBound : i.val < seed.length + 1 := by
      have hjVal : j.val = seed.length := by
        simpa using congrArg Fin.val hjLast
      rw [hjVal] at hij
      omega
    let iSeed : Fin (seed.length + 1) := ⟨i.val, hiBound⟩
    have hiCast : Fin.castLE (Nat.succ_le_succ hlen) iSeed = i := by
      apply Fin.ext
      rfl
    simp only [TreeSequenceVertexSet, Finset.mem_image]
    refine ⟨iSeed, Finset.mem_univ _, ?_⟩
    rw [← hvertices iSeed, hiCast]
    exact hiw
  have before_prime : ∀ w : V,
      w ∈ TreeVerticesBefore Tj terminalSupport hterminalTj →
      w ∈ TreeSequenceVertexSet TjPrime := by
    intro w hw
    exact initial_subset hseedPrime (before_seed w hw)
  have hE1 : StableColoringBeforeVertex Tj terminalSupport hterminalTj
      Dprev phiJ mu0 := by
    unfold StableColoringBeforeVertex at hb1 ⊢
    have before_ne : ∀ w : V,
        w ∈ TreeVerticesBefore Tj terminalSupport hterminalTj → w ≠ u := by
      intro w hw hwu
      subst w
      exact huSeed (before_seed u hw)
    constructor
    · intro f hf hcolor
      obtain ⟨w, hw, hwf⟩ := hf
      rw [hmuRho1PrimeFixed w (before_prime w hw) (before_ne w hw) f hwf]
      exact hb1.1 f ⟨w, hw, hwf⟩ hcolor
    · intro w hw
      exact (missing_eq_of_incident_eq w
        (hmuRho1PrimeFixed w (before_prime w hw) (before_ne w hw))).trans
          (hb1.2 w hw)
  have hmissingPrime : ∀ w : V,
      w ∈ TreeSequenceVertexSet TjPrime → w ≠ u →
      MissingColors G mu0 w = MissingColors G rho1 w := by
    intro w hw hwu
    exact missing_eq_of_incident_eq w (hmuRho1PrimeFixed w hw hwu)
  have htreeEdgeFixed : ∀ a : Fin TjPrime.length,
      mu0 (TjPrime.edge a) = rho1 (TjPrime.edge a) := by
    intro a
    obtain ⟨i, hi⟩ := TjPrime.attaches a
    let earlier : Fin (TjPrime.length + 1) :=
      Fin.castLT i (Nat.lt_trans i.isLt (Nat.succ_lt_succ a.isLt))
    have hlaterSet : TjPrime.vertex a.succ ∈
        TreeSequenceVertexSet TjPrime := by
      simp [TreeSequenceVertexSet]
    have hearlierSet : TjPrime.vertex earlier ∈
        TreeSequenceVertexSet TjPrime := by
      simp [TreeSequenceVertexSet]
    have hlaterInc : Incident G (TjPrime.vertex a.succ)
        (TjPrime.edge a) := by
      change TjPrime.vertex a.succ ∈ G.ends (TjPrime.edge a)
      rw [hi]
      simp
    have hearlierInc : Incident G (TjPrime.vertex earlier)
        (TjPrime.edge a) := by
      change TjPrime.vertex earlier ∈ G.ends (TjPrime.edge a)
      rw [hi]
      simp [earlier]
    have hverticesNe : TjPrime.vertex a.succ ≠ TjPrime.vertex earlier := by
      apply TjPrime.vertex_injective.ne
      intro heq
      have hval := congrArg Fin.val heq
      simp [earlier] at hval
      omega
    by_cases hlu : TjPrime.vertex a.succ = u
    · exact hmuRho1PrimeFixed (TjPrime.vertex earlier) hearlierSet
        (by intro heu; exact hverticesNe (hlu.trans heu.symm))
        (TjPrime.edge a) hearlierInc
    · exact hmuRho1PrimeFixed (TjPrime.vertex a.succ) hlaterSet hlu
        (TjPrime.edge a) hlaterInc
  have hE5 :
      ((TreeSequenceVertexSet TjPrime).erase u).biUnion
          (fun v => MissingColors G mu0 v) ∩ supportColors = {deltaN} ∧
        MissingColors G mu0 terminalSupport ∩ supportColors = {deltaN} ∧
        ∀ a : Fin TjPrime.length, seed.length ≤ a.val →
          ∀ c : Fin k, c ∈ supportColors \ {deltaN} →
            mu0 (TjPrime.edge a) ≠ some c := by
    constructor
    · apply Finset.ext
      intro c
      constructor
      · intro hc
        obtain ⟨hcm, hcs⟩ := Finset.mem_inter.mp hc
        obtain ⟨v, hvErase, hcMu⟩ := Finset.mem_biUnion.mp hcm
        have hv := Finset.mem_of_mem_erase hvErase
        have hvu := (Finset.mem_erase.mp hvErase).1
        have hcRho : c ∈ MissingColors G rho1 v := by
          rw [← hmissingPrime v hv hvu]
          exact hcMu
        have hcTree : c ∈ TreeMissingColors rho1 TjPrime := by
          unfold TreeMissingColors
          exact Finset.mem_biUnion.mpr ⟨v, hv, hcRho⟩
        have hcSingle : c ∈ ({deltaN} : Finset (Fin k)) := by
          rw [← hprimeMissing]
          exact Finset.mem_inter.mpr ⟨hcTree, hcs⟩
        exact hcSingle
      · intro hc
        have hcd : c = deltaN := by simpa using hc
        subst c
        have hdBoth : deltaN ∈
            TreeMissingColors rho1 TjPrime ∩ supportColors := by
          rw [hprimeMissing]
          simp
        have hdTree := (Finset.mem_inter.mp hdBoth).1
        unfold TreeMissingColors at hdTree
        obtain ⟨v, hv, hdv⟩ := Finset.mem_biUnion.mp hdTree
        have hvu : v ≠ u := by
          intro hvu
          subst v
          have hboth : deltaN ∈ MissingColors G rho1 u ∩ supportColors :=
            Finset.mem_inter.mpr ⟨hdv, hdeltaSupport⟩
          rw [hcaseTwo u huErase] at hboth
          simpa using hboth
        apply Finset.mem_inter.mpr
        refine ⟨Finset.mem_biUnion.mpr ⟨v,
          Finset.mem_erase.mpr ⟨hvu, hv⟩, ?_⟩, hdeltaSupport⟩
        rw [hmissingPrime v hv hvu]
        exact hdv
    · constructor
      · rw [hmissingPrime terminalSupport hterminalPrime (Ne.symm huTerminal)]
        exact hterminalColors
      · intro a ha c hc hbad
        apply hprimeEdges a ha c hc
        rw [← htreeEdgeFixed a]
        exact hbad
  have rho0_unaffected : ∀ (c : Fin k), c ≠ beta → c ≠ deltaN →
      ∀ f : E, (rho0 f = some c ↔ rho1 f = some c) := by
    intro c hcb hcd f
    unfold rho0 OutsideTreeColorSwap
    by_cases ht : TreeIncidentEdge TjPrime f
    · simp [ht]
    · simp only [if_neg ht]
      by_cases hfb : rho1 f = some beta
      · rw [if_pos hfb]
        constructor
        · intro h
          exact False.elim (hcd (Option.some.inj h).symm)
        · intro h
          exact False.elim (hcb (Option.some.inj (h.symm.trans hfb)))
      · rw [if_neg hfb]
        by_cases hfd : rho1 f = some deltaN
        · rw [if_pos hfd]
          constructor
          · intro h
            exact False.elim (hcb (Option.some.inj h).symm)
          · intro h
            exact False.elim (hcd (Option.some.inj (h.symm.trans hfd)))
        · rw [if_neg hfd]
  have hE4 : ∀ (s : Fin ett.rounds) (gammaS deltaS : Fin k),
      s ∈ (ExtensionBaseSupportClass ett terminalSupport
          hterminalSupport terminalSupport).erase terminalSlot →
      ett.series.data.gamma s.succ = some gammaS →
      ett.series.data.delta s.succ = some deltaS →
      ETTStrongInterchangeable ett s terminalSupport mu0 gammaS deltaS := by
    intro s gammaS deltaS hs hgammaS hdeltaS
    obtain ⟨hgammaSSupport, hdeltaSSupport⟩ :=
      hsupportColors s gammaS deltaS hs hgammaS hdeltaS
    obtain ⟨hdeltaNGammaS, hdeltaNDeltaS⟩ :=
      hdeltaEarlier s gammaS deltaS hs hgammaS hdeltaS
    have hgammaSBeta : gammaS ≠ beta := by
      intro h
      exact hbetaSupport (h ▸ hgammaSSupport)
    have hdeltaSBeta : deltaS ≠ beta := by
      intro h
      exact hbetaSupport (h ▸ hdeltaSSupport)
    have hgammaSDeltaN : gammaS ≠ deltaN := Ne.symm hdeltaNGammaS
    have hdeltaSDeltaN : deltaS ≠ deltaN := Ne.symm hdeltaNDeltaS
    obtain ⟨hgammaSDeltaS, hkind, hchosen, epsilon, hsepsilon,
        hepsilonKind, hbetweenKinds, hstrong⟩ :=
      hb4 s gammaS deltaS hs hgammaS hdeltaS
    refine ⟨hgammaSDeltaS, hkind, hchosen, epsilon, hsepsilon,
      hepsilonKind, hbetweenKinds, ?_⟩
    intro v hvTree hvTerminal
    obtain ⟨hcycleRho1, hterminalAvoid, hepsilonContain⟩ :=
      hstrong v hvTree hvTerminal
    let H1 := TwoColorIncidenceGraph G rho1 gammaS deltaS
    let HM := TwoColorIncidenceGraph G mu0 gammaS deltaS
    let C1 := TwoColorComponent G rho1 gammaS deltaS (Sum.inl v)
    let CM := TwoColorComponent G mu0 gammaS deltaS (Sum.inl v)
    have hverticesTn : ∀ w : V, Sum.inl w ∈ C1 →
        w ∈ TreeSequenceVertexSet Tn := by
      intro w hw
      exact hsupportOrder s gammaS deltaS hs hgammaS hdeltaS
        v hvTree hvTerminal w hw
    have hedgeAvoidsK : ∀ e : E, Sum.inr e ∈ C1 →
        Sum.inr e ∉ TwoColorComponent G rho0 gammaN beta (Sum.inl u) := by
      intro e heC heK
      have heSupport : Sum.inr e ∈ H1.support := by
        apply SimpleGraph.mem_support_of_reachable
          (G := H1) (u := Sum.inr e) (v := Sum.inl v)
        · simp
        · exact SimpleGraph.ConnectedComponent.eq.mp heC
      obtain ⟨y, hy⟩ := H1.mem_support.mp heSupport
      cases y with
      | inl w =>
          have hwC : Sum.inl w ∈ C1 := by
            change H1.connectedComponentMk (Sum.inl w) =
              H1.connectedComponentMk (Sum.inl v)
            change H1.connectedComponentMk (Sum.inr e) =
              H1.connectedComponentMk (Sum.inl v) at heC
            exact
              (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
                hy).symm.trans heC
          have hwTn := hverticesTn w hwC
          exact component_edge_avoids w
            (Finset.mem_union.mpr (Or.inl hwTn))
            (by intro hwu; subst w; exact huOutside hwTn) e hy.1 heK
      | inr f => simpa [H1, TwoColorIncidenceGraph] using hy
    have hadjIff : ∀ {a b : Sum V E}, a ∈ C1 →
        (HM.Adj a b ↔ H1.Adj a b) := by
      intro a b haC
      cases a with
      | inl w =>
          cases b with
          | inl z => simp [HM, H1, TwoColorIncidenceGraph]
          | inr e =>
              have hwTn := hverticesTn w haC
              simp only [HM, H1, TwoColorIncidenceGraph]
              constructor
              · rintro ⟨hwe, hec⟩
                have hfixed := hmuRho0Fixed w
                  (Finset.mem_union.mpr (Or.inl hwTn))
                  (by intro hwu; subst w; exact huOutside hwTn) e hwe
                rw [hfixed] at hec
                rcases hec with hec | hec
                · exact ⟨hwe, Or.inl
                    ((rho0_unaffected gammaS hgammaSBeta hgammaSDeltaN e).mp hec)⟩
                · exact ⟨hwe, Or.inr
                    ((rho0_unaffected deltaS hdeltaSBeta hdeltaSDeltaN e).mp hec)⟩
              · rintro ⟨hwe, hec⟩
                have hfixed := hmuRho0Fixed w
                  (Finset.mem_union.mpr (Or.inl hwTn))
                  (by intro hwu; subst w; exact huOutside hwTn) e hwe
                rw [hfixed]
                rcases hec with hec | hec
                · exact ⟨hwe, Or.inl
                    ((rho0_unaffected gammaS hgammaSBeta hgammaSDeltaN e).mpr hec)⟩
                · exact ⟨hwe, Or.inr
                    ((rho0_unaffected deltaS hdeltaSBeta hdeltaSDeltaN e).mpr hec)⟩
      | inr e =>
          cases b with
          | inl w =>
              have heK := hedgeAvoidsK e haC
              have hfixed : mu0 e = rho0 e := by
                simp [mu0, TwoColorComponentSwap, heK]
              simp only [HM, H1, TwoColorIncidenceGraph]
              constructor
              · rintro ⟨hwe, hec⟩
                rw [hfixed] at hec
                rcases hec with hec | hec
                · exact ⟨hwe, Or.inl
                    ((rho0_unaffected gammaS hgammaSBeta hgammaSDeltaN e).mp hec)⟩
                · exact ⟨hwe, Or.inr
                    ((rho0_unaffected deltaS hdeltaSBeta hdeltaSDeltaN e).mp hec)⟩
              · rintro ⟨hwe, hec⟩
                rw [hfixed]
                rcases hec with hec | hec
                · exact ⟨hwe, Or.inl
                    ((rho0_unaffected gammaS hgammaSBeta hgammaSDeltaN e).mpr hec)⟩
                · exact ⟨hwe, Or.inr
                    ((rho0_unaffected deltaS hdeltaSBeta hdeltaSDeltaN e).mpr hec)⟩
          | inr f => simp [HM, H1, TwoColorIncidenceGraph]
    have hcomponentEq : CM = C1 := by
      ext y
      constructor
      · intro hy
        have hreach : HM.Reachable (Sum.inl v) y := by
          apply SimpleGraph.ConnectedComponent.exact
          change HM.connectedComponentMk y = HM.connectedComponentMk (Sum.inl v)
            at hy
          exact hy.symm
        rw [SimpleGraph.reachable_iff_reflTransGen] at hreach
        clear hy
        have hyC1 : y ∈ C1 := by
          induction hreach with
          | refl => rfl
          | tail hreach hlast ih =>
              have hlast1 : H1.Adj _ _ := (hadjIff ih).mp hlast
              change H1.connectedComponentMk _ =
                H1.connectedComponentMk (Sum.inl v)
              exact
                (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
                  hlast1).symm.trans ih
        exact hyC1
      · intro hy
        have hreach : H1.Reachable (Sum.inl v) y := by
          apply SimpleGraph.ConnectedComponent.exact
          change H1.connectedComponentMk y = H1.connectedComponentMk (Sum.inl v)
            at hy
          exact hy.symm
        rw [SimpleGraph.reachable_iff_reflTransGen] at hreach
        clear hy
        have hpair : y ∈ C1 ∧ y ∈ CM := by
          induction hreach with
          | refl => exact ⟨rfl, rfl⟩
          | tail hreach hlast ih =>
              have hnextC1 :=
                (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
                  hlast).symm.trans ih.1
              have hlastM : HM.Adj _ _ := (hadjIff ih.1).mpr hlast
              have hnextCM :=
                (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
                  hlastM).symm.trans ih.2
              exact ⟨hnextC1, hnextCM⟩
        exact hpair.2
    unfold TwoColorComponentCycle at hcycleRho1 ⊢
    obtain ⟨cycle, hcycleSupport⟩ := hcycleRho1
    have hedgeTransfer : ∀ ed ∈ cycle.walk.edges, ed ∈ HM.edgeSet := by
      intro ed hed
      induction ed using Sym2.inductionOn with
      | _ a b =>
          have hab1 : H1.Adj a b := cycle.walk.adj_of_mem_edges hed
          have haSupport : a ∈ cycle.walk.support :=
            cycle.walk.fst_mem_support_of_mem_edges hed
          have haC : a ∈ C1 := (hcycleSupport a).mp haSupport
          exact (hadjIff haC).mpr hab1
    let walkM := cycle.walk.transfer HM hedgeTransfer
    let cycleM : TwoColorCycle G mu0 gammaS deltaS :=
      { base := cycle.base
        walk := walkM
        isCycle := cycle.isCycle.transfer hedgeTransfer }
    refine ⟨⟨cycleM, ?_⟩, ?_, ?_⟩
    · intro y
      change y ∈ walkM.support ↔ y ∈ CM
      rw [SimpleGraph.Walk.support_transfer, hcomponentEq]
      exact hcycleSupport y
    · intro hterminalM
      apply hterminalAvoid
      change Sum.inl terminalSupport ∈ C1
      rw [← hcomponentEq]
      exact hterminalM
    · intro w hwM
      apply hepsilonContain w
      change Sum.inl w ∈ C1
      rw [← hcomponentEq]
      exact hwM
  have augmentation_edge_missing {B : TreeSequence G e0}
      (hreach : TashkinovAugmentationSequence phiJ seed B) :
      ∀ a : Fin B.length, seed.length ≤ a.val →
        ∃ i : Fin (B.length + 1), i.val ≤ a.val ∧
          ∃ c : Fin k, phiJ (B.edge a) = some c ∧
            c ∈ MissingColors G phiJ (B.vertex i) := by
    unfold TashkinovAugmentationSequence at hreach
    induction hreach with
    | refl =>
        intro a ha
        omega
    | @tail A B hprior ih hstep =>
        intro a ha
        rcases ih with ⟨hlen, hinit, cnew, hcolor, hmissing⟩
        by_cases hold : a.val < A.length
        · let old : Fin A.length := ⟨a.val, hold⟩
          obtain ⟨i, hi, c, hcol, hmiss⟩ := hstep old (by simpa [old] using ha)
          refine ⟨Fin.castLE (Nat.succ_le_succ hinit.1) i, ?_, c, ?_, ?_⟩
          · simpa using hi
          · have haold : Fin.castLE hinit.1 old = a := by
              apply Fin.ext
              rfl
            rw [← haold, hinit.2.2]
            simpa [old] using hcol
          · simpa [hinit.2.1] using hmiss
        · have hnew : a.val = A.length := by omega
          let last : Fin B.length := ⟨a.val, by omega⟩
          have hlast : a = last := by
            apply Fin.ext
            simp [last]
          rw [hlast]
          rw [show B.edge last = B.edge (Fin.cast hlen.symm (Fin.last _)) by
            congr 1
            apply Fin.ext
            simpa [last] using hnew]
          rw [hcolor]
          rw [TreeMissingColors] at hmissing
          obtain ⟨w, hw, hwm⟩ := Finset.mem_biUnion.mp hmissing
          simp only [TreeSequenceVertexSet, Finset.mem_image] at hw
          obtain ⟨i, hi, hwi⟩ := hw
          refine ⟨Fin.castLE (Nat.succ_le_succ hinit.1) i, ?_, cnew, rfl, ?_⟩
          · change i.val ≤ a.val
            omega
          · rw [hinit.2.1, hwi]
            exact hwm
  have hTjEdgeFixed : ∀ a : Fin Tj.length, seed.length ≤ a.val →
      a.val < zPosition.val → mu0 (Tj.edge a) = rho1 (Tj.edge a) := by
    intro a ha hapos
    have hnotBeta := hzEdges a ha hapos
    have hnotDelta : rho1 (Tj.edge a) ≠ some deltaN := by
      intro hdelta
      obtain ⟨i, hi, c, hcolor, hmissing⟩ :=
        augmentation_edge_missing haugmentation a ha
      have hphiDelta : phiJ (Tj.edge a) = some deltaN := by
        rw [← hb2Edges a ha]
        exact hdelta
      have hc : c = deltaN := Option.some.inj (hcolor.symm.trans hphiDelta)
      subst c
      apply hdeltaPhiJ
      unfold TreeMissingColors
      exact Finset.mem_biUnion.mpr ⟨Tj.vertex i, by
        simp [TreeSequenceVertexSet], hmissing⟩
    have hlaterJ : Tj.vertex a.succ ∈ TreeSequenceVertexSet Tj := by
      simp [TreeSequenceVertexSet]
    have hlaterN := initial_subset hTjN hlaterJ
    obtain ⟨i, hi⟩ := Tj.attaches a
    have hlaterInc : Incident G (Tj.vertex a.succ) (Tj.edge a) := by
      change Tj.vertex a.succ ∈ G.ends (Tj.edge a)
      rw [hi]
      simp
    have hnotK := component_edge_avoids (Tj.vertex a.succ)
      (Finset.mem_union.mpr (Or.inl hlaterN))
      (by intro h; subst u; exact huOutside hlaterN) (Tj.edge a) hlaterInc
    have hmuRho0 : mu0 (Tj.edge a) = rho0 (Tj.edge a) := by
      simp [mu0, TwoColorComponentSwap, hnotK]
    rw [hmuRho0]
    by_cases ht : TreeIncidentEdge TjPrime (Tj.edge a)
    · exact hrho0Fixed (Tj.edge a) ht
    · simp [rho0, OutsideTreeColorSwap, ht, hnotBeta, hnotDelta]
  have before_mem_and_ne : ∀ {A : TreeSequence G e0} {a : V}
      (ha : a ∈ TreeSequenceVertexSet A) (w : V),
      w ∈ TreeVerticesBefore A a ha →
        w ∈ TreeSequenceVertexSet A ∧ w ≠ a := by
    intro A a ha w hw
    unfold TreeVerticesBefore at hw
    obtain ⟨hwA, i, j, hiw, hja, hij⟩ := Finset.mem_filter.mp hw
    refine ⟨hwA, ?_⟩
    intro hwa
    have hijEq : i = j := A.vertex_injective (hiw.trans (hwa.trans hja.symm))
    subst j
    omega
  have missing_eq_mu_rho0 : ∀ (w : V),
      (∀ f : E, Incident G w f → mu0 f = rho0 f) →
      MissingColors G mu0 w = MissingColors G rho0 w := by
    intro w hfixed
    apply Finset.ext
    intro c
    simp only [MissingColors, Finset.mem_sdiff, Finset.mem_univ, true_and,
      PresentColors, Finset.mem_filter]
    constructor
    · intro hnew hold
      obtain ⟨f, hwf, hfc⟩ := hold
      exact hnew ⟨f, hwf, (hfixed f hwf).trans hfc⟩
    · intro hold hnew
      obtain ⟨f, hwf, hfc⟩ := hnew
      exact hold ⟨f, hwf, (hfixed f hwf).symm.trans hfc⟩
  have outside_before_missing_eq : ∀ w : V,
      w ∈ TreeVerticesBefore Tj z hz →
      w ∉ TreeSequenceVertexSet TjPrime →
      MissingColors G mu0 w = MissingColors G rho1 w := by
    intro w hwBefore hwOutsidePrime
    obtain ⟨hwJ, hwz⟩ := before_mem_and_ne hz w hwBefore
    have hwN := initial_subset hTjN hwJ
    have hwu : w ≠ u := by
      intro h
      subst w
      exact huOutside hwN
    have hwTerminal : w ≠ terminalSupport := by
      intro h
      subst w
      exact hwOutsidePrime hterminalPrime
    have hbetaPresentRho : beta ∈ PresentColors G rho1 w := by
      simpa [MissingColors] using hzBefore w hwBefore
    have hdeltaNotMissingPhi :
        deltaN ∉ MissingColors G phiJ w := by
      intro hdelta
      apply hdeltaPhiJ
      unfold TreeMissingColors
      exact Finset.mem_biUnion.mpr ⟨w, hwJ, hdelta⟩
    have hdeltaNotMissingRho :
        deltaN ∉ MissingColors G rho1 w := by
      rw [hb2Missing w (Finset.mem_erase.mpr ⟨hwTerminal, hwJ⟩)]
      exact hdeltaNotMissingPhi
    have hdeltaPresentRho : deltaN ∈ PresentColors G rho1 w := by
      simpa [MissingColors] using hdeltaNotMissingRho
    have affected_not_tree : ∀ (f : E), Incident G w f →
        (rho1 f = some beta ∨ rho1 f = some deltaN) →
        ¬ TreeIncidentEdge TjPrime f := by
      intro f hwf hcolor ht
      obtain ⟨q, hqPrime, hqf⟩ := ht
      have hqw : q ≠ w := by
        intro h
        subst q
        exact hwOutsidePrime hqPrime
      have hboundary : f ∈ BoundaryEdges G
          (TreeSequenceVertexSet TjPrime) := by
        unfold BoundaryEdges
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨q, hqPrime, w, hwOutsidePrime,
          (Sym2.mem_and_mem_iff hqw).mp ⟨hqf, hwf⟩⟩
      rcases hcolor with hcolor | hcolor
      · exact (hclosure.2 hboundary huPrime hcolor) hbeta
      · exact (hclosure.2 hboundary hterminalPrime hcolor) hdeltaMissing
    have hbetaPresentRho0 : beta ∈ PresentColors G rho0 w := by
      simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
      simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
        at hdeltaPresentRho
      obtain ⟨f, hwf, hcolor⟩ := hdeltaPresentRho
      have ht := affected_not_tree f hwf (Or.inr hcolor)
      refine ⟨f, hwf, ?_⟩
      simp [rho0, OutsideTreeColorSwap, ht, hcolor, hbetaDelta,
        hbetaDelta.symm]
    have hdeltaPresentRho0 : deltaN ∈ PresentColors G rho0 w := by
      simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
      simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
        at hbetaPresentRho
      obtain ⟨f, hwf, hcolor⟩ := hbetaPresentRho
      have ht := affected_not_tree f hwf (Or.inl hcolor)
      refine ⟨f, hwf, ?_⟩
      simp [rho0, OutsideTreeColorSwap, ht, hcolor, hbetaDelta,
        hbetaDelta.symm]
    have hpresentEq : PresentColors G rho0 w = PresentColors G rho1 w := by
      apply Finset.ext
      intro c
      by_cases hcb : c = beta
      · subst c
        exact iff_of_true hbetaPresentRho0 hbetaPresentRho
      · by_cases hcd : c = deltaN
        · subst c
          exact iff_of_true hdeltaPresentRho0 hdeltaPresentRho
        · simp only [PresentColors, Finset.mem_filter, Finset.mem_univ,
            true_and]
          constructor
          · rintro ⟨f, hwf, hfc⟩
            exact ⟨f, hwf, (rho0_unaffected c hcb hcd f).mp hfc⟩
          · rintro ⟨f, hwf, hfc⟩
            exact ⟨f, hwf, (rho0_unaffected c hcb hcd f).mpr hfc⟩
    have hrhoMissing : MissingColors G rho0 w = MissingColors G rho1 w := by
      simp [MissingColors, hpresentEq]
    exact (missing_eq_mu_rho0 w (hmuRho0Fixed w
      (Finset.mem_union.mpr (Or.inl hwN)) hwu)).trans hrhoMissing
  have hE2 :
      (∀ v : V,
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
        MissingColors G mu0 z = MissingColors G rho1 z) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro v hv
      obtain ⟨hvz, hv⟩ := Finset.mem_erase.mp hv
      obtain ⟨hvu, hv⟩ := Finset.mem_erase.mp hv
      rcases Finset.mem_union.mp hv with hv | hv
      · rcases Finset.mem_union.mp hv with hvBefore | hvz'
        · by_cases hvPrime : v ∈ TreeSequenceVertexSet TjPrime
          · exact hmissingPrime v hvPrime hvu
          · exact outside_before_missing_eq v hvBefore hvPrime
        · exact False.elim (hvz (by simpa using hvz'))
      · rcases Finset.mem_union.mp hv with hvBefore | hvu'
        · exact hmissingPrime v (before_mem_and_ne huPrime v hvBefore).1 hvu
        · exact False.elim (hvu (by simpa using hvu'))
    · intro f hf
      rcases hf with hf | hf
      · obtain ⟨a, ha, haz, rfl⟩ := hf
        exact hTjEdgeFixed a ha haz
      · obtain ⟨a, uPosition, huPosition, hau, rfl⟩ := hf
        exact htreeEdgeFixed a
    · intro hbetaZ
      have hzN := initial_subset hTjN hz
      have hzu : z ≠ u := by
        intro h
        apply huOutside
        rw [← h]
        exact hzN
      have hmuRho0Z := missing_eq_mu_rho0 z (hmuRho0Fixed z
        (Finset.mem_union.mpr (Or.inl hzN)) hzu)
      rw [hmuRho0Z]
      by_cases hzPrime : z ∈ TreeSequenceVertexSet TjPrime
      · have hdisjoint := hprimeElementary hzPrime huPrime hzu
        exact False.elim ((Finset.disjoint_left.mp hdisjoint) hbetaZ hbeta)
      · apply Finset.mem_sdiff.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        intro hdeltaPresent
        simp only [PresentColors, Finset.mem_filter, Finset.mem_univ,
          true_and] at hdeltaPresent
        obtain ⟨f, hzf, hfRho0⟩ := hdeltaPresent
        by_cases ht : TreeIncidentEdge TjPrime f
        · have hfRho1 : rho1 f = some deltaN := by
            simpa [rho0, OutsideTreeColorSwap, ht] using hfRho0
          obtain ⟨q, hqPrime, hqf⟩ := ht
          have hqz : q ≠ z := by
            intro h
            subst q
            exact hzPrime hqPrime
          have hboundary : f ∈ BoundaryEdges G
              (TreeSequenceVertexSet TjPrime) := by
            unfold BoundaryEdges
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨q, hqPrime, z, hzPrime,
              (Sym2.mem_and_mem_iff hqz).mp ⟨hqf, hzf⟩⟩
          exact (hclosure.2 hboundary hterminalPrime hfRho1) hdeltaMissing
        · have hfBeta : rho1 f = some beta := by
            by_cases hfb : rho1 f = some beta
            · exact hfb
            · by_cases hfd : rho1 f = some deltaN
              · have : (some beta : Option (Fin k)) = some deltaN := by
                  simpa [rho0, OutsideTreeColorSwap, ht, hfb, hfd,
                    hbetaDelta, hbetaDelta.symm] using hfRho0
                exact False.elim (hbetaDelta (Option.some.inj this))
              · have : rho1 f = some deltaN := by
                  simpa [rho0, OutsideTreeColorSwap, ht, hfb, hfd]
                    using hfRho0
                exact False.elim (hfd this)
          have hbetaNotPresent : beta ∉ PresentColors G rho1 z := by
            simpa [MissingColors] using hbetaZ
          exact hbetaNotPresent (by
            simp only [PresentColors, Finset.mem_filter, Finset.mem_univ,
              true_and]
            exact ⟨f, hzf, hfBeta⟩)
    · intro hzBeforePrime
      obtain ⟨hzPrime, hzu⟩ :=
        before_mem_and_ne huPrime z hzBeforePrime
      exact hmissingPrime z hzPrime hzu
  exact ⟨hmu0Proper, hmu0One, hE1, hE2, hE3, hE4, hE5⟩
