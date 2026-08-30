import Tablet.AdjacentEdges
import Tablet.BoundaryColorEdges
import Tablet.ColoredVertexSetElementary
import Tablet.ETTStrongInterchangeable
import Tablet.ExtensionBaseAlgorithmC
import Tablet.ExtensionBaseAlgorithmCInvariant
import Tablet.ExtensionBaseAlgorithmCTrace
import Tablet.ExtensionBaseClaim46
import Tablet.ExtensionBaseSupportClass
import Tablet.Incident
import Tablet.InternalEdges
import Tablet.IsOneEdgeUncolored
import Tablet.IsProperEdgeColoring
import Tablet.LooplessMultigraph
import Tablet.MissingColors
import Tablet.OutsideTreeColorSwap
import Tablet.PresentColors
import Tablet.StableColoring
import Tablet.StableColoringBeforeVertex
import Tablet.TashkinovAugmentationSequence
import Tablet.TashkinovClosure
import Tablet.TashkinovExtensionKind
import Tablet.TreeSequence
import Tablet.TreeSequenceInitialSegment
import Tablet.TreeSequenceVertexSet
import Tablet.TreeVerticesBefore
import Tablet.TreeMissingColors
import Tablet.TwoColorComponent
import Tablet.TwoColorComponentSwap
import Tablet.TwoColorIncidenceDegreeAtMostTwo
import Tablet.TwoColorIncidenceGraph
import Tablet.sc2

-- [TABLET NODE: ExtensionBaseClaim45]
theorem ExtensionBaseClaim45 {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    {input : PartialEdgeColoring E k} {T : TreeSequence G e0}
    {generating : PartialEdgeColoring E k}
    (ett : ExtendedTashkinovTree G k e0 input T generating)
    (terminalSlot preterminalSlot jSlot : Fin ett.rounds)
    (hterminalAtEnd : terminalSlot.val + 1 = ett.rounds)
    (hpreterminalOrder : preterminalSlot.val < terminalSlot.val)
    (terminalSupport : V)
    (hterminalSupport : terminalSupport ∈ TreeSequenceVertexSet T)
    (Tj Tn seed TjPrime : TreeSequence G e0)
    (phiJ phiN sigmaN rho1 : PartialEdgeColoring E k)
    (Dprev controlled restorationColors supportColors : Finset (Fin k))
    (gammaFirst gammaN deltaN : Fin k) (fN : E) (x : V)
    (componentPath : (TwoColorIncidenceGraph G rho1 gammaN deltaN).Walk
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
    (hpath : componentPath.IsPath)
    (hcomponent : {y : Sum V E | y ∈ componentPath.support} =
      TwoColorComponent G rho1 gammaN deltaN
        (Sum.inl terminalSupport))
    (hxOutside : x ∉
      TreeSequenceVertexSet Tn ∪ TreeSequenceVertexSet TjPrime)
    (htwoN : ∃ w ∈ TreeSequenceVertexSet Tn,
      w ≠ terminalSupport ∧ Sum.inl w ∈ componentPath.support)
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
    (hgammaIdentity : ett.series.data.delta preterminalSlot.succ =
      some gammaN)
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
          w ∈ TreeSequenceVertexSet Tn)
    (supportLength : ℕ)
    (indices : Fin (supportLength + 1) → Fin ett.rounds)
    (gamma delta : Fin (supportLength + 1) → Fin k)
    (hincreasing : ∀ a c, a.val < c.val →
      (indices a).val < (indices c).val)
    (hclass : ∀ s : Fin ett.rounds,
      s ∈ ExtensionBaseSupportClass ett terminalSupport hterminalSupport
          terminalSupport ↔
        ∃ a : Fin (supportLength + 1), indices a = s)
    (hterminalIndex : indices (Fin.last supportLength) = terminalSlot)
    (hsupport : ∀ a,
      ett.series.data.chosenVertex (indices a).succ = some terminalSupport)
    (hkind : ∀ a,
      ett.series.data.kind (indices a).succ =
        some TashkinovExtensionKind.PE)
    (hgamma : ∀ a,
      ett.series.data.gamma (indices a).succ = some (gamma a))
    (hdelta : ∀ a,
      ett.series.data.delta (indices a).succ = some (delta a))
    (hstored : ∀ a,
      ett.series.data.stored (indices a).succ = {gamma a, delta a})
    (hchain : ∀ a : Fin supportLength,
      gamma a.succ = delta a.castSucc)
    (hdistinct : Function.Injective (Fin.cons (gamma 0) delta))
    (hTjStored : ett.series.data.tree jSlot.succ.castSucc = Tj)
    (hTjInitial : ∀ s : Fin ett.rounds,
      s ∈ (ExtensionBaseSupportClass ett terminalSupport hterminalSupport
          terminalSupport).erase terminalSlot →
        TreeSequenceInitialSegment Tj
          (ett.series.data.tree s.succ.castSucc))
    (hfirstGamma : gamma 0 = gammaFirst)
    (hpreterminalGammaPresent : ∀ (u : V) (beta : Fin k),
      u ∈ TreeSequenceVertexSet TjPrime →
      u ∉ TreeSequenceVertexSet Tn →
      beta ∈ MissingColors G rho1 u →
      ∀ a : Fin supportLength,
        gamma a.castSucc ∈ PresentColors G
          (TwoColorComponentSwap G
            (OutsideTreeColorSwap TjPrime rho1 beta deltaN)
            gammaN beta (Sum.inl u)) u) :
    ∃ (u : V) (huPrime : u ∈ TreeSequenceVertexSet TjPrime)
      (huOutside : u ∉ TreeSequenceVertexSet Tn)
      (exitPath : (TwoColorIncidenceGraph G rho1 gammaN deltaN).Walk
        (Sum.inl x) (Sum.inl u)),
      exitPath.IsPath ∧ 2 ≤ exitPath.length ∧
      (∀ y : Sum V E, y ∈ exitPath.support → y ∈ componentPath.support) ∧
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
        ∃ rho3 : PartialEdgeColoring E k,
          IsProperEdgeColoring G rho3 ∧
          IsOneEdgeUncolored rho3 e0 ∧
          StableColoringBeforeVertex Tj terminalSupport hterminalTj
            Dprev phiJ rho3 ∧
          (∀ v : V,
            v ∈ (((TreeVerticesBefore Tj z hz ∪ {z}) ∪
                (TreeVerticesBefore TjPrime u huPrime ∪ {u})).erase u).erase z →
            MissingColors G rho3 v = MissingColors G rho1 v) ∧
          (∀ f : E,
            ((∃ a : Fin Tj.length,
                seed.length ≤ a.val ∧ a.val < zPosition.val ∧
                  Tj.edge a = f) ∨
              (∃ (a : Fin TjPrime.length)
                (uPosition : Fin (TjPrime.length + 1)),
                TjPrime.vertex uPosition = u ∧ a.val < uPosition.val ∧
                  TjPrime.edge a = f)) →
            rho3 f = rho1 f) ∧
          (beta ∈ MissingColors G rho1 z →
            deltaN ∈ MissingColors G rho3 z) ∧
          (z ∈ TreeVerticesBefore TjPrime u huPrime →
            MissingColors G rho3 z = MissingColors G rho1 z) ∧
          gammaFirst ∈ MissingColors G rho3 u := by
-- BODY
  sorry
