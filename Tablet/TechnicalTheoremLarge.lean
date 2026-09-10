import Tablet.TechnicalInductionContextLarge

-- [TABLET NODE: TechnicalTheoremLarge]
theorem TechnicalTheoremLarge
    {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : Nat) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (generating : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T generating)
    (hMP : MaximumProperty ett)
    (hdegree : MaximumDegree G + 1 <= k)
    (hlarge : 11 <= TashkinovOrder G) :
    ColoredVertexSetElementary G generating (TreeSequenceVertexSet T) /\
      (let terminal : Fin (ett.rounds + 1) := Fin.last ett.rounds
       let Tnext : TreeSequence G e0 :=
         ett.series.data.tree (Fin.last (ett.rounds + 1))
       forall sigma : PartialEdgeColoring E k,
         IsProperEdgeColoring G sigma -> IsOneEdgeUncolored sigma e0 ->
         StableColoring Tnext
           (TashkinovStoredColors ett.series.data terminal)
           (ett.series.data.coloring terminal) sigma ->
         forall alpha beta : Fin k,
           (alpha ∈ TreeMissingColors sigma Tnext ∨
             beta ∈ TreeMissingColors sigma Tnext) ->
           TreeInterchangeable G Tnext sigma alpha beta) /\
      ((forall (q : Fin ett.rounds) (v : V),
          ett.series.data.kind q.succ = some TashkinovExtensionKind.PE ->
          ett.series.data.chosenVertex q.succ = some v ->
          forall hvFinal : v ∈ TreeSequenceVertexSet T,
          forall j : Fin (ett.rounds + 1),
            ETTFirstAppearanceIndex ett v hvFinal = j.val + 1 ->
            forall sigma : PartialEdgeColoring E k,
              IsProperEdgeColoring G sigma ->
              IsOneEdgeUncolored sigma e0 ->
              StableColoring (ett.series.data.tree q.succ.castSucc)
                (TashkinovStoredColors ett.series.data q.succ)
                (ett.series.data.coloring q.succ) sigma ->
              StableColoringBeforeVertex T v hvFinal
                  (TashkinovStoredColors ett.series.data j)
                  (ett.series.data.coloring j) sigma /\
                (0 < j.val ->
                  StableColoring (ett.series.data.tree j.castSucc)
                    (TashkinovStoredColors ett.series.data j)
                    (ett.series.data.coloring j) sigma)) /\
        forall (q r : Fin ett.rounds) (vq vr : V),
          q ≠ r -> vq ≠ vr ->
          ett.series.data.kind q.succ = some TashkinovExtensionKind.PE ->
          ett.series.data.kind r.succ = some TashkinovExtensionKind.PE ->
          ett.series.data.chosenVertex q.succ = some vq ->
          ett.series.data.chosenVertex r.succ = some vr ->
          forall (hvq : vq ∈ TreeSequenceVertexSet T)
            (hvr : vr ∈ TreeSequenceVertexSet T),
            ETTFirstAppearanceIndex ett vq hvq =
                ETTFirstAppearanceIndex ett vr hvr ->
            Disjoint (ett.series.data.stored q.succ)
              (ett.series.data.stored r.succ)) /\
      (let terminal : Fin (ett.rounds + 1) := Fin.last ett.rounds
       let Tterminal : TreeSequence G e0 :=
         ett.series.data.tree terminal.castSucc
       forall (v : V) (gamma delta : Fin k),
         ett.series.data.kind terminal = some TashkinovExtensionKind.PE ->
         ett.series.data.chosenVertex terminal = some v ->
         ett.series.data.gamma terminal = some gamma ->
         ett.series.data.delta terminal = some delta ->
         forall sigma : PartialEdgeColoring E k,
           IsProperEdgeColoring G sigma -> IsOneEdgeUncolored sigma e0 ->
           StableColoring Tterminal
             (TashkinovStoredColors ett.series.data terminal)
             (ett.series.data.coloring terminal) sigma ->
           forall w, w ∈ TreeSequenceVertexSet Tterminal ->
             (Sum.inl w ∈ TwoColorComponent G sigma gamma delta
                 (Sum.inl v) <-> w = v)) /\
      (let terminal : Fin (ett.rounds + 1) := Fin.last ett.rounds
       let Tterminal : TreeSequence G e0 :=
         ett.series.data.tree terminal.castSucc
       forall sigma : PartialEdgeColoring E k,
         IsProperEdgeColoring G sigma -> IsOneEdgeUncolored sigma e0 ->
         StableColoring Tterminal
           (TashkinovStoredColors ett.series.data terminal)
           (ett.series.data.coloring terminal) sigma ->
         forall delta : Fin k,
           DefectiveColor G sigma (TreeSequenceVertexSet Tterminal) delta ->
           forall v : V,
             BoundaryColorVertex G sigma
                 (TreeSequenceVertexSet Tterminal) delta v ->
             (exists w, BoundaryColorVertex G sigma
                 (TreeSequenceVertexSet Tterminal) delta w /\
               TreeVertexOrder Tterminal w v) ->
             forall (hvFinal : v ∈ TreeSequenceVertexSet T)
               (q : Fin ett.rounds) (vi : V),
               (ett.series.data.kind q.succ =
                    some TashkinovExtensionKind.PE ∨
                  ett.series.data.kind q.succ =
                    some TashkinovExtensionKind.SE) ->
               ett.series.data.chosenVertex q.succ = some vi ->
               ETTFirstAppearanceIndex ett v hvFinal <= q.val + 1 ->
               v = vi ∨ TreeVertexOrder T v vi) /\
      (let terminal : Fin (ett.rounds + 1) := Fin.last ett.rounds
       let Tterminal : TreeSequence G e0 :=
         ett.series.data.tree terminal.castSucc
       forall sigma : PartialEdgeColoring E k,
         IsProperEdgeColoring G sigma -> IsOneEdgeUncolored sigma e0 ->
         StableColoring Tterminal
           (TashkinovStoredColors ett.series.data terminal)
           (ett.series.data.coloring terminal) sigma ->
         ModColoring ett sigma) := by
-- BODY
  have ctx : TechnicalInductionContext G k e0 (ett.rounds + 1) :=
    TechnicalInductionContextLarge G k e0 hdegree hlarge (ett.rounds + 1)
  have hround : ett.rounds < ett.rounds + 1 := by omega
  exact And.intro
    (ctx.lowerOne ett ett.roundsPositive hround hMP)
    (And.intro
      (ctx.lowerTwo ett ett.roundsPositive hround hMP)
      (And.intro
        (ctx.lowerThree ett ett.roundsPositive hround hMP)
        (And.intro
          (ctx.lowerFour ett ett.roundsPositive hround hMP)
          (And.intro
            (ctx.lowerFive ett ett.roundsPositive hround hMP)
            (ctx.lowerSix ett ett.roundsPositive hround hMP)))))
