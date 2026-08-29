import Tablet.BoundaryColorVertex
import Tablet.DefectiveColor
import Tablet.DefectiveEdge
import Tablet.DefectiveVertex
import Tablet.ETTFirstAppearanceIndex
import Tablet.ExtendedTashkinovTree
import Tablet.ExtensionBaseActiveIndices
import Tablet.IsOneEdgeUncolored
import Tablet.IsProperEdgeColoring
import Tablet.MaximumDefectiveChoice
import Tablet.StableColoring
import Tablet.TashkinovExtensionKind
import Tablet.TashkinovSeries
import Tablet.TashkinovSeriesStep
import Tablet.TashkinovStoredColors
import Tablet.TreeSequenceInitialSegment
import Tablet.TreeSequence
import Tablet.TreeSequenceVertexSet
import Tablet.TreeVertexOrder

-- [TABLET NODE: ExtensionBaseSupportOrder]
theorem ExtensionBaseSupportOrder {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    {input : PartialEdgeColoring E k} {T : TreeSequence G e0}
    {generating : PartialEdgeColoring E k}
    (ett : ExtendedTashkinovTree G k e0 input T generating)
    (terminalSupport : V)
    (hterminalSupport : terminalSupport ∈ TreeSequenceVertexSet T)
    (q : Fin ett.rounds) (hqTerminal : q.val + 1 = ett.rounds)
    (hqKind : ett.series.data.kind q.succ =
      some TashkinovExtensionKind.PE)
    (hqVertex : ett.series.data.chosenVertex q.succ = some terminalSupport)
    (hLowerPartV : ∀ (r a : Fin ett.rounds), a.val < r.val →
      ∀ sigma : PartialEdgeColoring E k,
        IsProperEdgeColoring G sigma → IsOneEdgeUncolored sigma e0 →
        StableColoring (ett.series.data.tree r.succ.castSucc)
          (TashkinovStoredColors ett.series.data r.castSucc)
          (ett.series.data.coloring r.castSucc) sigma →
        ∀ delta : Fin k,
          DefectiveColor G sigma
            (TreeSequenceVertexSet
              (ett.series.data.tree r.succ.castSucc)) delta →
          ∀ v : V,
            BoundaryColorVertex G sigma
              (TreeSequenceVertexSet
                (ett.series.data.tree r.succ.castSucc)) delta v →
            (∃ w : V, BoundaryColorVertex G sigma
                (TreeSequenceVertexSet
                  (ett.series.data.tree r.succ.castSucc)) delta w ∧
              TreeVertexOrder (ett.series.data.tree r.succ.castSucc) w v) →
            ∀ hvFinal : v ∈ TreeSequenceVertexSet T,
              ETTFirstAppearanceIndex ett v hvFinal ≤ a.val + 1 →
              ∀ va : V,
                (ett.series.data.kind a.succ =
                    some TashkinovExtensionKind.PE ∨
                  ett.series.data.kind a.succ =
                    some TashkinovExtensionKind.SE) →
                ett.series.data.chosenVertex a.succ = some va →
                v = va ∨
                  TreeVertexOrder
                    (ett.series.data.tree r.succ.castSucc) v va) :
    (∀ (s t : Fin ett.rounds) (vs vt : V)
      (hvsFinal : vs ∈ TreeSequenceVertexSet T)
      (hvtFinal : vt ∈ TreeSequenceVertexSet T),
      s ∈ ExtensionBaseActiveIndices ett terminalSupport hterminalSupport →
      t ∈ ExtensionBaseActiveIndices ett terminalSupport hterminalSupport →
      s.val < t.val →
      ett.series.data.chosenVertex s.succ = some vs →
      ett.series.data.chosenVertex t.succ = some vt →
      vt = vs ∨ TreeVertexOrder T vt vs) ∧
    (∀ (s : Fin ett.rounds) (vs : V)
      (hvsFinal : vs ∈ TreeSequenceVertexSet T),
      s ∈ ExtensionBaseActiveIndices ett terminalSupport hterminalSupport →
      ett.series.data.chosenVertex s.succ = some vs →
      ETTFirstAppearanceIndex ett vs hvsFinal =
          ETTFirstAppearanceIndex ett terminalSupport hterminalSupport ∧
        (terminalSupport = vs ∨ TreeVertexOrder T terminalSupport vs)) ∧
    ∀ (s t : Fin ett.rounds) (vs vt : V)
      (hvsFinal : vs ∈ TreeSequenceVertexSet T)
      (hvtFinal : vt ∈ TreeSequenceVertexSet T),
      s ∈ ExtensionBaseActiveIndices ett terminalSupport hterminalSupport →
      t ∈ ExtensionBaseActiveIndices ett terminalSupport hterminalSupport →
      ett.series.data.chosenVertex s.succ = some vs →
      ett.series.data.chosenVertex t.succ = some vt →
      vs ≠ vt → TreeVertexOrder T vs vt → t.val < s.val := by
-- BODY
  set_option maxHeartbeats 800000 in
  letI : DecidableEq V := Classical.decEq V
  have segment : ∀ (j : Fin (ett.rounds + 1)) (i : Fin ett.rounds),
      j = i.succ →
      TreeSequenceInitialSegment
        (ett.series.data.tree i.succ.castSucc)
        (ett.series.data.tree i.succ.succ) := by
    intro j i hji
    cases ett.series.certified j with
    | initial triple seedLength initialColoring initialStored initialEdges
        initialKind initialVertex initialOutside initialDelta initialGamma
        initialClosure =>
      exact (Fin.succ_ne_zero i) hji.symm |>.elim
    | SE ci previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed noRevisiting choice seriesAlternative
        currentColoring currentStored currentEdges currentKind currentVertex
        currentOutside currentDelta currentGamma adjoined adjoinedExactly
        closedExtension orderedExtension strictExtension =>
      have hv := congrArg Fin.val hji
      have heq : ci = i := by apply Fin.ext; simp at hv ⊢; omega
      subst ci
      exact orderedExtension
    | PE ci previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed noRevisiting choice seriesAlternativeFails
        gamma gammaRule secondStable secondStableProper
        secondStableOneUncolored secondStableRelation exitWitness
        currentColoring currentProper currentOneUncolored currentStored
        currentEdges currentKind currentVertex currentOutside currentDelta
        currentGamma closedExtension orderedExtension strictExtension =>
      have hv := congrArg Fin.val hji
      have heq : ci = i := by apply Fin.ext; simp at hv ⊢; omega
      subst ci
      exact orderedExtension
    | RE ci previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed available currentColoring currentStored
        currentEdges currentKind currentVertex currentOutside currentDelta
        currentGamma adjoined adjoinedExactly closedExtension orderedExtension
        strictExtension =>
      have hv := congrArg Fin.val hji
      have heq : ci = i := by apply Fin.ext; simp at hv ⊢; omega
      subst ci
      exact orderedExtension
  have segmentTrans : ∀ (A B C : TreeSequence G e0),
      TreeSequenceInitialSegment A B → TreeSequenceInitialSegment B C →
      TreeSequenceInitialSegment A C := by
    intro A B C hab hbc
    rcases hab with ⟨hlab, hvab, heab⟩
    rcases hbc with ⟨hlbc, hvbc, hebc⟩
    refine ⟨hlab.trans hlbc, ?_, ?_⟩
    · intro i
      have heq : Fin.castLE (Nat.succ_le_succ (hlab.trans hlbc)) i =
          Fin.castLE (Nat.succ_le_succ hlbc)
            (Fin.castLE (Nat.succ_le_succ hlab) i) := by
        apply Fin.ext
        rfl
      rw [heq, hvbc, hvab]
    · intro i
      have heq : Fin.castLE (hlab.trans hlbc) i =
          Fin.castLE hlbc (Fin.castLE hlab i) := by
        apply Fin.ext
        rfl
      rw [heq, hebc, heab]
  have allSegment : ∀ (n : ℕ) (i : Fin (ett.rounds + 2)),
      i.val + n = ett.rounds → 2 ≤ i.val →
      TreeSequenceInitialSegment (ett.series.data.tree i)
        (ett.series.data.tree ⟨ett.rounds, by omega⟩) := by
    intro n
    induction n with
    | zero =>
      intro i hi htwo
      have heq : i.val = ett.rounds := by omega
      have hiq : i = ⟨ett.rounds, by omega⟩ := by apply Fin.ext; exact heq
      rw [hiq]
      exact ⟨Nat.le_refl _, by intro z; rfl, by intro z; rfl⟩
    | succ n ih =>
      intro i hi htwo
      have hil : i.val < ett.rounds := by omega
      let j : Fin ett.rounds := ⟨i.val - 1, by omega⟩
      let middle : Fin (ett.rounds + 1) := ⟨i.val, by omega⟩
      have hj : middle = j.succ := by
        apply Fin.ext
        change i.val = (i.val - 1) + 1
        omega
      have hs0 := segment middle j hj
      have hleft : i = j.succ.castSucc := by
        apply Fin.ext
        change i.val = (i.val - 1) + 1
        omega
      have hright : (⟨i.val + 1, by omega⟩ : Fin (ett.rounds + 2)) =
          j.succ.succ := by
        apply Fin.ext
        change i.val + 1 = (i.val - 1) + 2
        omega
      have hs : TreeSequenceInitialSegment (ett.series.data.tree i)
          (ett.series.data.tree ⟨i.val + 1, by omega⟩) := by
        have hleft' := congrArg (fun z : Fin (ett.rounds + 2) =>
          ett.series.data.tree z) hleft
        have hright' := congrArg (fun z : Fin (ett.rounds + 2) =>
          ett.series.data.tree z) hright
        exact hleft'.symm ▸ hright' ▸ hs0
      let next : Fin (ett.rounds + 2) := ⟨i.val + 1, by omega⟩
      have hn : next.val + n = ett.rounds := by
        dsimp [next]
        omega
      exact segmentTrans _ _ _ hs (ih next hn (by omega))
  have orderTransfer : ∀ {A B : TreeSequence G e0},
      TreeSequenceInitialSegment A B → ∀ u v, TreeVertexOrder A u v →
        TreeVertexOrder B u v := by
    intro A B hab u v huv
    rcases hab with ⟨hlen, hvertices, hedges⟩
    rcases huv with ⟨i, j, hi, hj, hij⟩
    refine ⟨Fin.castLE (Nat.succ_le_succ hlen) i,
      Fin.castLE (Nat.succ_le_succ hlen) j, ?_, ?_, ?_⟩
    · exact (hvertices i).trans hi
    · exact (hvertices j).trans hj
    · exact hij
  have stageInitial : ∀ i : Fin (ett.rounds + 1),
      TreeSequenceInitialSegment (ExtendedTashkinovLadderStage ett i) T := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [show ExtendedTashkinovLadderStage ett (Fin.last ett.rounds) = T by
          unfold ExtendedTashkinovLadderStage
          exact Fin.lastCases_last]
      exact ⟨Nat.le_refl _, by intro z; rfl, by intro z; rfl⟩
    · rw [show ExtendedTashkinovLadderStage ett j.castSucc =
          ett.series.data.tree j.succ.castSucc by
            unfold ExtendedTashkinovLadderStage
            simpa using (Fin.lastCases_castSucc
              (motive := fun z : Fin (ett.rounds + 1) => TreeSequence G e0) j)]
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      by_cases hj : j.val = 0
      · by_cases hone : ett.rounds = 1
        · have hj' : j = ⟨0, by omega⟩ := by apply Fin.ext; omega
          have hi' : j.succ.castSucc = ⟨1, by omega⟩ := by
            exact Fin.ext (by simp [hj'])
          rw [hi']
          simpa [hone] using ett.abovePenultimate
        · have htwo : 2 ≤ ett.rounds := by omega
          let zero : Fin ett.rounds := ⟨0, by omega⟩
          let one : Fin (ett.rounds + 1) := ⟨1, by omega⟩
          have hseg := segment one zero (by
            apply Fin.ext
            simp [one, zero])
          have hnext := allSegment (ett.rounds - 2)
            (⟨2, by omega⟩ : Fin (ett.rounds + 2))
            (by simp; omega) (by simp)
          have hj' : j = ⟨0, by omega⟩ := by apply Fin.ext; exact hj
          have hboth := segmentTrans _ _ _ hseg hnext
          have hfinal := segmentTrans _ _ _ hboth ett.abovePenultimate
          have hidx : (⟨0, by omega⟩ : Fin ett.rounds).succ.castSucc =
              zero.castSucc.succ := by
            apply Fin.ext
            simp [zero]
          rw [hj', hidx]
          exact hfinal
      · have hsum : j.val + 1 + (ett.rounds - (j.val + 1)) = ett.rounds :=
            Nat.add_sub_of_le (by omega)
        have harg : (⟨j.val + 1, by omega⟩ : Fin (ett.rounds + 2)).val +
            (ett.rounds - (j.val + 1)) = ett.rounds := by
          dsimp
          exact hsum
        have hseg := allSegment (ett.rounds - (j.val + 1))
          (⟨j.val + 1, by omega⟩ : Fin (ett.rounds + 2)) harg (by omega)
        have hsource : ett.series.data.tree j.succ.castSucc =
            ett.series.data.tree ⟨j.val + 1, by omega⟩ := by
          congr 1
        rw [hsource]
        exact segmentTrans _ _ _ hseg ett.abovePenultimate
  have peInfo : ∀ (t : Fin ett.rounds),
      ett.series.data.kind t.succ = some TashkinovExtensionKind.PE →
      ∃ choice : MaximumDefectiveChoice G e0
          (ett.series.data.tree t.succ.castSucc)
          (TashkinovStoredColors ett.series.data t.castSucc)
          (ett.series.data.coloring t.castSucc),
        IsProperEdgeColoring G choice.selected ∧
        IsOneEdgeUncolored choice.selected e0 ∧
        StableColoring (ett.series.data.tree t.succ.castSucc)
          (TashkinovStoredColors ett.series.data t.castSucc)
          (ett.series.data.coloring t.castSucc) choice.selected ∧
        ett.series.data.chosenVertex t.succ = some choice.vertex := by
    intro t ht
    have cert := ett.series.certified t.succ
    generalize hindex : t.succ = index at cert
    cases cert with
    | initial triple seedLength initialColoring initialStored initialEdges
        initialKind initialVertex initialOutside initialDelta initialGamma
        initialClosure => simp_all
    | SE ci previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed noRevisiting choice seriesAlternative
        currentColoring currentStored currentEdges currentKind currentVertex
        currentOutside currentDelta currentGamma adjoined adjoinedExactly
        closedExtension orderedExtension strictExtension =>
      have bad : (some TashkinovExtensionKind.SE) =
          some TashkinovExtensionKind.PE :=
        currentKind.symm.trans (by simpa [hindex] using ht)
      cases bad
    | RE ci previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed available currentColoring currentStored
        currentEdges currentKind currentVertex currentOutside currentDelta
        currentGamma adjoined adjoinedExactly closedExtension orderedExtension
        strictExtension =>
      have bad : (some TashkinovExtensionKind.RE) =
          some TashkinovExtensionKind.PE :=
        currentKind.symm.trans (by simpa [hindex] using ht)
      cases bad
    | PE ci previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed noRevisiting choice seriesAlternativeFails
        gamma gammaRule secondStable secondStableProper
        secondStableOneUncolored secondStableRelation exitWitness
        currentColoring currentProper currentOneUncolored currentStored
        currentEdges currentKind currentVertex currentOutside currentDelta
        currentGamma closedExtension orderedExtension strictExtension =>
      have hv := congrArg Fin.val hindex
      have heq : ci = t := by apply Fin.ext; simp at hv ⊢; omega
      subst ci
      exact ⟨choice, choice.selectedProper, choice.selectedOneUncolored,
        choice.selectedStable, currentVertex⟩
  have first : ∀ (s t : Fin ett.rounds) (vs vt : V),
      vs ∈ TreeSequenceVertexSet T → vt ∈ TreeSequenceVertexSet T →
      s ∈ ExtensionBaseActiveIndices ett terminalSupport hterminalSupport →
      t ∈ ExtensionBaseActiveIndices ett terminalSupport hterminalSupport →
      s.val < t.val →
      ett.series.data.chosenVertex s.succ = some vs →
      ett.series.data.chosenVertex t.succ = some vt →
      vt = vs ∨ TreeVertexOrder T vt vs := by
    intro s t vs vt hvs hvt hs ht hst hcsv hctv
    simp [ExtensionBaseActiveIndices] at hs ht
    rcases hs with ⟨hsj, hsk, vsv, hsv, hsi⟩
    rcases ht with ⟨htj, htk, vtv, htv, hti⟩
    rcases hsi with ⟨hsvFinal, hsvIndex⟩
    rcases hti with ⟨hvtFinal, hvtIndex⟩
    have hvsv : vsv = vs := Option.some.inj (hsv.symm.trans hcsv)
    have hvtv : vtv = vt := Option.some.inj (htv.symm.trans hctv)
    subst vtv
    have hkind : ett.series.data.kind t.succ =
        some TashkinovExtensionKind.PE := htk
    rcases peInfo t hkind with ⟨choice, hproper, hone, hstable, hchosen⟩
    have hdeltaData := choice.edgeDefective
    rcases hdeltaData with ⟨delta, hdef, hedge⟩
    have hdelta : delta = choice.color := by
      have hc := (Finset.mem_filter.mp hedge).2
      exact Option.some.inj (hc.symm.trans choice.edgeColor)
    let boundary := BoundaryColorEdges G choice.selected
      (TreeSequenceVertexSet (ett.series.data.tree t.succ.castSucc)) delta
    have hcard : 1 < boundary.card := by
      dsimp [boundary]
      exact Nat.lt_of_lt_of_le Nat.one_lt_two hdef
    rcases Finset.exists_mem_ne hcard choice.edge with ⟨f, hf, hfe⟩
    have hfbound : f ∈ BoundaryEdges G
        (TreeSequenceVertexSet (ett.series.data.tree t.succ.castSucc)) :=
      (Finset.mem_filter.mp hf).1
    have hfcolor : choice.selected f = some choice.color := by
      have hc := (Finset.mem_filter.mp hf).2
      simpa [hdelta] using hc
    simp [BoundaryEdges] at hfbound
    rcases hfbound with ⟨x, hx, hxo, hxf⟩
    rcases hxf with ⟨hxo, hxf⟩
    have hxfinc : Incident G x f := by
      change x ∈ G.ends f
      rw [hxf]
      simp
    have hxboundary : BoundaryColorVertex G choice.selected
        (TreeSequenceVertexSet (ett.series.data.tree t.succ.castSucc))
        delta x := by
      exact ⟨hx, f, hf, hxfinc⟩
    have hxdef : DefectiveVertex G choice.selected
        (TreeSequenceVertexSet (ett.series.data.tree t.succ.castSucc)) x := by
      exact ⟨hx, f, ⟨delta, hdef, hf⟩, hxfinc⟩
    have hxorder : x = choice.vertex ∨
        TreeVertexOrder (ett.series.data.tree t.succ.castSucc) x choice.vertex :=
      choice.maximal choice.selected x hproper hone hstable hxdef
    have hxne : x ≠ choice.vertex := by
      intro heq
      have hadj : AdjacentEdges G choice.edge f := by
        exact ⟨choice.vertex, choice.edgeIncident, heq ▸ hxfinc⟩
      have hbad := hproper hfe.symm hadj choice.edgeColor hfcolor
      exact hbad
    have hxorder' : TreeVertexOrder
        (ett.series.data.tree t.succ.castSucc) x choice.vertex :=
      hxorder.resolve_left hxne
    have hvtboundary : BoundaryColorVertex G choice.selected
        (TreeSequenceVertexSet (ett.series.data.tree t.succ.castSucc))
        choice.color choice.vertex := by
      have hinc : Incident G choice.vertex choice.edge := choice.edgeIncident
      exact ⟨choice.vertexDefective.1, choice.edge, by
        simpa [hdelta] using hedge, hinc⟩
    have hdefcolor : DefectiveColor G choice.selected
        (TreeSequenceVertexSet (ett.series.data.tree t.succ.castSucc)) choice.color := by
      simpa [hdelta] using hdef
    have hxboundary' : BoundaryColorVertex G choice.selected
        (TreeSequenceVertexSet (ett.series.data.tree t.succ.castSucc))
        choice.color x := by
      simpa [hdelta] using hxboundary
    have hvtchoice : vt = choice.vertex :=
      Option.some.inj (hctv.symm.trans hchosen)
    have hbound : ETTFirstAppearanceIndex ett choice.vertex
        (hvtchoice ▸ hvt) ≤ s.val + 1 := by
      have hvtFinal' : vt ∈ TreeSequenceVertexSet T := hvtFinal
      have hidx : ETTFirstAppearanceIndex ett vt hvtFinal' ≤ s.val + 1 :=
        hvtIndex.trans hsj
      simpa [hvtchoice] using hidx
    have hlow := hLowerPartV t s hst choice.selected hproper hone hstable
      choice.color hdefcolor choice.vertex hvtboundary
      ⟨x, hxboundary', hxorder'⟩ (hvtchoice ▸ hvt) hbound vs (Or.inl hsk) hcsv
    rcases hlow with hlow | hlow
    · exact Or.inl (hvtchoice.symm ▸ hlow)
    · right
      have htr : t.val + 1 ≤ ett.rounds := by omega
      have hsum : t.val + 1 + (ett.rounds - (t.val + 1)) = ett.rounds :=
        Nat.add_sub_of_le htr
      have segt := allSegment (ett.rounds - (t.val + 1))
        t.succ.castSucc (by simpa using hsum) (by simp; omega)
      exact orderTransfer ett.abovePenultimate vt vs
        (orderTransfer segt vt vs (hvtchoice.symm ▸ hlow))
  have second : ∀ (s : Fin ett.rounds) (vs : V)
      (hvs : vs ∈ TreeSequenceVertexSet T),
      s ∈ ExtensionBaseActiveIndices ett terminalSupport hterminalSupport →
      ett.series.data.chosenVertex s.succ = some vs →
      ETTFirstAppearanceIndex ett vs hvs =
          ETTFirstAppearanceIndex ett terminalSupport hterminalSupport ∧
        (terminalSupport = vs ∨ TreeVertexOrder T terminalSupport vs) := by
    intro s vs hvs hs hchosen
    have hsOriginal := hs
    simp [ExtensionBaseActiveIndices] at hs
    rcases hs with ⟨hsj, hsk, vsv, hsv, hsi⟩
    have hvsv : vsv = vs := Option.some.inj (hsv.symm.trans hchosen)
    subst vsv
    rcases hsi with ⟨hv, hi⟩
    rcases peInfo q hqKind with ⟨qchoice, _, _, _, qchosen⟩
    have hqchoice : terminalSupport = qchoice.vertex :=
      Option.some.inj (hqVertex.symm.trans qchosen)
    have hqstage : terminalSupport ∈
        TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc) := by
      exact hqchoice ▸ qchoice.vertexDefective.1
    have qbound : ETTFirstAppearanceIndex ett terminalSupport hterminalSupport ≤
        q.val + 1 := by
      unfold ETTFirstAppearanceIndex
      dsimp
      have hmem : q.castSucc ∈
          (Finset.univ.filter fun i : Fin (ett.rounds + 1) =>
            terminalSupport ∈ TreeSequenceVertexSet
              (ExtendedTashkinovLadderStage ett i)) := by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        simpa [ExtendedTashkinovLadderStage, hqTerminal] using hqstage
      have hmin := Finset.min'_le
        (Finset.univ.filter fun i : Fin (ett.rounds + 1) =>
          terminalSupport ∈ TreeSequenceVertexSet
            (ExtendedTashkinovLadderStage ett i))
        q.castSucc hmem
      apply Nat.succ_le_succ
      have hminval := Fin.le_iff_val_le_val.mp hmin
      change _ ≤ q.val at hminval
      exact hminval
    have qactive : q ∈ ExtensionBaseActiveIndices ett terminalSupport hterminalSupport := by
      simp [ExtensionBaseActiveIndices]
      refine ⟨qbound, hqKind, terminalSupport, hqVertex, hterminalSupport, ?_⟩
      exact le_rfl
    by_cases hsQ : s = q
    · subst s
      have hvq : vs = terminalSupport :=
        Option.some.inj (hchosen.symm.trans hqVertex)
      subst vs
      exact ⟨le_antisymm (by rfl) (by rfl), Or.inl rfl⟩
    have horder := first s q vs terminalSupport hvs hterminalSupport hsOriginal qactive
      (by omega) hchosen hqVertex
    have hindex : ETTFirstAppearanceIndex ett terminalSupport hterminalSupport ≤
        ETTFirstAppearanceIndex ett vs hvs := by
      unfold ETTFirstAppearanceIndex
      dsimp
      let candidates : Finset (Fin (ett.rounds + 1)) :=
        Finset.univ.filter fun i =>
          vs ∈ TreeSequenceVertexSet (ExtendedTashkinovLadderStage ett i)
      have hlast : Fin.last ett.rounds ∈ candidates := by
        simp only [candidates, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [show ExtendedTashkinovLadderStage ett (Fin.last ett.rounds) = T by
          simp [ExtendedTashkinovLadderStage, Fin.lastCases_last]]
        exact hvs
      have hnon : candidates.Nonempty := ⟨Fin.last ett.rounds, hlast⟩
      have hstage : vs ∈ TreeSequenceVertexSet
          (ExtendedTashkinovLadderStage ett (candidates.min' hnon)) := by
        exact (Finset.mem_filter.mp
          (Finset.min'_mem candidates hnon)).2
      have hseg := stageInitial (candidates.min' hnon)
      have htermstage : terminalSupport ∈ TreeSequenceVertexSet
          (ExtendedTashkinovLadderStage ett (candidates.min' hnon)) := by
        rcases horder with heq | horder
        · simpa [heq] using hstage
        · rcases horder with ⟨a, b, ha, hb, hab⟩
          simp only [TreeSequenceVertexSet] at hstage
          rcases Finset.mem_image.mp hstage with ⟨c, hc, hcv⟩
          rcases hseg with ⟨hlen, hvertices, hedges⟩
          have hveq : T.vertex b = T.vertex
              (Fin.castLE (Nat.succ_le_succ hlen) c) :=
            hb.trans (hcv.symm.trans (hvertices c).symm)
          have heq : b = Fin.castLE (Nat.succ_le_succ hlen) c :=
            T.vertex_injective hveq
          have hac : a.val < c.val := by simpa [heq] using hab
          simp only [TreeSequenceVertexSet]
          apply Finset.mem_image.mpr
          let aa : Fin ((ExtendedTashkinovLadderStage ett (candidates.min' hnon)).length + 1) :=
            ⟨a.val, by omega⟩
          have haa : Fin.castLE (Nat.succ_le_succ hlen) aa = a := by
            apply Fin.ext
            rfl
          exact ⟨aa, Finset.mem_univ _,
            (ha.symm.trans (haa ▸ hvertices aa)).symm⟩
      let terminalCandidates : Finset (Fin (ett.rounds + 1)) :=
        Finset.univ.filter fun i =>
          terminalSupport ∈ TreeSequenceVertexSet
            (ExtendedTashkinovLadderStage ett i)
      have htermMem : candidates.min' hnon ∈ terminalCandidates := by
        simp only [terminalCandidates, Finset.mem_filter, Finset.mem_univ, true_and]
        exact htermstage
      change (terminalCandidates.min' _).val + 1 ≤
        (candidates.min' hnon).val + 1
      apply Nat.succ_le_succ
      exact_mod_cast (Finset.min'_le terminalCandidates
        (candidates.min' hnon) htermMem)
    constructor
    · omega
    · exact horder
  have third : ∀ (s t : Fin ett.rounds) (vs vt : V),
      vs ∈ TreeSequenceVertexSet T → vt ∈ TreeSequenceVertexSet T →
      s ∈ ExtensionBaseActiveIndices ett terminalSupport hterminalSupport →
      t ∈ ExtensionBaseActiveIndices ett terminalSupport hterminalSupport →
      ett.series.data.chosenVertex s.succ = some vs →
      ett.series.data.chosenVertex t.succ = some vt →
      vs ≠ vt → TreeVertexOrder T vs vt → t.val < s.val := by
    intro s t vs vt hvs hvt hs ht hcsv hctv hne horder
    by_contra hnot
    have hstne : s ≠ t := by
      intro heq
      subst t
      exact hne (Option.some.inj (hcsv.symm.trans hctv))
    have hst : s.val < t.val := by omega
    have hcontra := first s t vs vt hvs hvt hs ht hst hcsv hctv
    rcases hcontra with heq | hback
    · exact hne heq.symm
    · rcases horder with ⟨i, j, hi, hj, hij⟩
      rcases hback with ⟨a, b, ha, hb, hab⟩
      have hieq : i = b := T.vertex_injective (hi.trans hb.symm)
      have jeq : j = a := T.vertex_injective (hj.trans ha.symm)
      have hiab : b.val < a.val := by simpa [hieq, jeq] using hij
      have hba : a.val < b.val := by simpa [hieq, jeq] using hab
      omega
  set_option maxHeartbeats 800000 in
    exact ⟨first, second, third⟩
