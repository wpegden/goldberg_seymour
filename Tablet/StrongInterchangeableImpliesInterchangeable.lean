import Tablet.ETTStrongInterchangeable
import Tablet.TreeInterchangeable
import Tablet.TwoColorPathComponent

-- [TABLET NODE: StrongInterchangeableImpliesInterchangeable]
theorem StrongInterchangeableImpliesInterchangeable {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    {input : PartialEdgeColoring E k} {T : TreeSequence G e0}
    {generating phi : PartialEdgeColoring E k}
    (ett : ExtendedTashkinovTree G k e0 input T generating)
    (t : Fin ett.rounds) (support : V) (alpha beta : Fin k)
    (hSI : ETTStrongInterchangeable ett t support phi alpha beta) :
    TreeInterchangeable G
      (ett.series.data.tree t.succ.castSucc) phi alpha beta := by
-- BODY
  classical
  rcases hSI with ⟨hab, hkind, hchosen, epsilon, hte, hekind, hbetween, hcycle⟩
  unfold TreeInterchangeable
  have noLeaf : ∀ (c : TwoColorCycle G phi alpha beta) (x : Sum V E),
      x ∈ c.walk.support →
        ¬ Set.Subsingleton ((TwoColorIncidenceGraph G phi alpha beta).neighborSet x) := by
    intro c x hx hleaf
    by_cases hbase : x = c.base
    · subst x
      have hn : ¬ c.walk.Nil := c.isCycle.not_nil
      have ha : (TwoColorIncidenceGraph G phi alpha beta).Adj c.base c.walk.snd :=
        c.walk.adj_snd hn
      have hb : (TwoColorIncidenceGraph G phi alpha beta).Adj c.base c.walk.penultimate :=
        (c.walk.adj_penultimate hn).symm
      exact c.isCycle.snd_ne_penultimate (hleaf ha hb)
    · exact c.isCycle.isTrail.not_mem_support_of_subsingleton_neighborSet
        hbase hbase hleaf hx
  intro z w hz hw hzTree hwTree
  rcases hzTree with ⟨v, hv, hvz⟩
  rcases hwTree with ⟨u, hu, huw⟩
  have hvSupport : v = support := by
    by_contra hvne
    have hcv := (hcycle v hv hvne).1
    have hcomp :
        (TwoColorIncidenceGraph G phi alpha beta).connectedComponentMk
            (Sum.inl v) =
          (TwoColorIncidenceGraph G phi alpha beta).connectedComponentMk z := by
      exact (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mp hvz
    rcases hz with ⟨hzab, x, hxcomp, hxleaf⟩
    rcases hcv with ⟨cycle, cycleSupport⟩
    have hxcycle : x ∈ cycle.walk.support := by
      apply (cycleSupport x).2
      unfold TwoColorComponent
      rw [hcomp]
      exact hxcomp
    exact (noLeaf cycle x hxcycle) hxleaf
  have huSupport : u = support := by
    by_contra hune
    have hcu := (hcycle u hu hune).1
    have hcomp :
        (TwoColorIncidenceGraph G phi alpha beta).connectedComponentMk
            (Sum.inl u) =
          (TwoColorIncidenceGraph G phi alpha beta).connectedComponentMk w := by
      exact (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mp huw
    rcases hw with ⟨hwab, x, hxcomp, hxleaf⟩
    rcases hcu with ⟨cycle, cycleSupport⟩
    have hxcycle : x ∈ cycle.walk.support := by
      apply (cycleSupport x).2
      unfold TwoColorComponent
      rw [hcomp]
      exact hxcomp
    exact (noLeaf cycle x hxcycle) hxleaf
  subst v
  subst u
  have hzSupport : Sum.inl support ∈
      TwoColorComponent G phi alpha beta z := hvz
  have hwSupport : Sum.inl support ∈
      TwoColorComponent G phi alpha beta w := huw
  unfold TwoColorComponent at hzSupport hwSupport
  have hzEq :
      (TwoColorIncidenceGraph G phi alpha beta).connectedComponentMk
          (Sum.inl support) =
        (TwoColorIncidenceGraph G phi alpha beta).connectedComponentMk z :=
    (SimpleGraph.ConnectedComponent.mem_supp_iff
      ((TwoColorIncidenceGraph G phi alpha beta).connectedComponentMk z)
      (Sum.inl support)).mp hzSupport
  have hwEq :
      (TwoColorIncidenceGraph G phi alpha beta).connectedComponentMk
          (Sum.inl support) =
        (TwoColorIncidenceGraph G phi alpha beta).connectedComponentMk w :=
    (SimpleGraph.ConnectedComponent.mem_supp_iff
      ((TwoColorIncidenceGraph G phi alpha beta).connectedComponentMk w)
      (Sum.inl support)).mp hwSupport
  unfold TwoColorComponent
  exact congrArg
    (fun c : (TwoColorIncidenceGraph G phi alpha beta).ConnectedComponent =>
      (c : Set (Sum V E))) (hzEq.symm.trans hwEq)
