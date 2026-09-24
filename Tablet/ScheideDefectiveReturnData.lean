import Tablet.DefectiveColors
import Tablet.Incident
import Tablet.MissingColors
import Tablet.ScheideDefectiveSetup
import Tablet.ScheideExitVertices
import Tablet.TreeSequenceVertexSet

open scoped Sym2

-- [TABLET NODE: ScheideDefectiveReturnData]
structure ScheideDefectiveReturnData {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (C : ScheideReducedConfiguration G k e0 phi T)
    (D : ScheideDefectiveSetup G k e0 phi T C)
    (d : {delta // delta ∈ DefectiveColors G phi (TreeSequenceVertexSet T)}) where
-- BODY
  pathIndex : Fin ((D.replacementPath d).length + 1)
  edgeIndex : Fin ((D.replacementPath d).length + 1)
  outsideIndex : Fin ((D.replacementPath d).length + 1)
  v1 : V
  f1 : E
  u1 : V
  blockIndex : Fin C.s
  v1_at_index :
    (D.replacementPath d).getVert pathIndex.val = Sum.inl v1
  f1_at_index :
    (D.replacementPath d).getVert edgeIndex.val = Sum.inr f1
  u1_at_index :
    (D.replacementPath d).getVert outsideIndex.val = Sum.inl u1
  successive_indices :
    edgeIndex.val = pathIndex.val + 1 ∧
      outsideIndex.val = pathIndex.val + 2
  after_last_tree_vertex :
    ∀ r : Fin ((D.replacementPath d).length + 1), pathIndex.val < r.val →
      ∀ x : V, (D.replacementPath d).getVert r.val = Sum.inl x →
        x ∉ TreeSequenceVertexSet T
  v1_mem : v1 ∈ TreeSequenceVertexSet T
  v1_ne_v0 : v1 ≠ D.v0 d
  u1_outside : u1 ∉ TreeSequenceVertexSet T
  v1_is_exit : v1 ∈ ScheideExitVertices T phi
  v1_in_base : v1 ∈ Finset.univ.image C.y
  f1_color : phi f1 = some d.1
  f1_ends : G.ends f1 = s(v1, u1)
  gammaJ_missing : C.gamma blockIndex ∈ MissingColors G phi v1
  blockIndex_ne : blockIndex ≠ D.gammaIndex d
  alpha0_ne_gamma : D.alpha0 ≠ C.gamma (D.gammaIndex d)
  alpha0_ne_gammaJ : D.alpha0 ≠ C.gamma blockIndex
  alpha0_ne_delta : D.alpha0 ≠ d.1
  gamma_ne_gammaJ : C.gamma (D.gammaIndex d) ≠ C.gamma blockIndex
  gamma_ne_delta : C.gamma (D.gammaIndex d) ≠ d.1
  gammaJ_ne_delta : C.gamma blockIndex ≠ d.1
