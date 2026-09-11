import Tablet.IncidentCoreReduction
import Tablet.LargeOrderTerminalWitness
import Tablet.ThmScheide
import Tablet.egraph2

-- [TABLET NODE: ThmGS2]
theorem ThmGS2 {V E : Type*} [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (hG : MaximumDegree G + 2 ≤ ChromaticIndex G)
    (hcrit : Critical G) : Elementary G := by
-- BODY
  classical
  let H := IncidentCore G
  have reduction := IncidentCoreReduction G
  change
    (forall e : E,
      Sym2.map (fun x : IncidentVertex G => x.1) (H.ends e) = G.ends e) /\
    (forall x : IncidentVertex G, exists e : E, Incident H x e) /\
    (Critical H <-> Critical G) /\
    ChromaticIndex H = ChromaticIndex G /\
    MaximumDegree H = MaximumDegree G /\
    TashkinovOrder H = TashkinovOrder G /\
    (Elementary H -> Elementary G) at reduction
  rcases reduction with
    ⟨hendpoints, hnoisolated, hcriticalEq, hindexEq, hdegreeEq,
      horderEq, helementaryTransfer⟩
  have hcriticalH : Critical H := hcriticalEq.mpr hcrit
  have hhighH : MaximumDegree H + 2 <= ChromaticIndex H := by
    omega
  by_cases hsmall : TashkinovOrder H < 11
  · exact helementaryTransfer
      (ThmScheide H hcriticalH hnoisolated hhighH hsmall)
  · let k := ChromaticIndex H - 1
    have hindexH : ChromaticIndex H = k + 1 := by
      dsimp [k]
      omega
    have hdegreeH : MaximumDegree H + 1 <= k := by
      dsimp [k]
      omega
    have hlargeH : 11 <= TashkinovOrder H := by omega
    obtain ⟨e0, phi, X, hproper, hone, hends, helementary, hstrong⟩ :=
      LargeOrderTerminalWitness H k hcriticalH hindexH hdegreeH
        hlargeH
    have character := egraph2 H k hcriticalH hindexH hdegreeH hnoisolated
    apply helementaryTransfer
    exact character.1.mpr (character.2.1.mpr (character.2.2.mpr
      ⟨e0, phi, X, hproper, hone, hends, helementary, hstrong⟩))
