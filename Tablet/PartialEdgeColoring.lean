import Tablet.Preamble

-- [TABLET NODE: PartialEdgeColoring]
abbrev PartialEdgeColoring (E : Type*) (k : ℕ) :=
-- BODY
  E → Option (Fin k)
