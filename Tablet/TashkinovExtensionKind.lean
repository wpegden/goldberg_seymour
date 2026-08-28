import Tablet.Preamble

-- [TABLET NODE: TashkinovExtensionKind]
inductive TashkinovExtensionKind : Type where
-- BODY
  | SE : TashkinovExtensionKind
  | PE : TashkinovExtensionKind
  | RE : TashkinovExtensionKind
  deriving DecidableEq
