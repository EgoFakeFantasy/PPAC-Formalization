import PPAC.Migration.Internal.ProjectCompilerLocalSyntax

/-! Actual compiler-state natural guards; no target type or output-existence premise is assumed. -/
namespace PPAC.Migration.Internal.ProjectCompilerLocal
open Source SourceAlgebra SourceLogic OmegaSyntax ProjectCompilerLocalSyntax

theorem context {m} {Γ : Context m} (w b q h n : Fin m)
    (hs : Derives Γ (localStep w b q h n)) : Derives Γ (SyntaxTermSyntax.contexts w b q) := .conjL (.conjR hs)

theorem range {m} {Γ : Context m} (_hZ : ZFContext.Evidence Γ) (w b q h n : Fin m)
    (_hw : Derives Γ (omega w)) (hs : Derives Γ (localStep w b q h n)) : Derives Γ (.mem n w) := .conjL hs

end PPAC.Migration.Internal.ProjectCompilerLocal
