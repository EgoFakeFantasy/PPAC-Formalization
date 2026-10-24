import PPAC.Migration.Internal.ProjectCompilerSourceValid

/-! Exact source acceptance formulas retain the full internal source-context guard. -/
namespace PPAC.Migration.Internal.ProjectCompilerSourceAcceptedSyntax
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax

def accepted {m} (w n b f : Fin m) : Formula m :=
  (Formula.mem f w).conj (ProjectCompilerCompleteSyntax.existsOutput w n b)

def typedAccepted {m} (w n b f z : Fin m) : Formula m :=
  (Formula.mem f w).conj (ProjectCompilerUniqueFiberSyntax.typedFiber w n b z)

theorem accepted_rename {m j} (w n b f : Fin m) (σ : Fin m → Fin j) :
    (accepted w n b f).rename σ = accepted (σ w) (σ n) (σ b) (σ f) := by
  simp only [accepted, Formula.rename, ProjectCompilerCompleteSyntax.existsOutput_rename]

theorem typedAccepted_rename {m j} (w n b f z : Fin m) (σ : Fin m → Fin j) :
    (typedAccepted w n b f z).rename σ = typedAccepted (σ w) (σ n) (σ b) (σ f) (σ z) := by
  simp only [typedAccepted, Formula.rename, ProjectCompilerUniqueFiberSyntax.typedFiber_rename]

def lawBody {m} (w : Fin m) : Formula (m+3) :=
  (ProjectSourceCodeSyntax.sourceCode (old 3 w) (slot 3 0) (slot 3 1) (slot 3 2)).iff
    (accepted (old 3 w) (slot 3 0) (slot 3 1) (slot 3 2))

def allAcceptanceLaw {m} (w : Fin m) : Formula m := OriginalUniversalBlock.allMany 3 (lawBody w)

theorem lawBody_lift {m j} (w : Fin m) (σ : Fin m → Fin j) :
    (lawBody w).rename (lift 3 σ) = lawBody (σ w) := by
  simp only [lawBody, Formula.iff, Formula.rename, ProjectSourceCodeSyntax.sourceCode_rename, accepted_rename, lift_old, lift_slot]

theorem allAcceptanceLaw_rename {m j} (w : Fin m) (σ : Fin m → Fin j) :
    (allAcceptanceLaw w).rename σ = allAcceptanceLaw (σ w) := by
  simp only [allAcceptanceLaw, OriginalUniversalBlock.allMany_rename, lawBody_lift]

def typedLawBody {m} (w : Fin m) : Formula (m+4) :=
  (empty (slot 4 3)).imp
    ((ProjectSourceCodeSyntax.sourceCode (old 4 w) (slot 4 0) (slot 4 1) (slot 4 2)).iff
      (typedAccepted (old 4 w) (slot 4 0) (slot 4 1) (slot 4 2) (slot 4 3)))

def allTypedAcceptanceLaw {m} (w : Fin m) : Formula m := OriginalUniversalBlock.allMany 4 (typedLawBody w)

theorem typedLawBody_lift {m j} (w : Fin m) (σ : Fin m → Fin j) :
    (typedLawBody w).rename (lift 4 σ) = typedLawBody (σ w) := by
  simp only [typedLawBody, Formula.iff, Formula.rename, empty_rename, ProjectSourceCodeSyntax.sourceCode_rename,
    typedAccepted_rename, lift_old, lift_slot]

theorem allTypedAcceptanceLaw_rename {m j} (w : Fin m) (σ : Fin m → Fin j) :
    (allTypedAcceptanceLaw w).rename σ = allTypedAcceptanceLaw (σ w) := by
  simp only [allTypedAcceptanceLaw, OriginalUniversalBlock.allMany_rename, typedLawBody_lift]

end PPAC.Migration.Internal.ProjectCompilerSourceAcceptedSyntax
