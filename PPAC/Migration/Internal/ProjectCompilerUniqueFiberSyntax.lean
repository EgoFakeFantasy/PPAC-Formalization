import PPAC.Migration.Internal.ProjectCompilerUnique

/-! Object unique-output and actual target-typed unique fibers; no host selector is extracted. -/
namespace PPAC.Migration.Internal.ProjectCompilerUniqueFiberSyntax
open Source SourceAlgebra SourceLogic HornBinderSyntax

def uniqueOutput {m} (w n b q : Fin m) : Formula m := .all
  ((ProjectCompilerCodeSyntax.compiled w.castSucc n.castSucc b.castSucc (Fin.last m)).imp (.equal (Fin.last m) q.castSucc))

def typedFiber {m} (w n b z : Fin m) : Formula m := .ex
  (((ProjectCompilerCodeSyntax.compiled w.castSucc n.castSucc b.castSucc (Fin.last m)).conj
    (FormulaCodeSyntax.formulaCode w.castSucc (Fin.last m) b.castSucc z.castSucc)).conj
      (uniqueOutput w.castSucc n.castSucc b.castSucc (Fin.last m)))

theorem uniqueOutput_rename {m j} (w n b q : Fin m) (σ : Fin m → Fin j) :
    (uniqueOutput w n b q).rename σ = uniqueOutput (σ w) (σ n) (σ b) (σ q) := by
  simp only [uniqueOutput, Formula.rename, ProjectCompilerCodeSyntax.compiled_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem typedFiber_rename {m j} (w n b z : Fin m) (σ : Fin m → Fin j) :
    (typedFiber w n b z).rename σ = typedFiber (σ w) (σ n) (σ b) (σ z) := by
  simp only [typedFiber, Formula.rename, ProjectCompilerCodeSyntax.compiled_rename, FormulaCodeSyntax.formulaCode_rename,
    uniqueOutput_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

def sourceLawBody {m} (w : Fin m) : Formula (m+4) :=
  (OmegaSyntax.empty (slot 4 3)).imp
    ((ProjectSourceCodeSyntax.sourceCode (old 4 w) (slot 4 0) (slot 4 1) (slot 4 2)).imp
      (typedFiber (old 4 w) (slot 4 0) (slot 4 1) (slot 4 3)))

def allSourceTypedUniqueLaw {m} (w : Fin m) : Formula m := OriginalUniversalBlock.allMany 4 (sourceLawBody w)

theorem sourceLawBody_lift {m j} (w : Fin m) (σ : Fin m → Fin j) :
    (sourceLawBody w).rename (lift 4 σ) = sourceLawBody (σ w) := by
  simp only [sourceLawBody, Formula.rename, OmegaSyntax.empty_rename, ProjectSourceCodeSyntax.sourceCode_rename,
    typedFiber_rename, lift_old, lift_slot]

theorem allSourceTypedUniqueLaw_rename {m j} (w : Fin m) (σ : Fin m → Fin j) :
    (allSourceTypedUniqueLaw w).rename σ = allSourceTypedUniqueLaw (σ w) := by
  simp only [allSourceTypedUniqueLaw, OriginalUniversalBlock.allMany_rename, sourceLawBody_lift]

end PPAC.Migration.Internal.ProjectCompilerUniqueFiberSyntax
