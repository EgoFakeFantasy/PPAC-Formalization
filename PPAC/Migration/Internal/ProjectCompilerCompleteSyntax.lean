import PPAC.Migration.Internal.ObjectProjectCompilerTyping

/-! Object source-completeness property, with arbitrary internal source contexts and actual output witnesses. -/
namespace PPAC.Migration.Internal.ProjectCompilerCompleteSyntax
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)

def existsOutput {m} (w n b : Fin m) : Formula m := .ex
  (ProjectCompilerCodeSyntax.compiled w.castSucc n.castSucc b.castSucc (Fin.last m))

theorem existsOutput_rename {m j} (w n b : Fin m) (σ : Fin m → Fin j) :
    (existsOutput w n b).rename σ = existsOutput (σ w) (σ n) (σ b) := by
  simp only [existsOutput, Formula.rename, ProjectCompilerCodeSyntax.compiled_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem intro_output {m} {Γ : Context m} (w n b q : Fin m)
    (hc : Derives Γ (ProjectCompilerCodeSyntax.compiled w n b q)) : Derives Γ (existsOutput w n b) := by
  apply Derives.exI q
  exact of_eq (by simp only [Formula.instantiate, ProjectCompilerCodeSyntax.compiled_rename,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hc

def propertyBody {m} (w n : Fin m) : Formula (m+3) :=
  (empty (slot 3 2)).imp ((ProjectSourceCodeSyntax.sourceCode (old 3 w) (old 3 n) (slot 3 0) (slot 3 1)).imp
    (existsOutput (old 3 w) (old 3 n) (slot 3 0)))

def correct {m} (w n : Fin m) : Formula m := OriginalUniversalBlock.allMany 3 (propertyBody w n)

theorem propertyBody_lift {m j} (w n : Fin m) (σ : Fin m → Fin j) :
    (propertyBody w n).rename (lift 3 σ) = propertyBody (σ w) (σ n) := by
  simp only [propertyBody, Formula.rename, empty_rename, ProjectSourceCodeSyntax.sourceCode_rename,
    existsOutput_rename, lift_old, lift_slot]

theorem correct_rename {m j} (w n : Fin m) (σ : Fin m → Fin j) :
    (correct w n).rename σ = correct (σ w) (σ n) := by
  simp only [correct, OriginalUniversalBlock.allMany_rename, propertyBody_lift]

theorem at_correct {m} {Γ : Context m} (w n b f z : Fin m) (hc : Derives Γ (correct w n))
    (hz : Derives Γ (empty z)) (hi : Derives Γ (ProjectSourceCodeSyntax.sourceCode w n b f)) :
    Derives Γ (existsOutput w n b) := by
  have ha := OriginalUniversalBlock.at_many 3 (propertyBody w n) (SyntaxAtomSyntax.three b f z) hc
  have hr : Derives Γ ((empty z).imp ((ProjectSourceCodeSyntax.sourceCode w n b f).imp (existsOutput w n b))) :=
    of_eq (by simp only [propertyBody, Formula.rename, empty_rename, ProjectSourceCodeSyntax.sourceCode_rename,
      existsOutput_rename, assign_old, assign_slot]; rfl) ha
  exact .impE (.impE hr hz) hi

def allIH {m} (w n : Fin m) : Formula m := .all
  ((Formula.mem (Fin.last m) n.castSucc).imp (correct w.castSucc (Fin.last m)))

theorem allIH_rename {m j} (w n : Fin m) (σ : Fin m → Fin j) :
    (allIH w n).rename σ = allIH (σ w) (σ n) := by
  simp only [allIH, Formula.rename, correct_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem below_correct {m} {Γ : Context m} (w n x : Fin m)
    (hI : Derives Γ (allIH w n)) (hx : Derives Γ (.mem x n)) : Derives Γ (correct w x) := by
  have ha := Derives.allE x hI
  have hr : Derives Γ ((Formula.mem x n).imp (correct w x)) :=
    of_eq (by simp only [Formula.instantiate, Formula.rename, correct_rename,
      Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) ha
  exact .impE hr hx

end PPAC.Migration.Internal.ProjectCompilerCompleteSyntax
