import PPAC.Migration.Internal.ObjectProjectCompilerComplete

/-! The scalar-functionality property and its complete internal member induction hypothesis. -/
namespace PPAC.Migration.Internal.ProjectCompilerUniqueSyntax
open Source SourceAlgebra SourceLogic HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)

def propertyBody {m} (w n : Fin m) : Formula (m+3) :=
  (ProjectCompilerCodeSyntax.compiled (old 3 w) (old 3 n) (slot 3 0) (slot 3 1)).imp
    ((ProjectCompilerCodeSyntax.compiled (old 3 w) (old 3 n) (slot 3 0) (slot 3 2)).imp
      (.equal (slot 3 1) (slot 3 2)))

def functional {m} (w n : Fin m) : Formula m := OriginalUniversalBlock.allMany 3 (propertyBody w n)

theorem propertyBody_lift {m j} (w n : Fin m) (σ : Fin m → Fin j) :
    (propertyBody w n).rename (lift 3 σ) = propertyBody (σ w) (σ n) := by
  simp only [propertyBody, Formula.rename, ProjectCompilerCodeSyntax.compiled_rename, lift_old, lift_slot]

theorem functional_rename {m j} (w n : Fin m) (σ : Fin m → Fin j) :
    (functional w n).rename σ = functional (σ w) (σ n) := by
  simp only [functional, OriginalUniversalBlock.allMany_rename, propertyBody_lift]

theorem unique_at {m} {Γ : Context m} (w n b q r : Fin m) (hf : Derives Γ (functional w n))
    (hq : Derives Γ (ProjectCompilerCodeSyntax.compiled w n b q))
    (hr : Derives Γ (ProjectCompilerCodeSyntax.compiled w n b r)) : Derives Γ (.equal q r) := by
  have ha := OriginalUniversalBlock.at_many 3 (propertyBody w n) (SyntaxAtomSyntax.three b q r) hf
  have hi : Derives Γ ((ProjectCompilerCodeSyntax.compiled w n b q).imp
      ((ProjectCompilerCodeSyntax.compiled w n b r).imp (.equal q r))) :=
    of_eq (by simp only [propertyBody, Formula.rename, ProjectCompilerCodeSyntax.compiled_rename, assign_old, assign_slot]; rfl) ha
  exact .impE (.impE hi hq) hr

def allIH {m} (w n : Fin m) : Formula m := .all
  ((Formula.mem (Fin.last m) n.castSucc).imp (functional w.castSucc (Fin.last m)))

theorem allIH_rename {m j} (w n : Fin m) (σ : Fin m → Fin j) :
    (allIH w n).rename σ = allIH (σ w) (σ n) := by
  simp only [allIH, Formula.rename, functional_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem below_functional {m} {Γ : Context m} (w n x : Fin m)
    (hI : Derives Γ (allIH w n)) (hx : Derives Γ (.mem x n)) : Derives Γ (functional w x) := by
  have ha := Derives.allE x hI
  have hi : Derives Γ ((Formula.mem x n).imp (functional w x)) :=
    of_eq (by simp only [Formula.instantiate, Formula.rename, functional_rename,
      Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) ha
  exact .impE hi hx

end PPAC.Migration.Internal.ProjectCompilerUniqueSyntax
