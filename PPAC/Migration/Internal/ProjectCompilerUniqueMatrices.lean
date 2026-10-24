import PPAC.Migration.Internal.ProjectCompilerUniqueLogical

/-! Each of the twelve actual matrices is scalar-functional under the internal member hypothesis. -/
namespace PPAC.Migration.Internal.ProjectCompilerUniqueMatrices
open Source SourceAlgebra SourceLogic OmegaSyntax ProjectCompilerUniqueSyntax ProjectCompilerUniqueMatrixSyntax

theorem same_mode {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (mode : Mode)
    (w b z n q r : Fin m) (xs ys : Fin 4 → Fin m) (hw : Derives Γ (omega w)) (hI : Derives Γ (allIH w n))
    (hq : Derives Γ (matrix mode w b z n q xs)) (hr : Derives Γ (matrix mode w b z n r ys)) : Derives Γ (.equal q r) := by
  cases mode
  · exact ProjectCompilerUniqueAtoms.constant_unique false w n q r hq hr
  · exact ProjectCompilerUniqueAtoms.constant_unique true w n q r hq hr
  · exact ProjectCompilerUniqueAtoms.atomic_unique hZ 0 w b z (xs 0) (xs 1) (ys 0) (ys 1) n q r hw hq hr
  · exact ProjectCompilerUniqueAtoms.atomic_unique hZ 1 w b z (xs 0) (xs 1) (ys 0) (ys 1) n q r hw hq hr
  · exact ProjectCompilerUniqueAtoms.atomic_unique hZ 2 w b z (xs 0) (xs 1) (ys 0) (ys 1) n q r hw hq hr
  · exact ProjectCompilerUniqueLogical.single_unique hZ 4 false w b n q r (xs 0) (xs 1) (ys 0) (ys 1) hw hI hq hr
  · exact ProjectCompilerUniqueLogical.binary_unique hZ 0 w b n q r (xs 0) (xs 1) (xs 2) (xs 3) (ys 0) (ys 1) (ys 2) (ys 3) hw hI hq hr
  · exact ProjectCompilerUniqueLogical.binary_unique hZ 1 w b n q r (xs 0) (xs 1) (xs 2) (xs 3) (ys 0) (ys 1) (ys 2) (ys 3) hw hI hq hr
  · exact ProjectCompilerUniqueLogical.binary_unique hZ 2 w b n q r (xs 0) (xs 1) (xs 2) (xs 3) (ys 0) (ys 1) (ys 2) (ys 3) hw hI hq hr
  · exact ProjectCompilerUniqueLogical.binary_unique hZ 3 w b n q r (xs 0) (xs 1) (xs 2) (xs 3) (ys 0) (ys 1) (ys 2) (ys 3) hw hI hq hr
  · exact ProjectCompilerUniqueLogical.single_unique hZ 9 true w b n q r (xs 0) (xs 1) (ys 0) (ys 1) hw hI hq hr
  · exact ProjectCompilerUniqueLogical.single_unique hZ 10 true w b n q r (xs 0) (xs 1) (ys 0) (ys 1) hw hI hq hr

theorem any_modes {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (a c : Mode)
    (w b z n q r : Fin m) (xs ys : Fin 4 → Fin m) (hw : Derives Γ (omega w)) (hI : Derives Γ (allIH w n))
    (hq : Derives Γ (matrix a w b z n q xs)) (hr : Derives Γ (matrix c w b z n r ys)) : Derives Γ (.equal q r) := by
  by_cases h : a = c
  · subst c
    exact same_mode hZ a w b z n q r xs ys hw hI hq hr
  · exact .botE (ProjectCompilerUniqueMatrixHead.different_modes hZ a c h w b z n q r xs ys hw hq hr)

end PPAC.Migration.Internal.ProjectCompilerUniqueMatrices
