import PPAC.Migration.Internal.ProjectCompilerUniqueMatrixSyntax

/-! Each actual program matrix supplies its exact source constructor, so different modes conflict. -/
namespace PPAC.Migration.Internal.ProjectCompilerUniqueMatrixHead
open Source SourceAlgebra SourceLogic OmegaSyntax ProjectCompilerUniqueMatrixSyntax

theorem source_head {m} {Γ : Context m} (mode : Mode) (w b z n q : Fin m) (xs : Fin 4 → Fin m)
    (hc : Derives Γ (matrix mode w b z n q xs)) :
    Derives Γ (SyntaxNodeSyntax.constructor (arity mode) (tag mode) w (inputs mode xs) n) := by
  cases mode
  · exact (.conjL hc)
  · exact (.conjL hc)
  · exact (.conjR (.conjR (.conjR (.conjL hc))))
  · exact (.conjR (.conjR (.conjR (.conjL hc))))
  · exact (.conjR (.conjR (.conjR (.conjL hc))))
  · exact (.conjL hc)
  · exact (.conjL hc)
  · exact (.conjL hc)
  · exact (.conjL hc)
  · exact (.conjL hc)
  · exact (.conjL hc)
  · exact (.conjL hc)

theorem different_modes {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (a b : Mode) (hab : a ≠ b)
    (w B z n q r : Fin m) (xs ys : Fin 4 → Fin m) (hw : Derives Γ (omega w))
    (hx : Derives Γ (matrix a w B z n q xs)) (hy : Derives Γ (matrix b w B z n r ys)) : Derives Γ .bot := by
  have ht : tag a ≠ tag b := fun h => hab (tag_injective h)
  exact SyntaxConstructors.disjoint hZ (arity a) (arity b) (tag a) (tag b) ht w (inputs a xs) (inputs b ys) n hw
    (source_head a w B z n q xs hx) (source_head b w B z n r ys hy)

end PPAC.Migration.Internal.ProjectCompilerUniqueMatrixHead
