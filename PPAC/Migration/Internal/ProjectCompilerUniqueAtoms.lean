import PPAC.Migration.Internal.ProjectCompilerUniqueQueries

/-! Scalar uniqueness for actual constants and atoms with object source-field recovery. -/
namespace PPAC.Migration.Internal.ProjectCompilerUniqueAtoms
open Source SourceAlgebra SourceLogic OmegaSyntax

theorem constant_unique {m} {Γ : Context m} (truth : Bool) (w n q r : Fin m)
    (hq : Derives Γ (ProjectCompilerCaseSyntax.constant truth w n q))
    (hr : Derives Γ (ProjectCompilerCaseSyntax.constant truth w n r)) : Derives Γ (.equal q r) :=
  eq_trans (.conjR hq) (eq_symm (.conjR hr))

theorem atomic_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Fin 3)
    (w b z x y u v n q r : Fin m) (hw : Derives Γ (omega w))
    (hq : Derives Γ (ProjectAtomicSyntax.compiled kind w b z x y n q))
    (hr : Derives Γ (ProjectAtomicSyntax.compiled kind w b z u v n r)) : Derives Γ (.equal q r) := by
  have heX := SyntaxNodeInjective.constructor_input_eq hZ 2 (ProjectAtomicSyntax.sourceTag kind) (ProjectAtomicSyntax.sourceTag kind)
    w (SyntaxAtomSyntax.two x y) (SyntaxAtomSyntax.two u v) n 0 hw
    (.conjR (.conjR (.conjR (.conjL hq)))) (.conjR (.conjR (.conjR (.conjL hr))))
  have heY := SyntaxNodeInjective.constructor_input_eq hZ 2 (ProjectAtomicSyntax.sourceTag kind) (ProjectAtomicSyntax.sourceTag kind)
    w (SyntaxAtomSyntax.two x y) (SyntaxAtomSyntax.two u v) n 1 hw
    (.conjR (.conjR (.conjR (.conjL hq)))) (.conjR (.conjR (.conjR (.conjL hr))))
  have hrX := ProjectCompilerUniqueTransport.atomic_left kind w b z u v n r x (eq_symm heX) hr
  have hrY := ProjectCompilerUniqueTransport.atomic_right kind w b z x v n r y (eq_symm heY) hrX
  exact ProjectAtomicLaws.compiled_unique hZ kind w b z x y n q r hw hq hrY

end PPAC.Migration.Internal.ProjectCompilerUniqueAtoms
