import PPAC.Migration.Internal.ProjectCompilerUniqueAtoms

/-! Same-mode logical outputs are equal after object source-field recovery and child IH. -/
namespace PPAC.Migration.Internal.ProjectCompilerUniqueLogical
open Source SourceAlgebra SourceLogic OmegaSyntax ProjectCompilerCaseSyntax ProjectCompilerRecursiveSyntax ProjectCompilerUniqueSyntax

theorem single_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (tag : Nat) (advance : Bool)
    (w b n q r x y u v : Fin m) (hw : Derives Γ (omega w)) (hI : Derives Γ (allIH w n))
    (hq : Derives Γ (singleMatrix tag advance codeMatrix (parameters w) w b n q x y))
    (hr : Derives Γ (singleMatrix tag advance codeMatrix (parameters w) w b n r u v)) : Derives Γ (.equal q r) := by
  have he := SyntaxNodeInjective.constructor_input_eq hZ 1 tag tag w (fun _ => x) (fun _ => u) n 0 hw (.conjL hq) (.conjL hr)
  have hrCheck := ProjectCompilerUniqueTransport.check_input advance w n u b v x (eq_symm he) (.conjL (.conjR hr))
  have hy := ProjectCompilerUniqueQueries.check_unique hZ advance w n x b y v hI (.conjL (.conjR hq)) hrCheck
  have hrTarget := ProjectCompilerUniqueTransport.single_input tag w v r y (eq_symm hy) (.conjR (.conjR hr))
  exact SyntaxConstructors.unique hZ 1 tag w (fun _ => y) q r hw (.conjR (.conjR hq)) hrTarget

theorem binary_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Fin 4)
    (w b n q r x y X Y u v U V : Fin m) (hw : Derives Γ (omega w)) (hI : Derives Γ (allIH w n))
    (hq : Derives Γ (binaryMatrix kind codeMatrix (parameters w) w b n q x y X Y))
    (hr : Derives Γ (binaryMatrix kind codeMatrix (parameters w) w b n r u v U V)) : Derives Γ (.equal q r) := by
  have heX := SyntaxNodeInjective.constructor_input_eq hZ 2 (SyntaxLogicalSyntax.binaryTag kind) (SyntaxLogicalSyntax.binaryTag kind)
    w (SyntaxAtomSyntax.two x y) (SyntaxAtomSyntax.two u v) n 0 hw (.conjL hq) (.conjL hr)
  have heY := SyntaxNodeInjective.constructor_input_eq hZ 2 (SyntaxLogicalSyntax.binaryTag kind) (SyntaxLogicalSyntax.binaryTag kind)
    w (SyntaxAtomSyntax.two x y) (SyntaxAtomSyntax.two u v) n 1 hw (.conjL hq) (.conjL hr)
  have hrX := ProjectCompilerUniqueTransport.check_input false w n u b U x (eq_symm heX) (.conjL (.conjR hr))
  have hrY := ProjectCompilerUniqueTransport.check_input false w n v b V y (eq_symm heY) (.conjL (.conjR (.conjR hr)))
  have hX := ProjectCompilerUniqueQueries.query_unique w n x b X U hI (.conjL (.conjR hq)) hrX
  have hY := ProjectCompilerUniqueQueries.query_unique w n y b Y V hI (.conjL (.conjR (.conjR hq))) hrY
  have htX := ProjectCompilerUniqueTransport.binary_left kind w U V r X (eq_symm hX) (.conjR (.conjR (.conjR hr)))
  have htY := ProjectCompilerUniqueTransport.binary_right kind w X V r Y (eq_symm hY) htX
  exact SyntaxConstructors.unique hZ 2 (SyntaxLogicalSyntax.binaryTag kind) w (SyntaxAtomSyntax.two X Y) q r hw
    (.conjR (.conjR (.conjR hq))) htY

end PPAC.Migration.Internal.ProjectCompilerUniqueLogical
