import PPAC.Migration.Internal.ConstantExistingAtomBridge
import PPAC.Migration.Internal.OriginalAtomicRunDispatch

/-! 原mode0／3完整等词运行接入既有等词程序；数值分派和受检项比较均已推导。 -/
namespace PPAC.Migration.Internal.OriginalAtomicExistingAtom
open Source SourceAlgebra SourceLogic OmegaSyntax

theorem replace_equality_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w mode depth a b c L I R n q x y : Fin m)
    (h0 : Derives Γ (omega w))
    (h1 : Derives Γ (SyntaxNumeralSyntax.numeral 3 mode))
    (h2 : Derives Γ (OriginalTermTraceSyntax.metadata w depth L))
    (h3 : Derives Γ (SyntaxIdentityMapSyntax.identityCode w a I))
    (h4 : Derives Γ (IndexTermImageCodeSyntax.converted true w I R a a c))
    (h5 : Derives Γ (SyntaxMixedImageCodeSyntax.termList w b a c L))
    (hn : Derives Γ (SyntaxAtomSyntax.equalCode w x y n))
    (hT : Derives Γ (ArgumentForestProgramSyntax.typedInputs 2 w a b (SyntaxAtomSyntax.two x y))) :
    Derives Γ ((OriginalTransformRowSyntax.run 3 w mode depth L n q).iff (FormulaTransformAtomSyntax.equality w R L a b a c n q)) := by
  have hd := OriginalAtomicRunDispatch.run_iff_equality hZ true w mode depth L n q x y h0 h1 (.conjL h2) (.conjR h2) hn
  exact SyntaxTypeLocalTransfer.iff_trans hd (OriginalEqualityExistingAtom.replace_case_iff hZ w mode depth a b c L I R n q x y h0 h1 h2 h3 h4 h5 hn hT)

theorem weaken_equality_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w mode depth parameter a b B I J R S n q x y : Fin m)
    (h0 : Derives Γ (omega w))
    (h1 : Derives Γ (SyntaxNumeralSyntax.numeral 0 mode))
    (h2 : Derives Γ (OriginalTermTraceSyntax.metadata w depth parameter))
    (h3 : Derives Γ (SyntaxIdentityMapSyntax.identityCode w a I))
    (h4 : Derives Γ (SyntaxFreeShiftSyntax.shiftCode w b B J))
    (h5 : Derives Γ (IndexTermImageCodeSyntax.converted true w I R a a B))
    (h6 : Derives Γ (IndexTermImageCodeSyntax.converted false w J S b a B))
    (hn : Derives Γ (SyntaxAtomSyntax.equalCode w x y n))
    (hT : Derives Γ (ArgumentForestProgramSyntax.typedInputs 2 w a b (SyntaxAtomSyntax.two x y))) :
    Derives Γ ((OriginalTransformRowSyntax.run 3 w mode depth parameter n q).iff (FormulaTransformAtomSyntax.equality w R S a b a B n q)) := by
  have hd := OriginalAtomicRunDispatch.run_iff_equality hZ false w mode depth parameter n q x y h0 h1 (.conjL h2) (.conjR h2) hn
  exact SyntaxTypeLocalTransfer.iff_trans hd (OriginalEqualityExistingAtom.weaken_case_iff hZ w mode depth parameter a b B I J R S n q x y h0 h1 h2 h3 h4 h5 h6 hn hT)

theorem constant_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (three truth : Bool)
    (w mode depth parameter a b c d n q : Fin m)
    (h0 : Derives Γ (omega w))
    (h1 : Derives Γ (SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) mode))
    (h2 : Derives Γ (OriginalTermTraceSyntax.metadata w depth parameter))
    (hn : Derives Γ (SyntaxAtomSyntax.nullary truth w a b n))
    (ht : Derives Γ (SyntaxTermSyntax.contexts w c d)) :
    Derives Γ ((OriginalTransformRowSyntax.run 3 w mode depth parameter n q).iff
      (FormulaTransformAtomSyntax.nullary truth w a b c d n q)) := by
  have hc := ConstantExistingAtomBridge.constant_iff truth w a b c d n q (.conjL hn) ht
  apply SyntaxTypeLocalTransfer.iff_trans (hq := hc)
  cases truth with
  | false => exact OriginalAtomicRunDispatch.run_iff_false hZ three w mode depth parameter n q h0 h1 (.conjL h2) (.conjR h2) (.conjR hn)
  | true => exact OriginalAtomicRunDispatch.run_iff_true hZ three w mode depth parameter n q h0 h1 (.conjL h2) (.conjR h2) (.conjR hn)

end PPAC.Migration.Internal.OriginalAtomicExistingAtom
