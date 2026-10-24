import PPAC.Migration.Internal.SmallModeAtomicDispatch
import PPAC.Migration.Internal.AbstractFrameAtomicAgreement
import PPAC.Migration.Internal.MemberExistingAtomBridge
import PPAC.Migration.Internal.EqualityExistingAtomBridge
import PPAC.Migration.Internal.ConstantExistingAtomBridge

/-! mode1在任意内部深度frame的实际原子输入处，原完整Run3接既有四原子操作。 -/
namespace PPAC.Migration.Internal.AbstractFrameAtomicExisting
open Source SourceAlgebra SourceLogic OmegaSyntax AbstractOperationFrameSyntax

theorem membership_at {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w mode depth P a b c e R S n q x y s : Fin m)
    (hw : Derives Γ (omega w)) (hF : Derives Γ (frame w mode depth P a b c e R S))
    (hs : Derives Γ (SyntaxAtomSyntax.zeroScalar w s)) (hn : Derives Γ (SyntaxAtomSyntax.memberCode w s x y n))
    (hT : Derives Γ (ArgumentForestProgramSyntax.typedInputs 2 w a b (SyntaxAtomSyntax.two x y))) :
    Derives Γ ((OriginalTransformRowSyntax.run 3 w mode depth P n q).iff (FormulaTransformAtomSyntax.membership w R S a b c e n q)) := by
  have hd := metadata w mode depth P a b c e R S hF
  have hDispatch := SmallModeAtomicDispatch.run_iff_application hZ 1 (by decide) w mode depth P s x y n q hw (mode_number w mode depth P a b c e R S hF) (.conjL hd) (.conjR hd) hn
  have hAgreement := AbstractFrameAtomicAgreement.pair_agreement hZ w mode depth P a b c e R S x y hw hF hT
  have hInputs := MemberProgramSyntax.inputs_from_types hZ w a b x y hw hT
  have hLocal := MemberProgramCase.application_iff hZ w mode depth P R S c e s x y n q hw hs hn hInputs hAgreement
  have hExisting := MemberExistingAtomBridge.iff_existing hZ w R S a b c e s x y n q hw hs hn hT (term_lists w mode depth P a b c e R S hF)
  exact SyntaxTypeLocalTransfer.iff_trans hDispatch (SyntaxTypeLocalTransfer.iff_trans hLocal hExisting)

theorem equality_at {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w mode depth P a b c e R S n q x y : Fin m)
    (hw : Derives Γ (omega w)) (hF : Derives Γ (frame w mode depth P a b c e R S))
    (hn : Derives Γ (SyntaxAtomSyntax.equalCode w x y n))
    (hT : Derives Γ (ArgumentForestProgramSyntax.typedInputs 2 w a b (SyntaxAtomSyntax.two x y))) :
    Derives Γ ((OriginalTransformRowSyntax.run 3 w mode depth P n q).iff (FormulaTransformAtomSyntax.equality w R S a b c e n q)) := by
  have hd := metadata w mode depth P a b c e R S hF
  have hDispatch := SmallModeAtomicDispatch.run_iff_equality hZ 1 (by decide) w mode depth P n q x y hw (mode_number w mode depth P a b c e R S hF) (.conjL hd) (.conjR hd) hn
  have hAgreement := AbstractFrameAtomicAgreement.terms hZ w mode depth P a b c e R S hw hF
  exact SyntaxTypeLocalTransfer.iff_trans hDispatch (EqualityExistingAtomBridge.iff_existing hZ w mode depth P R S a b c e x y n q hw hn hT hAgreement)

theorem constant_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (truth : Bool) (w mode depth P a b c e R S n q : Fin m)
    (hw : Derives Γ (omega w)) (hF : Derives Γ (frame w mode depth P a b c e R S))
    (hn : Derives Γ (SyntaxAtomSyntax.nullary truth w a b n)) :
    Derives Γ ((OriginalTransformRowSyntax.run 3 w mode depth P n q).iff (FormulaTransformAtomSyntax.nullary truth w a b c e n q)) := by
  have hm := mode_number w mode depth P a b c e R S hF
  have hd := metadata w mode depth P a b c e R S hF
  have ht : Derives Γ (SyntaxTermSyntax.contexts w c e) := .conjL (.conjR (.conjL (term_lists w mode depth P a b c e R S hF)))
  have hc := ConstantExistingAtomBridge.constant_iff truth w a b c e n q (.conjL hn) ht
  apply SyntaxTypeLocalTransfer.iff_trans (hq := hc)
  cases truth
  · exact SmallModeAtomicDispatch.run_iff_false hZ 1 (by decide) w mode depth P n q hw hm (.conjL hd) (.conjR hd) (.conjR hn)
  · exact SmallModeAtomicDispatch.run_iff_true hZ 1 (by decide) w mode depth P n q hw hm (.conjL hd) (.conjR hd) (.conjR hn)

end PPAC.Migration.Internal.AbstractFrameAtomicExisting
