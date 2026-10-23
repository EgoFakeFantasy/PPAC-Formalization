import PPAC.Migration.Internal.AtomicTermAgreement

/-! 原等词局部二元分支与既有受检项程序等词分支双向对应。 -/
namespace PPAC.Migration.Internal.EqualityExistingAtomBridge
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem iff_existing {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w mode depth parameter R S a b c d x y n q : Fin m) (hw : Derives Γ (omega w))
    (hn : Derives Γ (SyntaxAtomSyntax.equalCode w x y n))
    (ht : Derives Γ (ArgumentForestProgramSyntax.typedInputs 2 w a b (SyntaxAtomSyntax.two x y)))
    (ha : Derives Γ (AtomicTermAgreementSyntax.agreement w mode depth parameter R S a b c d)) :
    Derives Γ ((OriginalFormulaCaseSyntax.binaryCase 3 1 w mode depth parameter n q).iff
      (FormulaTransformAtomSyntax.equality w R S a b c d n q)) := by
  apply Derives.conjI
  · apply Derives.impI
    let E := OriginalFormulaCaseSyntax.binaryCase 3 1 w mode depth parameter n q
    let B := OriginalFormulaCaseSyntax.binaryBody 3 1 w mode depth parameter n q
    let Δ := Context.add B (raisedContext 4 (Context.add E Γ))
    apply HornBinderRules.eliminate_many 4 B _ (.hyp (Or.inl rfl))
    have hZ1 := HornBinderRules.zf_body 4 (ZFContext.add hZ E) B
    have lift {p : Formula m} (h : Derives Γ p) : Derives Δ (p.rename (old 4)) := HornBinderRules.under_body 4 (add h E) B
    have hw1 : Derives Δ (omega (old 4 w)) := of_eq (omega_rename w (old 4)) (lift hw)
    have hn1 : Derives Δ (SyntaxAtomSyntax.equalCode (old 4 w) (old 4 x) (old 4 y) (old 4 n)) := of_eq (SyntaxAtomSyntax.equalCode_rename w x y n (old 4)) (lift hn)
    have ht1 : Derives Δ (ArgumentForestProgramSyntax.typedInputs 2 (old 4 w) (old 4 a) (old 4 b) (SyntaxAtomSyntax.two (old 4 x) (old 4 y))) := of_eq (by simp only [ArgumentForestProgramSyntax.typedInputs_rename, SyntaxAtomSyntax.two_map]) (lift ht)
    have ha1 : Derives Δ (AtomicTermAgreementSyntax.agreement (old 4 w) (old 4 mode) (old 4 depth) (old 4 parameter) (old 4 R) (old 4 S) (old 4 a) (old 4 b) (old 4 c) (old 4 d)) := of_eq (AtomicTermAgreementSyntax.agreement_rename w mode depth parameter R S a b c d (old 4)) (lift ha)
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have hX := SyntaxNodeInjective.constructor_input_eq hZ1 2 3 3 (old 4 w) (SyntaxAtomSyntax.two (slot 4 0) (slot 4 1)) (SyntaxAtomSyntax.two (old 4 x) (old 4 y)) (old 4 n) 0 hw1 (.conjL (.conjL hB)) hn1
    have hY := SyntaxNodeInjective.constructor_input_eq hZ1 2 3 3 (old 4 w) (SyntaxAtomSyntax.two (slot 4 0) (slot 4 1)) (SyntaxAtomSyntax.two (old 4 x) (old 4 y)) (old 4 n) 1 hw1 (.conjL (.conjL hB)) hn1
    have htx := TypedArgumentListConstruction.term_output_subst _ _ _ _ _ (eq_symm hX) (ArgumentForestProgramSyntax.typed_at 2 _ _ _ _ ht1 0)
    have hty := TypedArgumentListConstruction.term_output_subst _ _ _ _ _ (eq_symm hY) (ArgumentForestProgramSyntax.typed_at 2 _ _ _ _ ht1 1)
    have hxC := Derives.impE (.conjL (AtomicTermAgreementSyntax.agreement_at _ _ _ _ _ _ _ _ _ _ (slot 4 0) (slot 4 2) ha1 htx)) (.conjL (.conjR hB))
    have hyC := Derives.impE (.conjL (AtomicTermAgreementSyntax.agreement_at _ _ _ _ _ _ _ _ _ _ (slot 4 1) (slot 4 3) ha1 hty)) (.conjR (.conjR hB))
    have hx := AtomicTermAgreementSyntax.checked_input_subst _ _ _ _ _ _ _ _ _ _ hX hxC
    have hy := AtomicTermAgreementSyntax.checked_input_subst _ _ _ _ _ _ _ _ _ _ hY hyC
    have hData := Derives.conjI hn1 (.conjI (.conjR (.conjL hB)) (.conjI hx hy))
    have ho := FormulaTransformAtomSyntax.intro_equality (old 4 w) (old 4 R) (old 4 S) (old 4 a) (old 4 b) (old 4 c) (old 4 d) (old 4 n) (old 4 q) (old 4 x) (old 4 y) (slot 4 2) (slot 4 3) hData
    exact of_eq (FormulaTransformAtomSyntax.equality_rename w R S a b c d n q (old 4)).symm ho
  · apply Derives.impI
    let E := FormulaTransformAtomSyntax.equality w R S a b c d n q
    let B := FormulaTransformAtomSyntax.equalityBody w R S a b c d n q
    let Δ := Context.add B (raisedContext 4 (Context.add E Γ))
    apply HornBinderRules.eliminate_many 4 B _ (.hyp (Or.inl rfl))
    have hZ1 := HornBinderRules.zf_body 4 (ZFContext.add hZ E) B
    have lift {p : Formula m} (h : Derives Γ p) : Derives Δ (p.rename (old 4)) := HornBinderRules.under_body 4 (add h E) B
    have hw1 : Derives Δ (omega (old 4 w)) := of_eq (omega_rename w (old 4)) (lift hw)
    have hn1 : Derives Δ (SyntaxAtomSyntax.equalCode (old 4 w) (old 4 x) (old 4 y) (old 4 n)) := of_eq (SyntaxAtomSyntax.equalCode_rename w x y n (old 4)) (lift hn)
    have ht1 : Derives Δ (ArgumentForestProgramSyntax.typedInputs 2 (old 4 w) (old 4 a) (old 4 b) (SyntaxAtomSyntax.two (old 4 x) (old 4 y))) := of_eq (by simp only [ArgumentForestProgramSyntax.typedInputs_rename, SyntaxAtomSyntax.two_map]) (lift ht)
    have ha1 : Derives Δ (AtomicTermAgreementSyntax.agreement (old 4 w) (old 4 mode) (old 4 depth) (old 4 parameter) (old 4 R) (old 4 S) (old 4 a) (old 4 b) (old 4 c) (old 4 d)) := of_eq (AtomicTermAgreementSyntax.agreement_rename w mode depth parameter R S a b c d (old 4)) (lift ha)
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have hX := SyntaxNodeInjective.constructor_input_eq hZ1 2 3 3 (old 4 w) (SyntaxAtomSyntax.two (slot 4 0) (slot 4 1)) (SyntaxAtomSyntax.two (old 4 x) (old 4 y)) (old 4 n) 0 hw1 (.conjL hB) hn1
    have hY := SyntaxNodeInjective.constructor_input_eq hZ1 2 3 3 (old 4 w) (SyntaxAtomSyntax.two (slot 4 0) (slot 4 1)) (SyntaxAtomSyntax.two (old 4 x) (old 4 y)) (old 4 n) 1 hw1 (.conjL hB) hn1
    have hxC := AtomicTermAgreementSyntax.checked_input_subst _ _ _ _ _ _ _ _ _ _ hX (.conjL (.conjR (.conjR hB)))
    have hyC := AtomicTermAgreementSyntax.checked_input_subst _ _ _ _ _ _ _ _ _ _ hY (.conjR (.conjR (.conjR hB)))
    have hx := Derives.impE (.conjR (AtomicTermAgreementSyntax.agreement_at _ _ _ _ _ _ _ _ _ _ (old 4 x) (slot 4 2) ha1 (ArgumentForestProgramSyntax.typed_at 2 _ _ _ _ ht1 0))) hxC
    have hy := Derives.impE (.conjR (AtomicTermAgreementSyntax.agreement_at _ _ _ _ _ _ _ _ _ _ (old 4 y) (slot 4 3) ha1 (ArgumentForestProgramSyntax.typed_at 2 _ _ _ _ ht1 1))) hyC
    have hData := Derives.conjI (Derives.conjI hn1 (.conjL (.conjR hB))) (.conjI hx hy)
    have ho := OriginalFormulaCaseSyntax.intro_binary 3 1 (old 4 w) (old 4 mode) (old 4 depth) (old 4 parameter) (old 4 n) (old 4 q) (old 4 x) (old 4 y) (slot 4 2) (slot 4 3) hData
    exact of_eq (OriginalFormulaCaseSyntax.binaryCase_rename 3 1 w mode depth parameter n q (old 4)).symm ho

end PPAC.Migration.Internal.EqualityExistingAtomBridge
