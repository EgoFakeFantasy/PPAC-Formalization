import PPAC.Migration.Internal.OriginalLogicalChildTypes

/-! 非量词连接词的真实原子运行与既有历史read分支；内部子码归纳比较前提显式保留。 -/
namespace PPAC.Migration.Internal.OriginalLogicalCaseBridge
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem negation_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w mode depth parameter h R S a b c d n q : Fin m) (hw : Derives Γ (omega w))
    (hn : Derives Γ (FormulaCodeSyntax.formulaCode w n a b))
    (ha : Derives Γ (OriginalFormulaHistoryAgreementSyntax.agreement w mode depth parameter h R S a b c d n)) :
    Derives Γ ((OriginalFormulaCaseSyntax.unaryCase 4 w mode depth parameter n q).iff (FormulaTransformLogicalSyntax.single 4 false w h R S a b c d n q)) := by
  apply Derives.conjI
  · apply Derives.impI
    let E := OriginalFormulaCaseSyntax.unaryCase 4 w mode depth parameter n q
    let F := OriginalFormulaCaseSyntax.unaryBody 4 w mode depth parameter n q
    let Δ := Context.add F (raisedContext 2 (Context.add E Γ))
    apply HornBinderRules.eliminate_many 2 F _ (.hyp (Or.inl rfl))
    have hZ1 := HornBinderRules.zf_body 2 (ZFContext.add hZ E) F
    have lift {p : Formula m} (hp : Derives Γ p) : Derives Δ (p.rename (old 2)) := HornBinderRules.under_body 2 (add hp E) F
    have hw1 : Derives Δ (omega (old 2 w)) := of_eq (omega_rename w (old 2)) (lift hw)
    have hn1 : Derives Δ (FormulaCodeSyntax.formulaCode (old 2 w) (old 2 n) (old 2 a) (old 2 b)) := of_eq (FormulaCodeSyntax.formulaCode_rename w n a b (old 2)) (lift hn)
    have ha1 : Derives Δ (OriginalFormulaHistoryAgreementSyntax.agreement (old 2 w) (old 2 mode) (old 2 depth) (old 2 parameter) (old 2 h) (old 2 R) (old 2 S) (old 2 a) (old 2 b) (old 2 c) (old 2 d) (old 2 n)) := of_eq (OriginalFormulaHistoryAgreementSyntax.agreement_rename w mode depth parameter h R S a b c d n (old 2)) (lift ha)
    have hF : Derives Δ F := .hyp (Or.inl rfl)
    have hSource := Derives.conjL (Derives.conjL hF)
    have ht := OriginalLogicalChildTypes.negation hZ1 (old 2 w) (old 2 a) (old 2 b) (old 2 n) (slot 2 0) hw1 hn1 hSource
    have hx := SyntaxConstructors.child_member hZ1 1 4 (old 2 w) (fun _ => slot 2 0) (old 2 n) 0 hw1 hSource
    have he := OriginalFormulaHistoryAgreementSyntax.agreement_at (old 2 w) (old 2 mode) (old 2 depth) (old 2 parameter) (old 2 h) (old 2 R) (old 2 S) (old 2 a) (old 2 b) (old 2 c) (old 2 d) (old 2 n) (slot 2 0) (slot 2 1) ha1 hx ht
    have ho := FormulaTransformLogicalSyntax.intro_single 4 false (old 2 w) (old 2 h) (old 2 R) (old 2 S) (old 2 a) (old 2 b) (old 2 c) (old 2 d) (old 2 n) (old 2 q) (slot 2 0) (slot 2 1) (.conjI hSource (.conjI hx (.conjI (.conjR (.conjL hF)) (.impE (.conjL he) (.conjR hF)))))
    exact of_eq (FormulaTransformLogicalSyntax.single_rename 4 false w h R S a b c d n q (old 2)).symm ho
  · apply Derives.impI
    let E := FormulaTransformLogicalSyntax.single 4 false w h R S a b c d n q
    let F := FormulaTransformLogicalSyntax.singleBody 4 false w h R S a b c d n q
    let Δ := Context.add F (raisedContext 2 (Context.add E Γ))
    apply HornBinderRules.eliminate_many 2 F _ (.hyp (Or.inl rfl))
    have hZ1 := HornBinderRules.zf_body 2 (ZFContext.add hZ E) F
    have lift {p : Formula m} (hp : Derives Γ p) : Derives Δ (p.rename (old 2)) := HornBinderRules.under_body 2 (add hp E) F
    have hw1 : Derives Δ (omega (old 2 w)) := of_eq (omega_rename w (old 2)) (lift hw)
    have hn1 : Derives Δ (FormulaCodeSyntax.formulaCode (old 2 w) (old 2 n) (old 2 a) (old 2 b)) := of_eq (FormulaCodeSyntax.formulaCode_rename w n a b (old 2)) (lift hn)
    have ha1 : Derives Δ (OriginalFormulaHistoryAgreementSyntax.agreement (old 2 w) (old 2 mode) (old 2 depth) (old 2 parameter) (old 2 h) (old 2 R) (old 2 S) (old 2 a) (old 2 b) (old 2 c) (old 2 d) (old 2 n)) := of_eq (OriginalFormulaHistoryAgreementSyntax.agreement_rename w mode depth parameter h R S a b c d n (old 2)) (lift ha)
    have hF : Derives Δ F := .hyp (Or.inl rfl)
    have hSource := Derives.conjL hF
    have ht := OriginalLogicalChildTypes.negation hZ1 (old 2 w) (old 2 a) (old 2 b) (old 2 n) (slot 2 0) hw1 hn1 hSource
    have hx := Derives.conjL (Derives.conjR hF)
    have he := OriginalFormulaHistoryAgreementSyntax.agreement_at (old 2 w) (old 2 mode) (old 2 depth) (old 2 parameter) (old 2 h) (old 2 R) (old 2 S) (old 2 a) (old 2 b) (old 2 c) (old 2 d) (old 2 n) (slot 2 0) (slot 2 1) ha1 hx ht
    have ho := OriginalFormulaCaseSyntax.intro_unary 4 (old 2 w) (old 2 mode) (old 2 depth) (old 2 parameter) (old 2 n) (old 2 q) (slot 2 0) (slot 2 1) (.conjI (.conjI hSource (.conjL (.conjR (.conjR hF)))) (.impE (.conjR he) (.conjR (.conjR (.conjR hF)))))
    exact of_eq (OriginalFormulaCaseSyntax.unaryCase_rename 4 w mode depth parameter n q (old 2)).symm ho

theorem binary_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Fin 4)
    (w mode depth parameter h R S a b c d n q : Fin m) (hw : Derives Γ (omega w))
    (hn : Derives Γ (FormulaCodeSyntax.formulaCode w n a b))
    (ha : Derives Γ (OriginalFormulaHistoryAgreementSyntax.agreement w mode depth parameter h R S a b c d n)) :
    Derives Γ ((OriginalFormulaCaseSyntax.binaryCase (SyntaxLogicalSyntax.binaryTag kind) 3 w mode depth parameter n q).iff (FormulaTransformLogicalSyntax.binary kind w h R S a b c d n q)) := by
  apply Derives.conjI
  · apply Derives.impI
    let E := OriginalFormulaCaseSyntax.binaryCase (SyntaxLogicalSyntax.binaryTag kind) 3 w mode depth parameter n q
    let F := OriginalFormulaCaseSyntax.binaryBody (SyntaxLogicalSyntax.binaryTag kind) 3 w mode depth parameter n q
    let Δ := Context.add F (raisedContext 4 (Context.add E Γ))
    apply HornBinderRules.eliminate_many 4 F _ (.hyp (Or.inl rfl))
    have hZ1 := HornBinderRules.zf_body 4 (ZFContext.add hZ E) F
    have lift {p : Formula m} (hp : Derives Γ p) : Derives Δ (p.rename (old 4)) := HornBinderRules.under_body 4 (add hp E) F
    have hw1 : Derives Δ (omega (old 4 w)) := of_eq (omega_rename w (old 4)) (lift hw)
    have hn1 : Derives Δ (FormulaCodeSyntax.formulaCode (old 4 w) (old 4 n) (old 4 a) (old 4 b)) := of_eq (FormulaCodeSyntax.formulaCode_rename w n a b (old 4)) (lift hn)
    have ha1 : Derives Δ (OriginalFormulaHistoryAgreementSyntax.agreement (old 4 w) (old 4 mode) (old 4 depth) (old 4 parameter) (old 4 h) (old 4 R) (old 4 S) (old 4 a) (old 4 b) (old 4 c) (old 4 d) (old 4 n)) := of_eq (OriginalFormulaHistoryAgreementSyntax.agreement_rename w mode depth parameter h R S a b c d n (old 4)) (lift ha)
    have hF : Derives Δ F := .hyp (Or.inl rfl)
    have hSource := Derives.conjL (Derives.conjL hF)
    have ht := OriginalLogicalChildTypes.binary hZ1 kind (old 4 w) (old 4 a) (old 4 b) (old 4 n) (slot 4 0) (slot 4 1) hw1 hn1 hSource
    have hx := SyntaxConstructors.child_member hZ1 2 (SyntaxLogicalSyntax.binaryTag kind) (old 4 w) (SyntaxAtomSyntax.two (slot 4 0) (slot 4 1)) (old 4 n) 0 hw1 hSource
    have hy := SyntaxConstructors.child_member hZ1 2 (SyntaxLogicalSyntax.binaryTag kind) (old 4 w) (SyntaxAtomSyntax.two (slot 4 0) (slot 4 1)) (old 4 n) 1 hw1 hSource
    have he0 := OriginalFormulaHistoryAgreementSyntax.agreement_at (old 4 w) (old 4 mode) (old 4 depth) (old 4 parameter) (old 4 h) (old 4 R) (old 4 S) (old 4 a) (old 4 b) (old 4 c) (old 4 d) (old 4 n) (slot 4 0) (slot 4 2) ha1 hx (.conjL ht)
    have he1 := OriginalFormulaHistoryAgreementSyntax.agreement_at (old 4 w) (old 4 mode) (old 4 depth) (old 4 parameter) (old 4 h) (old 4 R) (old 4 S) (old 4 a) (old 4 b) (old 4 c) (old 4 d) (old 4 n) (slot 4 1) (slot 4 3) ha1 hy (.conjR ht)
    have ho := FormulaTransformLogicalSyntax.intro_binary kind (old 4 w) (old 4 h) (old 4 R) (old 4 S) (old 4 a) (old 4 b) (old 4 c) (old 4 d) (old 4 n) (old 4 q) (slot 4 0) (slot 4 1) (slot 4 2) (slot 4 3) (.conjI hSource (.conjI hx (.conjI hy (.conjI (.conjR (.conjL hF)) (.conjI (.impE (.conjL he0) (.conjL (.conjR hF))) (.impE (.conjL he1) (.conjR (.conjR hF))))))))
    exact of_eq (FormulaTransformLogicalSyntax.binary_rename kind w h R S a b c d n q (old 4)).symm ho
  · apply Derives.impI
    let E := FormulaTransformLogicalSyntax.binary kind w h R S a b c d n q
    let F := FormulaTransformLogicalSyntax.binaryBody kind w h R S a b c d n q
    let Δ := Context.add F (raisedContext 4 (Context.add E Γ))
    apply HornBinderRules.eliminate_many 4 F _ (.hyp (Or.inl rfl))
    have hZ1 := HornBinderRules.zf_body 4 (ZFContext.add hZ E) F
    have lift {p : Formula m} (hp : Derives Γ p) : Derives Δ (p.rename (old 4)) := HornBinderRules.under_body 4 (add hp E) F
    have hw1 : Derives Δ (omega (old 4 w)) := of_eq (omega_rename w (old 4)) (lift hw)
    have hn1 : Derives Δ (FormulaCodeSyntax.formulaCode (old 4 w) (old 4 n) (old 4 a) (old 4 b)) := of_eq (FormulaCodeSyntax.formulaCode_rename w n a b (old 4)) (lift hn)
    have ha1 : Derives Δ (OriginalFormulaHistoryAgreementSyntax.agreement (old 4 w) (old 4 mode) (old 4 depth) (old 4 parameter) (old 4 h) (old 4 R) (old 4 S) (old 4 a) (old 4 b) (old 4 c) (old 4 d) (old 4 n)) := of_eq (OriginalFormulaHistoryAgreementSyntax.agreement_rename w mode depth parameter h R S a b c d n (old 4)) (lift ha)
    have hF : Derives Δ F := .hyp (Or.inl rfl)
    have hSource := Derives.conjL hF
    have ht := OriginalLogicalChildTypes.binary hZ1 kind (old 4 w) (old 4 a) (old 4 b) (old 4 n) (slot 4 0) (slot 4 1) hw1 hn1 hSource
    have hx := Derives.conjL (Derives.conjR hF)
    have hy := Derives.conjL (Derives.conjR (Derives.conjR hF))
    have he0 := OriginalFormulaHistoryAgreementSyntax.agreement_at (old 4 w) (old 4 mode) (old 4 depth) (old 4 parameter) (old 4 h) (old 4 R) (old 4 S) (old 4 a) (old 4 b) (old 4 c) (old 4 d) (old 4 n) (slot 4 0) (slot 4 2) ha1 hx (.conjL ht)
    have he1 := OriginalFormulaHistoryAgreementSyntax.agreement_at (old 4 w) (old 4 mode) (old 4 depth) (old 4 parameter) (old 4 h) (old 4 R) (old 4 S) (old 4 a) (old 4 b) (old 4 c) (old 4 d) (old 4 n) (slot 4 1) (slot 4 3) ha1 hy (.conjR ht)
    have ho := OriginalFormulaCaseSyntax.intro_binary (SyntaxLogicalSyntax.binaryTag kind) 3 (old 4 w) (old 4 mode) (old 4 depth) (old 4 parameter) (old 4 n) (old 4 q) (slot 4 0) (slot 4 1) (slot 4 2) (slot 4 3) (.conjI (.conjI hSource (.conjL (.conjR (.conjR (.conjR hF))))) (.conjI (.impE (.conjR he0) (.conjL (.conjR (.conjR (.conjR (.conjR hF)))))) (.impE (.conjR he1) (.conjR (.conjR (.conjR (.conjR (.conjR hF))))))))
    exact of_eq (OriginalFormulaCaseSyntax.binaryCase_rename (SyntaxLogicalSyntax.binaryTag kind) 3 w mode depth parameter n q (old 4)).symm ho

end PPAC.Migration.Internal.OriginalLogicalCaseBridge
