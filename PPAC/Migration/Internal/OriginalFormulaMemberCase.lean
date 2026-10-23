import PPAC.Migration.Internal.OriginalFormulaMemberCaseSyntax

/-! 已知纯成员输入上的原applicationCase精确恢复编号0和两个真实参数。 -/
namespace PPAC.Migration.Internal.OriginalFormulaMemberCase
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem case_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w mode depth parameter s x y n q : Fin m) (hw : Derives Γ (omega w))
    (hs : Derives Γ (SyntaxAtomSyntax.zeroScalar w s)) (hn : Derives Γ (SyntaxAtomSyntax.memberCode w s x y n)) :
    Derives Γ ((OriginalFormulaCaseSyntax.applicationCase w mode depth parameter n q).iff
      (OriginalFormulaMemberCaseSyntax.membershipCase w mode depth parameter x y q)) := by
  apply Derives.conjI
  · apply Derives.impI
    let E := OriginalFormulaCaseSyntax.applicationCase w mode depth parameter n q
    let B := OriginalFormulaCaseSyntax.applicationBody w mode depth parameter n q
    let Δ := Context.add B (raisedContext 3 (Context.add E Γ))
    apply HornBinderRules.eliminate_many 3 B _ (.hyp (Or.inl rfl))
    have hZ1 := HornBinderRules.zf_body 3 (ZFContext.add hZ E) B
    have lift {p : Formula m} (h : Derives Γ p) : Derives Δ (p.rename (old 3)) := HornBinderRules.under_body 3 (add h E) B
    have hw1 : Derives Δ (omega (old 3 w)) := of_eq (omega_rename w (old 3)) (lift hw)
    have hs1 : Derives Δ (SyntaxAtomSyntax.zeroScalar (old 3 w) (old 3 s)) := of_eq (SyntaxAtomSyntax.zeroScalar_rename w s (old 3)) (lift hs)
    have hn1 : Derives Δ (SyntaxAtomSyntax.memberCode (old 3 w) (old 3 s) (old 3 x) (old 3 y) (old 3 n)) := of_eq (SyntaxAtomSyntax.memberCode_rename w s x y n (old 3)) (lift hn)
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have hArgs := OriginalArgumentRunNaturality.input_natural hZ1 2 _ _ _ _ _ _ hw1 (.conjR hB)
    have hRecover := OriginalFormulaMemberApplication.recover_at_member hZ1 (old 3 w) (slot 3 0) (old 3 s) (old 3 x) (old 3 y) (slot 3 1) (old 3 n) hw1 hs1 hn1 hArgs (.conjL (.conjL hB))
    have ho := OriginalFormulaMemberCaseSyntax.intro_case (old 3 w) (old 3 mode) (old 3 depth) (old 3 parameter) (old 3 x) (old 3 y) (old 3 q) (slot 3 0) (slot 3 1) (slot 3 2) (.conjL hRecover) (.conjR hRecover) (.conjR (.conjL hB)) (.conjR hB)
    exact of_eq (OriginalFormulaMemberCaseSyntax.membershipCase_rename w mode depth parameter x y q (old 3)).symm ho
  · apply Derives.impI
    let E := OriginalFormulaMemberCaseSyntax.membershipCase w mode depth parameter x y q
    let B := OriginalFormulaMemberCaseSyntax.body w mode depth parameter x y q
    let Δ := Context.add B (raisedContext 3 (Context.add E Γ))
    apply HornBinderRules.eliminate_many 3 B _ (.hyp (Or.inl rfl))
    have hZ1 := HornBinderRules.zf_body 3 (ZFContext.add hZ E) B
    have lift {p : Formula m} (h : Derives Γ p) : Derives Δ (p.rename (old 3)) := HornBinderRules.under_body 3 (add h E) B
    have hw1 : Derives Δ (omega (old 3 w)) := of_eq (omega_rename w (old 3)) (lift hw)
    have hs1 : Derives Δ (SyntaxAtomSyntax.zeroScalar (old 3 w) (old 3 s)) := of_eq (SyntaxAtomSyntax.zeroScalar_rename w s (old 3)) (lift hs)
    have hn1 : Derives Δ (SyntaxAtomSyntax.memberCode (old 3 w) (old 3 s) (old 3 x) (old 3 y) (old 3 n)) := of_eq (SyntaxAtomSyntax.memberCode_rename w s x y n (old 3)) (lift hn)
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have hInput := Derives.impE (.conjR (OriginalFormulaMemberApplication.member_at_forest_iff hZ1 (old 3 w) (slot 3 0) (old 3 s) (old 3 x) (old 3 y) (slot 3 1) (old 3 n) hw1 (.conjL hB) hs1 (.conjL (.conjR hB)))) hn1
    have hData := Derives.conjI (Derives.conjI hInput (.conjL (.conjR (.conjR hB)))) (.conjR (.conjR (.conjR hB)))
    have ho := OriginalFormulaCaseSyntax.intro_application (old 3 w) (old 3 mode) (old 3 depth) (old 3 parameter) (old 3 n) (old 3 q) (slot 3 0) (slot 3 1) (slot 3 2) hData
    exact of_eq (OriginalFormulaCaseSyntax.applicationCase_rename w mode depth parameter n q (old 3)).symm ho

end PPAC.Migration.Internal.OriginalFormulaMemberCase
