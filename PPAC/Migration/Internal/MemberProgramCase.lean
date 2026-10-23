import PPAC.Migration.Internal.MemberProgramIntro

/-! 原纯成员应用分支与独立项程序成员输出的全候选双条件；构造前提在具体模式端点消去。 -/
namespace PPAC.Migration.Internal.MemberProgramCase
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem membership_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w mode depth parameter R S c d s x y q : Fin m) (hw : Derives Γ (omega w))
    (hs : Derives Γ (SyntaxAtomSyntax.zeroScalar w s))
    (hInputs : Derives Γ (SyntaxForestSyntax.inputs 2 w (SyntaxAtomSyntax.two x y)))
    (ha : Derives Γ (MemberPairAgreementSyntax.agreement w mode depth parameter R S c d x y)) :
    Derives Γ ((OriginalFormulaMemberCaseSyntax.membershipCase w mode depth parameter x y q).iff
      (MemberProgramSyntax.returned w R S c d s x y q)) := by
  apply Derives.conjI
  · apply Derives.impI
    let E := OriginalFormulaMemberCaseSyntax.membershipCase w mode depth parameter x y q
    let B := OriginalFormulaMemberCaseSyntax.body w mode depth parameter x y q
    let Δ := Context.add B (raisedContext 3 (Context.add E Γ))
    apply HornBinderRules.eliminate_many 3 B _ (.hyp (Or.inl rfl))
    have hZ1 := HornBinderRules.zf_body 3 (ZFContext.add hZ E) B
    have lift {p : Formula m} (h : Derives Γ p) : Derives Δ (p.rename (old 3)) := HornBinderRules.under_body 3 (add h E) B
    have hw1 : Derives Δ (omega (old 3 w)) := of_eq (omega_rename w (old 3)) (lift hw)
    have hs1 : Derives Δ (SyntaxAtomSyntax.zeroScalar (old 3 w) (old 3 s)) := of_eq (SyntaxAtomSyntax.zeroScalar_rename w s (old 3)) (lift hs)
    have ha1 : Derives Δ (MemberPairAgreementSyntax.agreement (old 3 w) (old 3 mode) (old 3 depth) (old 3 parameter) (old 3 R) (old 3 S) (old 3 c) (old 3 d) (old 3 x) (old 3 y)) := of_eq (MemberPairAgreementSyntax.agreement_rename w mode depth parameter R S c d x y (old 3)) (lift ha)
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have he := MemberPairAgreementSyntax.agreement_at _ _ _ _ _ _ _ _ _ _ (slot 3 1) (slot 3 2) ha1 (.conjL (.conjR hB))
    have hp := Derives.impE (.conjL he) (.conjR (.conjR (.conjR hB)))
    have hOut := MemberProgramOutput.from_pair hZ1 (old 3 w) (old 3 R) (old 3 S) (old 3 c) (old 3 d) (old 3 s) (old 3 x) (old 3 y) (old 3 q) (slot 3 0) (slot 3 2) hw1 hs1 (.conjL hB) (.conjL (.conjR (.conjR hB))) hp
    exact of_eq (MemberProgramSyntax.returned_rename w R S c d s x y q (old 3)).symm hOut
  · apply Derives.impI
    let E := MemberProgramSyntax.returned w R S c d s x y q
    let B := MemberProgramSyntax.body w R S c d s x y q
    let Δ := Context.add B (raisedContext 2 (Context.add E Γ))
    apply HornBinderRules.eliminate_many 2 B _ (.hyp (Or.inl rfl))
    have hZ1 := HornBinderRules.zf_body 2 (ZFContext.add hZ E) B
    have lift {p : Formula m} (h : Derives Γ p) : Derives Δ (p.rename (old 2)) := HornBinderRules.under_body 2 (add h E) B
    have hw1 : Derives Δ (omega (old 2 w)) := of_eq (omega_rename w (old 2)) (lift hw)
    have hs1 : Derives Δ (SyntaxAtomSyntax.zeroScalar (old 2 w) (old 2 s)) := of_eq (SyntaxAtomSyntax.zeroScalar_rename w s (old 2)) (lift hs)
    have ha1 : Derives Δ (MemberPairAgreementSyntax.agreement (old 2 w) (old 2 mode) (old 2 depth) (old 2 parameter) (old 2 R) (old 2 S) (old 2 c) (old 2 d) (old 2 x) (old 2 y)) := of_eq (MemberPairAgreementSyntax.agreement_rename w mode depth parameter R S c d x y (old 2)) (lift ha)
    have hi1 : Derives Δ (SyntaxForestSyntax.inputs 2 (old 2 w) (SyntaxAtomSyntax.two (old 2 x) (old 2 y))) := of_eq (by simp only [SyntaxForestSyntax.inputs_rename, SyntaxAtomSyntax.two_map]) (lift hInputs)
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have hOut := MemberProgramIntro.from_output hZ1 (old 2 w) (old 2 mode) (old 2 depth) (old 2 parameter) (old 2 R) (old 2 S) (old 2 c) (old 2 d) (old 2 s) (old 2 x) (old 2 y) (old 2 q) (slot 2 0) (slot 2 1) hw1 hs1 ha1 (.conjL hB) (.conjL (.conjR hB)) (.conjR (.conjR hB)) hi1
    exact of_eq (OriginalFormulaMemberCaseSyntax.membershipCase_rename w mode depth parameter x y q (old 2)).symm hOut

theorem application_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w mode depth parameter R S c d s x y n q : Fin m) (hw : Derives Γ (omega w))
    (hs : Derives Γ (SyntaxAtomSyntax.zeroScalar w s))
    (hn : Derives Γ (SyntaxAtomSyntax.memberCode w s x y n))
    (hInputs : Derives Γ (SyntaxForestSyntax.inputs 2 w (SyntaxAtomSyntax.two x y)))
    (ha : Derives Γ (MemberPairAgreementSyntax.agreement w mode depth parameter R S c d x y)) :
    Derives Γ ((OriginalFormulaCaseSyntax.applicationCase w mode depth parameter n q).iff
      (MemberProgramSyntax.returned w R S c d s x y q)) :=
  SyntaxTypeLocalTransfer.iff_trans (OriginalFormulaMemberCase.case_iff hZ w mode depth parameter s x y n q hw hs hn)
    (membership_iff hZ w mode depth parameter R S c d s x y q hw hs hInputs ha)

end PPAC.Migration.Internal.MemberProgramCase
