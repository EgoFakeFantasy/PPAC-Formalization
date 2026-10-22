import PPAC.Migration.Internal.SyntaxRenameSelectedIff

/-! 规范子判断恢复源 FormulaCode 与 Input；精确构造律无需隐藏合法源输入前提。 -/
namespace PPAC.Migration.Internal.SyntaxRenameKnownSource
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxRenameQuerySyntax SyntaxRenameKnownFieldsSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem source_contexts {m} {Γ : Context m} (w R S r s a b c d : Fin m)
    (hr : Derives Γ (SyntaxMapCodeSyntax.encoded w r a c R)) (hs : Derives Γ (SyntaxMapCodeSyntax.encoded w s b d S)) :
    Derives Γ (SyntaxTermSyntax.contexts w a b) := by
  have hR := SyntaxMapCodeDecode.contexts w a c R (SyntaxMapCodeSyntax.intro_code w r a c R hr)
  have hS := SyntaxMapCodeDecode.contexts w b d S (SyntaxMapCodeSyntax.intro_code w s b d S hs)
  exact .conjI (.conjL hR) (.conjL hS)

theorem input_of_code {m} {Γ : Context m} (w R S r s a b c d n : Fin m)
    (hr : Derives Γ (SyntaxMapCodeSyntax.encoded w r a c R)) (hs : Derives Γ (SyntaxMapCodeSyntax.encoded w s b d S))
    (hc : Derives Γ (FormulaCodeSyntax.formulaCode w n a b)) : Derives Γ (SyntaxRenameOutputSyntax.input w R S a b c d n) :=
  .conjI hc (.conjI (SyntaxMapCodeSyntax.intro_code w r a c R hr) (SyntaxMapCodeSyntax.intro_code w s b d S hs))

theorem check_source_type {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (advance : Bool) (w x r s a b c d q : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (SyntaxRenameRecursiveSyntax.check advance w x r s a b c d q)) :
    Derives Γ (FormulaCodeRecursiveSyntax.stepCheck advance w x a b) := by
  cases advance
  · exact SyntaxRenameRecursive.source_type hZ w r s a b c d x q hw hc
  · change Derives Γ (FormulaCodeRecursiveSyntax.advancedCode w x a b)
    let B := SyntaxRenameRecursiveSyntax.advancedBody w x r s a b c d q
    let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise Γ)))
    apply SyntaxRenameAdvancedKnown.eliminate_advanced w x r s a b c d q _ hc
    have hZ3 := SyntaxAtomLogic.zf_under_three hZ B
    have hw3 : Derives Δ (omega w.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxAtomLogic.under_three hw B)
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have hs := SyntaxMapLiftParameters.successors _ _ _ _ _ _ _ (.conjL hB)
    have ht := SyntaxRenameRecursive.source_type hZ3 _ _ _ _ _ _ _ _ _ hw3 (.conjR hB)
    have ho := FormulaCodeRecursiveSyntax.intro_advanced w.castSucc.castSucc.castSucc x.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc (.conjL hs) ht
    exact of_eq (by simp only [Formula.raise, FormulaCodeRecursiveSyntax.advancedCode_rename]) ho

theorem equality_input {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w R S r s a b c d n x y X Y : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (SyntaxMapCodeSyntax.encoded w r a c R)) (hs : Derives Γ (SyntaxMapCodeSyntax.encoded w s b d S))
    (hc : Derives Γ (SyntaxAtomSyntax.equalCode w x y n)) (hp : Derives Γ (equalOperands w r s a b c d x y X Y)) :
    Derives Γ (SyntaxRenameOutputSyntax.input w R S a b c d n) := by
  have hx := SyntaxRenameTermTyping.source_term w r s a b c d x X (.conjL hp)
  have hy := SyntaxRenameTermTyping.source_term w r s a b c d y Y (.conjR hp)
  have ht := Derives.impE (.conjR (FormulaCodeKnownAtomic.equal_iff hZ w a b x y n hw hc)) (.conjI hx hy)
  exact input_of_code w R S r s a b c d n hr hs ht

theorem membership_input {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w R S r s a b c d n z Z x y X Y : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (SyntaxMapCodeSyntax.encoded w r a c R)) (hs : Derives Γ (SyntaxMapCodeSyntax.encoded w s b d S))
    (hc : Derives Γ (SyntaxAtomSyntax.memberCode w z x y n)) (hp : Derives Γ (memberOperands w r s a b c d z Z x y X Y)) :
    Derives Γ (SyntaxRenameOutputSyntax.input w R S a b c d n) := by
  have hx := SyntaxRenameTermTyping.source_term w r s a b c d x X (.conjL (.conjR (.conjR hp)))
  have hy := SyntaxRenameTermTyping.source_term w r s a b c d y Y (.conjR (.conjR (.conjR hp)))
  have ht := Derives.impE (.conjR (FormulaCodeKnownAtomic.member_iff hZ w a b z x y n hw hc)) (.conjI (.conjL hp) (.conjI hx hy))
  exact input_of_code w R S r s a b c d n hr hs ht

theorem single_input {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (tag : Nat) (advance : Bool)
    (valid : (tag = 4 ∧ advance = false) ∨ (tag = 9 ∧ advance = true) ∨ (tag = 10 ∧ advance = true))
    (w R S r s a b c d n x X : Fin m) (hw : Derives Γ (omega w))
    (hr : Derives Γ (SyntaxMapCodeSyntax.encoded w r a c R)) (hs : Derives Γ (SyntaxMapCodeSyntax.encoded w s b d S))
    (hc : Derives Γ (SyntaxLogicalSyntax.singleCode tag w x n))
    (hp : Derives Γ (SyntaxRenameRecursiveSyntax.check advance w x R S a b c d X)) : Derives Γ (SyntaxRenameOutputSyntax.input w R S a b c d n) := by
  have hx := check_source_type hZ advance w x R S a b c d X hw hp
  have ht := Derives.impE (.conjR (SyntaxRenameLogicalConstruct.single_types hZ tag advance valid w a b x n hw hc)) (.conjI (source_contexts w R S r s a b c d hr hs) hx)
  exact input_of_code w R S r s a b c d n hr hs ht

theorem binary_input {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Fin 4)
    (w R S r s a b c d n x y X Y : Fin m) (hw : Derives Γ (omega w))
    (hr : Derives Γ (SyntaxMapCodeSyntax.encoded w r a c R)) (hs : Derives Γ (SyntaxMapCodeSyntax.encoded w s b d S))
    (hc : Derives Γ (SyntaxLogicalSyntax.binaryCode kind w x y n))
    (hp : Derives Γ ((SyntaxRenameJudgmentSyntax.renamed w R S a b c d x X).conj (SyntaxRenameJudgmentSyntax.renamed w R S a b c d y Y))) : Derives Γ (SyntaxRenameOutputSyntax.input w R S a b c d n) := by
  have hx := SyntaxRenameRecursive.source_type hZ w R S a b c d x X hw (.conjL hp)
  have hy := SyntaxRenameRecursive.source_type hZ w R S a b c d y Y hw (.conjR hp)
  have ht := Derives.impE (.conjR (SyntaxRenameLogicalConstruct.binary_types hZ kind w a b x y n hw hc)) (.conjI (source_contexts w R S r s a b c d hr hs) (.conjI hx hy))
  exact input_of_code w R S r s a b c d n hr hs ht
end PPAC.Migration.Internal.SyntaxRenameKnownSource
