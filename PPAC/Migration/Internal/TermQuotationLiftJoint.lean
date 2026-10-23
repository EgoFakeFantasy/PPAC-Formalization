import PPAC.Migration.Internal.TermQuotationLiftJointSyntax

/-! 原binder、整表quotation与完整候选唯一性在同一对象存在见证下同时成立。 -/
namespace PPAC.Migration.Internal.TermQuotationLiftJoint
open Source SourceAlgebra SourceLogic OmegaSyntax TermQuotationLiftJointSyntax
open SyntaxRenameQuerySyntax (of_eq)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem actual_fiber {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) {bound free : PureSyntaxQuotation.Ctx}
    (bs fs : List (PureSyntaxQuotation.Tm bound free)) (w R S a b c d A C : Fin m)
    (hw : Derives Γ (omega w))
    (ha : Derives Γ (SyntaxNumeralSyntax.numeral bs.length a))
    (hb : Derives Γ (SyntaxNumeralSyntax.numeral fs.length b))
    (hc : Derives Γ (SyntaxNumeralSyntax.numeral bound.length c))
    (hd : Derives Γ (SyntaxNumeralSyntax.numeral free.length d))
    (he : Derives Γ (TermQuotationEnvironmentSyntax.environment bs fs w a b c d R S))
    (hA : Derives Γ (successor A a)) (hC : Derives Γ (successor C c)) :
    Derives Γ (fiber bs fs w R S a b c d A C) := by
  have hex := SyntaxCodedMixedBinderExistence.exists_pair hZ w R S a b c d A C hw (.conjI (.conjR he) (.conjI hA hC))
  let B := SyntaxCodedMixedBinderSyntax.lifted w.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc A.castSucc.castSucc C.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
  let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply SyntaxRenameBinders.eliminate_2 B _ hex
  have hZ2 := SyntaxRenameBinders.zf_under_2 hZ B
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxRenameBinders.under_2 hw B)
  have ha2 : Derives Δ (SyntaxNumeralSyntax.numeral bs.length a.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxNumeralSyntax.numeral_rename]) (SyntaxRenameBinders.under_2 ha B)
  have hb2 : Derives Δ (SyntaxNumeralSyntax.numeral fs.length b.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxNumeralSyntax.numeral_rename]) (SyntaxRenameBinders.under_2 hb B)
  have hc2 : Derives Δ (SyntaxNumeralSyntax.numeral bound.length c.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxNumeralSyntax.numeral_rename]) (SyntaxRenameBinders.under_2 hc B)
  have hd2 : Derives Δ (SyntaxNumeralSyntax.numeral free.length d.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxNumeralSyntax.numeral_rename]) (SyntaxRenameBinders.under_2 hd B)
  have he2 : Derives Δ (TermQuotationEnvironmentSyntax.environment bs fs w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc) := of_eq (by simp only [Formula.raise, TermQuotationEnvironmentSyntax.environment_rename]) (SyntaxRenameBinders.under_2 he B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hnew := TermQuotationLiftEnvironment.at_lifted hZ2 bs fs w.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc A.castSucc.castSucc C.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) hw2 ha2 hb2 hc2 hd2 he2 hB
  have hu := SyntaxCodedMixedBinderFiber.unique_pair hZ2 w.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc A.castSucc.castSucc C.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) hw2 hB
  have ho := intro_fiber bs fs w.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc A.castSucc.castSucc C.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) (.conjI hB hnew) hu
  exact of_eq (by simp only [Formula.raise, fiber_rename]) ho

end PPAC.Migration.Internal.TermQuotationLiftJoint
