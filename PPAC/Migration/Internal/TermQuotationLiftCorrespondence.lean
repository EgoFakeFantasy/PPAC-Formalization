import PPAC.Migration.Internal.TermQuotationLiftEnvironment

/-! 在准确后继长度下，原coded binder与整张提升项像环境双向等价；不残留图或head见证假设。 -/
namespace PPAC.Migration.Internal.TermQuotationLiftCorrespondence
open Source SourceAlgebra SourceLogic OmegaSyntax TermQuotationLiftSyntax
open SyntaxRenameQuerySyntax (of_eq)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem output_subst {m} {Γ : Context m} (w R S a b c d A C K H U V : Fin m)
    (hK : Derives Γ (.equal K U)) (hH : Derives Γ (.equal H V))
    (hl : Derives Γ (SyntaxCodedMixedBinderSyntax.lifted w R S a b c d A C K H)) :
    Derives Γ (SyntaxCodedMixedBinderSyntax.lifted w R S a b c d A C U V) := by
  let P := SyntaxCodedMixedBinderSyntax.lifted w.castSucc R.castSucc S.castSucc a.castSucc b.castSucc c.castSucc d.castSucc A.castSucc C.castSucc (Fin.last m) H.castSucc
  have hi : Derives Γ (P.instantiate K) := of_eq (by simp only [P, Formula.instantiate, SyntaxCodedMixedBinderSyntax.lifted_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hl
  have hmid : Derives Γ (SyntaxCodedMixedBinderSyntax.lifted w R S a b c d A C U H) := of_eq (by simp only [P, Formula.instantiate, SyntaxCodedMixedBinderSyntax.lifted_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (Derives.eqSubst P hK hi)
  let Q := SyntaxCodedMixedBinderSyntax.lifted w.castSucc R.castSucc S.castSucc a.castSucc b.castSucc c.castSucc d.castSucc A.castSucc C.castSucc U.castSucc (Fin.last m)
  have hj : Derives Γ (Q.instantiate H) := of_eq (by simp only [Q, Formula.instantiate, SyntaxCodedMixedBinderSyntax.lifted_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hmid
  exact of_eq (by simp only [Q, Formula.instantiate, SyntaxCodedMixedBinderSyntax.lifted_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (Derives.eqSubst Q hH hj)

theorem of_environment {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) {bound free : PureSyntaxQuotation.Ctx}
    (bs fs : List (PureSyntaxQuotation.Tm bound free)) (w R S a b c d A C K H : Fin m)
    (hw : Derives Γ (omega w))
    (ha : Derives Γ (SyntaxNumeralSyntax.numeral bs.length a))
    (hb : Derives Γ (SyntaxNumeralSyntax.numeral fs.length b))
    (hc : Derives Γ (SyntaxNumeralSyntax.numeral bound.length c))
    (hd : Derives Γ (SyntaxNumeralSyntax.numeral free.length d))
    (he : Derives Γ (TermQuotationEnvironmentSyntax.environment bs fs w a b c d R S))
    (hA : Derives Γ (successor A a))
    (hC : Derives Γ (successor C c))
    (ht : Derives Γ (TermQuotationEnvironmentSyntax.environment (newBound bs) (shifted fs) w A b C d K H)) :
    Derives Γ (SyntaxCodedMixedBinderSyntax.lifted w R S a b c d A C K H) := by
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
  have ht2 : Derives Δ (TermQuotationEnvironmentSyntax.environment (newBound bs) (shifted fs) w.castSucc.castSucc A.castSucc.castSucc b.castSucc.castSucc C.castSucc.castSucc d.castSucc.castSucc K.castSucc.castSucc H.castSucc.castSucc) := of_eq (by simp only [Formula.raise, TermQuotationEnvironmentSyntax.environment_rename]) (SyntaxRenameBinders.under_2 ht B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hnew := TermQuotationLiftEnvironment.at_lifted hZ2 bs fs w.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc A.castSucc.castSucc C.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) hw2 ha2 hb2 hc2 hd2 he2 hB
  have heq := TermQuotationEnvironment.unique hZ2 (newBound bs) (shifted fs) w.castSucc.castSucc A.castSucc.castSucc b.castSucc.castSucc C.castSucc.castSucc d.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) K.castSucc.castSucc H.castSucc.castSucc hw2 hnew ht2
  have ho := output_subst w.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc A.castSucc.castSucc C.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) K.castSucc.castSucc H.castSucc.castSucc (.conjL heq) (.conjR heq) hB
  exact of_eq (by simp only [Formula.raise, SyntaxCodedMixedBinderSyntax.lifted_rename]) ho

theorem lifted_iff_environment {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) {bound free : PureSyntaxQuotation.Ctx}
    (bs fs : List (PureSyntaxQuotation.Tm bound free)) (w R S a b c d A C K H : Fin m)
    (hw : Derives Γ (omega w))
    (ha : Derives Γ (SyntaxNumeralSyntax.numeral bs.length a))
    (hb : Derives Γ (SyntaxNumeralSyntax.numeral fs.length b))
    (hc : Derives Γ (SyntaxNumeralSyntax.numeral bound.length c))
    (hd : Derives Γ (SyntaxNumeralSyntax.numeral free.length d))
    (he : Derives Γ (TermQuotationEnvironmentSyntax.environment bs fs w a b c d R S))
    (hA : Derives Γ (successor A a))
    (hC : Derives Γ (successor C c)) :
    Derives Γ ((SyntaxCodedMixedBinderSyntax.lifted w R S a b c d A C K H).iff
      (TermQuotationEnvironmentSyntax.environment (newBound bs) (shifted fs) w A b C d K H)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact TermQuotationLiftEnvironment.at_lifted (ZFContext.add hZ _) bs fs w R S a b c d A C K H (add hw _) (add ha _) (add hb _) (add hc _) (add hd _) (add he _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact of_environment (ZFContext.add hZ _) bs fs w R S a b c d A C K H (add hw _) (add ha _) (add hb _) (add hc _) (add hd _) (add he _) (add hA _) (add hC _) (.hyp (Or.inl rfl))

theorem actual_environment_fiber {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) {bound free : PureSyntaxQuotation.Ctx}
    (bs fs : List (PureSyntaxQuotation.Tm bound free)) (w a b c d A C : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (SyntaxNumeralSyntax.numeral bs.length a))
    (hb : Derives Γ (SyntaxNumeralSyntax.numeral fs.length b)) (hc : Derives Γ (SyntaxNumeralSyntax.numeral bound.length c))
    (hd : Derives Γ (SyntaxNumeralSyntax.numeral free.length d))
    (hA : Derives Γ (successor A a)) (hC : Derives Γ (successor C c)) :
    Derives Γ (TermQuotationEnvironmentSyntax.fiber (newBound bs) (shifted fs) w A b C d) := by
  have hANum : Derives Γ (SyntaxNumeralSyntax.numeral (newBound bs).length A) := of_eq (by simp only [newBound_length]) (SyntaxNumeralSyntax.intro_succ bs.length A a ha hA)
  have hBNum : Derives Γ (SyntaxNumeralSyntax.numeral (shifted fs).length b) := of_eq (by simp only [shifted_length]) hb
  have hCNum : Derives Γ (SyntaxNumeralSyntax.numeral (YesMetaZFC.SetTheory.SetSort.set :: bound).length C) := SyntaxNumeralSyntax.intro_succ bound.length C c hc hC
  exact TermQuotationEnvironment.actual_fiber hZ (newBound bs) (shifted fs) w A b C d hw hANum hBNum hCNum hd

end PPAC.Migration.Internal.TermQuotationLiftCorrespondence
