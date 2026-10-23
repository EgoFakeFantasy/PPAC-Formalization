import PPAC.Migration.Internal.TermQuotationEnvironment

/-! 已实际构造的原项像quotation环境精确计算混合项替换，不假定未来字段对应。 -/
namespace PPAC.Migration.Internal.TermQuotationSubstitution
open Source SourceAlgebra SourceLogic OmegaSyntax TermQuotationEnvironmentSyntax
open SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket (Tree leaf)
attribute [local irreducible] NaturalRecursionSyntax.matrix

def selected {bound free : PureSyntaxQuotation.Ctx} (isBound : Bool) (bs fs : List (PureSyntaxQuotation.Tm bound free)) : List (PureSyntaxQuotation.Tm bound free) :=
  if isBound then bs else fs

theorem selected_images {m} {Γ : Context m} {bound free : PureSyntaxQuotation.Ctx} (isBound : Bool)
    (bs fs : List (PureSyntaxQuotation.Tm bound free)) (w a b c d R S : Fin m)
    (he : Derives Γ (environment bs fs w a b c d R S)) :
    Derives Γ (TermImageQuotationSyntax.images (selected isBound bs fs) w (SyntaxIndexMapSyntax.selectMap isBound R S)) := by
  cases isBound
  · exact .conjR (.conjL he)
  · exact .conjL (.conjL he)

theorem at_index {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) {bound free : PureSyntaxQuotation.Ctx} (isBound : Bool)
    (bs fs : List (PureSyntaxQuotation.Tm bound free)) (j : Fin (selected isBound bs fs).length) (w a b c d R S n i q : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (SyntaxNumeralSyntax.numeral bs.length a)) (hb : Derives Γ (SyntaxNumeralSyntax.numeral fs.length b))
    (he : Derives Γ (environment bs fs w a b c d R S)) (hi : Derives Γ (SyntaxNumeralSyntax.numeral j.val i))
    (hn : Derives Γ (OriginalTreeQuotationSyntax.tree (.node (SyntaxVariableSyntax.tag isBound) [leaf j.val]) w n)) :
    Derives Γ ((SyntaxCodedMixedTermSyntax.substituted w R S a b c d n q).iff (PureQuotationSyntax.term ((selected isBound bs fs).get j) w q)) := by
  have hc := OriginalQuotationVariableFields.variable_of_tree hZ isBound j.val w i n hw hi hn
  have hm := SyntaxCodedMixedTermFields.at_field hZ isBound w R S a b c d n q i hw (.conjR he) hc
  have hL := selected_images isBound bs fs w a b c d R S he
  have hf := TermImageQuotationFields.field_at hZ (selected isBound bs fs) w (SyntaxIndexMapSyntax.selectMap isBound R S) j i q hw hL hi
  have hl : Derives Γ (SyntaxNumeralSyntax.numeral (selected isBound bs fs).length (SyntaxTermSyntax.limit isBound a b)) := by
    cases isBound
    · exact hb
    · exact ha
  have hd := SyntaxNumeralMembers.index_member hZ (selected isBound bs fs).length j (SyntaxTermSyntax.limit isBound a b) i hl hi
  apply Derives.conjI
  · apply Derives.impI
    have hQ := Derives.impE (add (.conjL hm) _) (.hyp (Or.inl rfl))
    exact Derives.impE (add (.conjL hf) _) (.conjR hQ)
  · apply Derives.impI
    have hQ := Derives.impE (add (.conjR hf) _) (.hyp (Or.inl rfl))
    exact Derives.impE (add (.conjR hm) _) (.conjI (add hd _) hQ)

theorem term_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) {bound free : PureSyntaxQuotation.Ctx} (isBound : Bool)
    (bs fs : List (PureSyntaxQuotation.Tm bound free)) (j : Fin (selected isBound bs fs).length) (w a b c d R S n q : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (SyntaxNumeralSyntax.numeral bs.length a)) (hb : Derives Γ (SyntaxNumeralSyntax.numeral fs.length b))
    (he : Derives Γ (environment bs fs w a b c d R S))
    (hn : Derives Γ (OriginalTreeQuotationSyntax.tree (.node (SyntaxVariableSyntax.tag isBound) [leaf j.val]) w n)) :
    Derives Γ ((SyntaxCodedMixedTermSyntax.substituted w R S a b c d n q).iff (PureQuotationSyntax.term ((selected isBound bs fs).get j) w q)) := by
  have hi := SyntaxNumerals.exists_numeral hZ j.val w hw
  let I := (Formula.mem (Fin.last m) w.castSucc).conj (SyntaxNumeralSyntax.numeral j.val (Fin.last m))
  let Δ := Context.add I (Context.image Formula.raise Γ)
  apply Derives.exE (p := I) hi
  have hZ1 := ZFContext.under hZ I
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw I)
  have ha1 : Derives Δ (SyntaxNumeralSyntax.numeral bs.length a.castSucc) := of_eq (SyntaxNumeralSyntax.numeral_rename _ a Fin.castSucc) (under ha I)
  have hb1 : Derives Δ (SyntaxNumeralSyntax.numeral fs.length b.castSucc) := of_eq (SyntaxNumeralSyntax.numeral_rename _ b Fin.castSucc) (under hb I)
  have he1 : Derives Δ (environment bs fs w.castSucc a.castSucc b.castSucc c.castSucc d.castSucc R.castSucc S.castSucc) := of_eq (environment_rename bs fs w a b c d R S Fin.castSucc) (under he I)
  have hn1 : Derives Δ (OriginalTreeQuotationSyntax.tree (.node (SyntaxVariableSyntax.tag isBound) [leaf j.val]) w.castSucc n.castSucc) := of_eq (OriginalTreeQuotationSyntax.tree_rename _ w n Fin.castSucc) (under hn I)
  have hI : Derives Δ I := .hyp (Or.inl rfl)
  have ho := at_index hZ1 isBound bs fs j w.castSucc a.castSucc b.castSucc c.castSucc d.castSucc R.castSucc S.castSucc n.castSucc (Fin.last m) q.castSucc hw1 ha1 hb1 he1 (.conjR hI) hn1
  exact of_eq (by simp only [Formula.raise, Formula.iff, Formula.rename, SyntaxCodedMixedTermSyntax.substituted_rename, PureQuotationSyntax.term_rename]) ho

end PPAC.Migration.Internal.TermQuotationSubstitution
