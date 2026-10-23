import PPAC.Migration.Internal.OriginalQuotationVariableFields

/-! 纯项quotation在真实内部长度上下文中具有原Term类型；长度numeral只是外部语法模式索引。 -/
namespace PPAC.Migration.Internal.PureQuotationTermTyping
open Source SourceAlgebra SourceLogic OmegaSyntax OriginalTreeQuotationSyntax
open SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket (Tree leaf)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem contexts_of_lengths {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (bLen fLen : Nat) (w b f : Fin m)
    (hw : Derives Γ (omega w)) (hb : Derives Γ (SyntaxNumeralSyntax.numeral bLen b)) (hf : Derives Γ (SyntaxNumeralSyntax.numeral fLen f)) :
    Derives Γ (SyntaxTermSyntax.contexts w b f) :=
  .conjI (SyntaxNumerals.range hZ bLen w b hw hb) (SyntaxNumerals.range hZ fLen w f hw hf)

theorem variable_type {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (bound : Bool) (k bLen fLen : Nat)
    (hlt : k < (if bound then bLen else fLen)) (w b f n : Fin m)
    (hw : Derives Γ (omega w)) (hb : Derives Γ (SyntaxNumeralSyntax.numeral bLen b)) (hf : Derives Γ (SyntaxNumeralSyntax.numeral fLen f))
    (hn : Derives Γ (tree (.node (SyntaxVariableSyntax.tag bound) [leaf k]) w n)) :
    Derives Γ (SyntaxTermSyntax.term w b f n) := by
  have hctx := contexts_of_lengths hZ bLen fLen w b f hw hb hf
  have he := SyntaxNumerals.exists_numeral hZ k w hw
  let I := (Formula.mem (Fin.last m) w.castSucc).conj (SyntaxNumeralSyntax.numeral k (Fin.last m))
  let Δ := Context.add I (Context.image Formula.raise Γ)
  apply Derives.exE (p := I) he
  have hZ1 := ZFContext.under hZ I
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw I)
  have hn1 : Derives Δ (tree (.node (SyntaxVariableSyntax.tag bound) [leaf k]) w.castSucc n.castSucc) := of_eq (tree_rename _ w n Fin.castSucc) (under hn I)
  have hb1 : Derives Δ (SyntaxNumeralSyntax.numeral bLen b.castSucc) := of_eq (SyntaxNumeralSyntax.numeral_rename bLen b Fin.castSucc) (under hb I)
  have hf1 : Derives Δ (SyntaxNumeralSyntax.numeral fLen f.castSucc) := of_eq (SyntaxNumeralSyntax.numeral_rename fLen f Fin.castSucc) (under hf I)
  have hctx1 : Derives Δ (SyntaxTermSyntax.contexts w.castSucc b.castSucc f.castSucc) := of_eq (SyntaxTermSyntax.contexts_rename w b f Fin.castSucc) (under hctx I)
  have hI : Derives Δ I := .hyp (Or.inl rfl)
  have hc := OriginalQuotationVariableFields.variable_of_tree hZ1 bound k w.castSucc (Fin.last m) n.castSucc hw1 (.conjR hI) hn1
  have hl : Derives Δ (SyntaxNumeralSyntax.numeral (if bound then bLen else fLen) (SyntaxTermSyntax.limit bound b.castSucc f.castSucc)) := by
    cases bound
    · exact hf1
    · exact hb1
  have hi := SyntaxNumerals.less hZ1 k (if bound then bLen else fLen) hlt (Fin.last m) (SyntaxTermSyntax.limit bound b.castSucc f.castSucc) (.conjR hI) hl
  have ho := SyntaxTermSyntax.intro_term bound w.castSucc b.castSucc f.castSucc n.castSucc (Fin.last m) (.conjI hctx1 hi) hc
  exact of_eq (by simp only [Formula.raise, SyntaxTermSyntax.term_rename]) ho

theorem term_type {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    {bound free : PureSyntaxQuotation.Ctx} {sort : YesMetaZFC.SetTheory.SetSort}
    (input : PureSyntaxQuotation.Tm bound free sort) (w b f n : Fin m)
    (hw : Derives Γ (omega w)) (hb : Derives Γ (SyntaxNumeralSyntax.numeral bound.length b)) (hf : Derives Γ (SyntaxNumeralSyntax.numeral free.length f))
    (hn : Derives Γ (PureQuotationSyntax.term input w n)) : Derives Γ (SyntaxTermSyntax.term w b f n) := by
  exact match input with
  | .bvar entry => variable_type hZ true entry.index bound.length free.length entry.index_lt_length w b f n hw hb hf hn
  | .fvar entry => variable_type hZ false entry.index bound.length free.length entry.index_lt_length w b f n hw hb hf hn
  | .app symbol _ => nomatch symbol

end PPAC.Migration.Internal.PureQuotationTermTyping
