import PPAC.Migration.Internal.PureQuotationTypedSyntax

/-! 所有纯项quotation模式在其精确内部上下文中实际取得带Term类型的唯一值。 -/
namespace PPAC.Migration.Internal.PureQuotationTypedTerms
open Source SourceAlgebra SourceLogic OmegaSyntax PureQuotationTypedSyntax
open SyntaxRenameQuerySyntax (of_eq)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem exists_typed {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    {bound free : PureSyntaxQuotation.Ctx} {sort : YesMetaZFC.SetTheory.SetSort}
    (input : PureSyntaxQuotation.Tm bound free sort) (w b f : Fin m)
    (hw : Derives Γ (omega w)) (hb : Derives Γ (SyntaxNumeralSyntax.numeral bound.length b)) (hf : Derives Γ (SyntaxNumeralSyntax.numeral free.length f)) :
    Derives Γ (termExists input w b f) := by
  have he := OriginalTreeQuotationExistence.tree_exists hZ (PureSyntaxQuotation.termTree input) w hw
  let P := (Formula.mem (Fin.last m) w.castSucc).conj (PureQuotationSyntax.term input w.castSucc (Fin.last m))
  let Δ := Context.add P (Context.image Formula.raise Γ)
  apply Derives.exE (p := P) he
  have hZ1 := ZFContext.under hZ P
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw P)
  have hb1 : Derives Δ (SyntaxNumeralSyntax.numeral bound.length b.castSucc) := of_eq (SyntaxNumeralSyntax.numeral_rename _ b Fin.castSucc) (under hb P)
  have hf1 : Derives Δ (SyntaxNumeralSyntax.numeral free.length f.castSucc) := of_eq (SyntaxNumeralSyntax.numeral_rename _ f Fin.castSucc) (under hf P)
  have hP : Derives Δ P := .hyp (Or.inl rfl)
  have ht := PureQuotationTermTyping.term_type hZ1 input w.castSucc b.castSucc f.castSucc (Fin.last m) hw1 hb1 hf1 (.conjR hP)
  have ho := intro_term_exists input w.castSucc b.castSucc f.castSucc (Fin.last m) (.conjI (.conjR hP) ht)
  exact of_eq (termExists_rename input w b f Fin.castSucc).symm ho

theorem unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    {bound free : PureSyntaxQuotation.Ctx} {sort : YesMetaZFC.SetTheory.SetSort}
    (input : PureSyntaxQuotation.Tm bound free sort) (w b f n v : Fin m) (hw : Derives Γ (omega w))
    (hn : Derives Γ (termValue input w b f n)) (hv : Derives Γ (termValue input w b f v)) : Derives Γ (.equal n v) :=
  PureQuotationSyntax.term_unique hZ input w n v hw (.conjL hn) (.conjL hv)

theorem unique_output {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    {bound free : PureSyntaxQuotation.Ctx} {sort : YesMetaZFC.SetTheory.SetSort}
    (input : PureSyntaxQuotation.Tm bound free sort) (w b f n : Fin m) (hw : Derives Γ (omega w))
    (hn : Derives Γ (termValue input w b f n)) : Derives Γ (termUnique input w b f n) := by
  apply Derives.allI
  apply Derives.impI
  let V := termValue input w.castSucc b.castSucc f.castSucc (Fin.last m)
  let Δ := Context.add V (Context.image Formula.raise Γ)
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw V)
  have hn1 : Derives Δ (termValue input w.castSucc b.castSucc f.castSucc n.castSucc) := of_eq (termValue_rename input w b f n Fin.castSucc) (under hn V)
  exact unique (ZFContext.under hZ V) input w.castSucc b.castSucc f.castSucc (Fin.last m) n.castSucc hw1 (.hyp (Or.inl rfl)) hn1

theorem actual_fiber {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    {bound free : PureSyntaxQuotation.Ctx} {sort : YesMetaZFC.SetTheory.SetSort}
    (input : PureSyntaxQuotation.Tm bound free sort) (w b f : Fin m)
    (hw : Derives Γ (omega w)) (hb : Derives Γ (SyntaxNumeralSyntax.numeral bound.length b)) (hf : Derives Γ (SyntaxNumeralSyntax.numeral free.length f)) :
    Derives Γ (termFiber input w b f) := by
  have he := exists_typed hZ input w b f hw hb hf
  let V := termValue input w.castSucc b.castSucc f.castSucc (Fin.last m)
  let Δ := Context.add V (Context.image Formula.raise Γ)
  apply Derives.exE (p := V) he
  have hV : Derives Δ V := .hyp (Or.inl rfl)
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw V)
  have hu := unique_output (ZFContext.under hZ V) input w.castSucc b.castSucc f.castSucc (Fin.last m) hw1 hV
  have ho := intro_term_fiber input w.castSucc b.castSucc f.castSucc (Fin.last m) hV hu
  exact of_eq (termFiber_rename input w b f Fin.castSucc).symm ho

end PPAC.Migration.Internal.PureQuotationTypedTerms
