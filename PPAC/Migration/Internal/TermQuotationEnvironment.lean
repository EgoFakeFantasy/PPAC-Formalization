import PPAC.Migration.Internal.TermQuotationEnvironmentSyntax

/-! 两张原项像quotation码在对象量词内实际存在，构成合法混合环境并具有实际唯一码对。 -/
namespace PPAC.Migration.Internal.TermQuotationEnvironment
open Source SourceAlgebra SourceLogic OmegaSyntax TermQuotationEnvironmentSyntax
open SyntaxRenameQuerySyntax (of_eq)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem exists_environment {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) {bound free : PureSyntaxQuotation.Ctx}
    (bs fs : List (PureSyntaxQuotation.Tm bound free)) (w a b c d : Fin m) (hw : Derives Γ (omega w))
    (ha : Derives Γ (SyntaxNumeralSyntax.numeral bs.length a)) (hb : Derives Γ (SyntaxNumeralSyntax.numeral fs.length b))
    (hc : Derives Γ (SyntaxNumeralSyntax.numeral bound.length c)) (hd : Derives Γ (SyntaxNumeralSyntax.numeral free.length d)) :
    Derives Γ (existsEnvironment bs fs w a b c d) := by
  have he1 := TermImageQuotationFields.exists_images hZ bs w hw
  let P := (Formula.mem (Fin.last m) w.castSucc).conj (TermImageQuotationSyntax.images bs w.castSucc (Fin.last m))
  let Δ := Context.add P (Context.image Formula.raise Γ)
  apply Derives.exE (p := P) he1
  have hZ1 := ZFContext.under hZ P
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw P)
  have ha1 : Derives Δ (SyntaxNumeralSyntax.numeral bs.length a.castSucc) := of_eq (SyntaxNumeralSyntax.numeral_rename _ a Fin.castSucc) (under ha P)
  have hb1 : Derives Δ (SyntaxNumeralSyntax.numeral fs.length b.castSucc) := of_eq (SyntaxNumeralSyntax.numeral_rename _ b Fin.castSucc) (under hb P)
  have hc1 : Derives Δ (SyntaxNumeralSyntax.numeral bound.length c.castSucc) := of_eq (SyntaxNumeralSyntax.numeral_rename _ c Fin.castSucc) (under hc P)
  have hd1 : Derives Δ (SyntaxNumeralSyntax.numeral free.length d.castSucc) := of_eq (SyntaxNumeralSyntax.numeral_rename _ d Fin.castSucc) (under hd P)
  have hP : Derives Δ P := .hyp (Or.inl rfl)
  have he2 := TermImageQuotationFields.exists_images hZ1 fs w.castSucc hw1
  let Q := (Formula.mem (Fin.last (m+1)) w.castSucc.castSucc).conj (TermImageQuotationSyntax.images fs w.castSucc.castSucc (Fin.last (m+1)))
  let Ξ := Context.add Q (Context.image Formula.raise Δ)
  apply Derives.exE (p := Q) he2
  have hZ2 := ZFContext.under hZ1 Q
  have hw2 : Derives Ξ (omega w.castSucc.castSucc) := of_eq (omega_rename w.castSucc Fin.castSucc) (under hw1 Q)
  have ha2 : Derives Ξ (SyntaxNumeralSyntax.numeral bs.length a.castSucc.castSucc) := of_eq (SyntaxNumeralSyntax.numeral_rename _ a.castSucc Fin.castSucc) (under ha1 Q)
  have hb2 : Derives Ξ (SyntaxNumeralSyntax.numeral fs.length b.castSucc.castSucc) := of_eq (SyntaxNumeralSyntax.numeral_rename _ b.castSucc Fin.castSucc) (under hb1 Q)
  have hc2 : Derives Ξ (SyntaxNumeralSyntax.numeral bound.length c.castSucc.castSucc) := of_eq (SyntaxNumeralSyntax.numeral_rename _ c.castSucc Fin.castSucc) (under hc1 Q)
  have hd2 : Derives Ξ (SyntaxNumeralSyntax.numeral free.length d.castSucc.castSucc) := of_eq (SyntaxNumeralSyntax.numeral_rename _ d.castSucc Fin.castSucc) (under hd1 Q)
  have hP2 : Derives Ξ ((Formula.mem (Fin.last m).castSucc w.castSucc.castSucc).conj (TermImageQuotationSyntax.images bs w.castSucc.castSucc (Fin.last m).castSucc)) := of_eq (by simp only [P, Formula.raise, Formula.rename, TermImageQuotationSyntax.images_rename]) (under hP Q)
  have hQ : Derives Ξ Q := .hyp (Or.inl rfl)
  have hR := TermImageQuotationTyping.term_list hZ2 bs w.castSucc.castSucc a.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc (Fin.last m).castSucc hw2 ha2 hc2 hd2 (.conjR hP2)
  have hS := TermImageQuotationTyping.term_list hZ2 fs w.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc (Fin.last (m+1)) hw2 hb2 hc2 hd2 (.conjR hQ)
  have hE : Derives Ξ (environment bs fs w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))) := .conjI (.conjI (.conjR hP2) (.conjR hQ)) (.conjI hR hS)
  have ho := intro_exists bs fs w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) hE
  exact of_eq (by simp only [Formula.raise, existsEnvironment_rename]) ho

theorem unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) {bound free : PureSyntaxQuotation.Ctx}
    (bs fs : List (PureSyntaxQuotation.Tm bound free)) (w a b c d R S U V : Fin m) (hw : Derives Γ (omega w))
    (he : Derives Γ (environment bs fs w a b c d R S)) (hf : Derives Γ (environment bs fs w a b c d U V)) :
    Derives Γ ((Formula.equal R U).conj (.equal S V)) :=
  .conjI (TermImageQuotationFields.unique hZ bs w R U hw (.conjL (.conjL he)) (.conjL (.conjL hf)))
    (TermImageQuotationFields.unique hZ fs w S V hw (.conjR (.conjL he)) (.conjR (.conjL hf)))

theorem unique_output {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) {bound free : PureSyntaxQuotation.Ctx}
    (bs fs : List (PureSyntaxQuotation.Tm bound free)) (w a b c d R S : Fin m) (hw : Derives Γ (omega w))
    (he : Derives Γ (environment bs fs w a b c d R S)) : Derives Γ (uniqueEnvironment bs fs w a b c d R S) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  let B := body bs fs w a b c d
  let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise Γ))
  have hZ2 := SyntaxRenameBinders.zf_under_2 hZ B
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxRenameBinders.under_2 hw B)
  have he2 : Derives Δ (environment bs fs w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc) := of_eq (by simp only [Formula.raise, environment_rename]) (SyntaxRenameBinders.under_2 he B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  exact unique hZ2 bs fs w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) R.castSucc.castSucc S.castSucc.castSucc hw2 hB he2

theorem actual_fiber {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) {bound free : PureSyntaxQuotation.Ctx}
    (bs fs : List (PureSyntaxQuotation.Tm bound free)) (w a b c d : Fin m) (hw : Derives Γ (omega w))
    (ha : Derives Γ (SyntaxNumeralSyntax.numeral bs.length a)) (hb : Derives Γ (SyntaxNumeralSyntax.numeral fs.length b))
    (hc : Derives Γ (SyntaxNumeralSyntax.numeral bound.length c)) (hd : Derives Γ (SyntaxNumeralSyntax.numeral free.length d)) :
    Derives Γ (fiber bs fs w a b c d) := by
  have he := exists_environment hZ bs fs w a b c d hw ha hb hc hd
  let B := body bs fs w a b c d
  let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply SyntaxRenameBinders.eliminate_2 B _ he
  have hZ2 := SyntaxRenameBinders.zf_under_2 hZ B
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxRenameBinders.under_2 hw B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hu := unique_output hZ2 bs fs w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) hw2 hB
  have ho := intro_fiber bs fs w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) hB hu
  exact of_eq (by simp only [Formula.raise, fiber_rename]) ho

end PPAC.Migration.Internal.TermQuotationEnvironment
