import PPAC.Migration.Internal.ObjectActualFormulaHistory
import PPAC.Migration.Internal.FreeSubstProgramBinder

/-! 实际自由变量项像转换的列表必满足自由变量替换码合同，不额外限制原转换结果。 -/
namespace PPAC.Migration.Internal.OriginalFreeImageConversion
open Source SourceAlgebra SourceLogic OmegaSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem list_subst {m} {Γ : Context m} (w b c L S J : Fin m)
    (he : Derives Γ (.equal L S)) (hc : Derives Γ (SyntaxFreeSubstSyntax.codeConversion w b c L J)) :
    Derives Γ (SyntaxFreeSubstSyntax.codeConversion w b c S J) := by
  let P := SyntaxFreeSubstSyntax.codeConversion w.castSucc b.castSucc c.castSucc (Fin.last m) J.castSucc
  have hL : P.instantiate L = SyntaxFreeSubstSyntax.codeConversion w b c L J := by
    simp only [P, Formula.instantiate, SyntaxFreeSubstSyntax.codeConversion_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have hS : P.instantiate S = SyntaxFreeSubstSyntax.codeConversion w b c S J := by
    simp only [P, Formula.instantiate, SyntaxFreeSubstSyntax.codeConversion_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact of_eq hS (Derives.eqSubst P he (of_eq hL.symm hc))

theorem from_converted {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w J S b a c : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (IndexTermImageCodeSyntax.converted false w J S b a c)) :
    Derives Γ (SyntaxFreeSubstSyntax.codeConversion w b c S J) := by
  have hi := IndexTermImageCodeTyping.input_of_converted false w J S b a c hc
  let B := SyntaxFreeSubstSyntax.codeConversion w.castSucc b.castSucc c.castSucc (Fin.last m) J.castSucc
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) (SyntaxFreeSubstCode.from_map hZ w b c J hw (.conjR hi))
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw B)
  have hc1 : Derives Δ (IndexTermImageCodeSyntax.converted false w.castSucc J.castSucc S.castSucc b.castSucc a.castSucc c.castSucc) := of_eq (IndexTermImageCodeSyntax.converted_rename false w J S b a c Fin.castSucc) (under hc B)
  have ha1 : Derives Δ (.mem a.castSucc w.castSucc) := under (.conjL (.conjL hi)) B
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have he := FreeSubstImageCode.converted_unique_same_code (ZFContext.under hZ B) w.castSucc b.castSucc a.castSucc c.castSucc (Fin.last m) J.castSucc S.castSucc hw1 ha1 hB hc1
  have ho := list_subst w.castSucc b.castSucc c.castSucc (Fin.last m) S.castSucc J.castSucc (eq_symm he) hB
  exact of_eq (SyntaxFreeSubstSyntax.codeConversion_rename w b c S J Fin.castSucc).symm ho

end PPAC.Migration.Internal.OriginalFreeImageConversion
