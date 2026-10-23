import PPAC.Migration.Internal.FreeSubstProgramSyntax
import PPAC.Migration.Internal.SyntaxFormulaFreeSubstUnique

/-! 原项码列表参数的全部内部自由替换，与实际独立公式程序特化双向对应。 -/
namespace PPAC.Migration.Internal.FreeSubstProgramCorrectness
open Source SourceAlgebra SourceLogic OmegaSyntax FreeSubstProgramSyntax
open SyntaxRenameQuerySyntax (of_eq)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem forward {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b a c L n q : Fin m)
    (hw : Derives Γ (omega w)) (hq : Derives Γ (SyntaxFormulaFreeSubstSyntax.substituted w b a c L n q)) :
    Derives Γ (executed w b a c L n q) := by
  let B := SyntaxFormulaFreeSubstSyntax.body w b a c L n q
  let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply SyntaxRenameBinders.eliminate_2 B _ hq
  have hZ2 := SyntaxRenameBinders.zf_under_2 hZ B
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxRenameBinders.under_2 hw B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hJ := SyntaxFreeSubstCode.map_of_conversion w.castSucc.castSucc a.castSucc.castSucc c.castSucc.castSucc L.castSucc.castSucc (Fin.last (m+1)) (.conjL (.conjR hB))
  have hc := Derives.conjR (SyntaxMapCodeDecode.contexts w.castSucc.castSucc a.castSucc.castSucc c.castSucc.castSucc (Fin.last (m+1)) hJ)
  have hx := FreeSubstImageCode.identity_image_exists hZ2 w.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc (Fin.last m).castSucc hw2 hc (.conjL hB)
  let E := IndexTermImageCodeSyntax.converted true w.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc (Fin.last (m+2)) b.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc
  let Ξ := Context.add E (Context.image Formula.raise Δ)
  apply Derives.exE (p := E) hx
  have hZ3 := ZFContext.under hZ2 E
  have hw3 : Derives Ξ (omega w.castSucc.castSucc.castSucc) := of_eq (omega_rename w.castSucc.castSucc Fin.castSucc) (under hw2 E)
  have hB3 : Derives Ξ ((SyntaxIdentityMapSyntax.identityCode w.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc).conj ((SyntaxFreeSubstSyntax.codeConversion w.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc L.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc).conj (SyntaxRenameJudgmentSyntax.renamed w.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc b.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc q.castSucc.castSucc.castSucc))) := of_eq (by simp only [B, SyntaxFormulaFreeSubstSyntax.body, Formula.rename, SyntaxIdentityMapSyntax.identityCode_rename, SyntaxFreeSubstSyntax.codeConversion_rename, SyntaxRenameJudgmentSyntax.renamed_rename, Formula.raise]) (under hB E)
  have hE : Derives Ξ E := .hyp (Or.inl rfl)
  have hI := SyntaxIdentityCode.map_code w.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc (.conjL hB3)
  have hb := Derives.conjL (SyntaxMapCodeDecode.contexts w.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc hI)
  have hFree := FreeSubstImageCode.same_code hZ3 w.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc L.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc hw3 hb (.conjL (.conjR hB3))
  have hBridge := IndexFormulaRenameBridge.program_iff hZ3 w.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc (Fin.last (m+2)) L.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc q.castSucc.castSucc.castSucc hw3 (.conjI hE hFree)
  have hRun := Derives.impE (.conjR hBridge) (.conjR (.conjR hB3))
  have hL := SyntaxFreeSubstCode.list_of_conversion w.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc L.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc (.conjL (.conjR hB3))
  have ho := intro_executed w.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc L.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc q.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc (Fin.last (m+2)) hL (.conjL hB3) hE hRun
  exact of_eq (by simp only [Formula.raise, executed_rename]) ho

theorem reverse {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b a c L n q : Fin m)
    (hw : Derives Γ (omega w)) (hq : Derives Γ (executed w b a c L n q)) :
    Derives Γ (SyntaxFormulaFreeSubstSyntax.substituted w b a c L n q) := by
  let B := FreeSubstProgramSyntax.body w b a c L n q
  let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply SyntaxRenameBinders.eliminate_2 B _ (.conjR hq)
  have hZ2 := SyntaxRenameBinders.zf_under_2 hZ B
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxRenameBinders.under_2 hw B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hL2 : Derives Δ (SyntaxFreeSubstSyntax.termList w.castSucc.castSucc a.castSucc.castSucc c.castSucc.castSucc L.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxFreeSubstSyntax.termList_rename]) (SyntaxRenameBinders.under_2 (.conjL hq) B)
  have hx := SyntaxFreeSubstCode.from_list hZ2 w.castSucc.castSucc a.castSucc.castSucc c.castSucc.castSucc L.castSucc.castSucc hw2 hL2
  let E := SyntaxFreeSubstSyntax.codeConversion w.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc L.castSucc.castSucc.castSucc (Fin.last (m+2))
  let Ξ := Context.add E (Context.image Formula.raise Δ)
  apply Derives.exE (p := E) hx
  have hZ3 := ZFContext.under hZ2 E
  have hw3 : Derives Ξ (omega w.castSucc.castSucc.castSucc) := of_eq (omega_rename w.castSucc.castSucc Fin.castSucc) (under hw2 E)
  have hB3 : Derives Ξ (ready w.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc L.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc q.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc) := of_eq (by simp only [B, FreeSubstProgramSyntax.body, ready_rename, Formula.raise]) (under hB E)
  have hE : Derives Ξ E := .hyp (Or.inl rfl)
  have hI := SyntaxIdentityCode.map_code w.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc (.conjL hB3)
  have hb := Derives.conjL (SyntaxMapCodeDecode.contexts w.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc hI)
  have hFree := FreeSubstImageCode.same_code hZ3 w.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc L.castSucc.castSucc.castSucc (Fin.last (m+2)) hw3 hb hE
  have hBridge := IndexFormulaRenameBridge.program_iff hZ3 w.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc (Fin.last (m+2)) (Fin.last (m+1)).castSucc L.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc q.castSucc.castSucc.castSucc hw3 (.conjI (.conjL (.conjR hB3)) hFree)
  have hOld := Derives.impE (.conjL hBridge) (.conjR (.conjR hB3))
  have ho := SyntaxFormulaFreeSubstSyntax.intro_substituted w.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc L.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc q.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc (Fin.last (m+2)) (.conjL hB3) hE hOld
  exact of_eq (by simp only [Formula.raise, SyntaxFormulaFreeSubstSyntax.substituted_rename]) ho

theorem executed_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b a c L n q : Fin m)
    (hw : Derives Γ (omega w)) :
    Derives Γ ((executed w b a c L n q).iff (SyntaxFormulaFreeSubstSyntax.substituted w b a c L n q)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact reverse (ZFContext.add hZ _) w b a c L n q (add hw _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact forward (ZFContext.add hZ _) w b a c L n q (add hw _) (.hyp (Or.inl rfl))

end PPAC.Migration.Internal.FreeSubstProgramCorrectness
