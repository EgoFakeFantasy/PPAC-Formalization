import PPAC.Migration.Internal.WeakenFreeProgramSyntax

/-! 原free头槽弱化与独立公式程序的全部内部对应，不附加FreeClosed条件。 -/
namespace PPAC.Migration.Internal.WeakenFreeProgramCorrectness
open Source SourceAlgebra SourceLogic OmegaSyntax WeakenFreeProgramSyntax
open SyntaxRenameQuerySyntax (of_eq)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem forward {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b B n q : Fin m)
    (hw : Derives Γ (omega w)) (hq : Derives Γ (SyntaxWeakenFreeSyntax.weakened w a b B n q)) :
    Derives Γ (executed w a b B n q) := by
  let H := SyntaxWeakenFreeSyntax.body w a b B n q
  let Δ := Context.add H (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply SyntaxRenameBinders.eliminate_2 H _ hq
  have hZ2 := SyntaxRenameBinders.zf_under_2 hZ H
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxRenameBinders.under_2 hw H)
  have hH : Derives Δ H := .hyp (Or.inl rfl)
  have hI := SyntaxIdentityCode.map_code w.castSucc.castSucc a.castSucc.castSucc (Fin.last m).castSucc (.conjL hH)
  have hJ := SyntaxFreeShiftCode.map_code w.castSucc.castSucc b.castSucc.castSucc B.castSucc.castSucc (Fin.last (m+1)) (.conjL (.conjR hH))
  have hx := IndexTermImageEnvironment.exists_environment hZ2 w.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) a.castSucc.castSucc b.castSucc.castSucc a.castSucc.castSucc B.castSucc.castSucc hw2 hI hJ
  let E := IndexTermImageCodeSyntax.environment w.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc (Fin.last (m+2)).castSucc (Fin.last (m+3)) a.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc B.castSucc.castSucc.castSucc.castSucc
  let Ξ := Context.add E (Context.image Formula.raise (Context.image Formula.raise Δ))
  apply SyntaxRenameBinders.eliminate_2 E _ hx
  have hZ4 := SyntaxRenameBinders.zf_under_2 hZ2 E
  have hw4 : Derives Ξ (omega w.castSucc.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxRenameBinders.under_2 hw2 E)
  have hH4 : Derives Ξ ((SyntaxIdentityMapSyntax.identityCode w.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc).conj ((SyntaxFreeShiftSyntax.shiftCode w.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc B.castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc).conj (SyntaxRenameJudgmentSyntax.renamed w.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc B.castSucc.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc.castSucc q.castSucc.castSucc.castSucc.castSucc))) := of_eq (by simp only [H, SyntaxWeakenFreeSyntax.body, Formula.raise, Formula.rename, SyntaxIdentityMapSyntax.identityCode_rename, SyntaxFreeShiftSyntax.shiftCode_rename, SyntaxRenameJudgmentSyntax.renamed_rename]) (SyntaxRenameBinders.under_2 hH E)
  have hE : Derives Ξ E := .hyp (Or.inl rfl)
  have hBridge := IndexFormulaRenameBridge.program_iff hZ4 w.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc (Fin.last (m+2)).castSucc (Fin.last (m+3)) a.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc B.castSucc.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc.castSucc q.castSucc.castSucc.castSucc.castSucc hw4 hE
  have ho := intro_executed w.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc B.castSucc.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc.castSucc q.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc (Fin.last (m+2)).castSucc (Fin.last (m+3)) (.conjL hH4) (.conjL (.conjR hH4)) hE (.impE (.conjR hBridge) (.conjR (.conjR hH4)))
  exact of_eq (by simp only [Formula.raise, executed_rename]) ho

theorem reverse {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b B n q : Fin m)
    (hw : Derives Γ (omega w)) (hq : Derives Γ (executed w a b B n q)) :
    Derives Γ (SyntaxWeakenFreeSyntax.weakened w a b B n q) := by
  let H := body w a b B n q
  let Δ := Context.add H (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise Γ))))
  apply SyntaxRenameBinders.eliminate_4 H _ hq
  have hZ4 := SyntaxRenameBinders.zf_under_4 hZ H
  have hw4 : Derives Δ (omega w.castSucc.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxRenameBinders.under_4 hw H)
  have hH : Derives Δ H := .hyp (Or.inl rfl)
  have hBridge := IndexFormulaRenameBridge.program_iff hZ4 w.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc (Fin.last (m+2)).castSucc (Fin.last (m+3)) a.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc B.castSucc.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc.castSucc q.castSucc.castSucc.castSucc.castSucc hw4 (.conjL (.conjR (.conjR hH)))
  have hOld := Derives.impE (.conjL hBridge) (.conjR (.conjR (.conjR hH)))
  have ho := SyntaxWeakenFreeSyntax.intro_weakened w.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc B.castSucc.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc.castSucc q.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc (.conjL hH) (.conjL (.conjR hH)) hOld
  exact of_eq (by simp only [Formula.raise, SyntaxWeakenFreeSyntax.weakened_rename]) ho

theorem executed_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b B n q : Fin m)
    (hw : Derives Γ (omega w)) :
    Derives Γ ((executed w a b B n q).iff (SyntaxWeakenFreeSyntax.weakened w a b B n q)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact reverse (ZFContext.add hZ _) w a b B n q (add hw _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact forward (ZFContext.add hZ _) w a b B n q (add hw _) (.hyp (Or.inl rfl))

end PPAC.Migration.Internal.WeakenFreeProgramCorrectness
