import PPAC.Migration.Internal.SyntaxTopFormulaExistence

/-! 全内部候选下首槽公式输出唯一，独立于数值环境见证。 -/
namespace PPAC.Migration.Internal.SyntaxTopFormulaUnique
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxRenameQuerySyntax SyntaxTopFormulaSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem instantiate_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b A t n q v : Fin m)
    (hw : Derives Γ (omega w)) (hq : Derives Γ (instantiated w a b A t n q)) (hv : Derives Γ (instantiated w a b A t n v)) : Derives Γ (.equal q v) := by
  let E := instantiateBody w a b A t n q
  let Δ := Context.add E (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply SyntaxRenameBinders.eliminate_2 E _ hq
  have hZ2 := SyntaxRenameBinders.zf_under_2 hZ E
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxRenameBinders.under_2 hw E)
  have hv2 : Derives Δ (instantiated w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc A.castSucc.castSucc t.castSucc.castSucc n.castSucc.castSucc v.castSucc.castSucc) := of_eq (by simp only [Formula.raise, instantiated_rename]) (SyntaxRenameBinders.under_2 hv E)
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have hr := Derives.impE (.conjL (SyntaxTopFormulaCodes.instantiate_at_codes hZ2 w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc A.castSucc.castSucc t.castSucc.castSucc n.castSucc.castSucc v.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) hw2 (.conjL hE))) hv2
  exact SyntaxMixedFormulaOutputInduction.unique hZ2 w.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) A.castSucc.castSucc b.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc n.castSucc.castSucc q.castSucc.castSucc v.castSucc.castSucc hw2 (.conjR hE) hr

theorem instantiate_unique_output {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b A t n q : Fin m)
    (hw : Derives Γ (omega w)) (hq : Derives Γ (instantiated w a b A t n q)) : Derives Γ (instantiateUnique w a b A t n q) := by
  apply Derives.allI
  apply Derives.impI
  let V := instantiated w.castSucc a.castSucc b.castSucc A.castSucc t.castSucc n.castSucc (Fin.last m)
  let Δ := Context.add V (Context.image Formula.raise Γ)
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw V)
  have hq1 : Derives Δ (instantiated w.castSucc a.castSucc b.castSucc A.castSucc t.castSucc n.castSucc q.castSucc) := of_eq (instantiated_rename w a b A t n q Fin.castSucc) (under hq V)
  exact instantiate_unique (ZFContext.under hZ V) w.castSucc a.castSucc b.castSucc A.castSucc t.castSucc n.castSucc (Fin.last m) q.castSucc hw1 (.hyp (Or.inl rfl)) hq1

theorem abstract_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b A B n q v : Fin m)
    (hw : Derives Γ (omega w)) (hq : Derives Γ (abstracted w a b A B n q)) (hv : Derives Γ (abstracted w a b A B n v)) : Derives Γ (.equal q v) := by
  let E := abstractBody w a b A B n q
  let Δ := Context.add E (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply SyntaxRenameBinders.eliminate_2 E _ hq
  have hZ2 := SyntaxRenameBinders.zf_under_2 hZ E
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxRenameBinders.under_2 hw E)
  have hv2 : Derives Δ (abstracted w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc A.castSucc.castSucc B.castSucc.castSucc n.castSucc.castSucc v.castSucc.castSucc) := of_eq (by simp only [Formula.raise, abstracted_rename]) (SyntaxRenameBinders.under_2 hv E)
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have hr := Derives.impE (.conjL (SyntaxTopFormulaCodes.abstract_at_codes hZ2 w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc A.castSucc.castSucc B.castSucc.castSucc n.castSucc.castSucc v.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) hw2 (.conjL hE))) hv2
  exact SyntaxMixedFormulaOutputInduction.unique hZ2 w.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) a.castSucc.castSucc B.castSucc.castSucc A.castSucc.castSucc b.castSucc.castSucc n.castSucc.castSucc q.castSucc.castSucc v.castSucc.castSucc hw2 (.conjR hE) hr

theorem abstract_unique_output {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b A B n q : Fin m)
    (hw : Derives Γ (omega w)) (hq : Derives Γ (abstracted w a b A B n q)) : Derives Γ (abstractUnique w a b A B n q) := by
  apply Derives.allI
  apply Derives.impI
  let V := abstracted w.castSucc a.castSucc b.castSucc A.castSucc B.castSucc n.castSucc (Fin.last m)
  let Δ := Context.add V (Context.image Formula.raise Γ)
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw V)
  have hq1 : Derives Δ (abstracted w.castSucc a.castSucc b.castSucc A.castSucc B.castSucc n.castSucc q.castSucc) := of_eq (abstracted_rename w a b A B n q Fin.castSucc) (under hq V)
  exact abstract_unique (ZFContext.under hZ V) w.castSucc a.castSucc b.castSucc A.castSucc B.castSucc n.castSucc (Fin.last m) q.castSucc hw1 (.hyp (Or.inl rfl)) hq1

end PPAC.Migration.Internal.SyntaxTopFormulaUnique
