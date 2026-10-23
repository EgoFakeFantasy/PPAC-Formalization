import PPAC.Migration.Internal.SyntaxTopFormulaCodes

/-! 无外部环境见证的首槽公式判断具有准确源/目标类型、合法输入和内部自然码守卫。 -/
namespace PPAC.Migration.Internal.SyntaxTopFormulaTyping
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxRenameQuerySyntax SyntaxTopFormulaSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem instantiate_environment {m} {Γ : Context m} (w a b A t n q : Fin m)
    (hq : Derives Γ (instantiated w a b A t n q)) : Derives Γ (SyntaxTopEnvironmentSyntax.instantiateInput w a b A t) := by
  let E := instantiateBody w a b A t n q
  let Δ := Context.add E (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply SyntaxRenameBinders.eliminate_2 E _ hq
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have ho : Derives Δ (SyntaxTopEnvironmentSyntax.instantiateInput w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc A.castSucc.castSucc t.castSucc.castSucc) := SyntaxTopCodedEnvironmentTyping.instantiate_input w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc A.castSucc.castSucc t.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) (.conjL hE)
  exact of_eq (by simp only [Formula.raise, SyntaxTopEnvironmentSyntax.instantiateInput_rename]) ho

theorem instantiate_source_type {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b A t n q : Fin m)
    (hw : Derives Γ (omega w)) (hq : Derives Γ (instantiated w a b A t n q)) : Derives Γ (FormulaCodeSyntax.formulaCode w n A b) := by
  let E := instantiateBody w a b A t n q
  let Δ := Context.add E (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply SyntaxRenameBinders.eliminate_2 E _ hq
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have hZ2 := SyntaxRenameBinders.zf_under_2 hZ E
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxRenameBinders.under_2 hw E)
  have ho : Derives Δ (FormulaCodeSyntax.formulaCode w.castSucc.castSucc n.castSucc.castSucc A.castSucc.castSucc b.castSucc.castSucc) := SyntaxMixedFormulaRecursive.source_type hZ2 w.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) A.castSucc.castSucc b.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc n.castSucc.castSucc q.castSucc.castSucc hw2 (.conjR hE)
  exact of_eq (by simp only [Formula.raise, FormulaCodeSyntax.formulaCode_rename]) ho

theorem instantiate_target_type {m} {Γ : Context m} (w a b A t n q : Fin m)
    (hq : Derives Γ (instantiated w a b A t n q)) : Derives Γ (FormulaCodeSyntax.formulaCode w q a b) := by
  let E := instantiateBody w a b A t n q
  let Δ := Context.add E (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply SyntaxRenameBinders.eliminate_2 E _ hq
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have ho : Derives Δ (FormulaCodeSyntax.formulaCode w.castSucc.castSucc q.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc) := SyntaxMixedFormulaJudgment.target_type w.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) A.castSucc.castSucc b.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc n.castSucc.castSucc q.castSucc.castSucc (.conjR hE)
  exact of_eq (by simp only [Formula.raise, FormulaCodeSyntax.formulaCode_rename]) ho

theorem instantiate_source_natural {m} {Γ : Context m} (w a b A t n q : Fin m)
    (hq : Derives Γ (instantiated w a b A t n q)) : Derives Γ (Formula.mem n w) := by
  let E := instantiateBody w a b A t n q
  let Δ := Context.add E (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply SyntaxRenameBinders.eliminate_2 E _ hq
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have ho : Derives Δ (Formula.mem n.castSucc.castSucc w.castSucc.castSucc) := .conjL (.conjR hE)
  exact of_eq (by simp only [Formula.raise, Formula.rename]) ho

theorem instantiate_input {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b A t n q : Fin m)
    (hw : Derives Γ (omega w)) (hq : Derives Γ (instantiated w a b A t n q)) : Derives Γ (instantiateInput w a b A t n) :=
  .conjI (instantiate_environment w a b A t n q hq) (instantiate_source_type hZ w a b A t n q hw hq)

theorem instantiate_target_natural {m} {Γ : Context m} (w a b A t n q : Fin m)
    (hq : Derives Γ (instantiated w a b A t n q)) : Derives Γ (.mem q w) :=
  .conjL (FormulaCodeProperties.guards w q a b (instantiate_target_type w a b A t n q hq))

theorem abstract_environment {m} {Γ : Context m} (w a b A B n q : Fin m)
    (hq : Derives Γ (abstracted w a b A B n q)) : Derives Γ (SyntaxTopEnvironmentSyntax.abstractInput w a b A B) := by
  let E := abstractBody w a b A B n q
  let Δ := Context.add E (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply SyntaxRenameBinders.eliminate_2 E _ hq
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have ho : Derives Δ (SyntaxTopEnvironmentSyntax.abstractInput w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc A.castSucc.castSucc B.castSucc.castSucc) := SyntaxTopCodedEnvironmentTyping.abstract_input w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc A.castSucc.castSucc B.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) (.conjL hE)
  exact of_eq (by simp only [Formula.raise, SyntaxTopEnvironmentSyntax.abstractInput_rename]) ho

theorem abstract_source_type {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b A B n q : Fin m)
    (hw : Derives Γ (omega w)) (hq : Derives Γ (abstracted w a b A B n q)) : Derives Γ (FormulaCodeSyntax.formulaCode w n a B) := by
  let E := abstractBody w a b A B n q
  let Δ := Context.add E (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply SyntaxRenameBinders.eliminate_2 E _ hq
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have hZ2 := SyntaxRenameBinders.zf_under_2 hZ E
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxRenameBinders.under_2 hw E)
  have ho : Derives Δ (FormulaCodeSyntax.formulaCode w.castSucc.castSucc n.castSucc.castSucc a.castSucc.castSucc B.castSucc.castSucc) := SyntaxMixedFormulaRecursive.source_type hZ2 w.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) a.castSucc.castSucc B.castSucc.castSucc A.castSucc.castSucc b.castSucc.castSucc n.castSucc.castSucc q.castSucc.castSucc hw2 (.conjR hE)
  exact of_eq (by simp only [Formula.raise, FormulaCodeSyntax.formulaCode_rename]) ho

theorem abstract_target_type {m} {Γ : Context m} (w a b A B n q : Fin m)
    (hq : Derives Γ (abstracted w a b A B n q)) : Derives Γ (FormulaCodeSyntax.formulaCode w q A b) := by
  let E := abstractBody w a b A B n q
  let Δ := Context.add E (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply SyntaxRenameBinders.eliminate_2 E _ hq
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have ho : Derives Δ (FormulaCodeSyntax.formulaCode w.castSucc.castSucc q.castSucc.castSucc A.castSucc.castSucc b.castSucc.castSucc) := SyntaxMixedFormulaJudgment.target_type w.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) a.castSucc.castSucc B.castSucc.castSucc A.castSucc.castSucc b.castSucc.castSucc n.castSucc.castSucc q.castSucc.castSucc (.conjR hE)
  exact of_eq (by simp only [Formula.raise, FormulaCodeSyntax.formulaCode_rename]) ho

theorem abstract_source_natural {m} {Γ : Context m} (w a b A B n q : Fin m)
    (hq : Derives Γ (abstracted w a b A B n q)) : Derives Γ (Formula.mem n w) := by
  let E := abstractBody w a b A B n q
  let Δ := Context.add E (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply SyntaxRenameBinders.eliminate_2 E _ hq
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have ho : Derives Δ (Formula.mem n.castSucc.castSucc w.castSucc.castSucc) := .conjL (.conjR hE)
  exact of_eq (by simp only [Formula.raise, Formula.rename]) ho

theorem abstract_input {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b A B n q : Fin m)
    (hw : Derives Γ (omega w)) (hq : Derives Γ (abstracted w a b A B n q)) : Derives Γ (abstractInput w a b A B n) :=
  .conjI (abstract_environment w a b A B n q hq) (abstract_source_type hZ w a b A B n q hw hq)

theorem abstract_target_natural {m} {Γ : Context m} (w a b A B n q : Fin m)
    (hq : Derives Γ (abstracted w a b A B n q)) : Derives Γ (.mem q w) :=
  .conjL (FormulaCodeProperties.guards w q A b (abstract_target_type w a b A B n q hq))

end PPAC.Migration.Internal.SyntaxTopFormulaTyping
