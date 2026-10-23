import PPAC.Migration.Internal.SyntaxTopCodedEnvironmentFiber
import PPAC.Migration.Internal.SyntaxMixedFormulaEndpoints

/-! 真实首槽数值环境接入全内部混合公式替换的实际输出纤维；原操作数值quotation另行证明。 -/
namespace PPAC.Migration.Internal.SyntaxTopFormulaAtCodes
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxRenameQuerySyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem instantiate_formula_fiber {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b A t R S n : Fin m)
    (hw : Derives Γ (omega w)) (he : Derives Γ (SyntaxTopCodedEnvironmentSyntax.instantiateCoded w a b A t R S))
    (hn : Derives Γ (FormulaCodeSyntax.formulaCode w n A b)) :
    Derives Γ (SyntaxMixedFormulaOutputSyntax.fiber w R S A b a b n) :=
  SyntaxMixedFormulaOutputInduction.actual_fiber hZ w R S A b a b n hw
    (.conjI hn (SyntaxTopCodedEnvironmentTyping.instantiate_lists w a b A t R S he))

theorem instantiate_formula_exists {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b A t R S n : Fin m)
    (hw : Derives Γ (omega w)) (he : Derives Γ (SyntaxTopCodedEnvironmentSyntax.instantiateCoded w a b A t R S))
    (hn : Derives Γ (FormulaCodeSyntax.formulaCode w n A b)) :
    Derives Γ (SyntaxMixedFormulaOutputSyntax.existsOutput w R S A b a b n) :=
  SyntaxMixedFormulaOutput.exists_of_fiber w R S A b a b n (instantiate_formula_fiber hZ w a b A t R S n hw he hn)

theorem abstract_formula_fiber {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b A B R S n : Fin m)
    (hw : Derives Γ (omega w)) (he : Derives Γ (SyntaxTopCodedEnvironmentSyntax.abstractCoded w a b A B R S))
    (hn : Derives Γ (FormulaCodeSyntax.formulaCode w n a B)) :
    Derives Γ (SyntaxMixedFormulaOutputSyntax.fiber w R S a B A b n) :=
  SyntaxMixedFormulaOutputInduction.actual_fiber hZ w R S a B A b n hw
    (.conjI hn (SyntaxTopCodedEnvironmentTyping.abstract_lists w a b A B R S he))

theorem abstract_formula_exists {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b A B R S n : Fin m)
    (hw : Derives Γ (omega w)) (he : Derives Γ (SyntaxTopCodedEnvironmentSyntax.abstractCoded w a b A B R S))
    (hn : Derives Γ (FormulaCodeSyntax.formulaCode w n a B)) :
    Derives Γ (SyntaxMixedFormulaOutputSyntax.existsOutput w R S a B A b n) :=
  SyntaxMixedFormulaOutput.exists_of_fiber w R S a B A b n (abstract_formula_fiber hZ w a b A B R S n hw he hn)

end PPAC.Migration.Internal.SyntaxTopFormulaAtCodes
