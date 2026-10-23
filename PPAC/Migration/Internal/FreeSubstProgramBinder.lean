import PPAC.Migration.Internal.ObjectFreeVariablePrograms
import PPAC.Migration.Internal.SyntaxIdentityLift

/-! 量词下原自由替换表L严格不变；实际新环境与子程序重新满足同一个特化接口。 -/
namespace PPAC.Migration.Internal.FreeSubstProgramBinder
open Source SourceAlgebra SourceLogic OmegaSyntax
open SyntaxRenameQuerySyntax (of_eq)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem environment_subst_free {m} {Γ : Context m} (w I J R S a b c d T : Fin m)
    (he : Derives Γ (.equal S T)) (hh : Derives Γ (IndexTermImageCodeSyntax.environment w I J R S a b c d)) :
    Derives Γ (IndexTermImageCodeSyntax.environment w I J R T a b c d) := by
  let P := IndexTermImageCodeSyntax.environment w.castSucc I.castSucc J.castSucc R.castSucc (Fin.last m) a.castSucc b.castSucc c.castSucc d.castSucc
  have e0 : P.instantiate S = IndexTermImageCodeSyntax.environment w I J R S a b c d := by
    simp only [P, Formula.instantiate, IndexTermImageCodeSyntax.environment_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have e1 : P.instantiate T = IndexTermImageCodeSyntax.environment w I J R T a b c d := by
    simp only [P, Formula.instantiate, IndexTermImageCodeSyntax.environment_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact of_eq e1 (Derives.eqSubst P he (of_eq e0.symm hh))

theorem environment_subst_bound {m} {Γ : Context m} (w I J R S a b c d C : Fin m)
    (he : Derives Γ (.equal c C)) (hh : Derives Γ (IndexTermImageCodeSyntax.environment w I J R S a b c d)) :
    Derives Γ (IndexTermImageCodeSyntax.environment w I J R S a b C d) := by
  let P := IndexTermImageCodeSyntax.environment w.castSucc I.castSucc J.castSucc R.castSucc S.castSucc a.castSucc b.castSucc (Fin.last m) d.castSucc
  have e0 : P.instantiate c = IndexTermImageCodeSyntax.environment w I J R S a b c d := by
    simp only [P, Formula.instantiate, IndexTermImageCodeSyntax.environment_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have e1 : P.instantiate C = IndexTermImageCodeSyntax.environment w I J R S a b C d := by
    simp only [P, Formula.instantiate, IndexTermImageCodeSyntax.environment_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact of_eq e1 (Derives.eqSubst P he (of_eq e0.symm hh))

theorem execution_subst_free {m} {Γ : Context m} (w R S a b c d n q T : Fin m)
    (he : Derives Γ (.equal S T)) (hh : Derives Γ (FormulaTransformExecutionSyntax.executed w R S a b c d n q)) :
    Derives Γ (FormulaTransformExecutionSyntax.executed w R T a b c d n q) := by
  let P := FormulaTransformExecutionSyntax.executed w.castSucc R.castSucc (Fin.last m) a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc q.castSucc
  have e0 : P.instantiate S = FormulaTransformExecutionSyntax.executed w R S a b c d n q := by
    simp only [P, Formula.instantiate, FormulaTransformExecutionSyntax.executed_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have e1 : P.instantiate T = FormulaTransformExecutionSyntax.executed w R T a b c d n q := by
    simp only [P, Formula.instantiate, FormulaTransformExecutionSyntax.executed_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact of_eq e1 (Derives.eqSubst P he (of_eq e0.symm hh))

theorem execution_subst_bound {m} {Γ : Context m} (w R S a b c d n q C : Fin m)
    (he : Derives Γ (.equal c C)) (hh : Derives Γ (FormulaTransformExecutionSyntax.executed w R S a b c d n q)) :
    Derives Γ (FormulaTransformExecutionSyntax.executed w R S a b C d n q) := by
  let P := FormulaTransformExecutionSyntax.executed w.castSucc R.castSucc S.castSucc a.castSucc b.castSucc (Fin.last m) d.castSucc n.castSucc q.castSucc
  have e0 : P.instantiate c = FormulaTransformExecutionSyntax.executed w R S a b c d n q := by
    simp only [P, Formula.instantiate, FormulaTransformExecutionSyntax.executed_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have e1 : P.instantiate C = FormulaTransformExecutionSyntax.executed w R S a b C d n q := by
    simp only [P, Formula.instantiate, FormulaTransformExecutionSyntax.executed_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact of_eq e1 (Derives.eqSubst P he (of_eq e0.symm hh))

theorem free_code_stable {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w I J R S a b c d A C M K H L : Fin m)
    (hw : Derives Γ (omega w)) (he : Derives Γ (IndexTermImageCodeSyntax.environment w I J R S a b c d))
    (hl : Derives Γ (SyntaxFreeSubstSyntax.codeConversion w b d L J))
    (ho : Derives Γ (SyntaxMapLiftSyntax.codedLift w a c I A C M))
    (hn : Derives Γ (SyntaxCodedMixedBinderSyntax.lifted w R S a b c d A C K H)) : Derives Γ (.equal H L) := by
  have hEnv := IndexTermCodedBinderTransport.coded_lift hZ w I J R S a b c d A C M K H hw he ho hn
  have hi := IndexTermImageCodeTyping.input_of_converted false w J H b C d (.conjR hEnv)
  exact FreeSubstImageCode.converted_unique_same_code hZ w b C d L J H hw (.conjL (.conjL hi)) hl (.conjR hEnv)

theorem lifted_environment {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b a c L I J R u v M K H : Fin m)
    (hw : Derives Γ (omega w)) (he : Derives Γ (IndexTermImageCodeSyntax.environment w I J R L b a b c))
    (hi : Derives Γ (SyntaxIdentityMapSyntax.identityCode w b I))
    (hl : Derives Γ (SyntaxFreeSubstSyntax.codeConversion w a c L J))
    (ho : Derives Γ (SyntaxMapLiftSyntax.codedLift w b b I u v M))
    (hn : Derives Γ (SyntaxCodedMixedBinderSyntax.lifted w R L b a b c u v K H)) :
    Derives Γ ((Formula.equal u v).conj ((SyntaxIdentityMapSyntax.identityCode w u M).conj
      ((Formula.equal H L).conj (IndexTermImageCodeSyntax.environment w M J K L u a u c)))) := by
  have hId := SyntaxIdentityLift.code_lift hZ w b I u v M hw hi ho
  have hFree := free_code_stable hZ w I J R L b a b c u v M K H L hw he hl ho hn
  have hEnv := IndexTermCodedBinderTransport.coded_lift hZ w I J R L b a b c u v M K H hw he ho hn
  have hEnv1 := environment_subst_free w M J K H u a v c L hFree hEnv
  have hEnv2 := environment_subst_bound w M J K L u a v c u (eq_symm (.conjL hId)) hEnv1
  exact .conjI (.conjL hId) (.conjI (.conjR hId) (.conjI hFree hEnv2))

theorem child_execution {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b a c L I J R u v M K H x q : Fin m)
    (hw : Derives Γ (omega w)) (he : Derives Γ (IndexTermImageCodeSyntax.environment w I J R L b a b c))
    (hi : Derives Γ (SyntaxIdentityMapSyntax.identityCode w b I))
    (hl : Derives Γ (SyntaxFreeSubstSyntax.codeConversion w a c L J))
    (ho : Derives Γ (SyntaxMapLiftSyntax.codedLift w b b I u v M))
    (hn : Derives Γ (SyntaxCodedMixedBinderSyntax.lifted w R L b a b c u v K H))
    (hx : Derives Γ (FormulaTransformExecutionSyntax.executed w K H u a v c x q)) :
    Derives Γ (FreeSubstProgramSyntax.executed w u a c L x q) := by
  have hh := lifted_environment hZ w b a c L I J R u v M K H hw he hi hl ho hn
  have hRun := execution_subst_bound w K L u a v c x q u (eq_symm (.conjL hh))
    (execution_subst_free w K H u a v c x q L (.conjL (.conjR (.conjR hh))) hx)
  exact FreeSubstProgramSyntax.intro_executed w u a c L x q M K
    (SyntaxFreeSubstCode.list_of_conversion w a c L J hl) (.conjL (.conjR hh))
    (.conjL (.conjR (.conjR (.conjR hh)))) hRun

end PPAC.Migration.Internal.FreeSubstProgramBinder
