import PPAC.Migration.Internal.HornVariableValue
import PPAC.Migration.Internal.HornExprExistence
import PPAC.Migration.Internal.OriginalAbstractTrace

/-! 从真实变量表达式图和实际变量码反向取出内部索引图；值见证只在对象EX中使用。 -/
namespace PPAC.Migration.Internal.AbstractVariableIndex
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax
open SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC.Automation.ObjectHorn (Expr)

theorem code_index_subst {m} {Γ : Context m} (bound : Bool) (w i j y : Fin m)
    (he : Derives Γ (.equal i j)) (hc : Derives Γ (SyntaxVariableSyntax.code bound w i y)) :
    Derives Γ (SyntaxVariableSyntax.code bound w j y) := by
  let P := SyntaxVariableSyntax.code bound w.castSucc (Fin.last m) y.castSucc
  exact of_eq (by simp only [P, Formula.instantiate, SyntaxVariableSyntax.code_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
    (Derives.eqSubst P he (of_eq (by simp only [P, Formula.instantiate, SyntaxVariableSyntax.code_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hc))

theorem index_graph {m n} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (bound : Bool) (e : Expr n)
    (w idx x : Fin m) (env : Fin n → Fin m) (hw : Derives Γ (omega w))
    (hn : Derives Γ (environmentNat n w env))
    (hg : Derives Γ (graph (HornVariableExpr.expression bound e) w env x))
    (hv : Derives Γ (SyntaxVariableSyntax.code bound w idx x)) : Derives Γ (graph e w env idx) := by
  let B := (Formula.mem (Fin.last m) w.castSucc).conj (graph e w.castSucc (fun j => (env j).castSucc) (Fin.last m))
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) (HornExprExistence.exists_value hZ e w env hw hn)
  have hZ1 := ZFContext.under hZ B
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw B)
  have hn1 := of_eq (environmentNat_rename n w env Fin.castSucc) (under hn B)
  have hg1 := of_eq (graph_rename _ w x env Fin.castSucc) (under hg B)
  have hv1 := of_eq (SyntaxVariableSyntax.code_rename bound w idx x Fin.castSucc) (under hv B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hc := HornVariableValue.graph_code hZ1 bound e _ _ _ _ hw1 hn1 (.conjR hB) hg1
  have he := SyntaxVariableDecode.index_eq hZ1 bound _ _ _ _ hw1 hc hv1
  have ho := output_subst e _ _ _ _ he (.conjR hB)
  exact of_eq (graph_rename e w idx env Fin.castSucc).symm ho

end PPAC.Migration.Internal.AbstractVariableIndex
