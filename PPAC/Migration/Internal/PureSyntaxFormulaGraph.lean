import PPAC.Migration.Internal.PureArgumentsModeThree
import PPAC.Migration.Internal.FormulaCodeKnownAtomic

/-! 真实kind4行的通用三字段表达式图；类型比较不进入接受关系定义。 -/
namespace PPAC.Migration.Internal.PureSyntaxFormulaGraph
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax
open SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC.Automation.ObjectHorn (Expr)

def fields {a} (i j : Fin a) (e : Expr a) : Fin 3 → Expr a := Fin.cases (.var i) (Fin.cases (.var j) (Fin.cases e Fin.elim0))
def head {a} (i j : Fin a) (e : Expr a) : Expr a := Expr.node (.literal 4) (List.ofFn (fields i j e))

theorem recover {m a} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (i j : Fin a) (e : Expr a)
    (w b f n r : Fin m) (env : Fin a → Fin m) (hw : Derives Γ (omega w))
    (hn : Derives Γ (environmentNat a w env)) (hr : Derives Γ (PureSyntaxTrace.formulaRow w b f n r))
    (hg : Derives Γ (graph (head i j e) w env r)) :
    Derives Γ ((Formula.equal b (env i)).conj ((Formula.equal f (env j)).conj (graph e w env n))) := by
  have h0 := HornNodeFields.field_3 hZ 4 (fields i j e) w r env (SyntaxAtomSyntax.three b f n) 0 hw hn hg hr
  have h1 := HornNodeFields.field_3 hZ 4 (fields i j e) w r env (SyntaxAtomSyntax.three b f n) 1 hw hn hg hr
  have h2 := HornNodeFields.field_3 hZ 4 (fields i j e) w r env (SyntaxAtomSyntax.three b f n) 2 hw hn hg hr
  exact .conjI (.conjR h0) (.conjI (.conjR h1) h2)

theorem construct {m a} {Γ : Context m} (i j : Fin a) (e : Expr a)
    (w n r : Fin m) (env : Fin a → Fin m) (hn : Derives Γ (environmentNat a w env))
    (hr : Derives Γ (PureSyntaxTrace.formulaRow w (env i) (env j) n r))
    (he : Derives Γ (graph e w env n)) : Derives Γ (graph (head i j e) w env r) := by
  apply HornExprForest.constructor_graph 3 4 (fields i j e) w r env (SyntaxAtomSyntax.three (env i) (env j) n) _ hr
  intro k
  refine Fin.cases ?_ (fun l => ?_) k
  · exact .conjI (environmentNat_at w env hn i) (.eqRefl _)
  · refine Fin.cases ?_ (fun t => ?_) l
    · exact .conjI (environmentNat_at w env hn j) (.eqRefl _)
    · exact Fin.cases he (fun z => Fin.elim0 z) t

theorem contexts_subst {m} {Γ : Context m} (w b f B F n : Fin m)
    (hb : Derives Γ (.equal B b)) (hf : Derives Γ (.equal F f))
    (ht : Derives Γ (FormulaCodeSyntax.formulaCode w n B F)) : Derives Γ (FormulaCodeSyntax.formulaCode w n b f) := by
  let P := FormulaCodeSyntax.formulaCode w.castSucc n.castSucc (Fin.last m) F.castSucc
  have h0 : P.instantiate B = FormulaCodeSyntax.formulaCode w n B F := by simp only [P, Formula.instantiate, FormulaCodeSyntax.formulaCode_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have h1 : P.instantiate b = FormulaCodeSyntax.formulaCode w n b F := by simp only [P, Formula.instantiate, FormulaCodeSyntax.formulaCode_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have hp := of_eq h1 (Derives.eqSubst P hb (of_eq h0.symm ht))
  let Q := FormulaCodeSyntax.formulaCode w.castSucc n.castSucc b.castSucc (Fin.last m)
  have h2 : Q.instantiate F = FormulaCodeSyntax.formulaCode w n b F := by simp only [Q, Formula.instantiate, FormulaCodeSyntax.formulaCode_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have h3 : Q.instantiate f = FormulaCodeSyntax.formulaCode w n b f := by simp only [Q, Formula.instantiate, FormulaCodeSyntax.formulaCode_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact of_eq h3 (Derives.eqSubst Q hf (of_eq h2.symm hp))

theorem intro_formula {m} {Γ : Context m} (w b f n r : Fin m)
    (hr : Derives Γ (PureSyntaxTrace.formulaRow w b f n r)) (hc : Derives Γ (PureSyntaxTrace.condition w r)) :
    Derives Γ (PureSyntaxTrace.formula w b f n) := by
  apply Derives.exI r
  exact of_eq (by simp only [Formula.instantiate, Formula.rename, PureSyntaxTrace.formulaRow_rename, PureSyntaxTrace.condition_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI hr hc)

end PPAC.Migration.Internal.PureSyntaxFormulaGraph
