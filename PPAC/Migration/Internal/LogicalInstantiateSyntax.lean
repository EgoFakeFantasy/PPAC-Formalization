import PPAC.Migration.Internal.LogicalInstantiateQueries

/-! 原逻辑20／23的三查询和25的五查询；规格仅使用纯类型与实际InstantiateTop。 -/
namespace PPAC.Migration.Internal.LogicalInstantiateSyntax
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax
open SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC.Automation
open YesMetaZFC.Automation.ObjectHorn (Expr)

def formula4 : Expr 4 := (ObjectLogicalAxiom.rule20.queries[0]).2

def term4 : Expr 4 := (ObjectLogicalAxiom.rule20.queries[1]).2

def transform4 : Expr 4 := (ObjectLogicalAxiom.rule20.queries[2]).2

def leftTerm6 : Expr 6 := (ObjectLogicalAxiom.rule25.queries[0]).2

def rightTerm6 : Expr 6 := (ObjectLogicalAxiom.rule25.queries[1]).2

def formula6 : Expr 6 := (ObjectLogicalAxiom.rule25.queries[2]).2

def leftTransform6 : Expr 6 := (ObjectLogicalAxiom.rule25.queries[3]).2

def rightTransform6 : Expr 6 := (ObjectLogicalAxiom.rule25.queries[4]).2

theorem same_twenty_twenty_three_queries : ObjectLogicalAxiom.rule23.queries = ObjectLogicalAxiom.rule20.queries := rfl

theorem actual_formula4 : formula4 = LogicalInstantiateQueries.formulaQuery 0 1 := rfl

theorem actual_term4 : term4 = LogicalInstantiateQueries.termQuery 0 2 := rfl

theorem actual_transform4 : transform4 = LogicalInstantiateQueries.transformQuery 2 1 3 := rfl

theorem actual_leftTerm6 : leftTerm6 = LogicalInstantiateQueries.termQuery 0 1 := rfl

theorem actual_rightTerm6 : rightTerm6 = LogicalInstantiateQueries.termQuery 0 2 := rfl

theorem actual_formula6 : formula6 = LogicalInstantiateQueries.formulaQuery 0 3 := rfl

theorem actual_leftTransform6 : leftTransform6 = LogicalInstantiateQueries.transformQuery 1 3 4 := rfl

theorem actual_rightTransform6 : rightTransform6 = LogicalInstantiateQueries.transformQuery 2 3 5 := rfl

def bundle4 {m} (w : Fin m) (env : Fin 4 → Fin m) : Formula m :=
  (PureSyntaxExprQuery.query formula4 w env).conj ((PureSyntaxExprQuery.query term4 w env).conj (OriginalTransformExprQuery.query transform4 w env))

def atBound4 {m} (w z A : Fin m) (env : Fin 4 → Fin m) : Formula m :=
  (FormulaCodeSyntax.formulaCode w (env 1) A (env 0)).conj ((SyntaxTermSyntax.term w z (env 0) (env 2)).conj (SyntaxTopFormulaSyntax.instantiated w z (env 0) A (env 2) (env 1) (env 3)))

def specification4 {m} (w z : Fin m) (env : Fin 4 → Fin m) : Formula m := .ex
  ((successor (Fin.last m) z.castSucc).conj (atBound4 w.castSucc z.castSucc (Fin.last m) (fun i => (env i).castSucc)))

theorem bundle4_rename {m l} (w : Fin m) (env : Fin 4 → Fin m) (ρ : Fin m → Fin l) :
    (bundle4 w env).rename ρ = bundle4 (ρ w) (fun i => ρ (env i)) := by
  simp only [bundle4, Formula.rename, PureSyntaxExprQuery.query_rename, OriginalTransformExprQuery.query_rename]

theorem atBound4_rename {m l} (w z A : Fin m) (env : Fin 4 → Fin m) (ρ : Fin m → Fin l) :
    (atBound4 w z A env).rename ρ = atBound4 (ρ w) (ρ z) (ρ A) (fun i => ρ (env i)) := by
  simp only [atBound4, Formula.rename, SyntaxTermSyntax.term_rename, FormulaCodeSyntax.formulaCode_rename, SyntaxTopFormulaSyntax.instantiated_rename]

theorem specification4_rename {m l} (w z : Fin m) (env : Fin 4 → Fin m) (ρ : Fin m → Fin l) :
    (specification4 w z env).rename ρ = specification4 (ρ w) (ρ z) (fun i => ρ (env i)) := by
  simp only [specification4, Formula.rename, successor_rename, atBound4_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem intro_specification4 {m} {Γ : Context m} (w z A : Fin m) (env : Fin 4 → Fin m)
    (hA : Derives Γ (successor A z)) (hs : Derives Γ (atBound4 w z A env)) : Derives Γ (specification4 w z env) := by
  apply Derives.exI A
  simpa only [specification4, Formula.instantiate, Formula.rename, successor_rename, atBound4_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using Derives.conjI hA hs

def bundle6 {m} (w : Fin m) (env : Fin 6 → Fin m) : Formula m :=
  (PureSyntaxExprQuery.query leftTerm6 w env).conj ((PureSyntaxExprQuery.query rightTerm6 w env).conj ((PureSyntaxExprQuery.query formula6 w env).conj ((OriginalTransformExprQuery.query leftTransform6 w env).conj (OriginalTransformExprQuery.query rightTransform6 w env))))

def atBound6 {m} (w z A : Fin m) (env : Fin 6 → Fin m) : Formula m :=
  (SyntaxTermSyntax.term w z (env 0) (env 1)).conj ((SyntaxTermSyntax.term w z (env 0) (env 2)).conj ((FormulaCodeSyntax.formulaCode w (env 3) A (env 0)).conj ((SyntaxTopFormulaSyntax.instantiated w z (env 0) A (env 1) (env 3) (env 4)).conj (SyntaxTopFormulaSyntax.instantiated w z (env 0) A (env 2) (env 3) (env 5)))))

def specification6 {m} (w z : Fin m) (env : Fin 6 → Fin m) : Formula m := .ex
  ((successor (Fin.last m) z.castSucc).conj (atBound6 w.castSucc z.castSucc (Fin.last m) (fun i => (env i).castSucc)))

theorem bundle6_rename {m l} (w : Fin m) (env : Fin 6 → Fin m) (ρ : Fin m → Fin l) :
    (bundle6 w env).rename ρ = bundle6 (ρ w) (fun i => ρ (env i)) := by
  simp only [bundle6, Formula.rename, PureSyntaxExprQuery.query_rename, OriginalTransformExprQuery.query_rename]

theorem atBound6_rename {m l} (w z A : Fin m) (env : Fin 6 → Fin m) (ρ : Fin m → Fin l) :
    (atBound6 w z A env).rename ρ = atBound6 (ρ w) (ρ z) (ρ A) (fun i => ρ (env i)) := by
  simp only [atBound6, Formula.rename, SyntaxTermSyntax.term_rename, FormulaCodeSyntax.formulaCode_rename, SyntaxTopFormulaSyntax.instantiated_rename]

theorem specification6_rename {m l} (w z : Fin m) (env : Fin 6 → Fin m) (ρ : Fin m → Fin l) :
    (specification6 w z env).rename ρ = specification6 (ρ w) (ρ z) (fun i => ρ (env i)) := by
  simp only [specification6, Formula.rename, successor_rename, atBound6_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem intro_specification6 {m} {Γ : Context m} (w z A : Fin m) (env : Fin 6 → Fin m)
    (hA : Derives Γ (successor A z)) (hs : Derives Γ (atBound6 w z A env)) : Derives Γ (specification6 w z env) := by
  apply Derives.exI A
  simpa only [specification6, Formula.instantiate, Formula.rename, successor_rename, atBound6_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using Derives.conjI hA hs

end PPAC.Migration.Internal.LogicalInstantiateSyntax
