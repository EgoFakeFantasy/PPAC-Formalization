import PPAC.Migration.Internal.LogicalAbstractQueries

/-! 原21／24准确查询、实际类型／AbstractFreeTop规格及两层对象后继EX。 -/
namespace PPAC.Migration.Internal.LogicalAbstractSyntax
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax
open SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC.Automation
open YesMetaZFC.Automation.ObjectHorn (Expr)

def leftFormula21 : Expr 5 := (ObjectLogicalAxiom.rule21.queries[0]).2

theorem actual_leftFormula21 : leftFormula21 = LogicalAbstractQueries.formulaQuery 0 1 := rfl

def rightFormula21 : Expr 5 := (ObjectLogicalAxiom.rule21.queries[1]).2

theorem actual_rightFormula21 : rightFormula21 = LogicalAbstractQueries.formulaQuery 0 2 := rfl

def leftTransform21 : Expr 5 := (ObjectLogicalAxiom.rule21.queries[2]).2

theorem actual_leftTransform21 : leftTransform21 = LogicalAbstractQueries.transformQuery 1 3 := rfl

def rightTransform21 : Expr 5 := (ObjectLogicalAxiom.rule21.queries[3]).2

theorem actual_rightTransform21 : rightTransform21 = LogicalAbstractQueries.transformQuery 2 4 := rfl

theorem actual_arity21 : ObjectLogicalAxiom.rule21.arity = 5 := rfl

theorem actual_queries21 : ObjectLogicalAxiom.rule21.queries = [(false, leftFormula21), (false, rightFormula21), (true, leftTransform21), (true, rightTransform21)] := rfl

def bundle21 {m} (w : Fin m) (env : Fin 5 → Fin m) : Formula m :=
  (PureSyntaxExprQuery.query leftFormula21 w env).conj ((PureSyntaxExprQuery.query rightFormula21 w env).conj ((OriginalTransformExprQuery.query leftTransform21 w env).conj ((OriginalTransformExprQuery.query rightTransform21 w env))))

def atSuccessor21 {m} (w z A B : Fin m) (env : Fin 5 → Fin m) : Formula m :=
  (FormulaCodeSyntax.formulaCode w (env 1) z B).conj ((FormulaCodeSyntax.formulaCode w (env 2) z B).conj ((SyntaxTopFormulaSyntax.abstracted w z (env 0) A B (env 1) (env 3)).conj ((SyntaxTopFormulaSyntax.abstracted w z (env 0) A B (env 2) (env 4)))))

def atOneSpecification21 {m} (w z A : Fin m) (env : Fin 5 → Fin m) : Formula m := .ex
  ((successor (Fin.last m) (env 0).castSucc).conj (atSuccessor21 w.castSucc z.castSucc A.castSucc (Fin.last m) (fun i => (env i).castSucc)))

def specification21 {m} (w z : Fin m) (env : Fin 5 → Fin m) : Formula m := .ex
  ((successor (Fin.last m) z.castSucc).conj (atOneSpecification21 w.castSucc z.castSucc (Fin.last m) (fun i => (env i).castSucc)))

theorem bundle21_rename {m l} (w : Fin m) (env : Fin 5 → Fin m) (ρ : Fin m → Fin l) :
    (bundle21 w env).rename ρ = bundle21 (ρ w) (fun i => ρ (env i)) := by
  simp only [bundle21, Formula.rename, PureSyntaxExprQuery.query_rename, OriginalTransformExprQuery.query_rename]

theorem atSuccessor21_rename {m l} (w z A B : Fin m) (env : Fin 5 → Fin m) (ρ : Fin m → Fin l) :
    (atSuccessor21 w z A B env).rename ρ = atSuccessor21 (ρ w) (ρ z) (ρ A) (ρ B) (fun i => ρ (env i)) := by
  simp only [atSuccessor21, Formula.rename, FormulaCodeSyntax.formulaCode_rename, SyntaxTopFormulaSyntax.abstracted_rename]

theorem atOneSpecification21_rename {m l} (w z A : Fin m) (env : Fin 5 → Fin m) (ρ : Fin m → Fin l) :
    (atOneSpecification21 w z A env).rename ρ = atOneSpecification21 (ρ w) (ρ z) (ρ A) (fun i => ρ (env i)) := by
  simp only [atOneSpecification21, Formula.rename, successor_rename, atSuccessor21_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem specification21_rename {m l} (w z : Fin m) (env : Fin 5 → Fin m) (ρ : Fin m → Fin l) :
    (specification21 w z env).rename ρ = specification21 (ρ w) (ρ z) (fun i => ρ (env i)) := by
  simp only [specification21, Formula.rename, successor_rename, atOneSpecification21_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem intro_atOneSpecification21 {m} {Γ : Context m} (w z A B : Fin m) (env : Fin 5 → Fin m)
    (hs : Derives Γ (successor B (env 0))) (ha : Derives Γ (atSuccessor21 w z A B env)) : Derives Γ (atOneSpecification21 w z A env) := by
  apply Derives.exI B
  simpa only [atOneSpecification21, Formula.instantiate, Formula.rename, successor_rename, atSuccessor21_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using Derives.conjI hs ha

theorem intro_specification21 {m} {Γ : Context m} (w z A : Fin m) (env : Fin 5 → Fin m)
    (hs : Derives Γ (successor A z)) (ha : Derives Γ (atOneSpecification21 w z A env)) : Derives Γ (specification21 w z env) := by
  apply Derives.exI A
  simpa only [specification21, Formula.instantiate, Formula.rename, successor_rename, atOneSpecification21_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using Derives.conjI hs ha

def leftFormula24 : Expr 4 := (ObjectLogicalAxiom.rule24.queries[0]).2

theorem actual_leftFormula24 : leftFormula24 = LogicalAbstractQueries.formulaQuery 0 1 := rfl

def rightFormula24 : Expr 4 := (ObjectLogicalAxiom.rule24.queries[1]).2

theorem actual_rightFormula24 : rightFormula24 = LogicalStaticQueries.query false 0 2 := rfl

def leftTransform24 : Expr 4 := (ObjectLogicalAxiom.rule24.queries[2]).2

theorem actual_leftTransform24 : leftTransform24 = LogicalAbstractQueries.transformQuery 1 3 := rfl

theorem actual_arity24 : ObjectLogicalAxiom.rule24.arity = 4 := rfl

theorem actual_queries24 : ObjectLogicalAxiom.rule24.queries = [(false, leftFormula24), (false, rightFormula24), (true, leftTransform24)] := rfl

def bundle24 {m} (w : Fin m) (env : Fin 4 → Fin m) : Formula m :=
  (PureSyntaxExprQuery.query leftFormula24 w env).conj ((PureSyntaxExprQuery.query rightFormula24 w env).conj ((OriginalTransformExprQuery.query leftTransform24 w env)))

def atSuccessor24 {m} (w z A B : Fin m) (env : Fin 4 → Fin m) : Formula m :=
  (FormulaCodeSyntax.formulaCode w (env 1) z B).conj ((FormulaCodeSyntax.formulaCode w (env 2) z (env 0)).conj ((SyntaxTopFormulaSyntax.abstracted w z (env 0) A B (env 1) (env 3))))

def atOneSpecification24 {m} (w z A : Fin m) (env : Fin 4 → Fin m) : Formula m := .ex
  ((successor (Fin.last m) (env 0).castSucc).conj (atSuccessor24 w.castSucc z.castSucc A.castSucc (Fin.last m) (fun i => (env i).castSucc)))

def specification24 {m} (w z : Fin m) (env : Fin 4 → Fin m) : Formula m := .ex
  ((successor (Fin.last m) z.castSucc).conj (atOneSpecification24 w.castSucc z.castSucc (Fin.last m) (fun i => (env i).castSucc)))

theorem bundle24_rename {m l} (w : Fin m) (env : Fin 4 → Fin m) (ρ : Fin m → Fin l) :
    (bundle24 w env).rename ρ = bundle24 (ρ w) (fun i => ρ (env i)) := by
  simp only [bundle24, Formula.rename, PureSyntaxExprQuery.query_rename, OriginalTransformExprQuery.query_rename]

theorem atSuccessor24_rename {m l} (w z A B : Fin m) (env : Fin 4 → Fin m) (ρ : Fin m → Fin l) :
    (atSuccessor24 w z A B env).rename ρ = atSuccessor24 (ρ w) (ρ z) (ρ A) (ρ B) (fun i => ρ (env i)) := by
  simp only [atSuccessor24, Formula.rename, FormulaCodeSyntax.formulaCode_rename, SyntaxTopFormulaSyntax.abstracted_rename]

theorem atOneSpecification24_rename {m l} (w z A : Fin m) (env : Fin 4 → Fin m) (ρ : Fin m → Fin l) :
    (atOneSpecification24 w z A env).rename ρ = atOneSpecification24 (ρ w) (ρ z) (ρ A) (fun i => ρ (env i)) := by
  simp only [atOneSpecification24, Formula.rename, successor_rename, atSuccessor24_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem specification24_rename {m l} (w z : Fin m) (env : Fin 4 → Fin m) (ρ : Fin m → Fin l) :
    (specification24 w z env).rename ρ = specification24 (ρ w) (ρ z) (fun i => ρ (env i)) := by
  simp only [specification24, Formula.rename, successor_rename, atOneSpecification24_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem intro_atOneSpecification24 {m} {Γ : Context m} (w z A B : Fin m) (env : Fin 4 → Fin m)
    (hs : Derives Γ (successor B (env 0))) (ha : Derives Γ (atSuccessor24 w z A B env)) : Derives Γ (atOneSpecification24 w z A env) := by
  apply Derives.exI B
  simpa only [atOneSpecification24, Formula.instantiate, Formula.rename, successor_rename, atSuccessor24_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using Derives.conjI hs ha

theorem intro_specification24 {m} {Γ : Context m} (w z A : Fin m) (env : Fin 4 → Fin m)
    (hs : Derives Γ (successor A z)) (ha : Derives Γ (atOneSpecification24 w z A env)) : Derives Γ (specification24 w z env) := by
  apply Derives.exI A
  simpa only [specification24, Formula.instantiate, Formula.rename, successor_rename, atOneSpecification24_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using Derives.conjI hs ha

end PPAC.Migration.Internal.LogicalAbstractSyntax
