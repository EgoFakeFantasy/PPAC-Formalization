import PPAC.Migration.Internal.OriginalLookupExpr

/-! 直接使用上游ObjectHorn.Rule的头、守卫和前提，消去函数符号的关系式局部矩阵。 -/
namespace PPAC.Migration.Internal.HornRuleSyntax
open Source SourceAlgebra SourceLogic
open HornExprSyntax
open SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC.Automation.ObjectHorn (Expr Rule)

def truth {m} : Formula m := .imp .bot .bot

def premise {m n} (e : Expr n) (w trace : Fin m) (env : Fin n → Fin m) : Formula m := .ex
  ((graph e w.castSucc (fun i => (env i).castSucc) (Fin.last m)).conj (.mem (Fin.last m) trace.castSucc))

def guard {m n} (e f : Expr n) (w : Fin m) (env : Fin n → Fin m) : Formula m := .ex (.ex
  ((graph e w.castSucc.castSucc (fun i => (env i).castSucc.castSucc) (Fin.last m).castSucc).conj
    ((graph f w.castSucc.castSucc (fun i => (env i).castSucc.castSucc) (Fin.last (m+1))).conj
      (.mem (Fin.last m).castSucc (Fin.last (m+1))))))

def premises {m n} : List (Expr n) → Fin m → Fin m → (Fin n → Fin m) → Formula m
  | .nil, _, _, _ => truth
  | e :: es, w, trace, env => (premise e w trace env).conj (premises es w trace env)

def guards {m n} : List (Expr n × Expr n) → Fin m → (Fin n → Fin m) → Formula m
  | .nil, _, _ => truth
  | (e,f) :: es, w, env => (guard e f w env).conj (guards es w env)

def matrix {m} (rule : Rule) (w row trace : Fin m) (env : Fin rule.arity → Fin m) : Formula m :=
  (graph rule.head w env row).conj ((guards rule.guards w env).conj (premises rule.premises w trace env))

theorem truth_proved {m} {Γ : Context m} : Derives Γ (truth : Formula m) := .impI (.hyp (Or.inl rfl))

theorem premise_rename {m k n} (e : Expr n) (w trace : Fin m) (env : Fin n → Fin m) (ρ : Fin m → Fin k) :
    (premise e w trace env).rename ρ = premise e (ρ w) (ρ trace) (fun i => ρ (env i)) := by
  simp only [premise, Formula.rename, graph_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem guard_rename {m k n} (e f : Expr n) (w : Fin m) (env : Fin n → Fin m) (ρ : Fin m → Fin k) :
    (guard e f w env).rename ρ = guard e f (ρ w) (fun i => ρ (env i)) := by
  simp only [guard, Formula.rename, graph_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem premises_rename {m k n} (es : List (Expr n)) (w trace : Fin m) (env : Fin n → Fin m) (ρ : Fin m → Fin k) :
    (premises es w trace env).rename ρ = premises es (ρ w) (ρ trace) (fun i => ρ (env i)) := by
  induction es with
  | nil => rfl
  | cons e es ih => simp only [premises, Formula.rename, premise_rename, ih]

theorem guards_rename {m k n} (es : List (Expr n × Expr n)) (w : Fin m) (env : Fin n → Fin m) (ρ : Fin m → Fin k) :
    (guards es w env).rename ρ = guards es (ρ w) (fun i => ρ (env i)) := by
  induction es with
  | nil => rfl
  | cons e es ih => simp only [guards, Formula.rename, guard_rename, ih]

theorem matrix_rename {m k} (rule : Rule) (w row trace : Fin m) (env : Fin rule.arity → Fin m) (ρ : Fin m → Fin k) :
    (matrix rule w row trace env).rename ρ = matrix rule (ρ w) (ρ row) (ρ trace) (fun i => ρ (env i)) := by
  simp only [matrix, Formula.rename, graph_rename, guards_rename, premises_rename]

end PPAC.Migration.Internal.HornRuleSyntax
