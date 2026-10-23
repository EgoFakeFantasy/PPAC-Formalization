import PPAC.Migration.Internal.PureSyntaxRules
import PPAC.Migration.Internal.OriginalHeadDisjoint

/-! 纯语法原Horn行及任意内部轨迹条件；定义不引用Term／TermList／FormulaCode类型结论。 -/
namespace PPAC.Migration.Internal.PureSyntaxTrace
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxRenameQuerySyntax

def four {α : Type} (a b c d : α) : Fin 4 → α := Fin.cases a (Fin.cases b (Fin.cases c (Fin.cases d Fin.elim0)))

theorem four_map {α β : Type} (a b c d : α) (f : α → β) : (fun i => f (four a b c d i)) = four (f a) (f b) (f c) (f d) := by
  funext i
  exact Fin.cases rfl (fun j => Fin.cases rfl (fun k => Fin.cases rfl (fun l => Fin.cases rfl (fun z => Fin.elim0 z) l) k) j) i

def termRow {m} (w b f n r : Fin m) : Formula m := SyntaxNodeSyntax.constructor 3 0 w (SyntaxAtomSyntax.three b f n) r

def argumentRow {m} (w b f k n r : Fin m) : Formula m := SyntaxNodeSyntax.constructor 4 1 w (four b f k n) r

def formulaRow {m} (w b f n r : Fin m) : Formula m := SyntaxNodeSyntax.constructor 3 4 w (SyntaxAtomSyntax.three b f n) r

def closed {m} (w R : Fin m) : Formula m := .all
  ((Formula.mem (Fin.last m) R.castSucc).imp (HornStepSyntax.step PureSyntaxRules.rules w.castSucc (Fin.last m) R.castSucc))

def witness {m} (w r R : Fin m) : Formula m := (RestrictionSyntax.subset R w).conj ((Formula.mem r R).conj (closed w R))

def condition {m} (w r : Fin m) : Formula m := .ex (witness w.castSucc r.castSucc (Fin.last m))

def term {m} (w b f n : Fin m) : Formula m := .ex
  ((termRow w.castSucc b.castSucc f.castSucc n.castSucc (Fin.last m)).conj (condition w.castSucc (Fin.last m)))

def arguments {m} (w b f k n : Fin m) : Formula m := .ex
  ((argumentRow w.castSucc b.castSucc f.castSucc k.castSucc n.castSucc (Fin.last m)).conj (condition w.castSucc (Fin.last m)))

def formula {m} (w b f n : Fin m) : Formula m := .ex
  ((formulaRow w.castSucc b.castSucc f.castSucc n.castSucc (Fin.last m)).conj (condition w.castSucc (Fin.last m)))

theorem termRow_rename {m l} (w b f n r : Fin m) (ρ : Fin m → Fin l) :
    (termRow w b f n r).rename ρ = termRow (ρ w) (ρ b) (ρ f) (ρ n) (ρ r) := by
  simp only [termRow, SyntaxNodeSyntax.constructor_rename, SyntaxAtomSyntax.three_map]

theorem argumentRow_rename {m l} (w b f k n r : Fin m) (ρ : Fin m → Fin l) :
    (argumentRow w b f k n r).rename ρ = argumentRow (ρ w) (ρ b) (ρ f) (ρ k) (ρ n) (ρ r) := by
  simp only [argumentRow, SyntaxNodeSyntax.constructor_rename, four_map]

theorem formulaRow_rename {m l} (w b f n r : Fin m) (ρ : Fin m → Fin l) :
    (formulaRow w b f n r).rename ρ = formulaRow (ρ w) (ρ b) (ρ f) (ρ n) (ρ r) := by
  simp only [formulaRow, SyntaxNodeSyntax.constructor_rename, SyntaxAtomSyntax.three_map]

theorem closed_rename {m l} (w R : Fin m) (ρ : Fin m → Fin l) :
    (closed w R).rename ρ = closed (ρ w) (ρ R) := by
  simp only [closed, Formula.rename, HornStepSyntax.step_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem witness_rename {m l} (w r R : Fin m) (ρ : Fin m → Fin l) :
    (witness w r R).rename ρ = witness (ρ w) (ρ r) (ρ R) := by
  simp only [witness, Formula.rename, RestrictionSyntax.subset_rename, closed_rename]

theorem condition_rename {m l} (w r : Fin m) (ρ : Fin m → Fin l) :
    (condition w r).rename ρ = condition (ρ w) (ρ r) := by
  simp only [condition, Formula.rename, witness_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem term_rename {m l} (w b f n : Fin m) (ρ : Fin m → Fin l) :
    (term w b f n).rename ρ = term (ρ w) (ρ b) (ρ f) (ρ n) := by
  simp only [term, Formula.rename, termRow_rename, condition_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem arguments_rename {m l} (w b f k n : Fin m) (ρ : Fin m → Fin l) :
    (arguments w b f k n).rename ρ = arguments (ρ w) (ρ b) (ρ f) (ρ k) (ρ n) := by
  simp only [arguments, Formula.rename, argumentRow_rename, condition_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem formula_rename {m l} (w b f n : Fin m) (ρ : Fin m → Fin l) :
    (formula w b f n).rename ρ = formula (ρ w) (ρ b) (ρ f) (ρ n) := by
  simp only [formula, Formula.rename, formulaRow_rename, condition_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem closed_at {m} {Γ : Context m} (w R r : Fin m) (hc : Derives Γ (closed w R)) (hr : Derives Γ (.mem r R)) :
    Derives Γ (HornStepSyntax.step PureSyntaxRules.rules w r R) := by
  have ht : Derives Γ ((Formula.mem r R).imp (HornStepSyntax.step PureSyntaxRules.rules w r R)) := of_eq
    (by simp only [Formula.instantiate, Formula.rename, HornStepSyntax.step_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (Derives.allE r hc)
  exact .impE ht hr

theorem intro_condition {m} {Γ : Context m} (w r R : Fin m) (hw : Derives Γ (witness w r R)) : Derives Γ (condition w r) := by
  apply Derives.exI R
  exact of_eq (by simp only [Formula.instantiate, witness_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hw

theorem intro_term {m} {Γ : Context m} (w b f n r : Fin m)
    (hr : Derives Γ (termRow w b f n r)) (hc : Derives Γ (condition w r)) : Derives Γ (term w b f n) := by
  apply Derives.exI r
  exact of_eq (by simp only [Formula.instantiate, Formula.rename, termRow_rename, condition_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI hr hc)

end PPAC.Migration.Internal.PureSyntaxTrace
