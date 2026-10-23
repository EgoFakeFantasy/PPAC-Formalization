import PPAC.Migration.Internal.HornBinderRules

/-! 原有限Rule的实际有界赋值存在块，直接量化全部原arity个内部值。 -/
namespace PPAC.Migration.Internal.HornApplicationSyntax
open Source SourceAlgebra SourceLogic HornBinderSyntax HornExprSyntax HornExprBounds HornRuleSyntax
open YesMetaZFC.Automation.ObjectHorn (Rule)

def boundedMatrix {m} (rule : Rule) (w row trace : Fin m) (env : Fin rule.arity → Fin m) : Formula m :=
  (environmentNat rule.arity w env).conj ((environmentBound rule.arity row env).conj (matrix rule w row trace env))

def body {m} (rule : Rule) (w row trace : Fin m) : Formula (m+rule.arity) :=
  boundedMatrix rule (old rule.arity w) (old rule.arity row) (old rule.arity trace) (slot rule.arity)

def application {m} (rule : Rule) (w row trace : Fin m) : Formula m := existsMany rule.arity (body rule w row trace)

theorem boundedMatrix_rename {m k} (rule : Rule) (w row trace : Fin m) (env : Fin rule.arity → Fin m) (ρ : Fin m → Fin k) :
    (boundedMatrix rule w row trace env).rename ρ = boundedMatrix rule (ρ w) (ρ row) (ρ trace) (fun i => ρ (env i)) := by
  simp only [boundedMatrix, Formula.rename, environmentNat_rename, environmentBound_rename, matrix_rename]

theorem body_lift {m k} (rule : Rule) (w row trace : Fin m) (ρ : Fin m → Fin k) :
    (body rule w row trace).rename (lift rule.arity ρ) = body rule (ρ w) (ρ row) (ρ trace) := by
  simp only [body, boundedMatrix_rename, lift_old, lift_slot]

theorem body_assign {m} (rule : Rule) (w row trace : Fin m) (env : Fin rule.arity → Fin m) :
    (body rule w row trace).rename (assign rule.arity env) = boundedMatrix rule w row trace env := by
  simp only [body, boundedMatrix_rename, assign_old, assign_slot]

theorem application_rename {m k} (rule : Rule) (w row trace : Fin m) (ρ : Fin m → Fin k) :
    (application rule w row trace).rename ρ = application rule (ρ w) (ρ row) (ρ trace) := by
  simp only [application, existsMany_rename, body_lift]

end PPAC.Migration.Internal.HornApplicationSyntax
