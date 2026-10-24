import PPAC.Migration.Internal.ObjectPacketAffineApplication

/-! The actual rule table is an explicit parameter of the relational closed-trace interface. -/
namespace PPAC.Migration.Internal.HornClosedTraceSyntax
open Source SourceAlgebra SourceLogic HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC.Automation.ObjectHorn (Rule)

def closed {m} (rules : List Rule) (w R : Fin m) : Formula m := .all
  ((Formula.mem (Fin.last m) R.castSucc).imp (HornStepSyntax.step rules w.castSucc (Fin.last m) R.castSucc))

def witness {m} (rules : List Rule) (w r R : Fin m) : Formula m :=
  (RestrictionSyntax.subset R w).conj ((Formula.mem r R).conj (closed rules w R))

def condition {m} (rules : List Rule) (w r : Fin m) : Formula m := .ex (witness rules w.castSucc r.castSucc (Fin.last m))

theorem closed_rename {m j} (rules : List Rule) (w R : Fin m) (ρ : Fin m → Fin j) :
    (closed rules w R).rename ρ = closed rules (ρ w) (ρ R) := by
  simp only [closed, Formula.rename, HornStepSyntax.step_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem witness_rename {m j} (rules : List Rule) (w r R : Fin m) (ρ : Fin m → Fin j) :
    (witness rules w r R).rename ρ = witness rules (ρ w) (ρ r) (ρ R) := by
  simp only [witness, Formula.rename, RestrictionSyntax.subset_rename, closed_rename]

theorem condition_rename {m j} (rules : List Rule) (w r : Fin m) (ρ : Fin m → Fin j) :
    (condition rules w r).rename ρ = condition rules (ρ w) (ρ r) := by
  simp only [condition, Formula.rename, witness_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem closed_at {m} {Γ : Context m} (rules : List Rule) (w R r : Fin m)
    (hc : Derives Γ (closed rules w R)) (hr : Derives Γ (.mem r R)) : Derives Γ (HornStepSyntax.step rules w r R) := by
  have hi : Derives Γ ((Formula.mem r R).imp (HornStepSyntax.step rules w r R)) :=
    of_eq (by simp only [Formula.instantiate, Formula.rename, HornStepSyntax.step_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (Derives.allE r hc)
  exact .impE hi hr

theorem intro_condition {m} {Γ : Context m} (rules : List Rule) (w r R : Fin m)
    (hw : Derives Γ (witness rules w r R)) : Derives Γ (condition rules w r) := by
  apply Derives.exI R
  exact of_eq (by simp only [Formula.instantiate, witness_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hw

theorem step_row_subst {m} {Γ : Context m} (rules : List Rule) (w r s R : Fin m)
    (he : Derives Γ (.equal r s)) (hr : Derives Γ (HornStepSyntax.step rules w r R)) : Derives Γ (HornStepSyntax.step rules w s R) := by
  let P := HornStepSyntax.step rules w.castSucc (Fin.last m) R.castSucc
  have h0 : P.instantiate r = HornStepSyntax.step rules w r R := by
    simp only [P, Formula.instantiate, HornStepSyntax.step_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have h1 : P.instantiate s = HornStepSyntax.step rules w s R := by
    simp only [P, Formula.instantiate, HornStepSyntax.step_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact of_eq h1 (Derives.eqSubst P he (of_eq h0.symm hr))

end PPAC.Migration.Internal.HornClosedTraceSyntax
