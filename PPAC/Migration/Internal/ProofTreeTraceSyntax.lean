import PPAC.Migration.Internal.ProofTreeRowLocalSyntax

/-! 原十二分支的带局部测试闭轨迹；全部轨迹为对象ω子集，不假设外部有限或标准ω。 -/
namespace PPAC.Migration.Internal.ProofTreeTraceSyntax
open Source SourceAlgebra SourceLogic HornExprSyntax
open SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC.Automation

def step {m} (test : Formula 1) (w r R : Fin m) : Formula m :=
  (HornStepSyntax.step ObjectProofTree.rules w r R).conj (ProofTreeRowLocalSyntax.localCondition test w r)

def closed {m} (test : Formula 1) (w R : Fin m) : Formula m := .all
  ((Formula.mem (Fin.last m) R.castSucc).imp (step test w.castSucc (Fin.last m) R.castSucc))

def witness {m} (test : Formula 1) (w r R : Fin m) : Formula m :=
  (RestrictionSyntax.subset R w).conj ((Formula.mem r R).conj (closed test w R))

def condition {m} (test : Formula 1) (w r : Fin m) : Formula m := .ex (witness test w.castSucc r.castSucc (Fin.last m))

theorem original_rules_count : ObjectProofTree.rules.length = 12 := rfl

theorem payload_arities : ObjectProofTree.shapes.map (fun shape => shape.extra+2) = [3,3,4,3,3,5] := rfl

theorem child_positions : ObjectProofTree.shapes.map (fun shape => shape.children.map Fin.val) = (List.cons List.nil (List.cons List.nil (List.cons (List.cons 2 (List.cons 3 List.nil)) (List.cons (List.cons 2 List.nil) (List.cons (List.cons 2 List.nil) (List.cons (List.cons 4 List.nil) List.nil)))))) := rfl

theorem step_rename {m l} (test : Formula 1) (w r R : Fin m) (ρ : Fin m → Fin l) :
    (step test w r R).rename ρ = step test (ρ w) (ρ r) (ρ R) := by
  simp only [step, Formula.rename, HornStepSyntax.step_rename, ProofTreeRowLocalSyntax.localCondition_rename]

theorem closed_rename {m l} (test : Formula 1) (w R : Fin m) (ρ : Fin m → Fin l) :
    (closed test w R).rename ρ = closed test (ρ w) (ρ R) := by
  simp only [closed, Formula.rename, step_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem witness_rename {m l} (test : Formula 1) (w r R : Fin m) (ρ : Fin m → Fin l) :
    (witness test w r R).rename ρ = witness test (ρ w) (ρ r) (ρ R) := by
  simp only [witness, Formula.rename, RestrictionSyntax.subset_rename, closed_rename]

theorem condition_rename {m l} (test : Formula 1) (w r : Fin m) (ρ : Fin m → Fin l) :
    (condition test w r).rename ρ = condition test (ρ w) (ρ r) := by
  simp only [condition, Formula.rename, witness_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem closed_at {m} {Γ : Context m} (test : Formula 1) (w R r : Fin m) (hc : Derives Γ (closed test w R)) (hm : Derives Γ (.mem r R)) :
    Derives Γ (step test w r R) := by
  have hh : Derives Γ ((Formula.mem r R).imp (step test w r R)) := of_eq
    (by simp only [Formula.instantiate, Formula.rename, step_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (Derives.allE r hc)
  exact .impE hh hm

theorem intro_condition {m} {Γ : Context m} (test : Formula 1) (w r R : Fin m) (hv : Derives Γ (witness test w r R)) : Derives Γ (condition test w r) := by
  apply Derives.exI R
  exact of_eq (by simp only [Formula.instantiate, witness_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hv

end PPAC.Migration.Internal.ProofTreeTraceSyntax
