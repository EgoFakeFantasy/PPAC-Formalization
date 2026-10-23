import PPAC.Migration.Internal.ObjectUniformOperationFrames

/-! 原量词深度后继子运行的纯对象存在块；后继见证由内部omega归纳闭包提供。 -/
namespace PPAC.Migration.Internal.OriginalBinderStepSyntax
open Source SourceAlgebra SourceLogic OmegaSyntax
open SyntaxRenameQuerySyntax (of_eq)

def body {m} (w mode depth parameter x X : Fin m) : Formula (m+1) :=
  (successor (Fin.last m) depth.castSucc).conj
    (OriginalTransformRowSyntax.run 3 w.castSucc mode.castSucc (Fin.last m) parameter.castSucc x.castSucc X.castSucc)

def step {m} (w mode depth parameter x X : Fin m) : Formula m := .ex (body w mode depth parameter x X)

theorem step_rename {m j} (w mode depth parameter x X : Fin m) (ρ : Fin m → Fin j) :
    (step w mode depth parameter x X).rename ρ = step (ρ w) (ρ mode) (ρ depth) (ρ parameter) (ρ x) (ρ X) := by
  simp only [step, body, Formula.rename, successor_rename, OriginalTransformRowSyntax.run_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem intro_step {m} {Γ : Context m} (w mode depth parameter x X D : Fin m)
    (hs : Derives Γ (successor D depth)) (hr : Derives Γ (OriginalTransformRowSyntax.run 3 w mode D parameter x X)) :
    Derives Γ (step w mode depth parameter x X) := by
  apply Derives.exI D
  exact of_eq (by simp only [body, Formula.instantiate, Formula.rename, successor_rename, OriginalTransformRowSyntax.run_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI hs hr)

theorem successor_exists {m} {Γ : Context m} (w x : Fin m)
    (hw : Derives Γ (omega w)) (hx : Derives Γ (.mem x w)) : Derives Γ (stepIn w x) := by
  have he : Derives Γ ((Formula.mem x w).imp (stepIn w x)) :=
    of_eq (by simp only [Formula.instantiate, Formula.rename, stepIn_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (Derives.allE x (.conjR (.conjL hw)))
  exact .impE he hx

end PPAC.Migration.Internal.OriginalBinderStepSyntax
