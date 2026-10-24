import PPAC.Migration.Internal.ProjectCompilerCodeProperties

/-! Actual parent graph, state, value edge, and local program witnesses for any produced output. -/
namespace PPAC.Migration.Internal.ProjectCompilerRootSyntax
open Source SourceAlgebra SourceLogic HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)

def matrix {m} (w n b q : Fin m) (e : Fin 4 → Fin m) : Formula m :=
  (ProjectCompilerCodeSyntax.carrier w (e 0) (e 1)).conj
    ((ProjectCompilerEvaluationSyntax.evaluation w (e 1) n (e 2)).conj
      ((GraphSyntax.edge (e 2) b q).conj
        ((ProjectCompilerRecursionSyntax.graph w (e 1) (e 3) n).conj
          ((ProjectCompilerStateSyntax.state w (e 1) n (e 3) (e 2)).conj
            (ProjectCompilerLocalSyntax.localStep w b q (e 3) n)))))

def body {m} (w n b q : Fin m) : Formula (m+4) := matrix (old 4 w) (old 4 n) (old 4 b) (old 4 q) (slot 4)

def certificate {m} (w n b q : Fin m) : Formula m := existsMany 4 (body w n b q)

def environment {m} (a c v h : Fin m) (i : Fin 4) : Fin m :=
  match i.val with | 0 => a | 1 => c | 2 => v | _ => h

theorem matrix_rename {m l} (w n b q : Fin m) (e : Fin 4 → Fin m) (ρ : Fin m → Fin l) :
    (matrix w n b q e).rename ρ = matrix (ρ w) (ρ n) (ρ b) (ρ q) (fun i => ρ (e i)) := by
  simp only [matrix, Formula.rename, ProjectCompilerCodeSyntax.carrier_rename, ProjectCompilerEvaluationSyntax.evaluation_rename,
    GraphSyntax.edge_rename, ProjectCompilerRecursionSyntax.graph_rename, ProjectCompilerStateSyntax.state_rename,
    ProjectCompilerLocalSyntax.localStep_rename]

theorem body_lift {m l} (w n b q : Fin m) (ρ : Fin m → Fin l) :
    (body w n b q).rename (lift 4 ρ) = body (ρ w) (ρ n) (ρ b) (ρ q) := by
  simp only [body, matrix_rename, lift_old, lift_slot]

theorem certificate_rename {m l} (w n b q : Fin m) (ρ : Fin m → Fin l) :
    (certificate w n b q).rename ρ = certificate (ρ w) (ρ n) (ρ b) (ρ q) := by
  simp only [certificate, existsMany_rename, body_lift]

theorem assemble {m} {Γ : Context m} (w n b q a c v h : Fin m)
    (hc : Derives Γ (ProjectCompilerCodeSyntax.carrier w a c))
    (hv : Derives Γ (ProjectCompilerEvaluationSyntax.evaluation w c n v)) (he : Derives Γ (GraphSyntax.edge v b q))
    (hg : Derives Γ (ProjectCompilerRecursionSyntax.graph w c h n)) (hs : Derives Γ (ProjectCompilerStateSyntax.state w c n h v))
    (hl : Derives Γ (ProjectCompilerLocalSyntax.localStep w b q h n)) : Derives Γ (certificate w n b q) := by
  have hm : Derives Γ (matrix w n b q (environment a c v h)) := .conjI hc (.conjI hv (.conjI he (.conjI hg (.conjI hs hl))))
  apply HornBinderRules.intro_many 4 (body w n b q) (environment a c v h)
  exact of_eq (by simp only [body, matrix_rename, assign_old, assign_slot]) hm

end PPAC.Migration.Internal.ProjectCompilerRootSyntax
