import PPAC.Migration.Internal.ProjectCompilerCaseSyntax

/-! Actual compiler local step: the second state coordinate is an output code, not a free-variable scope. -/
namespace PPAC.Migration.Internal.ProjectCompilerLocalSyntax
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)

def readMatrix : Formula (1+3) := SyntaxContextReadSyntax.read (0 : Fin 1).castSucc.castSucc.castSucc
  (Fin.last 1).castSucc.castSucc (Fin.last 2).castSucc (Fin.last 3)

def one {m} (h : Fin m) : Fin 1 → Fin m := fun _ => h

def casesAt {m} (w b q h n z : Fin m) : Formula m :=
  ProjectCompilerCaseSyntax.cases readMatrix (one h) w b z n q

def localBody {m} (w b q h n : Fin m) : Formula (m+1) :=
  (empty (Fin.last m)).conj (casesAt w.castSucc b.castSucc q.castSucc h.castSucc n.castSucc (Fin.last m))

def localStep {m} (w b q h n : Fin m) : Formula m :=
  (Formula.mem n w).conj ((SyntaxTermSyntax.contexts w b q).conj (.ex (localBody w b q h n)))

theorem readMatrix_at {m} (ρ : Fin 1 → Fin m) (x b q : Fin m) :
    ProjectCompilerCaseSyntax.relation readMatrix ρ x b q = SyntaxContextReadSyntax.read (ρ 0) x b q := by
  simp only [ProjectCompilerCaseSyntax.relation, readMatrix, SyntaxContextReadSyntax.read_rename,
    Fin.lastCases_last, Fin.lastCases_castSucc]

theorem one_map {m l} (h : Fin m) (σ : Fin m → Fin l) : (fun i => σ (one h i)) = one (σ h) := rfl

theorem casesAt_rename {m l} (w b q h n z : Fin m) (σ : Fin m → Fin l) :
    (casesAt w b q h n z).rename σ = casesAt (σ w) (σ b) (σ q) (σ h) (σ n) (σ z) := by
  simp only [casesAt, ProjectCompilerCaseSyntax.cases_rename, one_map]

theorem localStep_rename {m l} (w b q h n : Fin m) (σ : Fin m → Fin l) :
    (localStep w b q h n).rename σ = localStep (σ w) (σ b) (σ q) (σ h) (σ n) := by
  simp only [localStep, localBody, Formula.rename, SyntaxTermSyntax.contexts_rename, empty_rename, casesAt_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem subst_bound {m} {Γ : Context m} (w b B q h n : Fin m) (he : Derives Γ (.equal b B))
    (hs : Derives Γ (localStep w b q h n)) : Derives Γ (localStep w B q h n) := by
  let P := localStep w.castSucc (Fin.last m) q.castSucc h.castSucc n.castSucc
  have h0 : P.instantiate b = localStep w b q h n := by
    simp only [P, Formula.instantiate, localStep_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have h1 : P.instantiate B = localStep w B q h n := by
    simp only [P, Formula.instantiate, localStep_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact of_eq h1 (Derives.eqSubst P he (of_eq h0.symm hs))

theorem subst_output {m} {Γ : Context m} (w b q Q h n : Fin m) (he : Derives Γ (.equal q Q))
    (hs : Derives Γ (localStep w b q h n)) : Derives Γ (localStep w b Q h n) := by
  let P := localStep w.castSucc b.castSucc (Fin.last m) h.castSucc n.castSucc
  have h0 : P.instantiate q = localStep w b q h n := by
    simp only [P, Formula.instantiate, localStep_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have h1 : P.instantiate Q = localStep w b Q h n := by
    simp only [P, Formula.instantiate, localStep_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact of_eq h1 (Derives.eqSubst P he (of_eq h0.symm hs))

theorem intro_local {m} {Γ : Context m} (w b q h n z : Fin m) (hn : Derives Γ (.mem n w))
    (hc : Derives Γ (SyntaxTermSyntax.contexts w b q)) (hz : Derives Γ (empty z))
    (hs : Derives Γ (casesAt w b q h n z)) : Derives Γ (localStep w b q h n) := by
  apply Derives.conjI hn
  apply Derives.conjI hc
  apply Derives.exI z
  exact of_eq (by simp only [localBody, Formula.instantiate, Formula.rename, empty_rename, casesAt_rename,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI hz hs)

end PPAC.Migration.Internal.ProjectCompilerLocalSyntax
