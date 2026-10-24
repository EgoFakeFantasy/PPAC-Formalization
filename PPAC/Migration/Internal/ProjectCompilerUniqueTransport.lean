import PPAC.Migration.Internal.ProjectCompilerUniqueSyntax

/-! Equality transport of actual compiler queries, atomic data and target constructor fields. -/
namespace PPAC.Migration.Internal.ProjectCompilerUniqueTransport
open Source SourceAlgebra SourceLogic ProjectCompilerRecursiveSyntax

theorem atomic_left {m} {Γ : Context m} (kind : Fin 3) (w b z x y n q t : Fin m) (he : Derives Γ (.equal x t))
    (hc : Derives Γ (ProjectAtomicSyntax.compiled kind w b z x y n q)) : Derives Γ (ProjectAtomicSyntax.compiled kind w b z t y n q) := by
  have hi : Derives Γ ((ProjectAtomicSyntax.compiled kind w.castSucc b.castSucc z.castSucc (Fin.last m) y.castSucc n.castSucc q.castSucc).instantiate x) := by
    simpa only [Formula.instantiate, ProjectAtomicSyntax.compiled_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hc
  have ho := Derives.eqSubst (ProjectAtomicSyntax.compiled kind w.castSucc b.castSucc z.castSucc (Fin.last m) y.castSucc n.castSucc q.castSucc) he hi
  simpa only [Formula.instantiate, ProjectAtomicSyntax.compiled_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using ho

theorem atomic_right {m} {Γ : Context m} (kind : Fin 3) (w b z x y n q t : Fin m) (he : Derives Γ (.equal y t))
    (hc : Derives Γ (ProjectAtomicSyntax.compiled kind w b z x y n q)) : Derives Γ (ProjectAtomicSyntax.compiled kind w b z x t n q) := by
  have hi : Derives Γ ((ProjectAtomicSyntax.compiled kind w.castSucc b.castSucc z.castSucc x.castSucc (Fin.last m) n.castSucc q.castSucc).instantiate y) := by
    simpa only [Formula.instantiate, ProjectAtomicSyntax.compiled_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hc
  have ho := Derives.eqSubst (ProjectAtomicSyntax.compiled kind w.castSucc b.castSucc z.castSucc x.castSucc (Fin.last m) n.castSucc q.castSucc) he hi
  simpa only [Formula.instantiate, ProjectAtomicSyntax.compiled_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using ho

theorem single_input {m} {Γ : Context m} (tag : Nat) (w x q t : Fin m) (he : Derives Γ (.equal x t))
    (hc : Derives Γ (SyntaxLogicalSyntax.singleCode tag w x q)) : Derives Γ (SyntaxLogicalSyntax.singleCode tag w t q) := by
  have hi : Derives Γ ((SyntaxLogicalSyntax.singleCode tag w.castSucc (Fin.last m) q.castSucc).instantiate x) := by
    simpa only [Formula.instantiate, SyntaxLogicalSyntax.singleCode_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hc
  have ho := Derives.eqSubst (SyntaxLogicalSyntax.singleCode tag w.castSucc (Fin.last m) q.castSucc) he hi
  simpa only [Formula.instantiate, SyntaxLogicalSyntax.singleCode_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using ho

theorem binary_left {m} {Γ : Context m} (kind : Fin 4) (w x y q t : Fin m) (he : Derives Γ (.equal x t))
    (hc : Derives Γ (SyntaxLogicalSyntax.binaryCode kind w x y q)) : Derives Γ (SyntaxLogicalSyntax.binaryCode kind w t y q) := by
  have hi : Derives Γ ((SyntaxLogicalSyntax.binaryCode kind w.castSucc (Fin.last m) y.castSucc q.castSucc).instantiate x) := by
    simpa only [Formula.instantiate, SyntaxLogicalSyntax.binaryCode_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hc
  have ho := Derives.eqSubst (SyntaxLogicalSyntax.binaryCode kind w.castSucc (Fin.last m) y.castSucc q.castSucc) he hi
  simpa only [Formula.instantiate, SyntaxLogicalSyntax.binaryCode_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using ho

theorem binary_right {m} {Γ : Context m} (kind : Fin 4) (w x y q t : Fin m) (he : Derives Γ (.equal y t))
    (hc : Derives Γ (SyntaxLogicalSyntax.binaryCode kind w x y q)) : Derives Γ (SyntaxLogicalSyntax.binaryCode kind w x t q) := by
  have hi : Derives Γ ((SyntaxLogicalSyntax.binaryCode kind w.castSucc x.castSucc (Fin.last m) q.castSucc).instantiate y) := by
    simpa only [Formula.instantiate, SyntaxLogicalSyntax.binaryCode_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hc
  have ho := Derives.eqSubst (SyntaxLogicalSyntax.binaryCode kind w.castSucc x.castSucc (Fin.last m) q.castSucc) he hi
  simpa only [Formula.instantiate, SyntaxLogicalSyntax.binaryCode_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using ho

theorem check_input {m} {Γ : Context m} (advance : Bool) (w n x b q t : Fin m) (he : Derives Γ (.equal x t))
    (hc : Derives Γ (ProjectCompilerCaseSyntax.check advance codeMatrix (parameters w) n x b q)) : Derives Γ (ProjectCompilerCaseSyntax.check advance codeMatrix (parameters w) n t b q) := by
  have hi : Derives Γ ((ProjectCompilerCaseSyntax.check advance codeMatrix (parameters w.castSucc) n.castSucc (Fin.last m) b.castSucc q.castSucc).instantiate x) := by
    simpa only [Formula.instantiate, ProjectCompilerCaseSyntax.check_rename, parameters_map, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hc
  have ho := Derives.eqSubst (ProjectCompilerCaseSyntax.check advance codeMatrix (parameters w.castSucc) n.castSucc (Fin.last m) b.castSucc q.castSucc) he hi
  simpa only [Formula.instantiate, ProjectCompilerCaseSyntax.check_rename, parameters_map, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using ho

theorem cases_zero {m} {Γ : Context m}  (w b z n q t : Fin m) (he : Derives Γ (.equal z t))
    (hc : Derives Γ (casesAt w b z n q)) : Derives Γ (casesAt w b t n q) := by
  have hi : Derives Γ ((casesAt w.castSucc b.castSucc (Fin.last m) n.castSucc q.castSucc).instantiate z) := by
    simpa only [Formula.instantiate, casesAt_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hc
  have ho := Derives.eqSubst (casesAt w.castSucc b.castSucc (Fin.last m) n.castSucc q.castSucc) he hi
  simpa only [Formula.instantiate, casesAt_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using ho

end PPAC.Migration.Internal.ProjectCompilerUniqueTransport
