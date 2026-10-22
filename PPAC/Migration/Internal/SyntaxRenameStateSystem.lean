import PPAC.Migration.Internal.SyntaxRenameStateExistence

/-! 从两个实际完整索引图及目标公式，联合构造两个原自然映射码和实际状态自然码。 -/
namespace PPAC.Migration.Internal.SyntaxRenameStateSystem
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxIndexMapSyntax SyntaxMapCodeSyntax SyntaxRenameStateSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix FormulaCodeSyntax.formulaCode SyntaxMapCodeSyntax.mapCode SyntaxMapCodeSyntax.encoded SyntaxRenameStateSyntax.cell SyntaxRenameStateSyntax.state

def systemBody {m} (w r s a b c d q : Fin m) : Formula (m+3) :=
  (encoded w.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc).conj
    ((encoded w.castSucc.castSucc.castSucc s.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc).conj
      ((Formula.mem (Fin.last (m+2)) w.castSucc.castSucc.castSucc).conj (state w.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc a.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc q.castSucc.castSucc.castSucc (Fin.last (m+2)))))

def system {m} (w r s a b c d q : Fin m) : Formula m := .ex (.ex (.ex (systemBody w r s a b c d q)))

theorem system_rename {m n} (w r s a b c d q : Fin m) (ρ : Fin m → Fin n) :
    (system w r s a b c d q).rename ρ = system (ρ w) (ρ r) (ρ s) (ρ a) (ρ b) (ρ c) (ρ d) (ρ q) := by
  simp only [system, systemBody, Formula.rename, encoded_rename, state_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem context_head {m} (Γ : Context m) (p : Formula m) : Derives (Context.add p Γ) p :=
  .hyp (Or.inl rfl)

theorem under_encoded {m} {Γ : Context m} (w r a c k : Fin m)
    (he : Derives Γ (encoded w r a c k)) (P : Formula (m+1)) :
    Derives (Context.add P (Context.image Formula.raise Γ))
      (encoded w.castSucc r.castSucc a.castSucc c.castSucc k.castSucc) := by
  simpa only [Formula.raise, encoded_rename] using under he P

theorem under_formulaCode {m} {Γ : Context m} (w q c d : Fin m)
    (he : Derives Γ (FormulaCodeSyntax.formulaCode w q c d)) (P : Formula (m+1)) :
    Derives (Context.add P (Context.image Formula.raise Γ))
      (FormulaCodeSyntax.formulaCode w.castSucc q.castSucc c.castSucc d.castSucc) := by
  simpa only [Formula.raise, FormulaCodeSyntax.formulaCode_rename] using under he P

theorem intro_system {m} {Γ : Context m} (w r s a b c d q R S H : Fin m)
    (hr : Derives Γ (encoded w r a c R)) (hs : Derives Γ (encoded w s b d S))
    (hh : Derives Γ ((Formula.mem H w).conj (state w R S a b c d q H))) :
    Derives Γ (system w r s a b c d q) := by
  apply Derives.exI R
  apply Derives.exI S
  apply Derives.exI H
  simp only [systemBody, Formula.instantiate, Formula.rename, encoded_rename, state_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact .conjI hr (.conjI hs hh)

theorem actual_system {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r s a b c d q : Fin m)
    (hw : Derives Γ (omega w)) (hm : Derives Γ (maps w r s a b c d))
    (hq : Derives Γ (FormulaCodeSyntax.formulaCode w q c d)) : Derives Γ (system w r s a b c d q) := by
  have he := SyntaxMapCodeExistence.exists_code hZ w r a c hw (.conjL hm)
  let R := encoded w.castSucc r.castSucc a.castSucc c.castSucc (Fin.last m)
  let Ξ := Context.add R (Context.image Formula.raise Γ)
  change Derives Γ (.ex R) at he
  apply Derives.exE he
  have hZ1 := ZFContext.under hZ R
  have hw1 : Derives Ξ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw R
  have hm1 : Derives Ξ (maps w.castSucc r.castSucc s.castSucc a.castSucc b.castSucc c.castSucc d.castSucc) := by
    simpa only [Formula.raise, maps_rename] using under hm R
  have heS := SyntaxMapCodeExistence.exists_code hZ1 w.castSucc s.castSucc b.castSucc d.castSucc hw1 (.conjR hm1)
  let S := encoded w.castSucc.castSucc s.castSucc.castSucc b.castSucc.castSucc d.castSucc.castSucc (Fin.last (m+1))
  let Ψ := Context.add S (Context.image Formula.raise Ξ)
  change Derives Ξ (.ex S) at heS
  apply Derives.exE heS
  have hZ2 := ZFContext.under hZ1 S
  have hw2 : Derives Ψ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw1 S
  have hR : Derives Ξ R := context_head (Context.image Formula.raise Γ) R
  have hR2 : Derives Ψ (encoded w.castSucc.castSucc r.castSucc.castSucc a.castSucc.castSucc c.castSucc.castSucc (Fin.last m).castSucc) := under_encoded w.castSucc r.castSucc a.castSucc c.castSucc (Fin.last m) hR S
  have hS : Derives Ψ S := context_head (Context.image Formula.raise Ξ) S
  have hq2 : Derives Ψ (FormulaCodeSyntax.formulaCode w.castSucc.castSucc q.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc) := under_formulaCode w.castSucc q.castSucc c.castSucc d.castSucc (under_formulaCode w q c d hq R) S
  have hl : Derives Ψ (legal w.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc q.castSucc.castSucc) :=
    .conjI (intro_code w.castSucc.castSucc r.castSucc.castSucc a.castSucc.castSucc c.castSucc.castSucc (Fin.last m).castSucc hR2)
      (.conjI (intro_code w.castSucc.castSucc s.castSucc.castSucc b.castSucc.castSucc d.castSucc.castSucc (Fin.last (m+1)) hS) hq2)
  have hf := SyntaxRenameStateExistence.actual_exists hZ2 w.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc q.castSucc.castSucc hw2 hl
  let H := (Formula.mem (Fin.last (m+2)) w.castSucc.castSucc.castSucc).conj
    (state w.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc a.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc q.castSucc.castSucc.castSucc (Fin.last (m+2)))
  let Δ := Context.add H (Context.image Formula.raise Ψ)
  change Derives Ψ (.ex H) at hf
  apply Derives.exE hf
  have hr3 : Derives Δ (encoded w.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc) := under_encoded w.castSucc.castSucc r.castSucc.castSucc a.castSucc.castSucc c.castSucc.castSucc (Fin.last m).castSucc hR2 H
  have hs3 : Derives Δ (encoded w.castSucc.castSucc.castSucc s.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc) := under_encoded w.castSucc.castSucc s.castSucc.castSucc b.castSucc.castSucc d.castSucc.castSucc (Fin.last (m+1)) hS H
  have hH : Derives Δ H := context_head (Context.image Formula.raise Ψ) H
  have ho : Derives Δ (system w.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc s.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc q.castSucc.castSucc.castSucc) := intro_system w.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc s.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc q.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc (Fin.last (m+2)) hr3 hs3 hH
  have e : (system w r s a b c d q).raise.raise.raise = system w.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc s.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc q.castSucc.castSucc.castSucc := by
    simp only [Formula.raise, system_rename]
  exact Eq.mpr (congrArg (fun P => Derives Δ P) e) ho
end PPAC.Migration.Internal.SyntaxRenameStateSystem
