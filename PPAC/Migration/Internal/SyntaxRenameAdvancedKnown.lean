import PPAC.Migration.Internal.SyntaxRenameJudgmentSubst

/-! 给定真实CodedLift时，所有量词提升候选通过后继/码唯一性对齐到同一个子判断。 -/
namespace PPAC.Migration.Internal.SyntaxRenameAdvancedKnown
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxRenameQuerySyntax SyntaxRenameJudgmentSyntax SyntaxRenameRecursiveSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem intro_advanced {m} {Γ : Context m} (w x r s a b c d q u v l : Fin m)
    (hl : Derives Γ (SyntaxMapLiftSyntax.codedLift w a c r u v l)) (hr : Derives Γ (renamed w l s u b v d x q)) :
    Derives Γ (SyntaxRenameRecursiveSyntax.advanced w x r s a b c d q) := by
  apply Derives.exI u
  apply Derives.exI v
  apply Derives.exI l
  simp only [SyntaxRenameRecursiveSyntax.advancedBody, Formula.instantiate, Formula.rename, SyntaxMapLiftSyntax.codedLift_rename, renamed_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact .conjI hl hr

theorem eliminate_advanced {m} {Γ : Context m} (w x r s a b c d q : Fin m) (P : Formula m)
    (he : Derives Γ (SyntaxRenameRecursiveSyntax.advanced w x r s a b c d q))
    (hc : Derives (Context.add (SyntaxRenameRecursiveSyntax.advancedBody w x r s a b c d q)
      (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise Γ)))) P.raise.raise.raise) : Derives Γ P := by
  apply Derives.exE he
  apply Derives.exE (.hyp (Or.inl rfl))
  apply Derives.exE (.hyp (Or.inl rfl))
  refine Derives.weaken ?_ hc
  rintro p (hp | ⟨s1, ⟨s2, hs, h2⟩, h1⟩)
  · exact Or.inl hp
  · exact Or.inr ⟨s1, Or.inr ⟨s2, Or.inr hs, h2⟩, h1⟩

theorem at_lift {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w x r s a b c d q u v l : Fin m)
    (hw : Derives Γ (omega w)) (hl : Derives Γ (SyntaxMapLiftSyntax.codedLift w a c r u v l)) :
    Derives Γ ((SyntaxRenameRecursiveSyntax.advanced w x r s a b c d q).iff (renamed w l s u b v d x q)) := by
  apply Derives.conjI
  · apply Derives.impI
    let T := SyntaxRenameRecursiveSyntax.advanced w x r s a b c d q
    let B := SyntaxRenameRecursiveSyntax.advancedBody w x r s a b c d q
    let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.add T Γ))))
    apply eliminate_advanced w x r s a b c d q _ (.hyp (Or.inl rfl))
    have hZ3 := SyntaxAtomLogic.zf_under_three (ZFContext.add hZ T) B
    have hw3 : Derives Δ (omega w.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxAtomLogic.under_three (add hw T) B)
    have hl3 : Derives Δ (SyntaxMapLiftSyntax.codedLift w.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc u.castSucc.castSucc.castSucc v.castSucc.castSucc.castSucc l.castSucc.castSucc.castSucc) :=
      of_eq (by simp only [Formula.raise, SyntaxMapLiftSyntax.codedLift_rename]) (SyntaxAtomLogic.under_three (add hl T) B)
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have he := SyntaxMapLiftParameters.unique hZ3 w.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc
      (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc (Fin.last (m+2)) u.castSucc.castSucc.castSucc v.castSucc.castSucc.castSucc l.castSucc.castSucc.castSucc hw3 (.conjL hB) hl3
    have h0 := SyntaxRenameJudgmentSubst.subst_r w.castSucc.castSucc.castSucc (Fin.last (m+2)) s.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc b.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc d.castSucc.castSucc.castSucc x.castSucc.castSucc.castSucc q.castSucc.castSucc.castSucc l.castSucc.castSucc.castSucc (.conjR (.conjR he)) (.conjR hB)
    have h1 := SyntaxRenameJudgmentSubst.subst_a w.castSucc.castSucc.castSucc l.castSucc.castSucc.castSucc s.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc b.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc d.castSucc.castSucc.castSucc x.castSucc.castSucc.castSucc q.castSucc.castSucc.castSucc u.castSucc.castSucc.castSucc (.conjL he) h0
    have h2 := SyntaxRenameJudgmentSubst.subst_c w.castSucc.castSucc.castSucc l.castSucc.castSucc.castSucc s.castSucc.castSucc.castSucc u.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc d.castSucc.castSucc.castSucc x.castSucc.castSucc.castSucc q.castSucc.castSucc.castSucc v.castSucc.castSucc.castSucc (.conjL (.conjR he)) h1
    exact of_eq (by simp only [Formula.raise, renamed_rename]) h2
  · apply Derives.impI
    exact intro_advanced w x r s a b c d q u v l (add hl _) (.hyp (Or.inl rfl))
end PPAC.Migration.Internal.SyntaxRenameAdvancedKnown
