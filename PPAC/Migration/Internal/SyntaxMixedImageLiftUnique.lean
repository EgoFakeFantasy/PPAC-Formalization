import PPAC.Migration.Internal.SyntaxMixedImageLiftFields

/-! 给定实际目标映射和新头项码的混合binder两表唯一；内部中间表见证不影响结果。 -/
namespace PPAC.Migration.Internal.SyntaxMixedImageLiftUnique
open Source SourceAlgebra SourceLogic GraphSyntax SyntaxRenameQuerySyntax SyntaxMixedImageLiftSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem prefixed_subst_table {m} {Γ : Context m} (w f F a c d z A g : Fin m)
    (he : Derives Γ (.equal f F)) (hp : Derives Γ (SyntaxTermImagePrefixSyntax.prefixed w f a c d z A g)) :
    Derives Γ (SyntaxTermImagePrefixSyntax.prefixed w F a c d z A g) := by
  let P := SyntaxTermImagePrefixSyntax.prefixed w.castSucc (Fin.last m) a.castSucc c.castSucc d.castSucc z.castSucc A.castSucc g.castSucc
  have e0 : P.instantiate f = SyntaxTermImagePrefixSyntax.prefixed w f a c d z A g := by
    simp only [P, Formula.instantiate, SyntaxTermImagePrefixSyntax.prefixed_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have e1 : P.instantiate F = SyntaxTermImagePrefixSyntax.prefixed w F a c d z A g := by
    simp only [P, Formula.instantiate, SyntaxTermImagePrefixSyntax.prefixed_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact of_eq e1 (Derives.eqSubst P he (of_eq e0.symm hp))

theorem unique_pair {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w R S r s a b c d A C n k h K H : Fin m)
    (hl : Derives Γ (lifted w R S r s a b c d A C n k h))
    (hL : Derives Γ (lifted w R S r s a b c d A C n K H)) : Derives Γ ((Formula.equal k K).conj (Formula.equal h H)) := by
  let B := body w R S r s a b c d A C n k h
  let Ξ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) hl
  have hL1 : Derives Ξ (lifted w.castSucc R.castSucc S.castSucc r.castSucc s.castSucc a.castSucc b.castSucc c.castSucc d.castSucc A.castSucc C.castSucc n.castSucc K.castSucc H.castSucc) :=
    of_eq (lifted_rename w R S r s a b c d A C n K H Fin.castSucc) (under hL B)
  let D := body w.castSucc R.castSucc S.castSucc r.castSucc s.castSucc a.castSucc b.castSucc c.castSucc d.castSucc A.castSucc C.castSucc n.castSucc K.castSucc H.castSucc
  let Δ := Context.add D (Context.image Formula.raise Ξ)
  apply Derives.exE (p := D) hL1
  have hZ2 := ZFContext.under (ZFContext.under hZ B) D
  have hB : Derives Ξ B := .hyp (Or.inl rfl)
  have hb2 : Derives Δ ((SyntaxTermImagePushBoth.both w.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc C.castSucc.castSucc d.castSucc.castSucc r.castSucc.castSucc s.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc (Fin.last m).castSucc h.castSucc.castSucc).conj
      (SyntaxTermImagePrefixSyntax.prefixed w.castSucc.castSucc (Fin.last m).castSucc a.castSucc.castSucc C.castSucc.castSucc d.castSucc.castSucc n.castSucc.castSucc A.castSucc.castSucc k.castSucc.castSucc)) :=
    of_eq (by simp only [B, body, Formula.raise, Formula.rename, SyntaxTermImagePushBoth.both_rename, SyntaxTermImagePrefixSyntax.prefixed_rename]) (under hB D)
  have hD : Derives Δ D := .hyp (Or.inl rfl)
  have he := SyntaxTermImagePushBoth.unique_pair hZ2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (.conjL hb2) (.conjL hD)
  have hp := prefixed_subst_table _ _ _ _ _ _ _ _ _ (.conjL he) (.conjR hb2)
  have hk := SyntaxTermImagePrefixGraph.unique hZ2 _ _ _ _ _ _ _ _ _ hp (.conjR hD)
  exact .conjI hk (.conjR he)

end PPAC.Migration.Internal.SyntaxMixedImageLiftUnique
