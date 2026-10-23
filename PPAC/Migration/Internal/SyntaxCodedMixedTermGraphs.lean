import PPAC.Migration.Internal.SyntaxCodedMixedTermSyntax

/-! 任意实际环境解码图识别同一个原数值参数混合项替换；内部图见证经原等词规则对齐。 -/
namespace PPAC.Migration.Internal.SyntaxCodedMixedTermGraphs
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxRenameQuerySyntax SyntaxCodedMixedTermSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem subst_bound_graph {m} {Γ : Context m} (w r s a b c d n q V : Fin m)
    (he : Derives Γ (.equal r V)) (hq : Derives Γ (SyntaxMixedTermSyntax.substituted w r s a b c d n q)) :
    Derives Γ (SyntaxMixedTermSyntax.substituted w V s a b c d n q) := by
  let P := SyntaxMixedTermSyntax.substituted w.castSucc (Fin.last m) s.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc q.castSucc
  have e0 : P.instantiate r = SyntaxMixedTermSyntax.substituted w r s a b c d n q := by
    simp only [P, Formula.instantiate, SyntaxMixedTermSyntax.substituted_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have e1 : P.instantiate V = SyntaxMixedTermSyntax.substituted w V s a b c d n q := by
    simp only [P, Formula.instantiate, SyntaxMixedTermSyntax.substituted_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact of_eq e1 (Derives.eqSubst P he (of_eq e0.symm hq))

theorem subst_free_graph {m} {Γ : Context m} (w r s a b c d n q V : Fin m)
    (he : Derives Γ (.equal s V)) (hq : Derives Γ (SyntaxMixedTermSyntax.substituted w r s a b c d n q)) :
    Derives Γ (SyntaxMixedTermSyntax.substituted w r V a b c d n q) := by
  let P := SyntaxMixedTermSyntax.substituted w.castSucc r.castSucc (Fin.last m) a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc q.castSucc
  have e0 : P.instantiate s = SyntaxMixedTermSyntax.substituted w r s a b c d n q := by
    simp only [P, Formula.instantiate, SyntaxMixedTermSyntax.substituted_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have e1 : P.instantiate V = SyntaxMixedTermSyntax.substituted w r V a b c d n q := by
    simp only [P, Formula.instantiate, SyntaxMixedTermSyntax.substituted_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact of_eq e1 (Derives.eqSubst P he (of_eq e0.symm hq))

theorem at_graphs {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w R S a b c d n q r s : Fin m)
    (he : Derives Γ (SyntaxMixedImageCodeSyntax.encodings w r s a b c d R S))
    (hq : Derives Γ (substituted w R S a b c d n q)) : Derives Γ (SyntaxMixedTermSyntax.substituted w r s a b c d n q) := by
  let B := body w R S a b c d n q
  let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply SyntaxRenameBinders.eliminate_2 B _ hq
  have he2 : Derives Δ (SyntaxMixedImageCodeSyntax.encodings w.castSucc.castSucc r.castSucc.castSucc s.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise, SyntaxMixedImageCodeSyntax.encodings_rename]) (SyntaxRenameBinders.under_2 he B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have eq := SyntaxMixedImageCodePairs.graphs_unique (SyntaxRenameBinders.zf_under_2 hZ B) w.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc r.castSucc.castSucc s.castSucc.castSucc (.conjL hB) he2
  have hr := subst_bound_graph w.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc n.castSucc.castSucc q.castSucc.castSucc r.castSucc.castSucc (.conjL eq) (.conjR hB)
  have hs := subst_free_graph w.castSucc.castSucc r.castSucc.castSucc (Fin.last (m+1)) a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc n.castSucc.castSucc q.castSucc.castSucc s.castSucc.castSucc (.conjR eq) hr
  exact of_eq (by simp only [Formula.raise, SyntaxMixedTermSyntax.substituted_rename]) hs

theorem at_graphs_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w R S a b c d n q r s : Fin m)
    (he : Derives Γ (SyntaxMixedImageCodeSyntax.encodings w r s a b c d R S)) :
    Derives Γ ((substituted w R S a b c d n q).iff (SyntaxMixedTermSyntax.substituted w r s a b c d n q)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact at_graphs (ZFContext.add hZ _) w R S a b c d n q r s (add he _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact intro_substituted w R S a b c d n q r s (add he _) (.hyp (Or.inl rfl))

end PPAC.Migration.Internal.SyntaxCodedMixedTermGraphs
