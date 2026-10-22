import PPAC.Migration.Internal.SyntaxComposeCodeSyntax

/-! 任意实际输入/输出解码下的精确复合识别；不从列表码推断独立目标作用域。 -/
namespace PPAC.Migration.Internal.SyntaxComposeCodeReadback
open Source SourceAlgebra SourceLogic GraphSyntax SyntaxMapCodeSyntax SyntaxComposeSyntax SyntaxComposeCodeSyntax SyntaxRenameQuerySyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem first_code {m} {Γ : Context m} (w a c e R T K : Fin m) (hc : Derives Γ (coded w a c e R T K)) :
    Derives Γ (mapCode w a c R) := by
  let B := body w a c e R T K
  let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise Γ)))
  apply eliminate_code w a c e R T K _ hc
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have ho := SyntaxMapCodeSyntax.intro_code w.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc a.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc R.castSucc.castSucc.castSucc (.conjL hB)
  exact of_eq (by simp only [Formula.raise, mapCode_rename]) ho

theorem second_code {m} {Γ : Context m} (w a c e R T K : Fin m) (hc : Derives Γ (coded w a c e R T K)) :
    Derives Γ (mapCode w c e T) := by
  let B := body w a c e R T K
  let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise Γ)))
  apply eliminate_code w a c e R T K _ hc
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have ho := SyntaxMapCodeSyntax.intro_code w.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc c.castSucc.castSucc.castSucc e.castSucc.castSucc.castSucc T.castSucc.castSucc.castSucc (.conjL (.conjR hB))
  exact of_eq (by simp only [Formula.raise, mapCode_rename]) ho

theorem output_code {m} {Γ : Context m} (w a c e R T K : Fin m) (hc : Derives Γ (coded w a c e R T K)) :
    Derives Γ (mapCode w a e K) := by
  let B := body w a c e R T K
  let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise Γ)))
  apply eliminate_code w a c e R T K _ hc
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have ho := SyntaxMapCodeSyntax.intro_code w.castSucc.castSucc.castSucc (Fin.last (m+2)) a.castSucc.castSucc.castSucc e.castSucc.castSucc.castSucc K.castSucc.castSucc.castSucc (.conjR (.conjR (.conjR hB)))
  exact of_eq (by simp only [Formula.raise, mapCode_rename]) ho

theorem at_sources {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r t a c e R T K : Fin m)
    (hr : Derives Γ (encoded w r a c R)) (ht : Derives Γ (encoded w t c e T))
    (hc : Derives Γ (coded w a c e R T K)) : Derives Γ (outputAt w r t a c e K) := by
  let B := body w a c e R T K
  let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise Γ)))
  apply eliminate_code w a c e R T K _ hc
  have hZ3 := SyntaxAtomLogic.zf_under_three hZ B
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hr3 : Derives Δ (encoded w.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc R.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, encoded_rename]) (SyntaxAtomLogic.under_three hr B)
  have ht3 : Derives Δ (encoded w.castSucc.castSucc.castSucc t.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc e.castSucc.castSucc.castSucc T.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, encoded_rename]) (SyntaxAtomLogic.under_three ht B)
  have er := SyntaxMapCode.unique_graph hZ3 _ _ _ _ _ _ (.conjL hB) hr3
  have et := SyntaxMapCode.unique_graph hZ3 _ _ _ _ _ _ (.conjL (.conjR hB)) ht3
  have h1 := subst_first _ _ _ _ _ _ _ _ er (.conjL (.conjR (.conjR hB)))
  have h2 := subst_second _ _ _ _ _ _ _ _ et h1
  have ho : Derives Δ (outputAt w.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc t.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc e.castSucc.castSucc.castSucc K.castSucc.castSucc.castSucc) := by
    apply Derives.exI (Fin.last (m+2))
    exact of_eq (by simp only [Formula.instantiate, Formula.rename, composed_rename, encoded_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI h2 (.conjR (.conjR (.conjR hB))))
  exact of_eq (by simp only [Formula.raise, outputAt_rename]) ho

theorem at_graphs {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r t a c e R T K g : Fin m)
    (hr : Derives Γ (encoded w r a c R)) (ht : Derives Γ (encoded w t c e T)) (hg : Derives Γ (encoded w g a e K))
    (hc : Derives Γ (coded w a c e R T K)) : Derives Γ (composed w r t a c e g) := by
  have he := at_sources hZ w r t a c e R T K hr ht hc
  let B := (composed w.castSucc r.castSucc t.castSucc a.castSucc c.castSucc e.castSucc (Fin.last m)).conj (encoded w.castSucc (Fin.last m) a.castSucc e.castSucc K.castSucc)
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) he
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hg1 : Derives Δ (encoded w.castSucc g.castSucc a.castSucc e.castSucc K.castSucc) := of_eq (encoded_rename _ _ _ _ _ Fin.castSucc) (under hg B)
  have heq := SyntaxMapCode.unique_graph (ZFContext.under hZ B) _ _ _ _ _ _ (.conjR hB) hg1
  exact of_eq (composed_rename w r t a c e g Fin.castSucc).symm (subst_output _ _ _ _ _ _ _ _ heq (.conjL hB))

theorem encoded_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r t a c e R T K g : Fin m)
    (hr : Derives Γ (encoded w r a c R)) (ht : Derives Γ (encoded w t c e T)) (hg : Derives Γ (encoded w g a e K)) :
    Derives Γ ((coded w a c e R T K).iff (composed w r t a c e g)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact at_graphs (ZFContext.add hZ _) w r t a c e R T K g (add hr _) (add ht _) (add hg _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact intro_code w a c e R T K r t g (add hr _) (add ht _) (.hyp (Or.inl rfl)) (add hg _)

theorem edge_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r t a c e R T K g i j : Fin m)
    (hr : Derives Γ (encoded w r a c R)) (ht : Derives Γ (encoded w t c e T)) (hg : Derives Γ (encoded w g a e K))
    (hc : Derives Γ (coded w a c e R T K)) : Derives Γ ((edge g i j).iff (value r t i j)) :=
  SyntaxComposeGraph.edge_iff hZ w r t a c e g i j (at_graphs hZ w r t a c e R T K g hr ht hg hc)
end PPAC.Migration.Internal.SyntaxComposeCodeReadback
