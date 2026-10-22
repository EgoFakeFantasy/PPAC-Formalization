import PPAC.Migration.Internal.SyntaxComposeCodeReadback

/-! 两个可复合原自然映射码实际产生原自然复合码；所有实际图由对象存在消去取得。 -/
namespace PPAC.Migration.Internal.SyntaxComposeCodeExistence
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxMapCodeSyntax SyntaxComposeSyntax SyntaxComposeCodeSyntax SyntaxRenameQuerySyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem exists_at_sources {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r t a c e R T : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (encoded w r a c R)) (ht : Derives Γ (encoded w t c e T)) :
    Derives Γ (SyntaxComposeCodeSyntax.existsCode w a c e R T) := by
  let G := composed w.castSucc r.castSucc t.castSucc a.castSucc c.castSucc e.castSucc (Fin.last m)
  let Ξ := Context.add G (Context.image Formula.raise Γ)
  apply Derives.exE (p := G) (SyntaxComposeGraph.exists_graph hZ w r t a c e (.conjR hr) (.conjR ht))
  have hZ1 := ZFContext.under hZ G
  have hw1 : Derives Ξ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw G)
  have hG : Derives Ξ G := .hyp (Or.inl rfl)
  have hk := SyntaxMapCodeExistence.exists_code hZ1 w.castSucc (Fin.last m) a.castSucc e.castSucc hw1 (SyntaxComposeGraph.target_map _ _ _ _ _ _ _ hG)
  let K := encoded w.castSucc.castSucc (Fin.last m).castSucc a.castSucc.castSucc e.castSucc.castSucc (Fin.last (m+1))
  let Δ := Context.add K (Context.image Formula.raise Ξ)
  apply Derives.exE (p := K) hk
  have hr2 : Derives Δ (encoded w.castSucc.castSucc r.castSucc.castSucc a.castSucc.castSucc c.castSucc.castSucc R.castSucc.castSucc) := of_eq (by simp only [Formula.raise, encoded_rename]) (under (under hr G) K)
  have ht2 : Derives Δ (encoded w.castSucc.castSucc t.castSucc.castSucc c.castSucc.castSucc e.castSucc.castSucc T.castSucc.castSucc) := of_eq (by simp only [Formula.raise, encoded_rename]) (under (under ht G) K)
  have hg2 : Derives Δ (composed w.castSucc.castSucc r.castSucc.castSucc t.castSucc.castSucc a.castSucc.castSucc c.castSucc.castSucc e.castSucc.castSucc (Fin.last m).castSucc) := of_eq (by simp only [G, Formula.raise, composed_rename]) (under hG K)
  have hK : Derives Δ K := .hyp (Or.inl rfl)
  have hc := intro_code w.castSucc.castSucc a.castSucc.castSucc c.castSucc.castSucc e.castSucc.castSucc R.castSucc.castSucc T.castSucc.castSucc (Fin.last (m+1)) r.castSucc.castSucc t.castSucc.castSucc (Fin.last m).castSucc hr2 ht2 hg2 hK
  have ho : Derives Δ (SyntaxComposeCodeSyntax.existsCode w.castSucc.castSucc a.castSucc.castSucc c.castSucc.castSucc e.castSucc.castSucc R.castSucc.castSucc T.castSucc.castSucc) := by
    apply Derives.exI (Fin.last (m+1))
    exact of_eq (by simp only [Formula.instantiate, coded_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hc
  exact of_eq (by simp only [Formula.raise, SyntaxComposeCodeSyntax.existsCode_rename]) ho

theorem exists_code {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a c e R T : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (mapCode w a c R)) (ht : Derives Γ (mapCode w c e T)) :
    Derives Γ (SyntaxComposeCodeSyntax.existsCode w a c e R T) := by
  let G := encoded w.castSucc (Fin.last m) a.castSucc c.castSucc R.castSucc
  let Ξ := Context.add G (Context.image Formula.raise Γ)
  apply Derives.exE (p := G) hr
  have ht1 : Derives Ξ (mapCode w.castSucc c.castSucc e.castSucc T.castSucc) := of_eq (mapCode_rename _ _ _ _ Fin.castSucc) (under ht G)
  let H := encoded w.castSucc.castSucc (Fin.last (m+1)) c.castSucc.castSucc e.castSucc.castSucc T.castSucc.castSucc
  let Δ := Context.add H (Context.image Formula.raise Ξ)
  apply Derives.exE (p := H) ht1
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (under (under hw G) H)
  have hG : Derives Ξ G := .hyp (Or.inl rfl)
  have hg2 : Derives Δ (encoded w.castSucc.castSucc (Fin.last m).castSucc a.castSucc.castSucc c.castSucc.castSucc R.castSucc.castSucc) := of_eq (by simp only [G, Formula.raise, encoded_rename]) (under hG H)
  have ho := exists_at_sources (ZFContext.under (ZFContext.under hZ G) H) _ _ _ _ _ _ _ _ hw2 hg2 (.hyp (Or.inl rfl))
  exact of_eq (by simp only [Formula.raise, SyntaxComposeCodeSyntax.existsCode_rename]) ho
end PPAC.Migration.Internal.SyntaxComposeCodeExistence
