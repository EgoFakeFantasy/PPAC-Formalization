import PPAC.Migration.Internal.SyntaxComposeCodeExistence

/-! 实际复合自然码的全候选唯一性、实际唯一纤维与精确输入判据。 -/
namespace PPAC.Migration.Internal.SyntaxComposeCodeUnique
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxMapCodeSyntax SyntaxComposeSyntax SyntaxComposeCodeSyntax SyntaxRenameQuerySyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem at_sources {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r t a c e R T K L : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (encoded w r a c R)) (ht : Derives Γ (encoded w t c e T))
    (hk : Derives Γ (coded w a c e R T K)) (hl : Derives Γ (coded w a c e R T L)) : Derives Γ (.equal K L) := by
  let G := (composed w.castSucc r.castSucc t.castSucc a.castSucc c.castSucc e.castSucc (Fin.last m)).conj (encoded w.castSucc (Fin.last m) a.castSucc e.castSucc K.castSucc)
  let Ξ := Context.add G (Context.image Formula.raise Γ)
  apply Derives.exE (p := G) (SyntaxComposeCodeReadback.at_sources hZ w r t a c e R T K hr ht hk)
  have hr1 : Derives Ξ (encoded w.castSucc r.castSucc a.castSucc c.castSucc R.castSucc) := of_eq (encoded_rename _ _ _ _ _ Fin.castSucc) (under hr G)
  have ht1 : Derives Ξ (encoded w.castSucc t.castSucc c.castSucc e.castSucc T.castSucc) := of_eq (encoded_rename _ _ _ _ _ Fin.castSucc) (under ht G)
  have hl1 : Derives Ξ (coded w.castSucc a.castSucc c.castSucc e.castSucc R.castSucc T.castSucc L.castSucc) := of_eq (coded_rename _ _ _ _ _ _ _ Fin.castSucc) (under hl G)
  let H := (composed w.castSucc.castSucc r.castSucc.castSucc t.castSucc.castSucc a.castSucc.castSucc c.castSucc.castSucc e.castSucc.castSucc (Fin.last (m+1))).conj (encoded w.castSucc.castSucc (Fin.last (m+1)) a.castSucc.castSucc e.castSucc.castSucc L.castSucc.castSucc)
  let Δ := Context.add H (Context.image Formula.raise Ξ)
  apply Derives.exE (p := H) (SyntaxComposeCodeReadback.at_sources (ZFContext.under hZ G) _ _ _ _ _ _ _ _ _ hr1 ht1 hl1)
  have hZ2 := ZFContext.under (ZFContext.under hZ G) H
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (under (under hw G) H)
  have hG : Derives Ξ G := .hyp (Or.inl rfl)
  have hg2 : Derives Δ ((composed w.castSucc.castSucc r.castSucc.castSucc t.castSucc.castSucc a.castSucc.castSucc c.castSucc.castSucc e.castSucc.castSucc (Fin.last m).castSucc).conj (encoded w.castSucc.castSucc (Fin.last m).castSucc a.castSucc.castSucc e.castSucc.castSucc K.castSucc.castSucc)) := of_eq (by simp only [G, Formula.raise, Formula.rename, composed_rename, encoded_rename]) (under hG H)
  have hH : Derives Δ H := .hyp (Or.inl rfl)
  have he := SyntaxComposeGraph.unique hZ2 _ _ _ _ _ _ _ _ (.conjL hg2) (.conjL hH)
  have hk2 := graph_subst _ _ _ _ _ _ he (.conjR hg2)
  exact SyntaxMapCode.unique_code hZ2 _ _ _ _ _ _ hw2 hk2 (.conjR hH)

theorem unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a c e R T K L : Fin m)
    (hw : Derives Γ (omega w)) (hk : Derives Γ (coded w a c e R T K)) (hl : Derives Γ (coded w a c e R T L)) : Derives Γ (.equal K L) := by
  let B := body w a c e R T K
  let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise Γ)))
  apply eliminate_code w a c e R T K _ hk
  have hZ3 := SyntaxAtomLogic.zf_under_three hZ B
  have hw3 : Derives Δ (omega w.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxAtomLogic.under_three hw B)
  have hk3 : Derives Δ (coded w.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc e.castSucc.castSucc.castSucc R.castSucc.castSucc.castSucc T.castSucc.castSucc.castSucc K.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, coded_rename]) (SyntaxAtomLogic.under_three hk B)
  have hl3 : Derives Δ (coded w.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc e.castSucc.castSucc.castSucc R.castSucc.castSucc.castSucc T.castSucc.castSucc.castSucc L.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, coded_rename]) (SyntaxAtomLogic.under_three hl B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  exact at_sources hZ3 _ _ _ _ _ _ _ _ _ _ hw3 (.conjL hB) (.conjL (.conjR hB)) hk3 hl3

theorem actual_fiber {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a c e R T : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (mapCode w a c R)) (ht : Derives Γ (mapCode w c e T)) :
    Derives Γ (codeFiber w a c e R T) := by
  let K := coded w.castSucc a.castSucc c.castSucc e.castSucc R.castSucc T.castSucc (Fin.last m)
  let Ξ := Context.add K (Context.image Formula.raise Γ)
  apply Derives.exE (p := K) (SyntaxComposeCodeExistence.exists_code hZ w a c e R T hw hr ht)
  have hK : Derives Ξ K := .hyp (Or.inl rfl)
  have hu : Derives Ξ (.all ((coded w.castSucc.castSucc a.castSucc.castSucc c.castSucc.castSucc e.castSucc.castSucc R.castSucc.castSucc T.castSucc.castSucc (Fin.last (m+1))).imp (.equal (Fin.last (m+1)) (Fin.last m).castSucc))) := by
    apply Derives.allI
    apply Derives.impI
    let L := coded w.castSucc.castSucc a.castSucc.castSucc c.castSucc.castSucc e.castSucc.castSucc R.castSucc.castSucc T.castSucc.castSucc (Fin.last (m+1))
    let Δ := Context.add L (Context.image Formula.raise Ξ)
    have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (under (under hw K) L)
    have hk2 : Derives Δ (coded w.castSucc.castSucc a.castSucc.castSucc c.castSucc.castSucc e.castSucc.castSucc R.castSucc.castSucc T.castSucc.castSucc (Fin.last m).castSucc) := of_eq (by simp only [K, Formula.raise, coded_rename]) (under hK L)
    exact unique (ZFContext.under (ZFContext.under hZ K) L) _ _ _ _ _ _ _ _ hw2 (.hyp (Or.inl rfl)) hk2
  have ho : Derives Ξ (codeFiber w.castSucc a.castSucc c.castSucc e.castSucc R.castSucc T.castSucc) := by
    apply Derives.exI (Fin.last m)
    exact of_eq (by simp only [K, Formula.instantiate, Formula.rename, coded_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI hK hu)
  exact of_eq (codeFiber_rename w a c e R T Fin.castSucc).symm ho

theorem exists_iff_input {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a c e R T : Fin m) (hw : Derives Γ (omega w)) :
    Derives Γ ((SyntaxComposeCodeSyntax.existsCode w a c e R T).iff ((mapCode w a c R).conj (mapCode w c e T))) := by
  apply Derives.conjI
  · apply Derives.impI
    let E := SyntaxComposeCodeSyntax.existsCode w a c e R T
    let K := coded w.castSucc a.castSucc c.castSucc e.castSucc R.castSucc T.castSucc (Fin.last m)
    let Δ := Context.add K (Context.image Formula.raise (Context.add E Γ))
    apply Derives.exE (p := K) (.hyp (Or.inl rfl))
    have hK : Derives Δ K := .hyp (Or.inl rfl)
    have ho := Derives.conjI (SyntaxComposeCodeReadback.first_code _ _ _ _ _ _ _ hK) (SyntaxComposeCodeReadback.second_code _ _ _ _ _ _ _ hK)
    exact of_eq (by simp only [Formula.raise, Formula.rename, mapCode_rename]) ho
  · apply Derives.impI
    let I := (mapCode w a c R).conj (mapCode w c e T)
    have hI : Derives (Context.add I Γ) I := .hyp (Or.inl rfl)
    exact SyntaxComposeCodeExistence.exists_code (ZFContext.add hZ I) w a c e R T (add hw I) (.conjL hI) (.conjR hI)
end PPAC.Migration.Internal.SyntaxComposeCodeUnique
