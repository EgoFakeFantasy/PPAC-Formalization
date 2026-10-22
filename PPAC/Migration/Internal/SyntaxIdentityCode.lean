import PPAC.Migration.Internal.SyntaxIdentityGraph

/-! 实际恒等图的原自然列表码存在性与任意同码实际图的对角性。 -/
namespace PPAC.Migration.Internal.SyntaxIdentityCode
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxRenameQuerySyntax SyntaxIdentityMapSyntax
open SyntaxMapCodeSyntax SyntaxRenameTermIdentity
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem diagonal_subst {m} {Γ : Context m} (r s : Fin m)
    (he : Derives Γ (.equal r s)) (hd : Derives Γ (diagonal r)) : Derives Γ (diagonal s) := by
  let P := diagonal (Fin.last m)
  have e0 : P.instantiate r = diagonal r := by simp only [P, Formula.instantiate, diagonal_rename, Fin.lastCases_last]
  have e1 : P.instantiate s = diagonal s := by simp only [P, Formula.instantiate, diagonal_rename, Fin.lastCases_last]
  exact of_eq e1 (Derives.eqSubst P he (of_eq e0.symm hd))

theorem map_code {m} {Γ : Context m} (w a R : Fin m) (hi : Derives Γ (identityCode w a R)) :
    Derives Γ (mapCode w a a R) := by
  let B := (encoded w.castSucc (Fin.last m) a.castSucc a.castSucc R.castSucc).conj (diagonal (Fin.last m))
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) hi
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have ho := SyntaxMapCodeSyntax.intro_code w.castSucc (Fin.last m) a.castSucc a.castSucc R.castSucc (.conjL hB)
  exact of_eq (mapCode_rename w a a R Fin.castSucc).symm ho

theorem at_graph {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a R r : Fin m)
    (hi : Derives Γ (identityCode w a R)) (hr : Derives Γ (encoded w r a a R)) : Derives Γ (diagonal r) := by
  let B := (encoded w.castSucc (Fin.last m) a.castSucc a.castSucc R.castSucc).conj (diagonal (Fin.last m))
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) hi
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hr1 : Derives Δ (encoded w.castSucc r.castSucc a.castSucc a.castSucc R.castSucc) := of_eq (encoded_rename w r a a R Fin.castSucc) (under hr B)
  have he := SyntaxMapCode.unique_graph (ZFContext.under hZ B) w.castSucc (Fin.last m) r.castSucc a.castSucc a.castSucc R.castSucc (.conjL hB) hr1
  exact of_eq (diagonal_rename r Fin.castSucc).symm (diagonal_subst _ _ he (.conjR hB))

theorem encoded_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a R r : Fin m)
    (hr : Derives Γ (encoded w r a a R)) : Derives Γ ((identityCode w a R).iff (diagonal r)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact at_graph (ZFContext.add hZ _) w a R r (.hyp (Or.inl rfl)) (add hr _)
  · apply Derives.impI
    exact SyntaxIdentityMapSyntax.intro_code w a r R (add hr _) (.hyp (Or.inl rfl))

theorem exists_at_graph {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a r : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (identityMap w a r)) : Derives Γ (SyntaxIdentityMapSyntax.existsCode w a) := by
  have he := SyntaxMapCodeExistence.exists_code hZ w r a a hw (.conjL hi)
  let B := encoded w.castSucc r.castSucc a.castSucc a.castSucc (Fin.last m)
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) he
  have hd : Derives Δ (diagonal r.castSucc) := of_eq (diagonal_rename r Fin.castSucc) (under (.conjR hi) B)
  have hb : Derives Δ B := .hyp (Or.inl rfl)
  have hc := SyntaxIdentityMapSyntax.intro_code w.castSucc a.castSucc r.castSucc (Fin.last m) hb hd
  have ho : Derives Δ (SyntaxIdentityMapSyntax.existsCode w.castSucc a.castSucc) := by
    apply Derives.exI (Fin.last m)
    exact of_eq (by simp only [Formula.instantiate, identityCode_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hc
  exact of_eq (SyntaxIdentityMapSyntax.existsCode_rename w a Fin.castSucc).symm ho

theorem exists_code {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) : Derives Γ (SyntaxIdentityMapSyntax.existsCode w a) := by
  let B := identityMap w.castSucc a.castSucc (Fin.last m)
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) (SyntaxIdentityGraph.exists_map hZ w a ha)
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw B)
  have ho := exists_at_graph (ZFContext.under hZ B) w.castSucc a.castSucc (Fin.last m) hw1 (.hyp (Or.inl rfl))
  exact of_eq (SyntaxIdentityMapSyntax.existsCode_rename w a Fin.castSucc).symm ho
end PPAC.Migration.Internal.SyntaxIdentityCode
