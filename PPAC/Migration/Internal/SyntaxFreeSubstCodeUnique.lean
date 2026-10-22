import PPAC.Migration.Internal.SyntaxFreeSubstCode

/-! 原项列表和索引码的双向唯一性，所有实际解码图在对象量词内对齐。 -/
namespace PPAC.Migration.Internal.SyntaxFreeSubstCodeUnique
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxRenameQuerySyntax SyntaxFreeSubstSyntax
open StructuralListEncodeSyntax (encoding encoding_rename)
open SyntaxMapCodeSyntax (encoded encoded_rename)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem subst_f {m} {Γ : Context m} (w f a c r g : Fin m)
    (he : Derives Γ (.equal f g)) (hc : Derives Γ (conversion w f a c r)) : Derives Γ (conversion w g a c r) := by
  let P := conversion w.castSucc (Fin.last m) a.castSucc c.castSucc r.castSucc
  have e0 : P.instantiate f = conversion w f a c r := by
    simp only [P, Formula.instantiate, conversion_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have e1 : P.instantiate g = conversion w g a c r := by
    simp only [P, Formula.instantiate, conversion_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact of_eq e1 (Derives.eqSubst P he (of_eq e0.symm hc))

theorem subst_r {m} {Γ : Context m} (w f a c r s : Fin m)
    (he : Derives Γ (.equal r s)) (hc : Derives Γ (conversion w f a c r)) : Derives Γ (conversion w f a c s) := by
  let P := conversion w.castSucc f.castSucc a.castSucc c.castSucc (Fin.last m)
  have e0 : P.instantiate r = conversion w f a c r := by
    simp only [P, Formula.instantiate, conversion_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have e1 : P.instantiate s = conversion w f a c s := by
    simp only [P, Formula.instantiate, conversion_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact of_eq e1 (Derives.eqSubst P he (of_eq e0.symm hc))

theorem encoding_graph_subst {m} {Γ : Context m} (w f g a L : Fin m)
    (he : Derives Γ (.equal f g)) (hc : Derives Γ (encoding w f a L)) : Derives Γ (encoding w g a L) := by
  let P := encoding w.castSucc (Fin.last m) a.castSucc L.castSucc
  have e0 : P.instantiate f = encoding w f a L := by
    simp only [P, Formula.instantiate, encoding_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have e1 : P.instantiate g = encoding w g a L := by
    simp only [P, Formula.instantiate, encoding_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact of_eq e1 (Derives.eqSubst P he (of_eq e0.symm hc))

theorem map_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a c L S T : Fin m)
    (hw : Derives Γ (omega w)) (h0 : Derives Γ (codeConversion w a c L S))
    (h1 : Derives Γ (codeConversion w a c L T)) : Derives Γ (.equal S T) := by
  let A := codeBody w a c L S
  let Δ := Context.add A (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply eliminate_code_conversion w a c L S _ h0
  have hA : Derives Δ A := .hyp (Or.inl rfl)
  have h12 : Derives Δ (codeConversion w.castSucc.castSucc a.castSucc.castSucc c.castSucc.castSucc L.castSucc.castSucc T.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise, codeConversion_rename]) (SyntaxRenameBinders.under_2 h1 A)
  let B := codeBody w.castSucc.castSucc a.castSucc.castSucc c.castSucc.castSucc L.castSucc.castSucc T.castSucc.castSucc
  let Θ := Context.add B (Context.image Formula.raise (Context.image Formula.raise Δ))
  apply eliminate_code_conversion w.castSucc.castSucc a.castSucc.castSucc c.castSucc.castSucc L.castSucc.castSucc T.castSucc.castSucc _ h12
  have hZ4 := SyntaxRenameBinders.zf_under_2 (SyntaxRenameBinders.zf_under_2 hZ A) B
  have hw4 : Derives Θ (omega w.castSucc.castSucc.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxRenameBinders.under_2 (SyntaxRenameBinders.under_2 hw A) B)
  have ha4 : Derives Θ ((encoding w.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc L.castSucc.castSucc.castSucc.castSucc).conj
      ((conversion w.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc).conj (encoded w.castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc S.castSucc.castSucc.castSucc.castSucc))) :=
    of_eq (by simp only [A, codeBody, Formula.raise, Formula.rename, encoding_rename, conversion_rename, encoded_rename])
      (SyntaxRenameBinders.under_2 hA B)
  have hb4 : Derives Θ B := .hyp (Or.inl rfl)
  have ef := eq_symm (.conjR (StructuralListEncodeReadback.decode_after_encode hZ4 w.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc L.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc
    hw4 (.conjL ha4) (.conjR (.conjL (.conjL hb4))) (.conjR (.conjL hb4))))
  have hc0 := subst_f _ _ _ _ _ _ ef (.conjL (.conjR ha4))
  have er := SyntaxFreeSubstCode.indices_unique hZ4 _ _ _ _ _ _ hc0 (.conjL (.conjR hb4))
  have hs0 := SyntaxMapCodeSyntax.graph_subst _ _ _ _ _ _ er (.conjR (.conjR ha4))
  exact SyntaxMapCode.unique_code hZ4 _ _ _ _ _ _ hw4 hs0 (.conjR (.conjR hb4))

theorem list_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a c L M S : Fin m)
    (hw : Derives Γ (omega w)) (h0 : Derives Γ (codeConversion w a c L S))
    (h1 : Derives Γ (codeConversion w a c M S)) : Derives Γ (.equal L M) := by
  let A := codeBody w a c L S
  let Δ := Context.add A (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply eliminate_code_conversion w a c L S _ h0
  have hA : Derives Δ A := .hyp (Or.inl rfl)
  have h12 : Derives Δ (codeConversion w.castSucc.castSucc a.castSucc.castSucc c.castSucc.castSucc M.castSucc.castSucc S.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise, codeConversion_rename]) (SyntaxRenameBinders.under_2 h1 A)
  let B := codeBody w.castSucc.castSucc a.castSucc.castSucc c.castSucc.castSucc M.castSucc.castSucc S.castSucc.castSucc
  let Θ := Context.add B (Context.image Formula.raise (Context.image Formula.raise Δ))
  apply eliminate_code_conversion w.castSucc.castSucc a.castSucc.castSucc c.castSucc.castSucc M.castSucc.castSucc S.castSucc.castSucc _ h12
  have hZ4 := SyntaxRenameBinders.zf_under_2 (SyntaxRenameBinders.zf_under_2 hZ A) B
  have hw4 : Derives Θ (omega w.castSucc.castSucc.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxRenameBinders.under_2 (SyntaxRenameBinders.under_2 hw A) B)
  have ha4 : Derives Θ ((encoding w.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc L.castSucc.castSucc.castSucc.castSucc).conj
      ((conversion w.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc).conj (encoded w.castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc S.castSucc.castSucc.castSucc.castSucc))) :=
    of_eq (by simp only [A, codeBody, Formula.raise, Formula.rename, encoding_rename, conversion_rename, encoded_rename])
      (SyntaxRenameBinders.under_2 hA B)
  have hb4 : Derives Θ B := .hyp (Or.inl rfl)
  have er := SyntaxMapCode.unique_graph hZ4 w.castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc (Fin.last (m+3)) a.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc S.castSucc.castSucc.castSucc.castSucc
    (.conjR (.conjR ha4)) (.conjR (.conjR hb4))
  have hc0 := subst_r _ _ _ _ _ _ er (.conjL (.conjR ha4))
  have ef := SyntaxFreeSubstCode.terms_unique hZ4 _ _ _ _ _ _ hw4 hc0 (.conjL (.conjR hb4))
  have hl0 := encoding_graph_subst _ _ _ _ _ ef (.conjL ha4)
  exact StructuralListCodeGraph.encoded_unique hZ4 _ _ _ _ _ hw4 hl0 (.conjL hb4)

end PPAC.Migration.Internal.SyntaxFreeSubstCodeUnique
