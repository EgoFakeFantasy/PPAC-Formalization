import PPAC.Migration.Internal.SyntaxMixedImageCodeExistence

/-! 原自然列表码和混合项像图的双向唯一性及原等词规则下的参数传输。 -/
namespace PPAC.Migration.Internal.SyntaxMixedImageCodeUnique
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxRenameQuerySyntax SyntaxMixedImageCodeSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem unique_code {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w f a c d L M : Fin m)
    (hw : Derives Γ (omega w)) (hL : Derives Γ (encoded w f a c d L)) (hM : Derives Γ (encoded w f a c d M)) :
    Derives Γ (.equal L M) := StructuralListCodeGraph.encoded_unique hZ w f a L M hw (.conjR hL) (.conjR hM)

theorem unique_graph {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w f g a c d L : Fin m)
    (hf : Derives Γ (encoded w f a c d L)) (hg : Derives Γ (encoded w g a c d L)) : Derives Γ (.equal f g) :=
  StructuralListFieldGraphFiber.unique hZ w L a f g
    (.conjL (.conjR (.conjR (.conjR hf)))) (.conjL (.conjR (.conjR (.conjR hg))))

theorem subst_graph {m} {Γ : Context m} (w f a c d L V : Fin m)
    (he : Derives Γ (.equal f V)) (hc : Derives Γ (encoded w f a c d L)) : Derives Γ (encoded w V a c d L) := by
  let P := encoded w.castSucc (Fin.last m) a.castSucc c.castSucc d.castSucc L.castSucc
  have e0 : P.instantiate f = encoded w f a c d L := by
    simp only [P, Formula.instantiate, encoded_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have e1 : P.instantiate V = encoded w V a c d L := by
    simp only [P, Formula.instantiate, encoded_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact of_eq e1 (Derives.eqSubst P he (of_eq e0.symm hc))

theorem subst_code {m} {Γ : Context m} (w f a c d L V : Fin m)
    (he : Derives Γ (.equal L V)) (hc : Derives Γ (encoded w f a c d L)) : Derives Γ (encoded w f a c d V) := by
  let P := encoded w.castSucc f.castSucc a.castSucc c.castSucc d.castSucc (Fin.last m)
  have e0 : P.instantiate L = encoded w f a c d L := by
    simp only [P, Formula.instantiate, encoded_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have e1 : P.instantiate V = encoded w f a c d V := by
    simp only [P, Formula.instantiate, encoded_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact of_eq e1 (Derives.eqSubst P he (of_eq e0.symm hc))

theorem at_encoding {m} {Γ : Context m} (w f a c d L : Fin m)
    (hL : Derives Γ (termList w a c d L)) (he : Derives Γ (StructuralListEncodeSyntax.encoding w f a L)) :
    Derives Γ (encoded w f a c d L) := SyntaxMixedImageCodeFields.from_fields w f a c d L hL (.conjR he)

theorem encoded_iff_input {m} {Γ : Context m} (w f a c d L : Fin m)
    (he : Derives Γ (StructuralListEncodeSyntax.encoding w f a L)) :
    Derives Γ ((encoded w f a c d L).iff (termList w a c d L)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact SyntaxMixedImageCodeFields.term_list w f a c d L (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact at_encoding w f a c d L (.hyp (Or.inl rfl)) (add he _)

end PPAC.Migration.Internal.SyntaxMixedImageCodeUnique
