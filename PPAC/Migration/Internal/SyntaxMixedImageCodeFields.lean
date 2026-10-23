import PPAC.Migration.Internal.SyntaxMixedImageCodeSyntax

/-! 原列表码字段与实际完整混合项像图的双条件，以及不含图存在前提的纯类型谓词。 -/
namespace PPAC.Migration.Internal.SyntaxMixedImageCodeFields
open Source SourceAlgebra SourceLogic OmegaSyntax GraphSyntax SyntaxRenameQuerySyntax SyntaxMixedImageCodeSyntax
open SyntaxTermImageSyntax (imageMap imageMap_rename)
open StructuralListFieldSyntax (field field_rename)
open StructuralListFieldGraphSyntax (fields fields_rename law_at)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem typed_at {m} {Γ : Context m} (w a c d L i q : Fin m) (ht : Derives Γ (typedFields w a c d L)) :
    Derives Γ (((Formula.mem i a).conj (field w L i q)).imp (SyntaxTermSyntax.term w c d q)) :=
  of_eq (by simp only [Formula.instantiate, Formula.rename, field_rename, SyntaxTermSyntax.term_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (Derives.allE q (Derives.allE i ht))

theorem edges {m} {Γ : Context m} (w f a c d L i q : Fin m) (he : Derives Γ (encoded w f a c d L)) :
    Derives Γ ((edge f i q).iff ((Formula.mem i a).conj (field w L i q))) :=
  law_at w L a f i q (.conjR (.conjR (.conjR (.conjR he))))

theorem term_list {m} {Γ : Context m} (w f a c d L : Fin m) (he : Derives Γ (encoded w f a c d L)) :
    Derives Γ (termList w a c d L) := by
  apply Derives.conjI (.conjL (.conjL he))
  apply Derives.conjI (.conjL (.conjR (.conjL he)))
  apply Derives.conjI (.conjL (.conjR he))
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  let B := (Formula.mem (Fin.last m).castSucc a.castSucc.castSucc).conj
    (field w.castSucc.castSucc L.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)))
  let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise Γ))
  have he2 : Derives Δ (encoded w.castSucc.castSucc f.castSucc.castSucc a.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc L.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise, encoded_rename]) (SyntaxRenameBinders.under_2 he B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hg := Derives.impE (.conjR (edges _ _ _ _ _ _ _ _ he2)) hB
  exact SyntaxTermImageSyntax.image_type _ _ _ _ _ _ _ (.conjL he2) hg

theorem from_fields {m} {Γ : Context m} (w f a c d L : Fin m)
    (hL : Derives Γ (termList w a c d L)) (hf : Derives Γ (fields w L a f)) : Derives Γ (encoded w f a c d L) := by
  have hm : Derives Γ (imageMap w f a c d) := by
    apply Derives.conjI (.conjL hL)
    apply Derives.conjI (.conjL (.conjR hL))
    apply Derives.conjI (.conjL hf)
    apply Derives.allI
    apply Derives.allI
    apply Derives.impI
    let E := edge f.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
    let Δ := Context.add E (Context.image Formula.raise (Context.image Formula.raise Γ))
    have ht2 : Derives Δ (typedFields w.castSucc.castSucc a.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc L.castSucc.castSucc) :=
      of_eq (by simp only [Formula.raise, typedFields_rename]) (SyntaxRenameBinders.under_2 (.conjR (.conjR (.conjR hL))) E)
    have hf2 : Derives Δ (fields w.castSucc.castSucc L.castSucc.castSucc a.castSucc.castSucc f.castSucc.castSucc) :=
      of_eq (by simp only [Formula.raise, fields_rename]) (SyntaxRenameBinders.under_2 hf E)
    have hb := Derives.impE (.conjL (law_at _ _ _ _ _ _ (.conjR (.conjR hf2)))) (.hyp (Or.inl rfl))
    exact .impE (typed_at _ _ _ _ _ _ _ ht2) hb
  exact .conjI hm (.conjI (.conjL (.conjR (.conjR hL))) hf)

theorem field_type {m} {Γ : Context m} (w a c d L i q : Fin m) (hL : Derives Γ (termList w a c d L))
    (hi : Derives Γ (.mem i a)) (hq : Derives Γ (field w L i q)) : Derives Γ (SyntaxTermSyntax.term w c d q) :=
  .impE (typed_at w a c d L i q (.conjR (.conjR (.conjR hL)))) (.conjI hi hq)

end PPAC.Migration.Internal.SyntaxMixedImageCodeFields
