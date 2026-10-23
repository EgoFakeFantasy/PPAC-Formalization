import PPAC.Migration.Internal.SyntaxVariableTableExistence

/-! 实际变量项码表的准确像类型和见证无关唯一性。 -/
namespace PPAC.Migration.Internal.SyntaxVariableTableUnique
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxRenameQuerySyntax SyntaxVariableTableSyntax
open SyntaxTermSyntax (limit limit_map)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem identity_type {m} {Γ : Context m} (bound : Bool) (w c d f : Fin m)
    (hf : Derives Γ (identity bound w c d f)) :
    Derives Γ (SyntaxTermImageSyntax.imageMap w f (limit bound c d) c d) := by
  let B := identityBody bound w c d f
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) hf
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have ht := Derives.conjL (.conjR (.conjR hB))
  exact of_eq (by simp only [Formula.raise, SyntaxTermImageSyntax.imageMap_rename, limit_map]) ht

theorem identity_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (bound : Bool) (w c d f g : Fin m)
    (hf : Derives Γ (identity bound w c d f)) (hg : Derives Γ (identity bound w c d g)) : Derives Γ (.equal f g) := by
  let B := identityBody bound w c d f
  let Ξ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) hf
  have hg1 : Derives Ξ (identity bound w.castSucc c.castSucc d.castSucc g.castSucc) := of_eq (identity_rename bound w c d g Fin.castSucc) (under hg B)
  let C := identityBody bound w.castSucc c.castSucc d.castSucc g.castSucc
  let Δ := Context.add C (Context.image Formula.raise Ξ)
  apply Derives.exE (p := C) hg1
  have hZ2 := ZFContext.under (ZFContext.under hZ B) C
  have hB : Derives Ξ B := .hyp (Or.inl rfl)
  have hb2 : Derives Δ ((SyntaxIdentityMapSyntax.identityMap w.castSucc.castSucc (limit bound c.castSucc.castSucc d.castSucc.castSucc) (Fin.last m).castSucc).conj
      (SyntaxVariableImageSyntax.mapped bound w.castSucc.castSucc (Fin.last m).castSucc (limit bound c.castSucc.castSucc d.castSucc.castSucc) c.castSucc.castSucc d.castSucc.castSucc f.castSucc.castSucc)) :=
    of_eq (by simp only [B, identityBody, Formula.raise, Formula.rename, SyntaxIdentityMapSyntax.identityMap_rename, SyntaxVariableImageSyntax.mapped_rename, limit_map]) (under hB C)
  have hC : Derives Δ C := .hyp (Or.inl rfl)
  have he := SyntaxIdentityUnique.map_unique hZ2 w.castSucc.castSucc (limit bound c.castSucc.castSucc d.castSucc.castSucc) (Fin.last m).castSucc (Fin.last (m+1)) (.conjL hb2) (.conjL hC)
  have hm := SyntaxVariableImageFields.mapped_subst_index_graph bound w.castSucc.castSucc (Fin.last m).castSucc (limit bound c.castSucc.castSucc d.castSucc.castSucc) c.castSucc.castSucc d.castSucc.castSucc f.castSucc.castSucc (Fin.last (m+1)) he (.conjR hb2)
  exact SyntaxVariableImageGraph.unique hZ2 bound w.castSucc.castSucc (Fin.last (m+1)) (limit bound c.castSucc.castSucc d.castSucc.castSucc) c.castSucc.castSucc d.castSucc.castSucc f.castSucc.castSucc g.castSucc.castSucc hm (.conjR hC)

theorem shifted_type {m} {Γ : Context m} (bound : Bool) (w a c d f : Fin m)
    (hf : Derives Γ (shifted bound w a c d f)) :
    Derives Γ (SyntaxTermImageSyntax.imageMap w f (a) c d) := by
  let B := shiftedBody bound w a c d f
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) hf
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have ht := Derives.conjL (.conjR (.conjR hB))
  exact of_eq (by simp only [Formula.raise, SyntaxTermImageSyntax.imageMap_rename]) ht

theorem shifted_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (bound : Bool) (w a c d f g : Fin m)
    (hf : Derives Γ (shifted bound w a c d f)) (hg : Derives Γ (shifted bound w a c d g)) : Derives Γ (.equal f g) := by
  let B := shiftedBody bound w a c d f
  let Ξ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) hf
  have hg1 : Derives Ξ (shifted bound w.castSucc a.castSucc c.castSucc d.castSucc g.castSucc) := of_eq (shifted_rename bound w a c d g Fin.castSucc) (under hg B)
  let C := shiftedBody bound w.castSucc a.castSucc c.castSucc d.castSucc g.castSucc
  let Δ := Context.add C (Context.image Formula.raise Ξ)
  apply Derives.exE (p := C) hg1
  have hZ2 := ZFContext.under (ZFContext.under hZ B) C
  have hB : Derives Ξ B := .hyp (Or.inl rfl)
  have hb2 : Derives Δ ((SyntaxFreeShiftSyntax.shiftMap w.castSucc.castSucc a.castSucc.castSucc (limit bound c.castSucc.castSucc d.castSucc.castSucc) (Fin.last m).castSucc).conj
      (SyntaxVariableImageSyntax.mapped bound w.castSucc.castSucc (Fin.last m).castSucc a.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc f.castSucc.castSucc)) :=
    of_eq (by simp only [B, shiftedBody, Formula.raise, Formula.rename, SyntaxFreeShiftSyntax.shiftMap_rename, SyntaxVariableImageSyntax.mapped_rename, limit_map]) (under hB C)
  have hC : Derives Δ C := .hyp (Or.inl rfl)
  have he := SyntaxFreeShiftGraph.unique_map hZ2 w.castSucc.castSucc a.castSucc.castSucc (limit bound c.castSucc.castSucc d.castSucc.castSucc) (Fin.last m).castSucc (Fin.last (m+1)) (.conjL hb2) (.conjL hC)
  have hm := SyntaxVariableImageFields.mapped_subst_index_graph bound w.castSucc.castSucc (Fin.last m).castSucc a.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc f.castSucc.castSucc (Fin.last (m+1)) he (.conjR hb2)
  exact SyntaxVariableImageGraph.unique hZ2 bound w.castSucc.castSucc (Fin.last (m+1)) a.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc f.castSucc.castSucc g.castSucc.castSucc hm (.conjR hC)

theorem shifted_successor {m} {Γ : Context m} (bound : Bool) (w a c d f : Fin m)
    (hf : Derives Γ (shifted bound w a c d f)) : Derives Γ (OmegaSyntax.successor (limit bound c d) a) := by
  let B := shiftedBody bound w a c d f
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) hf
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  exact of_eq (by simp only [Formula.raise, OmegaSyntax.successor_rename, limit_map]) (.conjL (.conjL hB))

end PPAC.Migration.Internal.SyntaxVariableTableUnique
