import PPAC.Migration.Internal.SyntaxMixedImageCodeFields

/-! 每个内部合法混合项像表有实际原列表码；每个纯合法原列表有实际完整项像解码图。 -/
namespace PPAC.Migration.Internal.SyntaxMixedImageCodeExistence
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxRenameQuerySyntax SyntaxMixedImageCodeSyntax
open SyntaxTermImageSyntax (imageMap imageMap_rename)
open StructuralListEncodeSyntax (encoding encoding_rename)
open StructuralListFieldGraphSyntax (fields fields_rename)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem exists_code {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w f a c d : Fin m)
    (hw : Derives Γ (omega w)) (hf : Derives Γ (imageMap w f a c d)) : Derives Γ (existsCode w f a c d) := by
  let L := encoding w.castSucc f.castSucc a.castSucc (Fin.last m)
  let Δ := Context.add L (Context.image Formula.raise Γ)
  apply Derives.exE (p := L) (StructuralListEncodeExistence.exists_encoding hZ w f a hw (SyntaxTermImageSyntax.image_sequence _ _ _ _ _ hf) (.conjL hf))
  have hf1 : Derives Δ (imageMap w.castSucc f.castSucc a.castSucc c.castSucc d.castSucc) := of_eq (imageMap_rename w f a c d Fin.castSucc) (under hf L)
  have hL : Derives Δ L := .hyp (Or.inl rfl)
  have ho := intro_code w.castSucc f.castSucc a.castSucc c.castSucc d.castSucc (Fin.last m) (.conjI hf1 hL)
  exact of_eq (existsCode_rename w f a c d Fin.castSucc).symm ho

theorem exists_graph {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a c d L : Fin m)
    (hw : Derives Γ (omega w)) (hL : Derives Γ (termList w a c d L)) : Derives Γ (existsGraph w a c d L) := by
  let G := (fields w.castSucc L.castSucc a.castSucc (Fin.last m)).conj (.all
    ((StructuralListFieldPairSyntax.graph w.castSucc.castSucc L.castSucc.castSucc a.castSucc.castSucc (Fin.last (m+1))).imp
      (.equal (Fin.last (m+1)) (Fin.last m).castSucc)))
  let Δ := Context.add G (Context.image Formula.raise Γ)
  apply Derives.exE (p := G) (StructuralListFieldGraphFiber.exists_unique hZ w L a hw (.conjL hL))
  have hl1 : Derives Δ (termList w.castSucc a.castSucc c.castSucc d.castSucc L.castSucc) := of_eq (termList_rename w a c d L Fin.castSucc) (under hL G)
  have hG : Derives Δ G := .hyp (Or.inl rfl)
  have he := SyntaxMixedImageCodeFields.from_fields w.castSucc (Fin.last m) a.castSucc c.castSucc d.castSucc L.castSucc hl1 (.conjL hG)
  exact of_eq (existsGraph_rename w a c d L Fin.castSucc).symm (intro_graph _ _ _ _ _ _ he)

theorem graph_iff_input {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a c d L : Fin m)
    (hw : Derives Γ (omega w)) : Derives Γ ((existsGraph w a c d L).iff (termList w a c d L)) := by
  apply Derives.conjI
  · apply Derives.impI
    let E := existsGraph w a c d L
    let G := encoded w.castSucc (Fin.last m) a.castSucc c.castSucc d.castSucc L.castSucc
    let Δ := Context.add G (Context.image Formula.raise (Context.add E Γ))
    apply Derives.exE (p := G) (.hyp (Or.inl rfl))
    have ho := SyntaxMixedImageCodeFields.term_list w.castSucc (Fin.last m) a.castSucc c.castSucc d.castSucc L.castSucc (Derives.hyp (Or.inl rfl) : Derives Δ G)
    exact of_eq (termList_rename w a c d L Fin.castSucc).symm ho
  · apply Derives.impI
    exact exists_graph (ZFContext.add hZ _) w a c d L (add hw _) (.hyp (Or.inl rfl))

theorem code_iff_input {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w f a c d : Fin m)
    (hw : Derives Γ (omega w)) : Derives Γ ((existsCode w f a c d).iff (imageMap w f a c d)) := by
  apply Derives.conjI
  · apply Derives.impI
    let E := existsCode w f a c d
    let L := encoded w.castSucc f.castSucc a.castSucc c.castSucc d.castSucc (Fin.last m)
    let Δ := Context.add L (Context.image Formula.raise (Context.add E Γ))
    apply Derives.exE (p := L) (.hyp (Or.inl rfl))
    exact of_eq (imageMap_rename w f a c d Fin.castSucc).symm (Derives.conjL (Derives.hyp (Or.inl rfl) : Derives Δ L))
  · apply Derives.impI
    exact exists_code (ZFContext.add hZ _) w f a c d (add hw _) (.hyp (Or.inl rfl))

end PPAC.Migration.Internal.SyntaxMixedImageCodeExistence
