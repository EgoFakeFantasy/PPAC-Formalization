import PPAC.Migration.Internal.SyntaxCodedMixedTermFiber

/-! 混合项替换的已知源变量码精确读取原对应环境列表字段；输出项类别不受源类别限制。 -/
namespace PPAC.Migration.Internal.SyntaxCodedMixedTermFields
open Source SourceAlgebra SourceLogic OmegaSyntax GraphSyntax SyntaxRenameQuerySyntax SyntaxCodedMixedTermSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem selected_encoded {m} {Γ : Context m} (bound : Bool) (w r s a b c d R S : Fin m)
    (he : Derives Γ (SyntaxMixedImageCodeSyntax.encodings w r s a b c d R S)) :
    Derives Γ (SyntaxMixedImageCodeSyntax.encoded w (SyntaxIndexMapSyntax.selectMap bound r s)
      (SyntaxTermSyntax.limit bound a b) c d (SyntaxIndexMapSyntax.selectMap bound R S)) := by
  cases bound
  · exact .conjR he
  · exact .conjL he

theorem at_field {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (bound : Bool) (w R S a b c d n q i : Fin m)
    (hw : Derives Γ (omega w)) (hL : Derives Γ (SyntaxMixedImageCodeSyntax.termLists w a b c d R S))
    (hn : Derives Γ (SyntaxVariableSyntax.code bound w i n)) :
    Derives Γ ((substituted w R S a b c d n q).iff ((Formula.mem i (SyntaxTermSyntax.limit bound a b)).conj
      (StructuralListFieldSyntax.field w (SyntaxIndexMapSyntax.selectMap bound R S) i q))) := by
  let G := SyntaxMixedImageCodePairs.graphBody w a b c d R S
  let Δ := Context.add G (Context.image Formula.raise (Context.image Formula.raise Γ))
  have he : Derives Γ (.ex (.ex G)) := SyntaxMixedImageCodePairs.exists_graphs hZ w a b c d R S hw hL
  apply SyntaxRenameBinders.eliminate_2 G _ he
  have hZ2 := SyntaxRenameBinders.zf_under_2 hZ G
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxRenameBinders.under_2 hw G)
  have hn2 : Derives Δ (SyntaxVariableSyntax.code bound w.castSucc.castSucc i.castSucc.castSucc n.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxVariableSyntax.code_rename]) (SyntaxRenameBinders.under_2 hn G)
  have hG : Derives Δ G := .hyp (Or.inl rfl)
  have hm := SyntaxMixedImageCodePairs.image_maps _ _ _ _ _ _ _ _ _ hG
  have hc := SyntaxCodedMixedTermGraphs.at_graphs_iff hZ2 w.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc n.castSucc.castSucc q.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) hG
  have hk := SyntaxMixedTermKnown.at_code hZ2 bound w.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc n.castSucc.castSucc q.castSucc.castSucc i.castSucc.castSucc hw2 hm hn2
  have hf := SyntaxMixedImageCodeFields.edges _ _ _ _ _ _ i.castSucc.castSucc q.castSucc.castSucc
    (selected_encoded bound w.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc hG)
  have ho : Derives Δ ((substituted w.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc n.castSucc.castSucc q.castSucc.castSucc).iff
    ((Formula.mem i.castSucc.castSucc (SyntaxTermSyntax.limit bound a.castSucc.castSucc b.castSucc.castSucc)).conj
      (StructuralListFieldSyntax.field w.castSucc.castSucc (SyntaxIndexMapSyntax.selectMap bound R.castSucc.castSucc S.castSucc.castSucc) i.castSucc.castSucc q.castSucc.castSucc))) := by
    apply Derives.conjI
    · apply Derives.impI
      have ht := Derives.impE (add (.conjL hk) _) (.impE (add (.conjL hc) _) (.hyp (Or.inl rfl)))
      exact .impE (add (.conjL hf) _) (.conjR ht)
    · apply Derives.impI
      have h : Derives (Context.add ((Formula.mem i.castSucc.castSucc (SyntaxTermSyntax.limit bound a.castSucc.castSucc b.castSucc.castSucc)).conj
        (StructuralListFieldSyntax.field w.castSucc.castSucc (SyntaxIndexMapSyntax.selectMap bound R.castSucc.castSucc S.castSucc.castSucc) i.castSucc.castSucc q.castSucc.castSucc)) Δ)
        ((Formula.mem i.castSucc.castSucc (SyntaxTermSyntax.limit bound a.castSucc.castSucc b.castSucc.castSucc)).conj
        (StructuralListFieldSyntax.field w.castSucc.castSucc (SyntaxIndexMapSyntax.selectMap bound R.castSucc.castSucc S.castSucc.castSucc) i.castSucc.castSucc q.castSucc.castSucc)) := .hyp (Or.inl rfl)
      exact .impE (add (.conjR hc) _) (.impE (add (.conjR hk) _) (.conjI (.conjL h) (.impE (add (.conjR hf) _) h)))
  exact of_eq (by simp only [Formula.raise, Formula.iff, Formula.rename, substituted_rename, SyntaxTermSyntax.limit_map,
    StructuralListFieldSyntax.field_rename, SyntaxIndexMapSyntax.selectMap_map]) ho

end PPAC.Migration.Internal.SyntaxCodedMixedTermFields
