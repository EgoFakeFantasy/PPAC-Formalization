import PPAC.Migration.Internal.IndexVariableImageReadingSyntax

/-! 全部内部字段读值合同装配成原变量像表的完整实际图关系。 -/
namespace PPAC.Migration.Internal.IndexVariableImageReading
open Source SourceAlgebra SourceLogic GraphSyntax IndexVariableImageReadingSyntax
open SyntaxRenameQuerySyntax (of_eq)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem mapped_from_reads {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (isBound : Bool) (w r a c d f : Fin m)
    (hi : Derives Γ (SyntaxVariableImageSyntax.input isBound w r a c d))
    (hf : Derives Γ (SyntaxTermImageSyntax.imageMap w f a c d)) (hr : Derives Γ (reads isBound w r f)) :
    Derives Γ (SyntaxVariableImageSyntax.mapped isBound w r a c d f) := by
  apply Derives.conjI hi
  apply Derives.conjI hf
  apply Derives.conjI (SyntaxTermImageSyntax.image_function w f a c d hf)
  apply Derives.allI
  apply Derives.allI
  apply Derives.conjI
  · apply Derives.impI
    let E := edge f.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
    let Δ := Context.add E (Context.image Formula.raise (Context.image Formula.raise Γ))
    have hZ2 := SyntaxRenameBinders.zf_under_2 hZ E
    have hi2 : Derives Δ (SyntaxVariableImageSyntax.input isBound w.castSucc.castSucc r.castSucc.castSucc a.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxVariableImageSyntax.input_rename]) (SyntaxRenameBinders.under_2 hi E)
    have hf2 : Derives Δ (SyntaxTermImageSyntax.imageMap w.castSucc.castSucc f.castSucc.castSucc a.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxTermImageSyntax.imageMap_rename]) (SyntaxRenameBinders.under_2 hf E)
    have hr2 : Derives Δ (reads isBound w.castSucc.castSucc r.castSucc.castSucc f.castSucc.castSucc) := of_eq (by simp only [Formula.raise, reads_rename]) (SyntaxRenameBinders.under_2 hr E)
    have hE : Derives Δ E := .hyp (Or.inl rfl)
    have hDomain := GraphProperties.domain_of_edge f.castSucc.castSucc a.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) (ZFContext.arithmetic hZ2).base.extensionality (SyntaxTermImageSyntax.image_function _ _ _ _ _ hf2) hE
    have hx := GraphProperties.output_exists r.castSucc.castSucc a.castSucc.castSucc (Fin.last m).castSucc (.conjL (.conjR (.conjR hi2))) hDomain
    let J := edge r.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc (Fin.last (m+2))
    let Ξ := Context.add J (Context.image Formula.raise Δ)
    apply Derives.exE hx
    have hr3 : Derives Ξ (reads isBound w.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc f.castSucc.castSucc.castSucc) := of_eq (reads_rename isBound w.castSucc.castSucc r.castSucc.castSucc f.castSucc.castSucc Fin.castSucc) (under hr2 J)
    have hf3 : Derives Ξ (SyntaxTermImageSyntax.imageMap w.castSucc.castSucc.castSucc f.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc) := of_eq (SyntaxTermImageSyntax.imageMap_rename w.castSucc.castSucc f.castSucc.castSucc a.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc Fin.castSucc) (under hf2 J)
    have hE3 : Derives Ξ (edge f.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc) := of_eq (by simp only [E, Formula.raise, edge_rename]) (under hE J)
    have hJ : Derives Ξ J := .hyp (Or.inl rfl)
    have hp := Derives.impE (at_indices isBound w.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc f.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc (Fin.last (m+2)) (Fin.last (m+1)).castSucc hr3) hJ
    have hCode := Derives.impE (.conjL hp) hE3
    have hType := SyntaxTermImageSyntax.image_type w.castSucc.castSucc.castSucc f.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc hf3 hE3
    have hValue := SyntaxVariableImageSyntax.intro_value isBound w.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc (Fin.last (m+2)) hJ hCode hType
    exact of_eq (by simp only [Formula.raise, Formula.rename, SyntaxVariableImageSyntax.value_rename]) (.conjI (under hDomain J) hValue)
  · apply Derives.impI
    let B := (Formula.mem (Fin.last m).castSucc a.castSucc.castSucc).conj (SyntaxVariableImageSyntax.value isBound w.castSucc.castSucc r.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)))
    let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise Γ))
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    let V := SyntaxVariableImageSyntax.body isBound w.castSucc.castSucc r.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
    let Ξ := Context.add V (Context.image Formula.raise Δ)
    apply Derives.exE (.conjR hB)
    have hr3 : Derives Ξ (reads isBound w.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc f.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, reads_rename]) (under (SyntaxRenameBinders.under_2 hr B) V)
    have hV : Derives Ξ V := .hyp (Or.inl rfl)
    have hp := Derives.impE (at_indices isBound w.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc f.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc (Fin.last (m+2)) (Fin.last (m+1)).castSucc hr3) (.conjL hV)
    exact of_eq (by simp only [Formula.raise, edge_rename]) (Derives.impE (.conjR hp) (.conjL (.conjR hV)))

end PPAC.Migration.Internal.IndexVariableImageReading
