import PPAC.Migration.Internal.IndexFormulaRenameBridge

/-! 原自由替换项图在任意目标bound长度下仍是同一实际变量项像图。 -/
namespace PPAC.Migration.Internal.FreeSubstImageGraph
open Source SourceAlgebra SourceLogic OmegaSyntax GraphSyntax
open SyntaxRenameQuerySyntax (of_eq)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem image_map {m} {Γ : Context m} (w f a c d : Fin m)
    (hc : Derives Γ (.mem c w)) (hf : Derives Γ (SyntaxFreeSubstSyntax.termGraph w f a d)) :
    Derives Γ (SyntaxTermImageSyntax.imageMap w f a c d) := by
  apply Derives.conjI (.conjL (.conjL hf))
  apply Derives.conjI (.conjI hc (.conjR (.conjL hf)))
  apply Derives.conjI (.conjL (.conjR hf))
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  let E := edge f.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
  let Δ := Context.add E (Context.image Formula.raise (Context.image Formula.raise Γ))
  have hf2 : Derives Δ (SyntaxFreeSubstSyntax.termGraph w.castSucc.castSucc f.castSucc.castSucc a.castSucc.castSucc d.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxFreeSubstSyntax.termGraph_rename]) (SyntaxRenameBinders.under_2 hf E)
  have hc2 : Derives Δ (.mem c.castSucc.castSucc w.castSucc.castSucc) := SyntaxRenameBinders.under_2 hc E
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have hv := Derives.impE (SyntaxFreeSubstSyntax.values_at w.castSucc.castSucc f.castSucc.castSucc d.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) (.conjR (.conjR hf2))) hE
  exact .conjI (.conjI hc2 (.conjR (.conjL hf2))) (.disjR hv)

theorem read_at_edge {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r a d f i j q : Fin m)
    (hm : Derives Γ (SyntaxIndexMapSyntax.indexMap w r a d))
    (hg : Derives Γ (SyntaxFreeSubstSyntax.encodedGraph w r a f)) (he : Derives Γ (edge r i j)) :
    Derives Γ ((edge f i q).iff (SyntaxVariableSyntax.code false w j q)) := by
  apply Derives.conjI
  · apply Derives.impI
    let E := edge f i q
    let Ξ := Context.add E Γ
    have hE : Derives Ξ E := .hyp (Or.inl rfl)
    have hx := Derives.conjR (.impE (.conjL (SyntaxFreeSubstBridge.encoded_law w r a f i q (add hg E))) hE)
    let B := (edge r.castSucc i.castSucc (Fin.last m)).conj (SyntaxVariableSyntax.code false w.castSucc (Fin.last m) q.castSucc)
    let Δ := Context.add B (Context.image Formula.raise Ξ)
    apply Derives.exE (p := B) hx
    have hm1 : Derives Δ (SyntaxIndexMapSyntax.indexMap w.castSucc r.castSucc a.castSucc d.castSucc) := of_eq (SyntaxIndexMapSyntax.indexMap_rename w r a d Fin.castSucc) (under (add hm E) B)
    have he1 : Derives Δ (edge r.castSucc i.castSucc j.castSucc) := of_eq (edge_rename r i j Fin.castSucc) (under (add he E) B)
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have hEq := GraphProperties.single_valued r.castSucc a.castSucc i.castSucc (Fin.last m) j.castSucc (ZFContext.arithmetic (ZFContext.under (ZFContext.add hZ E) B)).base.extensionality (.conjL (.conjR hm1)) (.conjL hB) he1
    exact of_eq (SyntaxVariableSyntax.code_rename false w j q Fin.castSucc).symm
      (SyntaxRenameTermSyntax.code_index_subst false w.castSucc (Fin.last m) j.castSucc q.castSucc hEq (.conjR hB))
  · apply Derives.impI
    let V := SyntaxVariableSyntax.code false w j q
    have hi := SyntaxIndexMapSyntax.edge_source (ZFContext.add hZ V) w r a d i j (add hm V) (add he V)
    exact .impE (.conjR (SyntaxFreeSubstBridge.encoded_law w r a f i q (add hg V)))
      (.conjI hi (SyntaxFreeSubstSyntax.intro_encoded w r i q j (add he V) (.hyp (Or.inl rfl))))

theorem reads {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r a d f : Fin m)
    (hm : Derives Γ (SyntaxIndexMapSyntax.indexMap w r a d))
    (hg : Derives Γ (SyntaxFreeSubstSyntax.encodedGraph w r a f)) :
    Derives Γ (IndexVariableImageReadingSyntax.reads false w r f) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  let E := edge r.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc
  let Δ := Context.add E (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise Γ)))
  have hm3 : Derives Δ (SyntaxIndexMapSyntax.indexMap w.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxIndexMapSyntax.indexMap_rename]) (IndexFormulaRenameBinders.under_three hm E)
  have hg3 : Derives Δ (SyntaxFreeSubstSyntax.encodedGraph w.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc f.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxFreeSubstSyntax.encodedGraph_rename]) (IndexFormulaRenameBinders.under_three hg E)
  exact read_at_edge (IndexFormulaRenameBinders.zf_under_three hZ E) w.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc f.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc (Fin.last (m+2)) hm3 hg3 (.hyp (Or.inl rfl))

theorem mapped {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r f a c d : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (.mem c w))
    (hv : Derives Γ (SyntaxFreeSubstSyntax.conversion w f a d r)) :
    Derives Γ (SyntaxVariableImageSyntax.mapped false w r a c d f) := by
  have hm := image_map w f a c d hc (.conjL hv)
  have hg := SyntaxFreeSubstRoundTrip.decoded_implies_encoded hZ w r a d f hw (.conjL hv) (.conjR (.conjR hv))
  exact IndexVariableImageReading.mapped_from_reads hZ false w r a c d f
    (.conjI (.conjI hc (.conjR (.conjL (.conjL hv)))) (.conjL (.conjR hv))) hm
    (reads hZ w r a d f (.conjL (.conjR hv)) hg)

end PPAC.Migration.Internal.FreeSubstImageGraph
