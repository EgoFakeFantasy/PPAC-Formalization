import PPAC.Migration.Internal.IndexVariableImageReading

/-! 量词提升的三个实际字段分支保持变量码读取；旧bound和free像均经真实项变换。 -/
namespace PPAC.Migration.Internal.IndexVariableBinderEdges
open Source SourceAlgebra SourceLogic OmegaSyntax GraphSyntax
open SyntaxRenameQuerySyntax (of_eq)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem zero_read {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w U V f g a b c d A C n k h z i j q : Fin m)
    (hw : Derives Γ (omega w)) (hl : Derives Γ (SyntaxMixedImageLiftSyntax.lifted w U V f g a b c d A C n k h))
    (hn : Derives Γ (SyntaxMixedImageHead.head w C d z n)) (hi : Derives Γ (empty i)) (hj : Derives Γ (empty j)) :
    Derives Γ ((edge k i q).iff (SyntaxVariableSyntax.code true w j q)) := by
  have hIndex := OmegaUniversal.empty_unique z j (ZFContext.arithmetic hZ).base.extensionality (.conjL hn) hj
  have hCode := SyntaxRenameTermSyntax.code_index_subst true w z j n hIndex (.conjL (.conjR hn))
  exact SyntaxTypeLocalTransfer.iff_trans (SyntaxMixedImageLiftFields.zero_iff hZ w U V f g a b c d A C n k h i q hl hw hi)
    (IndexVariableTermReading.equality_iff_code hZ true w j n q hw hCode)

theorem bound_read {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r f g a b c d A C n k h U V i j p l q : Fin m)
    (hw : Derives Γ (omega w)) (hm : Derives Γ (SyntaxVariableImageSyntax.mapped true w r a c d f))
    (hl : Derives Γ (SyntaxMixedImageLiftSyntax.lifted w U V f g a b c d A C n k h))
    (hU : Derives Γ (SyntaxFreeShiftSyntax.shiftMap w c C U)) (hV : Derives Γ (SyntaxIdentityMapSyntax.identityMap w d V))
    (he : Derives Γ (edge r p l)) (hi : Derives Γ (successor i p)) (hj : Derives Γ (successor j l)) :
    Derives Γ ((edge k i q).iff (SyntaxVariableSyntax.code true w j q)) := by
  have hp := SyntaxIndexMapSyntax.edge_source hZ w r a c p l (.conjR (.conjL hm)) he
  have hTarget := SyntaxIndexMapSyntax.edge_target w r a c p l (.conjR (.conjL hm)) he
  have hMaps : Derives Γ (SyntaxIndexMapSyntax.maps w U V c d C d) := .conjI (.conjL (.conjR hU)) (.conjL hV)
  have hShift : Derives Γ (edge U l j) := .impE (.conjR (SyntaxFreeShiftGraph.edge_iff c U l j (SyntaxFreeShiftGraph.to_graph w c C U hU))) (.conjI hTarget hj)
  have hx := GraphProperties.output_exists f a p (SyntaxTermImageSyntax.image_function w f a c d (.conjL (.conjR hm))) hp
  let T := edge f.castSucc p.castSucc (Fin.last m)
  let Δ := Context.add T (Context.image Formula.raise Γ)
  apply Derives.exE hx
  have hZ1 := ZFContext.under hZ T
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw T)
  have hm1 : Derives Δ (SyntaxVariableImageSyntax.mapped true w.castSucc r.castSucc a.castSucc c.castSucc d.castSucc f.castSucc) := of_eq (SyntaxVariableImageSyntax.mapped_rename true w r a c d f Fin.castSucc) (under hm T)
  have hl1 : Derives Δ (SyntaxMixedImageLiftSyntax.lifted w.castSucc U.castSucc V.castSucc f.castSucc g.castSucc a.castSucc b.castSucc c.castSucc d.castSucc A.castSucc C.castSucc n.castSucc k.castSucc h.castSucc) := of_eq (SyntaxMixedImageLiftSyntax.lifted_rename w U V f g a b c d A C n k h Fin.castSucc) (under hl T)
  have he1 : Derives Δ (edge r.castSucc p.castSucc l.castSucc) := of_eq (edge_rename r p l Fin.castSucc) (under he T)
  have hi1 : Derives Δ (successor i.castSucc p.castSucc) := of_eq (successor_rename i p Fin.castSucc) (under hi T)
  have hMaps1 : Derives Δ (SyntaxIndexMapSyntax.maps w.castSucc U.castSucc V.castSucc c.castSucc d.castSucc C.castSucc d.castSucc) := of_eq (SyntaxIndexMapSyntax.maps_rename w U V c d C d Fin.castSucc) (under hMaps T)
  have hShift1 : Derives Δ (edge U.castSucc l.castSucc j.castSucc) := of_eq (edge_rename U l j Fin.castSucc) (under hShift T)
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  have hCode := Derives.impE (.conjL (SyntaxVariableImageFields.at_index hZ1 true w.castSucc r.castSucc a.castSucc c.castSucc d.castSucc f.castSucc p.castSucc l.castSucc (Fin.last m) hm1 he1)) hT
  have hNew := SyntaxMixedImageLiftFields.bound_iff hZ1 w.castSucc U.castSucc V.castSucc f.castSucc g.castSucc a.castSucc b.castSucc c.castSucc d.castSucc A.castSucc C.castSucc n.castSucc k.castSucc h.castSucc i.castSucc p.castSucc (Fin.last m) q.castSucc hl1 hw1 (under hp T) hi1 hT
  have hOld := IndexVariableTermReading.source_iff hZ1 true w.castSucc U.castSucc V.castSucc c.castSucc d.castSucc C.castSucc d.castSucc (Fin.last m) q.castSucc l.castSucc j.castSucc hw1 hMaps1 hCode hShift1
  exact of_eq (by simp only [Formula.raise, Formula.iff, Formula.rename, edge_rename, SyntaxVariableSyntax.code_rename]) (SyntaxTypeLocalTransfer.iff_trans hNew hOld)

theorem free_read {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w s f g a b c d A C n k h U V i j q : Fin m)
    (hw : Derives Γ (omega w)) (hm : Derives Γ (SyntaxVariableImageSyntax.mapped false w s b c d g))
    (hl : Derives Γ (SyntaxMixedImageLiftSyntax.lifted w U V f g a b c d A C n k h))
    (hU : Derives Γ (SyntaxFreeShiftSyntax.shiftMap w c C U)) (hV : Derives Γ (SyntaxIdentityMapSyntax.identityMap w d V))
    (he : Derives Γ (edge s i j)) : Derives Γ ((edge h i q).iff (SyntaxVariableSyntax.code false w j q)) := by
  have hi := SyntaxIndexMapSyntax.edge_source hZ w s b d i j (.conjR (.conjL hm)) he
  have hj := SyntaxIndexMapSyntax.edge_target w s b d i j (.conjR (.conjL hm)) he
  have hMaps : Derives Γ (SyntaxIndexMapSyntax.maps w U V c d C d) := .conjI (.conjL (.conjR hU)) (.conjL hV)
  have hId : Derives Γ (edge V j j) := SyntaxIdentityUnique.diagonal_edge w d V j (.conjL hV) (.conjR hV) hj
  have hx := GraphProperties.output_exists g b i (SyntaxTermImageSyntax.image_function w g b c d (.conjL (.conjR hm))) hi
  let T := edge g.castSucc i.castSucc (Fin.last m)
  let Δ := Context.add T (Context.image Formula.raise Γ)
  apply Derives.exE hx
  have hZ1 := ZFContext.under hZ T
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw T)
  have hm1 : Derives Δ (SyntaxVariableImageSyntax.mapped false w.castSucc s.castSucc b.castSucc c.castSucc d.castSucc g.castSucc) := of_eq (SyntaxVariableImageSyntax.mapped_rename false w s b c d g Fin.castSucc) (under hm T)
  have hl1 : Derives Δ (SyntaxMixedImageLiftSyntax.lifted w.castSucc U.castSucc V.castSucc f.castSucc g.castSucc a.castSucc b.castSucc c.castSucc d.castSucc A.castSucc C.castSucc n.castSucc k.castSucc h.castSucc) := of_eq (SyntaxMixedImageLiftSyntax.lifted_rename w U V f g a b c d A C n k h Fin.castSucc) (under hl T)
  have he1 : Derives Δ (edge s.castSucc i.castSucc j.castSucc) := of_eq (edge_rename s i j Fin.castSucc) (under he T)
  have hMaps1 : Derives Δ (SyntaxIndexMapSyntax.maps w.castSucc U.castSucc V.castSucc c.castSucc d.castSucc C.castSucc d.castSucc) := of_eq (SyntaxIndexMapSyntax.maps_rename w U V c d C d Fin.castSucc) (under hMaps T)
  have hId1 : Derives Δ (edge V.castSucc j.castSucc j.castSucc) := of_eq (edge_rename V j j Fin.castSucc) (under hId T)
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  have hCode := Derives.impE (.conjL (SyntaxVariableImageFields.at_index hZ1 false w.castSucc s.castSucc b.castSucc c.castSucc d.castSucc g.castSucc i.castSucc j.castSucc (Fin.last m) hm1 he1)) hT
  have hNew := SyntaxMixedImageLiftFields.free_iff hZ1 w.castSucc U.castSucc V.castSucc f.castSucc g.castSucc a.castSucc b.castSucc c.castSucc d.castSucc A.castSucc C.castSucc n.castSucc k.castSucc h.castSucc i.castSucc (Fin.last m) q.castSucc hl1 hT
  have hOld := IndexVariableTermReading.source_iff hZ1 false w.castSucc U.castSucc V.castSucc c.castSucc d.castSucc C.castSucc d.castSucc (Fin.last m) q.castSucc j.castSucc j.castSucc hw1 hMaps1 hCode hId1
  exact of_eq (by simp only [Formula.raise, Formula.iff, Formula.rename, edge_rename, SyntaxVariableSyntax.code_rename]) (SyntaxTypeLocalTransfer.iff_trans hNew hOld)

end PPAC.Migration.Internal.IndexVariableBinderEdges
