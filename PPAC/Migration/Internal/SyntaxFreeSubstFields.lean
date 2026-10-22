import PPAC.Migration.Internal.SyntaxFreeSubstFiber

/-! 原项码列表的真实字段与任意实际MapCode解码图精确对应。 -/
namespace PPAC.Migration.Internal.SyntaxFreeSubstFields
open Source SourceAlgebra SourceLogic OmegaSyntax GraphSyntax SyntaxRenameQuerySyntax SyntaxFreeSubstSyntax
open StructuralListEncodeSyntax (encoding encoding_rename)
open StructuralListFieldSyntax (field field_rename)
open SyntaxMapCodeSyntax (encoded encoded_rename)
open SyntaxVariableSyntax (code code_rename)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem at_graph {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a c L S r : Fin m)
    (hc : Derives Γ (codeConversion w a c L S)) (hr : Derives Γ (encoded w r a c S)) :
    Derives Γ (.ex ((encoding w.castSucc (Fin.last m) a.castSucc L.castSucc).conj
      (conversion w.castSucc (Fin.last m) a.castSucc c.castSucc r.castSucc))) := by
  let H := codeBody w a c L S
  let Δ := Context.add H (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply eliminate_code_conversion w a c L S _ hc
  have hr2 : Derives Δ (encoded w.castSucc.castSucc r.castSucc.castSucc a.castSucc.castSucc c.castSucc.castSucc S.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise, encoded_rename]) (SyntaxRenameBinders.under_2 hr H)
  have hH : Derives Δ H := .hyp (Or.inl rfl)
  have er := SyntaxMapCode.unique_graph (SyntaxRenameBinders.zf_under_2 hZ H) _ _ _ _ _ _ (.conjR (.conjR hH)) hr2
  have hconv := SyntaxFreeSubstCodeUnique.subst_r _ _ _ _ _ _ er (.conjL (.conjR hH))
  have ho : Derives Δ (.ex ((encoding w.castSucc.castSucc.castSucc (Fin.last (m+2)) a.castSucc.castSucc.castSucc L.castSucc.castSucc.castSucc).conj
      (conversion w.castSucc.castSucc.castSucc (Fin.last (m+2)) a.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc))) := by
    apply Derives.exI (Fin.last m).castSucc
    exact of_eq (by simp only [Formula.instantiate, Formula.rename, encoding_rename, conversion_rename,
      Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI (.conjL hH) hconv)
  exact of_eq (by simp only [Formula.raise, Formula.rename, encoding_rename, conversion_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]) ho

theorem field_at_code {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a c L S r i j t : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (codeConversion w a c L S))
    (hr : Derives Γ (encoded w r a c S)) (ht : Derives Γ (code false w j t)) :
    Derives Γ ((edge r i j).iff ((Formula.mem i a).conj (field w L i t))) := by
  let F := (encoding w.castSucc (Fin.last m) a.castSucc L.castSucc).conj
    (conversion w.castSucc (Fin.last m) a.castSucc c.castSucc r.castSucc)
  let Δ := Context.add F (Context.image Formula.raise Γ)
  apply Derives.exE (p := F) (at_graph hZ w a c L S r hc hr)
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw F)
  have ht1 : Derives Δ (code false w.castSucc j.castSucc t.castSucc) := of_eq (code_rename false w j t Fin.castSucc) (under ht F)
  have hF : Derives Δ F := .hyp (Or.inl rfl)
  have hk := SyntaxFreeSubstBridge.decoded_at_code (ZFContext.under hZ F) w.castSucc (Fin.last m) a.castSucc c.castSucc r.castSucc i.castSucc j.castSucc t.castSucc
    hw1 (.conjL (.conjR hF)) (.conjR (.conjR (.conjR hF))) ht1
  have hf := StructuralListFieldGraphSyntax.law_at w.castSucc L.castSucc a.castSucc (Fin.last m) i.castSucc t.castSucc
    (.conjR (.conjR (.conjR (.conjL hF))))
  have ho := SyntaxTypeLocalTransfer.iff_trans (.conjI (.conjR hk) (.conjL hk)) hf
  exact of_eq (by simp only [Formula.raise, Formula.iff, Formula.rename, edge_rename, field_rename]) ho

theorem field_is_free {m} {Γ : Context m} (w a c L i t : Fin m)
    (hL : Derives Γ (termList w a c L)) (hi : Derives Γ (.mem i a)) (ht : Derives Γ (field w L i t)) :
    Derives Γ (SyntaxTermSyntax.branch false w c t) := by
  let F := listBody w a c L
  let Δ := Context.add F (Context.image Formula.raise Γ)
  apply Derives.exE (p := F) hL
  have hF : Derives Δ F := .hyp (Or.inl rfl)
  have ht1 : Derives Δ (field w.castSucc L.castSucc i.castSucc t.castSucc) := of_eq (field_rename w L i t Fin.castSucc) (under ht F)
  have hf := StructuralListFieldGraphSyntax.law_at w.castSucc L.castSucc a.castSucc (Fin.last m) i.castSucc t.castSucc
    (.conjR (.conjR (.conjR (.conjL hF))))
  have he := Derives.impE (.conjR hf) (.conjI (under hi F) ht1)
  have hb := Derives.impE (values_at w.castSucc (Fin.last m) c.castSucc i.castSucc t.castSucc (.conjR (.conjR (.conjR hF)))) he
  exact of_eq (SyntaxTermSyntax.branch_rename false w c t Fin.castSucc).symm hb

end PPAC.Migration.Internal.SyntaxFreeSubstFields
