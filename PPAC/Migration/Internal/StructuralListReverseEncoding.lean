import PPAC.Migration.Internal.StructuralListReverseSyntax

/-! Original exact field graph and original sequence encoding construct the actual reverse list code. -/
namespace PPAC.Migration.Internal.StructuralListReverseEncoding
open Source SourceAlgebra SourceLogic OmegaSyntax GraphSyntax HornBinderSyntax StructuralListReverseSyntax
open StructuralListLengthSyntax (hasLength hasLength_rename)
open StructuralListFieldSyntax (field field_rename)
open SyntaxRenameQuerySyntax (of_eq)

theorem at_index {m} {Γ : Context m} (w n l g r i y : Fin m)
    (hg : Derives Γ (StructuralReverseFieldSyntax.graph w n l g))
    (hf : Derives Γ (StructuralListFieldGraphSyntax.fields w r l g)) (hi : Derives Γ (.mem i l)) :
    Derives Γ ((field w r i y).iff (StructuralReverseFieldSyntax.value w n l i y)) := by
  have hF := StructuralListFieldGraphSyntax.law_at w r l g i y (.conjR (.conjR hf))
  have hG := StructuralReverseFieldSyntax.law_at w n l g i y hg
  apply Derives.conjI
  · apply Derives.impI
    have he := Derives.impE (add (.conjR hF) _) (.conjI (add hi _) (.hyp (Or.inl rfl)))
    exact .conjR (.impE (add (.conjL hG) _) he)
  · apply Derives.impI
    have he := Derives.impE (add (.conjR hG) _) (.conjI (add hi _) (.hyp (Or.inl rfl)))
    exact .conjR (.impE (add (.conjL hF) _) he)

theorem reading_from_graph {m} {Γ : Context m} (w n l g r : Fin m)
    (hg : Derives Γ (StructuralReverseFieldSyntax.graph w n l g))
    (hf : Derives Γ (StructuralListFieldGraphSyntax.fields w r l g)) : Derives Γ (reading w n l r) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  let H := Formula.mem (slot 2 0) (old 2 l)
  let Δ := Context.add H (raisedContext 2 Γ)
  have hg2 := of_eq (StructuralReverseFieldSyntax.graph_rename w n l g (old 2)) (add (HornBinderRules.under_many 2 hg) H)
  have hf2 := of_eq (StructuralListFieldGraphSyntax.fields_rename w r l g (old 2)) (add (HornBinderRules.under_many 2 hf) H)
  exact at_index (old 2 w) (old 2 n) (old 2 l) (old 2 g) (old 2 r) (slot 2 0) (slot 2 1) hg2 hf2 (.hyp (Or.inl rfl))

theorem from_encoding {m} {Γ : Context m} (w n l g r : Fin m)
    (hL : Derives Γ (hasLength w n l)) (hg : Derives Γ (StructuralReverseFieldSyntax.graph w n l g))
    (hr : Derives Γ (StructuralListEncodeSyntax.encoding w g l r)) : Derives Γ (atLength w n l r) :=
  .conjI hL (.conjI (.conjR (.conjL hr)) (reading_from_graph w n l g r hg (.conjR hr)))

theorem exists_of_length {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n l : Fin m)
    (hw : Derives Γ (omega w)) (hL : Derives Γ (hasLength w n l)) : Derives Γ (existsReverse w n) := by
  have hl := StructuralListLengthBasic.length_member w n l hL
  let R := StructuralReverseFieldSyntax.graph w.castSucc n.castSucc l.castSucc (Fin.last m)
  let Δ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) (StructuralReverseFieldGraph.exists_graph hZ w n l hw hl)
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hZ1 := ZFContext.under hZ R
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw R)
  have hl1 : Derives Δ (.mem l.castSucc w.castSucc) := under hl R
  have hL1 := of_eq (hasLength_rename w n l Fin.castSucc) (under hL R)
  have hs := StructuralReverseFieldGraph.sequence hZ1 _ _ _ _ hw1 hR
  have hex := StructuralListEncodeExistence.exists_encoding hZ1 w.castSucc (Fin.last m) l.castSucc hw1 hs hl1
  let T := StructuralListEncodeSyntax.encoding w.castSucc.castSucc (Fin.last m).castSucc l.castSucc.castSucc (Fin.last (m+1))
  let Ξ := Context.add T (Context.image Formula.raise Δ)
  apply Derives.exE (p := T) hex
  have hT : Derives Ξ T := .hyp (Or.inl rfl)
  have hg2 := of_eq (StructuralReverseFieldSyntax.graph_rename w.castSucc n.castSucc l.castSucc (Fin.last m) Fin.castSucc) (under hR T)
  have hL2 := of_eq (hasLength_rename w.castSucc n.castSucc l.castSucc Fin.castSucc) (under hL1 T)
  have ha := from_encoding _ _ _ _ _ hL2 hg2 hT
  have hr := intro_reverse _ _ _ _ (under hl1 T) ha
  simpa only [Formula.raise,existsReverse_rename] using intro_exists _ _ _ (.conjL (.conjL hT)) hr

theorem exists_reverse {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n : Fin m)
    (hw : Derives Γ (omega w)) (hv : Derives Γ (StructuralListTraceSyntax.valid w n)) : Derives Γ (existsReverse w n) := by
  let R := (Formula.mem (Fin.last m) w.castSucc).conj (hasLength w.castSucc n.castSucc (Fin.last m))
  let Δ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) (StructuralListLengthBasic.exists_length w n hv)
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw R)
  simpa only [Formula.raise,existsReverse_rename] using exists_of_length (ZFContext.under hZ R) _ _ _ hw1 (.conjR hR)

end PPAC.Migration.Internal.StructuralListReverseEncoding
