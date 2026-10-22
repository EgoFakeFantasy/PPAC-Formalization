import PPAC.Migration.Internal.SyntaxFreeSubstRoundTrip

/-! 原项码列表与索引MapCode实际双向转换，不改变原替换参数格式。 -/
namespace PPAC.Migration.Internal.SyntaxFreeSubstCode
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxRenameQuerySyntax SyntaxFreeSubstSyntax
open StructuralListEncodeSyntax (encoding encoding_rename)
open SyntaxMapCodeSyntax (encoded encoded_rename mapCode mapCode_rename)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem indices_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w f a c r s : Fin m)
    (hr : Derives Γ (conversion w f a c r)) (hs : Derives Γ (conversion w f a c s)) : Derives Γ (.equal r s) :=
  SyntaxFreeSubstGraph.decode_unique hZ w f a r s (.conjR (.conjR hr)) (.conjR (.conjR hs))

theorem terms_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w f g a c r : Fin m)
    (hw : Derives Γ (omega w)) (hf : Derives Γ (conversion w f a c r)) (hg : Derives Γ (conversion w g a c r)) :
    Derives Γ (.equal f g) :=
  SyntaxFreeSubstGraph.encode_unique hZ w r a f g
    (SyntaxFreeSubstRoundTrip.decoded_implies_encoded hZ w r a c f hw (.conjL hf) (.conjR (.conjR hf)))
    (SyntaxFreeSubstRoundTrip.decoded_implies_encoded hZ w r a c g hw (.conjL hg) (.conjR (.conjR hg)))

theorem list_of_conversion {m} {Γ : Context m} (w a c L S : Fin m)
    (hc : Derives Γ (codeConversion w a c L S)) : Derives Γ (termList w a c L) := by
  let H := codeBody w a c L S
  let Δ := Context.add H (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply eliminate_code_conversion w a c L S _ hc
  have hH : Derives Δ H := .hyp (Or.inl rfl)
  have ho := intro_list w.castSucc.castSucc a.castSucc.castSucc c.castSucc.castSucc L.castSucc.castSucc (Fin.last m).castSucc
    (.conjL hH) (.conjL (.conjL (.conjR hH)))
  exact of_eq (by simp only [Formula.raise, termList_rename]) ho

theorem map_of_conversion {m} {Γ : Context m} (w a c L S : Fin m)
    (hc : Derives Γ (codeConversion w a c L S)) : Derives Γ (mapCode w a c S) := by
  let H := codeBody w a c L S
  let Δ := Context.add H (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply eliminate_code_conversion w a c L S _ hc
  have hH : Derives Δ H := .hyp (Or.inl rfl)
  have ho := SyntaxMapCodeSyntax.intro_code w.castSucc.castSucc (Fin.last (m+1)) a.castSucc.castSucc c.castSucc.castSucc S.castSucc.castSucc (.conjR (.conjR hH))
  exact of_eq (by simp only [Formula.raise, mapCode_rename]) ho

theorem from_list {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a c L : Fin m)
    (hw : Derives Γ (omega w)) (hL : Derives Γ (termList w a c L)) :
    Derives Γ (.ex (codeConversion w.castSucc a.castSucc c.castSucc L.castSucc (Fin.last m))) := by
  let F := listBody w a c L
  let Ξ := Context.add F (Context.image Formula.raise Γ)
  apply Derives.exE (p := F) hL
  have hZ1 := ZFContext.under hZ F
  have hw1 : Derives Ξ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw F)
  have hF : Derives Ξ F := .hyp (Or.inl rfl)
  let R := conversion w.castSucc.castSucc (Fin.last m).castSucc a.castSucc.castSucc c.castSucc.castSucc (Fin.last (m+1))
  let Δ := Context.add R (Context.image Formula.raise Ξ)
  apply Derives.exE (p := R) (SyntaxFreeSubstGraph.decode_exists hZ1 _ _ _ _ hw1 (.conjR hF))
  have hZ2 := ZFContext.under hZ1 R
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (omega_rename _ Fin.castSucc) (under hw1 R)
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  let S := encoded w.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc a.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc (Fin.last (m+2))
  let Θ := Context.add S (Context.image Formula.raise Δ)
  apply Derives.exE (p := S) (SyntaxMapCodeExistence.exists_code hZ2 _ _ _ _ hw2 (.conjL (.conjR hR)))
  have hl3 : Derives Θ (encoding w.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc a.castSucc.castSucc.castSucc L.castSucc.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise, encoding_rename]) (under (under (.conjL hF) R) S)
  have hr3 : Derives Θ (conversion w.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc a.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc) :=
    of_eq (by simp only [R, Formula.raise, conversion_rename]) (under hR S)
  have hS : Derives Θ S := .hyp (Or.inl rfl)
  have hc := intro_code_conversion _ _ _ _ _ _ _ hl3 hr3 hS
  have ho : Derives Θ (.ex (codeConversion w.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc L.castSucc.castSucc.castSucc.castSucc (Fin.last (m+3)))) := by
    apply Derives.exI (Fin.last (m+2))
    exact of_eq (by simp only [Formula.instantiate, codeConversion_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hc
  exact of_eq (by simp only [Formula.raise, Formula.rename, codeConversion_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]) ho

theorem from_map {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a c S : Fin m)
    (hw : Derives Γ (omega w)) (hS : Derives Γ (mapCode w a c S)) :
    Derives Γ (.ex (codeConversion w.castSucc a.castSucc c.castSucc (Fin.last m) S.castSucc)) := by
  let R := encoded w.castSucc (Fin.last m) a.castSucc c.castSucc S.castSucc
  let Ξ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) hS
  have hZ1 := ZFContext.under hZ R
  have hw1 : Derives Ξ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw R)
  have hR : Derives Ξ R := .hyp (Or.inl rfl)
  let F := (encodedGraph w.castSucc.castSucc (Fin.last m).castSucc a.castSucc.castSucc (Fin.last (m+1))).conj
    (termGraph w.castSucc.castSucc (Fin.last (m+1)) a.castSucc.castSucc c.castSucc.castSucc)
  let Δ := Context.add F (Context.image Formula.raise Ξ)
  apply Derives.exE (p := F) (SyntaxFreeSubstGraph.encode_exists hZ1 _ _ _ _ hw1 (.conjR hR))
  have hZ2 := ZFContext.under hZ1 F
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (omega_rename _ Fin.castSucc) (under hw1 F)
  have hr2 : Derives Δ (encoded w.castSucc.castSucc (Fin.last m).castSucc a.castSucc.castSucc c.castSucc.castSucc S.castSucc.castSucc) :=
    of_eq (by simp only [R, Formula.raise, encoded_rename]) (under hR F)
  have hF : Derives Δ F := .hyp (Or.inl rfl)
  have hd := SyntaxFreeSubstRoundTrip.encoded_implies_decoded hZ2 _ _ _ _ _ hw2 (.conjR hr2) (.conjL hF)
  have hconv : Derives Δ (conversion w.castSucc.castSucc (Fin.last (m+1)) a.castSucc.castSucc c.castSucc.castSucc (Fin.last m).castSucc) :=
    .conjI (.conjR hF) (.conjI (.conjR hr2) hd)
  let L := encoding w.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc a.castSucc.castSucc.castSucc (Fin.last (m+2))
  let Θ := Context.add L (Context.image Formula.raise Δ)
  apply Derives.exE (p := L) (StructuralListEncodeExistence.exists_encoding hZ2 _ _ _ hw2 (.conjL (.conjR (.conjR hF))) (.conjL (.conjL (.conjR hF))))
  have hc3 : Derives Θ (conversion w.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc a.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc) :=
    of_eq (conversion_rename _ _ _ _ _ Fin.castSucc) (under hconv L)
  have hs3 : Derives Θ (encoded w.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc a.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc S.castSucc.castSucc.castSucc) :=
    of_eq (encoded_rename _ _ _ _ _ Fin.castSucc) (under hr2 L)
  have hL : Derives Θ L := .hyp (Or.inl rfl)
  have hc := intro_code_conversion _ _ _ _ _ _ _ hL hc3 hs3
  have ho : Derives Θ (.ex (codeConversion w.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc (Fin.last (m+3)) S.castSucc.castSucc.castSucc.castSucc)) := by
    apply Derives.exI (Fin.last (m+2))
    exact of_eq (by simp only [Formula.instantiate, codeConversion_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hc
  exact of_eq (by simp only [Formula.raise, Formula.rename, codeConversion_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]) ho

end PPAC.Migration.Internal.SyntaxFreeSubstCode
