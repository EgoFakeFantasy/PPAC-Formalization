import PPAC.Migration.Internal.SyntaxMixedImageCodeExistence
import PPAC.Migration.Internal.SyntaxFreeSubstCode

/-! 纯成员签名下空绑定界的全部内部项列表，恰是自由变量像表；所有解码图均内部存在。 -/
namespace PPAC.Migration.Internal.EmptyBoundFreeInputs
open Source SourceAlgebra SourceLogic OmegaSyntax GraphSyntax SyntaxRenameQuerySyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem term_free {m} {Γ : Context m} (w z c t : Fin m)
    (hz : Derives Γ (empty z)) (ht : Derives Γ (SyntaxTermSyntax.term w z c t)) :
    Derives Γ (SyntaxTermSyntax.branch false w c t) := by
  have hb := SyntaxTermBranches.empty true w z t hz
  apply Derives.disjE (.conjR ht)
  · exact .botE (.impE (add hb _) (.hyp (Or.inl rfl)))
  · exact .hyp (Or.inl rfl)

theorem values_free {m} {Γ : Context m} (w f z c : Fin m)
    (hz : Derives Γ (empty z)) (hv : Derives Γ (SyntaxTermImageSyntax.values w f z c)) :
    Derives Γ (SyntaxFreeSubstSyntax.values w f c) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  let E := edge f.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
  let Δ := Context.add E (Context.image Formula.raise (Context.image Formula.raise Γ))
  have hz2 : Derives Δ (empty z.castSucc.castSucc) := of_eq (by simp only [Formula.raise, empty_rename]) (SyntaxRenameBinders.under_2 hz E)
  have hv2 : Derives Δ (SyntaxTermImageSyntax.values w.castSucc.castSucc f.castSucc.castSucc z.castSucc.castSucc c.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxTermImageSyntax.values_rename]) (SyntaxRenameBinders.under_2 hv E)
  have ht := Derives.impE (SyntaxTermImageSyntax.values_at w.castSucc.castSucc f.castSucc.castSucc z.castSucc.castSucc c.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) hv2) (.hyp (Or.inl rfl))
  exact term_free w.castSucc.castSucc z.castSucc.castSucc c.castSucc.castSucc (Fin.last (m+1)) hz2 ht

theorem graph_free {m} {Γ : Context m} (w f a z c : Fin m)
    (hz : Derives Γ (empty z)) (hf : Derives Γ (SyntaxTermImageSyntax.imageMap w f a z c)) :
    Derives Γ (SyntaxFreeSubstSyntax.termGraph w f a c) :=
  .conjI (.conjI (.conjL hf) (.conjR (.conjL (.conjR hf))))
    (.conjI (SyntaxTermImageSyntax.image_sequence w f a z c hf)
      (values_free w f z c hz (.conjR (.conjR (.conjR hf)))))

theorem encoded_free {m} {Γ : Context m} (w f a z c L : Fin m)
    (hz : Derives Γ (empty z)) (he : Derives Γ (SyntaxMixedImageCodeSyntax.encoded w f a z c L)) :
    Derives Γ (SyntaxFreeSubstSyntax.termList w a c L) :=
  SyntaxFreeSubstSyntax.intro_list w a c L f (.conjR he) (graph_free w f a z c hz (.conjL he))

theorem list_free {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a z c L : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hL : Derives Γ (SyntaxMixedImageCodeSyntax.termList w a z c L)) :
    Derives Γ (SyntaxFreeSubstSyntax.termList w a c L) := by
  let B := SyntaxMixedImageCodeSyntax.encoded w.castSucc (Fin.last m) a.castSucc z.castSucc c.castSucc L.castSucc
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) (SyntaxMixedImageCodeExistence.exists_graph hZ w a z c L hw hL)
  have hz1 : Derives Δ (empty z.castSucc) := of_eq (empty_rename z Fin.castSucc) (under hz B)
  have he : Derives Δ B := .hyp (Or.inl rfl)
  exact of_eq (SyntaxFreeSubstSyntax.termList_rename w a c L Fin.castSucc).symm
    (encoded_free w.castSucc (Fin.last m) a.castSucc z.castSucc c.castSucc L.castSucc hz1 he)

theorem values_mixed {m} {Γ : Context m} (w f z c : Fin m)
    (hc : Derives Γ (SyntaxTermSyntax.contexts w z c))
    (hv : Derives Γ (SyntaxFreeSubstSyntax.values w f c)) :
    Derives Γ (SyntaxTermImageSyntax.values w f z c) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  let E := edge f.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
  let Δ := Context.add E (Context.image Formula.raise (Context.image Formula.raise Γ))
  have hc2 : Derives Δ (SyntaxTermSyntax.contexts w.castSucc.castSucc z.castSucc.castSucc c.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxTermSyntax.contexts_rename]) (SyntaxRenameBinders.under_2 hc E)
  have hv2 : Derives Δ (SyntaxFreeSubstSyntax.values w.castSucc.castSucc f.castSucc.castSucc c.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxFreeSubstSyntax.values_rename]) (SyntaxRenameBinders.under_2 hv E)
  have ht := Derives.impE (SyntaxFreeSubstSyntax.values_at w.castSucc.castSucc f.castSucc.castSucc c.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) hv2) (.hyp (Or.inl rfl))
  exact .conjI hc2 (.disjR ht)

theorem graph_mixed {m} {Γ : Context m} (w f a z c : Fin m)
    (hz : Derives Γ (.mem z w)) (hf : Derives Γ (SyntaxFreeSubstSyntax.termGraph w f a c)) :
    Derives Γ (SyntaxTermImageSyntax.imageMap w f a z c) :=
  .conjI (.conjL (.conjL hf)) (.conjI (.conjI hz (.conjR (.conjL hf)))
    (.conjI (.conjL (.conjR hf)) (values_mixed w f z c (.conjI hz (.conjR (.conjL hf))) (.conjR (.conjR hf)))))

theorem list_mixed {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a z c L : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hL : Derives Γ (SyntaxFreeSubstSyntax.termList w a c L)) :
    Derives Γ (SyntaxMixedImageCodeSyntax.termList w a z c L) := by
  have hzNat := OmegaStructureAlgebra.zero_member w z (ZFContext.arithmetic hZ).base.extensionality hw hz
  let B := SyntaxFreeSubstSyntax.listBody w a c L
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) hL
  have hz1 : Derives Δ (.mem z.castSucc w.castSucc) := under hzNat B
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hm := graph_mixed w.castSucc (Fin.last m) a.castSucc z.castSucc c.castSucc hz1 (.conjR hB)
  have ht := SyntaxMixedImageCodeFields.term_list w.castSucc (Fin.last m) a.castSucc z.castSucc c.castSucc L.castSucc (.conjI hm (.conjL hB))
  exact of_eq (SyntaxMixedImageCodeSyntax.termList_rename w a z c L Fin.castSucc).symm ht

theorem list_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a z c L : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) :
    Derives Γ ((SyntaxMixedImageCodeSyntax.termList w a z c L).iff (SyntaxFreeSubstSyntax.termList w a c L)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact list_free (ZFContext.add hZ _) w a z c L (add hw _) (add hz _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact list_mixed (ZFContext.add hZ _) w a z c L (add hw _) (add hz _) (.hyp (Or.inl rfl))

theorem conversion_exists {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a z c L : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hL : Derives Γ (SyntaxMixedImageCodeSyntax.termList w a z c L)) :
    Derives Γ (SyntaxFreeSubstFiber.mapExists w a c L) :=
  SyntaxFreeSubstCode.from_list hZ w a c L hw (list_free hZ w a z c L hw hz hL)

end PPAC.Migration.Internal.EmptyBoundFreeInputs
