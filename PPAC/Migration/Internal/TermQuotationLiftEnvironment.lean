import PPAC.Migration.Internal.TermQuotationLiftReading

/-! 原coded混合binder的实际输出就是提升后的整张项像quotation环境。 -/
namespace PPAC.Migration.Internal.TermQuotationLiftEnvironment
open Source SourceAlgebra SourceLogic OmegaSyntax TermQuotationLiftSyntax
open SyntaxRenameQuerySyntax (of_eq)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem at_witnesses {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) {bound free : PureSyntaxQuotation.Ctx}
    (bs fs : List (PureSyntaxQuotation.Tm bound free)) (w R S a b c d A C K H U V z n : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (SyntaxNumeralSyntax.numeral bs.length a))
    (hb : Derives Γ (SyntaxNumeralSyntax.numeral fs.length b)) (hc : Derives Γ (SyntaxNumeralSyntax.numeral bound.length c))
    (hd : Derives Γ (SyntaxNumeralSyntax.numeral free.length d))
    (he : Derives Γ (TermQuotationEnvironmentSyntax.environment bs fs w a b c d R S))
    (hl : Derives Γ (SyntaxCodedMixedBinderSyntax.lifted w R S a b c d A C K H))
    (hU : Derives Γ (SyntaxFreeShiftSyntax.shiftMap w c C U)) (hV : Derives Γ (SyntaxIdentityMapSyntax.identityMap w d V))
    (hh : Derives Γ (SyntaxMixedImageHead.head w C d z n)) :
    Derives Γ (TermQuotationEnvironmentSyntax.environment (newBound bs) (shifted fs) w A b C d K H) := by
  have hInput := SyntaxCodedMixedBinderTyping.input_of_lifted w R S a b c d A C K H hl
  have hA := SyntaxNumeralSyntax.intro_succ bs.length A a ha (.conjL (.conjR hInput))
  have hANum : Derives Γ (SyntaxNumeralSyntax.numeral (newBound bs).length A) := of_eq (by simp only [newBound_length]) hA
  have hBNum : Derives Γ (SyntaxNumeralSyntax.numeral (shifted fs).length b) := of_eq (by simp only [shifted_length]) hb
  have hLists := SyntaxCodedMixedBinderTyping.output_lists w R S a b c d A C K H hl
  have hKLen : Derives Γ (StructuralListLengthSyntax.hasLength w K A) := .conjR (.conjL (.conjR (.conjR (.conjL hLists))))
  have hHLen : Derives Γ (StructuralListLengthSyntax.hasLength w H b) := .conjR (.conjL (.conjR (.conjR (.conjR hLists))))
  have hKR := TermQuotationLiftReading.bound_readings hZ bs fs w R S a b c d A C K H U V z n hw ha hc hd he hl hU hV hh
  have hHR := TermQuotationLiftReading.free_readings hZ bs fs w R S a b c d A C K H U V z n hw hb hc hd he hl hU hV hh
  have hKQ := TermImageReading.images_of_readings hZ (newBound bs) w A K hw hANum hKLen hKR
  have hHQ := TermImageReading.images_of_readings hZ (shifted fs) w b H hw hBNum hHLen hHR
  exact .conjI (.conjI hKQ hHQ) hLists

theorem at_maps {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) {bound free : PureSyntaxQuotation.Ctx}
    (bs fs : List (PureSyntaxQuotation.Tm bound free)) (w R S a b c d A C K H U V : Fin m)
    (hw : Derives Γ (omega w))
    (ha : Derives Γ (SyntaxNumeralSyntax.numeral bs.length a))
    (hb : Derives Γ (SyntaxNumeralSyntax.numeral fs.length b))
    (hc : Derives Γ (SyntaxNumeralSyntax.numeral bound.length c))
    (hd : Derives Γ (SyntaxNumeralSyntax.numeral free.length d))
    (he : Derives Γ (TermQuotationEnvironmentSyntax.environment bs fs w a b c d R S))
    (hl : Derives Γ (SyntaxCodedMixedBinderSyntax.lifted w R S a b c d A C K H))
    (hU : Derives Γ (SyntaxFreeShiftSyntax.shiftMap w c C U))
    (hV : Derives Γ (SyntaxIdentityMapSyntax.identityMap w d V)) :
    Derives Γ (TermQuotationEnvironmentSyntax.environment (newBound bs) (shifted fs) w A b C d K H) := by
  have hInput := SyntaxCodedMixedBinderTyping.input_of_lifted w R S a b c d A C K H hl
  have hcn := SyntaxNumerals.range hZ bound.length w c hw hc
  have hdn := SyntaxNumerals.range hZ free.length w d hw hd
  have hex := SyntaxMixedImageHead.exists_head hZ w c C d hw hcn hdn (.conjR (.conjR hInput))
  let B := SyntaxMixedImageHead.head w.castSucc.castSucc C.castSucc.castSucc d.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
  let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply SyntaxRenameBinders.eliminate_2 B _ hex
  have hZ2 := SyntaxRenameBinders.zf_under_2 hZ B
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxRenameBinders.under_2 hw B)
  have ha2 : Derives Δ (SyntaxNumeralSyntax.numeral bs.length a.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxNumeralSyntax.numeral_rename]) (SyntaxRenameBinders.under_2 ha B)
  have hb2 : Derives Δ (SyntaxNumeralSyntax.numeral fs.length b.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxNumeralSyntax.numeral_rename]) (SyntaxRenameBinders.under_2 hb B)
  have hc2 : Derives Δ (SyntaxNumeralSyntax.numeral bound.length c.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxNumeralSyntax.numeral_rename]) (SyntaxRenameBinders.under_2 hc B)
  have hd2 : Derives Δ (SyntaxNumeralSyntax.numeral free.length d.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxNumeralSyntax.numeral_rename]) (SyntaxRenameBinders.under_2 hd B)
  have he2 : Derives Δ (TermQuotationEnvironmentSyntax.environment bs fs w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc) := of_eq (by simp only [Formula.raise, TermQuotationEnvironmentSyntax.environment_rename]) (SyntaxRenameBinders.under_2 he B)
  have hl2 : Derives Δ (SyntaxCodedMixedBinderSyntax.lifted w.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc A.castSucc.castSucc C.castSucc.castSucc K.castSucc.castSucc H.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxCodedMixedBinderSyntax.lifted_rename]) (SyntaxRenameBinders.under_2 hl B)
  have hU2 : Derives Δ (SyntaxFreeShiftSyntax.shiftMap w.castSucc.castSucc c.castSucc.castSucc C.castSucc.castSucc U.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxFreeShiftSyntax.shiftMap_rename]) (SyntaxRenameBinders.under_2 hU B)
  have hV2 : Derives Δ (SyntaxIdentityMapSyntax.identityMap w.castSucc.castSucc d.castSucc.castSucc V.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxIdentityMapSyntax.identityMap_rename]) (SyntaxRenameBinders.under_2 hV B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have ho := at_witnesses hZ2 bs fs w.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc A.castSucc.castSucc C.castSucc.castSucc K.castSucc.castSucc H.castSucc.castSucc U.castSucc.castSucc V.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) hw2 ha2 hb2 hc2 hd2 he2 hl2 hU2 hV2 hB
  exact of_eq (by simp only [Formula.raise, TermQuotationEnvironmentSyntax.environment_rename]) ho

theorem at_lifted {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) {bound free : PureSyntaxQuotation.Ctx}
    (bs fs : List (PureSyntaxQuotation.Tm bound free)) (w R S a b c d A C K H : Fin m)
    (hw : Derives Γ (omega w))
    (ha : Derives Γ (SyntaxNumeralSyntax.numeral bs.length a))
    (hb : Derives Γ (SyntaxNumeralSyntax.numeral fs.length b))
    (hc : Derives Γ (SyntaxNumeralSyntax.numeral bound.length c))
    (hd : Derives Γ (SyntaxNumeralSyntax.numeral free.length d))
    (he : Derives Γ (TermQuotationEnvironmentSyntax.environment bs fs w a b c d R S))
    (hl : Derives Γ (SyntaxCodedMixedBinderSyntax.lifted w R S a b c d A C K H)) :
    Derives Γ (TermQuotationEnvironmentSyntax.environment (newBound bs) (shifted fs) w A b C d K H) := by
  have hInput := SyntaxCodedMixedBinderTyping.input_of_lifted w R S a b c d A C K H hl
  have hcn := SyntaxNumerals.range hZ bound.length w c hw hc
  have hex := SyntaxFreeShiftGraph.exists_map hZ w c C hw hcn (.conjR (.conjR hInput))
  let U := SyntaxFreeShiftSyntax.shiftMap w.castSucc c.castSucc C.castSucc (Fin.last m)
  let Δ1 := Context.add U (Context.image Formula.raise Γ)
  apply Derives.exE (p := U) hex
  have hZ1 := ZFContext.under hZ U
  have hw1 : Derives Δ1 (omega w.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (under hw U)
  have ha1 : Derives Δ1 (SyntaxNumeralSyntax.numeral bs.length a.castSucc) := of_eq (by simp only [Formula.raise, SyntaxNumeralSyntax.numeral_rename]) (under ha U)
  have hb1 : Derives Δ1 (SyntaxNumeralSyntax.numeral fs.length b.castSucc) := of_eq (by simp only [Formula.raise, SyntaxNumeralSyntax.numeral_rename]) (under hb U)
  have hc1 : Derives Δ1 (SyntaxNumeralSyntax.numeral bound.length c.castSucc) := of_eq (by simp only [Formula.raise, SyntaxNumeralSyntax.numeral_rename]) (under hc U)
  have hd1 : Derives Δ1 (SyntaxNumeralSyntax.numeral free.length d.castSucc) := of_eq (by simp only [Formula.raise, SyntaxNumeralSyntax.numeral_rename]) (under hd U)
  have he1 : Derives Δ1 (TermQuotationEnvironmentSyntax.environment bs fs w.castSucc a.castSucc b.castSucc c.castSucc d.castSucc R.castSucc S.castSucc) := of_eq (by simp only [Formula.raise, TermQuotationEnvironmentSyntax.environment_rename]) (under he U)
  have hl1 : Derives Δ1 (SyntaxCodedMixedBinderSyntax.lifted w.castSucc R.castSucc S.castSucc a.castSucc b.castSucc c.castSucc d.castSucc A.castSucc C.castSucc K.castSucc H.castSucc) := of_eq (by simp only [Formula.raise, SyntaxCodedMixedBinderSyntax.lifted_rename]) (under hl U)
  have hdn1 := SyntaxNumerals.range hZ1 free.length w.castSucc d.castSucc hw1 hd1
  have hvex := SyntaxIdentityGraph.exists_map hZ1 w.castSucc d.castSucc hdn1
  let V := SyntaxIdentityMapSyntax.identityMap w.castSucc.castSucc d.castSucc.castSucc (Fin.last (m+1))
  let Δ2 := Context.add V (Context.image Formula.raise Δ1)
  apply Derives.exE (p := V) hvex
  have hZ2 := ZFContext.under hZ1 V
  have hw2 : Derives Δ2 (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (under hw1 V)
  have ha2 : Derives Δ2 (SyntaxNumeralSyntax.numeral bs.length a.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxNumeralSyntax.numeral_rename]) (under ha1 V)
  have hb2 : Derives Δ2 (SyntaxNumeralSyntax.numeral fs.length b.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxNumeralSyntax.numeral_rename]) (under hb1 V)
  have hc2 : Derives Δ2 (SyntaxNumeralSyntax.numeral bound.length c.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxNumeralSyntax.numeral_rename]) (under hc1 V)
  have hd2 : Derives Δ2 (SyntaxNumeralSyntax.numeral free.length d.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxNumeralSyntax.numeral_rename]) (under hd1 V)
  have he2 : Derives Δ2 (TermQuotationEnvironmentSyntax.environment bs fs w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc) := of_eq (by simp only [Formula.raise, TermQuotationEnvironmentSyntax.environment_rename]) (under he1 V)
  have hl2 : Derives Δ2 (SyntaxCodedMixedBinderSyntax.lifted w.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc A.castSucc.castSucc C.castSucc.castSucc K.castSucc.castSucc H.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxCodedMixedBinderSyntax.lifted_rename]) (under hl1 V)
  have hU1 : Derives Δ1 U := .hyp (Or.inl rfl)
  have hu2 : Derives Δ2 (SyntaxFreeShiftSyntax.shiftMap w.castSucc.castSucc c.castSucc.castSucc C.castSucc.castSucc (Fin.last m).castSucc) := of_eq (by simp only [U, Formula.raise, SyntaxFreeShiftSyntax.shiftMap_rename]) (under hU1 V)
  have hv2 : Derives Δ2 V := .hyp (Or.inl rfl)
  have ho := at_maps hZ2 bs fs w.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc A.castSucc.castSucc C.castSucc.castSucc K.castSucc.castSucc H.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) hw2 ha2 hb2 hc2 hd2 he2 hl2 hu2 hv2
  exact of_eq (by simp only [Formula.raise, TermQuotationEnvironmentSyntax.environment_rename]) ho

end PPAC.Migration.Internal.TermQuotationLiftEnvironment
