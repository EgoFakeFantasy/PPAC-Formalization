import PPAC.Migration.Internal.TermQuotationLiftSyntax

/-! 整张提升项像表的对象全称字段模式；每个位置的实际旧项码均已消去。 -/
namespace PPAC.Migration.Internal.TermQuotationLiftReading
open Source SourceAlgebra SourceLogic OmegaSyntax TermQuotationLiftSyntax TermImageReadingSyntax
open SyntaxRenameQuerySyntax (of_eq)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem bound_readings {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) {bound free : PureSyntaxQuotation.Ctx}
    (bs fs : List (PureSyntaxQuotation.Tm bound free)) (w R S a b c d A C K H U V z n : Fin m)
    (hw : Derives Γ (omega w))
    (ha : Derives Γ (SyntaxNumeralSyntax.numeral bs.length a))
    (hc : Derives Γ (SyntaxNumeralSyntax.numeral bound.length c))
    (hd : Derives Γ (SyntaxNumeralSyntax.numeral free.length d))
    (he : Derives Γ (TermQuotationEnvironmentSyntax.environment bs fs w a b c d R S))
    (hl : Derives Γ (SyntaxCodedMixedBinderSyntax.lifted w R S a b c d A C K H))
    (hU : Derives Γ (SyntaxFreeShiftSyntax.shiftMap w c C U))
    (hV : Derives Γ (SyntaxIdentityMapSyntax.identityMap w d V))
    (hh : Derives Γ (SyntaxMixedImageHead.head w C d z n)) :
    Derives Γ (readings (newBound bs) w K) := by
  apply intro_rows
  intro j
  refine Fin.cases ?_ (fun k => ?_) j
  · apply Derives.allI
    apply Derives.allI
    apply Derives.impI
    let I := SyntaxNumeralSyntax.numeral 0 (Fin.last m).castSucc
    let Δ := Context.add I (Context.image Formula.raise (Context.image Formula.raise Γ))
    have hZ2 := SyntaxRenameBinders.zf_under_2 hZ I
    have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxRenameBinders.under_2 hw I)
    have hl2 : Derives Δ (SyntaxCodedMixedBinderSyntax.lifted w.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc A.castSucc.castSucc C.castSucc.castSucc K.castSucc.castSucc H.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxCodedMixedBinderSyntax.lifted_rename]) (SyntaxRenameBinders.under_2 hl I)
    have hU2 : Derives Δ (SyntaxFreeShiftSyntax.shiftMap w.castSucc.castSucc c.castSucc.castSucc C.castSucc.castSucc U.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxFreeShiftSyntax.shiftMap_rename]) (SyntaxRenameBinders.under_2 hU I)
    have hV2 : Derives Δ (SyntaxIdentityMapSyntax.identityMap w.castSucc.castSucc d.castSucc.castSucc V.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxIdentityMapSyntax.identityMap_rename]) (SyntaxRenameBinders.under_2 hV I)
    have hh2 : Derives Δ (SyntaxMixedImageHead.head w.castSucc.castSucc C.castSucc.castSucc d.castSucc.castSucc z.castSucc.castSucc n.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxMixedImageHead.head_rename]) (SyntaxRenameBinders.under_2 hh I)
    exact TermQuotationBinderValues.zero_at_numeral hZ2 w.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc A.castSucc.castSucc C.castSucc.castSucc K.castSucc.castSucc H.castSucc.castSucc U.castSucc.castSucc V.castSucc.castSucc z.castSucc.castSucc n.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) hw2 hl2 hU2 hV2 hh2 (.hyp (Or.inl rfl))
  · apply Derives.allI
    apply Derives.allI
    apply Derives.impI
    let I := SyntaxNumeralSyntax.numeral (k.val+1) (Fin.last m).castSucc
    let Δ := Context.add I (Context.image Formula.raise (Context.image Formula.raise Γ))
    have hZ2 := SyntaxRenameBinders.zf_under_2 hZ I
    have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxRenameBinders.under_2 hw I)
    have ha2 : Derives Δ (SyntaxNumeralSyntax.numeral bs.length a.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxNumeralSyntax.numeral_rename]) (SyntaxRenameBinders.under_2 ha I)
    have hc2 : Derives Δ (SyntaxNumeralSyntax.numeral bound.length c.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxNumeralSyntax.numeral_rename]) (SyntaxRenameBinders.under_2 hc I)
    have hd2 : Derives Δ (SyntaxNumeralSyntax.numeral free.length d.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxNumeralSyntax.numeral_rename]) (SyntaxRenameBinders.under_2 hd I)
    have he2 : Derives Δ (TermQuotationEnvironmentSyntax.environment bs fs w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc) := of_eq (by simp only [Formula.raise, TermQuotationEnvironmentSyntax.environment_rename]) (SyntaxRenameBinders.under_2 he I)
    have hl2 : Derives Δ (SyntaxCodedMixedBinderSyntax.lifted w.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc A.castSucc.castSucc C.castSucc.castSucc K.castSucc.castSucc H.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxCodedMixedBinderSyntax.lifted_rename]) (SyntaxRenameBinders.under_2 hl I)
    have hU2 : Derives Δ (SyntaxFreeShiftSyntax.shiftMap w.castSucc.castSucc c.castSucc.castSucc C.castSucc.castSucc U.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxFreeShiftSyntax.shiftMap_rename]) (SyntaxRenameBinders.under_2 hU I)
    have hV2 : Derives Δ (SyntaxIdentityMapSyntax.identityMap w.castSucc.castSucc d.castSucc.castSucc V.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxIdentityMapSyntax.identityMap_rename]) (SyntaxRenameBinders.under_2 hV I)
    have hh2 : Derives Δ (SyntaxMixedImageHead.head w.castSucc.castSucc C.castSucc.castSucc d.castSucc.castSucc z.castSucc.castSucc n.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxMixedImageHead.head_rename]) (SyntaxRenameBinders.under_2 hh I)
    have hI : Derives Δ I := .hyp (Or.inl rfl)
    have hInput := SyntaxCodedMixedBinderTyping.input_of_lifted w.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc A.castSucc.castSucc C.castSucc.castSucc K.castSucc.castSucc H.castSucc.castSucc hl2
    have hA := SyntaxNumeralSyntax.intro_succ bs.length A.castSucc.castSucc a.castSucc.castSucc ha2 (.conjL (.conjR hInput))
    have hm := SyntaxNumerals.less hZ2 (k.val+1) (bs.length+1) (Nat.succ_lt_succ (originalIndex bs k).isLt) (Fin.last m).castSucc A.castSucc.castSucc hI hA
    have ho := TermQuotationBinderValues.bound_at_numeral hZ2 bs fs (originalIndex bs k) w.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc A.castSucc.castSucc C.castSucc.castSucc K.castSucc.castSucc H.castSucc.castSucc U.castSucc.castSucc V.castSucc.castSucc z.castSucc.castSucc n.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) hw2 ha2 hc2 hd2 he2 hl2 hU2 hV2 hh2 hI
    have hread := TermQuotationBinderFields.drop_member _ _ _ hm ho
    simpa only [I, Fin.val_succ, newBound_get_succ] using hread

theorem free_readings {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) {bound free : PureSyntaxQuotation.Ctx}
    (bs fs : List (PureSyntaxQuotation.Tm bound free)) (w R S a b c d A C K H U V z n : Fin m)
    (hw : Derives Γ (omega w))
    (hb : Derives Γ (SyntaxNumeralSyntax.numeral fs.length b))
    (hc : Derives Γ (SyntaxNumeralSyntax.numeral bound.length c))
    (hd : Derives Γ (SyntaxNumeralSyntax.numeral free.length d))
    (he : Derives Γ (TermQuotationEnvironmentSyntax.environment bs fs w a b c d R S))
    (hl : Derives Γ (SyntaxCodedMixedBinderSyntax.lifted w R S a b c d A C K H))
    (hU : Derives Γ (SyntaxFreeShiftSyntax.shiftMap w c C U))
    (hV : Derives Γ (SyntaxIdentityMapSyntax.identityMap w d V))
    (hh : Derives Γ (SyntaxMixedImageHead.head w C d z n)) :
    Derives Γ (readings (shifted fs) w H) := by
  apply intro_rows
  intro j
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  let I := SyntaxNumeralSyntax.numeral j.val (Fin.last m).castSucc
  let Δ := Context.add I (Context.image Formula.raise (Context.image Formula.raise Γ))
  have hZ2 := SyntaxRenameBinders.zf_under_2 hZ I
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxRenameBinders.under_2 hw I)
  have hb2 : Derives Δ (SyntaxNumeralSyntax.numeral fs.length b.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxNumeralSyntax.numeral_rename]) (SyntaxRenameBinders.under_2 hb I)
  have hc2 : Derives Δ (SyntaxNumeralSyntax.numeral bound.length c.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxNumeralSyntax.numeral_rename]) (SyntaxRenameBinders.under_2 hc I)
  have hd2 : Derives Δ (SyntaxNumeralSyntax.numeral free.length d.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxNumeralSyntax.numeral_rename]) (SyntaxRenameBinders.under_2 hd I)
  have he2 : Derives Δ (TermQuotationEnvironmentSyntax.environment bs fs w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc) := of_eq (by simp only [Formula.raise, TermQuotationEnvironmentSyntax.environment_rename]) (SyntaxRenameBinders.under_2 he I)
  have hl2 : Derives Δ (SyntaxCodedMixedBinderSyntax.lifted w.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc A.castSucc.castSucc C.castSucc.castSucc K.castSucc.castSucc H.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxCodedMixedBinderSyntax.lifted_rename]) (SyntaxRenameBinders.under_2 hl I)
  have hU2 : Derives Δ (SyntaxFreeShiftSyntax.shiftMap w.castSucc.castSucc c.castSucc.castSucc C.castSucc.castSucc U.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxFreeShiftSyntax.shiftMap_rename]) (SyntaxRenameBinders.under_2 hU I)
  have hV2 : Derives Δ (SyntaxIdentityMapSyntax.identityMap w.castSucc.castSucc d.castSucc.castSucc V.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxIdentityMapSyntax.identityMap_rename]) (SyntaxRenameBinders.under_2 hV I)
  have hh2 : Derives Δ (SyntaxMixedImageHead.head w.castSucc.castSucc C.castSucc.castSucc d.castSucc.castSucc z.castSucc.castSucc n.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxMixedImageHead.head_rename]) (SyntaxRenameBinders.under_2 hh I)
  have hI : Derives Δ I := .hyp (Or.inl rfl)
  have hm := SyntaxNumeralMembers.index_member hZ2 fs.length (originalIndex fs j) b.castSucc.castSucc (Fin.last m).castSucc hb2 hI
  have ho := TermQuotationBinderValues.free_iff hZ2 bs fs (originalIndex fs j) w.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc A.castSucc.castSucc C.castSucc.castSucc K.castSucc.castSucc H.castSucc.castSucc U.castSucc.castSucc V.castSucc.castSucc z.castSucc.castSucc n.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) hw2 hb2 hc2 hd2 he2 hl2 hU2 hV2 hh2 hI
  have hread := TermQuotationBinderFields.drop_member _ _ _ hm ho
  simpa only [shifted_get] using hread

end PPAC.Migration.Internal.TermQuotationLiftReading
