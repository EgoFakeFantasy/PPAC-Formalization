import PPAC.Migration.Internal.TermImageReadingSyntax

/-! 原长度与全部内部字段一致性恢复整张项像quotation；不假定列表码外部标准。 -/
namespace PPAC.Migration.Internal.TermImageReading
open Source SourceAlgebra SourceLogic OmegaSyntax TermImageReadingSyntax
open SyntaxRenameQuerySyntax (of_eq)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem from_images {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) {bound free : PureSyntaxQuotation.Ctx}
    (values : List (PureSyntaxQuotation.Tm bound free)) (w L : Fin m) (hw : Derives Γ (omega w))
    (hL : Derives Γ (TermImageQuotationSyntax.images values w L)) : Derives Γ (readings values w L) := by
  apply intro_rows
  intro j
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  let I := SyntaxNumeralSyntax.numeral j.val (Fin.last m).castSucc
  let Δ := Context.add I (Context.image Formula.raise (Context.image Formula.raise Γ))
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxRenameBinders.under_2 hw I)
  have hL2 : Derives Δ (TermImageQuotationSyntax.images values w.castSucc.castSucc L.castSucc.castSucc) := of_eq (by simp only [Formula.raise, TermImageQuotationSyntax.images_rename]) (SyntaxRenameBinders.under_2 hL I)
  exact TermImageQuotationFields.field_at (SyntaxRenameBinders.zf_under_2 hZ I) values w.castSucc.castSucc L.castSucc.castSucc j (Fin.last m).castSucc (Fin.last (m+1)) hw2 hL2 (.hyp (Or.inl rfl))

theorem agree_from_readings {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) {bound free : PureSyntaxQuotation.Ctx}
    (values : List (PureSyntaxQuotation.Tm bound free)) (w a L V : Fin m) (hw : Derives Γ (omega w))
    (ha : Derives Γ (SyntaxNumeralSyntax.numeral values.length a)) (hr : Derives Γ (readings values w L))
    (hV : Derives Γ (TermImageQuotationSyntax.images values w V)) : Derives Γ (StructuralListCodeSyntax.agree w a L V) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  let M := Formula.mem (Fin.last m).castSucc a.castSucc.castSucc
  let Δ := Context.add M (Context.image Formula.raise (Context.image Formula.raise Γ))
  have hZ2 := SyntaxRenameBinders.zf_under_2 hZ M
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxRenameBinders.under_2 hw M)
  have ha2 : Derives Δ (SyntaxNumeralSyntax.numeral values.length a.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxNumeralSyntax.numeral_rename]) (SyntaxRenameBinders.under_2 ha M)
  have hr2 : Derives Δ (readings values w.castSucc.castSucc L.castSucc.castSucc) := of_eq (by simp only [Formula.raise, readings_rename]) (SyntaxRenameBinders.under_2 hr M)
  have hV2 : Derives Δ (TermImageQuotationSyntax.images values w.castSucc.castSucc V.castSucc.castSucc) := of_eq (by simp only [Formula.raise, TermImageQuotationSyntax.images_rename]) (SyntaxRenameBinders.under_2 hV M)
  have hb := Derives.impE (.conjL (SyntaxNumeralMembers.member_iff hZ2 values.length a.castSucc.castSucc (Fin.last m).castSucc ha2)) (.hyp (Or.inl rfl))
  have hi : Derives Δ ((SyntaxPositionSyntax.below values.length (Fin.last m).castSucc).imp
      ((StructuralListFieldSyntax.field w.castSucc.castSucc L.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))).iff
        (StructuralListFieldSyntax.field w.castSucc.castSucc V.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))))) := by
    apply SyntaxPositionSyntax.below_imp
    intro j
    apply Derives.impI
    let J := SyntaxNumeralSyntax.numeral j.val (Fin.last m).castSucc
    let Ξ := Context.add J Δ
    have hJ : Derives Ξ J := .hyp (Or.inl rfl)
    have hL := at_index values w.castSucc.castSucc L.castSucc.castSucc j (Fin.last m).castSucc (Fin.last (m+1)) (add hr2 J) hJ
    have hR := TermImageQuotationFields.field_at (ZFContext.add hZ2 J) values w.castSucc.castSucc V.castSucc.castSucc j (Fin.last m).castSucc (Fin.last (m+1)) (add hw2 J) (add hV2 J) hJ
    exact SyntaxTypeLocalTransfer.iff_trans hL (.conjI (.conjR hR) (.conjL hR))
  exact .impE hi hb

theorem output_subst {m} {Γ : Context m} {bound free : PureSyntaxQuotation.Ctx}
    (values : List (PureSyntaxQuotation.Tm bound free)) (w L V : Fin m) (he : Derives Γ (.equal L V))
    (hL : Derives Γ (TermImageQuotationSyntax.images values w L)) : Derives Γ (TermImageQuotationSyntax.images values w V) := by
  let P := TermImageQuotationSyntax.images values w.castSucc (Fin.last m)
  have hi : Derives Γ (P.instantiate L) := of_eq (by simp only [P, Formula.instantiate, TermImageQuotationSyntax.images_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hL
  have ho := Derives.eqSubst P he hi
  exact of_eq (by simp only [P, Formula.instantiate, TermImageQuotationSyntax.images_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) ho

theorem images_of_readings {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) {bound free : PureSyntaxQuotation.Ctx}
    (values : List (PureSyntaxQuotation.Tm bound free)) (w a L : Fin m) (hw : Derives Γ (omega w))
    (ha : Derives Γ (SyntaxNumeralSyntax.numeral values.length a)) (hl : Derives Γ (StructuralListLengthSyntax.hasLength w L a))
    (hr : Derives Γ (readings values w L)) : Derives Γ (TermImageQuotationSyntax.images values w L) := by
  have he := TermImageQuotationFields.exists_images hZ values w hw
  let P := (Formula.mem (Fin.last m) w.castSucc).conj (TermImageQuotationSyntax.images values w.castSucc (Fin.last m))
  let Δ := Context.add P (Context.image Formula.raise Γ)
  apply Derives.exE (p := P) he
  have hZ1 := ZFContext.under hZ P
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw P)
  have ha1 : Derives Δ (SyntaxNumeralSyntax.numeral values.length a.castSucc) := of_eq (SyntaxNumeralSyntax.numeral_rename _ a Fin.castSucc) (under ha P)
  have hl1 : Derives Δ (StructuralListLengthSyntax.hasLength w.castSucc L.castSucc a.castSucc) := of_eq (StructuralListLengthSyntax.hasLength_rename w L a Fin.castSucc) (under hl P)
  have hr1 : Derives Δ (readings values w.castSucc L.castSucc) := of_eq (readings_rename values w L Fin.castSucc) (under hr P)
  have hP : Derives Δ P := .hyp (Or.inl rfl)
  have hvLen := TermImageQuotationFields.length_at hZ1 values w.castSucc (Fin.last m) a.castSucc hw1 (.conjR hP) ha1
  have hg := agree_from_readings hZ1 values w.castSucc a.castSucc L.castSucc (Fin.last m) hw1 ha1 hr1 (.conjR hP)
  have heq := StructuralListCodeInduction.unique hZ1 w.castSucc a.castSucc L.castSucc (Fin.last m) hw1 hl1 hvLen hg
  have ho := output_subst values w.castSucc (Fin.last m) L.castSucc (eq_symm heq) (.conjR hP)
  exact of_eq (TermImageQuotationSyntax.images_rename values w L Fin.castSucc).symm ho

end PPAC.Migration.Internal.TermImageReading
