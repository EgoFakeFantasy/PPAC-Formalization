import PPAC.Migration.Internal.TopQuotationVariableFields

/-! 原首槽码表的完整项像quotation读取，全部内部位置/输出量词保留；外部位置只指定有限模式。 -/
namespace PPAC.Migration.Internal.TopQuotationReadings
open Source SourceAlgebra SourceLogic OmegaSyntax NativeSubstitutionSyntax TermImageReadingSyntax
open SyntaxRenameQuerySyntax (of_eq)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem instantiate_bound_readings {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) {bound free : PureSyntaxQuotation.Ctx}
    (replacement : PureSyntaxQuotation.Tm bound free)
    (w a b A t R S : Fin m)
    (hw : Derives Γ (omega w))
    (ha : Derives Γ (SyntaxNumeralSyntax.numeral bound.length a))
    (he : Derives Γ (SyntaxTopCodedEnvironmentSyntax.instantiateCoded w a b A t R S))
    (ht : Derives Γ (PureQuotationSyntax.term replacement w t)) :
    Derives Γ (readings (NativeSubstitutionImages.images (YesMetaZFC.SetTheory.SetSort.set :: bound) (NativeTopQuotationIndices.instantiateBound replacement)) w R) := by
  have hInput := SyntaxTopCodedEnvironmentTyping.instantiate_input w a b A t R S he
  have hDomain : Derives Γ (SyntaxNumeralSyntax.numeral (YesMetaZFC.SetTheory.SetSort.set :: bound).length A) := SyntaxNumeralSyntax.intro_succ bound.length A a ha (.conjR hInput)
  apply intro_rows
  intro j
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  let I := SyntaxNumeralSyntax.numeral j.val (Fin.last m).castSucc
  let Δ := Context.add I (Context.image Formula.raise (Context.image Formula.raise Γ))
  have hZ2 := SyntaxRenameBinders.zf_under_2 hZ I
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxRenameBinders.under_2 hw I)
  have ha2 : Derives Δ (SyntaxNumeralSyntax.numeral bound.length a.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxNumeralSyntax.numeral_rename]) (SyntaxRenameBinders.under_2 ha I)
  have he2 : Derives Δ (SyntaxTopCodedEnvironmentSyntax.instantiateCoded w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc A.castSucc.castSucc t.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxTopCodedEnvironmentSyntax.instantiateCoded_rename]) (SyntaxRenameBinders.under_2 he I)
  have ht2 : Derives Δ (PureQuotationSyntax.term replacement w.castSucc.castSucc t.castSucc.castSucc) := of_eq (by simp only [Formula.raise, PureQuotationSyntax.term_rename]) (SyntaxRenameBinders.under_2 ht I)
  have hDomain2 : Derives Δ (SyntaxNumeralSyntax.numeral (YesMetaZFC.SetTheory.SetSort.set :: bound).length A.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxNumeralSyntax.numeral_rename]) (SyntaxRenameBinders.under_2 hDomain I)
  let entry := NativeTopQuotationIndices.entryAt (YesMetaZFC.SetTheory.SetSort.set :: bound) (NativeTopQuotationIndices.sourceIndex (NativeTopQuotationIndices.instantiateBound replacement) j)
  have hidx : entry.index = j.val := NativeTopQuotationIndices.index_entryAt (YesMetaZFC.SetTheory.SetSort.set :: bound) (NativeTopQuotationIndices.sourceIndex (NativeTopQuotationIndices.instantiateBound replacement) j)
  have hI : Derives Δ I := .hyp (Or.inl rfl)
  have hNum : Derives Δ (SyntaxNumeralSyntax.numeral entry.index (Fin.last m).castSucc) := of_eq (congrArg (fun k => SyntaxNumeralSyntax.numeral k (Fin.last m).castSucc) hidx.symm) hI
  have hm := SyntaxNumerals.less hZ2 entry.index (YesMetaZFC.SetTheory.SetSort.set :: bound).length entry.index_lt_length (Fin.last m).castSucc A.castSucc.castSucc hNum hDomain2
  have ho := TopQuotationVariableFields.instantiate_bound hZ2 (bound := bound) (free := free) replacement entry w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc A.castSucc.castSucc t.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) hw2 ha2 he2 ht2 hNum
  have hread := TermQuotationBinderFields.drop_member _ _ _ hm ho
  simpa only [NativeTopQuotationIndices.get_at] using hread

theorem instantiate_free_readings {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) {bound free : PureSyntaxQuotation.Ctx}
    (w a b A t R S : Fin m)
    (hw : Derives Γ (omega w))
    (hb : Derives Γ (SyntaxNumeralSyntax.numeral free.length b))
    (he : Derives Γ (SyntaxTopCodedEnvironmentSyntax.instantiateCoded w a b A t R S)) :
    Derives Γ (readings (NativeSubstitutionImages.images free (@NativeTopQuotationIndices.identityFree bound free)) w S) := by
  apply intro_rows
  intro j
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  let I := SyntaxNumeralSyntax.numeral j.val (Fin.last m).castSucc
  let Δ := Context.add I (Context.image Formula.raise (Context.image Formula.raise Γ))
  have hZ2 := SyntaxRenameBinders.zf_under_2 hZ I
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxRenameBinders.under_2 hw I)
  have hb2 : Derives Δ (SyntaxNumeralSyntax.numeral free.length b.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxNumeralSyntax.numeral_rename]) (SyntaxRenameBinders.under_2 hb I)
  have he2 : Derives Δ (SyntaxTopCodedEnvironmentSyntax.instantiateCoded w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc A.castSucc.castSucc t.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxTopCodedEnvironmentSyntax.instantiateCoded_rename]) (SyntaxRenameBinders.under_2 he I)
  let entry := NativeTopQuotationIndices.entryAt free (NativeTopQuotationIndices.sourceIndex (@NativeTopQuotationIndices.identityFree bound free) j)
  have hidx : entry.index = j.val := NativeTopQuotationIndices.index_entryAt free (NativeTopQuotationIndices.sourceIndex (@NativeTopQuotationIndices.identityFree bound free) j)
  have hI : Derives Δ I := .hyp (Or.inl rfl)
  have hNum : Derives Δ (SyntaxNumeralSyntax.numeral entry.index (Fin.last m).castSucc) := of_eq (congrArg (fun k => SyntaxNumeralSyntax.numeral k (Fin.last m).castSucc) hidx.symm) hI
  have hm := SyntaxNumerals.less hZ2 entry.index free.length entry.index_lt_length (Fin.last m).castSucc b.castSucc.castSucc hNum hb2
  have ho := TopQuotationVariableFields.instantiate_free hZ2 (bound := bound) (free := free) entry w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc A.castSucc.castSucc t.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) hw2 hb2 he2 hNum
  have hread := TermQuotationBinderFields.drop_member _ _ _ hm ho
  simpa only [NativeTopQuotationIndices.get_at] using hread

theorem abstract_bound_readings {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) {bound free : PureSyntaxQuotation.Ctx}
    (w a b A B R S : Fin m)
    (hw : Derives Γ (omega w))
    (ha : Derives Γ (SyntaxNumeralSyntax.numeral bound.length a))
    (he : Derives Γ (SyntaxTopCodedEnvironmentSyntax.abstractCoded w a b A B R S)) :
    Derives Γ (readings (NativeSubstitutionImages.images bound (@NativeTopQuotationIndices.abstractBound bound free)) w R) := by
  apply intro_rows
  intro j
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  let I := SyntaxNumeralSyntax.numeral j.val (Fin.last m).castSucc
  let Δ := Context.add I (Context.image Formula.raise (Context.image Formula.raise Γ))
  have hZ2 := SyntaxRenameBinders.zf_under_2 hZ I
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxRenameBinders.under_2 hw I)
  have ha2 : Derives Δ (SyntaxNumeralSyntax.numeral bound.length a.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxNumeralSyntax.numeral_rename]) (SyntaxRenameBinders.under_2 ha I)
  have he2 : Derives Δ (SyntaxTopCodedEnvironmentSyntax.abstractCoded w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc A.castSucc.castSucc B.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxTopCodedEnvironmentSyntax.abstractCoded_rename]) (SyntaxRenameBinders.under_2 he I)
  let entry := NativeTopQuotationIndices.entryAt bound (NativeTopQuotationIndices.sourceIndex (@NativeTopQuotationIndices.abstractBound bound free) j)
  have hidx : entry.index = j.val := NativeTopQuotationIndices.index_entryAt bound (NativeTopQuotationIndices.sourceIndex (@NativeTopQuotationIndices.abstractBound bound free) j)
  have hI : Derives Δ I := .hyp (Or.inl rfl)
  have hNum : Derives Δ (SyntaxNumeralSyntax.numeral entry.index (Fin.last m).castSucc) := of_eq (congrArg (fun k => SyntaxNumeralSyntax.numeral k (Fin.last m).castSucc) hidx.symm) hI
  have hm := SyntaxNumerals.less hZ2 entry.index bound.length entry.index_lt_length (Fin.last m).castSucc a.castSucc.castSucc hNum ha2
  have ho := TopQuotationVariableFields.abstract_bound hZ2 (bound := bound) (free := free) entry w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc A.castSucc.castSucc B.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) hw2 ha2 he2 hNum
  have hread := TermQuotationBinderFields.drop_member _ _ _ hm ho
  simpa only [NativeTopQuotationIndices.get_at] using hread

theorem abstract_free_readings {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) {bound free : PureSyntaxQuotation.Ctx}
    (w a b A B R S : Fin m)
    (hw : Derives Γ (omega w))
    (hb : Derives Γ (SyntaxNumeralSyntax.numeral free.length b))
    (he : Derives Γ (SyntaxTopCodedEnvironmentSyntax.abstractCoded w a b A B R S)) :
    Derives Γ (readings (NativeSubstitutionImages.images (YesMetaZFC.SetTheory.SetSort.set :: free) (@NativeTopQuotationIndices.abstractFree bound free)) w S) := by
  have hInput := SyntaxTopCodedEnvironmentTyping.abstract_input w a b A B R S he
  have hDomain : Derives Γ (SyntaxNumeralSyntax.numeral (YesMetaZFC.SetTheory.SetSort.set :: free).length B) := SyntaxNumeralSyntax.intro_succ free.length B b hb (.conjR (.conjR hInput))
  apply intro_rows
  intro j
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  let I := SyntaxNumeralSyntax.numeral j.val (Fin.last m).castSucc
  let Δ := Context.add I (Context.image Formula.raise (Context.image Formula.raise Γ))
  have hZ2 := SyntaxRenameBinders.zf_under_2 hZ I
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxRenameBinders.under_2 hw I)
  have hb2 : Derives Δ (SyntaxNumeralSyntax.numeral free.length b.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxNumeralSyntax.numeral_rename]) (SyntaxRenameBinders.under_2 hb I)
  have he2 : Derives Δ (SyntaxTopCodedEnvironmentSyntax.abstractCoded w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc A.castSucc.castSucc B.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxTopCodedEnvironmentSyntax.abstractCoded_rename]) (SyntaxRenameBinders.under_2 he I)
  have hDomain2 : Derives Δ (SyntaxNumeralSyntax.numeral (YesMetaZFC.SetTheory.SetSort.set :: free).length B.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxNumeralSyntax.numeral_rename]) (SyntaxRenameBinders.under_2 hDomain I)
  let entry := NativeTopQuotationIndices.entryAt (YesMetaZFC.SetTheory.SetSort.set :: free) (NativeTopQuotationIndices.sourceIndex (@NativeTopQuotationIndices.abstractFree bound free) j)
  have hidx : entry.index = j.val := NativeTopQuotationIndices.index_entryAt (YesMetaZFC.SetTheory.SetSort.set :: free) (NativeTopQuotationIndices.sourceIndex (@NativeTopQuotationIndices.abstractFree bound free) j)
  have hI : Derives Δ I := .hyp (Or.inl rfl)
  have hNum : Derives Δ (SyntaxNumeralSyntax.numeral entry.index (Fin.last m).castSucc) := of_eq (congrArg (fun k => SyntaxNumeralSyntax.numeral k (Fin.last m).castSucc) hidx.symm) hI
  have hm := SyntaxNumerals.less hZ2 entry.index (YesMetaZFC.SetTheory.SetSort.set :: free).length entry.index_lt_length (Fin.last m).castSucc B.castSucc.castSucc hNum hDomain2
  have ho := TopQuotationVariableFields.abstract_free hZ2 (bound := bound) (free := free) entry w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc A.castSucc.castSucc B.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) hw2 hb2 he2 hNum
  have hread := TermQuotationBinderFields.drop_member _ _ _ hm ho
  simpa only [NativeTopQuotationIndices.get_at] using hread

end PPAC.Migration.Internal.TopQuotationReadings
