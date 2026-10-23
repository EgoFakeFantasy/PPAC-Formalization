import PPAC.Migration.Internal.NativeTopQuotationIndices

/-! 首槽原码表在每个原生变量模式上的准确quotation；前驱和后继索引皆在对象量词内消去。 -/
namespace PPAC.Migration.Internal.TopQuotationVariableFields
open Source SourceAlgebra SourceLogic OmegaSyntax NativeSubstitutionSyntax
open SyntaxRenameQuerySyntax (of_eq)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem instantiate_bound {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) {bound free : PureSyntaxQuotation.Ctx}
    (replacement : PureSyntaxQuotation.Tm bound free) (entry : YesMetaZFC.Logic.FirstOrder.Variable (YesMetaZFC.SetTheory.SetSort.set :: bound) YesMetaZFC.SetTheory.SetSort.set)
    (w a b A t R S i q : Fin m) (hw : Derives Γ (omega w))
    (ha : Derives Γ (SyntaxNumeralSyntax.numeral bound.length a))
    (he : Derives Γ (SyntaxTopCodedEnvironmentSyntax.instantiateCoded w a b A t R S))
    (ht : Derives Γ (PureQuotationSyntax.term replacement w t))
    (hi : Derives Γ (SyntaxNumeralSyntax.numeral entry.index i)) :
    Derives Γ (((Formula.mem i A).conj (StructuralListFieldSyntax.field w R i q)).iff
      (PureQuotationSyntax.term (NativeTopQuotationIndices.instantiateBound replacement entry) w q)) := by
  cases entry with
  | here =>
    have hold := SyntaxTopCodedEnvironmentFields.instantiate_zero hZ w a b A t R S i q hw he hi
    have hquote := OriginalQuotationValue.at_value hZ (PureSyntaxQuotation.termTree replacement) w t q hw ht
    exact SyntaxTypeLocalTransfer.iff_trans hold (.conjI (.conjR hquote) (.conjL hquote))
  | there entry =>
    let P := (SyntaxNumeralSyntax.numeral entry.index (Fin.last m)).conj (successor i.castSucc (Fin.last m))
    let Δ := Context.add P (Context.image Formula.raise Γ)
    apply SyntaxNumeralSyntax.eliminate_succ entry.index i _ hi
    have hZ1 := ZFContext.under hZ P
    have hw1 : Derives Δ (omega w.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (under hw P)
    have ha1 : Derives Δ (SyntaxNumeralSyntax.numeral bound.length a.castSucc) := of_eq (by simp only [Formula.raise, SyntaxNumeralSyntax.numeral_rename]) (under ha P)
    have he1 : Derives Δ (SyntaxTopCodedEnvironmentSyntax.instantiateCoded w.castSucc a.castSucc b.castSucc A.castSucc t.castSucc R.castSucc S.castSucc) := of_eq (by simp only [Formula.raise, SyntaxTopCodedEnvironmentSyntax.instantiateCoded_rename]) (under he P)
    have hP : Derives Δ P := .hyp (Or.inl rfl)
    have hm := SyntaxNumerals.less hZ1 entry.index bound.length entry.index_lt_length (Fin.last m) a.castSucc (.conjL hP) ha1
    have hold := SyntaxTopCodedEnvironmentFields.instantiate_bound hZ1 w.castSucc a.castSucc b.castSucc A.castSucc t.castSucc R.castSucc S.castSucc i.castSucc (Fin.last m) q.castSucc hw1 he1 hm (.conjR hP)
    have hquote := OriginalQuotationVariableFields.variable_iff hZ1 true entry.index w.castSucc (Fin.last m) q.castSucc hw1 (.conjL hP)
    have ho := SyntaxTypeLocalTransfer.iff_trans hold (.conjI (.conjR hquote) (.conjL hquote))
    exact of_eq (by simp only [Formula.raise, Formula.iff, Formula.rename, StructuralListFieldSyntax.field_rename, PureQuotationSyntax.term_rename] <;> rfl) ho

theorem instantiate_free {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) {bound free : PureSyntaxQuotation.Ctx}
    (entry : YesMetaZFC.Logic.FirstOrder.Variable free YesMetaZFC.SetTheory.SetSort.set) (w a b A t R S i q : Fin m) (hw : Derives Γ (omega w))
    (hb : Derives Γ (SyntaxNumeralSyntax.numeral free.length b))
    (he : Derives Γ (SyntaxTopCodedEnvironmentSyntax.instantiateCoded w a b A t R S))
    (hi : Derives Γ (SyntaxNumeralSyntax.numeral entry.index i)) :
    Derives Γ (((Formula.mem i b).conj (StructuralListFieldSyntax.field w S i q)).iff
      (PureQuotationSyntax.term ((NativeTopQuotationIndices.identityFree : Mapping free bound free) entry) w q)) := by
  have hm := SyntaxNumerals.less hZ entry.index free.length entry.index_lt_length i b hi hb
  have hold := SyntaxTopCodedEnvironmentFields.instantiate_free hZ w a b A t R S i q he hm
  have hquote := OriginalQuotationVariableFields.variable_iff hZ false entry.index w i q hw hi
  exact SyntaxTypeLocalTransfer.iff_trans hold (.conjI (.conjR hquote) (.conjL hquote))

theorem abstract_bound {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) {bound free : PureSyntaxQuotation.Ctx}
    (entry : YesMetaZFC.Logic.FirstOrder.Variable bound YesMetaZFC.SetTheory.SetSort.set) (w a b A B R S i q : Fin m) (hw : Derives Γ (omega w))
    (ha : Derives Γ (SyntaxNumeralSyntax.numeral bound.length a))
    (he : Derives Γ (SyntaxTopCodedEnvironmentSyntax.abstractCoded w a b A B R S))
    (hi : Derives Γ (SyntaxNumeralSyntax.numeral entry.index i)) :
    Derives Γ (((Formula.mem i a).conj (StructuralListFieldSyntax.field w R i q)).iff
      (PureQuotationSyntax.term ((NativeTopQuotationIndices.abstractBound : Mapping bound (YesMetaZFC.SetTheory.SetSort.set :: bound) free) entry) w q)) := by
  have hm := SyntaxNumerals.less hZ entry.index bound.length entry.index_lt_length i a hi ha
  have hex := InsertExistence.exists_insert i i (ZFContext.arithmetic hZ).base.pairing (ZFContext.arithmetic hZ).base.union
  let P := successor (Fin.last m) i.castSucc
  let Δ := Context.add P (Context.image Formula.raise Γ)
  apply Derives.exE (p := P) hex
  have hZ1 := ZFContext.under hZ P
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (under hw P)
  have he1 : Derives Δ (SyntaxTopCodedEnvironmentSyntax.abstractCoded w.castSucc a.castSucc b.castSucc A.castSucc B.castSucc R.castSucc S.castSucc) := of_eq (by simp only [Formula.raise, SyntaxTopCodedEnvironmentSyntax.abstractCoded_rename]) (under he P)
  have hi1 : Derives Δ (SyntaxNumeralSyntax.numeral entry.index i.castSucc) := of_eq (by simp only [Formula.raise, SyntaxNumeralSyntax.numeral_rename]) (under hi P)
  have hm1 : Derives Δ (.mem i.castSucc a.castSucc) := under hm P
  have hP : Derives Δ P := .hyp (Or.inl rfl)
  have hj := SyntaxNumeralSyntax.intro_succ entry.index (Fin.last m) i.castSucc hi1 hP
  have hold := SyntaxTopCodedEnvironmentFields.abstract_bound hZ1 w.castSucc a.castSucc b.castSucc A.castSucc B.castSucc R.castSucc S.castSucc i.castSucc (Fin.last m) q.castSucc he1 hm1 hP
  have hquote := OriginalQuotationVariableFields.variable_iff hZ1 true (entry.index+1) w.castSucc (Fin.last m) q.castSucc hw1 hj
  have ho := SyntaxTypeLocalTransfer.iff_trans hold (.conjI (.conjR hquote) (.conjL hquote))
  exact of_eq (by simp only [Formula.raise, Formula.iff, Formula.rename, StructuralListFieldSyntax.field_rename, PureQuotationSyntax.term_rename] <;> rfl) ho

theorem abstract_free {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) {bound free : PureSyntaxQuotation.Ctx}
    (entry : YesMetaZFC.Logic.FirstOrder.Variable (YesMetaZFC.SetTheory.SetSort.set :: free) YesMetaZFC.SetTheory.SetSort.set) (w a b A B R S i q : Fin m) (hw : Derives Γ (omega w))
    (hb : Derives Γ (SyntaxNumeralSyntax.numeral free.length b))
    (he : Derives Γ (SyntaxTopCodedEnvironmentSyntax.abstractCoded w a b A B R S))
    (hi : Derives Γ (SyntaxNumeralSyntax.numeral entry.index i)) :
    Derives Γ (((Formula.mem i B).conj (StructuralListFieldSyntax.field w S i q)).iff
      (PureQuotationSyntax.term ((NativeTopQuotationIndices.abstractFree : Mapping (YesMetaZFC.SetTheory.SetSort.set :: free) (YesMetaZFC.SetTheory.SetSort.set :: bound) free) entry) w q)) := by
  cases entry with
  | here =>
    have hold := SyntaxTopCodedEnvironmentFields.abstract_zero hZ w a b A B R S i q hw he hi
    have hquote := OriginalQuotationVariableFields.variable_iff hZ true 0 w i q hw hi
    exact SyntaxTypeLocalTransfer.iff_trans hold (.conjI (.conjR hquote) (.conjL hquote))
  | there entry =>
    let P := (SyntaxNumeralSyntax.numeral entry.index (Fin.last m)).conj (successor i.castSucc (Fin.last m))
    let Δ := Context.add P (Context.image Formula.raise Γ)
    apply SyntaxNumeralSyntax.eliminate_succ entry.index i _ hi
    have hZ1 := ZFContext.under hZ P
    have hw1 : Derives Δ (omega w.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (under hw P)
    have hb1 : Derives Δ (SyntaxNumeralSyntax.numeral free.length b.castSucc) := of_eq (by simp only [Formula.raise, SyntaxNumeralSyntax.numeral_rename]) (under hb P)
    have he1 : Derives Δ (SyntaxTopCodedEnvironmentSyntax.abstractCoded w.castSucc a.castSucc b.castSucc A.castSucc B.castSucc R.castSucc S.castSucc) := of_eq (by simp only [Formula.raise, SyntaxTopCodedEnvironmentSyntax.abstractCoded_rename]) (under he P)
    have hP : Derives Δ P := .hyp (Or.inl rfl)
    have hm := SyntaxNumerals.less hZ1 entry.index free.length entry.index_lt_length (Fin.last m) b.castSucc (.conjL hP) hb1
    have hold := SyntaxTopCodedEnvironmentFields.abstract_free hZ1 w.castSucc a.castSucc b.castSucc A.castSucc B.castSucc R.castSucc S.castSucc i.castSucc (Fin.last m) q.castSucc hw1 he1 hm (.conjR hP)
    have hquote := OriginalQuotationVariableFields.variable_iff hZ1 false entry.index w.castSucc (Fin.last m) q.castSucc hw1 (.conjL hP)
    have ho := SyntaxTypeLocalTransfer.iff_trans hold (.conjI (.conjR hquote) (.conjL hquote))
    exact of_eq (by simp only [Formula.raise, Formula.iff, Formula.rename, StructuralListFieldSyntax.field_rename, PureQuotationSyntax.term_rename] <;> rfl) ho

end PPAC.Migration.Internal.TopQuotationVariableFields
