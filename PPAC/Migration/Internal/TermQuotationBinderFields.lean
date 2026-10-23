import PPAC.Migration.Internal.TermImageReading

/-! 实际混合binder的零、旧bound后继和旧free字段与原项quotation逐项精确对应。 -/
namespace PPAC.Migration.Internal.TermQuotationBinderFields
open Source SourceAlgebra SourceLogic OmegaSyntax
open SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket (Tree leaf)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem drop_member {m} {Γ : Context m} (P Q R : Formula m) (hp : Derives Γ P)
    (he : Derives Γ ((P.conj Q).iff R)) : Derives Γ (Q.iff R) := by
  apply Derives.conjI
  · apply Derives.impI
    exact .impE (add (.conjL he) _) (.conjI (add hp _) (.hyp (Or.inl rfl)))
  · apply Derives.impI
    exact .conjR (.impE (add (.conjR he) _) (.hyp (Or.inl rfl)))

theorem zero_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w R S a b c d A C K H U V z n q : Fin m)
    (hw : Derives Γ (omega w)) (hl : Derives Γ (SyntaxCodedMixedBinderSyntax.lifted w R S a b c d A C K H))
    (hU : Derives Γ (SyntaxFreeShiftSyntax.shiftMap w c C U)) (hV : Derives Γ (SyntaxIdentityMapSyntax.identityMap w d V))
    (hh : Derives Γ (SyntaxMixedImageHead.head w C d z n)) :
    Derives Γ (((Formula.mem z A).conj (StructuralListFieldSyntax.field w K z q)).iff
      (OriginalTreeQuotationSyntax.tree (.node 0 [leaf 0]) w q)) := by
  have hz := OriginalQuotationVariableFields.tree_of_variable true 0 w z n (.conjL hh) (.conjL (.conjR hh))
  have he := SyntaxCodedMixedBinderFields.zero_iff hZ w R S a b c d A C K H U V z n q hw hl hU hV hh
  have hq := OriginalQuotationValue.at_value hZ (.node 0 [leaf 0]) w n q hw hz
  exact SyntaxTypeLocalTransfer.iff_trans he (.conjI (.conjR hq) (.conjL hq))

theorem bound_at_code {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) {bound free : PureSyntaxQuotation.Ctx}
    (bs fs : List (PureSyntaxQuotation.Tm bound free)) (j : Fin bs.length) (w R S a b c d A C K H U V z n i v t q : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (SyntaxNumeralSyntax.numeral bs.length a))
    (hc : Derives Γ (SyntaxNumeralSyntax.numeral bound.length c)) (hd : Derives Γ (SyntaxNumeralSyntax.numeral free.length d))
    (he : Derives Γ (TermQuotationEnvironmentSyntax.environment bs fs w a b c d R S))
    (hl : Derives Γ (SyntaxCodedMixedBinderSyntax.lifted w R S a b c d A C K H))
    (hU : Derives Γ (SyntaxFreeShiftSyntax.shiftMap w c C U)) (hV : Derives Γ (SyntaxIdentityMapSyntax.identityMap w d V))
    (hh : Derives Γ (SyntaxMixedImageHead.head w C d z n)) (hj : Derives Γ (SyntaxNumeralSyntax.numeral j.val v))
    (hi : Derives Γ (successor i v)) (ht : Derives Γ (PureQuotationSyntax.term (bs.get j) w t)) :
    Derives Γ (((Formula.mem i A).conj (StructuralListFieldSyntax.field w K i q)).iff
      (PureQuotationSyntax.term ((bs.get j).weakenBound YesMetaZFC.SetTheory.SetSort.set) w q)) := by
  have hv := SyntaxNumeralMembers.index_member hZ bs.length j a v ha hj
  have hField := Derives.impE (.conjR (TermImageQuotationFields.field_at hZ bs w R j v t hw (.conjL (.conjL he)) hj)) ht
  have hLift := SyntaxCodedMixedBinderFields.bound_iff hZ w R S a b c d A C K H U V z n i v t q hw hl hU hV hh hv hi hField
  have hShift := TermQuotationShift.term_iff hZ (bs.get j) w U V c d C t q hw hc hd hU hV ht
  exact SyntaxTypeLocalTransfer.iff_trans hLift hShift

theorem free_at_code {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) {bound free : PureSyntaxQuotation.Ctx}
    (bs fs : List (PureSyntaxQuotation.Tm bound free)) (j : Fin fs.length) (w R S a b c d A C K H U V z n v t q : Fin m)
    (hw : Derives Γ (omega w)) (hb : Derives Γ (SyntaxNumeralSyntax.numeral fs.length b))
    (hc : Derives Γ (SyntaxNumeralSyntax.numeral bound.length c)) (hd : Derives Γ (SyntaxNumeralSyntax.numeral free.length d))
    (he : Derives Γ (TermQuotationEnvironmentSyntax.environment bs fs w a b c d R S))
    (hl : Derives Γ (SyntaxCodedMixedBinderSyntax.lifted w R S a b c d A C K H))
    (hU : Derives Γ (SyntaxFreeShiftSyntax.shiftMap w c C U)) (hV : Derives Γ (SyntaxIdentityMapSyntax.identityMap w d V))
    (hh : Derives Γ (SyntaxMixedImageHead.head w C d z n)) (hj : Derives Γ (SyntaxNumeralSyntax.numeral j.val v))
    (ht : Derives Γ (PureQuotationSyntax.term (fs.get j) w t)) :
    Derives Γ (((Formula.mem v b).conj (StructuralListFieldSyntax.field w H v q)).iff
      (PureQuotationSyntax.term ((fs.get j).weakenBound YesMetaZFC.SetTheory.SetSort.set) w q)) := by
  have hv := SyntaxNumeralMembers.index_member hZ fs.length j b v hb hj
  have hField := Derives.impE (.conjR (TermImageQuotationFields.field_at hZ fs w S j v t hw (.conjR (.conjL he)) hj)) ht
  have hLift := SyntaxCodedMixedBinderFields.free_iff hZ w R S a b c d A C K H U V z n v t q hw hl hU hV hh hv hField
  have hShift := TermQuotationShift.term_iff hZ (fs.get j) w U V c d C t q hw hc hd hU hV ht
  exact SyntaxTypeLocalTransfer.iff_trans hLift hShift

end PPAC.Migration.Internal.TermQuotationBinderFields
