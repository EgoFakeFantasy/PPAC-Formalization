import PPAC.Migration.Internal.TermQuotationBinderFields

/-! 实际取得并消去旧像项码，恢复提升表字段的全候选quotation；后继索引也由numeral内部解包。 -/
namespace PPAC.Migration.Internal.TermQuotationBinderValues
open Source SourceAlgebra SourceLogic OmegaSyntax
open SyntaxRenameQuerySyntax (of_eq)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem bound_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) {bound free : PureSyntaxQuotation.Ctx}
    (bs fs : List (PureSyntaxQuotation.Tm bound free)) (j : Fin bs.length) (w R S a b c d A C K H U V z n i v q : Fin m)
    (hw : Derives Γ (omega w))
    (ha : Derives Γ (SyntaxNumeralSyntax.numeral bs.length a))
    (hc : Derives Γ (SyntaxNumeralSyntax.numeral bound.length c))
    (hd : Derives Γ (SyntaxNumeralSyntax.numeral free.length d))
    (he : Derives Γ (TermQuotationEnvironmentSyntax.environment bs fs w a b c d R S))
    (hl : Derives Γ (SyntaxCodedMixedBinderSyntax.lifted w R S a b c d A C K H))
    (hU : Derives Γ (SyntaxFreeShiftSyntax.shiftMap w c C U))
    (hV : Derives Γ (SyntaxIdentityMapSyntax.identityMap w d V))
    (hh : Derives Γ (SyntaxMixedImageHead.head w C d z n))
    (hj : Derives Γ (SyntaxNumeralSyntax.numeral j.val v))
    (hi : Derives Γ (successor i v)) :
    Derives Γ (((Formula.mem i A).conj (StructuralListFieldSyntax.field w K i q)).iff
      (PureQuotationSyntax.term ((bs.get j).weakenBound YesMetaZFC.SetTheory.SetSort.set) w q)) := by
  have hex := OriginalTreeQuotationExistence.tree_exists hZ (PureSyntaxQuotation.termTree (bs.get j)) w hw
  let P := (Formula.mem (Fin.last m) w.castSucc).conj (PureQuotationSyntax.term (bs.get j) w.castSucc (Fin.last m))
  let Δ := Context.add P (Context.image Formula.raise Γ)
  apply Derives.exE (p := P) hex
  have hZ1 := ZFContext.under hZ P
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (under hw P)
  have ha1 : Derives Δ (SyntaxNumeralSyntax.numeral bs.length a.castSucc) := of_eq (by simp only [Formula.raise, SyntaxNumeralSyntax.numeral_rename]) (under ha P)
  have hc1 : Derives Δ (SyntaxNumeralSyntax.numeral bound.length c.castSucc) := of_eq (by simp only [Formula.raise, SyntaxNumeralSyntax.numeral_rename]) (under hc P)
  have hd1 : Derives Δ (SyntaxNumeralSyntax.numeral free.length d.castSucc) := of_eq (by simp only [Formula.raise, SyntaxNumeralSyntax.numeral_rename]) (under hd P)
  have he1 : Derives Δ (TermQuotationEnvironmentSyntax.environment bs fs w.castSucc a.castSucc b.castSucc c.castSucc d.castSucc R.castSucc S.castSucc) := of_eq (by simp only [Formula.raise, TermQuotationEnvironmentSyntax.environment_rename]) (under he P)
  have hl1 : Derives Δ (SyntaxCodedMixedBinderSyntax.lifted w.castSucc R.castSucc S.castSucc a.castSucc b.castSucc c.castSucc d.castSucc A.castSucc C.castSucc K.castSucc H.castSucc) := of_eq (by simp only [Formula.raise, SyntaxCodedMixedBinderSyntax.lifted_rename]) (under hl P)
  have hU1 : Derives Δ (SyntaxFreeShiftSyntax.shiftMap w.castSucc c.castSucc C.castSucc U.castSucc) := of_eq (by simp only [Formula.raise, SyntaxFreeShiftSyntax.shiftMap_rename]) (under hU P)
  have hV1 : Derives Δ (SyntaxIdentityMapSyntax.identityMap w.castSucc d.castSucc V.castSucc) := of_eq (by simp only [Formula.raise, SyntaxIdentityMapSyntax.identityMap_rename]) (under hV P)
  have hh1 : Derives Δ (SyntaxMixedImageHead.head w.castSucc C.castSucc d.castSucc z.castSucc n.castSucc) := of_eq (by simp only [Formula.raise, SyntaxMixedImageHead.head_rename]) (under hh P)
  have hj1 : Derives Δ (SyntaxNumeralSyntax.numeral j.val v.castSucc) := of_eq (by simp only [Formula.raise, SyntaxNumeralSyntax.numeral_rename]) (under hj P)
  have hi1 : Derives Δ (successor i.castSucc v.castSucc) := of_eq (by simp only [Formula.raise, successor_rename]) (under hi P)
  have hP : Derives Δ P := .hyp (Or.inl rfl)
  have ho := TermQuotationBinderFields.bound_at_code hZ1 bs fs j w.castSucc R.castSucc S.castSucc a.castSucc b.castSucc c.castSucc d.castSucc A.castSucc C.castSucc K.castSucc H.castSucc U.castSucc V.castSucc z.castSucc n.castSucc i.castSucc v.castSucc (Fin.last m) q.castSucc hw1 ha1 hc1 hd1 he1 hl1 hU1 hV1 hh1 hj1 hi1 (.conjR hP)
  exact of_eq (by simp only [Formula.raise, Formula.iff, Formula.rename, StructuralListFieldSyntax.field_rename, PureQuotationSyntax.term_rename]) ho

theorem free_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) {bound free : PureSyntaxQuotation.Ctx}
    (bs fs : List (PureSyntaxQuotation.Tm bound free)) (j : Fin fs.length) (w R S a b c d A C K H U V z n v q : Fin m)
    (hw : Derives Γ (omega w))
    (hb : Derives Γ (SyntaxNumeralSyntax.numeral fs.length b))
    (hc : Derives Γ (SyntaxNumeralSyntax.numeral bound.length c))
    (hd : Derives Γ (SyntaxNumeralSyntax.numeral free.length d))
    (he : Derives Γ (TermQuotationEnvironmentSyntax.environment bs fs w a b c d R S))
    (hl : Derives Γ (SyntaxCodedMixedBinderSyntax.lifted w R S a b c d A C K H))
    (hU : Derives Γ (SyntaxFreeShiftSyntax.shiftMap w c C U))
    (hV : Derives Γ (SyntaxIdentityMapSyntax.identityMap w d V))
    (hh : Derives Γ (SyntaxMixedImageHead.head w C d z n))
    (hj : Derives Γ (SyntaxNumeralSyntax.numeral j.val v)) :
    Derives Γ (((Formula.mem v b).conj (StructuralListFieldSyntax.field w H v q)).iff
      (PureQuotationSyntax.term ((fs.get j).weakenBound YesMetaZFC.SetTheory.SetSort.set) w q)) := by
  have hex := OriginalTreeQuotationExistence.tree_exists hZ (PureSyntaxQuotation.termTree (fs.get j)) w hw
  let P := (Formula.mem (Fin.last m) w.castSucc).conj (PureQuotationSyntax.term (fs.get j) w.castSucc (Fin.last m))
  let Δ := Context.add P (Context.image Formula.raise Γ)
  apply Derives.exE (p := P) hex
  have hZ1 := ZFContext.under hZ P
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (under hw P)
  have hb1 : Derives Δ (SyntaxNumeralSyntax.numeral fs.length b.castSucc) := of_eq (by simp only [Formula.raise, SyntaxNumeralSyntax.numeral_rename]) (under hb P)
  have hc1 : Derives Δ (SyntaxNumeralSyntax.numeral bound.length c.castSucc) := of_eq (by simp only [Formula.raise, SyntaxNumeralSyntax.numeral_rename]) (under hc P)
  have hd1 : Derives Δ (SyntaxNumeralSyntax.numeral free.length d.castSucc) := of_eq (by simp only [Formula.raise, SyntaxNumeralSyntax.numeral_rename]) (under hd P)
  have he1 : Derives Δ (TermQuotationEnvironmentSyntax.environment bs fs w.castSucc a.castSucc b.castSucc c.castSucc d.castSucc R.castSucc S.castSucc) := of_eq (by simp only [Formula.raise, TermQuotationEnvironmentSyntax.environment_rename]) (under he P)
  have hl1 : Derives Δ (SyntaxCodedMixedBinderSyntax.lifted w.castSucc R.castSucc S.castSucc a.castSucc b.castSucc c.castSucc d.castSucc A.castSucc C.castSucc K.castSucc H.castSucc) := of_eq (by simp only [Formula.raise, SyntaxCodedMixedBinderSyntax.lifted_rename]) (under hl P)
  have hU1 : Derives Δ (SyntaxFreeShiftSyntax.shiftMap w.castSucc c.castSucc C.castSucc U.castSucc) := of_eq (by simp only [Formula.raise, SyntaxFreeShiftSyntax.shiftMap_rename]) (under hU P)
  have hV1 : Derives Δ (SyntaxIdentityMapSyntax.identityMap w.castSucc d.castSucc V.castSucc) := of_eq (by simp only [Formula.raise, SyntaxIdentityMapSyntax.identityMap_rename]) (under hV P)
  have hh1 : Derives Δ (SyntaxMixedImageHead.head w.castSucc C.castSucc d.castSucc z.castSucc n.castSucc) := of_eq (by simp only [Formula.raise, SyntaxMixedImageHead.head_rename]) (under hh P)
  have hj1 : Derives Δ (SyntaxNumeralSyntax.numeral j.val v.castSucc) := of_eq (by simp only [Formula.raise, SyntaxNumeralSyntax.numeral_rename]) (under hj P)
  have hP : Derives Δ P := .hyp (Or.inl rfl)
  have ho := TermQuotationBinderFields.free_at_code hZ1 bs fs j w.castSucc R.castSucc S.castSucc a.castSucc b.castSucc c.castSucc d.castSucc A.castSucc C.castSucc K.castSucc H.castSucc U.castSucc V.castSucc z.castSucc n.castSucc v.castSucc (Fin.last m) q.castSucc hw1 hb1 hc1 hd1 he1 hl1 hU1 hV1 hh1 hj1 (.conjR hP)
  exact of_eq (by simp only [Formula.raise, Formula.iff, Formula.rename, StructuralListFieldSyntax.field_rename, PureQuotationSyntax.term_rename]) ho

theorem bound_at_numeral {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) {bound free : PureSyntaxQuotation.Ctx}
    (bs fs : List (PureSyntaxQuotation.Tm bound free)) (j : Fin bs.length) (w R S a b c d A C K H U V z n i q : Fin m)
    (hw : Derives Γ (omega w))
    (ha : Derives Γ (SyntaxNumeralSyntax.numeral bs.length a))
    (hc : Derives Γ (SyntaxNumeralSyntax.numeral bound.length c))
    (hd : Derives Γ (SyntaxNumeralSyntax.numeral free.length d))
    (he : Derives Γ (TermQuotationEnvironmentSyntax.environment bs fs w a b c d R S))
    (hl : Derives Γ (SyntaxCodedMixedBinderSyntax.lifted w R S a b c d A C K H))
    (hU : Derives Γ (SyntaxFreeShiftSyntax.shiftMap w c C U))
    (hV : Derives Γ (SyntaxIdentityMapSyntax.identityMap w d V))
    (hh : Derives Γ (SyntaxMixedImageHead.head w C d z n))
    (hi : Derives Γ (SyntaxNumeralSyntax.numeral (j.val+1) i)) :
    Derives Γ (((Formula.mem i A).conj (StructuralListFieldSyntax.field w K i q)).iff
      (PureQuotationSyntax.term ((bs.get j).weakenBound YesMetaZFC.SetTheory.SetSort.set) w q)) := by
  let I := (SyntaxNumeralSyntax.numeral j.val (Fin.last m)).conj (successor i.castSucc (Fin.last m))
  let Δ := Context.add I (Context.image Formula.raise Γ)
  apply SyntaxNumeralSyntax.eliminate_succ j.val i _ hi
  have hZ1 := ZFContext.under hZ I
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (under hw I)
  have ha1 : Derives Δ (SyntaxNumeralSyntax.numeral bs.length a.castSucc) := of_eq (by simp only [Formula.raise, SyntaxNumeralSyntax.numeral_rename]) (under ha I)
  have hc1 : Derives Δ (SyntaxNumeralSyntax.numeral bound.length c.castSucc) := of_eq (by simp only [Formula.raise, SyntaxNumeralSyntax.numeral_rename]) (under hc I)
  have hd1 : Derives Δ (SyntaxNumeralSyntax.numeral free.length d.castSucc) := of_eq (by simp only [Formula.raise, SyntaxNumeralSyntax.numeral_rename]) (under hd I)
  have he1 : Derives Δ (TermQuotationEnvironmentSyntax.environment bs fs w.castSucc a.castSucc b.castSucc c.castSucc d.castSucc R.castSucc S.castSucc) := of_eq (by simp only [Formula.raise, TermQuotationEnvironmentSyntax.environment_rename]) (under he I)
  have hl1 : Derives Δ (SyntaxCodedMixedBinderSyntax.lifted w.castSucc R.castSucc S.castSucc a.castSucc b.castSucc c.castSucc d.castSucc A.castSucc C.castSucc K.castSucc H.castSucc) := of_eq (by simp only [Formula.raise, SyntaxCodedMixedBinderSyntax.lifted_rename]) (under hl I)
  have hU1 : Derives Δ (SyntaxFreeShiftSyntax.shiftMap w.castSucc c.castSucc C.castSucc U.castSucc) := of_eq (by simp only [Formula.raise, SyntaxFreeShiftSyntax.shiftMap_rename]) (under hU I)
  have hV1 : Derives Δ (SyntaxIdentityMapSyntax.identityMap w.castSucc d.castSucc V.castSucc) := of_eq (by simp only [Formula.raise, SyntaxIdentityMapSyntax.identityMap_rename]) (under hV I)
  have hh1 : Derives Δ (SyntaxMixedImageHead.head w.castSucc C.castSucc d.castSucc z.castSucc n.castSucc) := of_eq (by simp only [Formula.raise, SyntaxMixedImageHead.head_rename]) (under hh I)
  have hI : Derives Δ I := .hyp (Or.inl rfl)
  have ho := bound_iff hZ1 bs fs j w.castSucc R.castSucc S.castSucc a.castSucc b.castSucc c.castSucc d.castSucc A.castSucc C.castSucc K.castSucc H.castSucc U.castSucc V.castSucc z.castSucc n.castSucc i.castSucc (Fin.last m) q.castSucc hw1 ha1 hc1 hd1 he1 hl1 hU1 hV1 hh1 (.conjL hI) (.conjR hI)
  exact of_eq (by simp only [Formula.raise, Formula.iff, Formula.rename, StructuralListFieldSyntax.field_rename, PureQuotationSyntax.term_rename]) ho

theorem zero_at_numeral {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w R S a b c d A C K H U V z n i q : Fin m)
    (hw : Derives Γ (omega w)) (hl : Derives Γ (SyntaxCodedMixedBinderSyntax.lifted w R S a b c d A C K H))
    (hU : Derives Γ (SyntaxFreeShiftSyntax.shiftMap w c C U)) (hV : Derives Γ (SyntaxIdentityMapSyntax.identityMap w d V))
    (hh : Derives Γ (SyntaxMixedImageHead.head w C d z n)) (hi : Derives Γ (SyntaxNumeralSyntax.numeral 0 i)) :
    Derives Γ ((StructuralListFieldSyntax.field w K i q).iff
      (OriginalTreeQuotationSyntax.tree (.node 0 [YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.leaf 0]) w q)) := by
  have heq := OmegaUniversal.empty_unique z i (ZFContext.arithmetic hZ).base.extensionality (.conjL hh) hi
  have hcode := SyntaxRenameTermSyntax.code_index_subst true w z i n heq (.conjL (.conjR hh))
  have hnew : Derives Γ (SyntaxMixedImageHead.head w C d i n) := .conjI hi (.conjI hcode (.conjR (.conjR hh)))
  have hInput := SyntaxCodedMixedBinderTyping.input_of_lifted w R S a b c d A C K H hl
  have hm := SyntaxIndexLiftOrder.zero_member hZ w a A i hw (.conjL (.conjL (.conjL hInput))) (.conjL (.conjR hInput)) hi
  have hiff := TermQuotationBinderFields.zero_iff hZ w R S a b c d A C K H U V i n q hw hl hU hV hnew
  exact TermQuotationBinderFields.drop_member _ _ _ hm hiff

end PPAC.Migration.Internal.TermQuotationBinderValues
