import PPAC.Migration.Internal.TermQuotationShiftFields

/-! 原重命名关系在全部候选输出上恰好计算纯项weakenBound；实际输出见证在对象量词内消去。 -/
namespace PPAC.Migration.Internal.TermQuotationShift
open Source SourceAlgebra SourceLogic OmegaSyntax TermQuotationShiftFields
open SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket (Tree leaf)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem at_index_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (isBound : Bool) (k bLen fLen : Nat)
    (hlt : k < (if isBound then bLen else fLen)) (w U V c d C n q i : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (SyntaxNumeralSyntax.numeral bLen c)) (hd : Derives Γ (SyntaxNumeralSyntax.numeral fLen d))
    (hU : Derives Γ (SyntaxFreeShiftSyntax.shiftMap w c C U)) (hV : Derives Γ (SyntaxIdentityMapSyntax.identityMap w d V))
    (hi : Derives Γ (SyntaxNumeralSyntax.numeral k i))
    (hn : Derives Γ (OriginalTreeQuotationSyntax.tree (.node (SyntaxVariableSyntax.tag isBound) [leaf k]) w n)) :
    Derives Γ ((SyntaxRenameTermSyntax.renamed w U V c d C d n q).iff
      (OriginalTreeQuotationSyntax.tree (.node (SyntaxVariableSyntax.tag isBound) [leaf (shiftIndex isBound k)]) w q)) := by
  have ht := PureQuotationTermTyping.variable_type hZ isBound k bLen fLen hlt w c d n hw hc hd hn
  have hm : Derives Γ (SyntaxIndexMapSyntax.maps w U V c d C d) := .conjI (.conjL (.conjR hU)) (.conjL hV)
  have hex := SyntaxRenameTermExistence.for_term hZ w U V c d C d n hw hm ht
  apply Derives.conjI
  · apply Derives.impI
    exact renamed_forward (ZFContext.add hZ _) isBound k w U V c d C n q i (add hw _) (add hU _) (add hV _) (add hi _) (add hn _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    let P := OriginalTreeQuotationSyntax.tree (.node (SyntaxVariableSyntax.tag isBound) [leaf (shiftIndex isBound k)]) w q
    let Ξ := Context.add P Γ
    let Q := (Formula.mem (Fin.last m) w.castSucc).conj (SyntaxRenameTermSyntax.renamed w.castSucc U.castSucc V.castSucc c.castSucc d.castSucc C.castSucc d.castSucc n.castSucc (Fin.last m))
    let Δ := Context.add Q (Context.image Formula.raise Ξ)
    apply Derives.exE (p := Q) (add hex P)
    have hZ1 := ZFContext.under (ZFContext.add hZ P) Q
    have hw1 : Derives Δ (omega w.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (under (add hw P) Q)
    have hU1 : Derives Δ (SyntaxFreeShiftSyntax.shiftMap w.castSucc c.castSucc C.castSucc U.castSucc) := of_eq (by simp only [Formula.raise, SyntaxFreeShiftSyntax.shiftMap_rename]) (under (add hU P) Q)
    have hV1 : Derives Δ (SyntaxIdentityMapSyntax.identityMap w.castSucc d.castSucc V.castSucc) := of_eq (by simp only [Formula.raise, SyntaxIdentityMapSyntax.identityMap_rename]) (under (add hV P) Q)
    have hi1 : Derives Δ (SyntaxNumeralSyntax.numeral k i.castSucc) := of_eq (by simp only [Formula.raise, SyntaxNumeralSyntax.numeral_rename]) (under (add hi P) Q)
    have hn1 : Derives Δ (OriginalTreeQuotationSyntax.tree (.node (SyntaxVariableSyntax.tag isBound) [leaf k]) w.castSucc n.castSucc) := of_eq (by simp only [Formula.raise, OriginalTreeQuotationSyntax.tree_rename]) (under (add hn P) Q)
    have hP : Derives Ξ P := .hyp (Or.inl rfl)
    have hP1 : Derives Δ (OriginalTreeQuotationSyntax.tree (.node (SyntaxVariableSyntax.tag isBound) [leaf (shiftIndex isBound k)]) w.castSucc q.castSucc) := of_eq (by simp only [P, Formula.raise, OriginalTreeQuotationSyntax.tree_rename]) (under hP Q)
    have hQ : Derives Δ Q := .hyp (Or.inl rfl)
    have hnew := renamed_forward hZ1 isBound k w.castSucc U.castSucc V.castSucc c.castSucc d.castSucc C.castSucc n.castSucc (Fin.last m) i.castSucc hw1 hU1 hV1 hi1 hn1 (.conjR hQ)
    have heq := OriginalTreeQuotationUnique.tree_unique hZ1 (.node (SyntaxVariableSyntax.tag isBound) [leaf (shiftIndex isBound k)]) w.castSucc (Fin.last m) q.castSucc hw1 hnew hP1
    have ho := SyntaxRenameTermIdentity.output_subst w.castSucc U.castSucc V.castSucc c.castSucc d.castSucc C.castSucc d.castSucc n.castSucc (Fin.last m) q.castSucc heq (.conjR hQ)
    exact of_eq (by simp only [Formula.raise, SyntaxRenameTermSyntax.renamed_rename]) ho

theorem variable_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (isBound : Bool) (k bLen fLen : Nat)
    (hlt : k < (if isBound then bLen else fLen)) (w U V c d C n q : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (SyntaxNumeralSyntax.numeral bLen c)) (hd : Derives Γ (SyntaxNumeralSyntax.numeral fLen d))
    (hU : Derives Γ (SyntaxFreeShiftSyntax.shiftMap w c C U)) (hV : Derives Γ (SyntaxIdentityMapSyntax.identityMap w d V))
    (hn : Derives Γ (OriginalTreeQuotationSyntax.tree (.node (SyntaxVariableSyntax.tag isBound) [leaf k]) w n)) :
    Derives Γ ((SyntaxRenameTermSyntax.renamed w U V c d C d n q).iff
      (OriginalTreeQuotationSyntax.tree (.node (SyntaxVariableSyntax.tag isBound) [leaf (shiftIndex isBound k)]) w q)) := by
  have hex := SyntaxNumerals.exists_numeral hZ k w hw
  let I := (Formula.mem (Fin.last m) w.castSucc).conj (SyntaxNumeralSyntax.numeral k (Fin.last m))
  let Δ := Context.add I (Context.image Formula.raise Γ)
  apply Derives.exE (p := I) hex
  have hZ1 := ZFContext.under hZ I
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (under hw I)
  have hc1 : Derives Δ (SyntaxNumeralSyntax.numeral bLen c.castSucc) := of_eq (by simp only [Formula.raise, SyntaxNumeralSyntax.numeral_rename]) (under hc I)
  have hd1 : Derives Δ (SyntaxNumeralSyntax.numeral fLen d.castSucc) := of_eq (by simp only [Formula.raise, SyntaxNumeralSyntax.numeral_rename]) (under hd I)
  have hU1 : Derives Δ (SyntaxFreeShiftSyntax.shiftMap w.castSucc c.castSucc C.castSucc U.castSucc) := of_eq (by simp only [Formula.raise, SyntaxFreeShiftSyntax.shiftMap_rename]) (under hU I)
  have hV1 : Derives Δ (SyntaxIdentityMapSyntax.identityMap w.castSucc d.castSucc V.castSucc) := of_eq (by simp only [Formula.raise, SyntaxIdentityMapSyntax.identityMap_rename]) (under hV I)
  have hn1 : Derives Δ (OriginalTreeQuotationSyntax.tree (.node (SyntaxVariableSyntax.tag isBound) [leaf k]) w.castSucc n.castSucc) := of_eq (by simp only [Formula.raise, OriginalTreeQuotationSyntax.tree_rename]) (under hn I)
  have hI : Derives Δ I := .hyp (Or.inl rfl)
  have ho := at_index_iff hZ1 isBound k bLen fLen hlt w.castSucc U.castSucc V.castSucc c.castSucc d.castSucc C.castSucc n.castSucc q.castSucc (Fin.last m) hw1 hc1 hd1 hU1 hV1 (.conjR hI) hn1
  exact of_eq (by simp only [Formula.raise, Formula.iff, Formula.rename, SyntaxRenameTermSyntax.renamed_rename, OriginalTreeQuotationSyntax.tree_rename]) ho

theorem term_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    {bound free : PureSyntaxQuotation.Ctx} {sort : YesMetaZFC.SetTheory.SetSort} (input : PureSyntaxQuotation.Tm bound free sort)
    (w U V c d C n q : Fin m) (hw : Derives Γ (omega w))
    (hc : Derives Γ (SyntaxNumeralSyntax.numeral bound.length c)) (hd : Derives Γ (SyntaxNumeralSyntax.numeral free.length d))
    (hU : Derives Γ (SyntaxFreeShiftSyntax.shiftMap w c C U)) (hV : Derives Γ (SyntaxIdentityMapSyntax.identityMap w d V))
    (hn : Derives Γ (PureQuotationSyntax.term input w n)) :
    Derives Γ ((SyntaxRenameTermSyntax.renamed w U V c d C d n q).iff
      (PureQuotationSyntax.term (input.weakenBound YesMetaZFC.SetTheory.SetSort.set) w q)) := by
  exact match input with
  | .bvar entry => variable_iff hZ true entry.index bound.length free.length entry.index_lt_length w U V c d C n q hw hc hd hU hV hn
  | .fvar entry => variable_iff hZ false entry.index bound.length free.length entry.index_lt_length w U V c d C n q hw hc hd hU hV hn
  | .app symbol _ => nomatch symbol

end PPAC.Migration.Internal.TermQuotationShift
