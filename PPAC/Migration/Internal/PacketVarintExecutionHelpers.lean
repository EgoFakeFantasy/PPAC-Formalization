import PPAC.Migration.Internal.PacketVarintExecutionSyntax

/-! Real quotient bounds authorize each smaller IH; original equalities transport actual graphs and constructors. -/
namespace PPAC.Migration.Internal.PacketVarintExecutionHelpers
open Source SourceAlgebra SourceLogic OmegaSyntax PacketVarintSyntax PacketByteInputSyntax PacketVarintExecutionSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem cases_at {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B n s : Fin m) (hw : Derives Γ (omega w))
    (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B)) (hc : Derives Γ (canonical w n s)) : Derives Γ (PacketVarintCanonicalRecursionSyntax.atCriterion true w B n s) :=
  .impE (.conjL (PacketVarintCanonicalRecursionBridge.at_actual_iff hZ w B n s hw hB)) (PacketVarintDomain.at_radix hZ w B n s hB hc)

theorem below_property {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B n d q : Fin m) (hw : Derives Γ (omega w))
    (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B)) (hi : Derives Γ (earlier w n))
    (ha : Derives Γ (PacketAffineSyntax.affine w B d q n)) (hq : Derives Γ (empty q).neg) : Derives Γ (property w q) :=
  earlier_at w n q hi (PacketAffineCore.tail_guard _ _ _ _ _ ha) (.impE (.conjR (PacketDivisionDescentCore.quotient_bounds hZ false w B d q n hw hB ha)) hq)

theorem list_natural {m} {Γ : Context m} (w n s : Fin m) (hc : Derives Γ (canonical w n s)) : Derives Γ (.mem s w) :=
  StructuralListValidity.range _ _ (.conjL (.conjR (PacketVarintDomain.domain w n s hc)))

theorem cons_tail {m} {Γ : Context m} (w h x s y : Fin m) (he : Derives Γ (.equal x y))
    (hc : Derives Γ (StructuralListSyntax.consCode w h x s)) : Derives Γ (StructuralListSyntax.consCode w h y s) := by
  let P := StructuralListSyntax.consCode w.castSucc h.castSucc (Fin.last m) s.castSucc
  have h0 : P.instantiate x = StructuralListSyntax.consCode w h x s := by simp only [P,Formula.instantiate,StructuralListSyntax.consCode_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  have h1 : P.instantiate y = StructuralListSyntax.consCode w h y s := by simp only [P,Formula.instantiate,StructuralListSyntax.consCode_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  exact of_eq h1 (Derives.eqSubst P he (of_eq h0.symm hc))

theorem canonical_input {m} {Γ : Context m} (w n s k : Fin m) (he : Derives Γ (.equal n k)) (hc : Derives Γ (canonical w n s)) : Derives Γ (canonical w k s) := by
  let P := canonical w.castSucc (Fin.last m) s.castSucc
  have h0 : P.instantiate n = canonical w n s := by simp only [P,Formula.instantiate,canonical_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  have h1 : P.instantiate k = canonical w k s := by simp only [P,Formula.instantiate,canonical_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  exact of_eq h1 (Derives.eqSubst P he (of_eq h0.symm hc))

theorem sum_left {m} {Γ : Context m} (w d B h e : Fin m) (he : Derives Γ (.equal d e)) (hs : Derives Γ (NaturalAdditionSyntax.sum w d B h)) : Derives Γ (NaturalAdditionSyntax.sum w e B h) := by
  let P := NaturalAdditionSyntax.sum w.castSucc (Fin.last m) B.castSucc h.castSucc
  have h0 : P.instantiate d = NaturalAdditionSyntax.sum w d B h := by simp only [P,Formula.instantiate,NaturalAdditionSyntax.sum_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  have h1 : P.instantiate e = NaturalAdditionSyntax.sum w e B h := by simp only [P,Formula.instantiate,NaturalAdditionSyntax.sum_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  exact of_eq h1 (Derives.eqSubst P he (of_eq h0.symm hs))

theorem nil_input {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w s : Fin m) (hw : Derives Γ (omega w))
    (hs : Derives Γ (StructuralListSyntax.nilCode w s)) : Derives Γ (byteList w s) :=
  .impE (.conjR (PacketByteInputLaws.actual_iff hZ w s hw)) (.disjL hs)

theorem cons_input {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w s h x : Fin m) (hw : Derives Γ (omega w))
    (hs : Derives Γ (StructuralListSyntax.consCode w h x s)) (hh : Derives Γ (byte h)) (hx : Derives Γ (byteList w x)) : Derives Γ (byteList w s) :=
  .impE (.conjR (PacketByteInputLaws.actual_iff hZ w s hw)) (.disjR (PacketByteInputRecursionSyntax.intro_actual_cons w s h x hs hh hx))

end PPAC.Migration.Internal.PacketVarintExecutionHelpers
