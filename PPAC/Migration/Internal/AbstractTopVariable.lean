import PPAC.Migration.Internal.AbstractTopVariablePoint

/-! 实际首槽抽象环境上，原mode1零深度变量运行与独立项程序逐点等价。 -/
namespace PPAC.Migration.Internal.AbstractTopVariable
open Source SourceAlgebra SourceLogic OmegaSyntax AbstractVariableValueSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem numeric_field_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (bound : Bool) (w z a b A B R S i n q : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (he : Derives Γ (SyntaxTopCodedEnvironmentSyntax.abstractCoded w a b A B R S))
    (hi : Derives Γ (.mem i (SyntaxTermSyntax.limit bound a B))) :
    Derives Γ ((valueSpec bound w z i n q).iff
      (StructuralListFieldSyntax.field w (SyntaxIndexMapSyntax.selectMap bound R S) i q)) := by
  cases bound with
  | true =>
    let D := successor (Fin.last m) i.castSucc
    let Δ := Context.add D (Context.image Formula.raise Γ)
    apply Derives.exE (p := D) (InsertExistence.exists_insert i i (ZFContext.arithmetic hZ).base.pairing (ZFContext.arithmetic hZ).base.union)
    have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw D)
    have hz1 := of_eq (empty_rename z Fin.castSucc) (under hz D)
    have he1 := of_eq (SyntaxTopCodedEnvironmentSyntax.abstractCoded_rename w a b A B R S Fin.castSucc) (under he D)
    have hi1 : Derives Δ (.mem i.castSucc a.castSucc) := under hi D
    have hD : Derives Δ D := .hyp (Or.inl rfl)
    have ho := AbstractTopVariablePoint.bound_at_successor (ZFContext.under hZ D)
      w.castSucc z.castSucc a.castSucc b.castSucc A.castSucc B.castSucc R.castSucc S.castSucc i.castSucc (Fin.last m) n.castSucc q.castSucc hw1 hz1 he1 hi1 hD
    exact of_eq (by simp only [Formula.raise, Formula.iff, Formula.rename, valueSpec, ite_true, boundValue_rename, StructuralListFieldSyntax.field_rename, SyntaxIndexMapSyntax.selectMap]) ho
  | false =>
    have hin := SyntaxTopCodedEnvironmentTyping.abstract_input w a b A B R S he
    have hBNat := OmegaStructureAlgebra.successor_member w B b (ZFContext.arithmetic hZ).base.extensionality hw (.conjR (.conjL hin)) (.conjR (.conjR hin))
    have hiNat := StructuralListTraceOrder.member_member hZ w i B hw hBNat hi
    have hsplit := OmegaStructureInduction.decomposition w (ZFContext.separation hZ OmegaStructureSyntax.splitMatrix) hw
    apply Derives.disjE (OmegaStructureAlgebra.decomposition_at w i hsplit hiNat)
    · exact AbstractTopVariablePoint.free_at_zero (ZFContext.add hZ _) w z a b A B R S i q
        (add hw _) (add hz _) (add he _) (add hi _) (.hyp (Or.inl rfl))
    · let E := OmegaStructureSyntax.predecessor w i
      let D := (Formula.mem (Fin.last m) w.castSucc).conj (successor i.castSucc (Fin.last m))
      let Δ := Context.add D (Context.image Formula.raise (Context.add E Γ))
      apply Derives.exE (p := D) (.hyp (Or.inl rfl))
      have hw1 := of_eq (omega_rename w Fin.castSucc) (under (add hw E) D)
      have he1 := of_eq (SyntaxTopCodedEnvironmentSyntax.abstractCoded_rename w a b A B R S Fin.castSucc) (under (add he E) D)
      have hi1 : Derives Δ (.mem i.castSucc B.castSucc) := under (add hi E) D
      have hD : Derives Δ D := .hyp (Or.inl rfl)
      have ho := AbstractTopVariablePoint.free_at_successor (ZFContext.under (ZFContext.add hZ E) D)
        w.castSucc z.castSucc a.castSucc b.castSucc A.castSucc B.castSucc R.castSucc S.castSucc i.castSucc (Fin.last m) q.castSucc hw1 he1 hi1 (.conjR hD)
      exact of_eq (by simp only [Formula.raise, Formula.iff, Formula.rename, valueSpec, Bool.false_eq_true, ite_false, freeValue_rename, StructuralListFieldSyntax.field_rename, SyntaxIndexMapSyntax.selectMap]) ho

theorem program_at_variable {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (bound : Bool)
    (w mode z P a b A B R S n q i : Fin m)
    (hw : Derives Γ (omega w)) (hm : Derives Γ (SyntaxNumeralSyntax.numeral 1 mode))
    (hd : Derives Γ (OriginalTermTraceSyntax.metadata w z P)) (hz : Derives Γ (empty z))
    (he : Derives Γ (SyntaxTopCodedEnvironmentSyntax.abstractCoded w a b A B R S))
    (hi : Derives Γ (.mem i (SyntaxTermSyntax.limit bound a B))) (hv : Derives Γ (SyntaxVariableSyntax.code bound w i n)) :
    Derives Γ ((OriginalTransformRowSyntax.run 1 w mode z P n q).iff
      (TermTransformProgramSyntax.run TermTransformProgramSyntax.termProgram w R S n q)) := by
  have hr := AbstractVariableRun.run_iff hZ bound w mode z P n i q hw hm hd hv
  have hf := numeric_field_iff hZ bound w z a b A B R S i n q hw hz he hi
  have hp := TermTransformProgramVariable.at_variable hZ bound w R S n q i hw hv
  exact SyntaxTypeLocalTransfer.iff_trans hr (SyntaxTypeLocalTransfer.iff_trans hf (.conjI (.conjR hp) (.conjL hp)))

end PPAC.Migration.Internal.AbstractTopVariable
