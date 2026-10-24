import PPAC.Migration.Internal.InstantiateVariableSpecialization
import PPAC.Migration.Internal.InstantiateOperationFrameSyntax
import PPAC.Migration.Internal.AbstractTopVariablePoint
import PPAC.Migration.Internal.AbstractBinderRename

/-! 实际 InstantiateTop 在空绑定目标上的根框架；兼容性由原环境字段律推出。 -/
namespace PPAC.Migration.Internal.InstantiateOperationFrameRoot
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax InstantiateOperationFrameSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem member_successor_empty {m} {Γ : Context m} (z A i : Fin m)
    (hz : Derives Γ (empty z)) (hA : Derives Γ (successor A z)) (hi : Derives Γ (.mem i A)) :
    Derives Γ (.equal i z) := by
  apply Derives.disjE (InsertLogic.member_cases A z z i hA hi)
  · exact .botE (.impE (add (empty_at z i hz) _) (.hyp (Or.inl rfl)))
  · exact .hyp (Or.inl rfl)

theorem numeric_field_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (bound : Bool)
    (w z b A P R S i n q : Fin m) (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (he : Derives Γ (SyntaxTopCodedEnvironmentSyntax.instantiateCoded w z b A P R S))
    (hi : Derives Γ (.mem i (SyntaxTermSyntax.limit bound A b)))
    (hv : Derives Γ (SyntaxVariableSyntax.code bound w i n)) :
    Derives Γ ((InstantiateVariableValueSyntax.valueSpec bound w z P i n q).iff
      (StructuralListFieldSyntax.field w (SyntaxIndexMapSyntax.selectMap bound R S) i q)) := by
  cases bound with
  | true =>
    have hin := SyntaxTopCodedEnvironmentTyping.instantiate_input w z b A P R S he
    have hEq := member_successor_empty z A i hz (.conjR hin) hi
    have hi0 : Derives Γ (empty i) := by
      let F := empty (Fin.last m)
      have hzF : Derives Γ (F.instantiate z) := of_eq (by simp only [F, Formula.instantiate, empty_rename, Fin.lastCases_last]) hz
      exact of_eq (by simp only [F, Formula.instantiate, empty_rename, Fin.lastCases_last]) (Derives.eqSubst F (eq_symm hEq) hzF)
    have hn := InstantiateVariableSpecialization.at_point_iff hZ w z P i n q hEq
    have hf := AbstractTopVariablePoint.remove_scope hi (SyntaxTopCodedEnvironmentFields.instantiate_zero hZ w z b A P R S i q hw he hi0)
    exact SyntaxTypeLocalTransfer.iff_trans hn (.conjI (.conjR hf) (.conjL hf))
  | false =>
    have hn := AbstractBinderRename.code_iff_equal hZ false w i n q hw hv
    have hf := AbstractTopVariablePoint.remove_scope hi (SyntaxTopCodedEnvironmentFields.instantiate_free hZ w z b A P R S i q he hi)
    exact SyntaxTypeLocalTransfer.iff_trans (.conjI (.conjR hn) (.conjL hn)) (.conjI (.conjR hf) (.conjL hf))

theorem compatible_from_actual {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (bound : Bool)
    (w z b A P R S : Fin m) (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (he : Derives Γ (SyntaxTopCodedEnvironmentSyntax.instantiateCoded w z b A P R S)) :
    Derives Γ (compatible bound w z P A b R S) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  let G := (Formula.mem (slot 3 0) (SyntaxTermSyntax.limit bound (old 3 A) (old 3 b))).conj
    (SyntaxVariableSyntax.code bound (old 3 w) (slot 3 0) (slot 3 1))
  let Δ := Context.add G (raisedContext 3 Γ)
  have hw3 : Derives Δ (omega (old 3 w)) := of_eq (omega_rename w (old 3)) (HornBinderRules.under_body 3 hw G)
  have hz3 : Derives Δ (empty (old 3 z)) := of_eq (empty_rename z (old 3)) (HornBinderRules.under_body 3 hz G)
  have he3 : Derives Δ (SyntaxTopCodedEnvironmentSyntax.instantiateCoded (old 3 w) (old 3 z) (old 3 b) (old 3 A) (old 3 P) (old 3 R) (old 3 S)) :=
    of_eq (SyntaxTopCodedEnvironmentSyntax.instantiateCoded_rename w z b A P R S (old 3)) (HornBinderRules.under_body 3 he G)
  have hG : Derives Δ G := .hyp (Or.inl rfl)
  exact numeric_field_iff (HornBinderRules.zf_body 3 hZ G) bound (old 3 w) (old 3 z) (old 3 b) (old 3 A) (old 3 P) (old 3 R) (old 3 S)
    (slot 3 0) (slot 3 1) (slot 3 2) hw3 hz3 he3 (.conjL hG) (.conjR hG)

theorem from_actual {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w mode z P b A R S : Fin m)
    (hw : Derives Γ (omega w)) (hm : Derives Γ (SyntaxNumeralSyntax.numeral 2 mode))
    (hd : Derives Γ (OriginalTermTraceSyntax.metadata w z P)) (hz : Derives Γ (empty z))
    (he : Derives Γ (SyntaxTopCodedEnvironmentSyntax.instantiateCoded w z b A P R S)) :
    Derives Γ (frame w mode z P A b z b R S) := by
  have hin := SyntaxTopCodedEnvironmentTyping.instantiate_input w z b A P R S he
  exact .conjI hm (.conjI hd
    (.conjI (intro_closedParameter w b P z hz (.conjL hin))
      (.conjI (SyntaxTopCodedEnvironmentTyping.instantiate_lists w z b A P R S he)
        (.conjI (compatible_from_actual hZ true w z b A P R S hw hz he)
          (.conjI (compatible_from_actual hZ false w z b A P R S hw hz he)
            (.conjI (.conjR hin) (.conjI (.eqRefl z) (.eqRefl b))))))))

theorem from_actual_input {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w mode z P b A R S : Fin m)
    (hw : Derives Γ (omega w)) (hm : Derives Γ (SyntaxNumeralSyntax.numeral 2 mode))
    (hz : Derives Γ (empty z))
    (he : Derives Γ (SyntaxTopCodedEnvironmentSyntax.instantiateCoded w z b A P R S)) :
    Derives Γ (frame w mode z P A b z b R S) := by
  have hin := SyntaxTopCodedEnvironmentTyping.instantiate_input w z b A P R S he
  have hzNat := OmegaStructureAlgebra.zero_member w z (ZFContext.arithmetic hZ).base.extensionality hw hz
  have hpNat := SyntaxTerms.range hZ w z b P hw (.conjL hin)
  exact from_actual hZ w mode z P b A R S hw hm (.conjI hzNat hpNat) hz he

end PPAC.Migration.Internal.InstantiateOperationFrameRoot
