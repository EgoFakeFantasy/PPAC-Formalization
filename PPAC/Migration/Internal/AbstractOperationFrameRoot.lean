import PPAC.Migration.Internal.AbstractOperationFrameSyntax

/-! 实际首槽抽象码表在零深度满足任意深度frame的真实根实例，不外加兼容性假设。 -/
namespace PPAC.Migration.Internal.AbstractOperationFrameRoot
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax AbstractOperationFrameSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem compatible_from_actual {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (bound : Bool)
    (w z a b A B R S : Fin m) (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (he : Derives Γ (SyntaxTopCodedEnvironmentSyntax.abstractCoded w a b A B R S)) :
    Derives Γ (compatible bound w z a B R S) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  let G := (Formula.mem (slot 3 0) (SyntaxTermSyntax.limit bound (old 3 a) (old 3 B))).conj
    (SyntaxVariableSyntax.code bound (old 3 w) (slot 3 0) (slot 3 1))
  let Δ := Context.add G (raisedContext 3 Γ)
  have hw3 : Derives Δ (omega (old 3 w)) := of_eq (omega_rename w (old 3)) (HornBinderRules.under_body 3 hw G)
  have hz3 : Derives Δ (empty (old 3 z)) := of_eq (empty_rename z (old 3)) (HornBinderRules.under_body 3 hz G)
  have he3 : Derives Δ (SyntaxTopCodedEnvironmentSyntax.abstractCoded (old 3 w) (old 3 a) (old 3 b) (old 3 A) (old 3 B) (old 3 R) (old 3 S)) := of_eq (SyntaxTopCodedEnvironmentSyntax.abstractCoded_rename w a b A B R S (old 3)) (HornBinderRules.under_body 3 he G)
  have hG : Derives Δ G := .hyp (Or.inl rfl)
  exact AbstractTopVariable.numeric_field_iff (HornBinderRules.zf_body 3 hZ G) bound (old 3 w) (old 3 z) (old 3 a) (old 3 b) (old 3 A) (old 3 B) (old 3 R) (old 3 S) (slot 3 0) (slot 3 1) (slot 3 2) hw3 hz3 he3 (.conjL hG)

theorem from_actual {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w mode z P a b A B R S : Fin m)
    (hw : Derives Γ (omega w)) (hm : Derives Γ (SyntaxNumeralSyntax.numeral 1 mode))
    (hd : Derives Γ (OriginalTermTraceSyntax.metadata w z P)) (hz : Derives Γ (empty z))
    (he : Derives Γ (SyntaxTopCodedEnvironmentSyntax.abstractCoded w a b A B R S)) :
    Derives Γ (frame w mode z P a B A b R S) :=
  .conjI hm (.conjI hd (.conjI (SyntaxTopCodedEnvironmentTyping.abstract_lists w a b A B R S he)
    (.conjI (compatible_from_actual hZ true w z a b A B R S hw hz he)
      (compatible_from_actual hZ false w z a b A B R S hw hz he))))

end PPAC.Migration.Internal.AbstractOperationFrameRoot
