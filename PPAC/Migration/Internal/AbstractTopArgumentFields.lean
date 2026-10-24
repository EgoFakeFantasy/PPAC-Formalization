import PPAC.Migration.Internal.AbstractTopTermFiber
import PPAC.Migration.Internal.SmallModeArgumentFieldCompletion

/-! 实际零深度抽象码表下，原列表全部字段运行与独立项程序的逐字段像等价。 -/
namespace PPAC.Migration.Internal.AbstractTopArgumentFields
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem fields_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w mode z P a b A B R S n q k : Fin m)
    (hw : Derives Γ (omega w)) (hm : Derives Γ (SyntaxNumeralSyntax.numeral 1 mode))
    (hd : Derives Γ (OriginalTermTraceSyntax.metadata w z P)) (hz : Derives Γ (empty z))
    (he : Derives Γ (SyntaxTopCodedEnvironmentSyntax.abstractCoded w a b A B R S))
    (hL : Derives Γ (SyntaxMixedImageCodeSyntax.termList w k a B n)) :
    Derives Γ ((OriginalArgumentFieldSyntax.fields w mode z P k n q).iff (ArgumentProgramFieldSyntax.fields w R S k n q)) := by
  apply Derives.conjI
  · apply Derives.impI
    let E := OriginalArgumentFieldSyntax.fields w mode z P k n q
    have hEF : Derives (Context.add E Γ) E := .hyp (Or.inl rfl)
    apply Derives.allI
    apply Derives.allI
    apply Derives.allI
    apply Derives.impI
    let C := (Formula.mem (slot 3 0) (old 3 k)).conj
      ((StructuralListFieldSyntax.field (old 3 w) (old 3 n) (slot 3 0) (slot 3 1)).conj
        (StructuralListFieldSyntax.field (old 3 w) (old 3 q) (slot 3 0) (slot 3 2)))
    let Δ := Context.add C (raisedContext 3 (Context.add E Γ))
    have hZ3 := HornBinderRules.zf_body 3 (ZFContext.add hZ E) C
    have hw3 : Derives Δ (omega (old 3 w)) := of_eq (by simp only [omega_rename]) (HornBinderRules.under_body 3 (add hw E) C)
    have hm3 : Derives Δ (SyntaxNumeralSyntax.numeral 1 (old 3 mode)) := of_eq (by simp only [SyntaxNumeralSyntax.numeral_rename]) (HornBinderRules.under_body 3 (add hm E) C)
    have hd3 : Derives Δ (OriginalTermTraceSyntax.metadata (old 3 w) (old 3 z) (old 3 P)) := of_eq (by simp only [OriginalTermTraceSyntax.metadata_rename]) (HornBinderRules.under_body 3 (add hd E) C)
    have hz3 : Derives Δ (empty (old 3 z)) := of_eq (by simp only [empty_rename]) (HornBinderRules.under_body 3 (add hz E) C)
    have he3 : Derives Δ (SyntaxTopCodedEnvironmentSyntax.abstractCoded (old 3 w) (old 3 a) (old 3 b) (old 3 A) (old 3 B) (old 3 R) (old 3 S)) := of_eq (by simp only [SyntaxTopCodedEnvironmentSyntax.abstractCoded_rename]) (HornBinderRules.under_body 3 (add he E) C)
    have hL3 : Derives Δ (SyntaxMixedImageCodeSyntax.termList (old 3 w) (old 3 k) (old 3 a) (old 3 B) (old 3 n)) := of_eq (by simp only [SyntaxMixedImageCodeSyntax.termList_rename]) (HornBinderRules.under_body 3 (add hL E) C)
    have hF : Derives Δ (OriginalArgumentFieldSyntax.fields (old 3 w) (old 3 mode) (old 3 z) (old 3 P) (old 3 k) (old 3 n) (old 3 q)) := of_eq (OriginalArgumentFieldSyntax.fields_rename w mode z P k n q (old 3)) (HornBinderRules.under_body 3 hEF C)
    have hC : Derives Δ C := .hyp (Or.inl rfl)
    have hTyped := SyntaxMixedImageCodeFields.field_type (old 3 w) (old 3 k) (old 3 a) (old 3 B) (old 3 n) (slot 3 0) (slot 3 1)
      hL3 (.conjL hC) (.conjL (.conjR hC))
    have hiff := AbstractTopTerm.program_iff hZ3 (old 3 w) (old 3 mode) (old 3 z) (old 3 P)
      (old 3 a) (old 3 b) (old 3 A) (old 3 B) (old 3 R) (old 3 S) (slot 3 1) (slot 3 2) hw3 hm3 hd3 hz3 he3 hTyped
    have hRel := OriginalArgumentFieldSyntax.fields_at (old 3 w) (old 3 mode) (old 3 z) (old 3 P) (old 3 k) (old 3 n) (old 3 q)
      (slot 3 0) (slot 3 1) (slot 3 2) hF (.conjL hC) (.conjL (.conjR hC)) (.conjR (.conjR hC))
    exact .impE (.conjL hiff) hRel
  · apply Derives.impI
    let E := ArgumentProgramFieldSyntax.fields w R S k n q
    have hEF : Derives (Context.add E Γ) E := .hyp (Or.inl rfl)
    apply Derives.allI
    apply Derives.allI
    apply Derives.allI
    apply Derives.impI
    let C := (Formula.mem (slot 3 0) (old 3 k)).conj
      ((StructuralListFieldSyntax.field (old 3 w) (old 3 n) (slot 3 0) (slot 3 1)).conj
        (StructuralListFieldSyntax.field (old 3 w) (old 3 q) (slot 3 0) (slot 3 2)))
    let Δ := Context.add C (raisedContext 3 (Context.add E Γ))
    have hZ3 := HornBinderRules.zf_body 3 (ZFContext.add hZ E) C
    have hw3 : Derives Δ (omega (old 3 w)) := of_eq (by simp only [omega_rename]) (HornBinderRules.under_body 3 (add hw E) C)
    have hm3 : Derives Δ (SyntaxNumeralSyntax.numeral 1 (old 3 mode)) := of_eq (by simp only [SyntaxNumeralSyntax.numeral_rename]) (HornBinderRules.under_body 3 (add hm E) C)
    have hd3 : Derives Δ (OriginalTermTraceSyntax.metadata (old 3 w) (old 3 z) (old 3 P)) := of_eq (by simp only [OriginalTermTraceSyntax.metadata_rename]) (HornBinderRules.under_body 3 (add hd E) C)
    have hz3 : Derives Δ (empty (old 3 z)) := of_eq (by simp only [empty_rename]) (HornBinderRules.under_body 3 (add hz E) C)
    have he3 : Derives Δ (SyntaxTopCodedEnvironmentSyntax.abstractCoded (old 3 w) (old 3 a) (old 3 b) (old 3 A) (old 3 B) (old 3 R) (old 3 S)) := of_eq (by simp only [SyntaxTopCodedEnvironmentSyntax.abstractCoded_rename]) (HornBinderRules.under_body 3 (add he E) C)
    have hL3 : Derives Δ (SyntaxMixedImageCodeSyntax.termList (old 3 w) (old 3 k) (old 3 a) (old 3 B) (old 3 n)) := of_eq (by simp only [SyntaxMixedImageCodeSyntax.termList_rename]) (HornBinderRules.under_body 3 (add hL E) C)
    have hF : Derives Δ (ArgumentProgramFieldSyntax.fields (old 3 w) (old 3 R) (old 3 S) (old 3 k) (old 3 n) (old 3 q)) := of_eq (ArgumentProgramFieldSyntax.fields_rename w R S k n q (old 3)) (HornBinderRules.under_body 3 hEF C)
    have hC : Derives Δ C := .hyp (Or.inl rfl)
    have hTyped := SyntaxMixedImageCodeFields.field_type (old 3 w) (old 3 k) (old 3 a) (old 3 B) (old 3 n) (slot 3 0) (slot 3 1)
      hL3 (.conjL hC) (.conjL (.conjR hC))
    have hiff := AbstractTopTerm.program_iff hZ3 (old 3 w) (old 3 mode) (old 3 z) (old 3 P)
      (old 3 a) (old 3 b) (old 3 A) (old 3 B) (old 3 R) (old 3 S) (slot 3 1) (slot 3 2) hw3 hm3 hd3 hz3 he3 hTyped
    have hRel := ArgumentProgramFieldSyntax.fields_at (old 3 w) (old 3 R) (old 3 S) (old 3 k) (old 3 n) (old 3 q)
      (slot 3 0) (slot 3 1) (slot 3 2) hF (.conjL hC) (.conjL (.conjR hC)) (.conjR (.conjR hC))
    exact .impE (.conjR hiff) hRel

theorem run_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w mode z P a b A B R S n q k : Fin m)
    (hw : Derives Γ (omega w)) (hm : Derives Γ (SyntaxNumeralSyntax.numeral 1 mode))
    (hd : Derives Γ (OriginalTermTraceSyntax.metadata w z P)) (hz : Derives Γ (empty z))
    (he : Derives Γ (SyntaxTopCodedEnvironmentSyntax.abstractCoded w a b A B R S))
    (hL : Derives Γ (SyntaxMixedImageCodeSyntax.termList w k a B n)) :
    Derives Γ ((OriginalTransformRowSyntax.run 2 w mode z P n q).iff (ArgumentProgramFieldSyntax.mapped w R S k A b n q)) := by
  have hp := AbstractTopTermFiber.promise hZ w mode z P a b A B R S hw hm hd hz he
  have hMaps := SyntaxTopCodedEnvironmentTyping.abstract_lists w a b A B R S he
  have hc : Derives Γ (SyntaxTermSyntax.contexts w A b) := .conjL (.conjR (.conjL hMaps))
  have hRaw := SmallModeArgumentFieldCompletion.run_iff hZ 1 (by decide) w mode z P a B A b n k q hw hm (.conjL hd) (.conjR hd) hc hp hL
  have hFields := fields_iff hZ w mode z P a b A B R S n q k hw hm hd hz he hL
  exact SyntaxTypeLocalTransfer.iff_trans hRaw
    (FormulaCodeCongruence.conj_congr (SyntaxTypeLocalTransfer.iff_refl (SyntaxMixedImageCodeSyntax.termList w k A b q)) hFields)

end PPAC.Migration.Internal.AbstractTopArgumentFields
