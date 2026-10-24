import PPAC.Migration.Internal.InstantiateFrameTermFiber
import PPAC.Migration.Internal.SmallModeArgumentFieldCompletion

/-! 任意内部深度frame下原Run2与真实码表逐字段项程序的全内部对应，列表IH及Promise均已消去。 -/
namespace PPAC.Migration.Internal.InstantiateFrameArguments
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax InstantiateOperationFrameSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem fields_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w mode depth P a b c e R S n q k : Fin m)
    (hw : Derives Γ (omega w)) (hFrame : Derives Γ (frame w mode depth P a b c e R S))
    (hL : Derives Γ (SyntaxMixedImageCodeSyntax.termList w k a b n)) :
    Derives Γ ((OriginalArgumentFieldSyntax.fields w mode depth P k n q).iff (ArgumentProgramFieldSyntax.fields w R S k n q)) := by
  apply Derives.conjI
  · apply Derives.impI
    let E := OriginalArgumentFieldSyntax.fields w mode depth P k n q
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
    have hFrame3 : Derives Δ (frame (old 3 w) (old 3 mode) (old 3 depth) (old 3 P) (old 3 a) (old 3 b) (old 3 c) (old 3 e) (old 3 R) (old 3 S)) := of_eq (frame_rename w mode depth P a b c e R S (old 3)) (HornBinderRules.under_body 3 (add hFrame E) C)
    have hL3 : Derives Δ (SyntaxMixedImageCodeSyntax.termList (old 3 w) (old 3 k) (old 3 a) (old 3 b) (old 3 n)) := of_eq (by simp only [SyntaxMixedImageCodeSyntax.termList_rename]) (HornBinderRules.under_body 3 (add hL E) C)
    have hF : Derives Δ (OriginalArgumentFieldSyntax.fields (old 3 w) (old 3 mode) (old 3 depth) (old 3 P) (old 3 k) (old 3 n) (old 3 q)) := of_eq (OriginalArgumentFieldSyntax.fields_rename w mode depth P k n q (old 3)) (HornBinderRules.under_body 3 hEF C)
    have hC : Derives Δ C := .hyp (Or.inl rfl)
    have hTyped := SyntaxMixedImageCodeFields.field_type (old 3 w) (old 3 k) (old 3 a) (old 3 b) (old 3 n) (slot 3 0) (slot 3 1)
      hL3 (.conjL hC) (.conjL (.conjR hC))
    have hiff := InstantiateFrameTerm.program_iff hZ3 (old 3 w) (old 3 mode) (old 3 depth) (old 3 P) (old 3 a) (old 3 b) (old 3 c) (old 3 e) (old 3 R) (old 3 S) (slot 3 1) (slot 3 2) hw3 hFrame3 hTyped
    have hRel := OriginalArgumentFieldSyntax.fields_at (old 3 w) (old 3 mode) (old 3 depth) (old 3 P) (old 3 k) (old 3 n) (old 3 q)
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
    have hFrame3 : Derives Δ (frame (old 3 w) (old 3 mode) (old 3 depth) (old 3 P) (old 3 a) (old 3 b) (old 3 c) (old 3 e) (old 3 R) (old 3 S)) := of_eq (frame_rename w mode depth P a b c e R S (old 3)) (HornBinderRules.under_body 3 (add hFrame E) C)
    have hL3 : Derives Δ (SyntaxMixedImageCodeSyntax.termList (old 3 w) (old 3 k) (old 3 a) (old 3 b) (old 3 n)) := of_eq (by simp only [SyntaxMixedImageCodeSyntax.termList_rename]) (HornBinderRules.under_body 3 (add hL E) C)
    have hF : Derives Δ (ArgumentProgramFieldSyntax.fields (old 3 w) (old 3 R) (old 3 S) (old 3 k) (old 3 n) (old 3 q)) := of_eq (ArgumentProgramFieldSyntax.fields_rename w R S k n q (old 3)) (HornBinderRules.under_body 3 hEF C)
    have hC : Derives Δ C := .hyp (Or.inl rfl)
    have hTyped := SyntaxMixedImageCodeFields.field_type (old 3 w) (old 3 k) (old 3 a) (old 3 b) (old 3 n) (slot 3 0) (slot 3 1)
      hL3 (.conjL hC) (.conjL (.conjR hC))
    have hiff := InstantiateFrameTerm.program_iff hZ3 (old 3 w) (old 3 mode) (old 3 depth) (old 3 P) (old 3 a) (old 3 b) (old 3 c) (old 3 e) (old 3 R) (old 3 S) (slot 3 1) (slot 3 2) hw3 hFrame3 hTyped
    have hRel := ArgumentProgramFieldSyntax.fields_at (old 3 w) (old 3 R) (old 3 S) (old 3 k) (old 3 n) (old 3 q)
      (slot 3 0) (slot 3 1) (slot 3 2) hF (.conjL hC) (.conjL (.conjR hC)) (.conjR (.conjR hC))
    exact .impE (.conjR hiff) hRel

theorem run_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w mode depth P a b c e R S n q k : Fin m)
    (hw : Derives Γ (omega w)) (hFrame : Derives Γ (frame w mode depth P a b c e R S))
    (hL : Derives Γ (SyntaxMixedImageCodeSyntax.termList w k a b n)) :
    Derives Γ ((OriginalTransformRowSyntax.run 2 w mode depth P n q).iff (ArgumentProgramFieldSyntax.mapped w R S k c e n q)) := by
  have hp := InstantiateFrameTermFiber.promise hZ w mode depth P a b c e R S hw hFrame
  have hMaps := term_lists w mode depth P a b c e R S hFrame
  have hc : Derives Γ (SyntaxTermSyntax.contexts w c e) := .conjL (.conjR (.conjL hMaps))
  have hd := metadata w mode depth P a b c e R S hFrame
  have hm := mode_number w mode depth P a b c e R S hFrame
  have hRaw := SmallModeArgumentFieldCompletion.run_iff hZ 2 (by decide) w mode depth P a b c e n k q hw hm (.conjL hd) (.conjR hd) hc hp hL
  have hFields := fields_iff hZ w mode depth P a b c e R S n q k hw hFrame hL
  exact SyntaxTypeLocalTransfer.iff_trans hRaw
    (FormulaCodeCongruence.conj_congr (SyntaxTypeLocalTransfer.iff_refl (SyntaxMixedImageCodeSyntax.termList w k c e q)) hFields)

theorem guarded_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w mode depth P a b c e R S n q k : Fin m)
    (hw : Derives Γ (omega w)) (hFrame : Derives Γ (frame w mode depth P a b c e R S)) :
    Derives Γ (((SyntaxMixedImageCodeSyntax.termList w k a b n).conj (OriginalTransformRowSyntax.run 2 w mode depth P n q)).iff
      ((SyntaxMixedImageCodeSyntax.termList w k a b n).conj (ArgumentProgramFieldSyntax.mapped w R S k c e n q))) := by
  apply Derives.conjI
  · apply Derives.impI
    let E := (SyntaxMixedImageCodeSyntax.termList w k a b n).conj (OriginalTransformRowSyntax.run 2 w mode depth P n q)
    have hE : Derives (Context.add E Γ) E := .hyp (Or.inl rfl)
    have hh := run_iff (ZFContext.add hZ E) w mode depth P a b c e R S n q k (add hw E) (add hFrame E) (.conjL hE)
    exact .conjI (.conjL hE) (.impE (.conjL hh) (.conjR hE))
  · apply Derives.impI
    let E := (SyntaxMixedImageCodeSyntax.termList w k a b n).conj (ArgumentProgramFieldSyntax.mapped w R S k c e n q)
    have hE : Derives (Context.add E Γ) E := .hyp (Or.inl rfl)
    have hh := run_iff (ZFContext.add hZ E) w mode depth P a b c e R S n q k (add hw E) (add hFrame E) (.conjL hE)
    exact .conjI (.conjL hE) (.impE (.conjR hh) (.conjR hE))

end PPAC.Migration.Internal.InstantiateFrameArguments
