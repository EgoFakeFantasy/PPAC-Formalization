import PPAC.Migration.Internal.ArgumentProgramFieldSyntax

/-! 原mode0／3逐字段关系与独立项程序字段像的全内部双向桥。 -/
namespace PPAC.Migration.Internal.OriginalArgumentProgramFields
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem replace_fields_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w mode depth a b c L I R n q k : Fin m)
    (h0 : Derives Γ (omega w))
    (h1 : Derives Γ (SyntaxNumeralSyntax.numeral 3 mode))
    (h2 : Derives Γ (OriginalTermTraceSyntax.metadata w depth L))
    (h3 : Derives Γ (SyntaxIdentityMapSyntax.identityCode w a I))
    (h4 : Derives Γ (IndexTermImageCodeSyntax.converted true w I R a a c))
    (h5 : Derives Γ (SyntaxMixedImageCodeSyntax.termList w b a c L))
    (hL : Derives Γ (SyntaxMixedImageCodeSyntax.termList w k a b n))
    : Derives Γ ((OriginalArgumentFieldSyntax.fields w mode depth L k n q).iff (ArgumentProgramFieldSyntax.fields w R L k n q)) := by
  apply Derives.conjI
  · apply Derives.impI
    let E := OriginalArgumentFieldSyntax.fields w mode depth L k n q
    apply Derives.allI
    apply Derives.allI
    apply Derives.allI
    apply Derives.impI
    let A := (Formula.mem (slot 3 0) (old 3 k)).conj ((StructuralListFieldSyntax.field (old 3 w) (old 3 n) (slot 3 0) (slot 3 1)).conj (StructuralListFieldSyntax.field (old 3 w) (old 3 q) (slot 3 0) (slot 3 2)))
    let Δ := Context.add A (raisedContext 3 (Context.add E Γ))
    have hZ3 := HornBinderRules.zf_body 3 (ZFContext.add hZ E) A
    have g0 : Derives Δ (omega (old 3 w)) := of_eq (by simp only [omega_rename]) (HornBinderRules.under_body 3 (add h0 E) A)
    have g1 : Derives Δ (SyntaxNumeralSyntax.numeral 3 (old 3 mode)) := of_eq (by simp only [SyntaxNumeralSyntax.numeral_rename]) (HornBinderRules.under_body 3 (add h1 E) A)
    have g2 : Derives Δ (OriginalTermTraceSyntax.metadata (old 3 w) (old 3 depth) (old 3 L)) := of_eq (by simp only [OriginalTermTraceSyntax.metadata_rename]) (HornBinderRules.under_body 3 (add h2 E) A)
    have g3 : Derives Δ (SyntaxIdentityMapSyntax.identityCode (old 3 w) (old 3 a) (old 3 I)) := of_eq (by simp only [SyntaxIdentityMapSyntax.identityCode_rename]) (HornBinderRules.under_body 3 (add h3 E) A)
    have g4 : Derives Δ (IndexTermImageCodeSyntax.converted true (old 3 w) (old 3 I) (old 3 R) (old 3 a) (old 3 a) (old 3 c)) := of_eq (by simp only [IndexTermImageCodeSyntax.converted_rename]) (HornBinderRules.under_body 3 (add h4 E) A)
    have g5 : Derives Δ (SyntaxMixedImageCodeSyntax.termList (old 3 w) (old 3 b) (old 3 a) (old 3 c) (old 3 L)) := of_eq (by simp only [SyntaxMixedImageCodeSyntax.termList_rename]) (HornBinderRules.under_body 3 (add h5 E) A)
    have hL3 : Derives Δ (SyntaxMixedImageCodeSyntax.termList (old 3 w) (old 3 k) (old 3 a) (old 3 b) (old 3 n)) := of_eq (SyntaxMixedImageCodeSyntax.termList_rename w k a b n (old 3)) (HornBinderRules.under_body 3 (add hL E) A)
    have hF : Derives Δ (OriginalArgumentFieldSyntax.fields (old 3 w) (old 3 mode) (old 3 depth) (old 3 L) (old 3 k) (old 3 n) (old 3 q)) := of_eq (by simp only [E, OriginalArgumentFieldSyntax.fields_rename]) (HornBinderRules.under_body 3 (Derives.hyp (Or.inl rfl) : Derives (Context.add E Γ) E) A)
    have hA : Derives Δ A := .hyp (Or.inl rfl)
    have hTyped := SyntaxMixedImageCodeFields.field_type (old 3 w) (old 3 k) (old 3 a) (old 3 b) (old 3 n) (slot 3 0) (slot 3 1) hL3 (.conjL hA) (.conjL (.conjR hA))
    have hif := OriginalNumericTermProgram.replace_on_term hZ3 (old 3 w) (old 3 mode) (old 3 depth) (old 3 a) (old 3 b) (old 3 c) (old 3 L) (old 3 I) (old 3 R) (slot 3 1) (slot 3 2) g0 g1 g2 g3 g4 g5 hTyped
    have hRel := OriginalArgumentFieldSyntax.fields_at (old 3 w) (old 3 mode) (old 3 depth) (old 3 L) (old 3 k) (old 3 n) (old 3 q) (slot 3 0) (slot 3 1) (slot 3 2) hF (.conjL hA) (.conjL (.conjR hA)) (.conjR (.conjR hA))
    exact .impE (.conjL hif) hRel
  · apply Derives.impI
    let E := ArgumentProgramFieldSyntax.fields w R L k n q
    apply Derives.allI
    apply Derives.allI
    apply Derives.allI
    apply Derives.impI
    let A := (Formula.mem (slot 3 0) (old 3 k)).conj ((StructuralListFieldSyntax.field (old 3 w) (old 3 n) (slot 3 0) (slot 3 1)).conj (StructuralListFieldSyntax.field (old 3 w) (old 3 q) (slot 3 0) (slot 3 2)))
    let Δ := Context.add A (raisedContext 3 (Context.add E Γ))
    have hZ3 := HornBinderRules.zf_body 3 (ZFContext.add hZ E) A
    have g0 : Derives Δ (omega (old 3 w)) := of_eq (by simp only [omega_rename]) (HornBinderRules.under_body 3 (add h0 E) A)
    have g1 : Derives Δ (SyntaxNumeralSyntax.numeral 3 (old 3 mode)) := of_eq (by simp only [SyntaxNumeralSyntax.numeral_rename]) (HornBinderRules.under_body 3 (add h1 E) A)
    have g2 : Derives Δ (OriginalTermTraceSyntax.metadata (old 3 w) (old 3 depth) (old 3 L)) := of_eq (by simp only [OriginalTermTraceSyntax.metadata_rename]) (HornBinderRules.under_body 3 (add h2 E) A)
    have g3 : Derives Δ (SyntaxIdentityMapSyntax.identityCode (old 3 w) (old 3 a) (old 3 I)) := of_eq (by simp only [SyntaxIdentityMapSyntax.identityCode_rename]) (HornBinderRules.under_body 3 (add h3 E) A)
    have g4 : Derives Δ (IndexTermImageCodeSyntax.converted true (old 3 w) (old 3 I) (old 3 R) (old 3 a) (old 3 a) (old 3 c)) := of_eq (by simp only [IndexTermImageCodeSyntax.converted_rename]) (HornBinderRules.under_body 3 (add h4 E) A)
    have g5 : Derives Δ (SyntaxMixedImageCodeSyntax.termList (old 3 w) (old 3 b) (old 3 a) (old 3 c) (old 3 L)) := of_eq (by simp only [SyntaxMixedImageCodeSyntax.termList_rename]) (HornBinderRules.under_body 3 (add h5 E) A)
    have hL3 : Derives Δ (SyntaxMixedImageCodeSyntax.termList (old 3 w) (old 3 k) (old 3 a) (old 3 b) (old 3 n)) := of_eq (SyntaxMixedImageCodeSyntax.termList_rename w k a b n (old 3)) (HornBinderRules.under_body 3 (add hL E) A)
    have hF : Derives Δ (ArgumentProgramFieldSyntax.fields (old 3 w) (old 3 R) (old 3 L) (old 3 k) (old 3 n) (old 3 q)) := of_eq (by simp only [E, ArgumentProgramFieldSyntax.fields_rename]) (HornBinderRules.under_body 3 (Derives.hyp (Or.inl rfl) : Derives (Context.add E Γ) E) A)
    have hA : Derives Δ A := .hyp (Or.inl rfl)
    have hTyped := SyntaxMixedImageCodeFields.field_type (old 3 w) (old 3 k) (old 3 a) (old 3 b) (old 3 n) (slot 3 0) (slot 3 1) hL3 (.conjL hA) (.conjL (.conjR hA))
    have hif := OriginalNumericTermProgram.replace_on_term hZ3 (old 3 w) (old 3 mode) (old 3 depth) (old 3 a) (old 3 b) (old 3 c) (old 3 L) (old 3 I) (old 3 R) (slot 3 1) (slot 3 2) g0 g1 g2 g3 g4 g5 hTyped
    have hRel := ArgumentProgramFieldSyntax.fields_at (old 3 w) (old 3 R) (old 3 L) (old 3 k) (old 3 n) (old 3 q) (slot 3 0) (slot 3 1) (slot 3 2) hF (.conjL hA) (.conjL (.conjR hA)) (.conjR (.conjR hA))
    exact .impE (.conjR hif) hRel

theorem weaken_fields_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w mode depth parameter a b B I J R S n q k : Fin m)
    (h0 : Derives Γ (omega w))
    (h1 : Derives Γ (SyntaxNumeralSyntax.numeral 0 mode))
    (h2 : Derives Γ (OriginalTermTraceSyntax.metadata w depth parameter))
    (h3 : Derives Γ (SyntaxIdentityMapSyntax.identityCode w a I))
    (h4 : Derives Γ (SyntaxFreeShiftSyntax.shiftCode w b B J))
    (h5 : Derives Γ (IndexTermImageCodeSyntax.converted true w I R a a B))
    (h6 : Derives Γ (IndexTermImageCodeSyntax.converted false w J S b a B))
    (hL : Derives Γ (SyntaxMixedImageCodeSyntax.termList w k a b n))
    : Derives Γ ((OriginalArgumentFieldSyntax.fields w mode depth parameter k n q).iff (ArgumentProgramFieldSyntax.fields w R S k n q)) := by
  apply Derives.conjI
  · apply Derives.impI
    let E := OriginalArgumentFieldSyntax.fields w mode depth parameter k n q
    apply Derives.allI
    apply Derives.allI
    apply Derives.allI
    apply Derives.impI
    let A := (Formula.mem (slot 3 0) (old 3 k)).conj ((StructuralListFieldSyntax.field (old 3 w) (old 3 n) (slot 3 0) (slot 3 1)).conj (StructuralListFieldSyntax.field (old 3 w) (old 3 q) (slot 3 0) (slot 3 2)))
    let Δ := Context.add A (raisedContext 3 (Context.add E Γ))
    have hZ3 := HornBinderRules.zf_body 3 (ZFContext.add hZ E) A
    have g0 : Derives Δ (omega (old 3 w)) := of_eq (by simp only [omega_rename]) (HornBinderRules.under_body 3 (add h0 E) A)
    have g1 : Derives Δ (SyntaxNumeralSyntax.numeral 0 (old 3 mode)) := of_eq (by simp only [SyntaxNumeralSyntax.numeral_rename]) (HornBinderRules.under_body 3 (add h1 E) A)
    have g2 : Derives Δ (OriginalTermTraceSyntax.metadata (old 3 w) (old 3 depth) (old 3 parameter)) := of_eq (by simp only [OriginalTermTraceSyntax.metadata_rename]) (HornBinderRules.under_body 3 (add h2 E) A)
    have g3 : Derives Δ (SyntaxIdentityMapSyntax.identityCode (old 3 w) (old 3 a) (old 3 I)) := of_eq (by simp only [SyntaxIdentityMapSyntax.identityCode_rename]) (HornBinderRules.under_body 3 (add h3 E) A)
    have g4 : Derives Δ (SyntaxFreeShiftSyntax.shiftCode (old 3 w) (old 3 b) (old 3 B) (old 3 J)) := of_eq (by simp only [SyntaxFreeShiftSyntax.shiftCode_rename]) (HornBinderRules.under_body 3 (add h4 E) A)
    have g5 : Derives Δ (IndexTermImageCodeSyntax.converted true (old 3 w) (old 3 I) (old 3 R) (old 3 a) (old 3 a) (old 3 B)) := of_eq (by simp only [IndexTermImageCodeSyntax.converted_rename]) (HornBinderRules.under_body 3 (add h5 E) A)
    have g6 : Derives Δ (IndexTermImageCodeSyntax.converted false (old 3 w) (old 3 J) (old 3 S) (old 3 b) (old 3 a) (old 3 B)) := of_eq (by simp only [IndexTermImageCodeSyntax.converted_rename]) (HornBinderRules.under_body 3 (add h6 E) A)
    have hL3 : Derives Δ (SyntaxMixedImageCodeSyntax.termList (old 3 w) (old 3 k) (old 3 a) (old 3 b) (old 3 n)) := of_eq (SyntaxMixedImageCodeSyntax.termList_rename w k a b n (old 3)) (HornBinderRules.under_body 3 (add hL E) A)
    have hF : Derives Δ (OriginalArgumentFieldSyntax.fields (old 3 w) (old 3 mode) (old 3 depth) (old 3 parameter) (old 3 k) (old 3 n) (old 3 q)) := of_eq (by simp only [E, OriginalArgumentFieldSyntax.fields_rename]) (HornBinderRules.under_body 3 (Derives.hyp (Or.inl rfl) : Derives (Context.add E Γ) E) A)
    have hA : Derives Δ A := .hyp (Or.inl rfl)
    have hTyped := SyntaxMixedImageCodeFields.field_type (old 3 w) (old 3 k) (old 3 a) (old 3 b) (old 3 n) (slot 3 0) (slot 3 1) hL3 (.conjL hA) (.conjL (.conjR hA))
    have hif := OriginalNumericTermProgram.weaken_on_term hZ3 (old 3 w) (old 3 mode) (old 3 depth) (old 3 parameter) (old 3 a) (old 3 b) (old 3 B) (old 3 I) (old 3 J) (old 3 R) (old 3 S) (slot 3 1) (slot 3 2) g0 g1 g2 g3 g4 g5 g6 hTyped
    have hRel := OriginalArgumentFieldSyntax.fields_at (old 3 w) (old 3 mode) (old 3 depth) (old 3 parameter) (old 3 k) (old 3 n) (old 3 q) (slot 3 0) (slot 3 1) (slot 3 2) hF (.conjL hA) (.conjL (.conjR hA)) (.conjR (.conjR hA))
    exact .impE (.conjL hif) hRel
  · apply Derives.impI
    let E := ArgumentProgramFieldSyntax.fields w R S k n q
    apply Derives.allI
    apply Derives.allI
    apply Derives.allI
    apply Derives.impI
    let A := (Formula.mem (slot 3 0) (old 3 k)).conj ((StructuralListFieldSyntax.field (old 3 w) (old 3 n) (slot 3 0) (slot 3 1)).conj (StructuralListFieldSyntax.field (old 3 w) (old 3 q) (slot 3 0) (slot 3 2)))
    let Δ := Context.add A (raisedContext 3 (Context.add E Γ))
    have hZ3 := HornBinderRules.zf_body 3 (ZFContext.add hZ E) A
    have g0 : Derives Δ (omega (old 3 w)) := of_eq (by simp only [omega_rename]) (HornBinderRules.under_body 3 (add h0 E) A)
    have g1 : Derives Δ (SyntaxNumeralSyntax.numeral 0 (old 3 mode)) := of_eq (by simp only [SyntaxNumeralSyntax.numeral_rename]) (HornBinderRules.under_body 3 (add h1 E) A)
    have g2 : Derives Δ (OriginalTermTraceSyntax.metadata (old 3 w) (old 3 depth) (old 3 parameter)) := of_eq (by simp only [OriginalTermTraceSyntax.metadata_rename]) (HornBinderRules.under_body 3 (add h2 E) A)
    have g3 : Derives Δ (SyntaxIdentityMapSyntax.identityCode (old 3 w) (old 3 a) (old 3 I)) := of_eq (by simp only [SyntaxIdentityMapSyntax.identityCode_rename]) (HornBinderRules.under_body 3 (add h3 E) A)
    have g4 : Derives Δ (SyntaxFreeShiftSyntax.shiftCode (old 3 w) (old 3 b) (old 3 B) (old 3 J)) := of_eq (by simp only [SyntaxFreeShiftSyntax.shiftCode_rename]) (HornBinderRules.under_body 3 (add h4 E) A)
    have g5 : Derives Δ (IndexTermImageCodeSyntax.converted true (old 3 w) (old 3 I) (old 3 R) (old 3 a) (old 3 a) (old 3 B)) := of_eq (by simp only [IndexTermImageCodeSyntax.converted_rename]) (HornBinderRules.under_body 3 (add h5 E) A)
    have g6 : Derives Δ (IndexTermImageCodeSyntax.converted false (old 3 w) (old 3 J) (old 3 S) (old 3 b) (old 3 a) (old 3 B)) := of_eq (by simp only [IndexTermImageCodeSyntax.converted_rename]) (HornBinderRules.under_body 3 (add h6 E) A)
    have hL3 : Derives Δ (SyntaxMixedImageCodeSyntax.termList (old 3 w) (old 3 k) (old 3 a) (old 3 b) (old 3 n)) := of_eq (SyntaxMixedImageCodeSyntax.termList_rename w k a b n (old 3)) (HornBinderRules.under_body 3 (add hL E) A)
    have hF : Derives Δ (ArgumentProgramFieldSyntax.fields (old 3 w) (old 3 R) (old 3 S) (old 3 k) (old 3 n) (old 3 q)) := of_eq (by simp only [E, ArgumentProgramFieldSyntax.fields_rename]) (HornBinderRules.under_body 3 (Derives.hyp (Or.inl rfl) : Derives (Context.add E Γ) E) A)
    have hA : Derives Δ A := .hyp (Or.inl rfl)
    have hTyped := SyntaxMixedImageCodeFields.field_type (old 3 w) (old 3 k) (old 3 a) (old 3 b) (old 3 n) (slot 3 0) (slot 3 1) hL3 (.conjL hA) (.conjL (.conjR hA))
    have hif := OriginalNumericTermProgram.weaken_on_term hZ3 (old 3 w) (old 3 mode) (old 3 depth) (old 3 parameter) (old 3 a) (old 3 b) (old 3 B) (old 3 I) (old 3 J) (old 3 R) (old 3 S) (slot 3 1) (slot 3 2) g0 g1 g2 g3 g4 g5 g6 hTyped
    have hRel := ArgumentProgramFieldSyntax.fields_at (old 3 w) (old 3 R) (old 3 S) (old 3 k) (old 3 n) (old 3 q) (slot 3 0) (slot 3 1) (slot 3 2) hF (.conjL hA) (.conjL (.conjR hA)) (.conjR (.conjR hA))
    exact .impE (.conjR hif) hRel

end PPAC.Migration.Internal.OriginalArgumentProgramFields
