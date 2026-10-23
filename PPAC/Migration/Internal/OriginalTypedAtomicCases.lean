import PPAC.Migration.Internal.FormulaAtomicProgramSyntax
import PPAC.Migration.Internal.OriginalAtomicExistingAtom

/-! 消去源membership／equality的内部字段见证；实际mode0／3环境中取得整条运行双条件。 -/
namespace PPAC.Migration.Internal.OriginalTypedAtomicCases
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem replace_membership_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w mode depth a b c L I R n q : Fin m)
    (h0 : Derives Γ (omega w))
    (h1 : Derives Γ (SyntaxNumeralSyntax.numeral 3 mode))
    (h2 : Derives Γ (OriginalTermTraceSyntax.metadata w depth L))
    (h3 : Derives Γ (SyntaxIdentityMapSyntax.identityCode w a I))
    (h4 : Derives Γ (IndexTermImageCodeSyntax.converted true w I R a a c))
    (h5 : Derives Γ (SyntaxMixedImageCodeSyntax.termList w b a c L))
    (hS : Derives Γ (SyntaxAtomSyntax.membership w a b n)) :
    Derives Γ ((OriginalTransformRowSyntax.run 3 w mode depth L n q).iff (FormulaTransformAtomSyntax.membership w R L a b a c n q)) := by
  let F :=  SyntaxAtomSyntax.memberBody w a b n
  let Δ := Context.add F (raisedContext 3 Γ)
  apply SyntaxAtomLogic.eliminate_member w a b n _ hS
  have hZ1 : ZFContext.Evidence Δ := HornBinderRules.zf_body 3 hZ F
  have h01 : Derives Δ (omega (old 3 w)) := of_eq (omega_rename w (old 3)) (HornBinderRules.under_body 3 h0 F)
  have h11 : Derives Δ (SyntaxNumeralSyntax.numeral 3 (old 3 mode)) := of_eq (SyntaxNumeralSyntax.numeral_rename 3 mode (old 3)) (HornBinderRules.under_body 3 h1 F)
  have h21 : Derives Δ (OriginalTermTraceSyntax.metadata (old 3 w) (old 3 depth) (old 3 L)) := of_eq (OriginalTermTraceSyntax.metadata_rename w depth L (old 3)) (HornBinderRules.under_body 3 h2 F)
  have h31 : Derives Δ (SyntaxIdentityMapSyntax.identityCode (old 3 w) (old 3 a) (old 3 I)) := of_eq (SyntaxIdentityMapSyntax.identityCode_rename w a I (old 3)) (HornBinderRules.under_body 3 h3 F)
  have h41 : Derives Δ (IndexTermImageCodeSyntax.converted true (old 3 w) (old 3 I) (old 3 R) (old 3 a) (old 3 a) (old 3 c)) := of_eq (IndexTermImageCodeSyntax.converted_rename true w I R a a c (old 3)) (HornBinderRules.under_body 3 h4 F)
  have h51 : Derives Δ (SyntaxMixedImageCodeSyntax.termList (old 3 w) (old 3 b) (old 3 a) (old 3 c) (old 3 L)) := of_eq (SyntaxMixedImageCodeSyntax.termList_rename w b a c L (old 3)) (HornBinderRules.under_body 3 h5 F)
  have hB : Derives Δ F := .hyp (Or.inl rfl)
  have hT : Derives Δ (ArgumentForestProgramSyntax.typedInputs 2 (old 3 w) (old 3 a) (old 3 b) (SyntaxAtomSyntax.two (slot 3 1) (slot 3 2))) :=
    .conjI (.conjL (.conjR (.conjL hB))) (.conjI (.conjR (.conjR (.conjL hB))) (.eqRefl (old 3 w)))
  have hh := OriginalMemberExistingAtom.replace_iff hZ1 (old 3 w) (old 3 mode) (old 3 depth) (old 3 a) (old 3 b) (old 3 c) (old 3 L) (old 3 I) (old 3 R) (old 3 n) (old 3 q) (slot 3 1) (slot 3 2) (slot 3 0) h01 h11 h21 h31 h41 h51 (.conjL (.conjL hB)) (.conjR hB) hT
  exact of_eq (by simp only [old, Formula.raise, Formula.iff, Formula.rename, OriginalTransformRowSyntax.run_rename, FormulaTransformAtomSyntax.membership_rename]) hh

theorem replace_equality_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w mode depth a b c L I R n q : Fin m)
    (h0 : Derives Γ (omega w))
    (h1 : Derives Γ (SyntaxNumeralSyntax.numeral 3 mode))
    (h2 : Derives Γ (OriginalTermTraceSyntax.metadata w depth L))
    (h3 : Derives Γ (SyntaxIdentityMapSyntax.identityCode w a I))
    (h4 : Derives Γ (IndexTermImageCodeSyntax.converted true w I R a a c))
    (h5 : Derives Γ (SyntaxMixedImageCodeSyntax.termList w b a c L))
    (hS : Derives Γ (SyntaxAtomSyntax.equality w a b n)) :
    Derives Γ ((OriginalTransformRowSyntax.run 3 w mode depth L n q).iff (FormulaTransformAtomSyntax.equality w R L a b a c n q)) := by
  let F :=  SyntaxAtomSyntax.equalBody w a b n
  let Δ := Context.add F (raisedContext 2 Γ)
  apply SyntaxAtomLogic.eliminate_equality w a b n _ hS
  have hZ1 : ZFContext.Evidence Δ := HornBinderRules.zf_body 2 hZ F
  have h01 : Derives Δ (omega (old 2 w)) := of_eq (omega_rename w (old 2)) (HornBinderRules.under_body 2 h0 F)
  have h11 : Derives Δ (SyntaxNumeralSyntax.numeral 3 (old 2 mode)) := of_eq (SyntaxNumeralSyntax.numeral_rename 3 mode (old 2)) (HornBinderRules.under_body 2 h1 F)
  have h21 : Derives Δ (OriginalTermTraceSyntax.metadata (old 2 w) (old 2 depth) (old 2 L)) := of_eq (OriginalTermTraceSyntax.metadata_rename w depth L (old 2)) (HornBinderRules.under_body 2 h2 F)
  have h31 : Derives Δ (SyntaxIdentityMapSyntax.identityCode (old 2 w) (old 2 a) (old 2 I)) := of_eq (SyntaxIdentityMapSyntax.identityCode_rename w a I (old 2)) (HornBinderRules.under_body 2 h3 F)
  have h41 : Derives Δ (IndexTermImageCodeSyntax.converted true (old 2 w) (old 2 I) (old 2 R) (old 2 a) (old 2 a) (old 2 c)) := of_eq (IndexTermImageCodeSyntax.converted_rename true w I R a a c (old 2)) (HornBinderRules.under_body 2 h4 F)
  have h51 : Derives Δ (SyntaxMixedImageCodeSyntax.termList (old 2 w) (old 2 b) (old 2 a) (old 2 c) (old 2 L)) := of_eq (SyntaxMixedImageCodeSyntax.termList_rename w b a c L (old 2)) (HornBinderRules.under_body 2 h5 F)
  have hB : Derives Δ F := .hyp (Or.inl rfl)
  have hT : Derives Δ (ArgumentForestProgramSyntax.typedInputs 2 (old 2 w) (old 2 a) (old 2 b) (SyntaxAtomSyntax.two (slot 2 0) (slot 2 1))) :=
    .conjI (.conjL (.conjL hB)) (.conjI (.conjR (.conjL hB)) (.eqRefl (old 2 w)))
  have hh := OriginalAtomicExistingAtom.replace_equality_iff hZ1 (old 2 w) (old 2 mode) (old 2 depth) (old 2 a) (old 2 b) (old 2 c) (old 2 L) (old 2 I) (old 2 R) (old 2 n) (old 2 q) (slot 2 0) (slot 2 1) h01 h11 h21 h31 h41 h51 (.conjR hB) hT
  exact of_eq (by simp only [old, Formula.raise, Formula.iff, Formula.rename, OriginalTransformRowSyntax.run_rename, FormulaTransformAtomSyntax.equality_rename]) hh

theorem weaken_membership_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w mode depth parameter a b B I J R S n q : Fin m)
    (h0 : Derives Γ (omega w))
    (h1 : Derives Γ (SyntaxNumeralSyntax.numeral 0 mode))
    (h2 : Derives Γ (OriginalTermTraceSyntax.metadata w depth parameter))
    (h3 : Derives Γ (SyntaxIdentityMapSyntax.identityCode w a I))
    (h4 : Derives Γ (SyntaxFreeShiftSyntax.shiftCode w b B J))
    (h5 : Derives Γ (IndexTermImageCodeSyntax.converted true w I R a a B))
    (h6 : Derives Γ (IndexTermImageCodeSyntax.converted false w J S b a B))
    (hS : Derives Γ (SyntaxAtomSyntax.membership w a b n)) :
    Derives Γ ((OriginalTransformRowSyntax.run 3 w mode depth parameter n q).iff (FormulaTransformAtomSyntax.membership w R S a b a B n q)) := by
  let F :=  SyntaxAtomSyntax.memberBody w a b n
  let Δ := Context.add F (raisedContext 3 Γ)
  apply SyntaxAtomLogic.eliminate_member w a b n _ hS
  have hZ1 : ZFContext.Evidence Δ := HornBinderRules.zf_body 3 hZ F
  have h01 : Derives Δ (omega (old 3 w)) := of_eq (omega_rename w (old 3)) (HornBinderRules.under_body 3 h0 F)
  have h11 : Derives Δ (SyntaxNumeralSyntax.numeral 0 (old 3 mode)) := of_eq (SyntaxNumeralSyntax.numeral_rename 0 mode (old 3)) (HornBinderRules.under_body 3 h1 F)
  have h21 : Derives Δ (OriginalTermTraceSyntax.metadata (old 3 w) (old 3 depth) (old 3 parameter)) := of_eq (OriginalTermTraceSyntax.metadata_rename w depth parameter (old 3)) (HornBinderRules.under_body 3 h2 F)
  have h31 : Derives Δ (SyntaxIdentityMapSyntax.identityCode (old 3 w) (old 3 a) (old 3 I)) := of_eq (SyntaxIdentityMapSyntax.identityCode_rename w a I (old 3)) (HornBinderRules.under_body 3 h3 F)
  have h41 : Derives Δ (SyntaxFreeShiftSyntax.shiftCode (old 3 w) (old 3 b) (old 3 B) (old 3 J)) := of_eq (SyntaxFreeShiftSyntax.shiftCode_rename w b B J (old 3)) (HornBinderRules.under_body 3 h4 F)
  have h51 : Derives Δ (IndexTermImageCodeSyntax.converted true (old 3 w) (old 3 I) (old 3 R) (old 3 a) (old 3 a) (old 3 B)) := of_eq (IndexTermImageCodeSyntax.converted_rename true w I R a a B (old 3)) (HornBinderRules.under_body 3 h5 F)
  have h61 : Derives Δ (IndexTermImageCodeSyntax.converted false (old 3 w) (old 3 J) (old 3 S) (old 3 b) (old 3 a) (old 3 B)) := of_eq (IndexTermImageCodeSyntax.converted_rename false w J S b a B (old 3)) (HornBinderRules.under_body 3 h6 F)
  have hB : Derives Δ F := .hyp (Or.inl rfl)
  have hT : Derives Δ (ArgumentForestProgramSyntax.typedInputs 2 (old 3 w) (old 3 a) (old 3 b) (SyntaxAtomSyntax.two (slot 3 1) (slot 3 2))) :=
    .conjI (.conjL (.conjR (.conjL hB))) (.conjI (.conjR (.conjR (.conjL hB))) (.eqRefl (old 3 w)))
  have hh := OriginalMemberExistingAtom.weaken_iff hZ1 (old 3 w) (old 3 mode) (old 3 depth) (old 3 parameter) (old 3 a) (old 3 b) (old 3 B) (old 3 I) (old 3 J) (old 3 R) (old 3 S) (old 3 n) (old 3 q) (slot 3 1) (slot 3 2) (slot 3 0) h01 h11 h21 h31 h41 h51 h61 (.conjL (.conjL hB)) (.conjR hB) hT
  exact of_eq (by simp only [old, Formula.raise, Formula.iff, Formula.rename, OriginalTransformRowSyntax.run_rename, FormulaTransformAtomSyntax.membership_rename]) hh

theorem weaken_equality_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w mode depth parameter a b B I J R S n q : Fin m)
    (h0 : Derives Γ (omega w))
    (h1 : Derives Γ (SyntaxNumeralSyntax.numeral 0 mode))
    (h2 : Derives Γ (OriginalTermTraceSyntax.metadata w depth parameter))
    (h3 : Derives Γ (SyntaxIdentityMapSyntax.identityCode w a I))
    (h4 : Derives Γ (SyntaxFreeShiftSyntax.shiftCode w b B J))
    (h5 : Derives Γ (IndexTermImageCodeSyntax.converted true w I R a a B))
    (h6 : Derives Γ (IndexTermImageCodeSyntax.converted false w J S b a B))
    (hS : Derives Γ (SyntaxAtomSyntax.equality w a b n)) :
    Derives Γ ((OriginalTransformRowSyntax.run 3 w mode depth parameter n q).iff (FormulaTransformAtomSyntax.equality w R S a b a B n q)) := by
  let F :=  SyntaxAtomSyntax.equalBody w a b n
  let Δ := Context.add F (raisedContext 2 Γ)
  apply SyntaxAtomLogic.eliminate_equality w a b n _ hS
  have hZ1 : ZFContext.Evidence Δ := HornBinderRules.zf_body 2 hZ F
  have h01 : Derives Δ (omega (old 2 w)) := of_eq (omega_rename w (old 2)) (HornBinderRules.under_body 2 h0 F)
  have h11 : Derives Δ (SyntaxNumeralSyntax.numeral 0 (old 2 mode)) := of_eq (SyntaxNumeralSyntax.numeral_rename 0 mode (old 2)) (HornBinderRules.under_body 2 h1 F)
  have h21 : Derives Δ (OriginalTermTraceSyntax.metadata (old 2 w) (old 2 depth) (old 2 parameter)) := of_eq (OriginalTermTraceSyntax.metadata_rename w depth parameter (old 2)) (HornBinderRules.under_body 2 h2 F)
  have h31 : Derives Δ (SyntaxIdentityMapSyntax.identityCode (old 2 w) (old 2 a) (old 2 I)) := of_eq (SyntaxIdentityMapSyntax.identityCode_rename w a I (old 2)) (HornBinderRules.under_body 2 h3 F)
  have h41 : Derives Δ (SyntaxFreeShiftSyntax.shiftCode (old 2 w) (old 2 b) (old 2 B) (old 2 J)) := of_eq (SyntaxFreeShiftSyntax.shiftCode_rename w b B J (old 2)) (HornBinderRules.under_body 2 h4 F)
  have h51 : Derives Δ (IndexTermImageCodeSyntax.converted true (old 2 w) (old 2 I) (old 2 R) (old 2 a) (old 2 a) (old 2 B)) := of_eq (IndexTermImageCodeSyntax.converted_rename true w I R a a B (old 2)) (HornBinderRules.under_body 2 h5 F)
  have h61 : Derives Δ (IndexTermImageCodeSyntax.converted false (old 2 w) (old 2 J) (old 2 S) (old 2 b) (old 2 a) (old 2 B)) := of_eq (IndexTermImageCodeSyntax.converted_rename false w J S b a B (old 2)) (HornBinderRules.under_body 2 h6 F)
  have hB : Derives Δ F := .hyp (Or.inl rfl)
  have hT : Derives Δ (ArgumentForestProgramSyntax.typedInputs 2 (old 2 w) (old 2 a) (old 2 b) (SyntaxAtomSyntax.two (slot 2 0) (slot 2 1))) :=
    .conjI (.conjL (.conjL hB)) (.conjI (.conjR (.conjL hB)) (.eqRefl (old 2 w)))
  have hh := OriginalAtomicExistingAtom.weaken_equality_iff hZ1 (old 2 w) (old 2 mode) (old 2 depth) (old 2 parameter) (old 2 a) (old 2 b) (old 2 B) (old 2 I) (old 2 J) (old 2 R) (old 2 S) (old 2 n) (old 2 q) (slot 2 0) (slot 2 1) h01 h11 h21 h31 h41 h51 h61 (.conjR hB) hT
  exact of_eq (by simp only [old, Formula.raise, Formula.iff, Formula.rename, OriginalTransformRowSyntax.run_rename, FormulaTransformAtomSyntax.equality_rename]) hh

end PPAC.Migration.Internal.OriginalTypedAtomicCases
