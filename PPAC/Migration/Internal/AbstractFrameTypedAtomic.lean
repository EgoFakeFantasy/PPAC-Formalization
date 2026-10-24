import PPAC.Migration.Internal.AbstractFrameAtomicExisting
import PPAC.Migration.Internal.FormulaAtomicProgramSyntax

/-! mode1成员／等词原子输入字段全部由对象EX消去，不留下预给标量或两项见证。 -/
namespace PPAC.Migration.Internal.AbstractFrameTypedAtomic
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax AbstractOperationFrameSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem membership_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w mode depth P a b c e R S n q : Fin m)
    (hw : Derives Γ (omega w)) (hF : Derives Γ (frame w mode depth P a b c e R S))
    (hS : Derives Γ (SyntaxAtomSyntax.membership w a b n)) :
    Derives Γ ((OriginalTransformRowSyntax.run 3 w mode depth P n q).iff (FormulaTransformAtomSyntax.membership w R S a b c e n q)) := by
  let F := SyntaxAtomSyntax.memberBody w a b n
  let Δ := Context.add F (raisedContext 3 Γ)
  apply SyntaxAtomLogic.eliminate_member w a b n _ hS
  have hZ3 := HornBinderRules.zf_body 3 hZ F
  have hw3 : Derives Δ (omega (old 3 w)) := of_eq (omega_rename w (old 3)) (HornBinderRules.under_body 3 hw F)
  have hf3 : Derives Δ (frame (old 3 w) (old 3 mode) (old 3 depth) (old 3 P) (old 3 a) (old 3 b) (old 3 c) (old 3 e) (old 3 R) (old 3 S)) := of_eq (frame_rename w mode depth P a b c e R S (old 3)) (HornBinderRules.under_body 3 hF F)
  have hB : Derives Δ F := .hyp (Or.inl rfl)
  have hT : Derives Δ (ArgumentForestProgramSyntax.typedInputs 2 (old 3 w) (old 3 a) (old 3 b) (SyntaxAtomSyntax.two (slot 3 1) (slot 3 2))) :=
    .conjI (.conjL (.conjR (.conjL hB))) (.conjI (.conjR (.conjR (.conjL hB))) (.eqRefl (old 3 w)))
  have hh := AbstractFrameAtomicExisting.membership_at hZ3 (old 3 w) (old 3 mode) (old 3 depth) (old 3 P) (old 3 a) (old 3 b) (old 3 c) (old 3 e) (old 3 R) (old 3 S) (old 3 n) (old 3 q) (slot 3 1) (slot 3 2) (slot 3 0) hw3 hf3 (.conjL (.conjL hB)) (.conjR hB) hT
  exact of_eq (by simp only [old, Formula.raise, Formula.iff, Formula.rename, OriginalTransformRowSyntax.run_rename, FormulaTransformAtomSyntax.membership_rename]) hh

theorem equality_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w mode depth P a b c e R S n q : Fin m)
    (hw : Derives Γ (omega w)) (hF : Derives Γ (frame w mode depth P a b c e R S))
    (hS : Derives Γ (SyntaxAtomSyntax.equality w a b n)) :
    Derives Γ ((OriginalTransformRowSyntax.run 3 w mode depth P n q).iff (FormulaTransformAtomSyntax.equality w R S a b c e n q)) := by
  let F := SyntaxAtomSyntax.equalBody w a b n
  let Δ := Context.add F (raisedContext 2 Γ)
  apply SyntaxAtomLogic.eliminate_equality w a b n _ hS
  have hZ2 := HornBinderRules.zf_body 2 hZ F
  have hw2 : Derives Δ (omega (old 2 w)) := of_eq (omega_rename w (old 2)) (HornBinderRules.under_body 2 hw F)
  have hf2 : Derives Δ (frame (old 2 w) (old 2 mode) (old 2 depth) (old 2 P) (old 2 a) (old 2 b) (old 2 c) (old 2 e) (old 2 R) (old 2 S)) := of_eq (frame_rename w mode depth P a b c e R S (old 2)) (HornBinderRules.under_body 2 hF F)
  have hB : Derives Δ F := .hyp (Or.inl rfl)
  have hT : Derives Δ (ArgumentForestProgramSyntax.typedInputs 2 (old 2 w) (old 2 a) (old 2 b) (SyntaxAtomSyntax.two (slot 2 0) (slot 2 1))) :=
    .conjI (.conjL (.conjL hB)) (.conjI (.conjR (.conjL hB)) (.eqRefl (old 2 w)))
  have hh := AbstractFrameAtomicExisting.equality_at hZ2 (old 2 w) (old 2 mode) (old 2 depth) (old 2 P) (old 2 a) (old 2 b) (old 2 c) (old 2 e) (old 2 R) (old 2 S) (old 2 n) (old 2 q) (slot 2 0) (slot 2 1) hw2 hf2 (.conjR hB) hT
  exact of_eq (by simp only [old, Formula.raise, Formula.iff, Formula.rename, OriginalTransformRowSyntax.run_rename, FormulaTransformAtomSyntax.equality_rename]) hh

end PPAC.Migration.Internal.AbstractFrameTypedAtomic
