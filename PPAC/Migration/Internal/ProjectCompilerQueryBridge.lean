import PPAC.Migration.Internal.ProjectCompilerCaseTransport

/-! Guarded reads in an actual parent recursor equal the actual child Compiled relation. -/
namespace PPAC.Migration.Internal.ProjectCompilerQueryBridge
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open ProjectCompilerCaseSyntax (queried)
open ProjectCompilerLocalSyntax (readMatrix one readMatrix_at)
open ProjectCompilerRecursiveSyntax (codeMatrix parameters codeMatrix_at)
open SyntaxRenameQuerySyntax (of_eq)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem at_member {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a c h n x b q : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (.mem n w))
    (hc : Derives Γ (ProjectCompilerCodeSyntax.carrier w a c))
    (hg : Derives Γ (ProjectCompilerRecursionSyntax.graph w c h n)) (hx : Derives Γ (.mem x n)) :
    Derives Γ ((SyntaxContextReadSyntax.read h x b q).iff (ProjectCompilerCodeSyntax.compiled w x b q)) := by
  have ho := NaturalOrderBasic.ordinal hZ w n hw hn
  have hxW := StructuralListTraceOrder.member_member hZ w x n hw hn hx
  have hr := ProjectCompilerJudgment.read_iff hZ w c h n x b q ho hx hxW hg
  have ht := ProjectCompilerCodeCarrier.code_iff_atCarrier hZ w a c x b q hc
  exact ProjectSourceTypeLocalTransfer.iff_trans hr (.conjI (.conjR ht) (.conjL ht))

theorem guarded {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a c h n x b q : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (.mem n w))
    (hc : Derives Γ (ProjectCompilerCodeSyntax.carrier w a c))
    (hg : Derives Γ (ProjectCompilerRecursionSyntax.graph w c h n)) :
    Derives Γ ((queried readMatrix (one h) n x b q).iff (queried codeMatrix (parameters w) n x b q)) := by
  have hi : Derives Γ (((Formula.mem x n).conj (SyntaxContextReadSyntax.read h x b q)).iff
      ((Formula.mem x n).conj (ProjectCompilerCodeSyntax.compiled w x b q))) := by
    apply Derives.conjI
    · apply Derives.impI
      let A := (Formula.mem x n).conj (SyntaxContextReadSyntax.read h x b q)
      let Δ := Context.add A Γ
      have hA : Derives Δ A := .hyp (Or.inl rfl)
      have he := at_member (ZFContext.add hZ A) w a c h n x b q (add hw A) (add hn A) (add hc A) (add hg A) (.conjL hA)
      exact .conjI (.conjL hA) (.impE (.conjL he) (.conjR hA))
    · apply Derives.impI
      let A := (Formula.mem x n).conj (ProjectCompilerCodeSyntax.compiled w x b q)
      let Δ := Context.add A Γ
      have hA : Derives Δ A := .hyp (Or.inl rfl)
      have he := at_member (ZFContext.add hZ A) w a c h n x b q (add hw A) (add hn A) (add hc A) (add hg A) (.conjL hA)
      exact .conjI (.conjL hA) (.impE (.conjR he) (.conjR hA))
  exact of_eq (by simp only [queried, readMatrix_at, codeMatrix_at, one, parameters]) hi

theorem all_queries {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a c h n : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (.mem n w))
    (hc : Derives Γ (ProjectCompilerCodeSyntax.carrier w a c))
    (hg : Derives Γ (ProjectCompilerRecursionSyntax.graph w c h n)) :
    Derives Γ (ProjectCompilerQuerySyntax.equivalent readMatrix (one h) codeMatrix (parameters w) n) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  have hZ3 := HornBinderRules.zf_many 3 hZ
  have hw3 := of_eq (omega_rename w (old 3)) (HornBinderRules.under_many 3 hw)
  have hn3 : Derives (raisedContext 3 Γ) (.mem (old 3 n) (old 3 w)) := HornBinderRules.under_many 3 hn
  have hc3 := of_eq (ProjectCompilerCodeSyntax.carrier_rename w a c (old 3)) (HornBinderRules.under_many 3 hc)
  have hg3 := of_eq (ProjectCompilerRecursionSyntax.graph_rename w c h n (old 3)) (HornBinderRules.under_many 3 hg)
  exact guarded hZ3 (old 3 w) (old 3 a) (old 3 c) (old 3 h) (old 3 n) (slot 3 0) (slot 3 1) (slot 3 2) hw3 hn3 hc3 hg3

end PPAC.Migration.Internal.ProjectCompilerQueryBridge
