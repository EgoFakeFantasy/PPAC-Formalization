import PPAC.Migration.Internal.HornLookupHeadPositive

/-! 规范轨迹中的实际子行把后继执行送入真实lookupTail应用与完整原表。 -/
namespace PPAC.Migration.Internal.HornLookupTailPositive
open Source SourceAlgebra SourceLogic OmegaSyntax HornLookupRowSyntax HornLookupPositiveSyntax
open HornLookupTraceValueSyntax (value value_rename)
open SyntaxRenameQuerySyntax (of_eq)

theorem step {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w R n i y r : Fin m)
    (hw : Derives Γ (omega w)) (hv : Derives Γ (value w R)) (hr : Derives Γ (row w n i y r))
    (hc : Derives Γ (LookupTableRecursiveSyntax.successorCase w n i y)) : Derives Γ (HornStepSyntax.originalStep w r R) := by
  let A := LookupTableRecursiveSyntax.successorBody w n i y
  let Δ := Context.add A (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply SyntaxRenameBinders.eliminate_2 A _ hc
  have hZ2 := SyntaxRenameBinders.zf_under_2 hZ A
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxRenameBinders.under_2 hw A)
  have hv2 : Derives Δ (value w.castSucc.castSucc R.castSucc.castSucc) := of_eq (by simp only [Formula.raise, value_rename]) (SyntaxRenameBinders.under_2 hv A)
  have hr2 : Derives Δ (row w.castSucc.castSucc n.castSucc.castSucc i.castSucc.castSucc y.castSucc.castSucc r.castSucc.castSucc) := of_eq (by simp only [Formula.raise, row_rename]) (SyntaxRenameBinders.under_2 hr A)
  have hA : Derives Δ A := .hyp (Or.inl rfl)
  let H := StructuralListProjectionSyntax.body false w.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc (Fin.last (m+2))
  let Ξ := Context.add H (Context.image Formula.raise Δ)
  apply Derives.exE (p := H) (.conjL hA)
  have hZ3 := ZFContext.under hZ2 H
  have hw3 : Derives Ξ (omega w.castSucc.castSucc.castSucc) := of_eq (omega_rename _ Fin.castSucc) (under hw2 H)
  have hv3 : Derives Ξ (value w.castSucc.castSucc.castSucc R.castSucc.castSucc.castSucc) := of_eq (value_rename _ _ Fin.castSucc) (under hv2 H)
  have hr3 : Derives Ξ (row w.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc i.castSucc.castSucc.castSucc y.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc) := of_eq (row_rename _ _ _ _ _ Fin.castSucc) (under hr2 H)
  have hj3 : Derives Ξ (.mem (Fin.last (m+1)).castSucc w.castSucc.castSucc.castSucc) := under (.conjL (.conjL (.conjR hA))) H
  have hs3 : Derives Ξ (successor i.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc) := of_eq (successor_rename _ _ Fin.castSucc) (under (.conjR (.conjL (.conjR hA))) H)
  have he3 : Derives Ξ (LookupTableExecutionSyntax.executed w.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc y.castSucc.castSucc.castSucc) := of_eq (LookupTableExecutionSyntax.executed_rename _ _ _ _ Fin.castSucc) (under (.conjR (.conjR hA)) H)
  have hH : Derives Ξ H := .hyp (Or.inl rfl)
  have hy3 := Derives.conjR (.conjR (naturals hZ3 _ _ _ _ _ hw3 hr3))
  have hex := exists_row hZ3 w.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc y.castSucc.castSucc.castSucc hw3 (.conjL (.conjL hH)) hj3 hy3
  let F := (Formula.mem (Fin.last (m+3)) w.castSucc.castSucc.castSucc.castSucc).conj
    (row w.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc y.castSucc.castSucc.castSucc.castSucc (Fin.last (m+3)))
  let Ω := Context.add F (Context.image Formula.raise Ξ)
  apply Derives.exE (p := F) hex
  have hZ4 := ZFContext.under hZ3 F
  have hw4 : Derives Ω (omega w.castSucc.castSucc.castSucc.castSucc) := of_eq (omega_rename _ Fin.castSucc) (under hw3 F)
  have hv4 : Derives Ω (value w.castSucc.castSucc.castSucc.castSucc R.castSucc.castSucc.castSucc.castSucc) := of_eq (value_rename _ _ Fin.castSucc) (under hv3 F)
  have hr4 : Derives Ω (row w.castSucc.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc.castSucc i.castSucc.castSucc.castSucc.castSucc y.castSucc.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc.castSucc) := of_eq (row_rename _ _ _ _ _ Fin.castSucc) (under hr3 F)
  have hh4 : Derives Ω (.mem (Fin.last (m+2)).castSucc w.castSucc.castSucc.castSucc.castSucc) := under (.conjR (.conjL hH)) F
  have ht4 : Derives Ω (.mem (Fin.last m).castSucc.castSucc.castSucc w.castSucc.castSucc.castSucc.castSucc) := under (.conjL (.conjL hH)) F
  have hj4 : Derives Ω (.mem (Fin.last (m+1)).castSucc.castSucc w.castSucc.castSucc.castSucc.castSucc) := under hj3 F
  have hy4 : Derives Ω (.mem y.castSucc.castSucc.castSucc.castSucc w.castSucc.castSucc.castSucc.castSucc) := under hy3 F
  have hs4 : Derives Ω (successor i.castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc) := of_eq (successor_rename _ _ Fin.castSucc) (under hs3 F)
  have he4 : Derives Ω (LookupTableExecutionSyntax.executed w.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc y.castSucc.castSucc.castSucc.castSucc) := of_eq (LookupTableExecutionSyntax.executed_rename _ _ _ _ Fin.castSucc) (under he3 F)
  have hC4 : Derives Ω (StructuralListSyntax.consCode w.castSucc.castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc (Fin.last m).castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc.castSucc) := of_eq (StructuralListSyntax.consCode_rename _ _ _ _ Fin.castSucc) (under (.conjR hH) F)
  have hF : Derives Ω F := .hyp (Or.inl rfl)
  have hm := HornLookupTraceValue.successful_member hZ4 _ _ _ _ _ _ hw4 hv4 (.conjR hF) he4
  have hNat := env4_natural _ _ _ _ _ hh4 ht4 hj4 hy4
  have hChild := intro_child_member _ _ _ (env4 (Fin.last (m+2)).castSucc (Fin.last m).castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc y.castSucc.castSucc.castSucc.castSucc) (.conjR hF) hm
  have hM := Derives.impE (.conjR (OriginalLookupRuleMatrix.tail_matrix_iff hZ4 _ _ _ _ _ _ hw4 hNat hC4 hs4)) (.conjI hr4 hChild)
  have ha := HornApplicationRules.lookup_tail_intro hZ4 _ _ _ _ hw4 hNat hM
  have ho := OriginalLookupDispatch.lookup_intro _ _ _ (.disjR ha)
  exact of_eq (by simp only [Formula.raise, HornStepSyntax.originalStep_rename]) ho

end PPAC.Migration.Internal.HornLookupTailPositive
