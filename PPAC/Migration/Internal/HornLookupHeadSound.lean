import PPAC.Migration.Internal.HornLookupSoundSyntax

/-! 从原lookupHead真实矩阵取得实际Cons及零索引，逐字段对齐后返回原查找执行。 -/
namespace PPAC.Migration.Internal.HornLookupHeadSound
open Source SourceAlgebra SourceLogic OmegaSyntax HornLookupRowSyntax
open SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC.Automation.ObjectSyntaxTransform (lookupHead)

theorem matrix_execution {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n i y r R : Fin m) (env : Fin 2 → Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (row w n i y r))
    (hn : Derives Γ (HornExprSyntax.environmentNat 2 w env)) (hm : Derives Γ (HornRuleSyntax.matrix lookupHead w r R env)) :
    Derives Γ (LookupTableExecutionSyntax.executed w n i y) := by
  have he := StructuralConsCore.exists_cons hZ w (env 0) (env 1) hw
    (HornExprSyntax.environmentNat_at w env hn 0) (HornExprSyntax.environmentNat_at w env hn 1)
  let N := (Formula.mem (Fin.last m) w.castSucc).conj (StructuralListSyntax.consCode w.castSucc (env 0).castSucc (env 1).castSucc (Fin.last m))
  let Δ := Context.add N (Context.image Formula.raise Γ)
  apply Derives.exE (p := N) he
  have hZ1 := ZFContext.under hZ N
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw N)
  let Z := (Formula.mem (Fin.last (m+1)) w.castSucc.castSucc).conj (empty (Fin.last (m+1)))
  let Ξ := Context.add Z (Context.image Formula.raise Δ)
  have hz : Derives Δ (.ex Z) := .conjL (.conjL hw1)
  apply Derives.exE (p := Z) hz
  have hZ2 := ZFContext.under hZ1 Z
  have hw2 : Derives Ξ (omega w.castSucc.castSucc) := of_eq (omega_rename w.castSucc Fin.castSucc) (under hw1 Z)
  have hn2 : Derives Ξ (HornExprSyntax.environmentNat 2 w.castSucc.castSucc (fun j => (env j).castSucc.castSucc)) := of_eq
    (by simp only [Formula.raise, HornExprSyntax.environmentNat_rename]) (under (under hn N) Z)
  have hm2 : Derives Ξ (HornRuleSyntax.matrix lookupHead w.castSucc.castSucc r.castSucc.castSucc R.castSucc.castSucc (fun j => (env j).castSucc.castSucc)) := of_eq
    (by simp only [Formula.raise, HornRuleSyntax.matrix_rename]) (under (under hm N) Z)
  have hr2 : Derives Ξ (row w.castSucc.castSucc n.castSucc.castSucc i.castSucc.castSucc y.castSucc.castSucc r.castSucc.castSucc) := of_eq
    (by simp only [Formula.raise, row_rename]) (under (under hr N) Z)
  have hN : Derives Δ N := .hyp (Or.inl rfl)
  have hC : Derives Ξ (StructuralListSyntax.consCode w.castSucc.castSucc (env 0).castSucc.castSucc (env 1).castSucc.castSucc (Fin.last m).castSucc) := of_eq
    (StructuralListSyntax.consCode_rename _ _ _ _ Fin.castSucc) (under (.conjR hN) Z)
  have hZ : Derives Ξ Z := .hyp (Or.inl rfl)
  have hCode := Derives.impE (.conjL (OriginalLookupRuleMatrix.head_matrix_iff hZ2 w.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) r.castSucc.castSucc R.castSucc.castSucc (fun j => (env j).castSucc.castSucc) hw2 hn2 hC (.conjR hZ))) hm2
  have hf := fields_equal hZ2 _ _ _ _ _ _ _ _ hw2 hr2 hCode
  have hC0 := HornExprStructural.cons_output_subst _ _ _ _ _ (eq_symm (.conjL hf)) hC
  have hC1 := StructuralListCodeFields.head_subst _ _ _ _ _ (eq_symm (.conjR (.conjR hf))) hC0
  have hi := SyntaxNumeralSyntax.output_subst 0 _ _ (eq_symm (.conjL (.conjR hf))) (.conjR hZ)
  have hy := mem_subst (eq_symm (.conjR (.conjR hf))) (HornExprSyntax.environmentNat_at _ _ hn2 0)
  have ho := HornLookupExecution.zero hZ2 _ _ _ _ _ hw2 hy (HornExprSyntax.environmentNat_at _ _ hn2 1) hC1 hi
  exact of_eq (by simp only [Formula.raise, LookupTableExecutionSyntax.executed_rename]) ho

theorem application_execution {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n i y r R : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (row w n i y r))
    (ha : Derives Γ (HornApplicationSyntax.application lookupHead w r R)) : Derives Γ (LookupTableExecutionSyntax.executed w n i y) := by
  let B := HornApplicationSyntax.body lookupHead w r R
  let Δ := Context.add B (HornBinderSyntax.raisedContext 2 Γ)
  apply HornApplicationRules.eliminate_application lookupHead w r R _ ha
  have hZ2 := HornBinderRules.zf_body 2 hZ B
  have hw2 : Derives Δ (omega (HornBinderSyntax.old 2 w)) := of_eq (omega_rename w (HornBinderSyntax.old 2)) (HornBinderRules.under_body 2 hw B)
  have hr2 : Derives Δ (row (HornBinderSyntax.old 2 w) (HornBinderSyntax.old 2 n) (HornBinderSyntax.old 2 i) (HornBinderSyntax.old 2 y) (HornBinderSyntax.old 2 r)) := of_eq
    (row_rename _ _ _ _ _ (HornBinderSyntax.old 2)) (HornBinderRules.under_body 2 hr B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have ho := matrix_execution hZ2 _ _ _ _ _ _ (HornBinderSyntax.slot 2) hw2 hr2 (.conjL hB) (.conjR (.conjR hB))
  exact of_eq (LookupTableExecutionSyntax.executed_rename w n i y (HornBinderSyntax.old 2)).symm ho

end PPAC.Migration.Internal.HornLookupHeadSound
