import PPAC.Migration.Internal.HornLookupHeadSound

/-! 原lookupTail真实矩阵取得实际Cons/后继/子行；tail严格界下调用对象归纳假设。 -/
namespace PPAC.Migration.Internal.HornLookupTailSound
open Source SourceAlgebra SourceLogic OmegaSyntax HornLookupRowSyntax HornLookupSoundSyntax
open SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC.Automation.ObjectSyntaxTransform (lookupTail)

theorem matrix_execution {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n i y r R : Fin m) (env : Fin 4 → Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (row w n i y r)) (he : Derives Γ (earlier w R n))
    (hn : Derives Γ (HornExprSyntax.environmentNat 4 w env)) (hm : Derives Γ (HornRuleSyntax.matrix lookupTail w r R env)) :
    Derives Γ (LookupTableExecutionSyntax.executed w n i y) := by
  have hc := StructuralConsCore.exists_cons hZ w (env 0) (env 1) hw
    (HornExprSyntax.environmentNat_at w env hn 0) (HornExprSyntax.environmentNat_at w env hn 1)
  let N := (Formula.mem (Fin.last m) w.castSucc).conj (StructuralListSyntax.consCode w.castSucc (env 0).castSucc (env 1).castSucc (Fin.last m))
  let Δ := Context.add N (Context.image Formula.raise Γ)
  apply Derives.exE (p := N) hc
  have hZ1 := ZFContext.under hZ N
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw N)
  have hx := InsertExistence.exists_insert (env 2).castSucc (env 2).castSucc (ZFContext.arithmetic hZ1).base.pairing (ZFContext.arithmetic hZ1).base.union
  let S := successor (Fin.last (m+1)) (env 2).castSucc.castSucc
  let Ξ := Context.add S (Context.image Formula.raise Δ)
  apply Derives.exE (p := S) hx
  have hZ2 := ZFContext.under hZ1 S
  have hw2 : Derives Ξ (omega w.castSucc.castSucc) := of_eq (omega_rename w.castSucc Fin.castSucc) (under hw1 S)
  have hn2 : Derives Ξ (HornExprSyntax.environmentNat 4 w.castSucc.castSucc (fun j => (env j).castSucc.castSucc)) := of_eq
    (by simp only [Formula.raise, HornExprSyntax.environmentNat_rename]) (under (under hn N) S)
  have hm2 : Derives Ξ (HornRuleSyntax.matrix lookupTail w.castSucc.castSucc r.castSucc.castSucc R.castSucc.castSucc (fun j => (env j).castSucc.castSucc)) := of_eq
    (by simp only [Formula.raise, HornRuleSyntax.matrix_rename]) (under (under hm N) S)
  have hr2 : Derives Ξ (row w.castSucc.castSucc n.castSucc.castSucc i.castSucc.castSucc y.castSucc.castSucc r.castSucc.castSucc) := of_eq
    (by simp only [Formula.raise, row_rename]) (under (under hr N) S)
  have he2 : Derives Ξ (earlier w.castSucc.castSucc R.castSucc.castSucc n.castSucc.castSucc) := of_eq
    (by simp only [Formula.raise, earlier_rename]) (under (under he N) S)
  have hN : Derives Δ N := .hyp (Or.inl rfl)
  have hC : Derives Ξ (StructuralListSyntax.consCode w.castSucc.castSucc (env 0).castSucc.castSucc (env 1).castSucc.castSucc (Fin.last m).castSucc) := of_eq
    (StructuralListSyntax.consCode_rename _ _ _ _ Fin.castSucc) (under (.conjR hN) S)
  have hS : Derives Ξ S := .hyp (Or.inl rfl)
  have hCode := Derives.impE (.conjL (OriginalLookupRuleMatrix.tail_matrix_iff hZ2 w.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) r.castSucc.castSucc R.castSucc.castSucc (fun j => (env j).castSucc.castSucc) hw2 hn2 hC hS)) hm2
  have hf := fields_equal hZ2 _ _ _ _ _ _ _ _ hw2 hr2 (.conjL hCode)
  have hC0 := HornExprStructural.cons_output_subst _ _ _ _ _ (eq_symm (.conjL hf)) hC
  have hs0 := successor_output_subst _ _ _ (.conjL (.conjR hf)) hS
  let K := (row w.castSucc.castSucc.castSucc (env 1).castSucc.castSucc.castSucc (env 2).castSucc.castSucc.castSucc (env 3).castSucc.castSucc.castSucc (Fin.last (m+2))).conj
    (.mem (Fin.last (m+2)) R.castSucc.castSucc.castSucc)
  let Ω := Context.add K (Context.image Formula.raise Ξ)
  apply Derives.exE (p := K) (.conjR hCode)
  have hZ3 := ZFContext.under hZ2 K
  have hw3 : Derives Ω (omega w.castSucc.castSucc.castSucc) := of_eq (omega_rename w.castSucc.castSucc Fin.castSucc) (under hw2 K)
  have hn3 : Derives Ω (HornExprSyntax.environmentNat 4 w.castSucc.castSucc.castSucc (fun j => (env j).castSucc.castSucc.castSucc)) := of_eq
    (HornExprSyntax.environmentNat_rename _ _ _ Fin.castSucc) (under hn2 K)
  have he3 : Derives Ω (earlier w.castSucc.castSucc.castSucc R.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc) := of_eq
    (earlier_rename _ _ _ Fin.castSucc) (under he2 K)
  have hC3 : Derives Ω (StructuralListSyntax.consCode w.castSucc.castSucc.castSucc (env 0).castSucc.castSucc.castSucc (env 1).castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc) := of_eq
    (StructuralListSyntax.consCode_rename _ _ _ _ Fin.castSucc) (under hC0 K)
  have hs3 : Derives Ω (successor i.castSucc.castSucc.castSucc (env 2).castSucc.castSucc.castSucc) := of_eq
    (successor_rename _ _ Fin.castSucc) (under hs0 K)
  have hy3 : Derives Ω (.equal y.castSucc.castSucc.castSucc (env 3).castSucc.castSucc.castSucc) := under (.conjR (.conjR hf)) K
  have hK : Derives Ω K := .hyp (Or.inl rfl)
  have hTail := Derives.conjR (StructuralConsCore.components hZ3 _ _ _ _ hw3
    (HornExprSyntax.environmentNat_at _ _ hn3 0) (HornExprSyntax.environmentNat_at _ _ hn3 1) hC3)
  have hChild := earlier_at _ _ _ _ _ _ _ he3 (HornExprSyntax.environmentNat_at _ _ hn3 1) hTail (.conjL hK) (.conjR hK)
  have hChild1 := execution_value_subst _ _ _ _ _ (eq_symm hy3) hChild
  have hyW := mem_subst (eq_symm hy3) (HornExprSyntax.environmentNat_at _ _ hn3 3)
  have ho := HornLookupExecution.successor hZ3 _ _ _ _ _ _ _ hw3
    (HornExprSyntax.environmentNat_at _ _ hn3 0) (HornExprSyntax.environmentNat_at _ _ hn3 1)
    (HornExprSyntax.environmentNat_at _ _ hn3 2) hyW hC3 hs3 hChild1
  exact of_eq (by simp only [Formula.raise, LookupTableExecutionSyntax.executed_rename]) ho

theorem application_execution {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n i y r R : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (row w n i y r)) (he : Derives Γ (earlier w R n))
    (ha : Derives Γ (HornApplicationSyntax.application lookupTail w r R)) : Derives Γ (LookupTableExecutionSyntax.executed w n i y) := by
  let B := HornApplicationSyntax.body lookupTail w r R
  let Δ := Context.add B (HornBinderSyntax.raisedContext 4 Γ)
  apply HornApplicationRules.eliminate_application lookupTail w r R _ ha
  have hZ4 := HornBinderRules.zf_body 4 hZ B
  have hw4 : Derives Δ (omega (HornBinderSyntax.old 4 w)) := of_eq (omega_rename w (HornBinderSyntax.old 4)) (HornBinderRules.under_body 4 hw B)
  have hr4 : Derives Δ (row (HornBinderSyntax.old 4 w) (HornBinderSyntax.old 4 n) (HornBinderSyntax.old 4 i) (HornBinderSyntax.old 4 y) (HornBinderSyntax.old 4 r)) := of_eq
    (row_rename _ _ _ _ _ (HornBinderSyntax.old 4)) (HornBinderRules.under_body 4 hr B)
  have he4 : Derives Δ (earlier (HornBinderSyntax.old 4 w) (HornBinderSyntax.old 4 R) (HornBinderSyntax.old 4 n)) := of_eq
    (earlier_rename _ _ _ (HornBinderSyntax.old 4)) (HornBinderRules.under_body 4 he B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have ho := matrix_execution hZ4 _ _ _ _ _ _ (HornBinderSyntax.slot 4) hw4 hr4 he4 (.conjL hB) (.conjR (.conjR hB))
  exact of_eq (LookupTableExecutionSyntax.executed_rename w n i y (HornBinderSyntax.old 4)).symm ho

end PPAC.Migration.Internal.HornLookupTailSound
