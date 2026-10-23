import PPAC.Migration.Internal.HornTraceExtension
import PPAC.Migration.Internal.HornLookupPositiveSyntax

/-! 原模式0/3变量规则的实际完整表轨迹引入；自由替换复用已证明的内部查找。 -/
namespace PPAC.Migration.Internal.OriginalScalarPositive
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax HornRuleSyntax
open SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC.Automation.ObjectHorn (Rule)
open YesMetaZFC.Automation.ObjectSyntaxTransform (rules boundIdentity freeWeaken freeReplace)

theorem head_bound {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (rule : Rule)
    (hi : ∀ i : Fin rule.arity, i ∈ rule.head.variables) (w r : Fin m) (env : Fin rule.arity → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat rule.arity w env))
    (hh : Derives Γ (graph rule.head w env r)) : Derives Γ (HornExprBounds.environmentBound rule.arity r env) :=
  HornExprBounds.intro_environmentBound r env (fun i => HornExprBounds.variable_bound hZ _ i (hi i) w r env hw hn hh)

theorem leaf_step {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (rule : Rule)
    (hm : rule ∈ rules) (hg : rule.guards = []) (hp : rule.premises = [])
    (hi : ∀ i : Fin rule.arity, i ∈ rule.head.variables) (w r R : Fin m) (env : Fin rule.arity → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat rule.arity w env))
    (hh : Derives Γ (graph rule.head w env r)) : Derives Γ (HornStepSyntax.originalStep w r R) := by
  have hmatrix : Derives Γ (matrix rule w r R env) := by
    simp only [HornRuleSyntax.matrix, hg, hp, guards, premises]
    exact .conjI hh (.conjI truth_proved truth_proved)
  exact HornStepSyntax.rule_intro rules rule hm w r R (HornApplicationRules.intro_application rule w r R env hn (head_bound hZ rule hi w r env hw hn hh) hmatrix)

theorem from_canonical {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (.mem r w))
    (hc : Derives (Context.add (HornLookupTraceValueSyntax.value w.castSucc (Fin.last m)) (Context.image Formula.raise Γ))
      (HornStepSyntax.originalStep w.castSucc r.castSucc (Fin.last m))) :
    Derives Γ (HornLookupConditionSyntax.condition w r) := by
  let V := HornLookupTraceValueSyntax.value w.castSucc (Fin.last m)
  let Δ := Context.add V (Context.image Formula.raise Γ)
  apply Derives.exE (p := V) (HornLookupTraceValue.exists_value hZ w)
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw V)
  have hn1 : Derives Δ (.mem r.castSucc w.castSucc) := under hn V
  have hv : Derives Δ V := .hyp (Or.inl rfl)
  have ho := HornTraceExtension.condition (ZFContext.under hZ V) w.castSucc (Fin.last m) r.castSucc
    (HornLookupTraceValue.subset _ _ hv) hn1 (HornLookupTraceClosed.closed (ZFContext.under hZ V) _ _ hw1 hv) hc
  exact of_eq (HornLookupConditionSyntax.condition_rename w r Fin.castSucc).symm ho

theorem leaf_condition {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (rule : Rule)
    (hm : rule ∈ rules) (hg : rule.guards = []) (hp : rule.premises = [])
    (hi : ∀ i : Fin rule.arity, i ∈ rule.head.variables) (w r : Fin m) (env : Fin rule.arity → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat rule.arity w env))
    (hh : Derives Γ (graph rule.head w env r)) : Derives Γ (HornLookupConditionSyntax.condition w r) := by
  apply from_canonical hZ w r hw (HornExprRange.range hZ _ w r env hw hn hh)
  let V := HornLookupTraceValueSyntax.value w.castSucc (Fin.last m)
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw V)
  have hn1 := of_eq (environmentNat_rename rule.arity w env Fin.castSucc) (under hn V)
  have hh1 := of_eq (graph_rename rule.head w r env Fin.castSucc) (under hh V)
  exact leaf_step (ZFContext.under hZ V) rule hm hg hp hi _ _ _ _ hw1 hn1 hh1

theorem bound_zero {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r : Fin m) (env : Fin 3 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 3 w env))
    (hh : Derives Γ (graph (boundIdentity 0).head w env r)) : Derives Γ (HornLookupConditionSyntax.condition w r) :=
  leaf_condition hZ (boundIdentity 0) (by simp [rules]) rfl rfl (by decide) w r env hw hn hh

theorem bound_three {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r : Fin m) (env : Fin 3 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 3 w env))
    (hh : Derives Γ (graph (boundIdentity 3).head w env r)) : Derives Γ (HornLookupConditionSyntax.condition w r) :=
  leaf_condition hZ (boundIdentity 3) (by simp [rules]) rfl rfl (by decide) w r env hw hn hh

theorem free_zero {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r : Fin m) (env : Fin 3 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 3 w env))
    (hh : Derives Γ (graph freeWeaken.head w env r)) : Derives Γ (HornLookupConditionSyntax.condition w r) :=
  leaf_condition hZ freeWeaken (by simp [rules]) rfl rfl (by decide) w r env hw hn hh

theorem lookup_premise {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w R : Fin m) (env : Fin 4 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 4 w env))
    (hv : Derives Γ (HornLookupTraceValueSyntax.value w R))
    (he : Derives Γ (LookupTableExecutionSyntax.executed w (env 1) (env 2) (env 3))) :
    Derives Γ (premise OriginalLookupExpr.premiseExpr w R env) := by
  have hex := HornLookupRowSyntax.exists_row hZ w (env 1) (env 2) (env 3) hw
    (environmentNat_at w env hn 1) (environmentNat_at w env hn 2) (environmentNat_at w env hn 3)
  let B := (Formula.mem (Fin.last m) w.castSucc).conj (HornLookupRowSyntax.row w.castSucc (env 1).castSucc (env 2).castSucc (env 3).castSucc (Fin.last m))
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) hex
  have hZ1 := ZFContext.under hZ B
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw B)
  have hn1 : Derives Δ (environmentNat 4 w.castSucc (fun i => (env i).castSucc)) := of_eq (environmentNat_rename 4 w env Fin.castSucc) (under hn B)
  have hv1 : Derives Δ (HornLookupTraceValueSyntax.value w.castSucc R.castSucc) := of_eq (HornLookupTraceValueSyntax.value_rename w R Fin.castSucc) (under hv B)
  have he1 : Derives Δ (LookupTableExecutionSyntax.executed w.castSucc (env 1).castSucc (env 2).castSucc (env 3).castSucc) := of_eq
    (LookupTableExecutionSyntax.executed_rename _ _ _ _ Fin.castSucc) (under he B)
  have hr := Derives.conjR (Derives.hyp (Γ := Δ) (Or.inl rfl))
  have hm := HornLookupTraceValue.successful_member hZ1 _ _ _ _ _ _ hw1 hv1 hr he1
  have hc := HornLookupPositiveSyntax.intro_child_member _ _ _ (fun i => (env i).castSucc) hr hm
  have ho := Derives.impE (.conjR (OriginalLookupRuleMatrix.child_member_iff hZ1 _ _ _ hw1 hn1)) hc
  exact of_eq (premise_rename OriginalLookupExpr.premiseExpr w R env Fin.castSucc).symm ho

theorem free_three {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r : Fin m) (env : Fin 4 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 4 w env))
    (hh : Derives Γ (graph freeReplace.head w env r))
    (he : Derives Γ (LookupTableExecutionSyntax.executed w (env 1) (env 2) (env 3))) :
    Derives Γ (HornLookupConditionSyntax.condition w r) := by
  apply from_canonical hZ w r hw (HornExprRange.range hZ _ w r env hw hn hh)
  let V := HornLookupTraceValueSyntax.value w.castSucc (Fin.last m)
  let Δ := Context.add V (Context.image Formula.raise Γ)
  have hZ1 := ZFContext.under hZ V
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw V)
  have hn1 : Derives Δ (environmentNat 4 w.castSucc (fun i => (env i).castSucc)) := of_eq (environmentNat_rename 4 w env Fin.castSucc) (under hn V)
  have hh1 : Derives Δ (graph freeReplace.head w.castSucc (fun i => (env i).castSucc) r.castSucc) := of_eq (graph_rename freeReplace.head w r env Fin.castSucc) (under hh V)
  have he1 : Derives Δ (LookupTableExecutionSyntax.executed w.castSucc (env 1).castSucc (env 2).castSucc (env 3).castSucc) := of_eq
    (LookupTableExecutionSyntax.executed_rename _ _ _ _ Fin.castSucc) (under he V)
  have hp := lookup_premise hZ1 _ _ _ hw1 hn1 (.hyp (Or.inl rfl)) he1
  have hm : Derives Δ (matrix freeReplace w.castSucc r.castSucc (Fin.last m) (fun i => (env i).castSucc)) :=
    .conjI hh1 (.conjI truth_proved (.conjI hp truth_proved))
  have hi : ∀ i : Fin 4, i ∈ freeReplace.head.variables := by decide
  exact HornStepSyntax.rule_intro rules freeReplace (by simp [rules]) _ _ _
    (HornApplicationRules.intro_application freeReplace _ _ _ _ hn1 (head_bound hZ1 freeReplace hi _ _ _ hw1 hn1 hh1) hm)

end PPAC.Migration.Internal.OriginalScalarPositive
