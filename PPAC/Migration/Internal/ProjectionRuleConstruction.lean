import PPAC.Migration.Internal.ProjectionExprQuery
import PPAC.Migration.Internal.ProjectionTraceExtension

/-! 七条原投影规则从真实内部头图和子查询构造闭轨迹，搜索界由实际头图推出。 -/
namespace PPAC.Migration.Internal.ProjectionRuleConstruction
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax
open SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC.Automation.ObjectHorn (Expr Rule)

theorem no_guards (rule : Rule) (hr : rule ∈ YesMetaZFC.Automation.ObjectProjection.rules) : rule.guards = [] := by
  simp only [YesMetaZFC.Automation.ObjectProjection.rules, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals rfl

theorem premises_shape (rule : Rule) (hr : rule ∈ YesMetaZFC.Automation.ObjectProjection.rules) :
    rule.premises = [] ∨ ∃ e, rule.premises = [e] := by
  simp only [YesMetaZFC.Automation.ObjectProjection.rules, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact Or.inl rfl | exact Or.inr ⟨_, rfl⟩

theorem head_bound {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (rule : Rule)
    (hr : rule ∈ YesMetaZFC.Automation.ObjectProjection.rules) (w r : Fin m) (env : Fin rule.arity → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat rule.arity w env))
    (hh : Derives Γ (graph rule.head w env r)) : Derives Γ (HornExprBounds.environmentBound rule.arity r env) :=
  HornExprBounds.intro_environmentBound r env (fun i => HornExprBounds.variable_bound hZ rule.head i
    (YesMetaZFC.Automation.ObjectProjection.head_variables rule hr i) w r env hw hn hh)

theorem application {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (rule : Rule)
    (hr : rule ∈ YesMetaZFC.Automation.ObjectProjection.rules) (w r R : Fin m) (env : Fin rule.arity → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat rule.arity w env))
    (hh : Derives Γ (graph rule.head w env r)) (hp : Derives Γ (HornRuleSyntax.premises rule.premises w R env)) :
    Derives Γ (HornApplicationSyntax.application rule w r R) := by
  have hg : Derives Γ (HornRuleSyntax.guards rule.guards w env) := by
    rw [no_guards rule hr]
    exact HornRuleSyntax.truth_proved
  exact HornApplicationRules.intro_application rule w r R env hn (head_bound hZ rule hr w r env hw hn hh)
    (.conjI hh (.conjI hg hp))

theorem leaf {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (rule : Rule)
    (hr : rule ∈ YesMetaZFC.Automation.ObjectProjection.rules) (he : rule.premises = [])
    (w r : Fin m) (env : Fin rule.arity → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat rule.arity w env))
    (hh : Derives Γ (graph rule.head w env r)) : Derives Γ (ProjectionTraceSyntax.condition w r) := by
  have hp : Derives Γ (HornRuleSyntax.premises rule.premises w w env) := by
    rw [he]
    exact HornRuleSyntax.truth_proved
  exact ProjectionTraceRules.premise_free_condition hZ rule hr he w r
    (HornExprRange.range hZ rule.head w r env hw hn hh) (application hZ rule hr w r w env hw hn hh hp)

theorem unary {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (rule : Rule)
    (hr : rule ∈ YesMetaZFC.Automation.ObjectProjection.rules) (e : Expr rule.arity) (he : rule.premises = [e])
    (w r : Fin m) (env : Fin rule.arity → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat rule.arity w env))
    (hh : Derives Γ (graph rule.head w env r)) (hq : Derives Γ (ProjectionExprQuery.query e w env)) :
    Derives Γ (ProjectionTraceSyntax.condition w r) := by
  let B := (graph e w.castSucc (fun i => (env i).castSucc) (Fin.last m)).conj
    (ProjectionTraceSyntax.condition w.castSucc (Fin.last m))
  let Ξ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) hq
  have hB : Derives Ξ B := .hyp (Or.inl rfl)
  let T := ProjectionTraceSyntax.witness w.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
  let Δ := Context.add T (Context.image Formula.raise Ξ)
  apply Derives.exE (p := T) (.conjR hB)
  have lift {P : Formula m} (h : Derives Γ P) : Derives Δ P.raise.raise := under (under h B) T
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (lift hw)
  have hn2 : Derives Δ (environmentNat rule.arity w.castSucc.castSucc (fun i => (env i).castSucc.castSucc)) :=
    of_eq (by simp only [Formula.raise, environmentNat_rename]) (lift hn)
  have hh2 : Derives Δ (graph rule.head w.castSucc.castSucc (fun i => (env i).castSucc.castSucc) r.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise, graph_rename]) (lift hh)
  have hg2 : Derives Δ (graph e w.castSucc.castSucc (fun i => (env i).castSucc.castSucc) (Fin.last m).castSucc) :=
    of_eq (graph_rename e _ _ _ Fin.castSucc) (under (.conjL hB) T)
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  have hp : Derives Δ (HornRuleSyntax.premise e w.castSucc.castSucc (Fin.last (m+1)) (fun i => (env i).castSucc.castSucc)) := by
    apply Derives.exI (Fin.last m).castSucc
    exact of_eq (by simp only [Formula.instantiate, Formula.rename, graph_rename,
      Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI hg2 (.conjL (.conjR hT)))
  have hps : Derives Δ (HornRuleSyntax.premises rule.premises w.castSucc.castSucc (Fin.last (m+1)) (fun i => (env i).castSucc.castSucc)) := by
    rw [he]
    exact .conjI hp HornRuleSyntax.truth_proved
  have hZ2 := ZFContext.under (ZFContext.under hZ B) T
  have ha := application hZ2 rule hr _ _ _ _ hw2 hn2 hh2 hps
  have hs := HornStepSyntax.rule_intro YesMetaZFC.Automation.ObjectProjection.rules rule hr _ _ _ ha
  have hout := ProjectionTraceExtension.condition hZ2 _ _ _ (.conjL hT)
    (HornExprRange.range hZ2 rule.head _ _ _ hw2 hn2 hh2) (.conjR (.conjR hT)) hs
  exact of_eq (by simp only [Formula.raise, ProjectionTraceSyntax.condition_rename]) hout

theorem condition_from_rule {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (rule : Rule)
    (hr : rule ∈ YesMetaZFC.Automation.ObjectProjection.rules) (w r : Fin m) (env : Fin rule.arity → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat rule.arity w env))
    (hh : Derives Γ (graph rule.head w env r)) (hp : Derives Γ (ProjectionExprQuery.premises rule.premises w env)) :
    Derives Γ (ProjectionTraceSyntax.condition w r) := by
  rcases premises_shape rule hr with he | ⟨e, he⟩
  · exact leaf hZ rule hr he w r env hw hn hh
  · have hp1 : Derives Γ ((ProjectionExprQuery.query e w env).conj (HornRuleSyntax.truth)) := of_eq (by rw [he]; rfl) hp
    exact unary hZ rule hr e he w r env hw hn hh (.conjL hp1)

theorem query_from_rule {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (rule : Rule)
    (hr : rule ∈ YesMetaZFC.Automation.ObjectProjection.rules) (w : Fin m) (env : Fin rule.arity → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat rule.arity w env))
    (hp : Derives Γ (ProjectionExprQuery.premises rule.premises w env)) :
    Derives Γ (ProjectionExprQuery.query rule.head w env) := by
  have he := HornExprExistence.exists_value hZ rule.head w env hw hn
  let B := (Formula.mem (Fin.last m) w.castSucc).conj (graph rule.head w.castSucc (fun i => (env i).castSucc) (Fin.last m))
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) he
  have hZ1 := ZFContext.under hZ B
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw B)
  have hn1 := of_eq (environmentNat_rename rule.arity w env Fin.castSucc) (under hn B)
  have hp1 := of_eq (ProjectionExprQuery.premises_rename rule.premises w env Fin.castSucc) (under hp B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hc := condition_from_rule hZ1 rule hr _ _ _ hw1 hn1 (.conjR hB) hp1
  have hout : Derives Δ (ProjectionExprQuery.query rule.head w.castSucc (fun i => (env i).castSucc)) := by
    apply Derives.exI (Fin.last m)
    exact of_eq (by simp only [Formula.instantiate, Formula.rename, graph_rename,
      ProjectionTraceSyntax.condition_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI (.conjR hB) hc)
  exact of_eq (ProjectionExprQuery.query_rename rule.head w env Fin.castSucc).symm hout

end PPAC.Migration.Internal.ProjectionRuleConstruction
