import PPAC.Migration.Internal.PureSyntaxVariableExpr

/-! 原变量检查规则局部矩阵与纯Term守卫的实际相容；完整表的其他头标签逐一排除。 -/
namespace PPAC.Migration.Internal.PureSyntaxTermMatrix
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax HornBinderSyntax PureSyntaxVariableExpr
open SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC.Automation.ObjectHorn (Expr Rule)
open YesMetaZFC.Automation
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem variable_head_variables (bound : Bool) : ∀ i : Fin 3, i ∈ (ObjectTermSyntax.variableRule (!bound)).head.variables := by
  have hr : ObjectTermSyntax.variableRule (!bound) ∈ PureSyntaxRules.rules := by
    cases bound with
    | false => exact List.mem_cons_of_mem _ List.mem_cons_self
    | true => exact List.mem_cons_self
  exact PureSyntaxRules.head_variables _ hr

theorem matrix_sound {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (bound : Bool)
    (w b f n r R : Fin m) (env : Fin 3 → Fin m) (hw : Derives Γ (omega w))
    (hn : Derives Γ (environmentNat 3 w env)) (hr : Derives Γ (PureSyntaxTrace.termRow w b f n r))
    (hm : Derives Γ (HornRuleSyntax.matrix (ObjectTermSyntax.variableRule (!bound)) w r R env)) :
    Derives Γ (SyntaxTermSyntax.term w b f n) := by
  have hg := Derives.conjL hm
  rw [actual_head bound] at hg
  have h0 := HornNodeFields.field_3 hZ 0 (fields bound) w r env (SyntaxAtomSyntax.three b f n) 0 hw hn hg hr
  have h1 := HornNodeFields.field_3 hZ 0 (fields bound) w r env (SyntaxAtomSyntax.three b f n) 1 hw hn hg hr
  have h2 := HornNodeFields.field_3 hZ 0 (fields bound) w r env (SyntaxAtomSyntax.three b f n) 2 hw hn hg hr
  have hv := Derives.impE (.conjL (variable_iff hZ bound (2 : Fin 3) w n env hw hn)) h2
  have hguards : Derives Γ (HornRuleSyntax.guards [(.var 2, .var (if bound then 0 else 1))] w env) :=
    of_eq (congrArg (fun gs => HornRuleSyntax.guards gs w env) (actual_guards bound)) (.conjL (.conjR hm))
  have hmem := Derives.impE (.conjL (HornRuleValue.guard_at hZ (.var 2) (.var (if bound then 0 else 1)) w (env 2) (env (if bound then 0 else 1)) env hw hn
    (.conjI (environmentNat_at w env hn 2) (.eqRefl _))
    (.conjI (environmentNat_at w env hn (if bound then 0 else 1)) (.eqRefl _)))) (.conjL hguards)
  have he : Derives Γ (.equal (env (if bound then 0 else 1)) (SyntaxTermSyntax.limit bound b f)) := by
    cases bound with
    | false => exact eq_symm (.conjR h1)
    | true => exact eq_symm (.conjR h0)
  have hi := UnorderedPairLogic.mem_container_subst _ _ _ he hmem
  have hc : Derives Γ (SyntaxTermSyntax.contexts w b f) := .conjI
    (mem_subst (eq_symm (.conjR h0)) (environmentNat_at w env hn 0))
    (mem_subst (eq_symm (.conjR h1)) (environmentNat_at w env hn 1))
  exact .impE (.conjR (SyntaxTerms.scope_iff hZ bound w b f n (env 2) hw hv)) (.conjI hc hi)

theorem matrix_complete {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (bound : Bool)
    (w n r R : Fin m) (env : Fin 3 → Fin m) (hw : Derives Γ (omega w))
    (hn : Derives Γ (environmentNat 3 w env))
    (hr : Derives Γ (PureSyntaxTrace.termRow w (env 0) (env 1) n r))
    (hv : Derives Γ (SyntaxVariableSyntax.code bound w (env 2) n))
    (hi : Derives Γ (.mem (env 2) (SyntaxTermSyntax.limit bound (env 0) (env 1)))) :
    Derives Γ (HornRuleSyntax.matrix (ObjectTermSyntax.variableRule (!bound)) w r R env) := by
  have hs : ∀ j : Fin 3, Derives Γ (graph (fields bound j) w env (SyntaxAtomSyntax.three (env 0) (env 1) n j)) := by
    intro j
    refine Fin.cases ?_ (fun k => ?_) j
    · exact .conjI (environmentNat_at w env hn 0) (.eqRefl _)
    · refine Fin.cases ?_ (fun l => ?_) k
      · exact .conjI (environmentNat_at w env hn 1) (.eqRefl _)
      · refine Fin.cases ?_ (fun z => Fin.elim0 z) l
        exact .impE (.conjR (variable_iff hZ bound (2 : Fin 3) w n env hw hn)) hv
  have hhead := HornExprForest.constructor_graph 3 0 (fields bound) w r env (SyntaxAtomSyntax.three (env 0) (env 1) n) hs hr
  have hactual : Derives Γ (graph (ObjectTermSyntax.variableRule (!bound)).head w env r) :=
    of_eq (congrArg (fun e => graph e w env r) (actual_head bound).symm) hhead
  have ht : env (if bound then 0 else 1) = SyntaxTermSyntax.limit bound (env 0) (env 1) := by cases bound <;> rfl
  have hmem : Derives Γ (.mem (env 2) (env (if bound then 0 else 1))) := of_eq (congrArg (Formula.mem (env 2)) ht.symm) hi
  have hg := Derives.impE (.conjR (HornRuleValue.guard_at hZ (.var 2) (.var (if bound then 0 else 1)) w (env 2) (env (if bound then 0 else 1)) env hw hn
    (.conjI (environmentNat_at w env hn 2) (.eqRefl _))
    (.conjI (environmentNat_at w env hn (if bound then 0 else 1)) (.eqRefl _)))) hmem
  have hguards : Derives Γ (HornRuleSyntax.guards (ObjectTermSyntax.variableRule (!bound)).guards w env) :=
    of_eq (congrArg (fun gs => HornRuleSyntax.guards gs w env) (actual_guards bound).symm) (.conjI hg HornRuleSyntax.truth_proved)
  exact .conjI hactual (.conjI hguards HornRuleSyntax.truth_proved)

theorem application_complete {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (bound : Bool)
    (w n r R : Fin m) (env : Fin 3 → Fin m) (hw : Derives Γ (omega w))
    (hn : Derives Γ (environmentNat 3 w env))
    (hr : Derives Γ (PureSyntaxTrace.termRow w (env 0) (env 1) n r))
    (hv : Derives Γ (SyntaxVariableSyntax.code bound w (env 2) n))
    (hi : Derives Γ (.mem (env 2) (SyntaxTermSyntax.limit bound (env 0) (env 1)))) :
    Derives Γ (HornApplicationSyntax.application (ObjectTermSyntax.variableRule (!bound)) w r R) := by
  have hm := matrix_complete hZ bound w n r R env hw hn hr hv hi
  have hb := HornExprBounds.intro_environmentBound r env (fun i =>
    HornExprBounds.variable_bound hZ (ObjectTermSyntax.variableRule (!bound)).head i (variable_head_variables bound i) w r env hw hn (.conjL hm))
  exact HornApplicationRules.intro_application _ w r R env hn hb hm

theorem application_sound {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (bound : Bool)
    (w b f n r R : Fin m) (hw : Derives Γ (omega w))
    (hr : Derives Γ (PureSyntaxTrace.termRow w b f n r))
    (ha : Derives Γ (HornApplicationSyntax.application (ObjectTermSyntax.variableRule (!bound)) w r R)) :
    Derives Γ (SyntaxTermSyntax.term w b f n) := by
  let B := HornApplicationSyntax.body (ObjectTermSyntax.variableRule (!bound)) w r R
  let Δ := Context.add B (raisedContext 3 Γ)
  apply HornApplicationRules.eliminate_application (ObjectTermSyntax.variableRule (!bound)) w r R _ ha
  have hw1 : Derives Δ (omega (old 3 w)) := of_eq (omega_rename w (old 3)) (HornBinderRules.under_body 3 hw B)
  have hr1 : Derives Δ (PureSyntaxTrace.termRow (old 3 w) (old 3 b) (old 3 f) (old 3 n) (old 3 r)) := of_eq (PureSyntaxTrace.termRow_rename w b f n r (old 3)) (HornBinderRules.under_body 3 hr B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have ht := matrix_sound (HornBinderRules.zf_body 3 hZ B) bound (old 3 w) (old 3 b) (old 3 f) (old 3 n) (old 3 r) (old 3 R) (slot 3) hw1 (.conjL hB) hr1 (.conjR (.conjR hB))
  exact of_eq (SyntaxTermSyntax.term_rename w b f n (old 3)).symm ht

theorem nonterm_imp {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (rules : List Rule)
    (hn : ∀ rule, rule ∈ rules → OriginalRuleTags.nonzeroOuter rule.head = true)
    (w b f n r R : Fin m) (hw : Derives Γ (omega w)) (hr : Derives Γ (PureSyntaxTrace.termRow w b f n r)) :
    Derives Γ ((HornStepSyntax.step rules w r R).imp .bot) := by
  induction rules with
  | nil => exact .impI (.hyp (Or.inl rfl))
  | cons rule rest ih =>
    have h0 : Derives Γ ((HornApplicationSyntax.application rule w r R).imp .bot) := by
      apply Derives.impI
      exact OriginalHeadDisjoint.application_contradiction (ZFContext.add hZ _) rule (hn rule List.mem_cons_self) 3 w r R (SyntaxAtomSyntax.three b f n) (add hw _) (add hr _) (.hyp (Or.inl rfl))
    have ht := ih (fun r h => hn r (List.mem_cons_of_mem rule h))
    exact .impE (.impE (SourcePropositional.disjunction_elimination (HornApplicationSyntax.application rule w r R) (HornStepSyntax.step rest w r R) .bot) h0) ht

theorem step_sound {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b f n r R : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (PureSyntaxTrace.termRow w b f n r))
    (hs : Derives Γ (HornStepSyntax.step PureSyntaxRules.rules w r R)) : Derives Γ (SyntaxTermSyntax.term w b f n) := by
  apply Derives.disjE hs
  · exact application_sound (ZFContext.add hZ _) true w b f n r R (add hw _) (add hr _) (.hyp (Or.inl rfl))
  · apply Derives.disjE (.hyp (Or.inl rfl))
    · exact application_sound (ZFContext.add (ZFContext.add hZ _) _) false w b f n r R (add (add hw _) _) (add (add hr _) _) (.hyp (Or.inl rfl))
    · exact .botE (.impE (nonterm_imp (ZFContext.add (ZFContext.add hZ _) _) PureSyntaxRules.remaining PureSyntaxRules.remaining_nonzero w b f n r R (add (add hw _) _) (add (add hr _) _)) (.hyp (Or.inl rfl)))

end PPAC.Migration.Internal.PureSyntaxTermMatrix
