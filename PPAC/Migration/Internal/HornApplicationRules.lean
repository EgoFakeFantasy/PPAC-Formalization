import PPAC.Migration.Internal.HornApplicationSyntax

/-! 原规则的内部有界赋值实际引入/消去，自然守卫从原搜索界推出。 -/
namespace PPAC.Migration.Internal.HornApplicationRules
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax HornExprSyntax HornExprBounds HornRuleSyntax HornApplicationSyntax
open SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC.Automation.ObjectHorn (Rule)

theorem intro_nat {m n} {Γ : Context m} (w : Fin m) (env : Fin n → Fin m)
    (hn : ∀ i, Derives Γ (.mem (env i) w)) : Derives Γ (environmentNat n w env) := by
  induction n with
  | zero => exact truth_proved
  | succ n ih => exact .conjI (hn 0) (ih (fun i => env i.succ) (fun i => hn i.succ))

theorem natural_below {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w row x : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (.mem row w)) (hx : Derives Γ (NaturalAdditionBounds.below x row)) :
    Derives Γ (.mem x w) := by
  apply Derives.disjE hx
  · exact mem_subst (eq_symm (.hyp (Or.inl rfl))) (add hr _)
  · exact StructuralListTraceOrder.member_member (ZFContext.add hZ _) w x row (add hw _) (add hr _) (.hyp (Or.inl rfl))

theorem natural_environment {m n} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w row : Fin m) (env : Fin n → Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (.mem row w)) (hb : Derives Γ (environmentBound n row env)) :
    Derives Γ (environmentNat n w env) := by
  induction n with
  | zero => exact truth_proved
  | succ n ih => exact .conjI (natural_below hZ w row (env 0) hw hr (.conjL hb)) (ih (fun i => env i.succ) (.conjR hb))

theorem intro_application {m} {Γ : Context m} (rule : Rule) (w row trace : Fin m) (env : Fin rule.arity → Fin m)
    (hn : Derives Γ (environmentNat rule.arity w env)) (hb : Derives Γ (environmentBound rule.arity row env))
    (hm : Derives Γ (matrix rule w row trace env)) : Derives Γ (application rule w row trace) := by
  apply HornBinderRules.intro_many rule.arity (body rule w row trace) env
  exact of_eq (body_assign rule w row trace env).symm (.conjI hn (.conjI hb hm))

theorem eliminate_application {m} {Γ : Context m} (rule : Rule) (w row trace : Fin m) (p : Formula m)
    (he : Derives Γ (application rule w row trace))
    (hc : Derives (Context.add (body rule w row trace) (raisedContext rule.arity Γ)) (p.rename (old rule.arity))) :
    Derives Γ p := HornBinderRules.eliminate_many rule.arity (body rule w row trace) p he hc

theorem intro_bounded {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (rule : Rule) (w row trace : Fin m) (env : Fin rule.arity → Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (.mem row w))
    (hb : Derives Γ (environmentBound rule.arity row env)) (hm : Derives Γ (matrix rule w row trace env)) :
    Derives Γ (application rule w row trace) :=
  intro_application rule w row trace env (natural_environment hZ w row env hw hr hb) hb hm

theorem lookup_head_intro {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w row trace : Fin m) (env : Fin 2 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 2 w env))
    (hm : Derives Γ (matrix YesMetaZFC.Automation.ObjectSyntaxTransform.lookupHead w row trace env)) :
    Derives Γ (application YesMetaZFC.Automation.ObjectSyntaxTransform.lookupHead w row trace) :=
  intro_application _ w row trace env hn (HornExprBounds.lookup_head_bound hZ w row env hw hn (.conjL hm)) hm

theorem lookup_tail_intro {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w row trace : Fin m) (env : Fin 4 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 4 w env))
    (hm : Derives Γ (matrix YesMetaZFC.Automation.ObjectSyntaxTransform.lookupTail w row trace env)) :
    Derives Γ (application YesMetaZFC.Automation.ObjectSyntaxTransform.lookupTail w row trace) :=
  intro_application _ w row trace env hn (HornExprBounds.lookup_tail_bound hZ w row env hw hn (.conjL hm)) hm

end PPAC.Migration.Internal.HornApplicationRules
