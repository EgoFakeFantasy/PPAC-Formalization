import PPAC.Migration.Internal.ProjectionTraceSyntax

/-! 原七规则的实际单点闭轨迹；不通过数值投影结论定义接受。 -/
namespace PPAC.Migration.Internal.ProjectionTraceRules
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxRenameQuerySyntax
open YesMetaZFC.Automation.ObjectHorn (Rule)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem step_mem {m} {Γ : Context m} (rules : List Rule) (rule : Rule) (hr : rule ∈ rules)
    (w r R : Fin m) (ha : Derives Γ (HornApplicationSyntax.application rule w r R)) :
    Derives Γ (HornStepSyntax.step rules w r R) := by
  induction rules with
  | nil => exact False.elim (List.not_mem_nil hr)
  | cons first rest ih =>
    rcases List.mem_cons.mp hr with h | h
    · subst first
      exact .disjL ha
    · exact .disjR (ih h)

theorem step_subst_row {m} {Γ : Context m} (w r s R : Fin m)
    (he : Derives Γ (.equal r s)) (hs : Derives Γ (HornStepSyntax.step YesMetaZFC.Automation.ObjectProjection.rules w r R)) :
    Derives Γ (HornStepSyntax.step YesMetaZFC.Automation.ObjectProjection.rules w s R) := by
  let P := HornStepSyntax.step YesMetaZFC.Automation.ObjectProjection.rules w.castSucc (Fin.last m) R.castSucc
  have h0 : P.instantiate r = HornStepSyntax.step YesMetaZFC.Automation.ObjectProjection.rules w r R := by
    simp only [P, Formula.instantiate, HornStepSyntax.step_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have h1 : P.instantiate s = HornStepSyntax.step YesMetaZFC.Automation.ObjectProjection.rules w s R := by
    simp only [P, Formula.instantiate, HornStepSyntax.step_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact of_eq h1 (Derives.eqSubst P he (of_eq h0.symm hs))

theorem premise_free_eq {m} (rule : Rule) (hn : rule.premises = []) (w r R S : Fin m) :
    HornApplicationSyntax.application rule w r R = HornApplicationSyntax.application rule w r S := by
  simp only [HornApplicationSyntax.application, HornApplicationSyntax.body, HornApplicationSyntax.boundedMatrix,
    HornRuleSyntax.matrix, hn, HornRuleSyntax.premises]

theorem singleton_subset {m} {Γ : Context m} (w r R : Fin m)
    (hr : Derives Γ (.mem r w)) (hp : Derives Γ (PairSyntax.pair R r r)) :
    Derives Γ (RestrictionSyntax.subset R w) := by
  apply Derives.allI
  apply Derives.impI
  let M := Formula.mem (Fin.last m) R.castSucc
  let Δ := Context.add M (Context.image Formula.raise Γ)
  have hp1 : Derives Δ (PairSyntax.pair R.castSucc r.castSucc r.castSucc) := of_eq (PairSyntax.pair_rename R r r Fin.castSucc) (under hp M)
  have hr1 : Derives Δ (.mem r.castSucc w.castSucc) := under hr M
  have hc := UnorderedPairLogic.member_cases R.castSucc r.castSucc r.castSucc (Fin.last m) hp1 (.hyp (Or.inl rfl))
  apply Derives.disjE hc
  · exact mem_subst (eq_symm (.hyp (Or.inl rfl))) (add hr1 _)
  · exact mem_subst (eq_symm (.hyp (Or.inl rfl))) (add hr1 _)

theorem singleton_closed {m} {Γ : Context m} (w r R : Fin m)
    (hp : Derives Γ (PairSyntax.pair R r r))
    (hs : Derives Γ (HornStepSyntax.step YesMetaZFC.Automation.ObjectProjection.rules w r R)) : Derives Γ (ProjectionTraceSyntax.closed w R) := by
  apply Derives.allI
  apply Derives.impI
  let M := Formula.mem (Fin.last m) R.castSucc
  let Δ := Context.add M (Context.image Formula.raise Γ)
  have hp1 : Derives Δ (PairSyntax.pair R.castSucc r.castSucc r.castSucc) := of_eq (PairSyntax.pair_rename R r r Fin.castSucc) (under hp M)
  have hs1 : Derives Δ (HornStepSyntax.step YesMetaZFC.Automation.ObjectProjection.rules w.castSucc r.castSucc R.castSucc) := of_eq (HornStepSyntax.step_rename YesMetaZFC.Automation.ObjectProjection.rules w r R Fin.castSucc) (under hs M)
  have hc := UnorderedPairLogic.member_cases R.castSucc r.castSucc r.castSucc (Fin.last m) hp1 (.hyp (Or.inl rfl))
  apply Derives.disjE hc
  · exact step_subst_row w.castSucc r.castSucc (Fin.last m) R.castSucc (eq_symm (.hyp (Or.inl rfl))) (add hs1 _)
  · exact step_subst_row w.castSucc r.castSucc (Fin.last m) R.castSucc (eq_symm (.hyp (Or.inl rfl))) (add hs1 _)

theorem premise_free_condition {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (rule : Rule)
    (hmem : rule ∈ YesMetaZFC.Automation.ObjectProjection.rules) (hn : rule.premises = []) (w r : Fin m)
    (hr : Derives Γ (.mem r w)) (ha : Derives Γ (HornApplicationSyntax.application rule w r w)) :
    Derives Γ (ProjectionTraceSyntax.condition w r) := by
  let P := PairSyntax.pair (Fin.last m) r.castSucc r.castSucc
  let Δ := Context.add P (Context.image Formula.raise Γ)
  apply Derives.exE (p := P) (PairSyntax.pairing_instance r r (ZFContext.arithmetic hZ).base.pairing)
  have hP : Derives Δ P := .hyp (Or.inl rfl)
  have hr1 : Derives Δ (.mem r.castSucc w.castSucc) := under hr P
  have ha1 : Derives Δ (HornApplicationSyntax.application rule w.castSucc r.castSucc w.castSucc) := of_eq
    (HornApplicationSyntax.application_rename rule w r w Fin.castSucc) (under ha P)
  have hs := step_mem YesMetaZFC.Automation.ObjectProjection.rules rule hmem w.castSucc r.castSucc (Fin.last m)
    (of_eq (premise_free_eq rule hn w.castSucc r.castSucc w.castSucc (Fin.last m)) ha1)
  have hc := singleton_closed w.castSucc r.castSucc (Fin.last m) hP hs
  have hw := ProjectionTraceSyntax.intro_condition w.castSucc r.castSucc (Fin.last m)
    (.conjI (singleton_subset w.castSucc r.castSucc (Fin.last m) hr1 hP)
      (.conjI (UnorderedPairLogic.member_left (Fin.last m) r.castSucc r.castSucc hP) hc))
  exact of_eq (ProjectionTraceSyntax.condition_rename w r Fin.castSucc).symm hw

end PPAC.Migration.Internal.ProjectionTraceRules
