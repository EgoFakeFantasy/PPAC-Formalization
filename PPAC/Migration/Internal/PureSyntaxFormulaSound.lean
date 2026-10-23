import PPAC.Migration.Internal.PureSyntaxUnaryComplete
import PPAC.Migration.Internal.HornNodeDisjoint

/-! 完整十五条纯语法规则的公式行分派；可靠性只保留统一对象IH。 -/
namespace PPAC.Migration.Internal.PureSyntaxFormulaSound
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax HornApplicationSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)
open PureSyntaxFormulaInductionSyntax
open YesMetaZFC.Automation.ObjectHorn (Expr Rule)
open YesMetaZFC.Automation

def notFourOuter {n} : Expr n → Bool
  | .succ (.pair (.literal tag) _) => tag != 4
  | _ => false

def nonformula : List Rule := [ObjectTermSyntax.variableRule false, ObjectTermSyntax.variableRule true, ObjectTermSyntax.nilRule, ObjectTermSyntax.consRule]

theorem nonformula_classified : nonformula.all (fun r => notFourOuter r.head) = true := by decide

theorem nonformula_not_four (rule : Rule) (hr : rule ∈ nonformula) : notFourOuter rule.head = true :=
  List.all_eq_true.mp nonformula_classified rule hr

theorem outer_shape {n} (e : Expr n) (he : notFourOuter e = true) :
    ∃ tag payload, tag ≠ 4 ∧ e = Expr.succ (.pair (.literal tag) payload) := by
  cases e with
  | literal _ | var _ | pair _ _ => cases he
  | succ e =>
    cases e with
    | literal _ | var _ | succ _ => cases he
    | pair a payload =>
      cases a with
      | var _ | succ _ | pair _ _ => cases he
      | literal tag => exact ⟨tag, payload, by simpa only [notFourOuter, bne_iff_ne] using he, rfl⟩

theorem application_contradiction {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (rule : Rule)
    (hr : rule ∈ nonformula) (w b f n r R : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (PureSyntaxTrace.formulaRow w b f n r))
    (ha : Derives Γ (application rule w r R)) : Derives Γ .bot := by
  rcases outer_shape rule.head (nonformula_not_four rule hr) with ⟨tag, payload, hk, hs⟩
  let B := body rule w r R
  let Δ := Context.add B (raisedContext rule.arity Γ)
  apply HornApplicationRules.eliminate_application rule w r R .bot ha
  have hZ1 := HornBinderRules.zf_body rule.arity hZ B
  have hw1 : Derives Δ (omega (old rule.arity w)) := of_eq (omega_rename w (old rule.arity)) (HornBinderRules.under_body rule.arity hw B)
  have hc1 : Derives Δ (PureSyntaxTrace.formulaRow (old rule.arity w) (old rule.arity b) (old rule.arity f) (old rule.arity n) (old rule.arity r)) := of_eq
    (PureSyntaxTrace.formulaRow_rename w b f n r (old rule.arity)) (HornBinderRules.under_body rule.arity hc B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hg : Derives Δ (graph rule.head (old rule.arity w) (slot rule.arity) (old rule.arity r)) := .conjL (.conjR (.conjR hB))
  rw [hs] at hg
  exact HornNodeDisjoint.node_contradiction hZ1 tag 4 3 hk payload _ _ _ _ hw1 (.conjL hB) hg hc1

theorem step_sound {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b f n r R : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (allIH w n))
    (hs : Derives Γ (RestrictionSyntax.subset R w)) (hc : Derives Γ (PureSyntaxTrace.closed w R))
    (hr : Derives Γ (PureSyntaxTrace.formulaRow w b f n r))
    (he : Derives Γ (HornStepSyntax.step PureSyntaxRules.rules w r R)) :
    Derives Γ (FormulaCodeSyntax.formulaCode w n b f) := by
  apply HornStepSyntax.step_elim PureSyntaxRules.rules w r R _ he
  intro rule hmem
  apply Derives.impI
  simp only [PureSyntaxRules.rules, PureSyntaxRules.remaining, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact .botE (application_contradiction (ZFContext.add hZ _) _ (by simp [nonformula]) w b f n r R (add hw _) (add hr _) (.hyp (Or.inl rfl)))
  · exact .botE (application_contradiction (ZFContext.add hZ _) _ (by simp [nonformula]) w b f n r R (add hw _) (add hr _) (.hyp (Or.inl rfl)))
  · exact .botE (application_contradiction (ZFContext.add hZ _) _ (by simp [nonformula]) w b f n r R (add hw _) (add hr _) (.hyp (Or.inl rfl)))
  · exact .botE (application_contradiction (ZFContext.add hZ _) _ (by simp [nonformula]) w b f n r R (add hw _) (add hr _) (.hyp (Or.inl rfl)))
  · exact PureSyntaxConstantRule.application_sound (ZFContext.add hZ _) false w b f n r R (add hw _) (add hr _) (.hyp (Or.inl rfl))
  · exact PureSyntaxConstantRule.application_sound (ZFContext.add hZ _) true w b f n r R (add hw _) (add hr _) (.hyp (Or.inl rfl))
  · exact PureSyntaxMembershipRule.application_sound (ZFContext.add hZ _) w b f n r R (add hw _) (add hs _) (add hc _) (add hr _) (.hyp (Or.inl rfl))
  · exact PureSyntaxEqualityRule.application_sound (ZFContext.add hZ _) w b f n r R (add hw _) (add hc _) (add hr _) (.hyp (Or.inl rfl))
  · exact PureSyntaxUnaryRule.application_sound (ZFContext.add hZ _) 0 w b f n r R (add hw _) (add hi _) (add hs _) (add hc _) (add hr _) (.hyp (Or.inl rfl))
  · exact PureSyntaxBinaryRule.application_sound (ZFContext.add hZ _) 0 w b f n r R (add hw _) (add hi _) (add hs _) (add hc _) (add hr _) (.hyp (Or.inl rfl))
  · exact PureSyntaxBinaryRule.application_sound (ZFContext.add hZ _) 1 w b f n r R (add hw _) (add hi _) (add hs _) (add hc _) (add hr _) (.hyp (Or.inl rfl))
  · exact PureSyntaxBinaryRule.application_sound (ZFContext.add hZ _) 2 w b f n r R (add hw _) (add hi _) (add hs _) (add hc _) (add hr _) (.hyp (Or.inl rfl))
  · exact PureSyntaxBinaryRule.application_sound (ZFContext.add hZ _) 3 w b f n r R (add hw _) (add hi _) (add hs _) (add hc _) (add hr _) (.hyp (Or.inl rfl))
  · exact PureSyntaxUnaryRule.application_sound (ZFContext.add hZ _) 1 w b f n r R (add hw _) (add hi _) (add hs _) (add hc _) (add hr _) (.hyp (Or.inl rfl))
  · exact PureSyntaxUnaryRule.application_sound (ZFContext.add hZ _) 2 w b f n r R (add hw _) (add hi _) (add hs _) (add hc _) (add hr _) (.hyp (Or.inl rfl))

theorem condition_sound {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b f n r : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (allIH w n))
    (hr : Derives Γ (PureSyntaxTrace.formulaRow w b f n r))
    (hc : Derives Γ (PureSyntaxTrace.condition w r)) : Derives Γ (FormulaCodeSyntax.formulaCode w n b f) := by
  let B := PureSyntaxTrace.witness w.castSucc r.castSucc (Fin.last m)
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) hc
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw B)
  have hi1 : Derives Δ (allIH w.castSucc n.castSucc) := of_eq (allIH_rename w n Fin.castSucc) (under hi B)
  have hr1 : Derives Δ (PureSyntaxTrace.formulaRow w.castSucc b.castSucc f.castSucc n.castSucc r.castSucc) := of_eq (PureSyntaxTrace.formulaRow_rename w b f n r Fin.castSucc) (under hr B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have he := PureSyntaxTrace.closed_at _ _ _ (.conjR (.conjR hB)) (.conjL (.conjR hB))
  have ht := step_sound (ZFContext.under hZ B) _ _ _ _ _ _ hw1 hi1 (.conjL hB) (.conjR (.conjR hB)) hr1 he
  exact of_eq (FormulaCodeSyntax.formulaCode_rename w n b f Fin.castSucc).symm ht

theorem checked_sound {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b f n : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (allIH w n))
    (ht : Derives Γ (PureSyntaxTrace.formula w b f n)) : Derives Γ (FormulaCodeSyntax.formulaCode w n b f) := by
  let B := (PureSyntaxTrace.formulaRow w.castSucc b.castSucc f.castSucc n.castSucc (Fin.last m)).conj (PureSyntaxTrace.condition w.castSucc (Fin.last m))
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) ht
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw B)
  have hi1 : Derives Δ (allIH w.castSucc n.castSucc) := of_eq (allIH_rename w n Fin.castSucc) (under hi B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  exact of_eq (FormulaCodeSyntax.formulaCode_rename w n b f Fin.castSucc).symm
    (condition_sound (ZFContext.under hZ B) _ _ _ _ _ hw1 hi1 (.conjL hB) (.conjR hB))

end PPAC.Migration.Internal.PureSyntaxFormulaSound
