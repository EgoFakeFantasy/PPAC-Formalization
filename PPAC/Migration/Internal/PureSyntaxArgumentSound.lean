import PPAC.Migration.Internal.PureSyntaxConsSound
import PPAC.Migration.Internal.HornNodeDisjoint

/-! 完整十五规则的参数行分派及查询健全性；统一严格成员IH暂保留。 -/
namespace PPAC.Migration.Internal.PureSyntaxArgumentSound
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax HornApplicationSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)
open PureSyntaxListInductionSyntax
open YesMetaZFC.Automation.ObjectHorn (Expr Rule)
open YesMetaZFC.Automation

def notOneOuter {n} : Expr n → Bool
  | .succ (.pair (.literal tag) _) => tag != 1
  | _ => false

def nonargument : List Rule := ObjectTermSyntax.variableRule false :: ObjectTermSyntax.variableRule true :: PureSyntaxRules.remaining.drop 2

theorem nonargument_classified : nonargument.all (fun r => notOneOuter r.head) = true := by decide

theorem nonargument_not_one (rule : Rule) (hr : rule ∈ nonargument) : notOneOuter rule.head = true :=
  List.all_eq_true.mp nonargument_classified rule hr

theorem outer_shape {n} (e : Expr n) (he : notOneOuter e = true) :
    ∃ tag payload, tag ≠ 1 ∧ e = Expr.succ (.pair (.literal tag) payload) := by
  cases e with
  | literal _ | var _ | pair _ _ => cases he
  | succ e =>
    cases e with
    | literal _ | var _ | succ _ => cases he
    | pair a payload =>
      cases a with
      | var _ | succ _ | pair _ _ => cases he
      | literal tag => exact ⟨tag, payload, by simpa only [notOneOuter, bne_iff_ne] using he, rfl⟩

theorem rule_cases (rule : Rule) (hr : rule ∈ PureSyntaxRules.rules) :
    rule = ObjectTermSyntax.nilRule ∨ rule = ObjectTermSyntax.consRule ∨ rule ∈ nonargument := by
  simp only [PureSyntaxRules.rules, PureSyntaxRules.remaining, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact Or.inl rfl
    | exact Or.inr (Or.inl rfl)
    | exact Or.inr (Or.inr (by simp [nonargument, PureSyntaxRules.remaining]))

theorem application_contradiction {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (rule : Rule)
    (hr : rule ∈ nonargument) (w b f k n r R : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (PureSyntaxTrace.argumentRow w b f k n r))
    (ha : Derives Γ (application rule w r R)) : Derives Γ .bot := by
  rcases outer_shape rule.head (nonargument_not_one rule hr) with ⟨tag, payload, hk, hs⟩
  let B := body rule w r R
  let Δ := Context.add B (raisedContext rule.arity Γ)
  apply HornApplicationRules.eliminate_application rule w r R .bot ha
  have hZ1 := HornBinderRules.zf_body rule.arity hZ B
  have hw1 : Derives Δ (omega (old rule.arity w)) := of_eq (omega_rename w (old rule.arity)) (HornBinderRules.under_body rule.arity hw B)
  have hc1 : Derives Δ (PureSyntaxTrace.argumentRow (old rule.arity w) (old rule.arity b) (old rule.arity f) (old rule.arity k) (old rule.arity n) (old rule.arity r)) := of_eq
    (PureSyntaxTrace.argumentRow_rename w b f k n r (old rule.arity)) (HornBinderRules.under_body rule.arity hc B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hg : Derives Δ (graph rule.head (old rule.arity w) (slot rule.arity) (old rule.arity r)) := .conjL (.conjR (.conjR hB))
  rw [hs] at hg
  exact HornNodeDisjoint.node_contradiction hZ1 tag 1 4 hk payload _ _ _ _ hw1 (.conjL hB) hg hc1

theorem step_sound {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b f k n r R : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (allIH w n))
    (hs : Derives Γ (RestrictionSyntax.subset R w)) (hc : Derives Γ (PureSyntaxTrace.closed w R))
    (hr : Derives Γ (PureSyntaxTrace.argumentRow w b f k n r))
    (he : Derives Γ (HornStepSyntax.step PureSyntaxRules.rules w r R)) :
    Derives Γ (SyntaxMixedImageCodeSyntax.termList w k b f n) := by
  apply HornStepSyntax.step_elim PureSyntaxRules.rules w r R _ he
  intro rule hmem
  apply Derives.impI
  rcases rule_cases rule hmem with h | h | h
  · subst rule
    exact PureSyntaxNilRule.application_sound (ZFContext.add hZ _) w b f k n r R (add hw _) (add hr _) (.hyp (Or.inl rfl))
  · subst rule
    exact PureSyntaxConsSound.application_sound (ZFContext.add hZ _) w b f k n r R (add hw _) (add hi _) (add hs _) (add hc _) (add hr _) (.hyp (Or.inl rfl))
  · exact .botE (application_contradiction (ZFContext.add hZ _) rule h w b f k n r R (add hw _) (add hr _) (.hyp (Or.inl rfl)))

theorem condition_sound {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b f k n r : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (allIH w n))
    (hr : Derives Γ (PureSyntaxTrace.argumentRow w b f k n r))
    (hc : Derives Γ (PureSyntaxTrace.condition w r)) : Derives Γ (SyntaxMixedImageCodeSyntax.termList w k b f n) := by
  let B := PureSyntaxTrace.witness w.castSucc r.castSucc (Fin.last m)
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) hc
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw B)
  have hi1 : Derives Δ (allIH w.castSucc n.castSucc) := of_eq (allIH_rename w n Fin.castSucc) (under hi B)
  have hr1 : Derives Δ (PureSyntaxTrace.argumentRow w.castSucc b.castSucc f.castSucc k.castSucc n.castSucc r.castSucc) := of_eq (PureSyntaxTrace.argumentRow_rename w b f k n r Fin.castSucc) (under hr B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have he := PureSyntaxTrace.closed_at _ _ _ (.conjR (.conjR hB)) (.conjL (.conjR hB))
  have ht := step_sound (ZFContext.under hZ B) _ _ _ _ _ _ _ hw1 hi1 (.conjL hB) (.conjR (.conjR hB)) hr1 he
  exact of_eq (SyntaxMixedImageCodeSyntax.termList_rename w k b f n Fin.castSucc).symm ht

theorem checked_sound {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b f k n : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (allIH w n))
    (ht : Derives Γ (PureSyntaxTrace.arguments w b f k n)) : Derives Γ (SyntaxMixedImageCodeSyntax.termList w k b f n) := by
  let B := (PureSyntaxTrace.argumentRow w.castSucc b.castSucc f.castSucc k.castSucc n.castSucc (Fin.last m)).conj (PureSyntaxTrace.condition w.castSucc (Fin.last m))
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) ht
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw B)
  have hi1 : Derives Δ (allIH w.castSucc n.castSucc) := of_eq (allIH_rename w n Fin.castSucc) (under hi B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  exact of_eq (SyntaxMixedImageCodeSyntax.termList_rename w k b f n Fin.castSucc).symm
    (condition_sound (ZFContext.under hZ B) _ _ _ _ _ _ hw1 hi1 (.conjL hB) (.conjR hB))

end PPAC.Migration.Internal.PureSyntaxArgumentSound
