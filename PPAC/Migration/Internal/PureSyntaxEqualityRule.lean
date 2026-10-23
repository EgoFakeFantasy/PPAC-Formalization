import PPAC.Migration.Internal.PureSyntaxConstantComplete
import PPAC.Migration.Internal.PureSyntaxTermPremise

/-! 原等式规则的真实两个项前提及有界赋值；局部对象健全与构造。 -/
namespace PPAC.Migration.Internal.PureSyntaxEqualityRule
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC.Automation.ObjectHorn (Expr)
open YesMetaZFC.Automation

def input : Expr 4 := Expr.node (.literal 3) [.var 2, .var 3]
def fields : Fin 2 → Expr 4 := Fin.cases (.var 2) (Fin.cases (.var 3) Fin.elim0)

theorem actual_head : ObjectFormulaSyntax.equalityRule.head = PureSyntaxFormulaGraph.head (0 : Fin 4) 1 input := rfl

theorem rule_mem : ObjectFormulaSyntax.equalityRule ∈ PureSyntaxRules.rules := by
  simp [PureSyntaxRules.rules, PureSyntaxRules.remaining]

theorem input_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n : Fin m) (env : Fin 4 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 4 w env)) :
    Derives Γ ((graph input w env n).iff (SyntaxAtomSyntax.equalCode w (env 2) (env 3) n)) := by
  have hv (i : Fin 4) : Derives Γ (graph (.var i) w env (env i)) := .conjI (environmentNat_at w env hn i) (.eqRefl _)
  exact HornExprConstructor.constructor_iff hZ 2 3 fields w n env (SyntaxAtomSyntax.two (env 2) (env 3)) hw hn
    (fun i => Fin.cases (hv 2) (fun j => Fin.cases (hv 3) (fun z => Fin.elim0 z) j) i)

theorem matrix_sound {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b f n r R : Fin m) (env : Fin 4 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 4 w env)) (hc : Derives Γ (PureSyntaxTrace.closed w R))
    (hr : Derives Γ (PureSyntaxTrace.formulaRow w b f n r))
    (hm : Derives Γ (HornRuleSyntax.matrix ObjectFormulaSyntax.equalityRule w r R env)) :
    Derives Γ (FormulaCodeSyntax.formulaCode w n b f) := by
  have hg : Derives Γ (graph (PureSyntaxFormulaGraph.head (0 : Fin 4) 1 input) w env r) := of_eq
    (congrArg (fun e => graph e w env r) actual_head) (.conjL hm)
  have hs := PureSyntaxFormulaGraph.recover hZ (0 : Fin 4) 1 input w b f n r env hw hn hr hg
  have heq := Derives.impE (.conjL (input_iff hZ w n env hw hn)) (.conjR (.conjR hs))
  have hp : Derives Γ (HornRuleSyntax.premise (PureSyntaxTermPremise.head (0 : Fin 4) 1 2) w R env) := .conjL (.conjR (.conjR hm))
  have hq : Derives Γ (HornRuleSyntax.premise (PureSyntaxTermPremise.head (0 : Fin 4) 1 3) w R env) := .conjL (.conjR (.conjR (.conjR hm)))
  have hx := PureSyntaxTermPremise.checked hZ (0 : Fin 4) 1 2 w R env hw hn hc hp
  have hy := PureSyntaxTermPremise.checked hZ (0 : Fin 4) 1 3 w R env hw hn hc hq
  have ht := Derives.impE (.conjR (FormulaCodeKnownAtomic.equal_iff hZ w (env 0) (env 1) (env 2) (env 3) n hw heq)) (.conjI hx hy)
  exact PureSyntaxFormulaGraph.contexts_subst w b f (env 0) (env 1) n (eq_symm (.conjL hs)) (eq_symm (.conjL (.conjR hs))) ht

theorem matrix_complete {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n r R p q : Fin m) (env : Fin 4 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 4 w env))
    (he : Derives Γ (SyntaxAtomSyntax.equalCode w (env 2) (env 3) n))
    (hr : Derives Γ (PureSyntaxTrace.formulaRow w (env 0) (env 1) n r))
    (hp : Derives Γ (PureSyntaxTrace.termRow w (env 0) (env 1) (env 2) p))
    (hq : Derives Γ (PureSyntaxTrace.termRow w (env 0) (env 1) (env 3) q))
    (hpm : Derives Γ (.mem p R)) (hqm : Derives Γ (.mem q R)) :
    Derives Γ (HornRuleSyntax.matrix ObjectFormulaSyntax.equalityRule w r R env) := by
  have hi := Derives.impE (.conjR (input_iff hZ w n env hw hn)) he
  have hg := PureSyntaxFormulaGraph.construct (0 : Fin 4) 1 input w n r env hn hr hi
  have gp := PureSyntaxTermPremise.construct (0 : Fin 4) 1 2 w p env hn hp
  have gq := PureSyntaxTermPremise.construct (0 : Fin 4) 1 3 w q env hn hq
  have pp := Derives.impE (.conjR (HornRuleValue.premise_at hZ _ w R p env hw hn gp)) hpm
  have pq := Derives.impE (.conjR (HornRuleValue.premise_at hZ _ w R q env hw hn gq)) hqm
  exact .conjI (of_eq (congrArg (fun e => graph e w env r) actual_head.symm) hg)
    (.conjI HornRuleSyntax.truth_proved (.conjI pp (.conjI pq HornRuleSyntax.truth_proved)))

theorem application_complete {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n r R p q : Fin m) (env : Fin 4 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 4 w env))
    (he : Derives Γ (SyntaxAtomSyntax.equalCode w (env 2) (env 3) n))
    (hr : Derives Γ (PureSyntaxTrace.formulaRow w (env 0) (env 1) n r))
    (hp : Derives Γ (PureSyntaxTrace.termRow w (env 0) (env 1) (env 2) p))
    (hq : Derives Γ (PureSyntaxTrace.termRow w (env 0) (env 1) (env 3) q))
    (hpm : Derives Γ (.mem p R)) (hqm : Derives Γ (.mem q R)) :
    Derives Γ (HornApplicationSyntax.application ObjectFormulaSyntax.equalityRule w r R) := by
  have hm := matrix_complete hZ w n r R p q env hw hn he hr hp hq hpm hqm
  have hb := HornExprBounds.intro_environmentBound r env (fun i =>
    HornExprBounds.variable_bound hZ ObjectFormulaSyntax.equalityRule.head i (PureSyntaxRules.head_variables _ rule_mem i) w r env hw hn (.conjL hm))
  exact HornApplicationRules.intro_application _ w r R env hn hb hm

theorem application_sound {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b f n r R : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (PureSyntaxTrace.closed w R))
    (hr : Derives Γ (PureSyntaxTrace.formulaRow w b f n r))
    (ha : Derives Γ (HornApplicationSyntax.application ObjectFormulaSyntax.equalityRule w r R)) :
    Derives Γ (FormulaCodeSyntax.formulaCode w n b f) := by
  let B := HornApplicationSyntax.body ObjectFormulaSyntax.equalityRule w r R
  let Δ := Context.add B (raisedContext 4 Γ)
  apply HornApplicationRules.eliminate_application ObjectFormulaSyntax.equalityRule w r R _ ha
  have hw1 : Derives Δ (omega (old 4 w)) := of_eq (omega_rename w (old 4)) (HornBinderRules.under_body 4 hw B)
  have hc1 : Derives Δ (PureSyntaxTrace.closed (old 4 w) (old 4 R)) := of_eq (PureSyntaxTrace.closed_rename w R (old 4)) (HornBinderRules.under_body 4 hc B)
  have hr1 : Derives Δ (PureSyntaxTrace.formulaRow (old 4 w) (old 4 b) (old 4 f) (old 4 n) (old 4 r)) := of_eq (PureSyntaxTrace.formulaRow_rename w b f n r (old 4)) (HornBinderRules.under_body 4 hr B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have ht := matrix_sound (HornBinderRules.zf_body 4 hZ B) _ _ _ _ _ _ (slot 4) hw1 (.conjL hB) hc1 hr1 (.conjR (.conjR hB))
  exact of_eq (FormulaCodeSyntax.formulaCode_rename w n b f (old 4)).symm ht

end PPAC.Migration.Internal.PureSyntaxEqualityRule
