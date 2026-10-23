import PPAC.Migration.Internal.PureSyntaxFormulaGraph

/-! 两种原公式常量的实际矩阵和有界规则应用；不假设类型结论。 -/
namespace PPAC.Migration.Internal.PureSyntaxConstantRule
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC.Automation.ObjectHorn (Expr)
open YesMetaZFC.Automation

def input (truth : Bool) : Expr 2 := Expr.node (.literal (SyntaxAtomSyntax.nullaryTag truth)) []

theorem actual_head (truth : Bool) : (ObjectFormulaSyntax.constantRule (SyntaxAtomSyntax.nullaryTag truth)).head = PureSyntaxFormulaGraph.head (0 : Fin 2) 1 (input truth) := rfl

theorem rule_mem (truth : Bool) : ObjectFormulaSyntax.constantRule (SyntaxAtomSyntax.nullaryTag truth) ∈ PureSyntaxRules.rules := by
  cases truth <;> simp [PureSyntaxRules.rules, PureSyntaxRules.remaining, SyntaxAtomSyntax.nullaryTag]

theorem input_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (truth : Bool) (w n : Fin m) (env : Fin 2 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 2 w env)) :
    Derives Γ ((graph (input truth) w env n).iff (SyntaxNodeSyntax.constructor 0 (SyntaxAtomSyntax.nullaryTag truth) w Fin.elim0 n)) := by
  simpa only [input, List.ofFn_zero] using HornExprConstructor.constructor_iff hZ 0 (SyntaxAtomSyntax.nullaryTag truth) (Fin.elim0 : Fin 0 → Expr 2) w n env Fin.elim0 hw hn (fun i => Fin.elim0 i)

theorem matrix_nullary {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (truth : Bool)
    (w b f n r R : Fin m) (env : Fin 2 → Fin m) (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 2 w env))
    (hr : Derives Γ (PureSyntaxTrace.formulaRow w b f n r))
    (hm : Derives Γ (HornRuleSyntax.matrix (ObjectFormulaSyntax.constantRule (SyntaxAtomSyntax.nullaryTag truth)) w r R env)) :
    Derives Γ (SyntaxAtomSyntax.nullary truth w b f n) := by
  have hg : Derives Γ (graph (PureSyntaxFormulaGraph.head (0 : Fin 2) 1 (input truth)) w env r) := of_eq
    (congrArg (fun e => graph e w env r) (actual_head truth)) (.conjL hm)
  have hs := PureSyntaxFormulaGraph.recover hZ (0 : Fin 2) 1 (input truth) w b f n r env hw hn hr hg
  have hc := Derives.impE (.conjL (input_iff hZ truth w n env hw hn)) (.conjR (.conjR hs))
  have hctx : Derives Γ (SyntaxTermSyntax.contexts w b f) := .conjI
    (mem_subst (eq_symm (.conjL hs)) (environmentNat_at w env hn 0))
    (mem_subst (eq_symm (.conjL (.conjR hs))) (environmentNat_at w env hn 1))
  exact .conjI hctx hc

theorem matrix_sound {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (truth : Bool)
    (w b f n r R : Fin m) (env : Fin 2 → Fin m) (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 2 w env))
    (hr : Derives Γ (PureSyntaxTrace.formulaRow w b f n r))
    (hm : Derives Γ (HornRuleSyntax.matrix (ObjectFormulaSyntax.constantRule (SyntaxAtomSyntax.nullaryTag truth)) w r R env)) :
    Derives Γ (FormulaCodeSyntax.formulaCode w n b f) := by
  have ht := matrix_nullary hZ truth w b f n r R env hw hn hr hm
  exact .impE (.conjR (FormulaCodeKnownAtomic.nullary_iff hZ truth w b f n hw (.conjR ht))) (.conjL ht)

theorem matrix_complete {m} {Γ : Context m} (truth : Bool) (w n r R : Fin m) (env : Fin 2 → Fin m)
    (hn : Derives Γ (environmentNat 2 w env))
    (hc : Derives Γ (SyntaxNodeSyntax.constructor 0 (SyntaxAtomSyntax.nullaryTag truth) w Fin.elim0 n))
    (hr : Derives Γ (PureSyntaxTrace.formulaRow w (env 0) (env 1) n r)) :
    Derives Γ (HornRuleSyntax.matrix (ObjectFormulaSyntax.constantRule (SyntaxAtomSyntax.nullaryTag truth)) w r R env) := by
  have hi : Derives Γ (graph (input truth) w env n) := by
    simpa only [input, List.ofFn_zero] using HornExprForest.constructor_graph 0 (SyntaxAtomSyntax.nullaryTag truth) (Fin.elim0 : Fin 0 → Expr 2) w n env Fin.elim0 (fun i => Fin.elim0 i) hc
  have hg := PureSyntaxFormulaGraph.construct (0 : Fin 2) 1 (input truth) w n r env hn hr hi
  exact .conjI (of_eq (congrArg (fun e => graph e w env r) (actual_head truth).symm) hg)
    (.conjI HornRuleSyntax.truth_proved HornRuleSyntax.truth_proved)

theorem application_complete {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (truth : Bool) (w n r R : Fin m) (env : Fin 2 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 2 w env))
    (hc : Derives Γ (SyntaxNodeSyntax.constructor 0 (SyntaxAtomSyntax.nullaryTag truth) w Fin.elim0 n))
    (hr : Derives Γ (PureSyntaxTrace.formulaRow w (env 0) (env 1) n r)) :
    Derives Γ (HornApplicationSyntax.application (ObjectFormulaSyntax.constantRule (SyntaxAtomSyntax.nullaryTag truth)) w r R) := by
  have hm := matrix_complete truth w n r R env hn hc hr
  have hb := HornExprBounds.intro_environmentBound r env (fun i =>
    HornExprBounds.variable_bound hZ (ObjectFormulaSyntax.constantRule (SyntaxAtomSyntax.nullaryTag truth)).head i
      (PureSyntaxRules.head_variables _ (rule_mem truth) i) w r env hw hn (.conjL hm))
  exact HornApplicationRules.intro_application _ w r R env hn hb hm

theorem application_nullary_sound {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (truth : Bool) (w b f n r R : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (PureSyntaxTrace.formulaRow w b f n r))
    (ha : Derives Γ (HornApplicationSyntax.application (ObjectFormulaSyntax.constantRule (SyntaxAtomSyntax.nullaryTag truth)) w r R)) :
    Derives Γ (SyntaxAtomSyntax.nullary truth w b f n) := by
  let B := HornApplicationSyntax.body (ObjectFormulaSyntax.constantRule (SyntaxAtomSyntax.nullaryTag truth)) w r R
  let Δ := Context.add B (raisedContext 2 Γ)
  apply HornApplicationRules.eliminate_application (ObjectFormulaSyntax.constantRule (SyntaxAtomSyntax.nullaryTag truth)) w r R _ ha
  have hw1 : Derives Δ (omega (old 2 w)) := of_eq (omega_rename w (old 2)) (HornBinderRules.under_body 2 hw B)
  have hr1 : Derives Δ (PureSyntaxTrace.formulaRow (old 2 w) (old 2 b) (old 2 f) (old 2 n) (old 2 r)) := of_eq (PureSyntaxTrace.formulaRow_rename w b f n r (old 2)) (HornBinderRules.under_body 2 hr B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have ht := matrix_nullary (HornBinderRules.zf_body 2 hZ B) truth _ _ _ _ _ _ (slot 2) hw1 (.conjL hB) hr1 (.conjR (.conjR hB))
  exact of_eq (SyntaxAtomSyntax.nullary_rename truth w b f n (old 2)).symm ht

theorem application_sound {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (truth : Bool) (w b f n r R : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (PureSyntaxTrace.formulaRow w b f n r))
    (ha : Derives Γ (HornApplicationSyntax.application (ObjectFormulaSyntax.constantRule (SyntaxAtomSyntax.nullaryTag truth)) w r R)) :
    Derives Γ (FormulaCodeSyntax.formulaCode w n b f) := by
  let B := HornApplicationSyntax.body (ObjectFormulaSyntax.constantRule (SyntaxAtomSyntax.nullaryTag truth)) w r R
  let Δ := Context.add B (raisedContext 2 Γ)
  apply HornApplicationRules.eliminate_application (ObjectFormulaSyntax.constantRule (SyntaxAtomSyntax.nullaryTag truth)) w r R _ ha
  have hw1 : Derives Δ (omega (old 2 w)) := of_eq (omega_rename w (old 2)) (HornBinderRules.under_body 2 hw B)
  have hr1 : Derives Δ (PureSyntaxTrace.formulaRow (old 2 w) (old 2 b) (old 2 f) (old 2 n) (old 2 r)) := of_eq (PureSyntaxTrace.formulaRow_rename w b f n r (old 2)) (HornBinderRules.under_body 2 hr B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have ht := matrix_sound (HornBinderRules.zf_body 2 hZ B) truth _ _ _ _ _ _ (slot 2) hw1 (.conjL hB) hr1 (.conjR (.conjR hB))
  exact of_eq (FormulaCodeSyntax.formulaCode_rename w n b f (old 2)).symm ht

end PPAC.Migration.Internal.PureSyntaxConstantRule
