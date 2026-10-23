import PPAC.Migration.Internal.PureSyntaxUnarySyntax

/-! 否定及两种量词的原规则传输；量词体绑定界由对象后继图给出。 -/
namespace PPAC.Migration.Internal.PureSyntaxUnaryRule
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax HornBinderSyntax PureSyntaxFormulaInductionSyntax PureSyntaxUnarySyntax
open SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC.Automation.ObjectHorn (Expr)
open YesMetaZFC.Automation

theorem matrix_sound {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Fin 3) (w b f n r R : Fin m) (env : Fin 3 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 3 w env)) (hi : Derives Γ (allIH w n))
    (hs : Derives Γ (RestrictionSyntax.subset R w)) (hc : Derives Γ (PureSyntaxTrace.closed w R))
    (hr : Derives Γ (PureSyntaxTrace.formulaRow w b f n r))
    (hm : Derives Γ (HornRuleSyntax.matrix (ObjectFormulaSyntax.unaryRule (tag kind) (advance kind)) w r R env)) :
    Derives Γ (FormulaCodeSyntax.formulaCode w n b f) := by
  have hg : Derives Γ (graph (PureSyntaxFormulaGraph.head (0 : Fin 3) 1 (input kind)) w env r) := of_eq
    (congrArg (fun e => graph e w env r) (actual_head kind)) (.conjL hm)
  have hfields := PureSyntaxFormulaGraph.recover hZ (0 : Fin 3) 1 (input kind) w b f n r env hw hn hr hg
  have hcode := Derives.impE (.conjL (input_iff hZ kind w n env hw hn)) (.conjR (.conjR hfields))
  have hxless := SyntaxConstructors.child_member hZ 1 (tag kind) w (fun _ => env 2) n 0 hw hcode
  have hp : Derives Γ (HornRuleSyntax.premise (PureSyntaxFormulaPremise.head (boundExpr (advance kind)) 1 2) w R env) := .conjL (.conjR (.conjR hm))
  have hx := step_from_premise hZ (advance kind) w n R env hw hn hi hxless hs hc hp
  have hctx : Derives Γ (SyntaxTermSyntax.contexts w (env 0) (env 1)) := .conjI (environmentNat_at w env hn 0) (environmentNat_at w env hn 1)
  have ht := Derives.impE (.conjR (known_iff hZ kind w (env 0) (env 1) (env 2) n hw hcode)) (.conjI hctx hx)
  exact PureSyntaxFormulaGraph.contexts_subst w b f (env 0) (env 1) n (eq_symm (.conjL hfields)) (eq_symm (.conjL (.conjR hfields))) ht

theorem matrix_complete {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Fin 3) (w n r R B p : Fin m) (env : Fin 3 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 3 w env))
    (he : Derives Γ (SyntaxLogicalSyntax.singleCode (tag kind) w (env 2) n))
    (hb : Derives Γ (graph (boundExpr (advance kind)) w env B))
    (hr : Derives Γ (PureSyntaxTrace.formulaRow w (env 0) (env 1) n r))
    (hp : Derives Γ (PureSyntaxTrace.formulaRow w B (env 1) (env 2) p))
    (hpm : Derives Γ (.mem p R)) :
    Derives Γ (HornRuleSyntax.matrix (ObjectFormulaSyntax.unaryRule (tag kind) (advance kind)) w r R env) := by
  have hi := Derives.impE (.conjR (input_iff hZ kind w n env hw hn)) he
  have hg := PureSyntaxFormulaGraph.construct (0 : Fin 3) 1 (input kind) w n r env hn hr hi
  have gp := PureSyntaxFormulaPremise.construct (boundExpr (advance kind)) 1 2 w B p env hn hb hp
  have pp := Derives.impE (.conjR (HornRuleValue.premise_at hZ _ w R p env hw hn gp)) hpm
  exact .conjI (of_eq (congrArg (fun e => graph e w env r) (actual_head kind).symm) hg)
    (.conjI HornRuleSyntax.truth_proved (.conjI pp HornRuleSyntax.truth_proved))

theorem application_complete {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Fin 3) (w n r R B p : Fin m) (env : Fin 3 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 3 w env))
    (he : Derives Γ (SyntaxLogicalSyntax.singleCode (tag kind) w (env 2) n))
    (hb : Derives Γ (graph (boundExpr (advance kind)) w env B))
    (hr : Derives Γ (PureSyntaxTrace.formulaRow w (env 0) (env 1) n r))
    (hp : Derives Γ (PureSyntaxTrace.formulaRow w B (env 1) (env 2) p))
    (hpm : Derives Γ (.mem p R)) :
    Derives Γ (HornApplicationSyntax.application (ObjectFormulaSyntax.unaryRule (tag kind) (advance kind)) w r R) := by
  have hm := matrix_complete hZ kind w n r R B p env hw hn he hb hr hp hpm
  have hb := HornExprBounds.intro_environmentBound r env (fun i =>
    HornExprBounds.variable_bound hZ (ObjectFormulaSyntax.unaryRule (tag kind) (advance kind)).head i (PureSyntaxRules.head_variables _ (rule_mem kind) i) w r env hw hn (.conjL hm))
  exact HornApplicationRules.intro_application _ w r R env hn hb hm

theorem application_sound {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Fin 3) (w b f n r R : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (allIH w n))
    (hs : Derives Γ (RestrictionSyntax.subset R w)) (hc : Derives Γ (PureSyntaxTrace.closed w R))
    (hr : Derives Γ (PureSyntaxTrace.formulaRow w b f n r))
    (ha : Derives Γ (HornApplicationSyntax.application (ObjectFormulaSyntax.unaryRule (tag kind) (advance kind)) w r R)) :
    Derives Γ (FormulaCodeSyntax.formulaCode w n b f) := by
  let B := HornApplicationSyntax.body (ObjectFormulaSyntax.unaryRule (tag kind) (advance kind)) w r R
  let Δ := Context.add B (raisedContext 3 Γ)
  apply HornApplicationRules.eliminate_application (ObjectFormulaSyntax.unaryRule (tag kind) (advance kind)) w r R _ ha
  have hw1 : Derives Δ (omega (old 3 w)) := of_eq (omega_rename w (old 3)) (HornBinderRules.under_body 3 hw B)
  have hi1 : Derives Δ (allIH (old 3 w) (old 3 n)) := of_eq (allIH_rename w n (old 3)) (HornBinderRules.under_body 3 hi B)
  have hs1 : Derives Δ (RestrictionSyntax.subset (old 3 R) (old 3 w)) := of_eq (RestrictionSyntax.subset_rename R w (old 3)) (HornBinderRules.under_body 3 hs B)
  have hc1 : Derives Δ (PureSyntaxTrace.closed (old 3 w) (old 3 R)) := of_eq (PureSyntaxTrace.closed_rename w R (old 3)) (HornBinderRules.under_body 3 hc B)
  have hr1 : Derives Δ (PureSyntaxTrace.formulaRow (old 3 w) (old 3 b) (old 3 f) (old 3 n) (old 3 r)) := of_eq (PureSyntaxTrace.formulaRow_rename w b f n r (old 3)) (HornBinderRules.under_body 3 hr B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have ht := matrix_sound (HornBinderRules.zf_body 3 hZ B) kind _ _ _ _ _ _ (slot 3) hw1 (.conjL hB) hi1 hs1 hc1 hr1 (.conjR (.conjR hB))
  exact of_eq (FormulaCodeSyntax.formulaCode_rename w n b f (old 3)).symm ht

end PPAC.Migration.Internal.PureSyntaxUnaryRule
