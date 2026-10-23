import PPAC.Migration.Internal.PureSyntaxMembershipPremise

/-! 原纯成员关系规则的实际矩阵、有界赋值及全内部局部健全性。 -/
namespace PPAC.Migration.Internal.PureSyntaxMembershipRule
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC.Automation

theorem actual_head : (ObjectFormulaSyntax.relationRule .membership).head = PureSyntaxFormulaGraph.head (0 : Fin 3) 1 PureSyntaxMembershipInput.input := rfl

theorem actual_premises : (ObjectFormulaSyntax.relationRule .membership).premises = [PureSyntaxMembershipPremise.head] := rfl

theorem rule_mem : ObjectFormulaSyntax.relationRule .membership ∈ PureSyntaxRules.rules := by
  simp [PureSyntaxRules.rules, PureSyntaxRules.remaining]

theorem matrix_sound {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b f n r R : Fin m) (env : Fin 3 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 3 w env))
    (hs : Derives Γ (RestrictionSyntax.subset R w)) (hc : Derives Γ (PureSyntaxTrace.closed w R))
    (hr : Derives Γ (PureSyntaxTrace.formulaRow w b f n r))
    (hm : Derives Γ (HornRuleSyntax.matrix (ObjectFormulaSyntax.relationRule .membership) w r R env)) :
    Derives Γ (FormulaCodeSyntax.formulaCode w n b f) := by
  have hg : Derives Γ (graph (PureSyntaxFormulaGraph.head (0 : Fin 3) 1 PureSyntaxMembershipInput.input) w env r) := of_eq
    (congrArg (fun e => graph e w env r) actual_head) (.conjL hm)
  have hfields := PureSyntaxFormulaGraph.recover hZ (0 : Fin 3) 1 PureSyntaxMembershipInput.input w b f n r env hw hn hr hg
  have hd := Derives.impE (.conjL (PureSyntaxMembershipInput.data_iff hZ w n env hw hn)) (.conjR (.conjR hfields))
  have hp : Derives Γ (HornRuleSyntax.premise PureSyntaxMembershipPremise.head w R env) := .conjL (.conjR (.conjR hm))
  have ht := PureSyntaxMembershipType.from_pair_output hZ w (env 0) (env 1) (env 2) n hw hd
    (PureSyntaxMembershipPremise.pair_output hZ w R env hw hn hs hc hp)
  exact PureSyntaxFormulaGraph.contexts_subst w b f (env 0) (env 1) n (eq_symm (.conjL hfields)) (eq_symm (.conjL (.conjR hfields))) ht

theorem matrix_complete {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n r R len p : Fin m) (env : Fin 3 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 3 w env))
    (hd : Derives Γ (PureSyntaxMembershipInput.data w (env 2) n)) (hl : Derives Γ (SyntaxNumeralSyntax.numeral 2 len))
    (hr : Derives Γ (PureSyntaxTrace.formulaRow w (env 0) (env 1) n r))
    (hp : Derives Γ (PureSyntaxTrace.argumentRow w (env 0) (env 1) len (env 2) p)) (hpm : Derives Γ (.mem p R)) :
    Derives Γ (HornRuleSyntax.matrix (ObjectFormulaSyntax.relationRule .membership) w r R env) := by
  have hi := PureSyntaxMembershipInput.graph_of_data w n env hn hd
  have hg := PureSyntaxFormulaGraph.construct (0 : Fin 3) 1 PureSyntaxMembershipInput.input w n r env hn hr hi
  have pp := PureSyntaxMembershipPremise.construct hZ w R len p env hw hn hl hp hpm
  exact .conjI (of_eq (congrArg (fun e => graph e w env r) actual_head.symm) hg)
    (.conjI HornRuleSyntax.truth_proved (.conjI pp HornRuleSyntax.truth_proved))

theorem application_complete {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n r R len p : Fin m) (env : Fin 3 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 3 w env))
    (hd : Derives Γ (PureSyntaxMembershipInput.data w (env 2) n)) (hl : Derives Γ (SyntaxNumeralSyntax.numeral 2 len))
    (hr : Derives Γ (PureSyntaxTrace.formulaRow w (env 0) (env 1) n r))
    (hp : Derives Γ (PureSyntaxTrace.argumentRow w (env 0) (env 1) len (env 2) p)) (hpm : Derives Γ (.mem p R)) :
    Derives Γ (HornApplicationSyntax.application (ObjectFormulaSyntax.relationRule .membership) w r R) := by
  have hm := matrix_complete hZ w n r R len p env hw hn hd hl hr hp hpm
  have hb := HornExprBounds.intro_environmentBound r env (fun i =>
    HornExprBounds.variable_bound hZ (ObjectFormulaSyntax.relationRule .membership).head i (PureSyntaxRules.head_variables _ rule_mem i) w r env hw hn (.conjL hm))
  exact HornApplicationRules.intro_application _ w r R env hn hb hm

theorem application_sound {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b f n r R : Fin m)
    (hw : Derives Γ (omega w)) (hs : Derives Γ (RestrictionSyntax.subset R w)) (hc : Derives Γ (PureSyntaxTrace.closed w R))
    (hr : Derives Γ (PureSyntaxTrace.formulaRow w b f n r))
    (ha : Derives Γ (HornApplicationSyntax.application (ObjectFormulaSyntax.relationRule .membership) w r R)) :
    Derives Γ (FormulaCodeSyntax.formulaCode w n b f) := by
  let B := HornApplicationSyntax.body (ObjectFormulaSyntax.relationRule .membership) w r R
  let Δ := Context.add B (raisedContext 3 Γ)
  apply HornApplicationRules.eliminate_application (ObjectFormulaSyntax.relationRule .membership) w r R _ ha
  have hw1 : Derives Δ (omega (old 3 w)) := of_eq (omega_rename w (old 3)) (HornBinderRules.under_body 3 hw B)
  have hs1 : Derives Δ (RestrictionSyntax.subset (old 3 R) (old 3 w)) := of_eq (RestrictionSyntax.subset_rename R w (old 3)) (HornBinderRules.under_body 3 hs B)
  have hc1 : Derives Δ (PureSyntaxTrace.closed (old 3 w) (old 3 R)) := of_eq (PureSyntaxTrace.closed_rename w R (old 3)) (HornBinderRules.under_body 3 hc B)
  have hr1 : Derives Δ (PureSyntaxTrace.formulaRow (old 3 w) (old 3 b) (old 3 f) (old 3 n) (old 3 r)) := of_eq (PureSyntaxTrace.formulaRow_rename w b f n r (old 3)) (HornBinderRules.under_body 3 hr B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have ht := matrix_sound (HornBinderRules.zf_body 3 hZ B) _ _ _ _ _ _ (slot 3) hw1 (.conjL hB) hs1 hc1 hr1 (.conjR (.conjR hB))
  exact of_eq (FormulaCodeSyntax.formulaCode_rename w n b f (old 3)).symm ht

end PPAC.Migration.Internal.PureSyntaxMembershipRule
