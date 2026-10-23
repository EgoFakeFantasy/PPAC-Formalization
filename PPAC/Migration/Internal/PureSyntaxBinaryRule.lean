import PPAC.Migration.Internal.PureSyntaxFormulaPremise

/-! 四种原二元连接词的实际规则，子码IH保持全部内部变化上下文。 -/
namespace PPAC.Migration.Internal.PureSyntaxBinaryRule
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax HornBinderSyntax PureSyntaxFormulaInductionSyntax
open SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC.Automation.ObjectHorn (Expr)
open YesMetaZFC.Automation

def input (kind : Fin 4) : Expr 4 := Expr.node (.literal (SyntaxLogicalSyntax.binaryTag kind)) [.var 2, .var 3]
def fields : Fin 2 → Expr 4 := Fin.cases (.var 2) (Fin.cases (.var 3) Fin.elim0)

theorem actual_head (kind : Fin 4) : (ObjectFormulaSyntax.binaryRule (SyntaxLogicalSyntax.binaryTag kind)).head = PureSyntaxFormulaGraph.head (0 : Fin 4) 1 (input kind) := rfl

theorem rule_mem (kind : Fin 4) : ObjectFormulaSyntax.binaryRule (SyntaxLogicalSyntax.binaryTag kind) ∈ PureSyntaxRules.rules := by
  rcases kind with ⟨k, hk⟩
  have hcases : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
  rcases hcases with rfl | rfl | rfl | rfl
  · change ObjectFormulaSyntax.binaryRule 5 ∈ PureSyntaxRules.rules
    simp [PureSyntaxRules.rules, PureSyntaxRules.remaining]
  · change ObjectFormulaSyntax.binaryRule 6 ∈ PureSyntaxRules.rules
    simp [PureSyntaxRules.rules, PureSyntaxRules.remaining]
  · change ObjectFormulaSyntax.binaryRule 7 ∈ PureSyntaxRules.rules
    simp [PureSyntaxRules.rules, PureSyntaxRules.remaining]
  · change ObjectFormulaSyntax.binaryRule 8 ∈ PureSyntaxRules.rules
    simp [PureSyntaxRules.rules, PureSyntaxRules.remaining]

theorem known_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Fin 4) (w b f x y n : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (SyntaxLogicalSyntax.binaryCode kind w x y n)) :
    Derives Γ ((FormulaCodeSyntax.formulaCode w n b f).iff (FormulaCodeBranchSyntax.binaryTypes w b f x y)) := by
  rcases kind with ⟨k, hk⟩
  have hcases : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
  rcases hcases with rfl | rfl | rfl | rfl
  · exact FormulaCodeKnownLogical.binary0_iff hZ w b f x y n hw hc
  · exact FormulaCodeKnownLogical.binary1_iff hZ w b f x y n hw hc
  · exact FormulaCodeKnownLogical.binary2_iff hZ w b f x y n hw hc
  · exact FormulaCodeKnownLogical.binary3_iff hZ w b f x y n hw hc

theorem input_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Fin 4) (w n : Fin m) (env : Fin 4 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 4 w env)) :
    Derives Γ ((graph (input kind) w env n).iff (SyntaxLogicalSyntax.binaryCode kind w (env 2) (env 3) n)) := by
  have hv (i : Fin 4) : Derives Γ (graph (.var i) w env (env i)) := .conjI (environmentNat_at w env hn i) (.eqRefl _)
  exact HornExprConstructor.constructor_iff hZ 2 (SyntaxLogicalSyntax.binaryTag kind) fields w n env (SyntaxAtomSyntax.two (env 2) (env 3)) hw hn
    (fun i => Fin.cases (hv 2) (fun j => Fin.cases (hv 3) (fun z => Fin.elim0 z) j) i)

theorem matrix_sound {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Fin 4) (w b f n r R : Fin m) (env : Fin 4 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 4 w env)) (hi : Derives Γ (allIH w n))
    (hs : Derives Γ (RestrictionSyntax.subset R w)) (hc : Derives Γ (PureSyntaxTrace.closed w R))
    (hr : Derives Γ (PureSyntaxTrace.formulaRow w b f n r))
    (hm : Derives Γ (HornRuleSyntax.matrix (ObjectFormulaSyntax.binaryRule (SyntaxLogicalSyntax.binaryTag kind)) w r R env)) :
    Derives Γ (FormulaCodeSyntax.formulaCode w n b f) := by
  have hg : Derives Γ (graph (PureSyntaxFormulaGraph.head (0 : Fin 4) 1 (input kind)) w env r) := of_eq
    (congrArg (fun e => graph e w env r) (actual_head kind)) (.conjL hm)
  have hfields := PureSyntaxFormulaGraph.recover hZ (0 : Fin 4) 1 (input kind) w b f n r env hw hn hr hg
  have hcode := Derives.impE (.conjL (input_iff hZ kind w n env hw hn)) (.conjR (.conjR hfields))
  have hxless := SyntaxConstructors.child_member hZ 2 (SyntaxLogicalSyntax.binaryTag kind) w (SyntaxAtomSyntax.two (env 2) (env 3)) n 0 hw hcode
  have hyless := SyntaxConstructors.child_member hZ 2 (SyntaxLogicalSyntax.binaryTag kind) w (SyntaxAtomSyntax.two (env 2) (env 3)) n 1 hw hcode
  have hb : Derives Γ (graph (.var (0 : Fin 4)) w env (env 0)) := .conjI (environmentNat_at w env hn 0) (.eqRefl _)
  have hp : Derives Γ (HornRuleSyntax.premise (PureSyntaxFormulaPremise.head (.var (0 : Fin 4)) 1 2) w R env) := .conjL (.conjR (.conjR hm))
  have hq : Derives Γ (HornRuleSyntax.premise (PureSyntaxFormulaPremise.head (.var (0 : Fin 4)) 1 3) w R env) := .conjL (.conjR (.conjR (.conjR hm)))
  have hx := PureSyntaxFormulaPremise.typed_from_induction hZ (.var (0 : Fin 4)) 1 2 w n (env 0) R env hw hn hi hxless hb hs hc hp
  have hy := PureSyntaxFormulaPremise.typed_from_induction hZ (.var (0 : Fin 4)) 1 3 w n (env 0) R env hw hn hi hyless hb hs hc hq
  have hctx : Derives Γ (SyntaxTermSyntax.contexts w (env 0) (env 1)) := .conjI (environmentNat_at w env hn 0) (environmentNat_at w env hn 1)
  have ht := Derives.impE (.conjR (known_iff hZ kind w (env 0) (env 1) (env 2) (env 3) n hw hcode)) (.conjI hctx (.conjI hx hy))
  exact PureSyntaxFormulaGraph.contexts_subst w b f (env 0) (env 1) n (eq_symm (.conjL hfields)) (eq_symm (.conjL (.conjR hfields))) ht

theorem matrix_complete {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Fin 4) (w n r R p q : Fin m) (env : Fin 4 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 4 w env))
    (he : Derives Γ (SyntaxLogicalSyntax.binaryCode kind w (env 2) (env 3) n))
    (hr : Derives Γ (PureSyntaxTrace.formulaRow w (env 0) (env 1) n r))
    (hp : Derives Γ (PureSyntaxTrace.formulaRow w (env 0) (env 1) (env 2) p))
    (hq : Derives Γ (PureSyntaxTrace.formulaRow w (env 0) (env 1) (env 3) q))
    (hpm : Derives Γ (.mem p R)) (hqm : Derives Γ (.mem q R)) :
    Derives Γ (HornRuleSyntax.matrix (ObjectFormulaSyntax.binaryRule (SyntaxLogicalSyntax.binaryTag kind)) w r R env) := by
  have hi := Derives.impE (.conjR (input_iff hZ kind w n env hw hn)) he
  have hg := PureSyntaxFormulaGraph.construct (0 : Fin 4) 1 (input kind) w n r env hn hr hi
  have hb : Derives Γ (graph (.var (0 : Fin 4)) w env (env 0)) := .conjI (environmentNat_at w env hn 0) (.eqRefl _)
  have gp := PureSyntaxFormulaPremise.construct (.var (0 : Fin 4)) 1 2 w (env 0) p env hn hb hp
  have gq := PureSyntaxFormulaPremise.construct (.var (0 : Fin 4)) 1 3 w (env 0) q env hn hb hq
  have pp := Derives.impE (.conjR (HornRuleValue.premise_at hZ _ w R p env hw hn gp)) hpm
  have pq := Derives.impE (.conjR (HornRuleValue.premise_at hZ _ w R q env hw hn gq)) hqm
  exact .conjI (of_eq (congrArg (fun e => graph e w env r) (actual_head kind).symm) hg)
    (.conjI HornRuleSyntax.truth_proved (.conjI pp (.conjI pq HornRuleSyntax.truth_proved)))

theorem application_complete {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Fin 4) (w n r R p q : Fin m) (env : Fin 4 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 4 w env))
    (he : Derives Γ (SyntaxLogicalSyntax.binaryCode kind w (env 2) (env 3) n))
    (hr : Derives Γ (PureSyntaxTrace.formulaRow w (env 0) (env 1) n r))
    (hp : Derives Γ (PureSyntaxTrace.formulaRow w (env 0) (env 1) (env 2) p))
    (hq : Derives Γ (PureSyntaxTrace.formulaRow w (env 0) (env 1) (env 3) q))
    (hpm : Derives Γ (.mem p R)) (hqm : Derives Γ (.mem q R)) :
    Derives Γ (HornApplicationSyntax.application (ObjectFormulaSyntax.binaryRule (SyntaxLogicalSyntax.binaryTag kind)) w r R) := by
  have hm := matrix_complete hZ kind w n r R p q env hw hn he hr hp hq hpm hqm
  have hb := HornExprBounds.intro_environmentBound r env (fun i =>
    HornExprBounds.variable_bound hZ (ObjectFormulaSyntax.binaryRule (SyntaxLogicalSyntax.binaryTag kind)).head i (PureSyntaxRules.head_variables _ (rule_mem kind) i) w r env hw hn (.conjL hm))
  exact HornApplicationRules.intro_application _ w r R env hn hb hm

theorem application_sound {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Fin 4) (w b f n r R : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (allIH w n))
    (hs : Derives Γ (RestrictionSyntax.subset R w)) (hc : Derives Γ (PureSyntaxTrace.closed w R))
    (hr : Derives Γ (PureSyntaxTrace.formulaRow w b f n r))
    (ha : Derives Γ (HornApplicationSyntax.application (ObjectFormulaSyntax.binaryRule (SyntaxLogicalSyntax.binaryTag kind)) w r R)) :
    Derives Γ (FormulaCodeSyntax.formulaCode w n b f) := by
  let B := HornApplicationSyntax.body (ObjectFormulaSyntax.binaryRule (SyntaxLogicalSyntax.binaryTag kind)) w r R
  let Δ := Context.add B (raisedContext 4 Γ)
  apply HornApplicationRules.eliminate_application (ObjectFormulaSyntax.binaryRule (SyntaxLogicalSyntax.binaryTag kind)) w r R _ ha
  have hw1 : Derives Δ (omega (old 4 w)) := of_eq (omega_rename w (old 4)) (HornBinderRules.under_body 4 hw B)
  have hi1 : Derives Δ (allIH (old 4 w) (old 4 n)) := of_eq (allIH_rename w n (old 4)) (HornBinderRules.under_body 4 hi B)
  have hs1 : Derives Δ (RestrictionSyntax.subset (old 4 R) (old 4 w)) := of_eq (RestrictionSyntax.subset_rename R w (old 4)) (HornBinderRules.under_body 4 hs B)
  have hc1 : Derives Δ (PureSyntaxTrace.closed (old 4 w) (old 4 R)) := of_eq (PureSyntaxTrace.closed_rename w R (old 4)) (HornBinderRules.under_body 4 hc B)
  have hr1 : Derives Δ (PureSyntaxTrace.formulaRow (old 4 w) (old 4 b) (old 4 f) (old 4 n) (old 4 r)) := of_eq (PureSyntaxTrace.formulaRow_rename w b f n r (old 4)) (HornBinderRules.under_body 4 hr B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have ht := matrix_sound (HornBinderRules.zf_body 4 hZ B) kind _ _ _ _ _ _ (slot 4) hw1 (.conjL hB) hi1 hs1 hc1 hr1 (.conjR (.conjR hB))
  exact of_eq (FormulaCodeSyntax.formulaCode_rename w n b f (old 4)).symm ht

end PPAC.Migration.Internal.PureSyntaxBinaryRule
