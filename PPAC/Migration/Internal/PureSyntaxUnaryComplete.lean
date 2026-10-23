import PPAC.Migration.Internal.PureSyntaxUnaryRule

/-! 一元公式的实际子轨迹延长及父行存在性，量词体保留内部后继界。 -/
namespace PPAC.Migration.Internal.PureSyntaxUnaryComplete
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax PureSyntaxFormulaInductionSyntax PureSyntaxUnarySyntax
open SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC.Automation

theorem condition_from_row {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Fin 3) (w n r p B : Fin m) (env : Fin 3 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 3 w env))
    (he : Derives Γ (SyntaxLogicalSyntax.singleCode (tag kind) w (env 2) n))
    (hb : Derives Γ (graph (boundExpr (advance kind)) w env B))
    (hr : Derives Γ (PureSyntaxTrace.formulaRow w (env 0) (env 1) n r))
    (hp : Derives Γ (PureSyntaxTrace.formulaRow w B (env 1) (env 2) p))
    (hcp : Derives Γ (PureSyntaxTrace.condition w p)) :
    Derives Γ (PureSyntaxTrace.condition w r) := by
  let A := PureSyntaxTrace.witness w.castSucc p.castSucc (Fin.last m)
  let Δ := Context.add A (Context.image Formula.raise Γ)
  apply Derives.exE (p := A) hcp
  have hZ1 := ZFContext.under hZ A
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw A)
  have hn1 : Derives Δ (environmentNat 3 w.castSucc (fun i => (env i).castSucc)) := of_eq (environmentNat_rename 3 w env Fin.castSucc) (under hn A)
  have hb1 : Derives Δ (graph (boundExpr (advance kind)) w.castSucc (fun i => (env i).castSucc) B.castSucc) := of_eq (graph_rename _ w B env Fin.castSucc) (under hb A)
  have he1 : Derives Δ (SyntaxLogicalSyntax.singleCode (tag kind) w.castSucc (env 2).castSucc n.castSucc) := of_eq (SyntaxLogicalSyntax.singleCode_rename (tag kind) _ _ _ Fin.castSucc) (under he A)
  have hr1 : Derives Δ (PureSyntaxTrace.formulaRow w.castSucc (env 0).castSucc (env 1).castSucc n.castSucc r.castSucc) := of_eq (PureSyntaxTrace.formulaRow_rename _ _ _ _ _ Fin.castSucc) (under hr A)
  have hp1 : Derives Δ (PureSyntaxTrace.formulaRow w.castSucc B.castSucc (env 1).castSucc (env 2).castSucc p.castSucc) := of_eq (PureSyntaxTrace.formulaRow_rename _ _ _ _ _ Fin.castSucc) (under hp A)
  have hA : Derives Δ A := .hyp (Or.inl rfl)
  have hm := PureSyntaxUnaryRule.matrix_complete hZ1 kind _ _ _ _ _ _ _ hw1 hn1 he1 hb1 hr1 hp1 (.conjL (.conjR hA))
  have ha := PureSyntaxUnaryRule.application_complete hZ1 kind _ _ _ _ _ _ _ hw1 hn1 he1 hb1 hr1 hp1 (.conjL (.conjR hA))
  have hnat := HornExprRange.range hZ1 (ObjectFormulaSyntax.unaryRule (tag kind) (advance kind)).head w.castSucc r.castSucc (fun i => (env i).castSucc) hw1 hn1 (.conjL hm)
  have hout := PureSyntaxTraceExtension.condition hZ1 w.castSucc (Fin.last m) r.castSucc (.conjL hA) hnat (.conjR (.conjR hA))
    (HornStepSyntax.rule_intro PureSyntaxRules.rules (ObjectFormulaSyntax.unaryRule (tag kind) (advance kind)) (rule_mem kind) _ _ _ ha)
  exact of_eq (PureSyntaxTrace.condition_rename w r Fin.castSucc).symm hout

theorem from_row {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Fin 3) (w n p B : Fin m) (env : Fin 3 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 3 w env))
    (he : Derives Γ (SyntaxLogicalSyntax.singleCode (tag kind) w (env 2) n))
    (hb : Derives Γ (graph (boundExpr (advance kind)) w env B))
    (hp : Derives Γ (PureSyntaxTrace.formulaRow w B (env 1) (env 2) p))
    (hcp : Derives Γ (PureSyntaxTrace.condition w p)) :
    Derives Γ (PureSyntaxTrace.formula w (env 0) (env 1) n) := by
  have hnn := SyntaxNodeInjective.constructor_range hZ 1 (tag kind) w (fun _ => env 2) n hw he
  have hi := SyntaxForestSyntax.intro_inputs 3 w (SyntaxAtomSyntax.three (env 0) (env 1) n)
    (fun i => Fin.cases (environmentNat_at w env hn 0) (fun j => Fin.cases (environmentNat_at w env hn 1) (fun k => Fin.cases hnn (fun z => Fin.elim0 z) k) j) i)
  let A := (Formula.mem (Fin.last m) w.castSucc).conj (PureSyntaxTrace.formulaRow w.castSucc (env 0).castSucc (env 1).castSucc n.castSucc (Fin.last m))
  let Δ := Context.add A (Context.image Formula.raise Γ)
  apply Derives.exE (p := A) (SyntaxConstructors.exists_constructor hZ 3 4 w (SyntaxAtomSyntax.three (env 0) (env 1) n) hw hi)
  have hZ1 := ZFContext.under hZ A
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw A)
  have hn1 : Derives Δ (environmentNat 3 w.castSucc (fun i => (env i).castSucc)) := of_eq (environmentNat_rename 3 w env Fin.castSucc) (under hn A)
  have hb1 : Derives Δ (graph (boundExpr (advance kind)) w.castSucc (fun i => (env i).castSucc) B.castSucc) := of_eq (graph_rename _ w B env Fin.castSucc) (under hb A)
  have he1 : Derives Δ (SyntaxLogicalSyntax.singleCode (tag kind) w.castSucc (env 2).castSucc n.castSucc) := of_eq (SyntaxLogicalSyntax.singleCode_rename (tag kind) _ _ _ Fin.castSucc) (under he A)
  have hp1 : Derives Δ (PureSyntaxTrace.formulaRow w.castSucc B.castSucc (env 1).castSucc (env 2).castSucc p.castSucc) := of_eq (PureSyntaxTrace.formulaRow_rename _ _ _ _ _ Fin.castSucc) (under hp A)
  have hcp1 : Derives Δ (PureSyntaxTrace.condition w.castSucc p.castSucc) := of_eq (PureSyntaxTrace.condition_rename w p Fin.castSucc) (under hcp A)
  have hA : Derives Δ A := .hyp (Or.inl rfl)
  have hcond := condition_from_row hZ1 kind _ _ _ _ _ _ hw1 hn1 he1 hb1 (.conjR hA) hp1 hcp1
  exact of_eq (PureSyntaxTrace.formula_rename w (env 0) (env 1) n Fin.castSucc).symm
    (PureSyntaxFormulaGraph.intro_formula _ _ _ _ _ (.conjR hA) hcond)

theorem checked_from_child {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Fin 3) (w b f x n B : Fin m)
    (hw : Derives Γ (omega w)) (hctx : Derives Γ (SyntaxTermSyntax.contexts w b f))
    (hb : Derives Γ (graph (boundExpr (advance kind)) w (SyntaxAtomSyntax.three b f x) B))
    (ht : Derives Γ (FormulaCodeSyntax.formulaCode w x B f))
    (hraw : Derives Γ (PureSyntaxTrace.formula w B f x))
    (he : Derives Γ (SyntaxLogicalSyntax.singleCode (tag kind) w x n)) :
    Derives Γ (PureSyntaxTrace.formula w b f n) := by
  let env : Fin 3 → Fin m := SyntaxAtomSyntax.three b f x
  have hxn := Derives.conjL (FormulaCodeProperties.guards w x B f ht)
  have hn : Derives Γ (environmentNat 3 w env) := HornApplicationRules.intro_nat w env
    (fun i => Fin.cases (.conjL hctx) (fun j => Fin.cases (.conjR hctx) (fun k => Fin.cases hxn (fun z => Fin.elim0 z) k) j) i)
  let A := (PureSyntaxTrace.formulaRow w.castSucc B.castSucc f.castSucc x.castSucc (Fin.last m)).conj (PureSyntaxTrace.condition w.castSucc (Fin.last m))
  let Δ := Context.add A (Context.image Formula.raise Γ)
  apply Derives.exE (p := A) hraw
  have hZ1 := ZFContext.under hZ A
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw A)
  have hn1 : Derives Δ (environmentNat 3 w.castSucc (fun i => (env i).castSucc)) := of_eq (environmentNat_rename 3 w env Fin.castSucc) (under hn A)
  have hb1 : Derives Δ (graph (boundExpr (advance kind)) w.castSucc (fun i => (env i).castSucc) B.castSucc) := of_eq (graph_rename _ w B env Fin.castSucc) (under hb A)
  have he1 : Derives Δ (SyntaxLogicalSyntax.singleCode (tag kind) w.castSucc x.castSucc n.castSucc) := of_eq (SyntaxLogicalSyntax.singleCode_rename (tag kind) _ _ _ Fin.castSucc) (under he A)
  have hA : Derives Δ A := .hyp (Or.inl rfl)
  have hout := from_row hZ1 kind w.castSucc n.castSucc (Fin.last m) B.castSucc (fun i => (env i).castSucc) hw1 hn1 he1 hb1 (.conjL hA) (.conjR hA)
  exact of_eq (PureSyntaxTrace.formula_rename w b f n Fin.castSucc).symm hout

theorem checked_from_step {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Fin 3) (w b f x n : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (allIH w n))
    (hctx : Derives Γ (SyntaxTermSyntax.contexts w b f))
    (hs : Derives Γ (FormulaCodeRecursiveSyntax.stepCheck (advance kind) w x b f))
    (he : Derives Γ (SyntaxLogicalSyntax.singleCode (tag kind) w x n)) :
    Derives Γ (PureSyntaxTrace.formula w b f n) := by
  have hl := SyntaxConstructors.child_member hZ 1 (tag kind) w (fun _ => x) n 0 hw he
  cases ha : advance kind with
  | false =>
    have ht : Derives Γ (FormulaCodeSyntax.formulaCode w x b f) := by simpa only [FormulaCodeRecursiveSyntax.stepCheck, ha, Bool.false_eq_true, ↓reduceIte] using hs
    have hr := Derives.impE (.conjR (correct_at w x b f (allIH_at w n x hi hl))) ht
    have hb : Derives Γ (graph (boundExpr (advance kind)) w (SyntaxAtomSyntax.three b f x) b) := by
      have hv : Derives Γ (graph (.var (0 : Fin 3)) w (SyntaxAtomSyntax.three b f x) b) := .conjI (.conjL hctx) (.eqRefl _)
      simpa only [boundExpr, ha, Bool.false_eq_true, ↓reduceIte] using hv
    exact checked_from_child hZ kind w b f x n b hw hctx hb ht hr he
  | true =>
    have hex : Derives Γ (FormulaCodeRecursiveSyntax.advancedCode w x b f) := by simpa only [FormulaCodeRecursiveSyntax.stepCheck, ha, ↓reduceIte] using hs
    let A := (successor (Fin.last m) b.castSucc).conj (FormulaCodeSyntax.formulaCode w.castSucc x.castSucc (Fin.last m) f.castSucc)
    let Δ := Context.add A (Context.image Formula.raise Γ)
    apply Derives.exE (p := A) hex
    have hZ1 := ZFContext.under hZ A
    have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw A)
    have hi1 : Derives Δ (allIH w.castSucc n.castSucc) := of_eq (allIH_rename w n Fin.castSucc) (under hi A)
    have hl1 : Derives Δ (.mem x.castSucc n.castSucc) := under hl A
    have hc1 : Derives Δ (SyntaxTermSyntax.contexts w.castSucc b.castSucc f.castSucc) := of_eq (SyntaxTermSyntax.contexts_rename w b f Fin.castSucc) (under hctx A)
    have he1 : Derives Δ (SyntaxLogicalSyntax.singleCode (tag kind) w.castSucc x.castSucc n.castSucc) := of_eq (SyntaxLogicalSyntax.singleCode_rename (tag kind) _ _ _ Fin.castSucc) (under he A)
    have hA : Derives Δ A := .hyp (Or.inl rfl)
    have hr := Derives.impE (.conjR (correct_at w.castSucc x.castSucc (Fin.last m) f.castSucc (allIH_at w.castSucc n.castSucc x.castSucc hi1 hl1))) (.conjR hA)
    have hv : Derives Δ (graph (.var (0 : Fin 3)) w.castSucc (SyntaxAtomSyntax.three b.castSucc f.castSucc x.castSucc) b.castSucc) := .conjI (.conjL hc1) (.eqRefl _)
    have hb : Derives Δ (graph (boundExpr (advance kind)) w.castSucc (SyntaxAtomSyntax.three b.castSucc f.castSucc x.castSucc) (Fin.last m)) := by
      simpa only [boundExpr, ha, ↓reduceIte] using HornExprSyntax.intro_succ (.var (0 : Fin 3)) w.castSucc (Fin.last m) b.castSucc (SyntaxAtomSyntax.three b.castSucc f.castSucc x.castSucc) hv (.conjL hA)
    have hout := checked_from_child hZ1 kind w.castSucc b.castSucc f.castSucc x.castSucc n.castSucc (Fin.last m) hw1 hc1 hb (.conjR hA) hr he1
    exact of_eq (PureSyntaxTrace.formula_rename w b f n Fin.castSucc).symm hout

theorem typed_unary_checked {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Fin 3) (w b f x n : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (allIH w n))
    (ht : Derives Γ (FormulaCodeSyntax.formulaCode w n b f)) (he : Derives Γ (SyntaxLogicalSyntax.singleCode (tag kind) w x n)) :
    Derives Γ (PureSyntaxTrace.formula w b f n) := by
  have hs := Derives.impE (.conjL (known_iff hZ kind w b f x n hw he)) ht
  exact checked_from_step hZ kind w b f x n hw hi (.conjL hs) (.conjR hs) he

end PPAC.Migration.Internal.PureSyntaxUnaryComplete
