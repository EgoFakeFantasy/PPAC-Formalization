import PPAC.Migration.Internal.PureSyntaxConstantRule

/-! 两种原常量的完整查询实际构造及原局部规则双条件。 -/
namespace PPAC.Migration.Internal.PureSyntaxConstantComplete
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax
open SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC.Automation

theorem application_iff_nullary {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (truth : Bool) (w b f n r R : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (PureSyntaxTrace.formulaRow w b f n r)) :
    Derives Γ ((HornApplicationSyntax.application (ObjectFormulaSyntax.constantRule (SyntaxAtomSyntax.nullaryTag truth)) w r R).iff
      (SyntaxAtomSyntax.nullary truth w b f n)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact PureSyntaxConstantRule.application_nullary_sound (ZFContext.add hZ _) truth w b f n r R (add hw _) (add hr _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    let A := SyntaxAtomSyntax.nullary truth w b f n
    have hA : Derives (Context.add A Γ) A := .hyp (Or.inl rfl)
    let env : Fin 2 → Fin m := Fin.cases b (fun _ => f)
    have hn : Derives (Context.add A Γ) (environmentNat 2 w env) := HornApplicationRules.intro_nat w env
      (fun i => Fin.cases (.conjL (.conjL hA)) (fun j => Fin.cases (.conjR (.conjL hA)) (fun z => Fin.elim0 z) j) i)
    exact PureSyntaxConstantRule.application_complete (ZFContext.add hZ A) truth w n r R env (add hw A) hn (.conjR hA) (add hr A)

theorem checked_nullary {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (truth : Bool) (w b f n : Fin m)
    (hw : Derives Γ (omega w)) (ht : Derives Γ (SyntaxAtomSyntax.nullary truth w b f n)) :
    Derives Γ (PureSyntaxTrace.formula w b f n) := by
  have hn := SyntaxNodeInjective.constructor_range hZ 0 (SyntaxAtomSyntax.nullaryTag truth) w Fin.elim0 n hw (.conjR ht)
  have hi := SyntaxForestSyntax.intro_inputs 3 w (SyntaxAtomSyntax.three b f n)
    (fun i => Fin.cases (.conjL (.conjL ht)) (fun j => Fin.cases (.conjR (.conjL ht)) (fun k => Fin.cases hn (fun z => Fin.elim0 z) k) j) i)
  let B := (Formula.mem (Fin.last m) w.castSucc).conj (PureSyntaxTrace.formulaRow w.castSucc b.castSucc f.castSucc n.castSucc (Fin.last m))
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) (SyntaxConstructors.exists_constructor hZ 3 4 w (SyntaxAtomSyntax.three b f n) hw hi)
  have hZ1 := ZFContext.under hZ B
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw B)
  have ht1 : Derives Δ (SyntaxAtomSyntax.nullary truth w.castSucc b.castSucc f.castSucc n.castSucc) := of_eq (SyntaxAtomSyntax.nullary_rename truth w b f n Fin.castSucc) (under ht B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have ha := Derives.impE (.conjR (application_iff_nullary hZ1 truth w.castSucc b.castSucc f.castSucc n.castSucc (Fin.last m) w.castSucc hw1 (.conjR hB))) ht1
  have hc := PureSyntaxTraceRules.premise_free_condition hZ1 (ObjectFormulaSyntax.constantRule (SyntaxAtomSyntax.nullaryTag truth)) (PureSyntaxConstantRule.rule_mem truth) rfl _ _ (.conjL hB) ha
  exact of_eq (PureSyntaxTrace.formula_rename w b f n Fin.castSucc).symm
    (PureSyntaxFormulaGraph.intro_formula _ _ _ _ _ (.conjR hB) hc)

theorem typed_constant_checked {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (truth : Bool) (w b f n : Fin m)
    (hw : Derives Γ (omega w)) (ht : Derives Γ (FormulaCodeSyntax.formulaCode w n b f))
    (hc : Derives Γ (SyntaxNodeSyntax.constructor 0 (SyntaxAtomSyntax.nullaryTag truth) w Fin.elim0 n)) :
    Derives Γ (PureSyntaxTrace.formula w b f n) :=
  checked_nullary hZ truth w b f n hw (.conjI (.impE (.conjL (FormulaCodeKnownAtomic.nullary_iff hZ truth w b f n hw hc)) ht) hc)

end PPAC.Migration.Internal.PureSyntaxConstantComplete
