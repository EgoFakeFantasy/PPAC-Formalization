import PPAC.Migration.Internal.PureSyntaxMembershipRule

/-! 成员父查询由实际长度2参数查询构造，编码行及轨迹见证在对象EX内消去。 -/
namespace PPAC.Migration.Internal.PureSyntaxMembershipQuery
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax
open SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC.Automation

theorem condition_from_row {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n r len p : Fin m) (env : Fin 3 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 3 w env))
    (hd : Derives Γ (PureSyntaxMembershipInput.data w (env 2) n)) (hl : Derives Γ (SyntaxNumeralSyntax.numeral 2 len))
    (hr : Derives Γ (PureSyntaxTrace.formulaRow w (env 0) (env 1) n r))
    (hp : Derives Γ (PureSyntaxTrace.argumentRow w (env 0) (env 1) len (env 2) p))
    (hc : Derives Γ (PureSyntaxTrace.condition w p)) : Derives Γ (PureSyntaxTrace.condition w r) := by
  let B := PureSyntaxTrace.witness w.castSucc p.castSucc (Fin.last m)
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) hc
  have hZ1 := ZFContext.under hZ B
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw B)
  have hn1 : Derives Δ (environmentNat 3 w.castSucc (fun i => (env i).castSucc)) := of_eq (environmentNat_rename 3 w env Fin.castSucc) (under hn B)
  have hd1 : Derives Δ (PureSyntaxMembershipInput.data w.castSucc (env 2).castSucc n.castSucc) := of_eq (PureSyntaxMembershipInput.data_rename _ _ _ Fin.castSucc) (under hd B)
  have hl1 : Derives Δ (SyntaxNumeralSyntax.numeral 2 len.castSucc) := of_eq (SyntaxNumeralSyntax.numeral_rename 2 len Fin.castSucc) (under hl B)
  have hr1 : Derives Δ (PureSyntaxTrace.formulaRow w.castSucc (env 0).castSucc (env 1).castSucc n.castSucc r.castSucc) := of_eq (PureSyntaxTrace.formulaRow_rename _ _ _ _ _ Fin.castSucc) (under hr B)
  have hp1 : Derives Δ (PureSyntaxTrace.argumentRow w.castSucc (env 0).castSucc (env 1).castSucc len.castSucc (env 2).castSucc p.castSucc) := of_eq (PureSyntaxTrace.argumentRow_rename _ _ _ _ _ _ Fin.castSucc) (under hp B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hm := PureSyntaxMembershipRule.matrix_complete hZ1 _ _ _ _ _ _ _ hw1 hn1 hd1 hl1 hr1 hp1 (.conjL (.conjR hB))
  have ha := PureSyntaxMembershipRule.application_complete hZ1 _ _ _ _ _ _ _ hw1 hn1 hd1 hl1 hr1 hp1 (.conjL (.conjR hB))
  have hnat := HornExprRange.range hZ1 (ObjectFormulaSyntax.relationRule .membership).head w.castSucc r.castSucc (fun i => (env i).castSucc) hw1 hn1 (.conjL hm)
  have hout := PureSyntaxTraceExtension.condition hZ1 w.castSucc (Fin.last m) r.castSucc (.conjL hB) hnat (.conjR (.conjR hB))
    (HornStepSyntax.rule_intro PureSyntaxRules.rules (ObjectFormulaSyntax.relationRule .membership) PureSyntaxMembershipRule.rule_mem _ _ _ ha)
  exact of_eq (PureSyntaxTrace.condition_rename w r Fin.castSucc).symm hout

theorem from_row {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n len p : Fin m) (env : Fin 3 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 3 w env))
    (hd : Derives Γ (PureSyntaxMembershipInput.data w (env 2) n)) (hl : Derives Γ (SyntaxNumeralSyntax.numeral 2 len))
    (hp : Derives Γ (PureSyntaxTrace.argumentRow w (env 0) (env 1) len (env 2) p))
    (hc : Derives Γ (PureSyntaxTrace.condition w p)) : Derives Γ (PureSyntaxTrace.formula w (env 0) (env 1) n) := by
  have hnn := HornExprRange.range hZ PureSyntaxMembershipInput.input w n env hw hn (PureSyntaxMembershipInput.graph_of_data w n env hn hd)
  have hi := SyntaxForestSyntax.intro_inputs 3 w (SyntaxAtomSyntax.three (env 0) (env 1) n)
    (fun i => Fin.cases (environmentNat_at w env hn 0) (fun j => Fin.cases (environmentNat_at w env hn 1) (fun k => Fin.cases hnn (fun z => Fin.elim0 z) k) j) i)
  let B := (Formula.mem (Fin.last m) w.castSucc).conj (PureSyntaxTrace.formulaRow w.castSucc (env 0).castSucc (env 1).castSucc n.castSucc (Fin.last m))
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) (SyntaxConstructors.exists_constructor hZ 3 4 w (SyntaxAtomSyntax.three (env 0) (env 1) n) hw hi)
  have hZ1 := ZFContext.under hZ B
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw B)
  have hn1 : Derives Δ (environmentNat 3 w.castSucc (fun i => (env i).castSucc)) := of_eq (environmentNat_rename 3 w env Fin.castSucc) (under hn B)
  have hd1 : Derives Δ (PureSyntaxMembershipInput.data w.castSucc (env 2).castSucc n.castSucc) := of_eq (PureSyntaxMembershipInput.data_rename _ _ _ Fin.castSucc) (under hd B)
  have hl1 : Derives Δ (SyntaxNumeralSyntax.numeral 2 len.castSucc) := of_eq (SyntaxNumeralSyntax.numeral_rename 2 len Fin.castSucc) (under hl B)
  have hp1 : Derives Δ (PureSyntaxTrace.argumentRow w.castSucc (env 0).castSucc (env 1).castSucc len.castSucc (env 2).castSucc p.castSucc) := of_eq (PureSyntaxTrace.argumentRow_rename _ _ _ _ _ _ Fin.castSucc) (under hp B)
  have hc1 : Derives Δ (PureSyntaxTrace.condition w.castSucc p.castSucc) := of_eq (PureSyntaxTrace.condition_rename w p Fin.castSucc) (under hc B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hcond := condition_from_row hZ1 _ _ _ _ _ _ hw1 hn1 hd1 hl1 (.conjR hB) hp1 hc1
  exact of_eq (PureSyntaxTrace.formula_rename w (env 0) (env 1) n Fin.castSucc).symm
    (PureSyntaxFormulaGraph.intro_formula _ _ _ _ _ (.conjR hB) hcond)

theorem checked_from_list {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b f args n len : Fin m)
    (hw : Derives Γ (omega w)) (hl : Derives Γ (SyntaxNumeralSyntax.numeral 2 len))
    (ht : Derives Γ (SyntaxMixedImageCodeSyntax.termList w len b f args))
    (hd : Derives Γ (PureSyntaxMembershipInput.data w args n)) : Derives Γ (PureSyntaxTrace.formula w b f n) := by
  let env : Fin 3 → Fin m := SyntaxAtomSyntax.three b f args
  have hbn := Derives.conjL (.conjL (.conjR ht))
  have hfn := Derives.conjR (.conjL (.conjR ht))
  have han := Derives.conjL (.conjL (.conjR (.conjR ht)))
  have hen : Derives Γ (environmentNat 3 w env) := HornApplicationRules.intro_nat w env
    (fun i => Fin.cases hbn (fun j => Fin.cases hfn (fun k => Fin.cases han (fun z => Fin.elim0 z) k) j) i)
  have hq := PureSyntaxArgumentInduction.checked_complete hZ w b f len args hw ht
  let B := (PureSyntaxTrace.argumentRow w.castSucc b.castSucc f.castSucc len.castSucc args.castSucc (Fin.last m)).conj (PureSyntaxTrace.condition w.castSucc (Fin.last m))
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) hq
  have hZ1 := ZFContext.under hZ B
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw B)
  have hn1 : Derives Δ (environmentNat 3 w.castSucc (fun i => (env i).castSucc)) := of_eq (environmentNat_rename 3 w env Fin.castSucc) (under hen B)
  have hd1 : Derives Δ (PureSyntaxMembershipInput.data w.castSucc args.castSucc n.castSucc) := of_eq (PureSyntaxMembershipInput.data_rename _ _ _ Fin.castSucc) (under hd B)
  have hl1 : Derives Δ (SyntaxNumeralSyntax.numeral 2 len.castSucc) := of_eq (SyntaxNumeralSyntax.numeral_rename 2 len Fin.castSucc) (under hl B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hout := from_row hZ1 w.castSucc n.castSucc len.castSucc (Fin.last m) (fun i => (env i).castSucc) hw1 hn1 hd1 hl1 (.conjL hB) (.conjR hB)
  exact of_eq (PureSyntaxTrace.formula_rename w b f n Fin.castSucc).symm hout

end PPAC.Migration.Internal.PureSyntaxMembershipQuery
