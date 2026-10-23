import PPAC.Migration.Internal.PureSyntaxBinaryRule

/-! 四种二元连接词的实际子查询合并、父行构造及统一IH下完备步骤。 -/
namespace PPAC.Migration.Internal.PureSyntaxBinaryComplete
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax PureSyntaxFormulaInductionSyntax
open SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC.Automation

theorem condition_from_rows {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Fin 4) (w n r p q : Fin m) (env : Fin 4 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 4 w env))
    (he : Derives Γ (SyntaxLogicalSyntax.binaryCode kind w (env 2) (env 3) n))
    (hr : Derives Γ (PureSyntaxTrace.formulaRow w (env 0) (env 1) n r))
    (hp : Derives Γ (PureSyntaxTrace.formulaRow w (env 0) (env 1) (env 2) p))
    (hq : Derives Γ (PureSyntaxTrace.formulaRow w (env 0) (env 1) (env 3) q))
    (hcp : Derives Γ (PureSyntaxTrace.condition w p)) (hcq : Derives Γ (PureSyntaxTrace.condition w q)) :
    Derives Γ (PureSyntaxTrace.condition w r) := by
  let B := PureSyntaxTraceMerge.pairWitness w.castSucc p.castSucc q.castSucc (Fin.last m)
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) (PureSyntaxTraceMerge.two_conditions hZ w p q hcp hcq)
  have hZ1 := ZFContext.under hZ B
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw B)
  have hn1 : Derives Δ (environmentNat 4 w.castSucc (fun i => (env i).castSucc)) := of_eq (environmentNat_rename 4 w env Fin.castSucc) (under hn B)
  have he1 : Derives Δ (SyntaxLogicalSyntax.binaryCode kind w.castSucc (env 2).castSucc (env 3).castSucc n.castSucc) := of_eq (SyntaxLogicalSyntax.binaryCode_rename kind _ _ _ _ Fin.castSucc) (under he B)
  have hr1 : Derives Δ (PureSyntaxTrace.formulaRow w.castSucc (env 0).castSucc (env 1).castSucc n.castSucc r.castSucc) := of_eq (PureSyntaxTrace.formulaRow_rename _ _ _ _ _ Fin.castSucc) (under hr B)
  have hp1 : Derives Δ (PureSyntaxTrace.formulaRow w.castSucc (env 0).castSucc (env 1).castSucc (env 2).castSucc p.castSucc) := of_eq (PureSyntaxTrace.formulaRow_rename _ _ _ _ _ Fin.castSucc) (under hp B)
  have hq1 : Derives Δ (PureSyntaxTrace.formulaRow w.castSucc (env 0).castSucc (env 1).castSucc (env 3).castSucc q.castSucc) := of_eq (PureSyntaxTrace.formulaRow_rename _ _ _ _ _ Fin.castSucc) (under hq B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hm := PureSyntaxBinaryRule.matrix_complete hZ1 kind _ _ _ _ _ _ _ hw1 hn1 he1 hr1 hp1 hq1 (.conjL (.conjR (.conjR hB))) (.conjR (.conjR (.conjR hB)))
  have ha := PureSyntaxBinaryRule.application_complete hZ1 kind _ _ _ _ _ _ _ hw1 hn1 he1 hr1 hp1 hq1 (.conjL (.conjR (.conjR hB))) (.conjR (.conjR (.conjR hB)))
  have hnat := HornExprRange.range hZ1 (ObjectFormulaSyntax.binaryRule (SyntaxLogicalSyntax.binaryTag kind)).head w.castSucc r.castSucc (fun i => (env i).castSucc) hw1 hn1 (.conjL hm)
  have hout := PureSyntaxTraceExtension.condition hZ1 w.castSucc (Fin.last m) r.castSucc (.conjL hB) hnat (.conjL (.conjR hB))
    (HornStepSyntax.rule_intro PureSyntaxRules.rules (ObjectFormulaSyntax.binaryRule (SyntaxLogicalSyntax.binaryTag kind)) (PureSyntaxBinaryRule.rule_mem kind) _ _ _ ha)
  exact of_eq (PureSyntaxTrace.condition_rename w r Fin.castSucc).symm hout

theorem from_rows {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Fin 4) (w n p q : Fin m) (env : Fin 4 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 4 w env))
    (he : Derives Γ (SyntaxLogicalSyntax.binaryCode kind w (env 2) (env 3) n))
    (hp : Derives Γ (PureSyntaxTrace.formulaRow w (env 0) (env 1) (env 2) p))
    (hq : Derives Γ (PureSyntaxTrace.formulaRow w (env 0) (env 1) (env 3) q))
    (hcp : Derives Γ (PureSyntaxTrace.condition w p)) (hcq : Derives Γ (PureSyntaxTrace.condition w q)) :
    Derives Γ (PureSyntaxTrace.formula w (env 0) (env 1) n) := by
  have hnn := SyntaxNodeInjective.constructor_range hZ 2 (SyntaxLogicalSyntax.binaryTag kind) w (SyntaxAtomSyntax.two (env 2) (env 3)) n hw he
  have hi := SyntaxForestSyntax.intro_inputs 3 w (SyntaxAtomSyntax.three (env 0) (env 1) n)
    (fun i => Fin.cases (environmentNat_at w env hn 0) (fun j => Fin.cases (environmentNat_at w env hn 1) (fun k => Fin.cases hnn (fun z => Fin.elim0 z) k) j) i)
  let B := (Formula.mem (Fin.last m) w.castSucc).conj (PureSyntaxTrace.formulaRow w.castSucc (env 0).castSucc (env 1).castSucc n.castSucc (Fin.last m))
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) (SyntaxConstructors.exists_constructor hZ 3 4 w (SyntaxAtomSyntax.three (env 0) (env 1) n) hw hi)
  have hZ1 := ZFContext.under hZ B
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw B)
  have hn1 : Derives Δ (environmentNat 4 w.castSucc (fun i => (env i).castSucc)) := of_eq (environmentNat_rename 4 w env Fin.castSucc) (under hn B)
  have he1 : Derives Δ (SyntaxLogicalSyntax.binaryCode kind w.castSucc (env 2).castSucc (env 3).castSucc n.castSucc) := of_eq (SyntaxLogicalSyntax.binaryCode_rename kind _ _ _ _ Fin.castSucc) (under he B)
  have hp1 : Derives Δ (PureSyntaxTrace.formulaRow w.castSucc (env 0).castSucc (env 1).castSucc (env 2).castSucc p.castSucc) := of_eq (PureSyntaxTrace.formulaRow_rename _ _ _ _ _ Fin.castSucc) (under hp B)
  have hq1 : Derives Δ (PureSyntaxTrace.formulaRow w.castSucc (env 0).castSucc (env 1).castSucc (env 3).castSucc q.castSucc) := of_eq (PureSyntaxTrace.formulaRow_rename _ _ _ _ _ Fin.castSucc) (under hq B)
  have hcp1 : Derives Δ (PureSyntaxTrace.condition w.castSucc p.castSucc) := of_eq (PureSyntaxTrace.condition_rename w p Fin.castSucc) (under hcp B)
  have hcq1 : Derives Δ (PureSyntaxTrace.condition w.castSucc q.castSucc) := of_eq (PureSyntaxTrace.condition_rename w q Fin.castSucc) (under hcq B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hcond := condition_from_rows hZ1 kind _ _ _ _ _ _ hw1 hn1 he1 (.conjR hB) hp1 hq1 hcp1 hcq1
  exact of_eq (PureSyntaxTrace.formula_rename w (env 0) (env 1) n Fin.castSucc).symm
    (PureSyntaxFormulaGraph.intro_formula _ _ _ _ _ (.conjR hB) hcond)

theorem checked_from_children {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Fin 4) (w b f h t n : Fin m)
    (hw : Derives Γ (omega w)) (hh : Derives Γ (FormulaCodeSyntax.formulaCode w h b f))
    (ht : Derives Γ (FormulaCodeSyntax.formulaCode w t b f))
    (hrawx : Derives Γ (PureSyntaxTrace.formula w b f h)) (hrawy : Derives Γ (PureSyntaxTrace.formula w b f t))
    (hc : Derives Γ (SyntaxLogicalSyntax.binaryCode kind w h t n)) :
    Derives Γ (PureSyntaxTrace.formula w b f n) := by
  let env : Fin 4 → Fin m := Fin.cases b (Fin.cases f (Fin.cases h (Fin.cases t Fin.elim0)))
  have hxguards := FormulaCodeProperties.guards w h b f hh
  have hyguards := FormulaCodeProperties.guards w t b f ht
  have hhn := Derives.conjL hxguards
  have htn := Derives.conjL hyguards
  have hctx := Derives.conjR hxguards
  have hen : Derives Γ (environmentNat 4 w env) := HornApplicationRules.intro_nat w env
    (fun i => Fin.cases (.conjL hctx) (fun j => Fin.cases (.conjR hctx) (fun l => Fin.cases hhn (fun v => Fin.cases htn (fun z => Fin.elim0 z) v) l) j) i)
  let P := (PureSyntaxTrace.formulaRow w.castSucc b.castSucc f.castSucc h.castSucc (Fin.last m)).conj (PureSyntaxTrace.condition w.castSucc (Fin.last m))
  let Δ := Context.add P (Context.image Formula.raise Γ)
  apply Derives.exE (p := P) hrawx
  have hP : Derives Δ P := .hyp (Or.inl rfl)
  have hq1 : Derives Δ (PureSyntaxTrace.formula w.castSucc b.castSucc f.castSucc t.castSucc) := of_eq (PureSyntaxTrace.formula_rename _ _ _ _ Fin.castSucc) (under hrawy P)
  let Q := (PureSyntaxTrace.formulaRow w.castSucc.castSucc b.castSucc.castSucc f.castSucc.castSucc t.castSucc.castSucc (Fin.last (m+1))).conj
    (PureSyntaxTrace.condition w.castSucc.castSucc (Fin.last (m+1)))
  let Ξ := Context.add Q (Context.image Formula.raise Δ)
  apply Derives.exE (p := Q) hq1
  have hZ2 := ZFContext.under (ZFContext.under hZ P) Q
  have lift {A : Formula m} (ha : Derives Γ A) : Derives Ξ A.raise.raise := under (under ha P) Q
  have hw2 : Derives Ξ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (lift hw)
  have hn2 : Derives Ξ (environmentNat 4 w.castSucc.castSucc (fun i => (env i).castSucc.castSucc)) := of_eq (by simp only [Formula.raise, environmentNat_rename]) (lift hen)
  have hc2 : Derives Ξ (SyntaxLogicalSyntax.binaryCode kind w.castSucc.castSucc h.castSucc.castSucc t.castSucc.castSucc n.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxLogicalSyntax.binaryCode_rename kind]) (lift hc)
  have hP1 : Derives Ξ ((PureSyntaxTrace.formulaRow w.castSucc.castSucc b.castSucc.castSucc f.castSucc.castSucc h.castSucc.castSucc (Fin.last m).castSucc).conj (PureSyntaxTrace.condition w.castSucc.castSucc (Fin.last m).castSucc)) := of_eq
    (by simp only [P, Formula.raise, Formula.rename, PureSyntaxTrace.formulaRow_rename, PureSyntaxTrace.condition_rename]) (under hP Q)
  have hQ : Derives Ξ Q := .hyp (Or.inl rfl)
  have hout := from_rows hZ2 kind w.castSucc.castSucc n.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
    (fun i => (env i).castSucc.castSucc) hw2 hn2 hc2 (.conjL hP1) (.conjL hQ) (.conjR hP1) (.conjR hQ)
  exact of_eq (by simp only [Formula.raise, PureSyntaxTrace.formula_rename]; rfl) hout

theorem typed_binary_checked {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Fin 4) (w b f x y n : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (allIH w n))
    (ht : Derives Γ (FormulaCodeSyntax.formulaCode w n b f)) (hc : Derives Γ (SyntaxLogicalSyntax.binaryCode kind w x y n)) :
    Derives Γ (PureSyntaxTrace.formula w b f n) := by
  have hp := Derives.impE (.conjL (PureSyntaxBinaryRule.known_iff hZ kind w b f x y n hw hc)) ht
  have hx := Derives.conjL (.conjR hp)
  have hy := Derives.conjR (.conjR hp)
  have hxless := SyntaxConstructors.child_member hZ 2 (SyntaxLogicalSyntax.binaryTag kind) w (SyntaxAtomSyntax.two x y) n 0 hw hc
  have hyless := SyntaxConstructors.child_member hZ 2 (SyntaxLogicalSyntax.binaryTag kind) w (SyntaxAtomSyntax.two x y) n 1 hw hc
  have hrawx := Derives.impE (.conjR (correct_at w x b f (allIH_at w n x hi hxless))) hx
  have hrawy := Derives.impE (.conjR (correct_at w y b f (allIH_at w n y hi hyless))) hy
  exact checked_from_children hZ kind w b f x y n hw hx hy hrawx hrawy hc

end PPAC.Migration.Internal.PureSyntaxBinaryComplete
