import PPAC.Migration.Internal.PureSyntaxEqualityRule

/-! 原等式完整查询的实际闭轨迹构造；子项／父行编码及公共轨迹见证在对象EX内消去。 -/
namespace PPAC.Migration.Internal.PureSyntaxEqualityComplete
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax
open SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC.Automation

theorem condition_from_rows {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n r p q : Fin m) (env : Fin 4 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 4 w env))
    (he : Derives Γ (SyntaxAtomSyntax.equalCode w (env 2) (env 3) n))
    (hr : Derives Γ (PureSyntaxTrace.formulaRow w (env 0) (env 1) n r))
    (hp : Derives Γ (PureSyntaxTrace.termRow w (env 0) (env 1) (env 2) p))
    (hq : Derives Γ (PureSyntaxTrace.termRow w (env 0) (env 1) (env 3) q))
    (hcp : Derives Γ (PureSyntaxTrace.condition w p)) (hcq : Derives Γ (PureSyntaxTrace.condition w q)) :
    Derives Γ (PureSyntaxTrace.condition w r) := by
  let B := PureSyntaxTraceMerge.pairWitness w.castSucc p.castSucc q.castSucc (Fin.last m)
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) (PureSyntaxTraceMerge.two_conditions hZ w p q hcp hcq)
  have hZ1 := ZFContext.under hZ B
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw B)
  have hn1 : Derives Δ (environmentNat 4 w.castSucc (fun i => (env i).castSucc)) := of_eq (environmentNat_rename 4 w env Fin.castSucc) (under hn B)
  have he1 : Derives Δ (SyntaxAtomSyntax.equalCode w.castSucc (env 2).castSucc (env 3).castSucc n.castSucc) := of_eq (SyntaxAtomSyntax.equalCode_rename _ _ _ _ Fin.castSucc) (under he B)
  have hr1 : Derives Δ (PureSyntaxTrace.formulaRow w.castSucc (env 0).castSucc (env 1).castSucc n.castSucc r.castSucc) := of_eq (PureSyntaxTrace.formulaRow_rename _ _ _ _ _ Fin.castSucc) (under hr B)
  have hp1 : Derives Δ (PureSyntaxTrace.termRow w.castSucc (env 0).castSucc (env 1).castSucc (env 2).castSucc p.castSucc) := of_eq (PureSyntaxTrace.termRow_rename _ _ _ _ _ Fin.castSucc) (under hp B)
  have hq1 : Derives Δ (PureSyntaxTrace.termRow w.castSucc (env 0).castSucc (env 1).castSucc (env 3).castSucc q.castSucc) := of_eq (PureSyntaxTrace.termRow_rename _ _ _ _ _ Fin.castSucc) (under hq B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hm := PureSyntaxEqualityRule.matrix_complete hZ1 _ _ _ _ _ _ _ hw1 hn1 he1 hr1 hp1 hq1 (.conjL (.conjR (.conjR hB))) (.conjR (.conjR (.conjR hB)))
  have ha := PureSyntaxEqualityRule.application_complete hZ1 _ _ _ _ _ _ _ hw1 hn1 he1 hr1 hp1 hq1 (.conjL (.conjR (.conjR hB))) (.conjR (.conjR (.conjR hB)))
  have hnat := HornExprRange.range hZ1 ObjectFormulaSyntax.equalityRule.head w.castSucc r.castSucc (fun i => (env i).castSucc) hw1 hn1 (.conjL hm)
  have hout := PureSyntaxTraceExtension.condition hZ1 w.castSucc (Fin.last m) r.castSucc (.conjL hB) hnat (.conjL (.conjR hB))
    (HornStepSyntax.rule_intro PureSyntaxRules.rules ObjectFormulaSyntax.equalityRule PureSyntaxEqualityRule.rule_mem _ _ _ ha)
  exact of_eq (PureSyntaxTrace.condition_rename w r Fin.castSucc).symm hout

theorem from_rows {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n p q : Fin m) (env : Fin 4 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 4 w env))
    (he : Derives Γ (SyntaxAtomSyntax.equalCode w (env 2) (env 3) n))
    (hp : Derives Γ (PureSyntaxTrace.termRow w (env 0) (env 1) (env 2) p))
    (hq : Derives Γ (PureSyntaxTrace.termRow w (env 0) (env 1) (env 3) q))
    (hcp : Derives Γ (PureSyntaxTrace.condition w p)) (hcq : Derives Γ (PureSyntaxTrace.condition w q)) :
    Derives Γ (PureSyntaxTrace.formula w (env 0) (env 1) n) := by
  have hnn := SyntaxNodeInjective.constructor_range hZ 2 3 w (SyntaxAtomSyntax.two (env 2) (env 3)) n hw he
  have hi := SyntaxForestSyntax.intro_inputs 3 w (SyntaxAtomSyntax.three (env 0) (env 1) n)
    (fun i => Fin.cases (environmentNat_at w env hn 0) (fun j => Fin.cases (environmentNat_at w env hn 1) (fun k => Fin.cases hnn (fun z => Fin.elim0 z) k) j) i)
  let B := (Formula.mem (Fin.last m) w.castSucc).conj (PureSyntaxTrace.formulaRow w.castSucc (env 0).castSucc (env 1).castSucc n.castSucc (Fin.last m))
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) (SyntaxConstructors.exists_constructor hZ 3 4 w (SyntaxAtomSyntax.three (env 0) (env 1) n) hw hi)
  have hZ1 := ZFContext.under hZ B
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw B)
  have hn1 : Derives Δ (environmentNat 4 w.castSucc (fun i => (env i).castSucc)) := of_eq (environmentNat_rename 4 w env Fin.castSucc) (under hn B)
  have he1 : Derives Δ (SyntaxAtomSyntax.equalCode w.castSucc (env 2).castSucc (env 3).castSucc n.castSucc) := of_eq (SyntaxAtomSyntax.equalCode_rename _ _ _ _ Fin.castSucc) (under he B)
  have hp1 : Derives Δ (PureSyntaxTrace.termRow w.castSucc (env 0).castSucc (env 1).castSucc (env 2).castSucc p.castSucc) := of_eq (PureSyntaxTrace.termRow_rename _ _ _ _ _ Fin.castSucc) (under hp B)
  have hq1 : Derives Δ (PureSyntaxTrace.termRow w.castSucc (env 0).castSucc (env 1).castSucc (env 3).castSucc q.castSucc) := of_eq (PureSyntaxTrace.termRow_rename _ _ _ _ _ Fin.castSucc) (under hq B)
  have hcp1 : Derives Δ (PureSyntaxTrace.condition w.castSucc p.castSucc) := of_eq (PureSyntaxTrace.condition_rename w p Fin.castSucc) (under hcp B)
  have hcq1 : Derives Δ (PureSyntaxTrace.condition w.castSucc q.castSucc) := of_eq (PureSyntaxTrace.condition_rename w q Fin.castSucc) (under hcq B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hcond := condition_from_rows hZ1 _ _ _ _ _ _ hw1 hn1 he1 (.conjR hB) hp1 hq1 hcp1 hcq1
  exact of_eq (PureSyntaxTrace.formula_rename w (env 0) (env 1) n Fin.castSucc).symm
    (PureSyntaxFormulaGraph.intro_formula _ _ _ _ _ (.conjR hB) hcond)

theorem checked_equality {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b f h t n : Fin m)
    (hw : Derives Γ (omega w)) (hh : Derives Γ (SyntaxTermSyntax.term w b f h))
    (ht : Derives Γ (SyntaxTermSyntax.term w b f t))
    (hc : Derives Γ (SyntaxAtomSyntax.equalCode w h t n)) :
    Derives Γ (PureSyntaxTrace.formula w b f n) := by
  let env : Fin 4 → Fin m := Fin.cases b (Fin.cases f (Fin.cases h (Fin.cases t Fin.elim0)))
  have hhn := SyntaxTerms.range hZ w b f h hw hh
  have htn := SyntaxTerms.range hZ w b f t hw ht
  have hen : Derives Γ (environmentNat 4 w env) := HornApplicationRules.intro_nat w env
    (fun i => Fin.cases (.conjL (.conjL hh)) (fun j => Fin.cases (.conjR (.conjL hh)) (fun l => Fin.cases hhn (fun v => Fin.cases htn (fun z => Fin.elim0 z) v) l) j) i)
  have hq := PureSyntaxTermCorrectness.checked_complete hZ w b f t hw ht
  have hhead := PureSyntaxTermCorrectness.checked_complete hZ w b f h hw hh
  let P := (PureSyntaxTrace.termRow w.castSucc b.castSucc f.castSucc h.castSucc (Fin.last m)).conj (PureSyntaxTrace.condition w.castSucc (Fin.last m))
  let Δ := Context.add P (Context.image Formula.raise Γ)
  apply Derives.exE (p := P) hhead
  have hP : Derives Δ P := .hyp (Or.inl rfl)
  have hq1 : Derives Δ (PureSyntaxTrace.term w.castSucc b.castSucc f.castSucc t.castSucc) := of_eq (PureSyntaxTrace.term_rename _ _ _ _ Fin.castSucc) (under hq P)
  let Q := (PureSyntaxTrace.termRow w.castSucc.castSucc b.castSucc.castSucc f.castSucc.castSucc t.castSucc.castSucc (Fin.last (m+1))).conj
    (PureSyntaxTrace.condition w.castSucc.castSucc (Fin.last (m+1)))
  let Ξ := Context.add Q (Context.image Formula.raise Δ)
  apply Derives.exE (p := Q) hq1
  have hZ2 := ZFContext.under (ZFContext.under hZ P) Q
  have lift {A : Formula m} (ha : Derives Γ A) : Derives Ξ A.raise.raise := under (under ha P) Q
  have hw2 : Derives Ξ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (lift hw)
  have hn2 : Derives Ξ (environmentNat 4 w.castSucc.castSucc (fun i => (env i).castSucc.castSucc)) := of_eq (by simp only [Formula.raise, environmentNat_rename]) (lift hen)
  have hc2 : Derives Ξ (SyntaxAtomSyntax.equalCode w.castSucc.castSucc h.castSucc.castSucc t.castSucc.castSucc n.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxAtomSyntax.equalCode_rename]) (lift hc)
  have hP1 : Derives Ξ ((PureSyntaxTrace.termRow w.castSucc.castSucc b.castSucc.castSucc f.castSucc.castSucc h.castSucc.castSucc (Fin.last m).castSucc).conj (PureSyntaxTrace.condition w.castSucc.castSucc (Fin.last m).castSucc)) := of_eq
    (by simp only [P, Formula.raise, Formula.rename, PureSyntaxTrace.termRow_rename, PureSyntaxTrace.condition_rename]) (under hP Q)
  have hQ : Derives Ξ Q := .hyp (Or.inl rfl)
  have hout := from_rows hZ2 w.castSucc.castSucc n.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
    (fun i => (env i).castSucc.castSucc) hw2 hn2 hc2 (.conjL hP1) (.conjL hQ) (.conjR hP1) (.conjR hQ)
  exact of_eq (by simp only [Formula.raise, PureSyntaxTrace.formula_rename]; rfl) hout

theorem typed_equality_checked {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b f x y n : Fin m)
    (hw : Derives Γ (omega w)) (ht : Derives Γ (FormulaCodeSyntax.formulaCode w n b f))
    (hc : Derives Γ (SyntaxAtomSyntax.equalCode w x y n)) : Derives Γ (PureSyntaxTrace.formula w b f n) := by
  have htypes := Derives.impE (.conjL (FormulaCodeKnownAtomic.equal_iff hZ w b f x y n hw hc)) ht
  exact checked_equality hZ w b f x y n hw (.conjL htypes) (.conjR htypes) hc

end PPAC.Migration.Internal.PureSyntaxEqualityComplete
