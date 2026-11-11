import PPAC.Migration.ForcingDensityCode
import PPAC.Migration.ForcingCodeUnary
import PPAC.Migration.InternalProofImplication
import PPAC.Migration.InternalProofBackground

/-! The source nullary cases use the actual forcing compilation and its
mixed output. The OpenAI falsum density branch needs the exact same falsum
in the density witness; the native truth constant uses original axiom 7. -/
namespace PPAC.Migration.ForcingSourceDensityConstant
open Internal Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax HornExprSyntax
open SyntaxRenameQuerySyntax (of_eq)
open FormulaCodeSyntax (formulaCode formulaCode_rename)
open SyntaxMixedFormulaJudgmentSyntax (substituted substituted_rename)
open SyntaxNodeSyntax (constructor constructor_rename)
open InternalProofBackground (implication implication_rename)
open YesMetaZFC.Automation

set_option maxRecDepth 16384

private abbrev test : Formula 1 := OriginalAxiomCodeTest.test false

private abbrev constant {m} (truth : Bool) (w N : Fin m) : Formula m :=
  constructor 0 (SyntaxAtomSyntax.nullaryTag truth) w Fin.elim0 N

private theorem constant_rename {m l} (truth : Bool) (w N : Fin m) (ρ : Fin m → Fin l) :
    (constant truth w N).rename ρ = constant truth (ρ w) (ρ N) := by
  rw [constructor_rename]
  rfl

private theorem constant_subst {m} {Γ : Context m} (truth : Bool) (w N M : Fin m)
    (he : Derives Γ (.equal N M)) (hc : Derives Γ (constant truth w N)) :
    Derives Γ (constant truth w M) := by
  let P := constant truth w.castSucc (Fin.last m)
  exact of_eq (by simp only [P, Formula.instantiate, constant_rename, Fin.lastCases_last,
      Fin.lastCases_castSucc, id_eq])
    (.eqSubst P he (of_eq (by simp only [P, Formula.instantiate, constant_rename, Fin.lastCases_last,
      Fin.lastCases_castSucc, id_eq]) hc))

/-- The source compiler's exact constant code survives the actual mixed query. -/
theorem output_code {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (truth : Bool)
    (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z a A B C f j n N b d L S Q : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (formulaCode w n a z))
    (hA : Derives Γ (successor A a)) (hB : Derives Γ (successor B A)) (hC : Derives Γ (successor C B))
    (hc : Derives Γ (constant truth w n))
    (hN : Derives Γ (ForcingCodeRecursion.compiled R H w z f j a n N))
    (hQ : Derives Γ (substituted w L S a f b d N Q)) : Derives Γ ((Formula.equal N n).conj (.equal Q n)) := by
  have hEq := ForcingCodeUnary.nullary hZ truth R H w z f j a A B C n N hw hn hA hB hC hc hN
  have hConst := constant_subst truth w n N (eq_symm hEq) hc
  have hq := SyntaxMixedFormulaNullary.unique hZ truth w L S a f b d N Q hw hConst hQ
  exact .conjI hEq (eq_trans hq hEq)

private theorem truth_proof {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z b F : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hF : Derives Γ (formulaCode w F z b)) (hc : Derives Γ (constant true w F)) :
    Derives Γ (InternalProofConjunction.proved test w z b F) := by
  let t : ObjectTreeTemplate.Template 1 := .leaf 1
  let env : Fin 1 → Fin m := fun _ => b
  have ht := FormulaCodeProperties.guards w F z b hF
  have hg : Derives Γ (graph t.expr w env F) :=
    HornExprForest.constructor_graph 0 1 Fin.elim0 w F env Fin.elim0 (fun i => Fin.elim0 i) hc
  have ha : ObjectLogicalAxiom.prop 7 0 t.expr ∈ ObjectLogicalAxiom.shapes := by
    change ObjectLogicalAxiom.rule7 ∈ ObjectLogicalAxiom.shapes
    simp only [ObjectLogicalAxiom.shapes, List.mem_cons, or_true, true_or]
  exact InternalProofTemplates.template_axiom hZ test 7 t (Or.inr rfl) ha w z F env
    hw hz (.conjR ht) (.conjI (.conjR (.conjR ht)) HornRuleSyntax.truth_proved)
    HornRuleSyntax.truth_proved (fun i hi => by
      simp [t, ObjectTreeTemplate.Template.expr, ObjectHorn.Expr.node, ObjectHorn.Expr.list,
        ObjectHorn.Expr.variables] at hi) hg

private theorem truth_implication {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z b G F : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hG : Derives Γ (formulaCode w G z b)) (hF : Derives Γ (formulaCode w F z b))
    (hc : Derives Γ (constant true w F)) : Derives Γ (implication test w z b G F) := by
  let E := (Formula.mem (Fin.last m) w.castSucc).conj
    (FormulaCodeConstructSyntax.typedAt 2 7 w.castSucc (SyntaxAtomSyntax.two G.castSucc F.castSucc)
      (Fin.last m) z.castSucc b.castSucc)
  let Δ := Context.add E (Context.image Formula.raise Γ)
  have he := FormulaCodeConstruct.exists_of_fiber 2 7 w (SyntaxAtomSyntax.two G F) z b
    (FormulaCodeConstructors.binary2 hZ w z b G F hw
      (.conjI (.conjR (FormulaCodeProperties.guards w G z b hG)) (.conjI hG hF)))
  apply Derives.exE (p := E) (of_eq (by simp only [FormulaCodeConstructSyntax.typedExists,
    E, SyntaxAtomSyntax.two_map]) he)
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have hI := Derives.conjL (Derives.conjR hE)
  have hZ1 := ZFContext.under hZ E
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw E)
  have hz1 := of_eq (empty_rename z Fin.castSucc) (under hz E)
  have hG1 := of_eq (formulaCode_rename w G z b Fin.castSucc) (under hG E)
  have hF1 := of_eq (formulaCode_rename w F z b Fin.castSucc) (under hF E)
  have hc1 := of_eq (constant_rename true w F Fin.castSucc) (under hc E)
  have hp := InternalProofImplication.weaken_proof hZ1 test w.castSucc z.castSucc b.castSucc G.castSucc
    F.castSucc (Fin.last m) hw1 hz1 hG1 hF1 hI (truth_proof hZ1 w.castSucc z.castSucc b.castSucc F.castSucc
      hw1 hz1 hF1 hc1)
  simp only [Formula.raise, implication_rename]
  apply Derives.exI (Fin.last m)
  exact of_eq (by simp only [Formula.instantiate, Formula.rename, constructor_rename, SyntaxAtomSyntax.two_map,
    InternalProofConjunction.proved_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI hI hp)

/-- Close the native truth case under the actual conditional proof background.
The generated proof works at arbitrary internal target free scopes. -/
theorem truth_from_compiler {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z a A B C f j n N b L S Q G : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) (hn : Derives Γ (formulaCode w n a z))
    (hA : Derives Γ (successor A a)) (hB : Derives Γ (successor B A)) (hC : Derives Γ (successor C B))
    (hc : Derives Γ (constant true w n))
    (hN : Derives Γ (ForcingCodeRecursion.compiled R H w z f j a n N))
    (hQ : Derives Γ (substituted w L S a f z b N Q)) (hG : Derives Γ (formulaCode w G z b)) :
    Derives Γ (implication test w z b G Q) := by
  have hOut := output_code hZ true R H w z a A B C f j n N z b L S Q hw hn hA hB hC hc hN hQ
  exact truth_implication hZ w z b G Q hw hz hG
    (SyntaxMixedFormulaJudgment.target_type w L S a f z b N Q hQ)
    (constant_subst true w n Q (eq_symm (.conjR hOut)) hc)


def falseWitnessData {k m} (R : Source.Formula (k+2))
    (w a A B f j N z b L S D E : Fin m) : Formula m :=
  (ForcingDensityCode.nullaryTrace R w a A B f j N D).conj (substituted w L S a f z b D E)

theorem falseWitnessData_rename {k m l} (R : Source.Formula (k+2))
    (w a A B f j N z b L S D E : Fin m) (ρ : Fin m → Fin l) :
    (falseWitnessData R w a A B f j N z b L S D E).rename ρ =
      falseWitnessData R (ρ w) (ρ a) (ρ A) (ρ B) (ρ f) (ρ j) (ρ N) (ρ z) (ρ b)
        (ρ L) (ρ S) (ρ D) (ρ E) := by
  simp only [falseWitnessData, Formula.rename, ForcingDensityCode.nullaryTrace_rename, substituted_rename]

def falseWitness {k m} (R : Source.Formula (k+2)) (w a A B f j N z b L S : Fin m) : Formula m :=
  existsMany 2 (falseWitnessData R (old 2 w) (old 2 a) (old 2 A) (old 2 B) (old 2 f) (old 2 j)
    (old 2 N) (old 2 z) (old 2 b) (old 2 L) (old 2 S) (slot 2 0) (slot 2 1))

theorem falseWitness_rename {k m l} (R : Source.Formula (k+2)) (w a A B f j N z b L S : Fin m)
    (ρ : Fin m → Fin l) :
    (falseWitness R w a A B f j N z b L S).rename ρ =
      falseWitness R (ρ w) (ρ a) (ρ A) (ρ B) (ρ f) (ρ j) (ρ N) (ρ z) (ρ b) (ρ L) (ρ S) := by
  simp only [falseWitness, existsMany_rename, falseWitnessData_rename, lift_old, lift_slot]

/-- Generate the actual false-density query, retaining the exact falsum
code in its witness body. The remaining proof step instantiates at p. -/
theorem false_from_compiler {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z a A B C f j n N b L S Q : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (formulaCode w n a z))
    (hA : Derives Γ (successor A a)) (hB : Derives Γ (successor B A)) (hC : Derives Γ (successor C B))
    (hf : Derives Γ (SyntaxNumeralSyntax.numeral (k+2) f)) (hj : Derives Γ (SyntaxNumeralSyntax.numeral (k+1) j))
    (hc : Derives Γ (constant false w n))
    (hN : Derives Γ (ForcingCodeRecursion.compiled R H w z f j a n N))
    (hQ : Derives Γ (substituted w L S a f z b N Q))
    (hTables : Derives Γ (SyntaxMixedImageCodeSyntax.termLists w a f z b L S)) :
    Derives Γ ((Formula.equal Q n).conj (falseWitness R w a A B f j N z b L S)) := by
  have he := output_code hZ false R H w z a A B C f j n N z b L S Q hw hn hA hB hC hc hN hQ
  have hConst := constant_subst false w n N (eq_symm (.conjL he)) hc
  have hType := Derives.impE (.conjR (FormulaCodeKnownAtomic.nullary_iff hZ false w a f N hw hConst))
    (.conjI (.conjL (Derives.conjL hTables)) (.conjL (Derives.conjR hTables)))
  apply Derives.conjI (.conjR he)
  let P := ForcingDensityCode.queryData R (old 2 w) (old 2 a) (old 2 A) (old 2 B) (old 2 f)
    (old 2 j) (old 2 N) (old 2 z) (old 2 b) (old 2 L) (old 2 S) (slot 2 0) (slot 2 1)
  let Δ := Context.add P (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 P _ (ForcingDensityCode.from_tables hZ R w a A B f j N z b L S hw hA hB hf hj hType hTables)
  have hP : Derives Δ P := .hyp (Or.inl rfl)
  have hTrace := ForcingDensityCode.nullary_trace (HornBinderRules.zf_body 2 hZ P) false R
    (old 2 w) (old 2 a) (old 2 A) (old 2 B) (old 2 f) (old 2 j) (old 2 N) (slot 2 0)
    (of_eq (omega_rename w (old 2)) (HornBinderRules.under_body 2 hw P))
    (of_eq (constant_rename false w N (old 2)) (HornBinderRules.under_body 2 hConst P)) (.conjL hP)
  apply of_eq (falseWitness_rename R w a A B f j N z b L S (old 2)).symm
  apply HornBinderRules.intro_many 2 _ (slot 2)
  exact of_eq (by simp only [falseWitnessData_rename, assign_old, assign_slot]; rfl)
    (.conjI hTrace (.conjR hP) : Derives Δ
      (falseWitnessData R (old 2 w) (old 2 a) (old 2 A) (old 2 B) (old 2 f) (old 2 j) (old 2 N)
        (old 2 z) (old 2 b) (old 2 L) (old 2 S) (slot 2 0) (slot 2 1)))

def truthInput {k m} (R : Source.Formula (k+2)) (H : Source.Formula (k+1))
    (w z a A B C f j n N b L S Q G : Fin m) : Formula m :=
  (omega w).conj ((empty z).conj ((formulaCode w n a z).conj ((successor A a).conj
    ((successor B A).conj ((successor C B).conj ((constant true w n).conj
      ((ForcingCodeRecursion.compiled R H w z f j a n N).conj ((substituted w L S a f z b N Q).conj
        (formulaCode w G z b)))))))))

def truthSentence {k m} (R : Source.Formula (k+2)) (H : Source.Formula (k+1))
    (w z a A B C f j n N b L S Q G : Fin m) : Source.Sentence :=
  ((truthInput R H w z a A B C f j n N b L S Q G).imp (implication test w z b G Q)).close

theorem truth_kernel_certificate {k m} (R : Source.Formula (k+2)) (H : Source.Formula (k+1))
    (w z a A B C f j n N b L S Q G : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence
      (truthSentence R H w z a A B C f j n N b L S Q G)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  let P := truthInput R H w z a A B C f j n N b L S Q G
  have hp : Derives (Context.add P (SetLanguage.ZF.at m)) P := .hyp (Or.inl rfl)
  have h2 := Derives.conjR hp
  have h3 := Derives.conjR h2
  have h4 := Derives.conjR h3
  have h5 := Derives.conjR h4
  have h6 := Derives.conjR h5
  have h7 := Derives.conjR h6
  have h8 := Derives.conjR h7
  have h9 := Derives.conjR h8
  exact truth_from_compiler (ZFContext.add (ZFContext.source_ZF m) P) R H w z a A B C f j n N b L S Q G
    (.conjL hp) (.conjL h2) (.conjL h3) (.conjL h4) (.conjL h5) (.conjL h6)
    (.conjL h7) (.conjL h8) (.conjL h9) (.conjR h9)

end PPAC.Migration.ForcingSourceDensityConstant
