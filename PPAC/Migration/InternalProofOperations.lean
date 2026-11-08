import PPAC.Migration.InternalMPProof
import PPAC.Migration.Internal.SyntaxTopFormulaTyping

/-! Concrete consumers of the original logical/forall/strengthening/substitution
rules. Inputs are actual axiom queries or existing typed syntax operations and
actual child Node/header predicates. Every parent payload and Node/Root trace
is constructed. No new checker, proof kernel, or syntax-operation backend.
These are target proof operations, not uniform forcing-preservation or Con. -/
namespace PPAC.Migration.InternalProofOperations
open Internal Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax HornExprSyntax
open SyntaxRenameQuerySyntax (of_eq)
open FormulaCodeSyntax (formulaCode formulaCode_rename)
open YesMetaZFC.Automation
open ProofTreeBranchConstruction (shape)
set_option maxRecDepth 16384

private theorem args3_map {m l} (a b c : Fin m) (r : Fin m → Fin l) :
    (fun i => r (SetLanguage.args3 a b c i)) = SetLanguage.args3 (r a) (r b) (r c) := by
  funext i
  exact Fin.cases rfl (fun i => Fin.cases rfl (fun i => Fin.cases rfl (fun x => Fin.elim0 x) i) i) i
private def five {m} (a b c d e : Fin m) : Fin 5 → Fin m := Fin.cases a (Fin.cases b (Fin.cases c (SyntaxAtomSyntax.two d e)))
private theorem five_map {m l} (a b c d e : Fin m) (r : Fin m → Fin l) :
    (fun i => r (five a b c d e i)) = five (r a) (r b) (r c) (r d) (r e) := by
  funext i
  exact Fin.cases rfl (fun i => Fin.cases rfl (fun i => Fin.cases rfl (fun i => Fin.cases rfl (fun i => Fin.cases rfl (fun x => Fin.elim0 x) i) i) i) i) i

/-- The unchanged original payload and accepted Node/header, with genuine Root
closure when its original free-context field is empty. -/
def result {m} (test : Formula 1) (kind : Fin 6) (w z code : Fin m) (env : Fin ((shape kind).extra+2) → Fin m) : Formula m :=
  (Formula.mem code w).conj ((SyntaxNodeSyntax.constructor ((shape kind).extra+2) (shape kind).tag w env code).conj
    ((InternalMPProof.annotated test w z (env 0) (env 1) code).conj
      ((empty (env 0)).imp (ProofTreeEntrySyntax.root test w code (env 1)))))
theorem result_rename {m l} (test : Formula 1) (kind : Fin 6) (w z code : Fin m) (env : Fin ((shape kind).extra+2) → Fin m) (r : Fin m → Fin l) :
    (result test kind w z code env).rename r = result test kind (r w) (r z) (r code) (fun i => r (env i)) := by
  simp only [result, Formula.rename, SyntaxNodeSyntax.constructor_rename, InternalMPProof.annotated_rename, empty_rename, ProofTreeEntryFacts.root_rename]
def existsResult {m} (test : Formula 1) (kind : Fin 6) (w z : Fin m) (env : Fin ((shape kind).extra+2) → Fin m) : Formula m := .ex
  (result test kind w.castSucc z.castSucc (Fin.last m) (fun i => (env i).castSucc))
theorem existsResult_rename {m l} (test : Formula 1) (kind : Fin 6) (w z : Fin m) (env : Fin ((shape kind).extra+2) → Fin m) (r : Fin m → Fin l) :
    (existsResult test kind w z env).rename r = existsResult test kind (r w) (r z) (fun i => r (env i)) := by
  simp only [existsResult, Formula.rename, result_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

private theorem header_one {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Fin 6) (w code : Fin m)
    (env : Fin ((shape kind).extra+2) → Fin m) (hw : Derives Γ (omega w))
    (hc : Derives Γ (SyntaxNodeSyntax.constructor ((shape kind).extra+2) (shape kind).tag w env code)) :
    Derives Γ (ProofSubstitutionProjectionSyntax.atOne w code (env 1)) := by
  let T := (Formula.mem (Fin.last m) w.castSucc).conj (SyntaxNumeralSyntax.numeral 1 (Fin.last m))
  let Δ := Context.add T (Context.image Formula.raise Γ)
  apply Derives.exE (p := T) (SyntaxNumerals.exists_numeral hZ 1 w hw)
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  have hc1 := of_eq (SyntaxNodeSyntax.constructor_rename ((shape kind).extra+2) (shape kind).tag w env code Fin.castSucc) (under hc T)
  have hf := RawCodeFieldAtConstructor.constructor_at (ZFContext.under hZ T) ((shape kind).extra+2) (shape kind).tag w.castSucc (fun i => (env i).castSucc) code.castSucc 1 (Fin.last m) (env 1).castSucc
    (of_eq (omega_rename w Fin.castSucc) (under hw T)) hc1 (.conjR hT)
  have ho := ProofSubstitutionProjectionSyntax.intro_atOne w.castSucc code.castSucc (env 1).castSucc (Fin.last m) (.conjR hT) (.impE (.conjR hf) (.eqRefl _))
  exact of_eq (ProofSubstitutionProjectionSyntax.atOne_rename w code (env 1) Fin.castSucc).symm ho

private theorem package {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1) (kind : Fin 6) (w z code : Fin m)
    (env : Fin ((shape kind).extra+2) → Fin m) (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hn : Derives Γ (environmentNat ((shape kind).extra+2) w env))
    (hc : Derives Γ (SyntaxNodeSyntax.constructor ((shape kind).extra+2) (shape kind).tag w env code))
    (hp : Derives Γ (ProofTreeEntrySyntax.node test w code)) : Derives Γ (result test kind w z code env) := by
  have hf := Derives.impE (.conjR (RawCodeFieldAtConstructor.constructor_at hZ ((shape kind).extra+2) (shape kind).tag w env code 0 z (env 0) hw hc hz)) (.eqRefl _)
  have ha : Derives Γ (InternalMPProof.annotated test w z (env 0) (env 1) code) := .conjI hp (.conjI hf (header_one hZ kind w code env hw hc))
  have hr : Derives Γ ((empty (env 0)).imp (ProofTreeEntrySyntax.root test w code (env 1))) := by
    apply Derives.impI
    exact ProofTreeRootBackward.matrix_backward test (ZFContext.add hZ _) kind w code (env 1) env (add hw _) (add hp _)
      (.conjI (add hn _) (.conjI (add hc _) (.conjI (.hyp (Or.inl rfl)) (.eqRefl _))))
  exact .conjI (ProofTreeConstructorFacts.range hZ _ _ w code env hw hc) (.conjI hc (.conjI ha hr))

def logicalInput {m} (w z b F c : Fin m) : Formula m :=
  (formulaCode w F z b).conj ((Formula.mem c w).conj (OriginalLogicalExprQuery.rowQuery 3 0 w (SetLanguage.args3 b c F)))
theorem logicalInput_rename {m l} (w z b F c : Fin m) (r : Fin m → Fin l) :
    (logicalInput w z b F c).rename r = logicalInput (r w) (r z) (r b) (r F) (r c) := by
  simp only [logicalInput, Formula.rename, formulaCode_rename, OriginalLogicalExprQuery.rowQuery_rename, args3_map]
private theorem logical_natural {m} {Γ : Context m} (w z b F c : Fin m) (hi : Derives Γ (logicalInput w z b F c)) :
    Derives Γ (environmentNat 3 w (SetLanguage.args3 b F c)) := by
  have hg := FormulaCodeProperties.guards w F z b (.conjL hi)
  exact .conjI (.conjR (.conjR hg)) (.conjI (.conjL hg) (.conjI (.conjL (.conjR hi)) HornRuleSyntax.truth_proved))
private theorem logical_payload {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1) (w z b F c code : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) (hi : Derives Γ (logicalInput w z b F c))
    (hc : Derives Γ (SyntaxNodeSyntax.constructor 3 0 w (SetLanguage.args3 b F c) code)) :
    Derives Γ (result test 0 w z code (SetLanguage.args3 b F c)) := by
  let env := SetLanguage.args3 b F c
  have hn := logical_natural w z b F c hi
  have hq := Derives.impE (.conjR (ProofLogicalQueries.query_constructor_iff hZ w env hw hn)) (.conjR (.conjR hi))
  have hh := Derives.impE (.conjR (ProofLogicalQueries.head_iff hZ w code env hw hn)) hc
  have hb := ProofLogicalQueries.all_assignment_bounds hZ w code env hw hn hh
  have hm : Derives Γ (ProofLogicalNodeSyntax.boundedMatrix w code env) := .conjI hn (.conjI hb (.conjI hh hq))
  have he : Derives Γ (ProofLogicalNodeSyntax.node w code) := by
    apply HornBinderRules.intro_many 3 (ProofLogicalNodeSyntax.body w code) env
    exact of_eq (by simp only [ProofLogicalNodeSyntax.body, ProofLogicalNodeSyntax.boundedMatrix, Formula.rename,
      environmentNat_rename, HornExprBounds.environmentBound_rename, graph_rename, ProofLogicalSyntax.bundle,
      OriginalLogicalExprQuery.query_rename, assign_old, assign_slot]) hm
  have ht := Derives.impE (.conjR (ProofAllNodes.raw_table_iff test w code)) (.disjL he)
  have hp := ProofTreeNodeBackward.matrix_backward test hZ 0 w code env hw ht (.conjI hn (.conjI hc HornRuleSyntax.truth_proved))
  exact package hZ test 0 w z code env hw hz hn hc hp

def strengtheningInput {m} (test : Formula 1) (w z b B F N p : Fin m) : Formula m :=
  (successor B b).conj ((WeakenFreeProgramSyntax.executed w z b B F N).conj
    ((Formula.mem p w).conj (InternalMPProof.annotated test w z B N p)))
theorem strengtheningInput_rename {m l} (test : Formula 1) (w z b B F N p : Fin m) (r : Fin m → Fin l) :
    (strengtheningInput test w z b B F N p).rename r = strengtheningInput test (r w) (r z) (r b) (r B) (r F) (r N) (r p) := by
  simp only [strengtheningInput, Formula.rename, successor_rename, WeakenFreeProgramSyntax.executed_rename, InternalMPProof.annotated_rename]
private theorem strengthening_natural {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1) (w z b B F N p : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (strengtheningInput test w z b B F N p)) : Derives Γ (environmentNat 3 w (SetLanguage.args3 b F p)) := by
  have ht := WeakenFreeProgramValue.source_type hZ w z b B F N hw (.conjL (.conjR hi))
  have hg := FormulaCodeProperties.guards w F z b ht
  exact .conjI (.conjR (.conjR hg)) (.conjI (.conjL hg) (.conjI (.conjL (.conjR (.conjR hi))) HornRuleSyntax.truth_proved))
private theorem strengthening_payload {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1) (w z b B F N p code : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) (hi : Derives Γ (strengtheningInput test w z b B F N p))
    (hc : Derives Γ (SyntaxNodeSyntax.constructor 3 4 w (SetLanguage.args3 b F p) code)) :
    Derives Γ (result test 4 w z code (SetLanguage.args3 b F p)) := by
  have hF := WeakenFreeProgramValue.source_type hZ w z b B F N hw (.conjL (.conjR hi))
  have hN := WeakenFreeProgramValue.target_type hZ w z b B F N hw (.conjL (.conjR hi))
  have hn3 := strengthening_natural hZ test w z b B F N p hw hi
  let env : Fin 4 → Fin m := Fin.lastCases N (SetLanguage.args3 b F p)
  have hn : Derives Γ (environmentNat 4 w env) := .conjI (.conjR (.conjR (FormulaCodeProperties.guards w F z b hF)))
    (.conjI (.conjL (FormulaCodeProperties.guards w F z b hF)) (.conjI (.conjL (.conjR (.conjR hi))) (.conjI (.conjL (FormulaCodeProperties.guards w N z B hN)) HornRuleSyntax.truth_proved)))
  let exprs : Fin 3 → ObjectHorn.Expr 4 := fun i => .var i.castSucc
  have hh : Derives Γ (graph ObjectProofNode.strengtheningShape.head w env code) := by
    change Derives Γ (graph (.node (.literal 4) (List.ofFn exprs)) w env code)
    exact HornExprForest.constructor_graph 3 4 exprs w code env (SetLanguage.args3 b F p)
      (fun i => of_eq (by simp only [exprs, graph, env, Fin.lastCases_castSucc]) (.conjI (environmentNat_at w env hn i.castSucc) (.eqRefl (SetLanguage.args3 b F p i)))) hc
  have hAnn : Derives Γ (InternalMPProof.annotated test w z B N p) := .conjR (.conjR (.conjR hi))
  have ha : Derives Γ (ProofStrengtheningSyntax.atSuccessor w z B env) :=
    .conjI hF (.conjI (.conjL (.conjR hAnn)) (.conjI (.conjR (.conjR hAnn)) (.conjL (.conjR hi))))
  have hs := ProofStrengtheningSyntax.intro_specification w z B env (.conjL hi) ha
  have hm : Derives Γ (ProofStrengtheningNodeSyntax.specificationMatrix w z code env) := .conjI hn (.conjI hh hs)
  have he : Derives Γ (ProofStrengtheningNodeSyntax.specification w z code) := by
    apply HornBinderRules.intro_many 4 (ProofStrengtheningNodeSyntax.specificationBody w z code) env
    exact of_eq (by simp only [ProofStrengtheningNodeSyntax.specificationBody, ProofStrengtheningNodeSyntax.specificationMatrix_rename, assign_old, assign_slot]) hm
  have ht := Derives.impE (.conjR (ProofAllNodes.table_iff test hZ w z code hw hz)) (.disjR (.disjR (.disjR (.disjR (.disjL he)))))
  have hp : Derives Γ (ProofTreeEntrySyntax.node test w code) := ProofTreeNodeBackward.matrix_backward test hZ 4 w code (SetLanguage.args3 b F p) hw ht
    (.conjI hn3 (.conjI hc (.conjI (.conjL (.conjR (.conjR (.conjR hi)))) HornRuleSyntax.truth_proved)))
  exact package hZ test 4 w z code (SetLanguage.args3 b F p) hw hz hn3 hc hp

def substitutionInput {m} (test : Formula 1) (w z b a L F N p : Fin m) : Formula m :=
  (FreeSubstProgramSyntax.executed w z a b L N F).conj ((Formula.mem p w).conj (InternalMPProof.annotated test w z a N p))
theorem substitutionInput_rename {m l} (test : Formula 1) (w z b a L F N p : Fin m) (r : Fin m → Fin l) :
    (substitutionInput test w z b a L F N p).rename r = substitutionInput test (r w) (r z) (r b) (r a) (r L) (r F) (r N) (r p) := by
  simp only [substitutionInput, Formula.rename, FreeSubstProgramSyntax.executed_rename, InternalMPProof.annotated_rename]
private theorem arguments_natural {m} {Γ : Context m} (w a b L : Fin m) (hl : Derives Γ (SyntaxFreeSubstSyntax.termList w a b L)) : Derives Γ (.mem L w) := by
  let T := SyntaxFreeSubstSyntax.listBody w a b L
  let Δ := Context.add T (Context.image Formula.raise Γ)
  apply Derives.exE (p := T) hl
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  exact .conjL (.conjL (.conjL hT))
private theorem substitution_natural {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1) (w z b a L F N p : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (substitutionInput test w z b a L F N p)) :
    Derives Γ (environmentNat 5 w (five b F a L p)) := by
  have hN := FreeSubstProgramValue.source_type hZ w z a b L N F hw (.conjL hi)
  have hF := FreeSubstProgramValue.target_type hZ w z a b L N F hw (.conjL hi)
  have hgF := FormulaCodeProperties.guards w F z b hF
  have hgN := FormulaCodeProperties.guards w N z a hN
  exact .conjI (.conjR (.conjR hgF)) (.conjI (.conjL hgF) (.conjI (.conjR (.conjR hgN))
    (.conjI (arguments_natural w a b L (.conjL (.conjL hi))) (.conjI (.conjL (.conjR hi)) HornRuleSyntax.truth_proved))))
private theorem substitution_payload {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1) (w z b a L F N p code : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) (hi : Derives Γ (substitutionInput test w z b a L F N p))
    (hc : Derives Γ (SyntaxNodeSyntax.constructor 5 5 w (five b F a L p) code)) :
    Derives Γ (result test 5 w z code (five b F a L p)) := by
  have hN := FreeSubstProgramValue.source_type hZ w z a b L N F hw (.conjL hi)
  have hn5 := substitution_natural hZ test w z b a L F N p hw hi
  let env : Fin 6 → Fin m := Fin.lastCases N (five b F a L p)
  have hn : Derives Γ (environmentNat 6 w env) := by
    have hnNat := Derives.conjL (FormulaCodeProperties.guards w N z a hN)
    exact .conjI (.conjL hn5) (.conjI (.conjL (.conjR hn5)) (.conjI (.conjL (.conjR (.conjR hn5)))
      (.conjI (.conjL (.conjR (.conjR (.conjR hn5)))) (.conjI (.conjL (.conjR (.conjR (.conjR (.conjR hn5))))) (.conjI hnNat HornRuleSyntax.truth_proved)))))
  let exprs : Fin 5 → ObjectHorn.Expr 6 := fun i => .var i.castSucc
  have hh : Derives Γ (graph ObjectProofNode.substitutionShape.head w env code) := by
    change Derives Γ (graph (.node (.literal 5) (List.ofFn exprs)) w env code)
    exact HornExprForest.constructor_graph 5 5 exprs w code env (five b F a L p)
      (fun i => of_eq (by simp only [exprs, graph, env, Fin.lastCases_castSucc]) (.conjI (environmentNat_at w env hn i.castSucc) (.eqRefl (five b F a L p i)))) hc
  have hAnn : Derives Γ (InternalMPProof.annotated test w z a N p) := .conjR (.conjR hi)
  have hs : Derives Γ (ProofSubstitutionAllQueries.specification w z env) :=
    .conjI (.conjI hN (.conjL hi)) (.conjI (.conjL (.conjR hAnn)) (.conjR (.conjR hAnn)))
  have hm : Derives Γ (ProofSubstitutionNodeSyntax.specificationMatrix w z code env) := .conjI hn (.conjI hh hs)
  have he : Derives Γ (ProofSubstitutionNodeSyntax.specification w z code) := by
    apply HornBinderRules.intro_many 6 (ProofSubstitutionNodeSyntax.specificationBody w z code) env
    exact of_eq (by simp only [ProofSubstitutionNodeSyntax.specificationBody, ProofSubstitutionNodeSyntax.specificationMatrix_rename, assign_old, assign_slot]) hm
  have ht := Derives.impE (.conjR (ProofAllNodes.table_iff test hZ w z code hw hz)) (.disjR (.disjR (.disjR (.disjR (.disjR (.disjL he))))))
  have hp := ProofTreeNodeBackward.matrix_backward test hZ 5 w code (five b F a L p) hw ht
    (.conjI hn5 (.conjI hc (.conjI (.conjL (.conjR (.conjR hi))) HornRuleSyntax.truth_proved)))
  exact package hZ test 5 w z code (five b F a L p) hw hz hn5 hc hp

theorem logical {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1) (w z b F c : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) (hi : Derives Γ (logicalInput w z b F c)) :
    Derives Γ (existsResult test 0 w z (SetLanguage.args3 b F c)) := by
  have hn := logical_natural w z b F c hi
  have hinputs := SyntaxForestSyntax.intro_inputs 3 w (SetLanguage.args3 b F c) (environmentNat_at w (SetLanguage.args3 b F c) hn)
  let T := (Formula.mem (Fin.last m) w.castSucc).conj (SyntaxNodeSyntax.constructor 3 0 w.castSucc (SetLanguage.args3 b.castSucc F.castSucc c.castSucc) (Fin.last m))
  let Δ := Context.add T (Context.image Formula.raise Γ)
  have hex : Derives Γ (.ex T) := of_eq (by simp only [T, SyntaxNodeSyntax.existsConstructor, args3_map])
    (SyntaxConstructors.exists_constructor hZ 3 0 w (SetLanguage.args3 b F c) hw hinputs)
  apply Derives.exE (p := T) hex
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  have hr := logical_payload (ZFContext.under hZ T) test w.castSucc z.castSucc b.castSucc F.castSucc c.castSucc (Fin.last m)
    (of_eq (omega_rename w Fin.castSucc) (under hw T)) (of_eq (empty_rename z Fin.castSucc) (under hz T))
    (of_eq (logicalInput_rename w z b F c Fin.castSucc) (under hi T)) (.conjR hT)
  have ho : Derives Δ (existsResult test 0 w.castSucc z.castSucc (SetLanguage.args3 b.castSucc F.castSucc c.castSucc)) := by
    apply Derives.exI (Fin.last m)
    exact of_eq (by simp only [Formula.instantiate, result_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hr
  have he := (existsResult_rename test 0 w z (SetLanguage.args3 b F c) Fin.castSucc).trans
    (congrArg (existsResult test 0 w.castSucc z.castSucc) (args3_map b F c Fin.castSucc))
  exact of_eq he.symm ho

theorem strengthening {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1) (w z b B F N p : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) (hi : Derives Γ (strengtheningInput test w z b B F N p)) :
    Derives Γ (existsResult test 4 w z (SetLanguage.args3 b F p)) := by
  have hn := strengthening_natural hZ test w z b B F N p hw hi
  have hinputs := SyntaxForestSyntax.intro_inputs 3 w (SetLanguage.args3 b F p) (environmentNat_at w (SetLanguage.args3 b F p) hn)
  let T := (Formula.mem (Fin.last m) w.castSucc).conj (SyntaxNodeSyntax.constructor 3 4 w.castSucc (SetLanguage.args3 b.castSucc F.castSucc p.castSucc) (Fin.last m))
  let Δ := Context.add T (Context.image Formula.raise Γ)
  have hex : Derives Γ (.ex T) := of_eq (by simp only [T, SyntaxNodeSyntax.existsConstructor, args3_map])
    (SyntaxConstructors.exists_constructor hZ 3 4 w (SetLanguage.args3 b F p) hw hinputs)
  apply Derives.exE (p := T) hex
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  have hr := strengthening_payload (ZFContext.under hZ T) test w.castSucc z.castSucc b.castSucc B.castSucc F.castSucc N.castSucc p.castSucc (Fin.last m)
    (of_eq (omega_rename w Fin.castSucc) (under hw T)) (of_eq (empty_rename z Fin.castSucc) (under hz T))
    (of_eq (strengtheningInput_rename test w z b B F N p Fin.castSucc) (under hi T)) (.conjR hT)
  have ho : Derives Δ (existsResult test 4 w.castSucc z.castSucc (SetLanguage.args3 b.castSucc F.castSucc p.castSucc)) := by
    apply Derives.exI (Fin.last m)
    exact of_eq (by simp only [Formula.instantiate, result_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hr
  have he := (existsResult_rename test 4 w z (SetLanguage.args3 b F p) Fin.castSucc).trans
    (congrArg (existsResult test 4 w.castSucc z.castSucc) (args3_map b F p Fin.castSucc))
  exact of_eq he.symm ho

theorem substitution {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1) (w z b a L F N p : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) (hi : Derives Γ (substitutionInput test w z b a L F N p)) :
    Derives Γ (existsResult test 5 w z (five b F a L p)) := by
  have hn := substitution_natural hZ test w z b a L F N p hw hi
  have hinputs := SyntaxForestSyntax.intro_inputs 5 w (five b F a L p) (environmentNat_at w (five b F a L p) hn)
  let T := (Formula.mem (Fin.last m) w.castSucc).conj (SyntaxNodeSyntax.constructor 5 5 w.castSucc (five b.castSucc F.castSucc a.castSucc L.castSucc p.castSucc) (Fin.last m))
  let Δ := Context.add T (Context.image Formula.raise Γ)
  have hex : Derives Γ (.ex T) := of_eq (by simp only [T, SyntaxNodeSyntax.existsConstructor, five_map])
    (SyntaxConstructors.exists_constructor hZ 5 5 w (five b F a L p) hw hinputs)
  apply Derives.exE (p := T) hex
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  have hr := substitution_payload (ZFContext.under hZ T) test w.castSucc z.castSucc b.castSucc a.castSucc L.castSucc F.castSucc N.castSucc p.castSucc (Fin.last m)
    (of_eq (omega_rename w Fin.castSucc) (under hw T)) (of_eq (empty_rename z Fin.castSucc) (under hz T))
    (of_eq (substitutionInput_rename test w z b a L F N p Fin.castSucc) (under hi T)) (.conjR hT)
  have ho : Derives Δ (existsResult test 5 w.castSucc z.castSucc (five b.castSucc F.castSucc a.castSucc L.castSucc p.castSucc)) := by
    apply Derives.exI (Fin.last m)
    exact of_eq (by simp only [Formula.instantiate, result_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hr
  have he := (existsResult_rename test 5 w z (five b F a L p) Fin.castSucc).trans
    (congrArg (existsResult test 5 w.castSucc z.castSucc) (five_map b F a L p Fin.castSucc))
  exact of_eq he.symm ho

def forallInput {m} (test : Formula 1) (w z b a B F G p : Fin m) : Formula m :=
  (SyntaxTopFormulaSyntax.abstracted w z b a B F G).conj
    ((Formula.mem p w).conj (InternalMPProof.annotated test w z B F p))
theorem forallInput_rename {m l} (test : Formula 1) (w z b a B F G p : Fin m) (r : Fin m → Fin l) :
    (forallInput test w z b a B F G p).rename r = forallInput test (r w) (r z) (r b) (r a) (r B) (r F) (r G) (r p) := by
  simp only [forallInput, Formula.rename, SyntaxTopFormulaSyntax.abstracted_rename, InternalMPProof.annotated_rename]

private def forallParent {m} (test : Formula 1) (w z b U p : Fin m) : Formula m :=
  existsResult test 3 w z (SetLanguage.args3 b U p)
private theorem forallParent_rename {m l} (test : Formula 1) (w z b U p : Fin m) (r : Fin m → Fin l) :
    (forallParent test w z b U p).rename r = forallParent test (r w) (r z) (r b) (r U) (r p) :=
  (existsResult_rename test 3 w z (SetLanguage.args3 b U p) r).trans
    (congrArg (existsResult test 3 (r w) (r z)) (args3_map b U p r))

def forallResult {m} (test : Formula 1) (w z b G p : Fin m) : Formula m := .ex
  ((SyntaxNodeSyntax.constructor 1 9 w.castSucc (fun _ : Fin 1 => G.castSucc) (Fin.last m)).conj
    (forallParent test w.castSucc z.castSucc b.castSucc (Fin.last m) p.castSucc))
theorem forallResult_rename {m l} (test : Formula 1) (w z b G p : Fin m) (r : Fin m → Fin l) :
    (forallResult test w z b G p).rename r = forallResult test (r w) (r z) (r b) (r G) (r p) := by
  simp only [forallResult, Formula.rename, SyntaxNodeSyntax.constructor_rename, forallParent_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]
private theorem forallMatrix_rename {m l} (w z code : Fin m) (env : Fin 4 → Fin m) (r : Fin m → Fin l) :
    (ProofForallNode.normalizedMatrix w z code env).rename r =
      ProofForallNode.normalizedMatrix (r w) (r z) (r code) (fun i => r (env i)) := by
  simp only [ProofForallNode.normalizedMatrix, Formula.rename, environmentNat_rename,
    ProofForallHead.normalized_rename, ProofForallSyntax.specification_rename]

private theorem forall_payload {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1) (w z b a B F G p U code : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) (hi : Derives Γ (forallInput test w z b a B F G p))
    (hu : Derives Γ (SyntaxNodeSyntax.constructor 1 9 w (fun _ : Fin 1 => G) U))
    (hc : Derives Γ (SyntaxNodeSyntax.constructor 3 3 w (SetLanguage.args3 b U p) code)) :
    Derives Γ (result test 3 w z code (SetLanguage.args3 b U p)) := by
  have hF := SyntaxTopFormulaTyping.abstract_source_type hZ w z b a B F G hw (.conjL hi)
  have hG := SyntaxTopFormulaTyping.abstract_target_type w z b a B F G (.conjL hi)
  have hE := SyntaxTopFormulaTyping.abstract_environment w z b a B F G (.conjL hi)
  have hb := Derives.conjR (.conjR (FormulaCodeProperties.guards w G a b hG))
  have hGN := Derives.conjL (FormulaCodeProperties.guards w G a b hG)
  have hFN := Derives.conjL (FormulaCodeProperties.guards w F z B hF)
  have hUN := ProofTreeConstructorFacts.range hZ 1 9 w U (fun _ : Fin 1 => G) hw hu
  have hPN := Derives.conjL (.conjR hi)
  have hAnn : Derives Γ (InternalMPProof.annotated test w z B F p) := .conjR (.conjR hi)
  let env : Fin 4 → Fin m := Fin.lastCases F (SetLanguage.args3 b G p)
  have hn : Derives Γ (environmentNat 4 w env) := .conjI hb (.conjI hGN (.conjI hPN (.conjI hFN HornRuleSyntax.truth_proved)))
  have hn3 : Derives Γ (environmentNat 3 w (SetLanguage.args3 b U p)) := .conjI hb (.conjI hUN (.conjI hPN HornRuleSyntax.truth_proved))
  have hs := ProofForallSyntax.intro_specification w z a env (.conjL (.conjR hE))
    (ProofForallSyntax.intro_atOneSpecification w z a B env (.conjR (.conjR hE))
      (.conjI hF (.conjI (.conjL (.conjR hAnn)) (.conjI (.conjR (.conjR hAnn)) (.conjL hi)))))
  have hh := ProofForallHead.intro_normalized w code U env (.conjI hu hc)
  have hm : Derives Γ (ProofForallNode.normalizedMatrix w z code env) := .conjI hn (.conjI hh hs)
  have he : Derives Γ (ProofForallNode.normalized w z code) := by
    apply HornBinderRules.intro_many 4 (ProofForallNode.normalizedBody w z code) env
    exact of_eq (by simp only [ProofForallNode.normalizedBody, forallMatrix_rename, assign_old, assign_slot]) hm
  have ht := Derives.impE (.conjR (ProofAllNodes.table_iff test hZ w z code hw hz)) (.disjR (.disjR (.disjR (.disjL he))))
  have hp := ProofTreeNodeBackward.matrix_backward test hZ 3 w code (SetLanguage.args3 b U p) hw ht
    (.conjI hn3 (.conjI hc (.conjI (.conjL hAnn) HornRuleSyntax.truth_proved)))
  exact package hZ test 3 w z code (SetLanguage.args3 b U p) hw hz hn3 hc hp

private theorem forall_at_quantifier {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1) (w z b a B F G p U : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) (hi : Derives Γ (forallInput test w z b a B F G p))
    (hu : Derives Γ (SyntaxNodeSyntax.constructor 1 9 w (fun _ : Fin 1 => G) U)) :
    Derives Γ (existsResult test 3 w z (SetLanguage.args3 b U p)) := by
  have hG := SyntaxTopFormulaTyping.abstract_target_type w z b a B F G (.conjL hi)
  have hb := Derives.conjR (.conjR (FormulaCodeProperties.guards w G a b hG))
  have hUN := ProofTreeConstructorFacts.range hZ 1 9 w U (fun _ : Fin 1 => G) hw hu
  have hn : Derives Γ (environmentNat 3 w (SetLanguage.args3 b U p)) :=
    .conjI hb (.conjI hUN (.conjI (.conjL (.conjR hi)) HornRuleSyntax.truth_proved))
  let T := (Formula.mem (Fin.last m) w.castSucc).conj
    (SyntaxNodeSyntax.constructor 3 3 w.castSucc (SetLanguage.args3 b.castSucc U.castSucc p.castSucc) (Fin.last m))
  let Δ := Context.add T (Context.image Formula.raise Γ)
  have hex : Derives Γ (.ex T) := of_eq (by simp only [T, SyntaxNodeSyntax.existsConstructor, args3_map])
    (SyntaxConstructors.exists_constructor hZ 3 3 w (SetLanguage.args3 b U p) hw (SyntaxForestSyntax.intro_inputs 3 w _ (environmentNat_at w _ hn)))
  apply Derives.exE (p := T) hex
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  have hr := forall_payload (ZFContext.under hZ T) test w.castSucc z.castSucc b.castSucc a.castSucc B.castSucc F.castSucc G.castSucc p.castSucc U.castSucc (Fin.last m)
    (of_eq (omega_rename w Fin.castSucc) (under hw T)) (of_eq (empty_rename z Fin.castSucc) (under hz T))
    (of_eq (forallInput_rename test w z b a B F G p Fin.castSucc) (under hi T))
    (of_eq (SyntaxNodeSyntax.constructor_rename 1 9 w (fun _ : Fin 1 => G) U Fin.castSucc) (under hu T)) (.conjR hT)
  have ho : Derives Δ (existsResult test 3 w.castSucc z.castSucc (SetLanguage.args3 b.castSucc U.castSucc p.castSucc)) := by
    apply Derives.exI (Fin.last m)
    exact of_eq (by simp only [Formula.instantiate, result_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hr
  have he := (existsResult_rename test 3 w z (SetLanguage.args3 b U p) Fin.castSucc).trans
    (congrArg (existsResult test 3 w.castSucc z.castSucc) (args3_map b U p Fin.castSucc))
  exact of_eq he.symm ho

/-- Constructs BOTH the original forall formula code and its actual parent
proof. AbstractFreeTop supplies its real successor scopes and binder lift. -/
theorem forall_produce {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1) (w z b a B F G p : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) (hi : Derives Γ (forallInput test w z b a B F G p)) :
    Derives Γ (forallResult test w z b G p) := by
  have hGN := SyntaxTopFormulaTyping.abstract_target_natural w z b a B F G (.conjL hi)
  let T := (Formula.mem (Fin.last m) w.castSucc).conj (SyntaxNodeSyntax.constructor 1 9 w.castSucc (fun _ : Fin 1 => G.castSucc) (Fin.last m))
  let Δ := Context.add T (Context.image Formula.raise Γ)
  have hex : Derives Γ (.ex T) := SyntaxConstructors.exists_constructor hZ 1 9 w (fun _ : Fin 1 => G) hw
    (SyntaxForestSyntax.intro_inputs 1 w _ (fun _ => hGN))
  apply Derives.exE (p := T) hex
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  have he := forall_at_quantifier (ZFContext.under hZ T) test w.castSucc z.castSucc b.castSucc a.castSucc B.castSucc F.castSucc G.castSucc p.castSucc (Fin.last m)
    (of_eq (omega_rename w Fin.castSucc) (under hw T)) (of_eq (empty_rename z Fin.castSucc) (under hz T))
    (of_eq (forallInput_rename test w z b a B F G p Fin.castSucc) (under hi T)) (.conjR hT)
  have hp : Derives Δ (forallParent test w.castSucc z.castSucc b.castSucc (Fin.last m) p.castSucc) := he
  have ho : Derives Δ (forallResult test w.castSucc z.castSucc b.castSucc G.castSucc p.castSucc) := by
    apply Derives.exI (Fin.last m)
    exact of_eq (by simp only [Formula.instantiate, Formula.rename, SyntaxNodeSyntax.constructor_rename, forallParent_rename,
      Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI (.conjR hT) hp)
  exact of_eq (forallResult_rename test w z b G p Fin.castSucc).symm ho

theorem result_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1) (kind : Fin 6) (w z r s : Fin m)
    (env : Fin ((shape kind).extra+2) → Fin m) (hw : Derives Γ (omega w))
    (hr : Derives Γ (result test kind w z r env)) (hs : Derives Γ (result test kind w z s env)) : Derives Γ (.equal r s) :=
  SyntaxConstructors.unique hZ ((shape kind).extra+2) (shape kind).tag w env r s hw (.conjL (.conjR hr)) (.conjL (.conjR hs))

def logicalSentence {m} (target : Bool) (w z b F c : Fin m) : Source.Sentence :=
  ((omega w).imp ((empty z).imp ((logicalInput w z b F c).imp (existsResult (OriginalAxiomCodeTest.test target) 0 w z (SetLanguage.args3 b F c))))).close

theorem logical_kernel_certificate {m} (target : Bool) (w z b F c : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (logicalSentence target w z b F c)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  exact logical (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.source_ZF m) _) _) _) (OriginalAxiomCodeTest.test target) w z b F c
    (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

def strengtheningSentence {m} (target : Bool) (w z b B F N p : Fin m) : Source.Sentence :=
  ((omega w).imp ((empty z).imp ((strengtheningInput (OriginalAxiomCodeTest.test target) w z b B F N p).imp (existsResult (OriginalAxiomCodeTest.test target) 4 w z (SetLanguage.args3 b F p))))).close

theorem strengthening_kernel_certificate {m} (target : Bool) (w z b B F N p : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (strengtheningSentence target w z b B F N p)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  exact strengthening (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.source_ZF m) _) _) _) (OriginalAxiomCodeTest.test target) w z b B F N p
    (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

def substitutionSentence {m} (target : Bool) (w z b a L F N p : Fin m) : Source.Sentence :=
  ((omega w).imp ((empty z).imp ((substitutionInput (OriginalAxiomCodeTest.test target) w z b a L F N p).imp (existsResult (OriginalAxiomCodeTest.test target) 5 w z (five b F a L p))))).close

theorem substitution_kernel_certificate {m} (target : Bool) (w z b a L F N p : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (substitutionSentence target w z b a L F N p)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  exact substitution (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.source_ZF m) _) _) _) (OriginalAxiomCodeTest.test target) w z b a L F N p
    (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

def forallSentence {m} (target : Bool) (w z b a B F G p : Fin m) : Source.Sentence :=
  ((omega w).imp ((empty z).imp ((forallInput (OriginalAxiomCodeTest.test target) w z b a B F G p).imp (forallResult (OriginalAxiomCodeTest.test target) w z b G p)))).close

theorem forall_kernel_certificate {m} (target : Bool) (w z b a B F G p : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (forallSentence target w z b a B F G p)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  exact forall_produce (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.source_ZF m) _) _) _) (OriginalAxiomCodeTest.test target) w z b a B F G p
    (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))
end PPAC.Migration.InternalProofOperations
