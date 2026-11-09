import PPAC.Migration.InternalProofTemplates
import PPAC.Migration.InternalProofImplication
import PPAC.Migration.ForcingPointwiseCode
import PPAC.Migration.Internal.LogicalInstantiateNode
import PPAC.Migration.Internal.LogicalOriginalNodes
import PPAC.Migration.Internal.SyntaxTopFormulaTyping
import PPAC.Migration.Internal.SyntaxTopFormulaExistence

/-! Actual original rule20 proof production, consuming original InstantiateTop
correctness and its complete queries. All certificate/axiom/MP witnesses are
internally constructed; arbitrary internal formulas, terms and scopes include
nonstandard values. This is a native proof operation, not forcing MP. -/
namespace PPAC.Migration.InternalProofQuantifier
open Internal Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)
open FormulaCodeSyntax (formulaCode formulaCode_rename)
open InternalProofConjunction (proved proved_rename)
open YesMetaZFC.Automation
set_option maxRecDepth 16384
attribute [local irreducible] NaturalRecursionSyntax.matrix

private def four {m} (b F t N : Fin m) : Fin 4 → Fin m := Fin.cases b (Fin.cases F (SyntaxAtomSyntax.two t N))
private theorem original20 : ObjectLogicalAxiom.rule20 ∈ ObjectLogicalAxiom.shapes := by
  simp only [ObjectLogicalAxiom.shapes, List.mem_cons, true_or, or_true]

private theorem types {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z b A F t N U : Fin m)
    (hw : Derives Γ (omega w))
    (hi : Derives Γ (SyntaxTopFormulaSyntax.instantiated w z b A t F N))
    (hu : Derives Γ (SyntaxLogicalSyntax.singleCode 9 w F U)) :
    Derives Γ ((formulaCode w U z b).conj (formulaCode w N z b)) := by
  have henv := SyntaxTopFormulaTyping.instantiate_environment w z b A t F N hi
  have hF := SyntaxTopFormulaTyping.instantiate_source_type hZ w z b A t F N hw hi
  have hN := SyntaxTopFormulaTyping.instantiate_target_type w z b A t F N hi
  have hs : Derives Γ (FormulaCodeRecursiveSyntax.stepCheck true w F z b) := by
    apply Derives.exI A
    exact of_eq (by simp only [Formula.instantiate, Formula.rename, successor_rename, formulaCode_rename,
      Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI (.conjR henv) hF)
  have hU := Derives.impE (.conjR (FormulaCodeKnownLogical.forall_iff hZ w z b F U hw hu)) (.conjI (.conjL (.conjL henv)) hs)
  exact .conjI hU hN

private theorem at_row {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1) (w z b A F t N U I c row : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hi : Derives Γ (SyntaxTopFormulaSyntax.instantiated w z b A t F N))
    (hu : Derives Γ (SyntaxLogicalSyntax.singleCode 9 w F U))
    (hI : Derives Γ (SyntaxNodeSyntax.constructor 2 7 w (SyntaxAtomSyntax.two U N) I))
    (hc : Derives Γ (SyntaxNodeSyntax.constructor 2 20 w (SyntaxAtomSyntax.two F t) c))
    (hr : Derives Γ (SyntaxNodeSyntax.constructor 3 0 w (SetLanguage.args3 b c I) row)) :
    Derives Γ (proved test w z b I) := by
  let env := four b F t N
  have henv := SyntaxTopFormulaTyping.instantiate_environment w z b A t F N hi
  have hF := SyntaxTopFormulaTyping.instantiate_source_type hZ w z b A t F N hw hi
  have hN := SyntaxTopFormulaTyping.instantiate_target_type w z b A t F N hi
  have hFN := FormulaCodeProperties.guards w F A b hF
  have hNN := FormulaCodeProperties.guards w N z b hN
  have hTN := SyntaxTerms.range hZ w z b t hw (.conjL henv)
  have hn : Derives Γ (environmentNat 4 w env) := .conjI (.conjR (.conjR hFN))
    (.conjI (.conjL hFN) (.conjI hTN (.conjI (.conjL hNN) HornRuleSyntax.truth_proved)))
  have hnorm := LogicalRule20Head.intro_normalized w row env (SetLanguage.args3 c U I) (.conjI hc (.conjI hu (.conjI hI hr)))
  have hh := Derives.impE (.conjR (LogicalRule20Head.head_iff hZ w row env hw hn)) hnorm
  have hs := LogicalInstantiateSyntax.intro_specification4 w z A env (.conjR henv) (.conjI hF (.conjI (.conjL henv) hi))
  have hspec : Derives Γ (LogicalInstantiateNodeSyntax.specification4 true w z row) := by
    apply HornBinderRules.intro_many 4 _ env
    exact of_eq (by simp only [LogicalInstantiateNodeSyntax.specificationBody4, LogicalInstantiateNodeSyntax.specificationMatrix4,
      Formula.rename, environmentNat_rename, graph_rename, LogicalInstantiateSyntax.specification4_rename, assign_old, assign_slot]; rfl) (.conjI hn (.conjI hh hs))
  have hn4 := Derives.impE (.conjR (LogicalInstantiateNode.node4_iff hZ true w z row hw hz)) hspec
  have hn20 := Derives.impE (.conjR (LogicalOriginalNodes.rule20_iff w row)) hn4
  have htable : Derives Γ (LogicalOriginalNodeSyntax.table w row) := ProofTreeRootSyntax.disjoin_intro _ _
    (List.mem_map.mpr ⟨ObjectLogicalAxiom.rule20, original20, rfl⟩) hn20
  have hquery : Derives Γ (OriginalLogicalExprQuery.rowQuery 3 0 w (SetLanguage.args3 b c I)) := by
    apply Derives.exI row
    exact of_eq (by simp only [Formula.instantiate, Formula.rename, SyntaxNodeSyntax.constructor_rename,
      LogicalTableRenaming.table_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI hr htable)
  have hT := types hZ w z b A F t N U hw hi hu
  have hIT := Derives.impE (.conjR (FormulaCodeKnownLogical.binary2_iff hZ w z b U N I hw hI))
    (.conjI (.conjR (FormulaCodeProperties.guards w N z b hN)) hT)
  have hcN := ProofTreeConstructorFacts.range hZ 2 20 w c (SyntaxAtomSyntax.two F t) hw hc
  exact InternalProofTemplates.logical_proof test w z b I c
    (InternalProofOperations.logical hZ test w z b I c hw hz (.conjI hIT (.conjI hcN hquery)))

private theorem at_certificate {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1) (w z b A F t N U I c : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hi : Derives Γ (SyntaxTopFormulaSyntax.instantiated w z b A t F N))
    (hu : Derives Γ (SyntaxLogicalSyntax.singleCode 9 w F U))
    (hI : Derives Γ (SyntaxNodeSyntax.constructor 2 7 w (SyntaxAtomSyntax.two U N) I))
    (hc : Derives Γ (SyntaxNodeSyntax.constructor 2 20 w (SyntaxAtomSyntax.two F t) c)) :
    Derives Γ (proved test w z b I) := by
  have hT := types hZ w z b A F t N U hw hi hu
  have hctx := Derives.conjR (FormulaCodeProperties.guards w N z b (.conjR hT))
  have hIN := ProofTreeConstructorFacts.range hZ 2 7 w I (SyntaxAtomSyntax.two U N) hw hI
  have hcN := ProofTreeConstructorFacts.range hZ 2 20 w c (SyntaxAtomSyntax.two F t) hw hc
  have hinputs := SyntaxForestSyntax.intro_inputs 3 w (SetLanguage.args3 b c I)
    (fun i => Fin.cases (.conjR hctx) (fun i => Fin.cases hcN (fun i => Fin.cases hIN (fun e => Fin.elim0 e) i) i) i)
  let E := (Formula.mem (Fin.last m) w.castSucc).conj (SyntaxNodeSyntax.constructor 3 0 w.castSucc (SetLanguage.args3 b.castSucc c.castSucc I.castSucc) (Fin.last m))
  let Δ := Context.add E (Context.image Formula.raise Γ)
  have hex : Derives Γ (.ex E) := of_eq (by simp only [E, SyntaxNodeSyntax.existsConstructor]; rfl) (SyntaxConstructors.exists_constructor hZ 3 0 w (SetLanguage.args3 b c I) hw hinputs)
  apply Derives.exE (p := E) hex
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have out := at_row (ZFContext.under hZ E) test w.castSucc z.castSucc b.castSucc A.castSucc F.castSucc t.castSucc N.castSucc U.castSucc I.castSucc c.castSucc (Fin.last m)
    (of_eq (omega_rename w Fin.castSucc) (under hw E)) (of_eq (empty_rename z Fin.castSucc) (under hz E))
    (of_eq (SyntaxTopFormulaSyntax.instantiated_rename w z b A t F N Fin.castSucc) (under hi E))
    (of_eq (SyntaxLogicalSyntax.singleCode_rename 9 w F U Fin.castSucc) (under hu E))
    (of_eq (by simp only [Formula.raise, SyntaxNodeSyntax.constructor_rename, SyntaxAtomSyntax.two_map]) (under hI E))
    (of_eq (by simp only [Formula.raise, SyntaxNodeSyntax.constructor_rename, SyntaxAtomSyntax.two_map]) (under hc E)) (.conjR hE)
  exact of_eq (proved_rename test w z b I Fin.castSucc).symm out

/-- Generate the ORIGINAL rule20 axiom proof with its complete actual queries.
Neither an axiom certificate nor a proof of the implication is supplied. -/
theorem universal_axiom {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1) (w z b A F t N U I : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hi : Derives Γ (SyntaxTopFormulaSyntax.instantiated w z b A t F N))
    (hu : Derives Γ (SyntaxLogicalSyntax.singleCode 9 w F U))
    (hI : Derives Γ (SyntaxNodeSyntax.constructor 2 7 w (SyntaxAtomSyntax.two U N) I)) :
    Derives Γ (proved test w z b I) := by
  have hFN := SyntaxTopFormulaTyping.instantiate_source_natural w z b A t F N hi
  have hTN := SyntaxTerms.range hZ w z b t hw (.conjL (SyntaxTopFormulaTyping.instantiate_environment w z b A t F N hi))
  have hinputs := SyntaxForestSyntax.intro_inputs 2 w (SyntaxAtomSyntax.two F t)
    (fun i => Fin.cases hFN (fun i => Fin.cases hTN (fun e => Fin.elim0 e) i) i)
  let E := (Formula.mem (Fin.last m) w.castSucc).conj (SyntaxNodeSyntax.constructor 2 20 w.castSucc (SyntaxAtomSyntax.two F.castSucc t.castSucc) (Fin.last m))
  let Δ := Context.add E (Context.image Formula.raise Γ)
  have hex : Derives Γ (.ex E) := of_eq (by simp only [E, SyntaxNodeSyntax.existsConstructor, SyntaxAtomSyntax.two_map]) (SyntaxConstructors.exists_constructor hZ 2 20 w (SyntaxAtomSyntax.two F t) hw hinputs)
  apply Derives.exE (p := E) hex
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have out := at_certificate (ZFContext.under hZ E) test w.castSucc z.castSucc b.castSucc A.castSucc F.castSucc t.castSucc N.castSucc U.castSucc I.castSucc (Fin.last m)
    (of_eq (omega_rename w Fin.castSucc) (under hw E)) (of_eq (empty_rename z Fin.castSucc) (under hz E))
    (of_eq (SyntaxTopFormulaSyntax.instantiated_rename w z b A t F N Fin.castSucc) (under hi E))
    (of_eq (SyntaxLogicalSyntax.singleCode_rename 9 w F U Fin.castSucc) (under hu E))
    (of_eq (by simp only [Formula.raise, SyntaxNodeSyntax.constructor_rename, SyntaxAtomSyntax.two_map]) (under hI E)) (.conjR hE)
  exact of_eq (proved_rename test w z b I Fin.castSucc).symm out

/-- Actual universal elimination: construct the rule20 axiom and a genuine MP
parent. Every term, formula, scope and proof code may be internally nonstandard. -/
theorem eliminate {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1) (w z b A F t N U : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hi : Derives Γ (SyntaxTopFormulaSyntax.instantiated w z b A t F N))
    (hu : Derives Γ (SyntaxLogicalSyntax.singleCode 9 w F U))
    (hp : Derives Γ (proved test w z b U)) : Derives Γ (proved test w z b N) := by
  have hT := types hZ w z b A F t N U hw hi hu
  have hUN := Derives.conjL (FormulaCodeProperties.guards w U z b (.conjL hT))
  have hNN := Derives.conjL (FormulaCodeProperties.guards w N z b (.conjR hT))
  have hinputs := SyntaxForestSyntax.intro_inputs 2 w (SyntaxAtomSyntax.two U N)
    (fun i => Fin.cases hUN (fun i => Fin.cases hNN (fun e => Fin.elim0 e) i) i)
  let E := (Formula.mem (Fin.last m) w.castSucc).conj (SyntaxNodeSyntax.constructor 2 7 w.castSucc (SyntaxAtomSyntax.two U.castSucc N.castSucc) (Fin.last m))
  let Δ := Context.add E (Context.image Formula.raise Γ)
  have hex : Derives Γ (.ex E) := of_eq (by simp only [E, SyntaxNodeSyntax.existsConstructor, SyntaxAtomSyntax.two_map]) (SyntaxConstructors.exists_constructor hZ 2 7 w (SyntaxAtomSyntax.two U N) hw hinputs)
  apply Derives.exE (p := E) hex
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw E)
  have hz1 := of_eq (empty_rename z Fin.castSucc) (under hz E)
  have hZ1 := ZFContext.under hZ E
  have hi1 := of_eq (SyntaxTopFormulaSyntax.instantiated_rename w z b A t F N Fin.castSucc) (under hi E)
  have hu1 := of_eq (SyntaxLogicalSyntax.singleCode_rename 9 w F U Fin.castSucc) (under hu E)
  have haxiom := universal_axiom hZ1 test w.castSucc z.castSucc b.castSucc A.castSucc F.castSucc t.castSucc N.castSucc U.castSucc (Fin.last m) hw1 hz1 hi1 hu1 (.conjR hE)
  have hout := InternalProofConjunction.modus_ponens hZ1 test w.castSucc z.castSucc b.castSucc U.castSucc N.castSucc (Fin.last m)
    hw1 hz1 (of_eq (formulaCode_rename w U z b Fin.castSucc) (under (.conjL hT) E))
    (of_eq (formulaCode_rename w N z b Fin.castSucc) (under (.conjR hT) E)) (.conjR hE)
    (of_eq (proved_rename test w z b U Fin.castSucc) (under hp E)) haxiom
  exact of_eq (proved_rename test w z b N Fin.castSucc).symm hout

private def instanceData {m} (test : Formula 1) (w z b F t A N : Fin m) : Formula m :=
  (successor A z).conj ((SyntaxTopFormulaSyntax.instantiated w z b A t F N).conj (proved test w z b N))
private theorem instanceData_rename {m l} (test : Formula 1) (w z b F t A N : Fin m) (r : Fin m → Fin l) :
    (instanceData test w z b F t A N).rename r = instanceData test (r w) (r z) (r b) (r F) (r t) (r A) (r N) := by
  simp only [instanceData, Formula.rename, successor_rename, SyntaxTopFormulaSyntax.instantiated_rename, proved_rename]
private def instanceBody {m} (test : Formula 1) (w z b F t : Fin m) : Formula (m+2) :=
  instanceData test (old 2 w) (old 2 z) (old 2 b) (old 2 F) (old 2 t) (slot 2 0) (slot 2 1)

/-- The actual original substitution result AND its actual original proof.
Both the bound-one scope and output code are internally quantified. -/
def instantiatedProof {m} (test : Formula 1) (w z b F t : Fin m) : Formula m := existsMany 2 (instanceBody test w z b F t)

theorem instantiatedProof_rename {m l} (test : Formula 1) (w z b F t : Fin m) (r : Fin m → Fin l) :
    (instantiatedProof test w z b F t).rename r = instantiatedProof test (r w) (r z) (r b) (r F) (r t) := by
  simp only [instantiatedProof, existsMany_rename, instanceBody, instanceData_rename, lift_old, lift_slot]

private theorem intro_instance {m} {Γ : Context m} (test : Formula 1) (w z b F t A N : Fin m)
    (hA : Derives Γ (successor A z)) (hi : Derives Γ (SyntaxTopFormulaSyntax.instantiated w z b A t F N))
    (hp : Derives Γ (proved test w z b N)) : Derives Γ (instantiatedProof test w z b F t) := by
  apply HornBinderRules.intro_many 2 _ (SyntaxAtomSyntax.two A N)
  exact of_eq (by simp only [instanceBody, instanceData_rename, assign_old, assign_slot]; rfl) (.conjI hA (.conjI hi hp))

private theorem at_scope {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1) (w z b A F t U : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) (hA : Derives Γ (successor A z))
    (hF : Derives Γ (formulaCode w F A b)) (ht : Derives Γ (SyntaxTermSyntax.term w z b t))
    (hu : Derives Γ (SyntaxLogicalSyntax.singleCode 9 w F U)) (hp : Derives Γ (proved test w z b U)) :
    Derives Γ (instantiatedProof test w z b F t) := by
  have hin : Derives Γ (SyntaxTopFormulaSyntax.instantiateInput w z b A t F) := .conjI (.conjI ht hA) hF
  let E := SyntaxTopFormulaSyntax.instantiated w.castSucc z.castSucc b.castSucc A.castSucc t.castSucc F.castSucc (Fin.last m)
  let Δ := Context.add E (Context.image Formula.raise Γ)
  apply Derives.exE (p := E) (SyntaxTopFormulaExistence.instantiate_exists hZ w z b A t F hw hin)
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have hproof := eliminate (ZFContext.under hZ E) test w.castSucc z.castSucc b.castSucc A.castSucc F.castSucc t.castSucc (Fin.last m) U.castSucc
    (of_eq (omega_rename w Fin.castSucc) (under hw E)) (of_eq (empty_rename z Fin.castSucc) (under hz E)) hE
    (of_eq (SyntaxLogicalSyntax.singleCode_rename 9 w F U Fin.castSucc) (under hu E))
    (of_eq (proved_rename test w z b U Fin.castSucc) (under hp E))
  exact of_eq (instantiatedProof_rename test w z b F t Fin.castSucc).symm
    (intro_instance test w.castSucc z.castSucc b.castSucc F.castSucc t.castSucc A.castSucc (Fin.last m)
      (of_eq (successor_rename A z Fin.castSucc) (under hA E)) hE hproof)

/-- Construct the instance code as well as its proof from the actual parent
proof and a legal term. No output code, operation judgment or scope witness is
supplied; all are produced internally by the existing original operations. -/
theorem instantiate {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1) (w z b F t U : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) (hU : Derives Γ (formulaCode w U z b))
    (hu : Derives Γ (SyntaxLogicalSyntax.singleCode 9 w F U)) (ht : Derives Γ (SyntaxTermSyntax.term w z b t))
    (hp : Derives Γ (proved test w z b U)) : Derives Γ (instantiatedProof test w z b F t) := by
  have htypes := Derives.impE (.conjL (FormulaCodeKnownLogical.forall_iff hZ w z b F U hw hu)) hU
  let E := (successor (Fin.last m) z.castSucc).conj (formulaCode w.castSucc F.castSucc (Fin.last m) b.castSucc)
  let Δ := Context.add E (Context.image Formula.raise Γ)
  apply Derives.exE (p := E) (.conjR htypes)
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have out := at_scope (ZFContext.under hZ E) test w.castSucc z.castSucc b.castSucc (Fin.last m) F.castSucc t.castSucc U.castSucc
    (of_eq (omega_rename w Fin.castSucc) (under hw E)) (of_eq (empty_rename z Fin.castSucc) (under hz E)) (.conjL hE) (.conjR hE)
    (of_eq (SyntaxTermSyntax.term_rename w z b t Fin.castSucc) (under ht E))
    (of_eq (SyntaxLogicalSyntax.singleCode_rename 9 w F U Fin.castSucc) (under hu E))
    (of_eq (proved_rename test w z b U Fin.castSucc) (under hp E))
  exact of_eq (instantiatedProof_rename test w z b F t Fin.castSucc).symm out

def input {m} (test : Formula 1) (w z b F t U : Fin m) : Formula m :=
  (omega w).conj ((empty z).conj ((formulaCode w U z b).conj ((SyntaxLogicalSyntax.singleCode 9 w F U).conj
    ((SyntaxTermSyntax.term w z b t).conj (proved test w z b U)))))

def sentence {m} (target : Bool) (w z b F t U : Fin m) : Source.Sentence :=
  ((input (OriginalAxiomCodeTest.test target) w z b F t U).imp (instantiatedProof (OriginalAxiomCodeTest.test target) w z b F t)).close

theorem kernel_certificate {m} (target : Bool) (w z b F t U : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (sentence target w z b F t U)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  let E := input (OriginalAxiomCodeTest.test target) w z b F t U
  let Γ := Context.add E (Source.SetLanguage.ZF.at m)
  have h : Derives Γ E := .hyp (Or.inl rfl)
  exact instantiate (ZFContext.add (ZFContext.source_ZF m) E) (OriginalAxiomCodeTest.test target) w z b F t U
    (.conjL h) (.conjL (.conjR h)) (.conjL (.conjR (.conjR h))) (.conjL (.conjR (.conjR (.conjR h))))
    (.conjL (.conjR (.conjR (.conjR (.conjR h))))) (.conjR (.conjR (.conjR (.conjR (.conjR h)))))

private def openedData {m} (test : Formula 1) (w z b f T x Q term : Fin m) (v : Fin 3 → Fin m) : Formula m :=
  (ForcingOpenLayout.environment w z b f T (v 0) (v 1)).conj
    ((SyntaxLogicalSyntax.singleCode 9 w (v 2) Q).conj
      ((SyntaxMixedFormulaRecursiveSyntax.check true w x (v 0) (v 1) b f z T (v 2)).conj
        (instantiatedProof test w z T (v 2) term)))
private theorem openedData_rename {m l} (test : Formula 1) (w z b f T x Q term : Fin m) (v : Fin 3 → Fin m) (r : Fin m → Fin l) :
    (openedData test w z b f T x Q term v).rename r = openedData test (r w) (r z) (r b) (r f) (r T) (r x) (r Q) (r term) (fun i => r (v i)) := by
  simp only [openedData, Formula.rename, ForcingOpenLayout.environment_rename, SyntaxLogicalSyntax.singleCode_rename,
    SyntaxMixedFormulaRecursiveSyntax.check_rename, instantiatedProof_rename]
private def openedBody {m} (test : Formula 1) (w z b f T x Q term : Fin m) : Formula (m+3) :=
  openedData test (old 3 w) (old 3 z) (old 3 b) (old 3 f) (old 3 T) (old 3 x) (old 3 Q) (old 3 term) (slot 3)

/-- The SAME real pointwise parent environment/body, its original mixed lift,
and an actual original proof of its actual term instance, all in object EX. -/
def openedInstance {m} (test : Formula 1) (w z b f T x Q term : Fin m) : Formula m := existsMany 3 (openedBody test w z b f T x Q term)

theorem openedInstance_rename {m l} (test : Formula 1) (w z b f T x Q term : Fin m) (r : Fin m → Fin l) :
    (openedInstance test w z b f T x Q term).rename r = openedInstance test (r w) (r z) (r b) (r f) (r T) (r x) (r Q) (r term) := by
  simp only [openedInstance, existsMany_rename, openedBody, openedData_rename, lift_old, lift_slot]

private theorem intro_opened_instance {m} {Γ : Context m} (test : Formula 1) (w z b f T x Q term L S X : Fin m)
    (he : Derives Γ (ForcingOpenLayout.environment w z b f T L S))
    (hc : Derives Γ (SyntaxLogicalSyntax.singleCode 9 w X Q))
    (hx : Derives Γ (SyntaxMixedFormulaRecursiveSyntax.check true w x L S b f z T X))
    (hp : Derives Γ (instantiatedProof test w z T X term)) : Derives Γ (openedInstance test w z b f T x Q term) := by
  apply HornBinderRules.intro_many 3 _ (SetLanguage.args3 L S X)
  exact of_eq (by simp only [openedBody, openedData_rename, assign_old, assign_slot]; rfl) (.conjI he (.conjI hc (.conjI hx hp)))

private theorem at_environment {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1) (w z b f T x Q term L S : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) (hQ : Derives Γ (formulaCode w Q z T))
    (ht : Derives Γ (SyntaxTermSyntax.term w z T term)) (hp : Derives Γ (proved test w z T Q))
    (he : Derives Γ (ForcingOpenLayout.environment w z b f T L S))
    (hs : Derives Γ (ForcingMixedUnary.singleOutput 9 true w L S b f z T x Q)) :
    Derives Γ (openedInstance test w z b f T x Q term) := by
  let E := (SyntaxLogicalSyntax.singleCode 9 w.castSucc (Fin.last m) Q.castSucc).conj
    (SyntaxMixedFormulaRecursiveSyntax.check true w.castSucc x.castSucc L.castSucc S.castSucc b.castSucc f.castSucc z.castSucc T.castSucc (Fin.last m))
  let Δ := Context.add E (Context.image Formula.raise Γ)
  apply Derives.exE (p := E) hs
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have hinst := instantiate (ZFContext.under hZ E) test w.castSucc z.castSucc T.castSucc (Fin.last m) term.castSucc Q.castSucc
    (of_eq (omega_rename w Fin.castSucc) (under hw E)) (of_eq (empty_rename z Fin.castSucc) (under hz E))
    (of_eq (formulaCode_rename w Q z T Fin.castSucc) (under hQ E)) (.conjL hE)
    (of_eq (SyntaxTermSyntax.term_rename w z T term Fin.castSucc) (under ht E))
    (of_eq (proved_rename test w z T Q Fin.castSucc) (under hp E))
  exact of_eq (openedInstance_rename test w z b f T x Q term Fin.castSucc).symm
    (intro_opened_instance test w.castSucc z.castSucc b.castSucc f.castSucc T.castSucc x.castSucc Q.castSucc term.castSucc L.castSucc S.castSucc (Fin.last m)
      (of_eq (ForcingOpenLayout.environment_rename w z b f T L S Fin.castSucc) (under he E)) (.conjL hE) (.conjR hE) hinst)

/-- Direct consumer of the REAL pointwise quantifier opening, not a supplied
body or forcing answer. Preserve the same actual environment, original lifted
child substitution and the actual native proof of its generated instance. -/
theorem opened_instance {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1) (w z b f T n x Q term : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hc : Derives Γ (SyntaxLogicalSyntax.singleCode 9 w x n))
    (ho : Derives Γ (ForcingPointwiseCode.opened w z b f T n Q))
    (ht : Derives Γ (SyntaxTermSyntax.term w z T term)) (hp : Derives Γ (proved test w z T Q)) :
    Derives Γ (openedInstance test w z b f T x Q term) := by
  have hq := ForcingPointwiseCode.opened_quantified hZ true w z b f T n x Q hw hc ho
  have hQ := ForcingPointwiseCode.opened_type w z b f T n Q ho
  let E := (ForcingOpenLayout.environment (old 2 w) (old 2 z) (old 2 b) (old 2 f) (old 2 T) (slot 2 0) (slot 2 1)).conj
    (ForcingMixedUnary.singleOutput 9 true (old 2 w) (slot 2 0) (slot 2 1) (old 2 b) (old 2 f) (old 2 z) (old 2 T) (old 2 x) (old 2 Q))
  let Δ := Context.add E (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 E _ hq
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have out := at_environment (HornBinderRules.zf_body 2 hZ E) test (old 2 w) (old 2 z) (old 2 b) (old 2 f) (old 2 T) (old 2 x) (old 2 Q) (old 2 term) (slot 2 0) (slot 2 1)
    (of_eq (omega_rename w (old 2)) (HornBinderRules.under_body 2 hw E))
    (of_eq (empty_rename z (old 2)) (HornBinderRules.under_body 2 hz E))
    (of_eq (formulaCode_rename w Q z T (old 2)) (HornBinderRules.under_body 2 hQ E))
    (of_eq (SyntaxTermSyntax.term_rename w z T term (old 2)) (HornBinderRules.under_body 2 ht E))
    (of_eq (proved_rename test w z T Q (old 2)) (HornBinderRules.under_body 2 hp E)) (.conjL hE) (.conjR hE)
  exact of_eq (openedInstance_rename test w z b f T x Q term (old 2)).symm out

def openedSentence {m} (target : Bool) (w z b f T n x Q term : Fin m) : Source.Sentence :=
  ((omega w).imp ((empty z).imp ((SyntaxLogicalSyntax.singleCode 9 w x n).imp
    ((ForcingPointwiseCode.opened w z b f T n Q).imp ((SyntaxTermSyntax.term w z T term).imp
      ((proved (OriginalAxiomCodeTest.test target) w z T Q).imp (openedInstance (OriginalAxiomCodeTest.test target) w z b f T x Q term))))))).close

theorem opened_kernel_certificate {m} (target : Bool) (w z b f T n x Q term : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (openedSentence target w z b f T n x Q term)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  exact opened_instance (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.source_ZF m) _) _) _) _) _) _)
    (OriginalAxiomCodeTest.test target) w z b f T n x Q term
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))) (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

/-- Preserve a COMMON actual background formula: from a proof of B→forall F
construct B→instance F. No proof or truth of B is assumed. Reuse the existing
original K/S implication composition, not a new deduction backend. -/
theorem guarded_eliminate {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1) (w z b A F term N U B I K : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hi : Derives Γ (SyntaxTopFormulaSyntax.instantiated w z b A term F N))
    (hu : Derives Γ (SyntaxLogicalSyntax.singleCode 9 w F U)) (hB : Derives Γ (formulaCode w B z b))
    (hI : Derives Γ (SyntaxNodeSyntax.constructor 2 7 w (SyntaxAtomSyntax.two B U) I))
    (hK : Derives Γ (SyntaxNodeSyntax.constructor 2 7 w (SyntaxAtomSyntax.two B N) K))
    (hp : Derives Γ (proved test w z b I)) : Derives Γ (proved test w z b K) := by
  have hT := types hZ w z b A F term N U hw hi hu
  have hUN := Derives.conjL (FormulaCodeProperties.guards w U z b (.conjL hT))
  have hNN := Derives.conjL (FormulaCodeProperties.guards w N z b (.conjR hT))
  have hinputs := SyntaxForestSyntax.intro_inputs 2 w (SyntaxAtomSyntax.two U N)
    (fun i => Fin.cases hUN (fun i => Fin.cases hNN (fun e => Fin.elim0 e) i) i)
  let E := (Formula.mem (Fin.last m) w.castSucc).conj (SyntaxNodeSyntax.constructor 2 7 w.castSucc (SyntaxAtomSyntax.two U.castSucc N.castSucc) (Fin.last m))
  let Δ := Context.add E (Context.image Formula.raise Γ)
  have hex : Derives Γ (.ex E) := of_eq (by simp only [E, SyntaxNodeSyntax.existsConstructor, SyntaxAtomSyntax.two_map])
    (SyntaxConstructors.exists_constructor hZ 2 7 w (SyntaxAtomSyntax.two U N) hw hinputs)
  apply Derives.exE (p := E) hex
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw E)
  have hz1 := of_eq (empty_rename z Fin.castSucc) (under hz E)
  have hZ1 := ZFContext.under hZ E
  have haxiom := universal_axiom hZ1 test w.castSucc z.castSucc b.castSucc A.castSucc F.castSucc term.castSucc N.castSucc U.castSucc (Fin.last m) hw1 hz1
    (of_eq (SyntaxTopFormulaSyntax.instantiated_rename w z b A term F N Fin.castSucc) (under hi E))
    (of_eq (SyntaxLogicalSyntax.singleCode_rename 9 w F U Fin.castSucc) (under hu E)) (.conjR hE)
  have hout := InternalProofImplication.compose hZ1 test w.castSucc z.castSucc b.castSucc B.castSucc U.castSucc N.castSucc I.castSucc (Fin.last m) K.castSucc
    hw1 hz1 (of_eq (formulaCode_rename w B z b Fin.castSucc) (under hB E))
    (of_eq (formulaCode_rename w U z b Fin.castSucc) (under (.conjL hT) E))
    (of_eq (formulaCode_rename w N z b Fin.castSucc) (under (.conjR hT) E))
    (of_eq (by simp only [Formula.raise, SyntaxNodeSyntax.constructor_rename, SyntaxAtomSyntax.two_map]) (under hI E)) (.conjR hE)
    (of_eq (by simp only [Formula.raise, SyntaxNodeSyntax.constructor_rename, SyntaxAtomSyntax.two_map]) (under hK E))
    (of_eq (proved_rename test w z b I Fin.castSucc) (under hp E)) haxiom
  exact of_eq (proved_rename test w z b K Fin.castSucc).symm hout

def guardedSentence {m} (target : Bool) (w z b A F term N U B I K : Fin m) : Source.Sentence :=
  ((omega w).imp ((empty z).imp ((SyntaxTopFormulaSyntax.instantiated w z b A term F N).imp
    ((SyntaxLogicalSyntax.singleCode 9 w F U).imp ((formulaCode w B z b).imp
      ((SyntaxNodeSyntax.constructor 2 7 w (SyntaxAtomSyntax.two B U) I).imp
        ((SyntaxNodeSyntax.constructor 2 7 w (SyntaxAtomSyntax.two B N) K).imp
          ((proved (OriginalAxiomCodeTest.test target) w z b I).imp (proved (OriginalAxiomCodeTest.test target) w z b K))))))))).close

theorem guarded_kernel_certificate {m} (target : Bool) (w z b A F term N U B I K : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (guardedSentence target w z b A F term N U B I K)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  exact guarded_eliminate (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.source_ZF m) _) _) _) _) _) _) _) _) (OriginalAxiomCodeTest.test target) w z b A F term N U B I K
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    (.hyp (Or.inr (Or.inr (Or.inl rfl))))
    (.hyp (Or.inr (Or.inl rfl)))
    (.hyp (Or.inl rfl))

private def guardedResultData {m} (test : Formula 1) (w z b F term G A N K : Fin m) : Formula m :=
  (successor A z).conj ((SyntaxTopFormulaSyntax.instantiated w z b A term F N).conj
    ((SyntaxNodeSyntax.constructor 2 7 w (SyntaxAtomSyntax.two G N) K).conj (proved test w z b K)))
private theorem guardedResultData_rename {m l} (test : Formula 1) (w z b F term G A N K : Fin m) (r : Fin m → Fin l) :
    (guardedResultData test w z b F term G A N K).rename r = guardedResultData test (r w) (r z) (r b) (r F) (r term) (r G) (r A) (r N) (r K) := by
  simp only [guardedResultData, Formula.rename, successor_rename, SyntaxTopFormulaSyntax.instantiated_rename,
    SyntaxNodeSyntax.constructor_rename, SyntaxAtomSyntax.two_map, proved_rename]
private def guardedResultBody {m} (test : Formula 1) (w z b F term G : Fin m) : Formula (m+3) :=
  guardedResultData test (old 3 w) (old 3 z) (old 3 b) (old 3 F) (old 3 term) (old 3 G) (slot 3 0) (slot 3 1) (slot 3 2)

/-- Actual instance and proof under the SAME background G. A,N,K and the
actual operation judgment are generated internally, not supplied. -/
def guardedInstance {m} (test : Formula 1) (w z b F term G : Fin m) : Formula m := existsMany 3 (guardedResultBody test w z b F term G)

theorem guardedInstance_rename {m l} (test : Formula 1) (w z b F term G : Fin m) (r : Fin m → Fin l) :
    (guardedInstance test w z b F term G).rename r = guardedInstance test (r w) (r z) (r b) (r F) (r term) (r G) := by
  simp only [guardedInstance, existsMany_rename, guardedResultBody, guardedResultData_rename, lift_old, lift_slot]

private theorem intro_guarded_instance {m} {Γ : Context m} (test : Formula 1) (w z b F term G A N K : Fin m)
    (hA : Derives Γ (successor A z)) (hi : Derives Γ (SyntaxTopFormulaSyntax.instantiated w z b A term F N))
    (hc : Derives Γ (SyntaxNodeSyntax.constructor 2 7 w (SyntaxAtomSyntax.two G N) K)) (hp : Derives Γ (proved test w z b K)) :
    Derives Γ (guardedInstance test w z b F term G) := by
  apply HornBinderRules.intro_many 3 _ (SetLanguage.args3 A N K)
  exact of_eq (by simp only [guardedResultBody, guardedResultData_rename, assign_old, assign_slot]; rfl) (.conjI hA (.conjI hi (.conjI hc hp)))

private theorem guarded_at_instance {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1) (w z b A F term N U G I : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hi : Derives Γ (SyntaxTopFormulaSyntax.instantiated w z b A term F N))
    (hu : Derives Γ (SyntaxLogicalSyntax.singleCode 9 w F U)) (hG : Derives Γ (formulaCode w G z b))
    (hI : Derives Γ (SyntaxNodeSyntax.constructor 2 7 w (SyntaxAtomSyntax.two G U) I)) (hp : Derives Γ (proved test w z b I)) :
    Derives Γ (guardedInstance test w z b F term G) := by
  have hN := SyntaxTopFormulaTyping.instantiate_target_type w z b A term F N hi
  have hin := SyntaxForestSyntax.intro_inputs 2 w (SyntaxAtomSyntax.two G N)
    (fun i => Fin.cases (.conjL (FormulaCodeProperties.guards w G z b hG))
      (fun i => Fin.cases (.conjL (FormulaCodeProperties.guards w N z b hN)) (fun e => Fin.elim0 e) i) i)
  let E := (Formula.mem (Fin.last m) w.castSucc).conj (SyntaxNodeSyntax.constructor 2 7 w.castSucc (SyntaxAtomSyntax.two G.castSucc N.castSucc) (Fin.last m))
  let Δ := Context.add E (Context.image Formula.raise Γ)
  have hex : Derives Γ (.ex E) := of_eq (by simp only [E, SyntaxNodeSyntax.existsConstructor, SyntaxAtomSyntax.two_map])
    (SyntaxConstructors.exists_constructor hZ 2 7 w (SyntaxAtomSyntax.two G N) hw hin)
  apply Derives.exE (p := E) hex
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have hi1 := of_eq (SyntaxTopFormulaSyntax.instantiated_rename w z b A term F N Fin.castSucc) (under hi E)
  have hproof := guarded_eliminate (ZFContext.under hZ E) test w.castSucc z.castSucc b.castSucc A.castSucc F.castSucc term.castSucc N.castSucc U.castSucc G.castSucc I.castSucc (Fin.last m)
    (of_eq (omega_rename w Fin.castSucc) (under hw E)) (of_eq (empty_rename z Fin.castSucc) (under hz E)) hi1
    (of_eq (SyntaxLogicalSyntax.singleCode_rename 9 w F U Fin.castSucc) (under hu E))
    (of_eq (formulaCode_rename w G z b Fin.castSucc) (under hG E))
    (of_eq (by simp only [Formula.raise, SyntaxNodeSyntax.constructor_rename, SyntaxAtomSyntax.two_map]) (under hI E)) (.conjR hE)
    (of_eq (proved_rename test w z b I Fin.castSucc) (under hp E))
  exact of_eq (guardedInstance_rename test w z b F term G Fin.castSucc).symm
    (intro_guarded_instance test w.castSucc z.castSucc b.castSucc F.castSucc term.castSucc G.castSucc A.castSucc N.castSucc (Fin.last m)
      (.conjR (SyntaxTopFormulaTyping.instantiate_environment _ _ _ _ _ _ _ hi1)) hi1 (.conjR hE) hproof)

private theorem guarded_at_scope {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1) (w z b A F term U G I : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) (hA : Derives Γ (successor A z))
    (hF : Derives Γ (formulaCode w F A b)) (ht : Derives Γ (SyntaxTermSyntax.term w z b term))
    (hu : Derives Γ (SyntaxLogicalSyntax.singleCode 9 w F U)) (hG : Derives Γ (formulaCode w G z b))
    (hI : Derives Γ (SyntaxNodeSyntax.constructor 2 7 w (SyntaxAtomSyntax.two G U) I)) (hp : Derives Γ (proved test w z b I)) :
    Derives Γ (guardedInstance test w z b F term G) := by
  let E := SyntaxTopFormulaSyntax.instantiated w.castSucc z.castSucc b.castSucc A.castSucc term.castSucc F.castSucc (Fin.last m)
  let Δ := Context.add E (Context.image Formula.raise Γ)
  apply Derives.exE (p := E) (SyntaxTopFormulaExistence.instantiate_exists hZ w z b A term F hw (.conjI (.conjI ht hA) hF))
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have hout := guarded_at_instance (ZFContext.under hZ E) test w.castSucc z.castSucc b.castSucc A.castSucc F.castSucc term.castSucc (Fin.last m) U.castSucc G.castSucc I.castSucc
    (of_eq (omega_rename w Fin.castSucc) (under hw E)) (of_eq (empty_rename z Fin.castSucc) (under hz E)) hE
    (of_eq (SyntaxLogicalSyntax.singleCode_rename 9 w F U Fin.castSucc) (under hu E))
    (of_eq (formulaCode_rename w G z b Fin.castSucc) (under hG E))
    (of_eq (by simp only [Formula.raise, SyntaxNodeSyntax.constructor_rename, SyntaxAtomSyntax.two_map]) (under hI E))
    (of_eq (proved_rename test w z b I Fin.castSucc) (under hp E))
  exact of_eq (guardedInstance_rename test w z b F term G Fin.castSucc).symm hout

/-- Generate the actual instance AND G→instance proof from the actual
G→forall parent. G is not assumed true or proved; no output is supplied. -/
theorem guarded_instantiate {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1) (w z b F term U G I : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) (hU : Derives Γ (formulaCode w U z b))
    (hu : Derives Γ (SyntaxLogicalSyntax.singleCode 9 w F U)) (ht : Derives Γ (SyntaxTermSyntax.term w z b term))
    (hG : Derives Γ (formulaCode w G z b))
    (hI : Derives Γ (SyntaxNodeSyntax.constructor 2 7 w (SyntaxAtomSyntax.two G U) I)) (hp : Derives Γ (proved test w z b I)) :
    Derives Γ (guardedInstance test w z b F term G) := by
  have htypes := Derives.impE (.conjL (FormulaCodeKnownLogical.forall_iff hZ w z b F U hw hu)) hU
  let E := (successor (Fin.last m) z.castSucc).conj (formulaCode w.castSucc F.castSucc (Fin.last m) b.castSucc)
  let Δ := Context.add E (Context.image Formula.raise Γ)
  apply Derives.exE (p := E) (.conjR htypes)
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have hout := guarded_at_scope (ZFContext.under hZ E) test w.castSucc z.castSucc b.castSucc (Fin.last m) F.castSucc term.castSucc U.castSucc G.castSucc I.castSucc
    (of_eq (omega_rename w Fin.castSucc) (under hw E)) (of_eq (empty_rename z Fin.castSucc) (under hz E)) (.conjL hE) (.conjR hE)
    (of_eq (SyntaxTermSyntax.term_rename w z b term Fin.castSucc) (under ht E))
    (of_eq (SyntaxLogicalSyntax.singleCode_rename 9 w F U Fin.castSucc) (under hu E))
    (of_eq (formulaCode_rename w G z b Fin.castSucc) (under hG E))
    (of_eq (by simp only [Formula.raise, SyntaxNodeSyntax.constructor_rename, SyntaxAtomSyntax.two_map]) (under hI E))
    (of_eq (proved_rename test w z b I Fin.castSucc) (under hp E))
  exact of_eq (guardedInstance_rename test w z b F term G Fin.castSucc).symm hout

private def guardedOpeningData {m} (test : Formula 1) (w z b f T x Q term G : Fin m) (v : Fin 3 → Fin m) : Formula m :=
  (ForcingOpenLayout.environment w z b f T (v 0) (v 1)).conj
    ((SyntaxLogicalSyntax.singleCode 9 w (v 2) Q).conj
      ((SyntaxMixedFormulaRecursiveSyntax.check true w x (v 0) (v 1) b f z T (v 2)).conj
        (guardedInstance test w z T (v 2) term G)))
private theorem guardedOpeningData_rename {m l} (test : Formula 1) (w z b f T x Q term G : Fin m) (v : Fin 3 → Fin m) (r : Fin m → Fin l) :
    (guardedOpeningData test w z b f T x Q term G v).rename r = guardedOpeningData test (r w) (r z) (r b) (r f) (r T) (r x) (r Q) (r term) (r G) (fun i => r (v i)) := by
  simp only [guardedOpeningData, Formula.rename, ForcingOpenLayout.environment_rename, SyntaxLogicalSyntax.singleCode_rename,
    SyntaxMixedFormulaRecursiveSyntax.check_rename, guardedInstance_rename]
private def guardedOpeningBody {m} (test : Formula 1) (w z b f T x Q term G : Fin m) : Formula (m+3) :=
  guardedOpeningData test (old 3 w) (old 3 z) (old 3 b) (old 3 f) (old 3 T) (old 3 x) (old 3 Q) (old 3 term) (old 3 G) (slot 3)

/-- SAME actual pointwise environment/body/lift, with a generated original
G→instance proof. The background G is not assumed true or proved. -/
def guardedOpenedInstance {m} (test : Formula 1) (w z b f T x Q term G : Fin m) : Formula m := existsMany 3 (guardedOpeningBody test w z b f T x Q term G)

theorem guardedOpenedInstance_rename {m l} (test : Formula 1) (w z b f T x Q term G : Fin m) (r : Fin m → Fin l) :
    (guardedOpenedInstance test w z b f T x Q term G).rename r = guardedOpenedInstance test (r w) (r z) (r b) (r f) (r T) (r x) (r Q) (r term) (r G) := by
  simp only [guardedOpenedInstance, existsMany_rename, guardedOpeningBody, guardedOpeningData_rename, lift_old, lift_slot]

private theorem intro_guarded_opening {m} {Γ : Context m} (test : Formula 1) (w z b f T x Q term G L S X : Fin m)
    (he : Derives Γ (ForcingOpenLayout.environment w z b f T L S))
    (hc : Derives Γ (SyntaxLogicalSyntax.singleCode 9 w X Q))
    (hx : Derives Γ (SyntaxMixedFormulaRecursiveSyntax.check true w x L S b f z T X))
    (hp : Derives Γ (guardedInstance test w z T X term G)) : Derives Γ (guardedOpenedInstance test w z b f T x Q term G) := by
  apply HornBinderRules.intro_many 3 _ (SetLanguage.args3 L S X)
  exact of_eq (by simp only [guardedOpeningBody, guardedOpeningData_rename, assign_old, assign_slot]; rfl) (.conjI he (.conjI hc (.conjI hx hp)))

private theorem at_guarded_environment {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1) (w z b f T x Q term G I L S : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) (hQ : Derives Γ (formulaCode w Q z T))
    (ht : Derives Γ (SyntaxTermSyntax.term w z T term)) (hG : Derives Γ (formulaCode w G z T))
    (hI : Derives Γ (SyntaxNodeSyntax.constructor 2 7 w (SyntaxAtomSyntax.two G Q) I)) (hp : Derives Γ (proved test w z T I))
    (he : Derives Γ (ForcingOpenLayout.environment w z b f T L S))
    (hs : Derives Γ (ForcingMixedUnary.singleOutput 9 true w L S b f z T x Q)) :
    Derives Γ (guardedOpenedInstance test w z b f T x Q term G) := by
  let E := (SyntaxLogicalSyntax.singleCode 9 w.castSucc (Fin.last m) Q.castSucc).conj
    (SyntaxMixedFormulaRecursiveSyntax.check true w.castSucc x.castSucc L.castSucc S.castSucc b.castSucc f.castSucc z.castSucc T.castSucc (Fin.last m))
  let Δ := Context.add E (Context.image Formula.raise Γ)
  apply Derives.exE (p := E) hs
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have hinst := guarded_instantiate (ZFContext.under hZ E) test w.castSucc z.castSucc T.castSucc (Fin.last m) term.castSucc Q.castSucc G.castSucc I.castSucc
    (of_eq (omega_rename w Fin.castSucc) (under hw E)) (of_eq (empty_rename z Fin.castSucc) (under hz E))
    (of_eq (formulaCode_rename w Q z T Fin.castSucc) (under hQ E)) (.conjL hE)
    (of_eq (SyntaxTermSyntax.term_rename w z T term Fin.castSucc) (under ht E))
    (of_eq (formulaCode_rename w G z T Fin.castSucc) (under hG E))
    (of_eq (by simp only [Formula.raise, SyntaxNodeSyntax.constructor_rename, SyntaxAtomSyntax.two_map]) (under hI E))
    (of_eq (proved_rename test w z T I Fin.castSucc) (under hp E))
  exact of_eq (guardedOpenedInstance_rename test w z b f T x Q term G Fin.castSucc).symm
    (intro_guarded_opening test w.castSucc z.castSucc b.castSucc f.castSucc T.castSucc x.castSucc Q.castSucc term.castSucc G.castSucc L.castSucc S.castSucc (Fin.last m)
      (of_eq (ForcingOpenLayout.environment_rename w z b f T L S Fin.castSucc) (under he E)) (.conjL hE) (.conjR hE) hinst)

/-- Consume a REAL opened forall under a common background, generating the
instance and its actual original proof without assuming the background. -/
theorem guarded_opened_instance {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1) (w z b f T n x Q term G I : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hc : Derives Γ (SyntaxLogicalSyntax.singleCode 9 w x n)) (ho : Derives Γ (ForcingPointwiseCode.opened w z b f T n Q))
    (ht : Derives Γ (SyntaxTermSyntax.term w z T term)) (hG : Derives Γ (formulaCode w G z T))
    (hI : Derives Γ (SyntaxNodeSyntax.constructor 2 7 w (SyntaxAtomSyntax.two G Q) I)) (hp : Derives Γ (proved test w z T I)) :
    Derives Γ (guardedOpenedInstance test w z b f T x Q term G) := by
  have hq := ForcingPointwiseCode.opened_quantified hZ true w z b f T n x Q hw hc ho
  have hQ := ForcingPointwiseCode.opened_type w z b f T n Q ho
  let E := (ForcingOpenLayout.environment (old 2 w) (old 2 z) (old 2 b) (old 2 f) (old 2 T) (slot 2 0) (slot 2 1)).conj
    (ForcingMixedUnary.singleOutput 9 true (old 2 w) (slot 2 0) (slot 2 1) (old 2 b) (old 2 f) (old 2 z) (old 2 T) (old 2 x) (old 2 Q))
  let Δ := Context.add E (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 E _ hq
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have hout := at_guarded_environment (HornBinderRules.zf_body 2 hZ E) test (old 2 w) (old 2 z) (old 2 b) (old 2 f) (old 2 T) (old 2 x) (old 2 Q) (old 2 term) (old 2 G) (old 2 I) (slot 2 0) (slot 2 1)
    (of_eq (omega_rename w (old 2)) (HornBinderRules.under_body 2 hw E)) (of_eq (empty_rename z (old 2)) (HornBinderRules.under_body 2 hz E))
    (of_eq (formulaCode_rename w Q z T (old 2)) (HornBinderRules.under_body 2 hQ E))
    (of_eq (SyntaxTermSyntax.term_rename w z T term (old 2)) (HornBinderRules.under_body 2 ht E))
    (of_eq (formulaCode_rename w G z T (old 2)) (HornBinderRules.under_body 2 hG E))
    (of_eq (by simp only [SyntaxNodeSyntax.constructor_rename, SyntaxAtomSyntax.two_map]) (HornBinderRules.under_body 2 hI E))
    (of_eq (proved_rename test w z T I (old 2)) (HornBinderRules.under_body 2 hp E)) (.conjL hE) (.conjR hE)
  exact of_eq (guardedOpenedInstance_rename test w z b f T x Q term G (old 2)).symm hout

end PPAC.Migration.InternalProofQuantifier
