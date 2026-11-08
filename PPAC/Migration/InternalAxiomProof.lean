import PPAC.Migration.OriginalAxiomTyping
import PPAC.Migration.Internal.ProofAllNodes
import PPAC.Migration.Internal.ProofTreeNodeBackward

/-! The actual theory-axiom base case for internal proof-code transmission.
Consume the unchanged complete original ZF/U unary axiom query, construct the
original theory payload and BOTH node/root traces. No external schema index,
given typed formula, valid trace, proof code, or source quotation is assumed.
The forcing interpretation and final contradiction reduction remain unproved. -/
namespace PPAC.Migration.InternalAxiomProof
open Internal Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)

def axiomQuery {m} (target : Bool) (w c f : Fin m) : Formula m :=
  OriginalAxiomExprQuery.rowQuery (OriginalAxiomCodeTest.test target) 2 0 w (SetLanguage.args2 c f)

def provable {m} (target : Bool) (w f : Fin m) : Formula m := .ex
  ((Formula.mem (Fin.last m) w.castSucc).conj
    (ProofTreeEntrySyntax.root (OriginalAxiomCodeTest.test target) w.castSucc (Fin.last m) f.castSucc))

private theorem query_rename {m n} (target : Bool) (w c f : Fin m) (r : Fin m → Fin n) :
    (axiomQuery target w c f).rename r = axiomQuery target (r w) (r c) (r f) := by
  simp only [axiomQuery, OriginalAxiomExprQuery.rowQuery_rename, ProofTreeEntryFacts.args2_map]

private theorem provable_rename {m n} (target : Bool) (w f : Fin m) (r : Fin m → Fin n) :
    (provable target w f).rename r = provable target (r w) (r f) := by
  simp only [provable, Formula.rename, ProofTreeEntryFacts.root_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

private theorem query_inputs {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (target : Bool) (w c f : Fin m) (hw : Derives Γ (omega w))
    (h : Derives Γ (axiomQuery target w c f)) :
    Derives Γ ((Formula.mem c w).conj (.mem f w)) := by
  let B := (SyntaxNodeSyntax.constructor 2 0 w.castSucc
    (SetLanguage.args2 c.castSucc f.castSucc) (Fin.last m)).conj
    (AxiomTestSyntax.holds (OriginalAxiomCodeTest.test target) (Fin.last m))
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) h
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw B)
  have hr := ProofTreeConstructorFacts.range (ZFContext.under hZ B) 2 0
    w.castSucc (Fin.last m) (SetLanguage.args2 c.castSucc f.castSucc) hw1 (.conjL hB)
  have hi (i : Fin 2) := StructuralListTraceOrder.member_member (ZFContext.under hZ B)
    w.castSucc (SetLanguage.args2 c.castSucc f.castSucc i) (Fin.last m) hw1 hr
      (SyntaxConstructors.child_member (ZFContext.under hZ B) 2 0 w.castSucc
        (SetLanguage.args2 c.castSucc f.castSucc) (Fin.last m) i hw1 (.conjL hB))
  exact .conjI (hi 0) (hi 1)

private theorem assign_axiomFields {m} (env : Fin 3 → Fin m) :
    (fun i => assign 3 env (ProofTheorySyntax.axiomFields (slot 3) i)) =
      ProofTheorySyntax.axiomFields env := by
  funext i
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun t => Fin.elim0 t) j) i <;>
    simp only [ProofTheorySyntax.axiomFields, Fin.cases_zero, Fin.cases_succ, assign_slot]

private theorem root_of_payload {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (target : Bool) (w z c f p : Fin m) (hw : Derives Γ (omega w))
    (hz : Derives Γ (empty z)) (hc : Derives Γ (.mem c w)) (hf : Derives Γ (.mem f w))
    (ht : Derives Γ (FormulaCodeSyntax.formulaCode w f z z))
    (hq : Derives Γ (axiomQuery target w c f))
    (hp : Derives Γ (SyntaxNodeSyntax.constructor 3 1 w (SetLanguage.args3 z f c) p)) :
    Derives Γ (ProofTreeEntrySyntax.root (OriginalAxiomCodeTest.test target) w p f) := by
  let test := OriginalAxiomCodeTest.test target
  let env := SetLanguage.args3 z f c
  have hn : Derives Γ (environmentNat 3 w env) :=
    .conjI (SyntaxNumerals.range hZ 0 w z hw hz) (.conjI hf (.conjI hc HornRuleSyntax.truth_proved))
  have hm : Derives Γ (ProofTheoryNodeSyntax.normalizedMatrix test w z p env) :=
    .conjI hn (.conjI hp (.conjI ht hq))
  have htheory : Derives Γ (ProofTheoryNodeSyntax.normalized test w z p) := by
    apply HornBinderRules.intro_many 3 (ProofTheoryNodeSyntax.normalizedBody test w z p) env
    simpa only [ProofTheoryNodeSyntax.normalizedBody, ProofTheoryNodeSyntax.normalizedMatrix,
      ProofTheorySyntax.specification, Formula.rename,
      environmentNat_rename, SyntaxNodeSyntax.constructor_rename, FormulaCodeSyntax.formulaCode_rename,
      OriginalAxiomExprQuery.rowQuery_rename, assign_old, assign_slot, assign_axiomFields] using hm
  have hall : Derives Γ (ProofAllNodeSyntax.table test w p) := by
    apply Derives.impE (.conjR (ProofAllNodes.table_iff test hZ w z p hw hz))
    exact .disjR (.disjL htheory)
  have hmatrix : Derives Γ (ProofTreeNodeSyntax.matrix test 1 w p env) :=
    .conjI hn (.conjI hp HornRuleSyntax.truth_proved)
  have hnode := ProofTreeNodeBackward.matrix_backward test hZ 1 w p env hw hall hmatrix
  have hroot : Derives Γ (ProofTreeRootSyntax.matrix 1 w p f env) :=
    .conjI hn (.conjI hp (.conjI hz (.eqRefl f)))
  exact ProofTreeRootBackward.matrix_backward test hZ 1 w p f env hw hnode hroot

/-- Uniform production of a complete proof from the ACTUAL full axiom query. -/
theorem from_query {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (target : Bool) (w c f : Fin m) (hw : Derives Γ (omega w))
    (hq : Derives Γ (axiomQuery target w c f)) : Derives Γ (provable target w f) := by
  have hi := query_inputs hZ target w c f hw hq
  have ht := OriginalAxiomTyping.query_typed hZ target w c f hw hq
  let B := (empty (Fin.last m)).conj
    (FormulaCodeSyntax.formulaCode w.castSucc f.castSucc (Fin.last m) (Fin.last m))
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) ht
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hZ1 := ZFContext.under hZ B
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw B)
  have hq1 := of_eq (query_rename target w c f Fin.castSucc) (under hq B)
  have hi1 : Derives Δ ((Formula.mem c.castSucc w.castSucc).conj (.mem f.castSucc w.castSucc)) := under hi B
  let env := SetLanguage.args3 (Fin.last m) f.castSucc c.castSucc
  have he := SyntaxConstructors.exists_constructor hZ1 3 1 w.castSucc env hw1
    (SyntaxForestSyntax.intro_inputs 3 w.castSucc env (fun i =>
      Fin.cases (SyntaxNumerals.range hZ1 0 w.castSucc (Fin.last m) hw1 (.conjL hB))
        (Fin.cases (.conjR hi1) (Fin.cases (.conjL hi1) (fun t => Fin.elim0 t))) i))
  let C := (Formula.mem (Fin.last (m+1)) w.castSucc.castSucc).conj
    (SyntaxNodeSyntax.constructor 3 1 w.castSucc.castSucc
      (SetLanguage.args3 (Fin.last m).castSucc f.castSucc.castSucc c.castSucc.castSucc) (Fin.last (m+1)))
  let Ξ := Context.add C (Context.image Formula.raise Δ)
  apply Derives.exE (p := C) he
  have hC : Derives Ξ C := .hyp (Or.inl rfl)
  have hw2 := of_eq (omega_rename w.castSucc Fin.castSucc) (under hw1 C)
  have hq2 := of_eq (query_rename target w.castSucc c.castSucc f.castSucc Fin.castSucc) (under hq1 C)
  have hz2 := of_eq (empty_rename (Fin.last m) Fin.castSucc) (under (.conjL hB) C)
  have ht2 := of_eq (FormulaCodeSyntax.formulaCode_rename w.castSucc f.castSucc
    (Fin.last m) (Fin.last m) Fin.castSucc) (under (.conjR hB) C)
  have hi2 : Derives Ξ ((Formula.mem c.castSucc.castSucc w.castSucc.castSucc).conj
    (.mem f.castSucc.castSucc w.castSucc.castSucc)) := under hi1 C
  have hr := root_of_payload (ZFContext.under hZ1 C) target w.castSucc.castSucc
    (Fin.last m).castSucc c.castSucc.castSucc f.castSucc.castSucc (Fin.last (m+1))
    hw2 hz2 (.conjL hi2) (.conjR hi2) ht2 hq2 (.conjR hC)
  have ho : Derives Ξ (provable target w.castSucc.castSucc f.castSucc.castSucc) := by
    apply Derives.exI (Fin.last (m+1))
    exact of_eq (by simp only [Formula.instantiate, Formula.rename, ProofTreeEntryFacts.root_rename,
      Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI (.conjL hC) hr)
  exact of_eq (by simp only [Formula.raise, provable_rename]) ho

def sentence {m} (target : Bool) (w c f : Fin m) : Source.Sentence :=
  ((omega w).imp ((axiomQuery target w c f).imp (provable target w f))).close

theorem kernel_certificate {m} (target : Bool) (w c f : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (sentence target w c f)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  exact from_query (ZFContext.add (ZFContext.add (ZFContext.source_ZF m) _) _)
    target w c f (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

end PPAC.Migration.InternalAxiomProof
