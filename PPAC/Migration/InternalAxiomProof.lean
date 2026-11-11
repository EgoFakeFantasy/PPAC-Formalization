import PPAC.Migration.OriginalAxiomTyping
import PPAC.Migration.Internal.ProofAllNodes
import PPAC.Migration.Internal.ProofTreeNodeBackward
import PPAC.Migration.SchemaAxiomQuotation
import PPAC.Migration.Internal.ProjectCompilerSourceValid

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


private theorem from_table {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (target : Bool) (w c f : Fin m) (hw : Derives Γ (omega w))
    (hc : Derives Γ (.mem c w)) (hf : Derives Γ (.mem f w))
    (ht : Derives Γ (OriginalAxiomCodeTest.table target w c f)) :
    Derives Γ (provable target w f) := by
  let B := (Formula.mem (slot 1 0) (old 1 w)).conj
    (SyntaxNodeSyntax.constructor 2 0 (old 1 w) (SetLanguage.args2 (old 1 c) (old 1 f)) (slot 1 0))
  let Δ := Context.add B (raisedContext 1 Γ)
  apply HornBinderRules.eliminate_many 1 B _
    (SyntaxConstructors.exists_constructor hZ 2 0 w (SetLanguage.args2 c f) hw
      (SyntaxForestSyntax.intro_inputs 2 w (SetLanguage.args2 c f) (fun i =>
        Fin.cases hc (fun j => Fin.cases hf (fun u => Fin.elim0 u) j) i)))
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hw1 := of_eq (omega_rename w (old 1)) (HornBinderRules.under_body 1 hw B)
  have ht1 := of_eq (OriginalAxiomCodeTest.table_rename target w c f (old 1))
    (HornBinderRules.under_body 1 ht B)
  have hZ1 := HornBinderRules.zf_body 1 hZ B
  have row := OriginalAxiomCodeTest.intro_row target (old 1 w) (slot 1 0) (old 1 c) (old 1 f) (.conjR hB) ht1
  have tested := Derives.impE (.conjR (OriginalAxiomCodeTest.test_iff_row hZ1 target (old 1 w) (slot 1 0) hw1)) row
  have query : Derives Δ (axiomQuery target (old 1 w) (old 1 c) (old 1 f)) := by
    apply Derives.exI (slot 1 0)
    exact of_eq (by simp only [Formula.instantiate, Formula.rename,
      SyntaxNodeSyntax.constructor_rename, ProofTreeEntryFacts.args2_map, AxiomTestSyntax.holds_rename,
      Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI (.conjR hB) tested)
  exact of_eq (provable_rename target w f (old 1)).symm
    (from_query hZ1 target (old 1 w) (old 1 c) (old 1 f) hw1 query)

/-- Reuse the original row test to turn the quotation of a fixed axiom into
an actual proof in the six-rule tree. The axiom code and its row are generated. -/
theorem from_fixed_quotation {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (target : Bool) (kind : Fin 10) (hk : kind ∈ FixedAxiomTableSyntax.kinds target)
    (w f : Fin m) (hw : Derives Γ (omega w))
    (hq : Derives Γ (PureQuotationSyntax.formula (NativeAxiomCertificateData.fixedFormula kind) w f)) :
    Derives Γ (provable target w f) := by
  let C := (Formula.mem (slot 1 0) (old 1 w)).conj
    (SyntaxNodeSyntax.constructor 0 (NativeAxiomCertificateData.fixedTag kind) (old 1 w) Fin.elim0 (slot 1 0))
  let Δ := Context.add C (raisedContext 1 Γ)
  apply HornBinderRules.eliminate_many 1 C _
    (SyntaxConstructors.exists_constructor hZ 0 (NativeAxiomCertificateData.fixedTag kind) w Fin.elim0 hw
      (SyntaxForestSyntax.intro_inputs 0 w Fin.elim0 (fun i => Fin.elim0 i)))
  have hC : Derives Δ C := .hyp (Or.inl rfl)
  have hw1 := of_eq (omega_rename w (old 1)) (HornBinderRules.under_body 1 hw C)
  have hq1 := of_eq (PureQuotationSyntax.formula_rename _ w f (old 1)) (HornBinderRules.under_body 1 hq C)
  have hZ1 := HornBinderRules.zf_body 1 hZ C
  have hf := OriginalTreeQuotationProperties.tree_range hZ1 _ (old 1 w) (old 1 f) hw1 hq1
  have table := OriginalAxiomCodeTest.intro_fixed target kind hk (old 1 w) (slot 1 0) (old 1 f) (.conjR hC) hq1
  exact of_eq (provable_rename target w f (old 1)).symm
    (from_table hZ1 target (old 1 w) (slot 1 0) (old 1 f) hw1 (.conjL hC) hf table)

private theorem from_schema_result {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (collection : Bool) (w f count z body : Fin m) (scopes : Fin 4 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (.mem count w)) (hz : Derives Γ (empty z))
    (hs : Derives Γ (SchemaIndexSyntax.chain count scopes))
    (hb : Derives Γ (.mem body w)) (hf : Derives Γ (.mem f w))
    (hv : Derives Γ (ProjectSourceCodeSyntax.sourceCode w body
      (SchemaIndexSyntax.sourceScope (SchemaAxiomCompilation.firstSite collection) scopes) z))
    (hr : Derives Γ (SchemaAxiomCompilation.schemaResult collection w count z body f scopes)) :
    Derives Γ (provable false w f) := by
  let L := (Formula.mem (slot 1 0) (old 1 w)).conj (SyntaxNodeSyntax.scalar (old 1 w) (old 1 count) (slot 1 0))
  let Δ := Context.add L (raisedContext 1 Γ)
  have hex : Derives Γ (existsMany 1 L) :=
    SyntaxNodes.exists_node hZ 0 w count Fin.elim0 hw hn
      (SyntaxForestSyntax.intro_inputs 0 w Fin.elim0 (fun i => Fin.elim0 i))
  apply HornBinderRules.eliminate_many 1 L _ hex
  have hL : Derives Δ L := .hyp (Or.inl rfl)
  have hZ1 := HornBinderRules.zf_body 1 hZ L
  have hw1 := of_eq (omega_rename w (old 1)) (HornBinderRules.under_body 1 hw L)
  have hb1 : Derives Δ (.mem (old 1 body) (old 1 w)) := HornBinderRules.under_body 1 hb L
  let tag := OriginalAxiomCodeTest.schemaTag collection
  let xs := SetLanguage.args2 (slot 1 0 : Fin (m+1)) (old 1 body)
  let C := (Formula.mem (slot 1 0) (old 1 (old 1 w))).conj
    (SyntaxNodeSyntax.constructor 2 tag (old 1 (old 1 w))
      (SetLanguage.args2 (old 1 (xs 0)) (old 1 (xs 1))) (slot 1 0))
  let Ξ := Context.add C (raisedContext 1 Δ)
  have hexC : Derives Δ (existsMany 1 C) := by
    exact SyntaxConstructors.exists_constructor hZ1 2 tag (old 1 w) xs hw1
      (SyntaxForestSyntax.intro_inputs 2 (old 1 w) xs (fun i =>
        Fin.cases (.conjL hL) (fun j => Fin.cases hb1 (fun u => Fin.elim0 u) j) i))
  apply HornBinderRules.eliminate_many 1 C _ hexC
  have hC : Derives Ξ C := .hyp (Or.inl rfl)
  have hZ2 := HornBinderRules.zf_body 1 hZ1 C
  let ρ := fun i : Fin m => old 1 (old 1 i)
  let sc := fun i => ρ (scopes i)
  let leaf := old 1 (slot 1 0 : Fin (m+1))
  let cert : Fin (m+1+1) := slot 1 0
  let env : Fin 8 → Fin (m+1+1) :=
    Fin.cases (ρ count) (Fin.cases (ρ body) (Fin.cases (ρ z) (Fin.lastCases leaf sc)))
  have he : (fun i : Fin 4 => env (Fin.natAdd 3 i).castSucc) = sc := by
    funext i
    exact Fin.cases (rfl : env 3 = sc 0)
      (fun j => Fin.cases (rfl : env 4 = sc 1)
        (fun k => Fin.cases (rfl : env 5 = sc 2)
          (fun l => Fin.cases (rfl : env 6 = sc 3) (fun u => Fin.elim0 u) l) k) j) i
  have move {p : Formula m} (hp : Derives Γ p) : Derives Ξ (p.rename ρ) :=
    of_eq (rename_comp _ _ _)
      (HornBinderRules.under_body 1 (HornBinderRules.under_body 1 hp L) C)
  have hw2 := of_eq (omega_rename w ρ) (move hw)
  have hs2 := of_eq (SchemaIndexSyntax.chain_rename count scopes ρ) (move hs)
  have hv2 : Derives Ξ (ProjectSourceCodeSyntax.sourceCode (ρ w) (ρ body)
      (SchemaIndexSyntax.sourceScope (SchemaAxiomCompilation.firstSite collection) sc) (ρ z)) :=
    of_eq (by simp only [ProjectSourceCodeSyntax.sourceCode_rename, sc, SchemaIndexSyntax.sourceScope_map]) (move hv)
  have hr2 := of_eq (SchemaAxiomCompilation.schemaResult_rename collection w count z body f scopes ρ) (move hr)
  have hl : Derives Ξ (SyntaxNodeSyntax.scalar (ρ w) (ρ count) leaf) :=
    of_eq (SyntaxNodeSyntax.scalar_rename (old 1 w) (old 1 count) (slot 1 0) (old 1))
      (HornBinderRules.under_body 1 (.conjR hL) C)
  have matrix : Derives Ξ (OriginalAxiomCodeTest.schemaMatrix collection (ρ w) cert (ρ f) env) := by
    unfold OriginalAxiomCodeTest.schemaMatrix
    rw [he]
    exact .conjI (move hn) (.conjI (of_eq (empty_rename z ρ) (move hz)) (.conjI hs2
      (.conjI hl (.conjI (.conjR hC) (.conjI hv2 hr2)))))
  have table := OriginalAxiomCodeTest.intro_schema_table false collection (ρ w) cert (ρ f)
    (OriginalAxiomCodeTest.intro_schema collection (ρ w) cert (ρ f) env matrix)
  exact of_eq (by simp only [provable_rename, ρ])
    (from_table hZ2 false (ρ w) cert (ρ f) hw2 (.conjL hC) (move hf) table)

open YesMetaZFC.SetTheory.Definitional.Project (fo_formula)
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
attribute [local implicit_reducible] YesMetaZFC.SetTheory.signature

private theorem schema_source_valid {m depth} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (input : YesMetaZFC.SetTheory.Definitional.Project.Formula 1 depth) (hc : input.FreeClosed)
    (w b z raw : Fin m) (hw : Derives Γ (omega w)) (hb : Derives Γ (SyntaxNumeralSyntax.numeral depth b))
    (hz : Derives Γ (empty z))
    (hr : Derives Γ (OriginalTreeQuotationSyntax.tree (ProjectEncode.formula input) w raw)) :
    Derives Γ (ProjectSourceCodeSyntax.sourceCode w raw b z) := by
  let Q := (Formula.mem (slot 1 0) (old 1 w)).conj
    (PureQuotationSyntax.formula (fo_formula input hc) (old 1 w) (slot 1 0))
  let Δ := Context.add Q (raisedContext 1 Γ)
  have hex : Derives Γ (existsMany 1 Q) :=
    OriginalTreeQuotationExistence.tree_exists hZ (PureSyntaxQuotation.formulaTree (fo_formula input hc)) w hw
  apply HornBinderRules.eliminate_many 1 Q _ hex
  have hQ : Derives Δ Q := .hyp (Or.inl rfl)
  have hZ1 := HornBinderRules.zf_body 1 hZ Q
  have hw1 := of_eq (omega_rename w (old 1)) (HornBinderRules.under_body 1 hw Q)
  have hb1 := of_eq (SyntaxNumeralSyntax.numeral_rename depth b (old 1)) (HornBinderRules.under_body 1 hb Q)
  have hz1 := of_eq (empty_rename z (old 1)) (HornBinderRules.under_body 1 hz Q)
  have hr1 := of_eq (OriginalTreeQuotationSyntax.tree_rename _ w raw (old 1)) (HornBinderRules.under_body 1 hr Q)
  have hcomp := ProjectCompilerQuotation.construct hZ1 input hc
    (old 1 w) (old 1 b) (old 1 z) (old 1 raw) (slot 1 0) hw1 hb1 hz1 hr1 (.conjR hQ)
  exact of_eq (ProjectSourceCodeSyntax.sourceCode_rename w raw b z (old 1)).symm
    (ProjectCompilerSourceValid.valid_input hZ1 _ _ _ _ _ hw1
      (SyntaxNumerals.range hZ1 0 _ _ hw1 hz1) hcomp)

private theorem from_schema_quotation {m n} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (collection : Bool) (input : YesMetaZFC.SetTheory.Definitional.Project.Formula 1 (if collection then n+2 else n+1))
    (hc : input.FreeClosed) (φ : YesMetaZFC.Logic.FirstOrder.Sentence ℒ)
    (build : ∀ {l} {Δ : Context l}, ZFContext.Evidence Δ → ∀ (w count z raw f : Fin l) (sc : Fin 4 → Fin l),
      Derives Δ (omega w) → Derives Δ (SyntaxNumeralSyntax.numeral n count) → Derives Δ (empty z) →
      Derives Δ (SchemaIndexSyntax.chain count sc) →
      Derives Δ (OriginalTreeQuotationSyntax.tree (ProjectEncode.formula input) w raw) →
      Derives Δ (ProjectSourceCodeSyntax.sourceCode w raw
        (SchemaIndexSyntax.sourceScope (SchemaAxiomCompilation.firstSite collection) sc) z) →
      Derives Δ (PureQuotationSyntax.formula φ w f) →
      Derives Δ (SchemaAxiomCompilation.schemaResult collection w count z raw f sc))
    (w f : Fin m) (hw : Derives Γ (omega w)) (hq : Derives Γ (PureQuotationSyntax.formula φ w f)) :
    Derives Γ (provable false w f) := by
  let site := SchemaAxiomCompilation.firstSite collection
  let N := (Formula.mem (slot 1 0) (old 1 w)).conj (SyntaxNumeralSyntax.numeral n (slot 1 0))
  let Γ1 := Context.add N (raisedContext 1 Γ)
  have hexN : Derives Γ (existsMany 1 N) := SyntaxNumerals.exists_numeral hZ n w hw
  apply HornBinderRules.eliminate_many 1 N _ hexN
  have hN : Derives Γ1 N := .hyp (Or.inl rfl)
  have hZ1 := HornBinderRules.zf_body 1 hZ N
  have hw1 := of_eq (omega_rename w (old 1)) (HornBinderRules.under_body 1 hw N)
  let S := SchemaIndexSyntax.stateBody site (old 1 w) (slot 1 0)
  let Γ2 := Context.add S (raisedContext 5 Γ1)
  have hexS : Derives Γ1 (existsMany 5 S) := SchemaIndexScopes.exists_state hZ1 site _ _ hw1 (.conjL hN)
  apply HornBinderRules.eliminate_many 5 S _ hexS
  have hS : Derives Γ2 S := .hyp (Or.inl rfl)
  have hZ2 := HornBinderRules.zf_body 5 hZ1 S
  let w2 := old 5 (old 1 w)
  let n2 := old 5 (slot 1 0 : Fin (m+1))
  let sc2 : Fin 4 → Fin (m+1+5) := fun i => slot 5 i.castSucc
  have hw2 := of_eq (omega_rename (old 1 w) (old 5)) (HornBinderRules.under_body 5 hw1 S)
  have hn2 := of_eq (SyntaxNumeralSyntax.numeral_rename n (slot 1 0) (old 5))
    (HornBinderRules.under_body 5 (.conjR hN) S)
  have hs2 : Derives Γ2 (SchemaIndexSyntax.chain n2 sc2) := .conjL hS
  let inputTree := ProjectEncode.formula input
  let R := (Formula.mem (slot 1 0) (old 1 w2)).conj
    (OriginalTreeQuotationSyntax.tree inputTree (old 1 w2) (slot 1 0))
  let Γ3 := Context.add R (raisedContext 1 Γ2)
  have hexR : Derives Γ2 (existsMany 1 R) := OriginalTreeQuotationExistence.tree_exists hZ2 inputTree w2 hw2
  apply HornBinderRules.eliminate_many 1 R _ hexR
  have hR : Derives Γ3 R := .hyp (Or.inl rfl)
  have hZ3 := HornBinderRules.zf_body 1 hZ2 R
  have hw3 := of_eq (omega_rename w2 (old 1)) (HornBinderRules.under_body 1 hw2 R)
  let O := (Formula.mem (slot 1 0) (old 1 (old 1 w2))).conj (empty (slot 1 0))
  let Ξ := Context.add O (raisedContext 1 Γ3)
  have hexO : Derives Γ3 (existsMany 1 O) := SyntaxNumerals.exists_numeral hZ3 0 _ hw3
  apply HornBinderRules.eliminate_many 1 O _ hexO
  have hO : Derives Ξ O := .hyp (Or.inl rfl)
  have hZ4 := HornBinderRules.zf_body 1 hZ3 O
  let ρ := fun i : Fin m => old 1 (old 1 (old 5 (old 1 i)))
  let count := old 1 (old 1 n2)
  let raw := old 1 (slot 1 0 : Fin (m+1+5+1))
  let z : Fin (m+1+5+1+1) := slot 1 0
  let sc := fun i => old 1 (old 1 (sc2 i))
  have hw4 := of_eq (omega_rename _ (old 1)) (HornBinderRules.under_body 1 hw3 O)
  have hn4 : Derives Ξ (SyntaxNumeralSyntax.numeral n count) := by
    simpa only [SyntaxNumeralSyntax.numeral_rename] using
      (HornBinderRules.under_body 1 (HornBinderRules.under_body 1 hn2 R) O)
  have hs4 : Derives Ξ (SchemaIndexSyntax.chain count sc) := by
    simpa only [SchemaIndexSyntax.chain_rename] using
      (HornBinderRules.under_body 1 (HornBinderRules.under_body 1 hs2 R) O)
  have hr4 := of_eq (OriginalTreeQuotationSyntax.tree_rename inputTree _ _ (old 1))
    (HornBinderRules.under_body 1 (.conjR hR) O)
  have hq4 : Derives Ξ (PureQuotationSyntax.formula φ (ρ w) (ρ f)) := by
    simpa only [PureQuotationSyntax.formula_rename] using
      (HornBinderRules.under_body 1 (HornBinderRules.under_body 1
        (HornBinderRules.under_body 5 (HornBinderRules.under_body 1 hq N) S) R) O)
  have hd : Derives Ξ (SyntaxNumeralSyntax.numeral (if collection then n+2 else n+1)
      (SchemaIndexSyntax.sourceScope site sc)) := by
    have first := SyntaxNumeralSyntax.intro_succ n (sc 0) count hn4 (.conjL hs4)
    cases collection
    · exact first
    · exact SyntaxNumeralSyntax.intro_succ (n+1) (sc 1) (sc 0) first (.conjL (.conjR hs4))
  have hv := schema_source_valid hZ4 input hc (ρ w) (SchemaIndexSyntax.sourceScope site sc) z raw
    hw4 hd (.conjR hO) hr4
  have result := build hZ4 (ρ w) count z raw (ρ f) sc hw4 hn4 (.conjR hO) hs4 hr4 hv hq4
  have hf := OriginalTreeQuotationProperties.tree_range hZ4 _ (ρ w) (ρ f) hw4 hq4
  have hraw : Derives Ξ (.mem raw (ρ w)) := HornBinderRules.under_body 1 (.conjL hR) O
  have out := from_schema_result hZ4 collection (ρ w) (ρ f) count z raw sc hw4
    (SyntaxNumerals.range hZ4 n _ _ hw4 hn4) (.conjR hO) hs4 hraw hf hv result
  exact of_eq (by simp only [provable_rename, ρ]) out

/-- Quote any native ZF axiom instance into an actual leaf of the original
six-rule proof tree. The schema compiler and its original certificate row
are used for Separation and Collection. -/
theorem from_native_quotation {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (φ : YesMetaZFC.Logic.FirstOrder.Sentence ℒ) (hφ : nativeZF φ)
    (w f : Fin m) (hw : Derives Γ (omega w))
    (hq : Derives Γ (PureQuotationSyntax.formula φ w f)) : Derives Γ (provable false w f) := by
  obtain ⟨cert, rfl⟩ := NativeAxiomCertificateData.complete hφ
  cases cert with
  | extensionality => exact from_fixed_quotation hZ false 0 (by decide) w f hw hq
  | emptySet => exact from_fixed_quotation hZ false 1 (by decide) w f hw hq
  | pairing => exact from_fixed_quotation hZ false 2 (by decide) w f hw hq
  | union => exact from_fixed_quotation hZ false 3 (by decide) w f hw hq
  | powerSet => exact from_fixed_quotation hZ false 4 (by decide) w f hw hq
  | infinity => exact from_fixed_quotation hZ false 5 (by decide) w f hw hq
  | foundation => exact from_fixed_quotation hZ false 6 (by decide) w f hw hq
  | separation schema =>
    exact from_schema_quotation hZ false schema.body schema.freeClosed _
      (fun hZ w count z raw f sc hw hn hz hs hr hv hq =>
        .impE (.conjR (SchemaAxiomQuotation.separation_iff hZ schema w count z raw f sc hw hn hz hs hr hv)) hq) w f hw hq
  | collection schema =>
    exact from_schema_quotation hZ true schema.body schema.freeClosed _
      (fun hZ w count z raw f sc hw hn hz hs hr hv hq =>
        .impE (.conjR (SchemaAxiomQuotation.collection_iff hZ schema w count z raw f sc hw hn hz hs hr hv)) hq) w f hw hq

theorem native_quotation_kernel_certificate {m} (φ : YesMetaZFC.Logic.FirstOrder.Sentence ℒ) (hφ : nativeZF φ)
    (w f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
      (Translation.sentence (((omega w).conj (PureQuotationSyntax.formula φ w f)).imp (provable false w f)).close) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  let H := (omega w).conj (PureQuotationSyntax.formula φ w f)
  have h : Derives (Context.add H (SetLanguage.ZF.at m)) H := .hyp (Or.inl rfl)
  exact from_native_quotation (ZFContext.add (ZFContext.source_ZF m) _) φ hφ w f (.conjL h) (.conjR h)

end PPAC.Migration.InternalAxiomProof
