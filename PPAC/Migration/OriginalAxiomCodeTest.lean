import PPAC.Migration.SchemaAxiomUnique
import PPAC.Migration.Internal.FixedAxiomTableSyntax

/-! Original ZF/U certificate trees and the actual six-rule axiom-row interface.
The code here is the Quine value of the ORIGINAL certificate tree, not the
NatPacket byte serialization used by the older fixed-packet partial test.
All counts, bodies, scopes and compiler witnesses remain internal objects.
This module does not assert the final internal Proof/Con reduction. -/
namespace PPAC.Migration.OriginalAxiomCodeTest
open Internal Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)
open NativeAxiomCertificateData (fixedFormula fixedTag)

def schemaTag (collection : Bool) : Nat := if collection then 9 else 8

def fixedBranch {m} (kind : Fin 10) (w certificate formula : Fin m) : Source.Formula m :=
  (SyntaxNodeSyntax.constructor 0 (fixedTag kind) w Fin.elim0 certificate).conj
    (PureQuotationSyntax.formula (fixedFormula kind) w formula)

def fixedTable {m} (target : Bool) (w certificate formula : Fin m) : Source.Formula m :=
  LogicalAllPatterns.disjoin ((FixedAxiomTableSyntax.kinds target).map (fun kind => fixedBranch kind w certificate formula))

/-- env: count, raw body, empty zero, four original scope successors, count leaf. -/
def schemaMatrix {m} (collection : Bool) (w certificate formula : Fin m) (env : Fin 8 → Fin m) : Source.Formula m :=
  (Source.Formula.mem (env 0) w).conj
    ((empty (env 2)).conj
      ((SchemaIndexSyntax.chain (env 0) (fun i => env (Fin.natAdd 3 i).castSucc)).conj
        ((SyntaxNodeSyntax.scalar w (env 0) (env 7)).conj
          ((SyntaxNodeSyntax.constructor 2 (schemaTag collection) w (SetLanguage.args2 (env 7) (env 1)) certificate).conj
            ((ProjectSourceCodeSyntax.sourceCode w (env 1)
              (SchemaIndexSyntax.sourceScope (SchemaAxiomCompilation.firstSite collection) (fun i => env (Fin.natAdd 3 i).castSucc)) (env 2)).conj
                (SchemaAxiomCompilation.schemaResult collection w (env 0) (env 2) (env 1) formula (fun i => env (Fin.natAdd 3 i).castSucc)))))))

def schemaBody {m} (collection : Bool) (w certificate formula : Fin m) : Source.Formula (m+8) :=
  schemaMatrix collection (old 8 w) (old 8 certificate) (old 8 formula) (slot 8)

def schemaBranch {m} (collection : Bool) (w certificate formula : Fin m) : Source.Formula m :=
  existsMany 8 (schemaBody collection w certificate formula)

def table {m} (target : Bool) (w certificate formula : Fin m) : Source.Formula m :=
  (fixedTable target w certificate formula).disj
    ((schemaBranch false w certificate formula).disj (schemaBranch true w certificate formula))

def rowBody {m} (target : Bool) (w row : Fin m) : Source.Formula (m+2) :=
  (SyntaxNodeSyntax.constructor 2 0 (old 2 w) (SetLanguage.args2 (slot 2 0) (slot 2 1)) (old 2 row)).conj
    (table target (old 2 w) (slot 2 0) (slot 2 1))

def rowTest {m} (target : Bool) (w row : Fin m) : Source.Formula m := existsMany 2 (rowBody target w row)

def test (target : Bool) : Source.Formula 1 := .ex
  ((omega (Fin.last 1)).conj (rowTest target (Fin.last 1) (0 : Fin 1).castSucc))

theorem fixedBranch_rename {m l} (kind : Fin 10) (w certificate formula : Fin m) (r : Fin m → Fin l) :
    (fixedBranch kind w certificate formula).rename r = fixedBranch kind (r w) (r certificate) (r formula) := by
  simp only [fixedBranch, Formula.rename, SyntaxNodeSyntax.constructor_rename, PureQuotationSyntax.formula_rename]
  rfl

theorem fixedTable_rename {m l} (target : Bool) (w certificate formula : Fin m) (r : Fin m → Fin l) :
    (fixedTable target w certificate formula).rename r = fixedTable target (r w) (r certificate) (r formula) := by
  unfold fixedTable
  rw [LogicalTableRenaming.disjoin_rename, List.map_map]
  apply congrArg LogicalAllPatterns.disjoin
  apply List.map_congr_left
  intro kind _
  exact fixedBranch_rename kind w certificate formula r

theorem schemaMatrix_rename {m l} (collection : Bool) (w certificate formula : Fin m) (env : Fin 8 → Fin m) (r : Fin m → Fin l) :
    (schemaMatrix collection w certificate formula env).rename r = schemaMatrix collection (r w) (r certificate) (r formula) (fun i => r (env i)) := by
  simp only [schemaMatrix, Formula.rename, empty_rename, SchemaIndexSyntax.chain_rename, SyntaxNodeSyntax.scalar_rename,
    SyntaxNodeSyntax.constructor_rename, ProofTreeEntryFacts.args2_map, ProjectSourceCodeSyntax.sourceCode_rename,
    SchemaAxiomCompilation.schemaResult_rename, SchemaIndexSyntax.sourceScope_map]

theorem schemaBranch_rename {m l} (collection : Bool) (w certificate formula : Fin m) (r : Fin m → Fin l) :
    (schemaBranch collection w certificate formula).rename r = schemaBranch collection (r w) (r certificate) (r formula) := by
  simp only [schemaBranch, schemaBody, existsMany_rename, schemaMatrix_rename, lift_old, lift_slot]

theorem table_rename {m l} (target : Bool) (w certificate formula : Fin m) (r : Fin m → Fin l) :
    (table target w certificate formula).rename r = table target (r w) (r certificate) (r formula) := by
  simp only [table, Formula.rename, fixedTable_rename, schemaBranch_rename]

theorem rowTest_rename {m l} (target : Bool) (w row : Fin m) (r : Fin m → Fin l) :
    (rowTest target w row).rename r = rowTest target (r w) (r row) := by
  simp only [rowTest, rowBody, existsMany_rename, Formula.rename, SyntaxNodeSyntax.constructor_rename,
    ProofTreeEntryFacts.args2_map, table_rename, lift_old, lift_slot]

theorem test_at {m} (target : Bool) (row : Fin m) :
    AxiomTestSyntax.holds (test target) row = .ex
      ((omega (Fin.last m)).conj (rowTest target (Fin.last m) row.castSucc)) := by
  simp only [AxiomTestSyntax.holds, test, Formula.rename, omega_rename, rowTest_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

/-- Exact original certificate envelope, before optional byte serialization. -/
theorem separation_certificate_shape {n : Nat} (s : YesMetaZFC.SetTheory.Definitional.Project.UnarySchema n) :
    NativeAxiomCertificateData.encode (.separation s) =
      .node 8 [YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.leaf n, YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.ProjectEncode.formula s.body] := rfl

theorem collection_certificate_shape {n : Nat} (s : YesMetaZFC.SetTheory.Definitional.Project.BinarySchema n) :
    NativeAxiomCertificateData.encode (.collection s) =
      .node 9 [YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.leaf n, YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.ProjectEncode.formula s.body] := rfl

theorem intro_schema {m} {Γ : Context m} (collection : Bool) (w c f : Fin m) (env : Fin 8 → Fin m)
    (h : Derives Γ (schemaMatrix collection w c f env)) : Derives Γ (schemaBranch collection w c f) := by
  apply HornBinderRules.intro_many 8 (schemaBody collection w c f) env
  exact of_eq (by simp only [schemaBody, schemaMatrix_rename, assign_old, assign_slot]) h

theorem intro_fixed {m} {Γ : Context m} (target : Bool) (kind : Fin 10) (hk : kind ∈ FixedAxiomTableSyntax.kinds target)
    (w c f : Fin m) (hc : Derives Γ (SyntaxNodeSyntax.constructor 0 (fixedTag kind) w Fin.elim0 c))
    (hf : Derives Γ (PureQuotationSyntax.formula (fixedFormula kind) w f)) : Derives Γ (table target w c f) :=
  .disjL (ProofTreeRootSyntax.disjoin_intro _ _ (List.mem_map.mpr ⟨kind,hk,rfl⟩) (.conjI hc hf))

theorem intro_schema_table {m} {Γ : Context m} (target collection : Bool) (w c f : Fin m)
    (h : Derives Γ (schemaBranch collection w c f)) : Derives Γ (table target w c f) := by
  cases collection
  · exact .disjR (.disjL h)
  · exact .disjR (.disjR h)

theorem table_inputs {m} {Γ : Context m} (target : Bool) (w c f d g : Fin m)
    (hc : Derives Γ (.equal c d)) (hf : Derives Γ (.equal f g)) (ht : Derives Γ (table target w c f)) :
    Derives Γ (table target w d g) := by
  let P := table target w.castSucc (Fin.last m) f.castSucc
  let Q := table target w.castSucc d.castSucc (Fin.last m)
  have hP0 : P.instantiate c = table target w c f := by simp only [P, Formula.instantiate, table_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have hP1 : P.instantiate d = table target w d f := by simp only [P, Formula.instantiate, table_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have hQ0 : Q.instantiate f = table target w d f := by simp only [Q, Formula.instantiate, table_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have hQ1 : Q.instantiate g = table target w d g := by simp only [Q, Formula.instantiate, table_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact of_eq hQ1 (Derives.eqSubst Q hf (of_eq hQ0.symm (of_eq hP1 (Derives.eqSubst P hc (of_eq hP0.symm ht)))))

theorem intro_row {m} {Γ : Context m} (target : Bool) (w row c f : Fin m)
    (hr : Derives Γ (SyntaxNodeSyntax.constructor 2 0 w (SetLanguage.args2 c f) row))
    (ht : Derives Γ (table target w c f)) : Derives Γ (rowTest target w row) := by
  apply HornBinderRules.intro_many 2 (rowBody target w row) (SetLanguage.args2 c f)
  exact of_eq (by simp only [rowBody, Formula.rename, SyntaxNodeSyntax.constructor_rename, table_rename,
    ProofTreeEntryFacts.args2_map, assign_old, assign_slot]; rfl) (.conjI hr ht)

/-- ALL internal row/certificate/formula codes, not just quoted standard rows. -/
theorem row_at {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (target : Bool) (w row c f : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (SyntaxNodeSyntax.constructor 2 0 w (SetLanguage.args2 c f) row)) :
    Derives Γ ((rowTest target w row).iff (table target w c f)) := by
  apply Derives.conjI
  · apply Derives.impI
    let E := rowTest target w row
    let B := rowBody target w row
    let Δ := Context.add B (raisedContext 2 (Context.add E Γ))
    have hE : Derives (Context.add E Γ) E := .hyp (Or.inl rfl)
    apply HornBinderRules.eliminate_many 2 B _ hE
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have hZ2 := HornBinderRules.zf_body 2 (ZFContext.add hZ E) B
    have hw2 := of_eq (omega_rename w (old 2)) (HornBinderRules.under_body 2 (add hw E) B)
    have hr2 : Derives Δ (SyntaxNodeSyntax.constructor 2 0 (old 2 w) (SetLanguage.args2 (old 2 c) (old 2 f)) (old 2 row)) :=
      of_eq (by simp only [SyntaxNodeSyntax.constructor_rename, ProofTreeEntryFacts.args2_map]) (HornBinderRules.under_body 2 (add hr E) B)
    have e0 := ProofTreeConstructorFacts.field_equal hZ2 2 0 (old 2 w) (old 2 row)
      (SetLanguage.args2 (slot 2 0) (slot 2 1)) (SetLanguage.args2 (old 2 c) (old 2 f)) 0 hw2 (.conjL hB) hr2
    have e1 := ProofTreeConstructorFacts.field_equal hZ2 2 0 (old 2 w) (old 2 row)
      (SetLanguage.args2 (slot 2 0) (slot 2 1)) (SetLanguage.args2 (old 2 c) (old 2 f)) 1 hw2 (.conjL hB) hr2
    exact of_eq (table_rename target w c f (old 2)).symm
      (table_inputs target (old 2 w) (slot 2 0) (slot 2 1) (old 2 c) (old 2 f) e0 e1 (.conjR hB))
  · apply Derives.impI
    exact intro_row target w row c f (add hr _) (.hyp (Or.inl rfl))

theorem row_omega_subst {m} {Γ : Context m} (target : Bool) (w v row : Fin m)
    (he : Derives Γ (.equal w v)) (hr : Derives Γ (rowTest target w row)) : Derives Γ (rowTest target v row) := by
  let P := rowTest target (Fin.last m) row.castSucc
  have h0 : P.instantiate w = rowTest target w row := by simp only [P, Formula.instantiate, rowTest_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have h1 : P.instantiate v = rowTest target v row := by simp only [P, Formula.instantiate, rowTest_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact of_eq h1 (Derives.eqSubst P he (of_eq h0.symm hr))

theorem test_iff_row {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (target : Bool) (w row : Fin m)
    (hw : Derives Γ (omega w)) : Derives Γ ((AxiomTestSyntax.holds (test target) row).iff (rowTest target w row)) := by
  apply Derives.conjI
  · apply Derives.impI
    let E := AxiomTestSyntax.holds (test target) row
    let B := (omega (Fin.last m)).conj (rowTest target (Fin.last m) row.castSucc)
    let Δ := Context.add B (Context.image Formula.raise (Context.add E Γ))
    have hE : Derives (Context.add E Γ) E := .hyp (Or.inl rfl)
    apply Derives.exE (p := B) (of_eq (test_at target row) hE)
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have hw1 := of_eq (omega_rename w Fin.castSucc) (under (add hw E) B)
    have he := OmegaAlgebra.unique (Fin.last m) w.castSucc (ZFContext.arithmetic (ZFContext.under (ZFContext.add hZ E) B)).base.extensionality (.conjL hB) hw1
    exact of_eq (by simp only [Formula.raise, rowTest_rename]) (row_omega_subst target (Fin.last m) w.castSucc row.castSucc he (.conjR hB))
  · apply Derives.impI
    apply of_eq (test_at target row).symm
    apply Derives.exI w
    exact of_eq (by simp only [Formula.instantiate, Formula.rename, omega_rename, rowTest_rename,
      Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI (add hw _) (.hyp (Or.inl rfl)))

theorem schema_wrong_tag {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (collection : Bool)
    (k tag : Nat) (hne : tag ≠ schemaTag collection) (w c f : Fin m) (xs : Fin k → Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (SyntaxNodeSyntax.constructor k tag w xs c)) :
    Derives Γ (schemaBranch collection w c f).neg := by
  apply Derives.impI
  let E := schemaBranch collection w c f
  let B := schemaBody collection w c f
  let Δ := Context.add B (raisedContext 8 (Context.add E Γ))
  have hE : Derives (Context.add E Γ) E := .hyp (Or.inl rfl)
  apply HornBinderRules.eliminate_many 8 B _ hE
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hZ8 := HornBinderRules.zf_body 8 (ZFContext.add hZ E) B
  have hw8 := of_eq (omega_rename w (old 8)) (HornBinderRules.under_body 8 (add hw E) B)
  have hc8 := of_eq (SyntaxNodeSyntax.constructor_rename k tag w xs c (old 8)) (HornBinderRules.under_body 8 (add hc E) B)
  exact SyntaxConstructors.disjoint hZ8 k 2 tag (schemaTag collection) hne (old 8 w)
    (fun i => old 8 (xs i)) (SetLanguage.args2 (slot 8 7) (slot 8 1)) (old 8 c) hw8 hc8
      (.conjL (.conjR (.conjR (.conjR (.conjR hB)))))

theorem fixedTag_ne_schema (kind : Fin 10) (collection : Bool) : fixedTag kind ≠ schemaTag collection := by
  cases collection <;> simp only [schemaTag, Bool.false_eq_true, ↓reduceIte] <;> unfold fixedTag <;> split <;> omega

theorem fixedTable_at {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (target : Bool) (kind : Fin 10)
    (hk : kind ∈ FixedAxiomTableSyntax.kinds target) (w c f : Fin m) (hw : Derives Γ (omega w))
    (hc : Derives Γ (SyntaxNodeSyntax.constructor 0 (fixedTag kind) w Fin.elim0 c)) :
    Derives Γ ((fixedTable target w c f).iff (PureQuotationSyntax.formula (fixedFormula kind) w f)) := by
  apply Derives.conjI
  · apply Derives.impI
    let E := fixedTable target w c f
    have hE : Derives (Context.add E Γ) E := .hyp (Or.inl rfl)
    apply ProofTreeRootSyntax.disjoin_elim _ _ hE
    intro q hq
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hq
    apply Derives.impI
    have hB : Derives (Context.add (fixedBranch j w c f) (Context.add E Γ)) (fixedBranch j w c f) := .hyp (Or.inl rfl)
    by_cases he : j = kind
    · subst j
      exact .conjR hB
    · exact .botE (SyntaxConstructors.disjoint (ZFContext.add (ZFContext.add hZ E) _) 0 0 (fixedTag j) (fixedTag kind)
        (fun h => he (NativeAxiomCertificateData.fixedTag_injective h)) w Fin.elim0 Fin.elim0 c
          (add (add hw E) _) (.conjL hB) (add (add hc E) _))
  · apply Derives.impI
    exact ProofTreeRootSyntax.disjoin_intro _ _ (List.mem_map.mpr ⟨kind,hk,rfl⟩) (.conjI (add hc _) (.hyp (Or.inl rfl)))

theorem table_at_fixed {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (target : Bool) (kind : Fin 10)
    (hk : kind ∈ FixedAxiomTableSyntax.kinds target) (w c f : Fin m) (hw : Derives Γ (omega w))
    (hc : Derives Γ (SyntaxNodeSyntax.constructor 0 (fixedTag kind) w Fin.elim0 c)) :
    Derives Γ ((table target w c f).iff (PureQuotationSyntax.formula (fixedFormula kind) w f)) := by
  have hF := fixedTable_at hZ target kind hk w c f hw hc
  have h0 := schema_wrong_tag hZ false 0 (fixedTag kind) (fixedTag_ne_schema kind false) w c f Fin.elim0 hw hc
  have h1 := schema_wrong_tag hZ true 0 (fixedTag kind) (fixedTag_ne_schema kind true) w c f Fin.elim0 hw hc
  apply Derives.conjI
  · apply Derives.impI
    let E := table target w c f
    have hE : Derives (Context.add E Γ) E := .hyp (Or.inl rfl)
    apply Derives.disjE hE
    · exact .impE (add (add (.conjL hF) E) _) (.hyp (Or.inl rfl))
    · apply Derives.disjE (.hyp (Or.inl rfl))
      · exact .botE (.impE (add (add (add h0 E) _) _) (.hyp (Or.inl rfl)))
      · exact .botE (.impE (add (add (add h1 E) _) _) (.hyp (Or.inl rfl)))
  · apply Derives.impI
    exact intro_fixed target kind hk w c f (add hc _) (.hyp (Or.inl rfl))

theorem reject_choice_table {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (target : Bool)
    (w c f : Fin m) (hw : Derives Γ (omega w))
    (hc : Derives Γ (SyntaxNodeSyntax.constructor 0 7 w Fin.elim0 c)) : Derives Γ (table target w c f).neg := by
  have h0 := schema_wrong_tag hZ false 0 7 (by decide) w c f Fin.elim0 hw hc
  have h1 := schema_wrong_tag hZ true 0 7 (by decide) w c f Fin.elim0 hw hc
  apply Derives.impI
  let E := table target w c f
  have hE : Derives (Context.add E Γ) E := .hyp (Or.inl rfl)
  apply Derives.disjE hE
  · have hF : Derives (Context.add (fixedTable target w c f) (Context.add E Γ)) (fixedTable target w c f) := .hyp (Or.inl rfl)
    apply ProofTreeRootSyntax.disjoin_elim _ _ hF
    intro q hq
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hq
    apply Derives.impI
    have hB : Derives (Context.add (fixedBranch j w c f) (Context.add (fixedTable target w c f) (Context.add E Γ))) (fixedBranch j w c f) := .hyp (Or.inl rfl)
    exact SyntaxConstructors.disjoint (ZFContext.add (ZFContext.add (ZFContext.add hZ E) _) _) 0 0 (fixedTag j) 7
      (NativeAxiomCertificateData.fixedTag_ne_choice j) w Fin.elim0 Fin.elim0 c (add (add (add hw E) _) _)
        (.conjL hB) (add (add (add hc E) _) _)
  · apply Derives.disjE (.hyp (Or.inl rfl))
    · exact .impE (add (add (add h0 E) _) _) (.hyp (Or.inl rfl))
    · exact .impE (add (add (add h1 E) _) _) (.hyp (Or.inl rfl))

def closedCode {m} (w f : Fin m) : Source.Formula m := .ex
  ((empty (Fin.last m)).conj (FormulaCodeSyntax.formulaCode w.castSucc f.castSucc (Fin.last m) (Fin.last m)))

theorem closedCode_rename {m l} (w f : Fin m) (r : Fin m → Fin l) :
    (closedCode w f).rename r = closedCode (r w) (r f) := by
  simp only [closedCode, Formula.rename, empty_rename, FormulaCodeSyntax.formulaCode_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem schemaBranch_typed {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (collection : Bool) (w c f : Fin m)
    (hw : Derives Γ (omega w)) (h : Derives Γ (schemaBranch collection w c f)) : Derives Γ (closedCode w f) := by
  let B := schemaBody collection w c f
  let Δ := Context.add B (raisedContext 8 Γ)
  apply HornBinderRules.eliminate_many 8 B _ h
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hZ8 := HornBinderRules.zf_body 8 hZ B
  have hw8 := of_eq (omega_rename w (old 8)) (HornBinderRules.under_body 8 hw B)
  have ht := SchemaShellTyping.result_type hZ8 collection (old 8 w) (slot 8 0) (slot 8 2) (slot 8 1) (old 8 f)
    (fun i => slot 8 (Fin.natAdd 3 i).castSucc) hw8 (.conjL hB) (.conjL (.conjR hB))
      (.conjL (.conjR (.conjR hB))) (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR hB))))))
  have ho : Derives Δ (closedCode (old 8 w) (old 8 f)) := by
    apply Derives.exI (slot 8 2)
    exact of_eq (by simp only [Formula.instantiate, Formula.rename, empty_rename, FormulaCodeSyntax.formulaCode_rename,
      Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI (.conjL (.conjR hB)) ht)
  exact of_eq (closedCode_rename w f (old 8)).symm ho

/-- This is the actual unary test accepted by the already migrated six-rule kernel. -/
def rowSentence {m} (target : Bool) (w row c f : Fin m) : Source.Sentence :=
  ((omega w).imp ((SyntaxNodeSyntax.constructor 2 0 w (SetLanguage.args2 c f) row).imp
    ((AxiomTestSyntax.holds (test target) row).iff (table target w c f)))).close

theorem row_source_certificate {m} (target : Bool) (w row c f : Fin m) :
    Derives (Source.SetLanguage.ZF.at 0) (rowSentence target w row c f) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let E := SyntaxNodeSyntax.constructor 2 0 w (SetLanguage.args2 c f) row
  let Δ := Context.add E (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := ZFContext.add (ZFContext.add (ZFContext.source_ZF m) _) _
  have hw : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have hr : Derives Δ E := .hyp (Or.inl rfl)
  have h0 := test_iff_row hZ target w row hw
  have h1 := row_at hZ target w row c f hw hr
  apply Derives.conjI
  · apply Derives.impI
    exact .impE (add (.conjL h1) _) (.impE (add (.conjL h0) _) (.hyp (Or.inl rfl)))
  · apply Derives.impI
    exact .impE (add (.conjR h0) _) (.impE (add (.conjR h1) _) (.hyp (Or.inl rfl)))

theorem row_kernel_certificate {m} (target : Bool) (w row c f : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (rowSentence target w row c f)) :=
  ZFReplay.replay (TheoryTransport.sentence (row_source_certificate target w row c f))

private theorem matrix_slot_subst {m} {Γ : Context m} (collection : Bool) (w c f a : Fin m) (env : Fin 8 → Fin m) (i : Fin 8)
    (he : Derives Γ (.equal (env i) a)) (h : Derives Γ (schemaMatrix collection w c f env)) :
    Derives Γ (schemaMatrix collection w c f (fun j => if j = i then a else env j)) := by
  let P := schemaMatrix collection w.castSucc c.castSucc f.castSucc
    (fun j => if j = i then Fin.last m else (env j).castSucc)
  have hs : (fun j => if j = i then env i else env j) = env := by
    funext j
    by_cases hj : j = i
    · subst j; simp only [↓reduceIte]
    · simp only [if_neg hj]
  have h0 : P.instantiate (env i) = schemaMatrix collection w c f env := by
    simp only [P, Formula.instantiate, schemaMatrix_rename, apply_ite, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq, hs]
  have h1 : P.instantiate a = schemaMatrix collection w c f (fun j => if j = i then a else env j) := by
    simp only [P, Formula.instantiate, schemaMatrix_rename, apply_ite, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact of_eq h1 (Derives.eqSubst P he (of_eq h0.symm h))

/-- The original certificate determines count/body. Empty zero and independent
scope/compilation witnesses are then aligned by existing object uniqueness. -/
theorem schema_matrix_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (collection : Bool)
    (w c f g : Fin m) (xs ys : Fin 8 → Fin m) (hw : Derives Γ (omega w))
    (hx : Derives Γ (schemaMatrix collection w c f xs)) (hy : Derives Γ (schemaMatrix collection w c g ys)) :
    Derives Γ (.equal f g) := by
  have hxc := Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hx))))
  have hyc := Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hy))))
  have e7 : Derives Γ (.equal (xs 7) (ys 7)) := SyntaxNodeInjective.constructor_input_eq hZ 2 _ _ w
    (SetLanguage.args2 (xs 7) (xs 1)) (SetLanguage.args2 (ys 7) (ys 1)) c 0 hw hxc hyc
  have e1 : Derives Γ (.equal (xs 1) (ys 1)) := SyntaxNodeInjective.constructor_input_eq hZ 2 _ _ w
    (SetLanguage.args2 (xs 7) (xs 1)) (SetLanguage.args2 (ys 7) (ys 1)) c 1 hw hxc hyc
  have hxs := Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR hx)))
  have hys := Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR hy)))
  have hys' := SyntaxNodeInjective.scalar_output_subst w (ys 0) (ys 7) (xs 7) (eq_symm e7) hys
  have e0 : Derives Γ (.equal (xs 0) (ys 0)) := SyntaxNodes.tags_equal hZ 0 0 w (xs 0) (ys 0) Fin.elim0 Fin.elim0 (xs 7) hw hxs hys'
  have e2 := OmegaUniversal.empty_unique (xs 2) (ys 2) (ZFContext.arithmetic hZ).base.extensionality (.conjL (.conjR hx)) (.conjL (.conjR hy))
  let s0 := fun j => if j = (0 : Fin 8) then xs 0 else ys j
  let s1 := fun j => if j = (1 : Fin 8) then xs 1 else s0 j
  let s2 := fun j => if j = (2 : Fin 8) then xs 2 else s1 j
  have h0 : Derives Γ (schemaMatrix collection w c g s0) := matrix_slot_subst collection w c g (xs 0) ys 0 (eq_symm e0) hy
  have h1 : Derives Γ (schemaMatrix collection w c g s1) := matrix_slot_subst collection w c g (xs 1) s0 1 (by change Derives Γ (.equal (ys 1) (xs 1)); exact eq_symm e1) h0
  have h2 : Derives Γ (schemaMatrix collection w c g s2) := matrix_slot_subst collection w c g (xs 2) s1 2 (by change Derives Γ (.equal (ys 2) (xs 2)); exact eq_symm e2) h1
  have hscope : (fun i : Fin 4 => s2 (Fin.natAdd 3 i).castSucc) = (fun i => ys (Fin.natAdd 3 i).castSucc) := by
    funext i
    have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases hi with rfl | rfl | rfl | rfl <;> rfl
  have hY : Derives Γ ((SchemaIndexSyntax.chain (xs 0) (fun i => ys (Fin.natAdd 3 i).castSucc)).conj
      (SchemaAxiomCompilation.schemaResult collection w (xs 0) (xs 2) (xs 1) g (fun i => ys (Fin.natAdd 3 i).castSucc))) := by
    have hc := Derives.conjL (Derives.conjR (Derives.conjR h2))
    have hr := Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR h2)))))
    have hh := Derives.conjI hc hr
    rw [hscope] at hh
    simpa [s2,s1,s0] using hh
  exact SchemaAxiomUnique.result_unique_across_scopes hZ collection w (xs 0) (xs 2) (xs 1) f g
    (fun i => xs (Fin.natAdd 3 i).castSucc) (fun i => ys (Fin.natAdd 3 i).castSucc) hw (.conjL hx)
      (.conjL (.conjR (.conjR hx))) (.conjL hY)
      (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR hx)))))) (.conjR hY)

theorem schemaBranch_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (collection : Bool) (w c f g : Fin m)
    (hw : Derives Γ (omega w)) (hf : Derives Γ (schemaBranch collection w c f)) (hg : Derives Γ (schemaBranch collection w c g)) :
    Derives Γ (.equal f g) := by
  let X := schemaBody collection w c f
  let Ξ := Context.add X (raisedContext 8 Γ)
  apply HornBinderRules.eliminate_many 8 X _ hf
  have hx : Derives Ξ X := .hyp (Or.inl rfl)
  have hg8 := of_eq (schemaBranch_rename collection w c g (old 8)) (HornBinderRules.under_body 8 hg X)
  let Y := schemaBody collection (old 8 w) (old 8 c) (old 8 g)
  let Δ := Context.add Y (raisedContext 8 Ξ)
  apply HornBinderRules.eliminate_many 8 Y _ hg8
  have hy : Derives Δ Y := .hyp (Or.inl rfl)
  have hZ16 := HornBinderRules.zf_body 8 (HornBinderRules.zf_body 8 hZ X) Y
  have hw16 : Derives Δ (omega (old 8 (old 8 w))) := of_eq (by simp only [omega_rename]) (HornBinderRules.under_body 8 (HornBinderRules.under_body 8 hw X) Y)
  have hx16 := of_eq (schemaMatrix_rename collection (old 8 w) (old 8 c) (old 8 f) (slot 8) (old 8)) (HornBinderRules.under_body 8 hx Y)
  exact schema_matrix_unique hZ16 collection (old 8 (old 8 w)) (old 8 (old 8 c)) (old 8 (old 8 f)) (old 8 (old 8 g))
    (fun i => old 8 (slot 8 i)) (slot 8) hw16 hx16 hy

def schemaUniqueSentence {m} (collection : Bool) (w c f g : Fin m) : Source.Sentence :=
  ((omega w).imp ((schemaBranch collection w c f).imp ((schemaBranch collection w c g).imp (.equal f g)))).close

theorem schema_unique_source_certificate {m} (collection : Bool) (w c f g : Fin m) :
    Derives (Source.SetLanguage.ZF.at 0) (schemaUniqueSentence collection w c f g) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ := Context.add (schemaBranch collection w c g) (Context.add (schemaBranch collection w c f) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.source_ZF m) _) _) _
  exact schemaBranch_unique hZ collection w c f g (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem schema_unique_kernel_certificate {m} (collection : Bool) (w c f g : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (schemaUniqueSentence collection w c f g)) :=
  ZFReplay.replay (TheoryTransport.sentence (schema_unique_source_certificate collection w c f g))

def schemaInput {m} (collection : Bool) (w c : Fin m) (env : Fin 8 → Fin m) : Source.Formula m :=
  (Source.Formula.mem (env 0) w).conj
    ((empty (env 2)).conj
      ((SchemaIndexSyntax.chain (env 0) (fun i => env (Fin.natAdd 3 i).castSucc)).conj
        ((SyntaxNodeSyntax.scalar w (env 0) (env 7)).conj
          ((SyntaxNodeSyntax.constructor 2 (schemaTag collection) w (SetLanguage.args2 (env 7) (env 1)) c).conj
            (ProjectSourceCodeSyntax.sourceCode w (env 1)
              (SchemaIndexSyntax.sourceScope (SchemaAxiomCompilation.firstSite collection) (fun i => env (Fin.natAdd 3 i).castSucc)) (env 2))))))

theorem schemaInput_rename {m l} (collection : Bool) (w c : Fin m) (env : Fin 8 → Fin m) (r : Fin m → Fin l) :
    (schemaInput collection w c env).rename r = schemaInput collection (r w) (r c) (fun i => r (env i)) := by
  simp only [schemaInput, Formula.rename, empty_rename, SchemaIndexSyntax.chain_rename, SyntaxNodeSyntax.scalar_rename,
    SyntaxNodeSyntax.constructor_rename, ProofTreeEntryFacts.args2_map, ProjectSourceCodeSyntax.sourceCode_rename, SchemaIndexSyntax.sourceScope_map]

def existsOutput {m} (collection : Bool) (w c : Fin m) : Source.Formula m := .ex
  ((Source.Formula.mem (Fin.last m) w.castSucc).conj (schemaBranch collection w.castSucc c.castSucc (Fin.last m)))

theorem existsOutput_rename {m l} (collection : Bool) (w c : Fin m) (r : Fin m → Fin l) :
    (existsOutput collection w c).rename r = existsOutput collection (r w) (r c) := by
  simp only [existsOutput, Formula.rename, schemaBranch_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

/-- Actual output from a valid original certificate envelope/body. The only
given syntax witnesses describe the INPUT; no output or compiler trace is given. -/
theorem exists_output {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (collection : Bool) (w c : Fin m) (env : Fin 8 → Fin m)
    (hw : Derives Γ (omega w)) (h : Derives Γ (schemaInput collection w c env)) : Derives Γ (existsOutput collection w c) := by
  have he := SchemaShellTyping.output_exists_typed hZ collection w (env 0) (env 2) (env 1)
    (fun i => env (Fin.natAdd 3 i).castSucc) hw (.conjL h) (.conjL (.conjR h)) (.conjL (.conjR (.conjR h)))
      (.conjR (.conjR (.conjR (.conjR (.conjR h)))))
  let B := ((Source.Formula.mem (Fin.last m) w.castSucc).conj
    (SchemaAxiomCompilation.schemaResult collection w.castSucc (env 0).castSucc (env 2).castSucc (env 1).castSucc (Fin.last m)
      (fun i => (env (Fin.natAdd 3 i).castSucc).castSucc))).conj
        (FormulaCodeSyntax.formulaCode w.castSucc (Fin.last m) (env 2).castSucc (env 2).castSucc)
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) he
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hi := of_eq (schemaInput_rename collection w c env Fin.castSucc) (under h B)
  have hm : Derives Δ (schemaMatrix collection w.castSucc c.castSucc (Fin.last m) (fun i => (env i).castSucc)) :=
    .conjI (.conjL hi) (.conjI (.conjL (.conjR hi)) (.conjI (.conjL (.conjR (.conjR hi)))
      (.conjI (.conjL (.conjR (.conjR (.conjR hi)))) (.conjI (.conjL (.conjR (.conjR (.conjR (.conjR hi)))))
        (.conjI (.conjR (.conjR (.conjR (.conjR (.conjR hi))))) (.conjR (.conjL hB)))))))
  have hb := intro_schema collection w.castSucc c.castSucc (Fin.last m) (fun i => (env i).castSucc) hm
  have ho : Derives Δ (existsOutput collection w.castSucc c.castSucc) := by
    apply Derives.exI (Fin.last m)
    exact of_eq (by simp only [Formula.instantiate, Formula.rename, schemaBranch_rename,
      Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI (.conjL (.conjL hB)) hb)
  exact of_eq (existsOutput_rename collection w c Fin.castSucc).symm ho

def schemaExistenceSentence {m} (collection : Bool) (w c : Fin m) (env : Fin 8 → Fin m) : Source.Sentence :=
  ((omega w).imp ((schemaInput collection w c env).imp (existsOutput collection w c))).close

theorem schema_existence_source_certificate {m} (collection : Bool) (w c : Fin m) (env : Fin 8 → Fin m) :
    Derives (Source.SetLanguage.ZF.at 0) (schemaExistenceSentence collection w c env) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ := Context.add (schemaInput collection w c env) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := ZFContext.add (ZFContext.add (ZFContext.source_ZF m) _) _
  exact exists_output hZ collection w c env (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem schema_existence_kernel_certificate {m} (collection : Bool) (w c : Fin m) (env : Fin 8 → Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (schemaExistenceSentence collection w c env)) :=
  ZFReplay.replay (TheoryTransport.sentence (schema_existence_source_certificate collection w c env))

end PPAC.Migration.OriginalAxiomCodeTest
