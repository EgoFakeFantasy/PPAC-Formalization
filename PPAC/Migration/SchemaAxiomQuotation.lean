import PPAC.Migration.SchemaMatrixQuotation
import PPAC.Migration.SchemaTemplateQuotation

/-! The ORIGINAL raw schema body through actual compilation, both actual
matrix branches, original finite template and WHOLE closure, compared with
its EXACT original native axiom sentence. Body/count remain external scheme
indices; internal/nonstandard axiom forcing and final Con are not asserted. -/
namespace PPAC.Migration.SchemaAxiomQuotation
open Internal Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax SchemaIndexSyntax
open SyntaxRenameQuerySyntax (of_eq)
attribute [local irreducible] NaturalRecursionSyntax.matrix
attribute [local implicit_reducible] YesMetaZFC.SetTheory.signature

private theorem separation_forward {m n} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (schema : YesMetaZFC.SetTheory.Definitional.Project.UnarySchema n)
    (w count z body out : Fin m) (scopes : Fin 4 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (SyntaxNumeralSyntax.numeral n count))
    (hz : Derives Γ (empty z)) (hChain : Derives Γ (chain count scopes))
    (hBody : Derives Γ (OriginalTreeQuotationSyntax.tree
      (YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.ProjectEncode.formula schema.body) w body))
    (hValid : Derives Γ (ProjectSourceCodeSyntax.sourceCode w body (sourceScope 0 scopes) z))
    (hm : Derives Γ (SchemaAxiomCompilation.schemaResult false w count z body out scopes)) :
    Derives Γ (PureQuotationSyntax.formula (NativeAxiomCertificateData.sentence (.separation schema)) w out) := by
  let B := SchemaAxiomCompilation.schemaBody false w count z body out scopes
  let Δ := Context.add B (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 B _ hm
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hZ2 := HornBinderRules.zf_body 2 hZ B
  have hw2 : Derives Δ (omega (old 2 w)) := of_eq (omega_rename w (old 2)) (HornBinderRules.under_body 2 hw B)
  have hn2 : Derives Δ (SyntaxNumeralSyntax.numeral n (old 2 count)) :=
    of_eq (SyntaxNumeralSyntax.numeral_rename n count (old 2)) (HornBinderRules.under_body 2 hn B)
  have hz2 : Derives Δ (empty (old 2 z)) := of_eq (empty_rename z (old 2)) (HornBinderRules.under_body 2 hz B)
  have hc2 : Derives Δ (chain (old 2 count) (fun i => old 2 (scopes i))) :=
    of_eq (chain_rename count scopes (old 2)) (HornBinderRules.under_body 2 hChain B)
  have hb2 := of_eq (OriginalTreeQuotationSyntax.tree_rename _ w body (old 2)) (HornBinderRules.under_body 2 hBody B)
  have hv2 : Derives Δ (ProjectSourceCodeSyntax.sourceCode (old 2 w) (old 2 body)
      (sourceScope 0 (fun i => old 2 (scopes i))) (old 2 z)) :=
    of_eq (by simp only [ProjectSourceCodeSyntax.sourceCode_rename,sourceScope_map]) (HornBinderRules.under_body 2 hValid B)
  have hFirst : Derives Δ (SchemaAxiomCompilation.compiledMatrix 0 (old 2 w) (old 2 count) (old 2 z) (old 2 body) (slot 2 0) (fun i => old 2 (scopes i))) :=
    of_eq (by rfl) (.conjL hB)
  have hQx := Derives.impE (.conjL (SchemaMatrixQuotation.separation_iff hZ2 schema.body schema.freeClosed
    (old 2 w) (old 2 count) (old 2 z) (old 2 body) (slot 2 0) (fun i => old 2 (scopes i)) hw2 hn2 hz2 hc2 hb2 hv2)) hFirst
  have hEq : Derives Δ (.equal (slot 2 1) (slot 2 0)) := of_eq (by rfl) (.conjL (.conjR hB))
  have hQy := OriginalQuotationValue.tree_output_subst _ (old 2 w) (slot 2 0) (slot 2 1) (eq_symm hEq) hQx
  let env : Fin 3 → Fin (m+2) := fun i => if i.val = 0 then slot 2 0 else slot 2 1
  have hEnv (i : Fin 3) : Derives Δ (OriginalTreeQuotationSyntax.tree (SchemaTemplateQuotation.separationInputs schema i) (old 2 w) (env i)) := by
    by_cases h : i.val = 0
    · simpa only [SchemaTemplateQuotation.separationInputs,env,h,↓reduceIte,PureQuotationSyntax.formula] using hQx
    · simpa only [SchemaTemplateQuotation.separationInputs,env,h,↓reduceIte,PureQuotationSyntax.formula] using hQy
  have hAsm : Derives Δ (SchemaAxiomAssembly.assembled false (old 2 w) (old 2 count) env (old 2 out)) := of_eq (by rfl) (.conjR (.conjR hB))
  have ho := Derives.impE (.conjL (SchemaTemplateQuotation.separation_iff hZ2 schema (old 2 w) (old 2 count) (old 2 out) env hw2 hn2 hEnv)) hAsm
  exact of_eq (PureQuotationSyntax.formula_rename _ w out (old 2)).symm ho

private theorem collection_forward {m n} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (schema : YesMetaZFC.SetTheory.Definitional.Project.BinarySchema n)
    (w count z body out : Fin m) (scopes : Fin 4 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (SyntaxNumeralSyntax.numeral n count))
    (hz : Derives Γ (empty z)) (hChain : Derives Γ (chain count scopes))
    (hBody : Derives Γ (OriginalTreeQuotationSyntax.tree
      (YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.ProjectEncode.formula schema.body) w body))
    (hValid : Derives Γ (ProjectSourceCodeSyntax.sourceCode w body (sourceScope 1 scopes) z))
    (hm : Derives Γ (SchemaAxiomCompilation.schemaResult true w count z body out scopes)) :
    Derives Γ (PureQuotationSyntax.formula (NativeAxiomCertificateData.sentence (.collection schema)) w out) := by
  let B := SchemaAxiomCompilation.schemaBody true w count z body out scopes
  let Δ := Context.add B (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 B _ hm
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hZ2 := HornBinderRules.zf_body 2 hZ B
  have hw2 : Derives Δ (omega (old 2 w)) := of_eq (omega_rename w (old 2)) (HornBinderRules.under_body 2 hw B)
  have hn2 : Derives Δ (SyntaxNumeralSyntax.numeral n (old 2 count)) :=
    of_eq (SyntaxNumeralSyntax.numeral_rename n count (old 2)) (HornBinderRules.under_body 2 hn B)
  have hz2 : Derives Δ (empty (old 2 z)) := of_eq (empty_rename z (old 2)) (HornBinderRules.under_body 2 hz B)
  have hc2 : Derives Δ (chain (old 2 count) (fun i => old 2 (scopes i))) :=
    of_eq (chain_rename count scopes (old 2)) (HornBinderRules.under_body 2 hChain B)
  have hb2 := of_eq (OriginalTreeQuotationSyntax.tree_rename _ w body (old 2)) (HornBinderRules.under_body 2 hBody B)
  have hv2 : Derives Δ (ProjectSourceCodeSyntax.sourceCode (old 2 w) (old 2 body)
      (sourceScope 1 (fun i => old 2 (scopes i))) (old 2 z)) :=
    of_eq (by simp only [ProjectSourceCodeSyntax.sourceCode_rename,sourceScope_map]) (HornBinderRules.under_body 2 hValid B)
  have hFirst : Derives Δ (SchemaAxiomCompilation.compiledMatrix 1 (old 2 w) (old 2 count) (old 2 z) (old 2 body) (slot 2 0) (fun i => old 2 (scopes i))) :=
    of_eq (by rfl) (.conjL hB)
  have hSecond : Derives Δ (SchemaAxiomCompilation.compiledMatrix 2 (old 2 w) (old 2 count) (old 2 z) (old 2 body) (slot 2 1) (fun i => old 2 (scopes i))) :=
    of_eq (by rfl) (.conjL (.conjR hB))
  have hQx := Derives.impE (.conjL (SchemaMatrixQuotation.collection_one_iff hZ2 schema.body schema.freeClosed
    (old 2 w) (old 2 count) (old 2 z) (old 2 body) (slot 2 0) (fun i => old 2 (scopes i)) hw2 hn2 hz2 hc2 hb2 hv2)) hFirst
  have hQy := Derives.impE (.conjL (SchemaMatrixQuotation.collection_two_iff hZ2 schema.body schema.freeClosed
    (old 2 w) (old 2 count) (old 2 z) (old 2 body) (slot 2 1) (fun i => old 2 (scopes i)) hw2 hn2 hz2 hc2 hb2 (of_eq (by rfl) hv2))) hSecond
  let env : Fin 3 → Fin (m+2) := fun i => if i.val = 0 then slot 2 0 else slot 2 1
  have hEnv (i : Fin 3) : Derives Δ (OriginalTreeQuotationSyntax.tree (SchemaTemplateQuotation.collectionInputs schema i) (old 2 w) (env i)) := by
    by_cases h : i.val = 0
    · simpa only [SchemaTemplateQuotation.collectionInputs,env,h,↓reduceIte,PureQuotationSyntax.formula] using hQx
    · simpa only [SchemaTemplateQuotation.collectionInputs,env,h,↓reduceIte,PureQuotationSyntax.formula] using hQy
  have hAsm : Derives Δ (SchemaAxiomAssembly.assembled true (old 2 w) (old 2 count) env (old 2 out)) := of_eq (by rfl) (.conjR (.conjR hB))
  have ho := Derives.impE (.conjL (SchemaTemplateQuotation.collection_iff hZ2 schema (old 2 w) (old 2 count) (old 2 out) env hw2 hn2 hEnv)) hAsm
  exact of_eq (PureQuotationSyntax.formula_rename _ w out (old 2)).symm ho

private theorem result_iff {m parameterCount source} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (collection : Bool) (input : YesMetaZFC.SetTheory.Definitional.Project.Formula 1 source)
    (output : PureSyntaxQuotation.Fm [] [])
    (forward : ∀ {l} {Δ : Context l}, ZFContext.Evidence Δ → ∀ (w count z body out : Fin l) (scopes : Fin 4 → Fin l),
      Derives Δ (omega w) → Derives Δ (SyntaxNumeralSyntax.numeral parameterCount count) → Derives Δ (empty z) →
      Derives Δ (chain count scopes) → Derives Δ (OriginalTreeQuotationSyntax.tree
        (YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.ProjectEncode.formula input) w body) →
      Derives Δ (ProjectSourceCodeSyntax.sourceCode w body (sourceScope (SchemaAxiomCompilation.firstSite collection) scopes) z) →
      Derives Δ (SchemaAxiomCompilation.schemaResult collection w count z body out scopes) →
      Derives Δ (PureQuotationSyntax.formula output w out))
    (w count z body out : Fin m) (scopes : Fin 4 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (SyntaxNumeralSyntax.numeral parameterCount count))
    (hz : Derives Γ (empty z)) (hChain : Derives Γ (chain count scopes))
    (hBody : Derives Γ (OriginalTreeQuotationSyntax.tree
      (YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.ProjectEncode.formula input) w body))
    (hValid : Derives Γ (ProjectSourceCodeSyntax.sourceCode w body (sourceScope (SchemaAxiomCompilation.firstSite collection) scopes) z)) :
    Derives Γ ((SchemaAxiomCompilation.schemaResult collection w count z body out scopes).iff
      (PureQuotationSyntax.formula output w out)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact forward (ZFContext.add hZ _) w count z body out scopes
      (add hw _) (add hn _) (add hz _) (add hChain _) (add hBody _) (add hValid _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    let E := PureQuotationSyntax.formula output w out
    let P := (Source.Formula.mem (Fin.last m) w.castSucc).conj
      (SchemaAxiomCompilation.schemaResult collection w.castSucc count.castSucc z.castSucc body.castSucc (Fin.last m) (fun i => (scopes i).castSucc))
    let Δ := Context.add P (Context.image Formula.raise (Context.add E Γ))
    have he := SchemaAxiomCompilation.schema_output_exists hZ collection w count z body scopes hw
      (SyntaxNumerals.range hZ parameterCount w count hw hn) hz hChain hValid
    apply Derives.exE (p := P) (add he E)
    have hP : Derives Δ P := .hyp (Or.inl rfl)
    have hZ1 := ZFContext.under (ZFContext.add hZ E) P
    have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under (add hw E) P)
    have hn1 : Derives Δ (SyntaxNumeralSyntax.numeral parameterCount count.castSucc) :=
      of_eq (SyntaxNumeralSyntax.numeral_rename _ count Fin.castSucc) (under (add hn E) P)
    have hz1 : Derives Δ (empty z.castSucc) := of_eq (empty_rename z Fin.castSucc) (under (add hz E) P)
    have hc1 : Derives Δ (chain count.castSucc (fun i => (scopes i).castSucc)) :=
      of_eq (chain_rename count scopes Fin.castSucc) (under (add hChain E) P)
    have hb1 := of_eq (OriginalTreeQuotationSyntax.tree_rename _ w body Fin.castSucc) (under (add hBody E) P)
    have hv1 : Derives Δ (ProjectSourceCodeSyntax.sourceCode w.castSucc body.castSucc
        (sourceScope (SchemaAxiomCompilation.firstSite collection) (fun i => (scopes i).castSucc)) z.castSucc) :=
      of_eq (by simp only [Formula.raise,ProjectSourceCodeSyntax.sourceCode_rename,sourceScope_map]) (under (add hValid E) P)
    have hQx := forward hZ1 w.castSucc count.castSucc z.castSucc body.castSucc (Fin.last m)
      (fun i => (scopes i).castSucc) hw1 hn1 hz1 hc1 hb1 hv1 (.conjR hP)
    have hE : Derives (Context.add E Γ) E := .hyp (Or.inl rfl)
    have hQout := of_eq (PureQuotationSyntax.formula_rename output w out Fin.castSucc) (under hE P)
    have hEq := OriginalTreeQuotationUnique.tree_unique hZ1 (PureSyntaxQuotation.formulaTree output)
      w.castSucc (Fin.last m) out.castSucc hw1 hQx hQout
    let Q := SchemaAxiomCompilation.schemaResult collection w.castSucc.castSucc count.castSucc.castSucc z.castSucc.castSucc
      body.castSucc.castSucc (Fin.last (m+1)) (fun i => (scopes i).castSucc.castSucc)
    have q0 : Q.instantiate (Fin.last m) = SchemaAxiomCompilation.schemaResult collection w.castSucc count.castSucc z.castSucc body.castSucc (Fin.last m) (fun i => (scopes i).castSucc) := by
      simp only [Q,Formula.instantiate,SchemaAxiomCompilation.schemaResult_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
    have q1 : Q.instantiate out.castSucc = SchemaAxiomCompilation.schemaResult collection w.castSucc count.castSucc z.castSucc body.castSucc out.castSucc (fun i => (scopes i).castSucc) := by
      simp only [Q,Formula.instantiate,SchemaAxiomCompilation.schemaResult_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
    have ho := of_eq q1 (Derives.eqSubst Q hEq (of_eq q0.symm (.conjR hP)))
    exact of_eq (SchemaAxiomCompilation.schemaResult_rename collection w count z body out scopes Fin.castSucc).symm ho

/-- Whole ORIGINAL raw-schema pipeline, with no given intermediate matrix
quotation, is exactly the ORIGINAL native separation sentence quotation. -/
theorem separation_iff {m n} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (schema : YesMetaZFC.SetTheory.Definitional.Project.UnarySchema n)
    (w count z body out : Fin m) (scopes : Fin 4 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (SyntaxNumeralSyntax.numeral n count))
    (hz : Derives Γ (empty z)) (hChain : Derives Γ (chain count scopes))
    (hBody : Derives Γ (OriginalTreeQuotationSyntax.tree
      (YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.ProjectEncode.formula schema.body) w body))
    (hValid : Derives Γ (ProjectSourceCodeSyntax.sourceCode w body (sourceScope 0 scopes) z)) :
    Derives Γ ((SchemaAxiomCompilation.schemaResult false w count z body out scopes).iff
      (PureQuotationSyntax.formula (NativeAxiomCertificateData.sentence (.separation schema)) w out)) :=
  result_iff hZ false schema.body (NativeAxiomCertificateData.sentence (.separation schema))
    (fun hZ w count z body out scopes hw hn hz hChain hBody hValid hm =>
      separation_forward hZ schema w count z body out scopes hw hn hz hChain hBody hValid hm)
    w count z body out scopes hw hn hz hChain hBody hValid

/-- Whole ORIGINAL raw-schema pipeline, with no given intermediate matrix
quotation, is exactly the ORIGINAL native collection sentence quotation. -/
theorem collection_iff {m n} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (schema : YesMetaZFC.SetTheory.Definitional.Project.BinarySchema n)
    (w count z body out : Fin m) (scopes : Fin 4 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (SyntaxNumeralSyntax.numeral n count))
    (hz : Derives Γ (empty z)) (hChain : Derives Γ (chain count scopes))
    (hBody : Derives Γ (OriginalTreeQuotationSyntax.tree
      (YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.ProjectEncode.formula schema.body) w body))
    (hValid : Derives Γ (ProjectSourceCodeSyntax.sourceCode w body (sourceScope 1 scopes) z)) :
    Derives Γ ((SchemaAxiomCompilation.schemaResult true w count z body out scopes).iff
      (PureQuotationSyntax.formula (NativeAxiomCertificateData.sentence (.collection schema)) w out)) :=
  result_iff hZ true schema.body (NativeAxiomCertificateData.sentence (.collection schema))
    (fun hZ w count z body out scopes hw hn hz hChain hBody hValid hm =>
      collection_forward hZ schema w count z body out scopes hw hn hz hChain hBody hValid hm)
    w count z body out scopes hw hn hz hChain hBody hValid

private def assumptions {m parameterCount source : Nat} (collection : Bool)
    (input : YesMetaZFC.SetTheory.Definitional.Project.Formula 1 source)
    (w count z body : Fin m) (scopes : Fin 4 → Fin m) : Source.Formula m :=
  (omega w).conj ((SyntaxNumeralSyntax.numeral parameterCount count).conj ((empty z).conj
    ((chain count scopes).conj ((OriginalTreeQuotationSyntax.tree
      (YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.ProjectEncode.formula input) w body).conj
        (ProjectSourceCodeSyntax.sourceCode w body (sourceScope (SchemaAxiomCompilation.firstSite collection) scopes) z)))))

private def statement {m parameterCount source : Nat} (collection : Bool)
    (input : YesMetaZFC.SetTheory.Definitional.Project.Formula 1 source) (output : PureSyntaxQuotation.Fm [] [])
    (w count z body out : Fin m) (scopes : Fin 4 → Fin m) : Source.Sentence :=
  ((assumptions (parameterCount := parameterCount) collection input w count z body scopes).imp
    ((SchemaAxiomCompilation.schemaResult collection w count z body out scopes).iff (PureQuotationSyntax.formula output w out))).close

private theorem source_certificate {m parameterCount source} (collection : Bool)
    (input : YesMetaZFC.SetTheory.Definitional.Project.Formula 1 source) (output : PureSyntaxQuotation.Fm [] [])
    (prover : ∀ {l} {Δ : Context l}, ZFContext.Evidence Δ → ∀ (w count z body out : Fin l) (scopes : Fin 4 → Fin l),
      Derives Δ (omega w) → Derives Δ (SyntaxNumeralSyntax.numeral parameterCount count) → Derives Δ (empty z) →
      Derives Δ (chain count scopes) → Derives Δ (OriginalTreeQuotationSyntax.tree
        (YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.ProjectEncode.formula input) w body) →
      Derives Δ (ProjectSourceCodeSyntax.sourceCode w body (sourceScope (SchemaAxiomCompilation.firstSite collection) scopes) z) →
      Derives Δ ((SchemaAxiomCompilation.schemaResult collection w count z body out scopes).iff (PureQuotationSyntax.formula output w out)))
    (w count z body out : Fin m) (scopes : Fin 4 → Fin m) :
    Derives (Source.SetLanguage.ZF.at 0) (statement (parameterCount := parameterCount) collection input output w count z body out scopes) := by
  apply close_derives
  apply Derives.impI
  let F := assumptions (parameterCount := parameterCount) collection input w count z body scopes
  let Δ := Context.add F (Source.SetLanguage.ZF.at m)
  have hF : Derives Δ F := .hyp (Or.inl rfl)
  have hZ := ZFContext.add (ZFContext.source_ZF m) F
  have hRest := Derives.conjR (.conjR (.conjR hF))
  exact prover hZ w count z body out scopes (.conjL hF) (.conjL (.conjR hF)) (.conjL (.conjR (.conjR hF)))
    (.conjL hRest) (.conjL (.conjR hRest)) (.conjR (.conjR hRest))

def separationSentence {m n} (schema : YesMetaZFC.SetTheory.Definitional.Project.UnarySchema n)
    (w count z body out : Fin m) (scopes : Fin 4 → Fin m) : Source.Sentence :=
  statement (parameterCount := n) false schema.body (NativeAxiomCertificateData.sentence (.separation schema)) w count z body out scopes

theorem separation_kernel_certificate {m n} (schema : YesMetaZFC.SetTheory.Definitional.Project.UnarySchema n)
    (w count z body out : Fin m) (scopes : Fin 4 → Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (separationSentence schema w count z body out scopes)) :=
  ZFReplay.replay (TheoryTransport.sentence (source_certificate false schema.body (NativeAxiomCertificateData.sentence (.separation schema))
    (fun hZ w count z body out scopes hw hn hz hChain hBody hValid =>
      separation_iff hZ schema w count z body out scopes hw hn hz hChain hBody hValid)
    w count z body out scopes))

def collectionSentence {m n} (schema : YesMetaZFC.SetTheory.Definitional.Project.BinarySchema n)
    (w count z body out : Fin m) (scopes : Fin 4 → Fin m) : Source.Sentence :=
  statement (parameterCount := n) true schema.body (NativeAxiomCertificateData.sentence (.collection schema)) w count z body out scopes

theorem collection_kernel_certificate {m n} (schema : YesMetaZFC.SetTheory.Definitional.Project.BinarySchema n)
    (w count z body out : Fin m) (scopes : Fin 4 → Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (collectionSentence schema w count z body out scopes)) :=
  ZFReplay.replay (TheoryTransport.sentence (source_certificate true schema.body (NativeAxiomCertificateData.sentence (.collection schema))
    (fun hZ w count z body out scopes hw hn hz hChain hBody hValid =>
      collection_iff hZ schema w count z body out scopes hw hn hz hChain hBody hValid)
    w count z body out scopes))

end PPAC.Migration.SchemaAxiomQuotation
