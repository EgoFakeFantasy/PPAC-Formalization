import PPAC.Migration.ProjectNativeRenaming
import PPAC.Migration.ProjectCompilerQuotation
import PPAC.Migration.SchemaAxiomCompilation

/-! Exact quotation of the ORIGINAL three actual compiled/renamed matrices.
All compiler/map/identity/converted-list witnesses are bound by object exists.
Native bodies/counts index an external scheme; uniform nonstandard Con is not
asserted. This consumes the existing compiler and native renaming bridges. -/
namespace PPAC.Migration.SchemaMatrixQuotation
open Internal Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax SchemaIndexSyntax
open SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC.SetTheory.Definitional.Project (fo_bound_context fo_formula)
attribute [local irreducible] NaturalRecursionSyntax.matrix
attribute [local implicit_reducible] YesMetaZFC.SetTheory.signature

private def graphPoints {m source target} (site : Fin 3) (f : Fin source → Fin target)
    (w count : Fin m) (scopes : Fin 4 → Fin m) : Source.Formula m := .all
  ((SchemaIndexSyntax.graph site w.castSucc count.castSucc (fun i => (scopes i).castSucc) (Fin.last m)).imp
    (NativeIndexFormulaQuotation.points (fo_bound_context source).length
      (fun j => (ProjectNativeRenaming.nativeVariable f (NativeTopQuotationIndices.entryAt (fo_bound_context source) j)).index) (Fin.last m)))

private theorem graphPoints_rename {m l source target} (site : Fin 3) (f : Fin source → Fin target)
    (w count : Fin m) (scopes : Fin 4 → Fin m) (r : Fin m → Fin l) :
    (graphPoints site f w count scopes).rename r = graphPoints site f (r w) (r count) (fun i => r (scopes i)) := by
  simp only [graphPoints,Formula.rename,SchemaIndexSyntax.graph_rename,NativeIndexFormulaQuotation.points_rename,
    Formula.liftRen,Fin.lastCases_last,Fin.lastCases_castSucc]

private theorem graphPoints_at {m source target} {Γ : Context m} (site : Fin 3) (f : Fin source → Fin target)
    (w count g : Fin m) (scopes : Fin 4 → Fin m) (hp : Derives Γ (graphPoints site f w count scopes))
    (hg : Derives Γ (SchemaIndexSyntax.graph site w count scopes g)) :
    Derives Γ (NativeIndexFormulaQuotation.points (fo_bound_context source).length
      (fun j => (ProjectNativeRenaming.nativeVariable f (NativeTopQuotationIndices.entryAt (fo_bound_context source) j)).index) g) :=
  .impE (of_eq (by simp only [Formula.instantiate,Formula.rename,SchemaIndexSyntax.graph_rename,
    NativeIndexFormulaQuotation.points_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]) (Derives.allE g hp)) hg

private theorem graph_points_proved {m parameterCount source target} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (site : Fin 3) (f : Fin source → Fin target)
    (producer : ∀ {l} {Δ : Context l}, ZFContext.Evidence Δ → ∀ (w count g : Fin l) (scopes : Fin 4 → Fin l),
      Derives Δ (omega w) → Derives Δ (SyntaxNumeralSyntax.numeral parameterCount count) →
      Derives Δ (chain count scopes) → Derives Δ (SchemaIndexSyntax.graph site w count scopes g) →
      ∀ j : Fin source, Derives Δ (SchemaIndexQuotation.value j.val (f j).val g))
    (w count : Fin m) (scopes : Fin 4 → Fin m) (hw : Derives Γ (omega w))
    (hn : Derives Γ (SyntaxNumeralSyntax.numeral parameterCount count)) (hc : Derives Γ (chain count scopes)) :
    Derives Γ (graphPoints site f w count scopes) := by
  apply Derives.allI
  apply Derives.impI
  let G := SchemaIndexSyntax.graph site w.castSucc count.castSucc (fun i => (scopes i).castSucc) (Fin.last m)
  let Δ := Context.add G (Context.image Formula.raise Γ)
  have hG : Derives Δ G := .hyp (Or.inl rfl)
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw G)
  have hn1 : Derives Δ (SyntaxNumeralSyntax.numeral parameterCount count.castSucc) :=
    of_eq (SyntaxNumeralSyntax.numeral_rename _ count Fin.castSucc) (under hn G)
  have hc1 : Derives Δ (chain count.castSucc (fun i => (scopes i).castSucc)) :=
    of_eq (chain_rename count scopes Fin.castSucc) (under hc G)
  apply NativeIndexFormulaQuotation.points_intro
  intro j
  let k : Fin source := ⟨j.val,by simpa only [fo_bound_context,List.length_replicate] using j.isLt⟩
  have hv := producer (ZFContext.under hZ G) w.castSucc count.castSucc (Fin.last m)
    (fun i => (scopes i).castSucc) hw1 hn1 hc1 hG k
  exact of_eq (by simp only [ProjectNativeRenaming.variable_index,NativeTopQuotationIndices.index_entryAt]; rfl) hv

private theorem renamed_forward {m source target} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (site : Fin 3) (input : YesMetaZFC.SetTheory.Definitional.Project.Formula 1 source) (hc : input.FreeClosed)
    (f : Fin source → Fin target) (w count z a out : Fin m) (scopes : Fin 4 → Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hs : Derives Γ (SyntaxNumeralSyntax.numeral source (sourceScope site scopes)))
    (ht : Derives Γ (SyntaxNumeralSyntax.numeral target (targetScope site scopes)))
    (hp : Derives Γ (graphPoints site f w count scopes))
    (ha : Derives Γ (PureQuotationSyntax.formula (fo_formula input hc) w a))
    (hm : Derives Γ (SchemaAxiomCompilation.renamedMatrix site w count z scopes a out)) :
    Derives Γ (PureQuotationSyntax.formula (fo_formula (input.rename f)
      ((YesMetaZFC.SetTheory.Definitional.Formula.freeClosed_rename f input).mpr hc)) w out) := by
  let B := SchemaAxiomCompilation.renamedBody site w count z scopes a out
  let Δ := Context.add B (raisedContext 3 Γ)
  apply HornBinderRules.eliminate_many 3 B _ hm
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hZ3 := HornBinderRules.zf_body 3 hZ B
  have hSys := Derives.conjL hB
  have hCoded := Derives.conjL hSys
  have hGraph := Derives.conjR (Derives.conjL hCoded)
  have hR := Derives.conjR hCoded
  have hId := Derives.conjL (Derives.conjR hSys)
  have hw3 : Derives Δ (omega (old 3 w)) := of_eq (omega_rename w (old 3)) (HornBinderRules.under_body 3 hw B)
  have hz3 : Derives Δ (empty (old 3 z)) := of_eq (empty_rename z (old 3)) (HornBinderRules.under_body 3 hz B)
  have hs3 : Derives Δ (SyntaxNumeralSyntax.numeral source (old 3 (sourceScope site scopes))) :=
    of_eq (SyntaxNumeralSyntax.numeral_rename _ _ (old 3)) (HornBinderRules.under_body 3 hs B)
  have ht3 : Derives Δ (SyntaxNumeralSyntax.numeral target (old 3 (targetScope site scopes))) :=
    of_eq (SyntaxNumeralSyntax.numeral_rename _ _ (old 3)) (HornBinderRules.under_body 3 ht B)
  have hp3 : Derives Δ (graphPoints site f (old 3 w) (old 3 count) (fun i => old 3 (scopes i))) :=
    of_eq (graphPoints_rename site f w count scopes (old 3)) (HornBinderRules.under_body 3 hp B)
  have hPoints := graphPoints_at site f (old 3 w) (old 3 count) (slot 3 0) (fun i => old 3 (scopes i)) hp3 hGraph
  have ha3 : Derives Δ (PureQuotationSyntax.formula (fo_formula input hc) (old 3 w) (old 3 a)) :=
    of_eq (PureQuotationSyntax.formula_rename _ w a (old 3)) (HornBinderRules.under_body 3 ha B)
  let D := (SyntaxMapCodeSyntax.encoded (old 3 w).castSucc (Fin.last (m+3)) (old 3 z).castSucc
    (old 3 z).castSucc (slot 3 2).castSucc).conj (SyntaxRenameTermIdentity.diagonal (Fin.last (m+3)))
  let Ξ := Context.add D (Context.image Formula.raise Δ)
  apply Derives.exE (p := D) hId
  have hD : Derives Ξ D := .hyp (Or.inl rfl)
  have hZ4 := ZFContext.under hZ3 D
  have hw4 : Derives Ξ (omega (old 3 w).castSucc) := of_eq (omega_rename _ Fin.castSucc) (under hw3 D)
  have hz4 : Derives Ξ (SyntaxNumeralSyntax.numeral 0 (old 3 z).castSucc) :=
    of_eq (by simp only [Formula.raise,empty_rename,SyntaxNumeralSyntax.numeral]) (under hz3 D)
  have hs4 : Derives Ξ (SyntaxNumeralSyntax.numeral (fo_bound_context source).length (old 3 (sourceScope site scopes)).castSucc) :=
    of_eq (by simp only [Formula.raise,SyntaxNumeralSyntax.numeral_rename,fo_bound_context,List.length_replicate]) (under hs3 D)
  have ht4 : Derives Ξ (SyntaxNumeralSyntax.numeral (fo_bound_context target).length (old 3 (targetScope site scopes)).castSucc) :=
    of_eq (by simp only [Formula.raise,SyntaxNumeralSyntax.numeral_rename,fo_bound_context,List.length_replicate]) (under ht3 D)
  have hR4 : Derives Ξ (SyntaxMapCodeSyntax.encoded (old 3 w).castSucc (slot 3 0).castSucc
      (old 3 (sourceScope site scopes)).castSucc (old 3 (targetScope site scopes)).castSucc (slot 3 1).castSucc) :=
    of_eq (by simp only [Formula.raise,SyntaxMapCodeSyntax.encoded_rename,sourceScope_map,targetScope_map]) (under hR D)
  have hPoints4 := of_eq (NativeIndexFormulaQuotation.points_rename _ _ (slot 3 0) Fin.castSucc) (under hPoints D)
  have ha4 := of_eq (PureQuotationSyntax.formula_rename _ (old 3 w) (old 3 a) Fin.castSucc) (under ha3 D)
  have hM4 : Derives Ξ (SyntaxRenameJudgmentSyntax.renamed (old 3 w).castSucc (slot 3 1).castSucc (slot 3 2).castSucc
      (old 3 (sourceScope site scopes)).castSucc (old 3 z).castSucc (old 3 (targetScope site scopes)).castSucc
      (old 3 z).castSucc (old 3 a).castSucc (old 3 out).castSucc) :=
    of_eq (by simp only [Formula.raise,SyntaxRenameJudgmentSyntax.renamed_rename])
      (under (.conjR hB) D)
  have hN := NativeIndexFormulaQuotation.formula_iff hZ4 (fo_formula input hc)
    (ProjectNativeRenaming.nativeVariable f) YesMetaZFC.Logic.FirstOrder.VariableRenaming.id
    (old 3 w).castSucc (slot 3 1).castSucc (slot 3 2).castSucc (old 3 (sourceScope site scopes)).castSucc
    (old 3 z).castSucc (old 3 (targetScope site scopes)).castSucc (old 3 z).castSucc (old 3 a).castSucc (old 3 out).castSucc
    (slot 3 0).castSucc (Fin.last (m+3)) hw4 hs4 hz4 ht4 hz4 hR4 (.conjL hD)
    (NativeIndexFormulaQuotation.points_at _ _ hPoints4) (fun j => Fin.elim0 j) ha4
  have ho := Derives.impE (.conjL hN) hM4
  have hNative := of_eq (congrArg (fun p => PureQuotationSyntax.formula p (old 3 w).castSucc (old 3 out).castSucc)
    (ProjectNativeRenaming.formula_substitute input hc f)) ho
  exact of_eq (by simp only [Formula.raise,PureQuotationSyntax.formula_rename]) hNative

private theorem compiled_forward {m source target} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (site : Fin 3) (input : YesMetaZFC.SetTheory.Definitional.Project.Formula 1 source) (hc : input.FreeClosed)
    (f : Fin source → Fin target) (w count z body out : Fin m) (scopes : Fin 4 → Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hs : Derives Γ (SyntaxNumeralSyntax.numeral source (sourceScope site scopes)))
    (ht : Derives Γ (SyntaxNumeralSyntax.numeral target (targetScope site scopes)))
    (hp : Derives Γ (graphPoints site f w count scopes))
    (hBody : Derives Γ (OriginalTreeQuotationSyntax.tree
      (YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.ProjectEncode.formula input) w body))
    (hm : Derives Γ (SchemaAxiomCompilation.compiledMatrix site w count z body out scopes)) :
    Derives Γ (PureQuotationSyntax.formula (fo_formula (input.rename f)
      ((YesMetaZFC.SetTheory.Definitional.Formula.freeClosed_rename f input).mpr hc)) w out) := by
  let C := SchemaAxiomCompilation.compiledBody site w count z body out scopes
  let Δ := Context.add C (Context.image Formula.raise Γ)
  apply Derives.exE (p := C) hm
  have hC : Derives Δ C := .hyp (Or.inl rfl)
  have hZ1 := ZFContext.under hZ C
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw C)
  have hz1 : Derives Δ (empty z.castSucc) := of_eq (empty_rename z Fin.castSucc) (under hz C)
  have hs1 : Derives Δ (SyntaxNumeralSyntax.numeral source (sourceScope site (fun i => (scopes i).castSucc))) :=
    of_eq (by simp only [Formula.raise,SyntaxNumeralSyntax.numeral_rename,sourceScope_map]) (under hs C)
  have ht1 : Derives Δ (SyntaxNumeralSyntax.numeral target (targetScope site (fun i => (scopes i).castSucc))) :=
    of_eq (by simp only [Formula.raise,SyntaxNumeralSyntax.numeral_rename,targetScope_map]) (under ht C)
  have hp1 : Derives Δ (graphPoints site f w.castSucc count.castSucc (fun i => (scopes i).castSucc)) :=
    of_eq (graphPoints_rename site f w count scopes Fin.castSucc) (under hp C)
  have hBody1 := of_eq (OriginalTreeQuotationSyntax.tree_rename _ w body Fin.castSucc) (under hBody C)
  have hCompiler := ProjectCompilerQuotation.formula_iff hZ1 input hc w.castSucc
    (sourceScope site (fun i => (scopes i).castSucc)) z.castSucc body.castSucc (Fin.last m) hw1 hs1 hz1 hBody1
  have hCode : Derives Δ (ProjectCompilerCodeSyntax.compiled w.castSucc body.castSucc (sourceScope site (fun i => (scopes i).castSucc)) (Fin.last m)) :=
    of_eq (by simp only [sourceScope_map]) (.conjL hC)
  have hi := Derives.impE (.conjL hCompiler) hCode
  have ho := renamed_forward hZ1 site input hc f w.castSucc count.castSucc z.castSucc (Fin.last m) out.castSucc
    (fun i => (scopes i).castSucc) hw1 hz1 hs1 ht1 hp1 hi (.conjR hC)
  exact of_eq (PureQuotationSyntax.formula_rename _ w out Fin.castSucc).symm ho

private theorem compiled_iff {m parameterCount source target} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (site : Fin 3) (input : YesMetaZFC.SetTheory.Definitional.Project.Formula 1 source) (hc : input.FreeClosed)
    (f : Fin source → Fin target) (w count z body out : Fin m) (scopes : Fin 4 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (SyntaxNumeralSyntax.numeral parameterCount count))
    (hz : Derives Γ (empty z)) (hChain : Derives Γ (chain count scopes))
    (hs : Derives Γ (SyntaxNumeralSyntax.numeral source (sourceScope site scopes)))
    (ht : Derives Γ (SyntaxNumeralSyntax.numeral target (targetScope site scopes)))
    (hp : Derives Γ (graphPoints site f w count scopes))
    (hBody : Derives Γ (OriginalTreeQuotationSyntax.tree
      (YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.ProjectEncode.formula input) w body))
    (hValid : Derives Γ (ProjectSourceCodeSyntax.sourceCode w body (sourceScope site scopes) z)) :
    Derives Γ ((SchemaAxiomCompilation.compiledMatrix site w count z body out scopes).iff
      (PureQuotationSyntax.formula (fo_formula (input.rename f)
        ((YesMetaZFC.SetTheory.Definitional.Formula.freeClosed_rename f input).mpr hc)) w out)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact compiled_forward (ZFContext.add hZ _) site input hc f w count z body out scopes
      (add hw _) (add hz _) (add hs _) (add ht _) (add hp _) (add hBody _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    let output := fo_formula (input.rename f) ((YesMetaZFC.SetTheory.Definitional.Formula.freeClosed_rename f input).mpr hc)
    let E := PureQuotationSyntax.formula output w out
    let P := (Source.Formula.mem (Fin.last m) w.castSucc).conj
      (SchemaAxiomCompilation.compiledMatrix site w.castSucc count.castSucc z.castSucc body.castSucc (Fin.last m) (fun i => (scopes i).castSucc))
    let Δ := Context.add P (Context.image Formula.raise (Context.add E Γ))
    have he := SchemaAxiomCompilation.exists_compiled hZ site w count z body scopes hw
      (SyntaxNumerals.range hZ parameterCount w count hw hn) hz hChain hValid
    apply Derives.exE (p := P) (add he E)
    have hP : Derives Δ P := .hyp (Or.inl rfl)
    have hZ1 := ZFContext.under (ZFContext.add hZ E) P
    have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under (add hw E) P)
    have hz1 : Derives Δ (empty z.castSucc) := of_eq (empty_rename z Fin.castSucc) (under (add hz E) P)
    have hs1 : Derives Δ (SyntaxNumeralSyntax.numeral source (sourceScope site (fun i => (scopes i).castSucc))) :=
      of_eq (by simp only [Formula.raise,SyntaxNumeralSyntax.numeral_rename,sourceScope_map]) (under (add hs E) P)
    have ht1 : Derives Δ (SyntaxNumeralSyntax.numeral target (targetScope site (fun i => (scopes i).castSucc))) :=
      of_eq (by simp only [Formula.raise,SyntaxNumeralSyntax.numeral_rename,targetScope_map]) (under (add ht E) P)
    have hp1 : Derives Δ (graphPoints site f w.castSucc count.castSucc (fun i => (scopes i).castSucc)) :=
      of_eq (graphPoints_rename site f w count scopes Fin.castSucc) (under (add hp E) P)
    have hBody1 := of_eq (OriginalTreeQuotationSyntax.tree_rename _ w body Fin.castSucc) (under (add hBody E) P)
    have hQuote := compiled_forward hZ1 site input hc f w.castSucc count.castSucc z.castSucc body.castSucc (Fin.last m)
      (fun i => (scopes i).castSucc) hw1 hz1 hs1 ht1 hp1 hBody1 (.conjR hP)
    have hE : Derives (Context.add E Γ) E := .hyp (Or.inl rfl)
    have hOut := of_eq (PureQuotationSyntax.formula_rename output w out Fin.castSucc) (under hE P)
    have hEq := OriginalTreeQuotationUnique.tree_unique hZ1 (PureSyntaxQuotation.formulaTree output)
      w.castSucc (Fin.last m) out.castSucc hw1 hQuote hOut
    let Q := SchemaAxiomCompilation.compiledMatrix site w.castSucc.castSucc count.castSucc.castSucc z.castSucc.castSucc
      body.castSucc.castSucc (Fin.last (m+1)) (fun i => (scopes i).castSucc.castSucc)
    have q0 : Q.instantiate (Fin.last m) = SchemaAxiomCompilation.compiledMatrix site w.castSucc count.castSucc z.castSucc body.castSucc (Fin.last m) (fun i => (scopes i).castSucc) := by
      simp only [Q,Formula.instantiate,SchemaAxiomCompilation.compiledMatrix_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
    have q1 : Q.instantiate out.castSucc = SchemaAxiomCompilation.compiledMatrix site w.castSucc count.castSucc z.castSucc body.castSucc out.castSucc (fun i => (scopes i).castSucc) := by
      simp only [Q,Formula.instantiate,SchemaAxiomCompilation.compiledMatrix_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
    have ho := of_eq q1 (Derives.eqSubst Q hEq (of_eq q0.symm (.conjR hP)))
    exact of_eq (SchemaAxiomCompilation.compiledMatrix_rename site w count z body out scopes Fin.castSucc).symm ho

private theorem scope_numerals {m n} {Γ : Context m} (count : Fin m) (scopes : Fin 4 → Fin m)
    (hn : Derives Γ (SyntaxNumeralSyntax.numeral n count)) (hc : Derives Γ (chain count scopes)) :
    ∀ i : Fin 4, Derives Γ (SyntaxNumeralSyntax.numeral (n+i.val+1) (scopes i)) := by
  have h0 := SyntaxNumeralSyntax.intro_succ n (scopes 0) count hn (.conjL hc)
  have h1 := SyntaxNumeralSyntax.intro_succ (n+1) (scopes 1) (scopes 0) h0 (.conjL (.conjR hc))
  have h2 := SyntaxNumeralSyntax.intro_succ (n+2) (scopes 2) (scopes 1) h1 (.conjL (.conjR (.conjR hc)))
  have h3 := SyntaxNumeralSyntax.intro_succ (n+3) (scopes 3) (scopes 2) h2 (.conjR (.conjR (.conjR hc)))
  intro i
  exact Fin.cases h0 (fun j => Fin.cases h1 (fun k => Fin.cases h2 (fun l => Fin.cases h3 (fun i => Fin.elim0 i) l) k) j) i

/-- Exact original site 0: actual raw compilation and original renamed matrix,
with all compiler/map/code/output witnesses constructed or internally bound. -/
theorem separation_iff {m n} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (input : YesMetaZFC.SetTheory.Definitional.Project.Formula 1 (n+1)) (hc : input.FreeClosed)
    (w count z body out : Fin m) (scopes : Fin 4 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (SyntaxNumeralSyntax.numeral n count))
    (hz : Derives Γ (empty z)) (hChain : Derives Γ (chain count scopes))
    (hBody : Derives Γ (OriginalTreeQuotationSyntax.tree
      (YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.ProjectEncode.formula input) w body))
    (hValid : Derives Γ (ProjectSourceCodeSyntax.sourceCode w body (sourceScope 0 scopes) z)) :
    Derives Γ ((SchemaAxiomCompilation.compiledMatrix 0 w count z body out scopes).iff
      (PureQuotationSyntax.formula (fo_formula (input.rename YesMetaZFC.SetTheory.BoundEmbedding.unaryUnderTwo)
        ((YesMetaZFC.SetTheory.Definitional.Formula.freeClosed_rename YesMetaZFC.SetTheory.BoundEmbedding.unaryUnderTwo input).mpr hc)) w out)) := by
  have hScopes := scope_numerals count scopes hn hChain
  have hPoints := graph_points_proved hZ 0 (YesMetaZFC.SetTheory.BoundEmbedding.unaryUnderTwo : Fin (n+1) → Fin (n+3))
    (fun {l} {Δ} hZ w count g scopes hw hn hChain hg j =>
      SchemaIndexQuotation.separation_value hZ w count g scopes hw hn hg j)
    w count scopes hw hn hChain
  exact compiled_iff hZ 0 input hc YesMetaZFC.SetTheory.BoundEmbedding.unaryUnderTwo w count z body out scopes hw hn hz hChain
    (of_eq (by rfl) (hScopes 0)) (of_eq (by rfl) (hScopes 2)) hPoints hBody hValid

/-- Exact original site 1: actual raw compilation and original renamed matrix,
with all compiler/map/code/output witnesses constructed or internally bound. -/
theorem collection_one_iff {m n} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (input : YesMetaZFC.SetTheory.Definitional.Project.Formula 1 (n+2)) (hc : input.FreeClosed)
    (w count z body out : Fin m) (scopes : Fin 4 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (SyntaxNumeralSyntax.numeral n count))
    (hz : Derives Γ (empty z)) (hChain : Derives Γ (chain count scopes))
    (hBody : Derives Γ (OriginalTreeQuotationSyntax.tree
      (YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.ProjectEncode.formula input) w body))
    (hValid : Derives Γ (ProjectSourceCodeSyntax.sourceCode w body (sourceScope 1 scopes) z)) :
    Derives Γ ((SchemaAxiomCompilation.compiledMatrix 1 w count z body out scopes).iff
      (PureQuotationSyntax.formula (fo_formula (input.rename YesMetaZFC.SetTheory.BoundEmbedding.binaryUnderOne)
        ((YesMetaZFC.SetTheory.Definitional.Formula.freeClosed_rename YesMetaZFC.SetTheory.BoundEmbedding.binaryUnderOne input).mpr hc)) w out)) := by
  have hScopes := scope_numerals count scopes hn hChain
  have hPoints := graph_points_proved hZ 1 (YesMetaZFC.SetTheory.BoundEmbedding.binaryUnderOne : Fin (n+2) → Fin (n+3))
    (fun {l} {Δ} hZ w count g scopes hw hn hChain hg j =>
      SchemaIndexQuotation.collection_one_value hZ w count g scopes hw hn hChain hg j)
    w count scopes hw hn hChain
  exact compiled_iff hZ 1 input hc YesMetaZFC.SetTheory.BoundEmbedding.binaryUnderOne w count z body out scopes hw hn hz hChain
    (of_eq (by rfl) (hScopes 1)) (of_eq (by rfl) (hScopes 2)) hPoints hBody hValid

/-- Exact original site 2: actual raw compilation and original renamed matrix,
with all compiler/map/code/output witnesses constructed or internally bound. -/
theorem collection_two_iff {m n} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (input : YesMetaZFC.SetTheory.Definitional.Project.Formula 1 (n+2)) (hc : input.FreeClosed)
    (w count z body out : Fin m) (scopes : Fin 4 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (SyntaxNumeralSyntax.numeral n count))
    (hz : Derives Γ (empty z)) (hChain : Derives Γ (chain count scopes))
    (hBody : Derives Γ (OriginalTreeQuotationSyntax.tree
      (YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.ProjectEncode.formula input) w body))
    (hValid : Derives Γ (ProjectSourceCodeSyntax.sourceCode w body (sourceScope 2 scopes) z)) :
    Derives Γ ((SchemaAxiomCompilation.compiledMatrix 2 w count z body out scopes).iff
      (PureQuotationSyntax.formula (fo_formula (input.rename YesMetaZFC.SetTheory.BoundEmbedding.binaryUnderTwo)
        ((YesMetaZFC.SetTheory.Definitional.Formula.freeClosed_rename YesMetaZFC.SetTheory.BoundEmbedding.binaryUnderTwo input).mpr hc)) w out)) := by
  have hScopes := scope_numerals count scopes hn hChain
  have hPoints := graph_points_proved hZ 2 (YesMetaZFC.SetTheory.BoundEmbedding.binaryUnderTwo : Fin (n+2) → Fin (n+4))
    (fun {l} {Δ} hZ w count g scopes hw hn hChain hg j =>
      SchemaIndexQuotation.collection_two_value hZ w count g scopes hw hn hChain hg j)
    w count scopes hw hn hChain
  exact compiled_iff hZ 2 input hc YesMetaZFC.SetTheory.BoundEmbedding.binaryUnderTwo w count z body out scopes hw hn hz hChain
    (of_eq (by rfl) (hScopes 1)) (of_eq (by rfl) (hScopes 3)) hPoints hBody hValid

private def assumptions {m parameterCount source : Nat} (site : Fin 3)
    (input : YesMetaZFC.SetTheory.Definitional.Project.Formula 1 source)
    (w count z body : Fin m) (scopes : Fin 4 → Fin m) : Source.Formula m :=
  (omega w).conj ((SyntaxNumeralSyntax.numeral parameterCount count).conj ((empty z).conj
    ((chain count scopes).conj ((OriginalTreeQuotationSyntax.tree
      (YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.ProjectEncode.formula input) w body).conj
        (ProjectSourceCodeSyntax.sourceCode w body (sourceScope site scopes) z)))))

/-- The final case-specific endpoints have ONLY the original raw input guards;
there is no given compiled body, index map, conversion, output or quotation of
any intermediate matrix. The external original body/count index the scheme. -/
def sentence {m source target} (parameterCount : Nat) (site : Fin 3)
    (input : YesMetaZFC.SetTheory.Definitional.Project.Formula 1 source) (hc : input.FreeClosed) (f : Fin source → Fin target)
    (w count z body out : Fin m) (scopes : Fin 4 → Fin m) : Source.Sentence :=
  ((assumptions (parameterCount := parameterCount) site input w count z body scopes).imp
    ((SchemaAxiomCompilation.compiledMatrix site w count z body out scopes).iff
      (PureQuotationSyntax.formula (fo_formula (input.rename f)
        ((YesMetaZFC.SetTheory.Definitional.Formula.freeClosed_rename f input).mpr hc)) w out))).close

private theorem source_certificate {m parameterCount source target} (site : Fin 3)
    (input : YesMetaZFC.SetTheory.Definitional.Project.Formula 1 source) (hc : input.FreeClosed) (f : Fin source → Fin target)
    (prover : ∀ {l} {Δ : Context l}, ZFContext.Evidence Δ → ∀ (w count z body out : Fin l) (scopes : Fin 4 → Fin l),
      Derives Δ (omega w) → Derives Δ (SyntaxNumeralSyntax.numeral parameterCount count) → Derives Δ (empty z) →
      Derives Δ (chain count scopes) → Derives Δ (OriginalTreeQuotationSyntax.tree
        (YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.ProjectEncode.formula input) w body) →
      Derives Δ (ProjectSourceCodeSyntax.sourceCode w body (sourceScope site scopes) z) →
      Derives Δ ((SchemaAxiomCompilation.compiledMatrix site w count z body out scopes).iff
        (PureQuotationSyntax.formula (fo_formula (input.rename f)
          ((YesMetaZFC.SetTheory.Definitional.Formula.freeClosed_rename f input).mpr hc)) w out)))
    (w count z body out : Fin m) (scopes : Fin 4 → Fin m) :
    Derives (Source.SetLanguage.ZF.at 0) (sentence parameterCount site input hc f w count z body out scopes) := by
  apply close_derives
  apply Derives.impI
  let F := assumptions (parameterCount := parameterCount) site input w count z body scopes
  let Δ := Context.add F (Source.SetLanguage.ZF.at m)
  have hF : Derives Δ F := .hyp (Or.inl rfl)
  have hZ := ZFContext.add (ZFContext.source_ZF m) F
  have hRest := Derives.conjR (.conjR (.conjR hF))
  exact prover hZ w count z body out scopes (.conjL hF) (.conjL (.conjR hF)) (.conjL (.conjR (.conjR hF)))
    (.conjL hRest) (.conjL (.conjR hRest)) (.conjR (.conjR hRest))

theorem separation_kernel_certificate {m n}
    (input : YesMetaZFC.SetTheory.Definitional.Project.Formula 1 (n+1)) (hc : input.FreeClosed)
    (w count z body out : Fin m) (scopes : Fin 4 → Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
      (Translation.sentence (sentence n 0 input hc YesMetaZFC.SetTheory.BoundEmbedding.unaryUnderTwo w count z body out scopes)) :=
  ZFReplay.replay (TheoryTransport.sentence (source_certificate 0 input hc YesMetaZFC.SetTheory.BoundEmbedding.unaryUnderTwo
    (fun hZ w count z body out scopes hw hn hz hChain hBody hValid =>
      separation_iff hZ input hc w count z body out scopes hw hn hz hChain hBody hValid)
    w count z body out scopes))

theorem collection_one_kernel_certificate {m n}
    (input : YesMetaZFC.SetTheory.Definitional.Project.Formula 1 (n+2)) (hc : input.FreeClosed)
    (w count z body out : Fin m) (scopes : Fin 4 → Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
      (Translation.sentence (sentence n 1 input hc YesMetaZFC.SetTheory.BoundEmbedding.binaryUnderOne w count z body out scopes)) :=
  ZFReplay.replay (TheoryTransport.sentence (source_certificate 1 input hc YesMetaZFC.SetTheory.BoundEmbedding.binaryUnderOne
    (fun hZ w count z body out scopes hw hn hz hChain hBody hValid =>
      collection_one_iff hZ input hc w count z body out scopes hw hn hz hChain hBody hValid)
    w count z body out scopes))

theorem collection_two_kernel_certificate {m n}
    (input : YesMetaZFC.SetTheory.Definitional.Project.Formula 1 (n+2)) (hc : input.FreeClosed)
    (w count z body out : Fin m) (scopes : Fin 4 → Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
      (Translation.sentence (sentence n 2 input hc YesMetaZFC.SetTheory.BoundEmbedding.binaryUnderTwo w count z body out scopes)) :=
  ZFReplay.replay (TheoryTransport.sentence (source_certificate 2 input hc YesMetaZFC.SetTheory.BoundEmbedding.binaryUnderTwo
    (fun hZ w count z body out scopes hw hn hz hChain hBody hValid =>
      collection_two_iff hZ input hc w count z body out scopes hw hn hz hChain hBody hValid)
    w count z body out scopes))

end PPAC.Migration.SchemaMatrixQuotation
