/- Connect existing actual Project compilation and the three ORIGINAL schema
renaming sites. All maps, codes, identity and renamed output are constructed
inside the object proof. The source input and count remain unrestricted
internal objects; no given compiler/map/output/law is a final premise. -/
import PPAC.Migration.SchemaAxiomAssembly
import PPAC.Migration.Internal.ProjectCompilerUniqueFiber
import PPAC.Migration.Internal.SyntaxRenameJudgment

namespace PPAC.Migration.SchemaAxiomCompilation
open Source SourceAlgebra SourceLogic OmegaSyntax
open PPAC.Migration.Internal
open PPAC.Migration.Internal.HornBinderSyntax
open PPAC.Migration.Internal.SchemaIndexSyntax
open PPAC.Migration.Internal.SyntaxRenameQuerySyntax (of_eq)
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 800000

def renamedBody {m} (site : Fin 3) (w count z : Fin m) (scopes : Fin 4 → Fin m) (a out : Fin m) : Source.Formula (m+3) :=
  (SchemaIndexRenameSystem.system site (old 3 w) (old 3 count) (old 3 z) (fun i => old 3 (scopes i))
    (slot 3 0) (slot 3 1) (slot 3 2)).conj
  (SyntaxRenameJudgmentSyntax.renamed (old 3 w) (slot 3 1) (slot 3 2)
    (old 3 (sourceScope site scopes)) (old 3 z) (old 3 (targetScope site scopes)) (old 3 z) (old 3 a) (old 3 out))

def renamedMatrix {m} (site : Fin 3) (w count z : Fin m) (scopes : Fin 4 → Fin m) (a out : Fin m) : Source.Formula m :=
  existsMany 3 (renamedBody site w count z scopes a out)

def existsRenamed {m} (site : Fin 3) (w count z : Fin m) (scopes : Fin 4 → Fin m) (a : Fin m) : Source.Formula m := .ex
  ((Source.Formula.mem (Fin.last m) w.castSucc).conj
    (renamedMatrix site w.castSucc count.castSucc z.castSucc (fun i => (scopes i).castSucc) a.castSucc (Fin.last m)))

theorem renamedBody_lift {m l} (site : Fin 3) (w count z a out : Fin m) (scopes : Fin 4 → Fin m) (r : Fin m → Fin l) :
    (renamedBody site w count z scopes a out).rename (lift 3 r) = renamedBody site (r w) (r count) (r z) (fun i => r (scopes i)) (r a) (r out) := by
  simp only [renamedBody,Formula.rename,SchemaIndexRenameSystem.system_rename,SyntaxRenameJudgmentSyntax.renamed_rename,
    lift_old,lift_slot,sourceScope_map,targetScope_map]

theorem renamedMatrix_rename {m l} (site : Fin 3) (w count z a out : Fin m) (scopes : Fin 4 → Fin m) (r : Fin m → Fin l) :
    (renamedMatrix site w count z scopes a out).rename r = renamedMatrix site (r w) (r count) (r z) (fun i => r (scopes i)) (r a) (r out) := by
  simp only [renamedMatrix,existsMany_rename,renamedBody_lift]

theorem existsRenamed_rename {m l} (site : Fin 3) (w count z a : Fin m) (scopes : Fin 4 → Fin m) (r : Fin m → Fin l) :
    (existsRenamed site w count z scopes a).rename r = existsRenamed site (r w) (r count) (r z) (fun i => r (scopes i)) (r a) := by
  simp only [existsRenamed,Formula.rename,renamedMatrix_rename,Formula.liftRen,Fin.lastCases_last,Fin.lastCases_castSucc]

private theorem intro_matrix {m} {Γ : Context m} (site : Fin 3) (w count z a out g R S : Fin m)
    (scopes : Fin 4 → Fin m)
    (hs : Derives Γ (SchemaIndexRenameSystem.system site w count z scopes g R S))
    (hr : Derives Γ (SyntaxRenameJudgmentSyntax.renamed w R S (sourceScope site scopes) z (targetScope site scopes) z a out)) :
    Derives Γ (renamedMatrix site w count z scopes a out) := by
  apply HornBinderRules.intro_many 3 (renamedBody site w count z scopes a out) (Source.SetLanguage.args3 g R S)
  exact of_eq (by simp only [renamedBody,Formula.rename,SchemaIndexRenameSystem.system_rename,
    SyntaxRenameJudgmentSyntax.renamed_rename,assign_old,assign_slot]; rfl) (.conjI hs hr)

/-- Every produced result retains the actual target type, not just a number. -/
theorem renamed_target_type {m} {Γ : Context m} (site : Fin 3) (w count z a out : Fin m)
    (scopes : Fin 4 → Fin m) (h : Derives Γ (renamedMatrix site w count z scopes a out)) :
    Derives Γ (FormulaCodeSyntax.formulaCode w out (targetScope site scopes) z) := by
  let B := renamedBody site w count z scopes a out
  let Δ := Context.add B (raisedContext 3 Γ)
  apply HornBinderRules.eliminate_many 3 B _ h
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have ht := SyntaxRenameJudgment.target_type (old 3 w) (slot 3 1) (slot 3 2)
    (old 3 (sourceScope site scopes)) (old 3 z) (old 3 (targetScope site scopes)) (old 3 z) (old 3 a) (old 3 out) (.conjR hB)
  exact of_eq (FormulaCodeSyntax.formulaCode_rename w out (targetScope site scopes) z (old 3)).symm ht

private theorem at_coded_state {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (site : Fin 3)
    (w count z a g R : Fin m) (scopes : Fin 4 → Fin m) (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hc : Derives Γ (codedState site w count scopes g R))
    (ha : Derives Γ (FormulaCodeSyntax.formulaCode w a (sourceScope site scopes) z)) :
    Derives Γ (existsRenamed site w count z scopes a) := by
  have hzW := OmegaStructureAlgebra.zero_member w z (ZFContext.arithmetic hZ).base.extensionality hw hz
  let S := SyntaxIdentityMapSyntax.identityCode w.castSucc z.castSucc (Fin.last m)
  let Δ := Context.add S (Context.image Formula.raise Γ)
  apply Derives.exE (p := S) (SyntaxIdentityCode.exists_code hZ w z hw hzW)
  have hZ1 := ZFContext.under hZ S
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw S)
  have hc1 := of_eq (codedState_rename site w count scopes g R Fin.castSucc) (under hc S)
  have ha1 : Derives Δ (FormulaCodeSyntax.formulaCode w.castSucc a.castSucc (sourceScope site (fun i => (scopes i).castSucc)) z.castSucc) := by
    simpa only [Formula.raise,FormulaCodeSyntax.formulaCode_rename,sourceScope_map] using under ha S
  have hS : Derives Δ S := .hyp (Or.inl rfl)
  have hR : Derives Δ (SyntaxMapCodeSyntax.encoded w.castSucc g.castSucc
      (sourceScope site (fun i => (scopes i).castSucc)) (targetScope site (fun i => (scopes i).castSucc)) R.castSucc) := by
    simpa only [sourceScope_map,targetScope_map] using Derives.conjR hc1
  have hl := SchemaIndexRenameSystem.law_proved hZ1 site w.castSucc (fun i => (scopes i).castSucc) g.castSucc R.castSucc (Fin.last m) z.castSucc hw1 hR hS
  have hs : Derives Δ (SchemaIndexRenameSystem.system site w.castSucc count.castSucc z.castSucc
      (fun i => (scopes i).castSucc) g.castSucc R.castSucc (Fin.last m)) := .conjI hc1 (.conjI hS hl)
  have he := SchemaIndexRenameSystem.law_at site w.castSucc (fun i => (scopes i).castSucc) R.castSucc (Fin.last m) z.castSucc a.castSucc hl ha1
  let Y := (SyntaxRenameJudgmentSyntax.renamed w.castSucc.castSucc R.castSucc.castSucc (Fin.last m).castSucc
    (sourceScope site (fun i => (scopes i).castSucc)).castSucc z.castSucc.castSucc
    (targetScope site (fun i => (scopes i).castSucc)).castSucc z.castSucc.castSucc a.castSucc.castSucc (Fin.last (m+1))).conj
      (SyntaxRenameOutputSyntax.uniqueOutput w.castSucc.castSucc R.castSucc.castSucc (Fin.last m).castSucc
        (sourceScope site (fun i => (scopes i).castSucc)).castSucc z.castSucc.castSucc
        (targetScope site (fun i => (scopes i).castSucc)).castSucc z.castSucc.castSucc a.castSucc.castSucc (Fin.last (m+1)))
  let Ξ := Context.add Y (Context.image Formula.raise Δ)
  apply Derives.exE (p := Y) he
  have hY : Derives Ξ Y := .hyp (Or.inl rfl)
  have hs2 : Derives Ξ (SchemaIndexRenameSystem.system site w.castSucc.castSucc count.castSucc.castSucc z.castSucc.castSucc
      (fun i => (scopes i).castSucc.castSucc) g.castSucc.castSucc R.castSucc.castSucc (Fin.last m).castSucc) := by
    simpa only [Formula.raise,SchemaIndexRenameSystem.system_rename] using under hs Y
  have hr : Derives Ξ (SyntaxRenameJudgmentSyntax.renamed w.castSucc.castSucc R.castSucc.castSucc (Fin.last m).castSucc
      (sourceScope site (fun i => (scopes i).castSucc.castSucc)) z.castSucc.castSucc
      (targetScope site (fun i => (scopes i).castSucc.castSucc)) z.castSucc.castSucc a.castSucc.castSucc (Fin.last (m+1))) := by
    simpa only [sourceScope_map,targetScope_map] using Derives.conjL hY
  have ht := SyntaxRenameJudgment.target_type _ _ _ _ _ _ _ _ _ hr
  have hn := Derives.conjL (FormulaCodeProperties.guards _ _ _ _ ht)
  have hm := intro_matrix site w.castSucc.castSucc count.castSucc.castSucc z.castSucc.castSucc a.castSucc.castSucc
    (Fin.last (m+1)) g.castSucc.castSucc R.castSucc.castSucc (Fin.last m).castSucc (fun i => (scopes i).castSucc.castSucc) hs2 hr
  have ho : Derives Ξ (existsRenamed site w.castSucc.castSucc count.castSucc.castSucc z.castSucc.castSucc
      (fun i => (scopes i).castSucc.castSucc) a.castSucc.castSucc) := by
    apply Derives.exI (Fin.last (m+1))
    exact of_eq (by simp only [Formula.instantiate,Formula.rename,renamedMatrix_rename,
      Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]) (.conjI hn hm)
  exact of_eq (by simp only [Formula.raise,existsRenamed_rename]) ho

private theorem at_graph {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (site : Fin 3)
    (w count z a g : Fin m) (scopes : Fin 4 → Fin m) (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hc : Derives Γ (chain count scopes)) (hg : Derives Γ (SchemaIndexSyntax.graph site w count scopes g))
    (ha : Derives Γ (FormulaCodeSyntax.formulaCode w a (sourceScope site scopes) z)) :
    Derives Γ (existsRenamed site w count z scopes a) := by
  have hMap := SchemaIndexFacts.graph_map site w count scopes g hg
  let R := SyntaxMapCodeSyntax.encoded w.castSucc g.castSucc (sourceScope site scopes).castSucc (targetScope site scopes).castSucc (Fin.last m)
  let Δ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) (SyntaxMapCodeExistence.exists_code hZ w g (sourceScope site scopes) (targetScope site scopes) hw hMap)
  have hc1 := of_eq (chain_rename count scopes Fin.castSucc) (under hc R)
  have hg1 := of_eq (SchemaIndexSyntax.graph_rename site w count scopes g Fin.castSucc) (under hg R)
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hcoded : Derives Δ (codedState site w.castSucc count.castSucc (fun i => (scopes i).castSucc) g.castSucc (Fin.last m)) := by
    simpa only [codedState,state,sourceScope_map,targetScope_map] using Derives.conjI (Derives.conjI hc1 hg1) hR
  have ho := at_coded_state (ZFContext.under hZ R) site w.castSucc count.castSucc z.castSucc a.castSucc g.castSucc (Fin.last m)
    (fun i => (scopes i).castSucc) (of_eq (omega_rename w Fin.castSucc) (under hw R)) (of_eq (empty_rename z Fin.castSucc) (under hz R)) hcoded
    (by simpa only [Formula.raise,FormulaCodeSyntax.formulaCode_rename,sourceScope_map] using under ha R)
  exact of_eq (existsRenamed_rename site w count z a scopes Fin.castSucc).symm ho

/-- All three ORIGINAL schema maps and their codes/identity/output are actual
object witnesses; the only parents are the source scope chain and typed input. -/
theorem exists_renamed {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (site : Fin 3)
    (w count z a : Fin m) (scopes : Fin 4 → Fin m) (hw : Derives Γ (omega w)) (hn : Derives Γ (Source.Formula.mem count w))
    (hz : Derives Γ (empty z)) (hc : Derives Γ (chain count scopes))
    (ha : Derives Γ (FormulaCodeSyntax.formulaCode w a (sourceScope site scopes) z)) :
    Derives Γ (existsRenamed site w count z scopes a) := by
  let G := SchemaIndexSyntax.graph site w.castSucc count.castSucc (fun i => (scopes i).castSucc) (Fin.last m)
  let Δ := Context.add G (Context.image Formula.raise Γ)
  apply Derives.exE (p := G) (SchemaIndexGraphExistence.exists_graph hZ site w count scopes hw hn hc)
  have ho := at_graph (ZFContext.under hZ G) site w.castSucc count.castSucc z.castSucc a.castSucc (Fin.last m) (fun i => (scopes i).castSucc)
    (of_eq (omega_rename w Fin.castSucc) (under hw G)) (of_eq (empty_rename z Fin.castSucc) (under hz G))
    (of_eq (chain_rename count scopes Fin.castSucc) (under hc G)) (.hyp (Or.inl rfl))
    (by simpa only [Formula.raise,FormulaCodeSyntax.formulaCode_rename,sourceScope_map] using under ha G)
  exact of_eq (existsRenamed_rename site w count z a scopes Fin.castSucc).symm ho

def compiledBody {m} (site : Fin 3) (w count z body out : Fin m) (scopes : Fin 4 → Fin m) : Source.Formula (m+1) :=
  (ProjectCompilerCodeSyntax.compiled w.castSucc body.castSucc (sourceScope site scopes).castSucc (Fin.last m)).conj
    (renamedMatrix site w.castSucc count.castSucc z.castSucc (fun i => (scopes i).castSucc) (Fin.last m) out.castSucc)

def compiledMatrix {m} (site : Fin 3) (w count z body out : Fin m) (scopes : Fin 4 → Fin m) : Source.Formula m :=
  .ex (compiledBody site w count z body out scopes)

def existsCompiled {m} (site : Fin 3) (w count z body : Fin m) (scopes : Fin 4 → Fin m) : Source.Formula m := .ex
  ((Source.Formula.mem (Fin.last m) w.castSucc).conj (compiledMatrix site w.castSucc count.castSucc z.castSucc body.castSucc (Fin.last m) (fun i => (scopes i).castSucc)))

theorem compiledMatrix_rename {m l} (site : Fin 3) (w count z body out : Fin m) (scopes : Fin 4 → Fin m) (r : Fin m → Fin l) :
    (compiledMatrix site w count z body out scopes).rename r = compiledMatrix site (r w) (r count) (r z) (r body) (r out) (fun i => r (scopes i)) := by
  simp only [compiledMatrix,compiledBody,Formula.rename,ProjectCompilerCodeSyntax.compiled_rename,renamedMatrix_rename,
    sourceScope_map,Formula.liftRen,Fin.lastCases_last,Fin.lastCases_castSucc]

theorem existsCompiled_rename {m l} (site : Fin 3) (w count z body : Fin m) (scopes : Fin 4 → Fin m) (r : Fin m → Fin l) :
    (existsCompiled site w count z body scopes).rename r = existsCompiled site (r w) (r count) (r z) (r body) (fun i => r (scopes i)) := by
  simp only [existsCompiled,Formula.rename,compiledMatrix_rename,Formula.liftRen,Fin.lastCases_last,Fin.lastCases_castSucc]

theorem compiled_target_type {m} {Γ : Context m} (site : Fin 3) (w count z body out : Fin m) (scopes : Fin 4 → Fin m)
    (h : Derives Γ (compiledMatrix site w count z body out scopes)) :
    Derives Γ (FormulaCodeSyntax.formulaCode w out (targetScope site scopes) z) := by
  let B := compiledBody site w count z body out scopes
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) h
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have ht := renamed_target_type site w.castSucc count.castSucc z.castSucc (Fin.last m) out.castSucc (fun i => (scopes i).castSucc) (.conjR hB)
  exact of_eq (by simp only [Formula.raise,FormulaCodeSyntax.formulaCode_rename,targetScope_map]) ht

/-- Actual original Project source body -> actual typed renamed pure formula.
Neither a compiled body nor any map/system/output is given as a parent. -/
theorem exists_compiled {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (site : Fin 3)
    (w count z body : Fin m) (scopes : Fin 4 → Fin m) (hw : Derives Γ (omega w)) (hn : Derives Γ (Source.Formula.mem count w))
    (hz : Derives Γ (empty z)) (hc : Derives Γ (chain count scopes))
    (ha : Derives Γ (ProjectSourceCodeSyntax.sourceCode w body (sourceScope site scopes) z)) :
    Derives Γ (existsCompiled site w count z body scopes) := by
  let C := (ProjectCompilerCodeSyntax.compiled w.castSucc body.castSucc (sourceScope site scopes).castSucc (Fin.last m)).conj
    (FormulaCodeSyntax.formulaCode w.castSucc (Fin.last m) (sourceScope site scopes).castSucc z.castSucc)
  let Δ := Context.add C (Context.image Formula.raise Γ)
  apply Derives.exE (p := C) (ProjectCompilerComplete.typed_output_exists hZ w body (sourceScope site scopes) z z hw hz ha)
  have hC : Derives Δ C := .hyp (Or.inl rfl)
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw C)
  have hn1 := under hn C
  have hz1 := of_eq (empty_rename z Fin.castSucc) (under hz C)
  have hc1 := of_eq (chain_rename count scopes Fin.castSucc) (under hc C)
  have ht : Derives Δ (FormulaCodeSyntax.formulaCode w.castSucc (Fin.last m) (sourceScope site (fun i => (scopes i).castSucc)) z.castSucc) := by
    simpa only [sourceScope_map] using Derives.conjR hC
  have he := exists_renamed (ZFContext.under hZ C) site w.castSucc count.castSucc z.castSucc (Fin.last m) (fun i => (scopes i).castSucc) hw1 hn1 hz1 hc1 ht
  let Y := (Source.Formula.mem (Fin.last (m+1)) w.castSucc.castSucc).conj (renamedMatrix site w.castSucc.castSucc count.castSucc.castSucc z.castSucc.castSucc
    (fun i => (scopes i).castSucc.castSucc) (Fin.last m).castSucc (Fin.last (m+1)))
  let Ξ := Context.add Y (Context.image Formula.raise Δ)
  apply Derives.exE (p := Y) he
  have hY : Derives Ξ Y := .hyp (Or.inl rfl)
  have hC2 : Derives Ξ ((ProjectCompilerCodeSyntax.compiled w.castSucc.castSucc body.castSucc.castSucc
      (sourceScope site scopes).castSucc.castSucc (Fin.last m).castSucc).conj
    (FormulaCodeSyntax.formulaCode w.castSucc.castSucc (Fin.last m).castSucc (sourceScope site scopes).castSucc.castSucc z.castSucc.castSucc)) := by
    simpa only [C,Formula.raise,Formula.rename,ProjectCompilerCodeSyntax.compiled_rename,FormulaCodeSyntax.formulaCode_rename] using under hC Y
  have hm : Derives Ξ (compiledMatrix site w.castSucc.castSucc count.castSucc.castSucc z.castSucc.castSucc body.castSucc.castSucc
      (Fin.last (m+1)) (fun i => (scopes i).castSucc.castSucc)) := by
    apply Derives.exI (Fin.last m).castSucc
    simp only [compiledBody,Formula.instantiate,Formula.rename,ProjectCompilerCodeSyntax.compiled_rename,renamedMatrix_rename,
      sourceScope_map,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
    exact .conjI (.conjL hC2) (.conjR hY)
  have ho : Derives Ξ (existsCompiled site w.castSucc.castSucc count.castSucc.castSucc z.castSucc.castSucc body.castSucc.castSucc
      (fun i => (scopes i).castSucc.castSucc)) := by
    apply Derives.exI (Fin.last (m+1))
    exact of_eq (by simp only [Formula.instantiate,Formula.rename,compiledMatrix_rename,
      Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]) (.conjI (.conjL hY) hm)
  exact of_eq (by simp only [Formula.raise,existsCompiled_rename]) ho

def sentence {m} (site : Fin 3) (w count z body : Fin m) (scopes : Fin 4 → Fin m) : Source.Sentence :=
  ((omega w).imp ((Source.Formula.mem count w).imp ((empty z).imp ((chain count scopes).imp
    ((ProjectSourceCodeSyntax.sourceCode w body (sourceScope site scopes) z).imp (existsCompiled site w count z body scopes)))))).close

theorem source_certificate {m} (site : Fin 3) (w count z body : Fin m) (scopes : Fin 4 → Fin m) :
    Derives (Source.SetLanguage.ZF.at 0) (sentence site w count z body scopes) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ := Context.add (ProjectSourceCodeSyntax.sourceCode w body (sourceScope site scopes) z)
    (Context.add (chain count scopes) (Context.add (empty z) (Context.add (Source.Formula.mem count w) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.source_ZF m) _) _) _) _) _
  exact exists_compiled hZ site w count z body scopes (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) (.hyp (Or.inr (Or.inr (Or.inl rfl))))
    (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem kernel_certificate {m} (site : Fin 3) (w count z body : Fin m) (scopes : Fin 4 → Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (sentence site w count z body scopes)) :=
  ZFReplay.replay (TheoryTransport.sentence (source_certificate site w count z body scopes))


attribute [local irreducible] compiledMatrix SchemaAxiomAssembly.assembled

/-- Separation uses site 0, Collection starts at site 1. -/
def firstSite (collection : Bool) : Fin 3 := if collection then 1 else 0

/-- Retain both actual compiled/renamed matrices and the original shell/closure.
Collection's two producers consume the SAME raw body and source scope. -/
def schemaBody {m} (collection : Bool) (w count z body out : Fin m) (scopes : Fin 4 → Fin m) : Source.Formula (m+2) :=
  (compiledMatrix (firstSite collection) (old 2 w) (old 2 count) (old 2 z) (old 2 body) (slot 2 0)
    (fun i => old 2 (scopes i))).conj
  ((if collection then compiledMatrix 2 (old 2 w) (old 2 count) (old 2 z) (old 2 body) (slot 2 1)
      (fun i => old 2 (scopes i)) else Formula.equal (slot 2 1) (slot 2 0)).conj
    (SchemaAxiomAssembly.assembled collection (old 2 w) (old 2 count)
      (fun i => if i.val = 0 then slot 2 0 else slot 2 1) (old 2 out)))

def schemaResult {m} (collection : Bool) (w count z body out : Fin m) (scopes : Fin 4 → Fin m) : Source.Formula m :=
  existsMany 2 (schemaBody collection w count z body out scopes)

def existsSchema {m} (collection : Bool) (w count z body : Fin m) (scopes : Fin 4 → Fin m) : Source.Formula m := .ex
  ((Source.Formula.mem (Fin.last m) w.castSucc).conj
    (schemaResult collection w.castSucc count.castSucc z.castSucc body.castSucc (Fin.last m) (fun i => (scopes i).castSucc)))

theorem schemaBody_lift {m l} (collection : Bool) (w count z body out : Fin m) (scopes : Fin 4 → Fin m) (r : Fin m → Fin l) :
    (schemaBody collection w count z body out scopes).rename (lift 2 r) =
      schemaBody collection (r w) (r count) (r z) (r body) (r out) (fun i => r (scopes i)) := by
  cases collection <;> simp only [schemaBody,Bool.false_eq_true,↓reduceIte,Formula.rename,
    compiledMatrix_rename,SchemaAxiomAssembly.assembled_rename,lift_old,apply_ite,lift_slot]

theorem schemaResult_rename {m l} (collection : Bool) (w count z body out : Fin m) (scopes : Fin 4 → Fin m) (r : Fin m → Fin l) :
    (schemaResult collection w count z body out scopes).rename r =
      schemaResult collection (r w) (r count) (r z) (r body) (r out) (fun i => r (scopes i)) := by
  simp only [schemaResult,existsMany_rename,schemaBody_lift]

theorem existsSchema_rename {m l} (collection : Bool) (w count z body : Fin m) (scopes : Fin 4 → Fin m) (r : Fin m → Fin l) :
    (existsSchema collection w count z body scopes).rename r =
      existsSchema collection (r w) (r count) (r z) (r body) (fun i => r (scopes i)) := by
  simp only [existsSchema,Formula.rename,schemaResult_rename,Formula.liftRen,Fin.lastCases_last,Fin.lastCases_castSucc]

private theorem finish_schema {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (collection : Bool)
    (w count z body x y : Fin m) (scopes : Fin 4 → Fin m) (hw : Derives Γ (omega w))
    (hn : Derives Γ (Source.Formula.mem count w)) (hxW : Derives Γ (Source.Formula.mem x w))
    (hyW : Derives Γ (Source.Formula.mem y w))
    (hx : Derives Γ (compiledMatrix (firstSite collection) w count z body x scopes))
    (hy : Derives Γ (if collection then compiledMatrix 2 w count z body y scopes else Formula.equal y x)) :
    Derives Γ (existsSchema collection w count z body scopes) := by
  let v : Fin 3 → Fin m := fun i => if i.val = 0 then x else y
  have hv : Derives Γ (HornExprSyntax.environmentNat 3 w v) := by
    change Derives Γ ((Source.Formula.mem x w).conj ((Source.Formula.mem y w).conj
      ((Source.Formula.mem y w).conj (Formula.bot.imp Formula.bot))))
    exact .conjI hxW (.conjI hyW (.conjI hyW (.impI (.hyp (Or.inl rfl)))))
  let O := (Source.Formula.mem (Fin.last m) w.castSucc).conj
    (SchemaAxiomAssembly.assembled collection w.castSucc count.castSucc (fun i => (v i).castSucc) (Fin.last m))
  let Δ := Context.add O (Context.image Formula.raise Γ)
  apply Derives.exE (p := O) (SchemaAxiomAssembly.output_exists hZ collection w count v hw hn hv)
  have hO : Derives Δ O := .hyp (Or.inl rfl)
  have hx1 := of_eq (compiledMatrix_rename (firstSite collection) w count z body x scopes Fin.castSucc) (under hx O)
  have hy1 : Derives Δ (if collection then compiledMatrix 2 w.castSucc count.castSucc z.castSucc body.castSucc y.castSucc
      (fun i => (scopes i).castSucc) else Formula.equal y.castSucc x.castSucc) := by
    cases collection <;> simpa only [Bool.false_eq_true,↓reduceIte,Formula.raise,Formula.rename,compiledMatrix_rename] using under hy O
  let M := (compiledMatrix (firstSite collection) w.castSucc count.castSucc z.castSucc body.castSucc x.castSucc
    (fun i => (scopes i).castSucc)).conj
      ((if collection then compiledMatrix 2 w.castSucc count.castSucc z.castSucc body.castSucc y.castSucc
        (fun i => (scopes i).castSucc) else Formula.equal y.castSucc x.castSucc).conj
          (SchemaAxiomAssembly.assembled collection w.castSucc count.castSucc (fun i => (v i).castSucc) (Fin.last m)))
  have hM : Derives Δ M := .conjI hx1 (.conjI hy1 (.conjR hO))
  have hEq : M = (schemaBody collection w.castSucc count.castSucc z.castSucc body.castSucc (Fin.last m)
      (fun i => (scopes i).castSucc)).rename (assign 2 (Source.SetLanguage.args2 x.castSucc y.castSucc)) := by
    cases collection <;>
      simp only [M,v,schemaBody,Bool.false_eq_true,↓reduceIte,Formula.rename,compiledMatrix_rename,
        SchemaAxiomAssembly.assembled_rename,assign_old,apply_ite,assign_slot]
    all_goals rfl
  have hm : Derives Δ (schemaResult collection w.castSucc count.castSucc z.castSucc body.castSucc (Fin.last m)
      (fun i => (scopes i).castSucc)) :=
    HornBinderRules.intro_many 2 (schemaBody collection w.castSucc count.castSucc z.castSucc body.castSucc
      (Fin.last m) (fun i => (scopes i).castSucc)) (Source.SetLanguage.args2 x.castSucc y.castSucc) (of_eq hEq hM)
  have ho : Derives Δ (existsSchema collection w.castSucc count.castSucc z.castSucc body.castSucc (fun i => (scopes i).castSucc)) := by
    apply Derives.exI (Fin.last m)
    exact of_eq (by simp only [Formula.instantiate,Formula.rename,schemaResult_rename,
      Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]) (.conjI (.conjL hO) hm)
  exact of_eq (existsSchema_rename collection w count z body scopes Fin.castSucc).symm ho

private theorem after_first {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (collection : Bool)
    (w count z body x : Fin m) (scopes : Fin 4 → Fin m) (hw : Derives Γ (omega w))
    (hn : Derives Γ (Source.Formula.mem count w)) (hz : Derives Γ (empty z)) (hc : Derives Γ (chain count scopes))
    (ha : Derives Γ (ProjectSourceCodeSyntax.sourceCode w body (sourceScope (firstSite collection) scopes) z))
    (hxW : Derives Γ (Source.Formula.mem x w))
    (hx : Derives Γ (compiledMatrix (firstSite collection) w count z body x scopes)) :
    Derives Γ (existsSchema collection w count z body scopes) := by
  cases collection with
  | false => exact finish_schema hZ false w count z body x x scopes hw hn hxW hxW hx (.eqRefl x)
  | true =>
    have ha2 : Derives Γ (ProjectSourceCodeSyntax.sourceCode w body (sourceScope 2 scopes) z) := by
      exact ha
    let Y := (Source.Formula.mem (Fin.last m) w.castSucc).conj
      (compiledMatrix 2 w.castSucc count.castSucc z.castSucc body.castSucc (Fin.last m) (fun i => (scopes i).castSucc))
    let Δ := Context.add Y (Context.image Formula.raise Γ)
    apply Derives.exE (p := Y) (exists_compiled hZ 2 w count z body scopes hw hn hz hc ha2)
    have hY : Derives Δ Y := .hyp (Or.inl rfl)
    have hx1 := of_eq (compiledMatrix_rename (firstSite true) w count z body x scopes Fin.castSucc) (under hx Y)
    have ho := finish_schema (ZFContext.under hZ Y) true w.castSucc count.castSucc z.castSucc body.castSucc x.castSucc (Fin.last m)
      (fun i => (scopes i).castSucc) (of_eq (omega_rename w Fin.castSucc) (under hw Y))
      (under hn Y) (under hxW Y) (.conjL hY) hx1 (.conjR hY)
    exact of_eq (existsSchema_rename true w count z body scopes Fin.castSucc).symm ho

/-- The raw original schema body supplies EVERY compiled/renamed matrix and
then the original shell plus full internal-count closure. No output is given. -/
theorem schema_output_exists {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (collection : Bool)
    (w count z body : Fin m) (scopes : Fin 4 → Fin m) (hw : Derives Γ (omega w))
    (hn : Derives Γ (Source.Formula.mem count w)) (hz : Derives Γ (empty z)) (hc : Derives Γ (chain count scopes))
    (ha : Derives Γ (ProjectSourceCodeSyntax.sourceCode w body (sourceScope (firstSite collection) scopes) z)) :
    Derives Γ (existsSchema collection w count z body scopes) := by
  let X := (Source.Formula.mem (Fin.last m) w.castSucc).conj
    (compiledMatrix (firstSite collection) w.castSucc count.castSucc z.castSucc body.castSucc (Fin.last m) (fun i => (scopes i).castSucc))
  let Δ := Context.add X (Context.image Formula.raise Γ)
  apply Derives.exE (p := X) (exists_compiled hZ (firstSite collection) w count z body scopes hw hn hz hc ha)
  have hX : Derives Δ X := .hyp (Or.inl rfl)
  have ho := after_first (ZFContext.under hZ X) collection w.castSucc count.castSucc z.castSucc body.castSucc (Fin.last m)
    (fun i => (scopes i).castSucc) (of_eq (omega_rename w Fin.castSucc) (under hw X)) (under hn X)
    (of_eq (empty_rename z Fin.castSucc) (under hz X)) (of_eq (chain_rename count scopes Fin.castSucc) (under hc X))
    (by simpa only [Formula.raise,ProjectSourceCodeSyntax.sourceCode_rename,sourceScope_map] using under ha X) (.conjL hX) (.conjR hX)
  exact of_eq (existsSchema_rename collection w count z body scopes Fin.castSucc).symm ho

def schema_sentence {m} (collection : Bool) (w count z body : Fin m) (scopes : Fin 4 → Fin m) : Source.Sentence :=
  ((omega w).imp ((Source.Formula.mem count w).imp ((empty z).imp ((chain count scopes).imp
    ((ProjectSourceCodeSyntax.sourceCode w body (sourceScope (firstSite collection) scopes) z).imp
      (existsSchema collection w count z body scopes)))))).close

theorem schema_source_certificate {m} (collection : Bool) (w count z body : Fin m) (scopes : Fin 4 → Fin m) :
    Derives (Source.SetLanguage.ZF.at 0) (schema_sentence collection w count z body scopes) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ := Context.add (ProjectSourceCodeSyntax.sourceCode w body (sourceScope (firstSite collection) scopes) z)
    (Context.add (chain count scopes) (Context.add (empty z) (Context.add (Source.Formula.mem count w) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.source_ZF m) _) _) _) _) _
  exact schema_output_exists hZ collection w count z body scopes (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) (.hyp (Or.inr (Or.inr (Or.inl rfl))))
    (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem schema_kernel_certificate {m} (collection : Bool) (w count z body : Fin m) (scopes : Fin 4 → Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (schema_sentence collection w count z body scopes)) :=
  ZFReplay.replay (TheoryTransport.sentence (schema_source_certificate collection w count z body scopes))

end PPAC.Migration.SchemaAxiomCompilation
