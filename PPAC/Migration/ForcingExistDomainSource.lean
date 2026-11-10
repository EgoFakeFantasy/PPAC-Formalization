import PPAC.Migration.ForcingExistGuardsCode
import PPAC.Migration.ForcingRelationSource

/-! Pinned Force.ex domain guard: domainOrder H ignores its second relation
argument. Reuse the ORIGINAL native substitution environment and quotation
correspondence to produce a query from the SAME bare H code. All source-code
and table witnesses are generated inside object EX. This is the source leg
of the actual domain/opening comparison, not that whole comparison or Con. -/
namespace PPAC.Migration.ForcingExistDomainSource
open Internal Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)
set_option maxRecDepth 32768
attribute [local irreducible] NaturalRecursionSyntax.matrix
attribute [local implicit_reducible] YesMetaZFC.SetTheory.signature

section Templates
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open SetTheory.Definitional.Project (fo_bound_context fo_bound_variable)

def source {k} (H : Source.Formula (k+1)) : PureSyntaxQuotation.Fm [] (fo_bound_context (k+1)) :=
  Syntax.formula (fun i => .fvar (fo_bound_variable i)) H

def arguments (k : Nat) : Fin (k+1) → PureSyntaxQuotation.Tm (fo_bound_context 1) (fo_bound_context (k+2)) :=
  Fin.lastCases (.bvar .here) (fun i => .fvar (fo_bound_variable i.castSucc.castSucc))
def mapping (k : Nat) : NativeSubstitutionSyntax.Mapping (fo_bound_context (k+1)) (fo_bound_context 1) (fo_bound_context (k+2)) :=
  ForcingRelationSource.mapping (arguments k)

/-- Finite AST identity reads the ORIGINAL template; the unused p parameter
is not reintroduced into the actual H argument table. -/
theorem source_template {k} (H : Source.Formula (k+1)) :
    (source H).substituteMapped ForcingRelationSource.emptyMap (mapping k) =
      ForcingGuardCode.template true (ForcingExistGuardsCode.domainOrder H) := by
  unfold source mapping
  rw [Syntax.substitute, ForcingGuardCode.relation_template]
  unfold ForcingExistGuardsCode.domainOrder
  rw [Syntax.rename]
  congr 1
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;>
    simp only [Term.substituteMapped, ForcingRelationSource.mapping_at, arguments, Fin.lastCases_last, Fin.lastCases_castSucc]
end Templates

open ForcingRelationSource (emptyMap)

def data {k m} (H : Source.Formula (k+1)) (w z t f h G B E F : Fin m) : Formula m :=
  (PureQuotationSyntax.formula (source H) w B).conj
    ((NativeSubstitutionSyntax.environment emptyMap (mapping k) w z h t f E F).conj
      (SyntaxMixedFormulaJudgmentSyntax.substituted w E F z h t f B G))

theorem data_rename {k m l} (H : Source.Formula (k+1)) (w z t f h G B E F : Fin m) (r : Fin m → Fin l) :
    (data H w z t f h G B E F).rename r = data H (r w) (r z) (r t) (r f) (r h) (r G) (r B) (r E) (r F) := by
  simp only [data, Formula.rename, PureQuotationSyntax.formula_rename, NativeSubstitutionSyntax.environment_rename, SyntaxMixedFormulaJudgmentSyntax.substituted_rename]

def body {k m} (H : Source.Formula (k+1)) (w z t f h G : Fin m) : Formula (m+3) :=
  data H (old 3 w) (old 3 z) (old 3 t) (old 3 f) (old 3 h) (old 3 G) (slot 3 0) (slot 3 1) (slot 3 2)
def produced {k m} (H : Source.Formula (k+1)) (w z t f h G : Fin m) : Formula m := existsMany 3 (body H w z t f h G)
theorem produced_rename {k m l} (H : Source.Formula (k+1)) (w z t f h G : Fin m) (r : Fin m → Fin l) :
    (produced H w z t f h G).rename r = produced H (r w) (r z) (r t) (r f) (r h) (r G) := by
  simp only [produced, existsMany_rename, body, data_rename, lift_old, lift_slot]

private theorem at_codes {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (H : Source.Formula (k+1))
    (w z t f h G B E F : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (SyntaxNumeralSyntax.numeral 0 z))
    (ht : Derives Γ (SyntaxNumeralSyntax.numeral 1 t)) (hf : Derives Γ (SyntaxNumeralSyntax.numeral (k+2) f))
    (hh : Derives Γ (SyntaxNumeralSyntax.numeral (k+1) h))
    (hG : Derives Γ (PureQuotationSyntax.formula (ForcingGuardCode.template true (ForcingExistGuardsCode.domainOrder H)) w G))
    (hB : Derives Γ (PureQuotationSyntax.formula (source H) w B))
    (he : Derives Γ (NativeSubstitutionSyntax.environment emptyMap (mapping k) w z h t f E F)) :
    Derives Γ (data H w z t f h G B E F) := by
  have hGuard := of_eq (congrArg (fun input => PureQuotationSyntax.formula input w G) (source_template H).symm) hG
  have hh' : Derives Γ (SyntaxNumeralSyntax.numeral (YesMetaZFC.SetTheory.Definitional.Project.fo_bound_context (k+1)).length h) := by
    simpa only [YesMetaZFC.SetTheory.Definitional.Project.fo_bound_context, List.length_replicate] using hh
  have hf' : Derives Γ (SyntaxNumeralSyntax.numeral (YesMetaZFC.SetTheory.Definitional.Project.fo_bound_context (k+2)).length f) := by
    simpa only [YesMetaZFC.SetTheory.Definitional.Project.fo_bound_context, List.length_replicate] using hf
  have hq := Derives.impE (.conjR (NativeFormulaQuotationCorrespondence.formula_iff hZ (source H) emptyMap (mapping k)
    w E F z h t f B G hw hz hh' ht hf' he hB)) hGuard
  exact .conjI hB (.conjI he hq)

/-- Generate H quotation and its TWO original native image tables internally,
then produce the actual query to the SAME original domain template output. -/
theorem produce {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (H : Source.Formula (k+1))
    (w z t f h G : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (SyntaxNumeralSyntax.numeral 0 z))
    (ht : Derives Γ (SyntaxNumeralSyntax.numeral 1 t)) (hf : Derives Γ (SyntaxNumeralSyntax.numeral (k+2) f))
    (hh : Derives Γ (SyntaxNumeralSyntax.numeral (k+1) h))
    (hG : Derives Γ (PureQuotationSyntax.formula (ForcingGuardCode.template true (ForcingExistGuardsCode.domainOrder H)) w G)) :
    Derives Γ (produced H w z t f h G) := by
  let B := (Formula.mem (Fin.last m) w.castSucc).conj (PureQuotationSyntax.formula (source H) w.castSucc (Fin.last m))
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) (OriginalTreeQuotationExistence.tree_exists hZ (PureSyntaxQuotation.formulaTree (source H)) w hw)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hZ1 := ZFContext.under hZ B
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw B)
  have hz1 := of_eq (SyntaxNumeralSyntax.numeral_rename 0 z Fin.castSucc) (under hz B)
  have ht1 := of_eq (SyntaxNumeralSyntax.numeral_rename 1 t Fin.castSucc) (under ht B)
  have hf1 := of_eq (SyntaxNumeralSyntax.numeral_rename (k+2) f Fin.castSucc) (under hf B)
  have hh1 := of_eq (SyntaxNumeralSyntax.numeral_rename (k+1) h Fin.castSucc) (under hh B)
  have hG1 := of_eq (PureQuotationSyntax.formula_rename (ForcingGuardCode.template true (ForcingExistGuardsCode.domainOrder H)) w G Fin.castSucc) (under hG B)
  have he := NativeSubstitutionEnvironment.exists_environment hZ1 emptyMap (mapping k) w.castSucc z.castSucc h.castSucc t.castSucc f.castSucc hw1 hz1
    (by simpa only [YesMetaZFC.SetTheory.Definitional.Project.fo_bound_context, List.length_replicate] using hh1) ht1
    (by simpa only [YesMetaZFC.SetTheory.Definitional.Project.fo_bound_context, List.length_replicate] using hf1)
  let C := NativeSubstitutionSyntax.environment emptyMap (mapping k) (old 2 w.castSucc) (old 2 z.castSucc) (old 2 h.castSucc) (old 2 t.castSucc) (old 2 f.castSucc) (slot 2 0) (slot 2 1)
  let Ξ := Context.add C (raisedContext 2 Δ)
  apply HornBinderRules.eliminate_many 2 C _ he
  have hC : Derives Ξ C := .hyp (Or.inl rfl)
  have hZ3 := HornBinderRules.zf_body 2 hZ1 C
  have hw3 := of_eq (omega_rename w.castSucc (old 2)) (HornBinderRules.under_body 2 hw1 C)
  have hz3 := of_eq (SyntaxNumeralSyntax.numeral_rename 0 z.castSucc (old 2)) (HornBinderRules.under_body 2 hz1 C)
  have ht3 := of_eq (SyntaxNumeralSyntax.numeral_rename 1 t.castSucc (old 2)) (HornBinderRules.under_body 2 ht1 C)
  have hf3 := of_eq (SyntaxNumeralSyntax.numeral_rename (k+2) f.castSucc (old 2)) (HornBinderRules.under_body 2 hf1 C)
  have hh3 := of_eq (SyntaxNumeralSyntax.numeral_rename (k+1) h.castSucc (old 2)) (HornBinderRules.under_body 2 hh1 C)
  have hG3 := of_eq (PureQuotationSyntax.formula_rename (ForcingGuardCode.template true (ForcingExistGuardsCode.domainOrder H)) w.castSucc G.castSucc (old 2)) (HornBinderRules.under_body 2 hG1 C)
  have hB3 : Derives Ξ (PureQuotationSyntax.formula (source H) (old 3 w) (old 2 (Fin.last m))) :=
    of_eq (PureQuotationSyntax.formula_rename (source H) w.castSucc (Fin.last m) (old 2)) (HornBinderRules.under_body 2 (.conjR hB) C)
  have hd := at_codes hZ3 H (old 3 w) (old 3 z) (old 3 t) (old 3 f) (old 3 h) (old 3 G) (old 2 (Fin.last m)) (slot 2 0) (slot 2 1)
    hw3 hz3 ht3 hf3 hh3 hG3 hB3 hC
  have hout : Derives Ξ (produced H (old 3 w) (old 3 z) (old 3 t) (old 3 f) (old 3 h) (old 3 G)) := by
    apply HornBinderRules.intro_many 3 _ (SetLanguage.args3 (old 2 (Fin.last m)) (slot 2 0) (slot 2 1))
    exact of_eq (by simp only [body, data_rename, assign_old, assign_slot]; rfl) hd
  exact of_eq (by simp only [Formula.raise, produced_rename]; rfl) hout


/-- Retain the SAME complete original compiler record; attach its source-H
query. The source quotation and both native tables remain OBJECT witnesses. -/
def compilerData {k m} (H : Source.Formula (k+1)) (w z a f h x Q : Fin m) (v : Fin 4 → Fin m) : Formula m :=
  (ForcingGuardCode.matrix true (ForcingExistGuardsCode.domainOrder H) w a f x Q v).conj
    (produced H w z (v 0) f h (v 1))
theorem compilerData_rename {k m l} (H : Source.Formula (k+1)) (w z a f h x Q : Fin m) (v : Fin 4 → Fin m) (r : Fin m → Fin l) :
    (compilerData H w z a f h x Q v).rename r = compilerData H (r w) (r z) (r a) (r f) (r h) (r x) (r Q) (fun i => r (v i)) := by
  simp only [compilerData, Formula.rename, ForcingGuardCode.matrix_rename, produced_rename]
def compilerBody {k m} (H : Source.Formula (k+1)) (w z a f h x Q : Fin m) : Formula (m+4) :=
  compilerData H (old 4 w) (old 4 z) (old 4 a) (old 4 f) (old 4 h) (old 4 x) (old 4 Q) (slot 4)
def compilerResult {k m} (H : Source.Formula (k+1)) (w z a f h x Q : Fin m) : Formula m :=
  existsMany 4 (compilerBody H w z a f h x Q)
theorem compilerResult_rename {k m l} (H : Source.Formula (k+1)) (w z a f h x Q : Fin m) (r : Fin m → Fin l) :
    (compilerResult H w z a f h x Q).rename r = compilerResult H (r w) (r z) (r a) (r f) (r h) (r x) (r Q) := by
  simp only [compilerResult, existsMany_rename, compilerBody, compilerData_rename, lift_old, lift_slot]

/-- Consume the COMPLETE original domain compiler. Its original four
witnesses are internally read and retained; three new source-H/query witnesses
are internally produced. No replacement quotation or query answer is assumed. -/
theorem from_compiled {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (H : Source.Formula (k+1))
    (w z a f h x Q : Fin m) (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hf : Derives Γ (SyntaxNumeralSyntax.numeral (k+2) f))
    (hh : Derives Γ (SyntaxNumeralSyntax.numeral (k+1) h))
    (hc : Derives Γ (ForcingGuardCode.compiled true (ForcingExistGuardsCode.domainOrder H) w a f x Q)) :
    Derives Γ (compilerResult H w z a f h x Q) := by
  let B := ForcingGuardCode.body true (ForcingExistGuardsCode.domainOrder H) w a f x Q
  let Δ := Context.add B (raisedContext 4 Γ)
  apply HornBinderRules.eliminate_many 4 B _ hc
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hZ4 := HornBinderRules.zf_body 4 hZ B
  have hw4 := of_eq (omega_rename w (old 4)) (HornBinderRules.under_body 4 hw B)
  have hz4 := of_eq (empty_rename z (old 4)) (HornBinderRules.under_body 4 hz B)
  have hf4 := of_eq (SyntaxNumeralSyntax.numeral_rename (k+2) f (old 4)) (HornBinderRules.under_body 4 hf B)
  have hh4 := of_eq (SyntaxNumeralSyntax.numeral_rename (k+1) h (old 4)) (HornBinderRules.under_body 4 hh B)
  have hp := produce hZ4 H (old 4 w) (old 4 z) (slot 4 0) (old 4 f) (old 4 h) (slot 4 1)
    hw4 hz4 (.conjL hB) hf4 hh4 (.conjL (.conjL (.conjR hB)))
  have hout : Derives Δ (compilerResult H (old 4 w) (old 4 z) (old 4 a) (old 4 f) (old 4 h) (old 4 x) (old 4 Q)) := by
    apply HornBinderRules.intro_many 4 _ (slot 4)
    have hdata : Derives Δ (compilerData H (old 4 w) (old 4 z) (old 4 a) (old 4 f) (old 4 h) (old 4 x) (old 4 Q) (slot 4)) := .conjI hB hp
    exact of_eq (by simp only [compilerBody, compilerData_rename, assign_old, assign_slot]) hdata
  exact of_eq (compilerResult_rename H w z a f h x Q (old 4)).symm hout

def input {k m} (H : Source.Formula (k+1)) (w z a f h x Q : Fin m) : Formula m :=
  (omega w).conj ((empty z).conj ((SyntaxNumeralSyntax.numeral (k+2) f).conj
    ((SyntaxNumeralSyntax.numeral (k+1) h).conj
      (ForcingGuardCode.compiled true (ForcingExistGuardsCode.domainOrder H) w a f x Q))))
def sentence {k m} (H : Source.Formula (k+1)) (w z a f h x Q : Fin m) : Source.Sentence :=
  ((input H w z a f h x Q).imp (compilerResult H w z a f h x Q)).close
theorem kernel_certificate {k m} (H : Source.Formula (k+1)) (w z a f h x Q : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (sentence H w z a f h x Q)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  let G := input H w z a f h x Q
  let Γ := Context.add G (Source.SetLanguage.ZF.at m)
  have hG : Derives Γ G := .hyp (Or.inl rfl)
  exact from_compiled (ZFContext.add (ZFContext.source_ZF m) G) H w z a f h x Q
    (.conjL hG) (.conjL (.conjR hG)) (.conjL (.conjR (.conjR hG)))
    (.conjL (.conjR (.conjR (.conjR hG)))) (.conjR (.conjR (.conjR (.conjR hG))))

end PPAC.Migration.ForcingExistDomainSource
