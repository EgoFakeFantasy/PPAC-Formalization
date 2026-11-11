import PPAC.Migration.ForcingPreorderCode
import PPAC.Migration.ProjectNativeRenaming
import PPAC.Migration.Internal.NativeFormulaQuotationCorrespondence
import PPAC.Migration.Internal.NativeSubstitutionEnvironment

/-! The literal source relation R is the common origin of the original
preorder atoms and guard template. Only intermediate SOURCE profiles are
fixed quotation metadata; no target forcing scope is made standard. Actual
runtime codes and generated term-image tables remain object witnesses. -/
namespace PPAC.Migration.ForcingRelationSource
open Internal Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)
set_option maxRecDepth 32768
set_option maxHeartbeats 1600000
attribute [local irreducible] NaturalRecursionSyntax.matrix
attribute [local implicit_reducible] YesMetaZFC.SetTheory.signature

section Templates
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open SetTheory.Definitional.Project (fo_bound_context fo_bound_variable)

/-- Fin readout of the original native variables, using the already proved
variable_index theorem. This does not define a syntax checker or recursion. -/
def mapping {n : Nat} {b f : PureSyntaxQuotation.Ctx} (ρ : Fin n → PureSyntaxQuotation.Tm b f) :
    NativeSubstitutionSyntax.Mapping (fo_bound_context n) b f :=
  fun {sort} entry => match sort with
    | .set => ρ ⟨entry.index, by simpa only [fo_bound_context, List.length_replicate] using entry.index_lt_length⟩

theorem mapping_at {n : Nat} {b f : PureSyntaxQuotation.Ctx} (ρ : Fin n → PureSyntaxQuotation.Tm b f) (i : Fin n) :
    mapping ρ (fo_bound_variable i) = ρ i := by
  change ρ ⟨(fo_bound_variable i).index, _⟩ = ρ i
  apply congrArg ρ
  apply Fin.ext
  exact ProjectNativeRenaming.variable_index (fun _ : Fin 1 => i) (fo_bound_variable (0 : Fin 1))

def emptyMap {b f : PureSyntaxQuotation.Ctx} : NativeSubstitutionSyntax.Mapping [] b f := fun v => nomatch v

def source {n} (R : Source.Formula (n+2)) : PureSyntaxQuotation.Fm [] (fo_bound_context (n+2)) :=
  Syntax.formula (fun i => .fvar (fo_bound_variable i)) R

theorem source_substitute {n} (R : Source.Formula (n+2)) {b f : PureSyntaxQuotation.Ctx} (ρ : Fin (n+2) → PureSyntaxQuotation.Tm b f) :
    (source R).substituteMapped emptyMap (mapping ρ) = Syntax.formula ρ R := by
  rw [source, Syntax.substitute]
  congr 1
  funext i
  exact mapping_at ρ i

def arguments {n} {b : PureSyntaxQuotation.Ctx} (x y : PureSyntaxQuotation.Tm b (fo_bound_context (n+2))) :
    Fin (n+2) → PureSyntaxQuotation.Tm b (fo_bound_context (n+2)) :=
  Fin.lastCases y (Fin.lastCases x (fun i => .fvar (fo_bound_variable i.castSucc.castSucc)))

def leftIndex : Fin 3 → Fin 3 := Fin.cases 2 (Fin.cases 1 (fun _ => 2))
def rightIndex : Fin 3 → Fin 3 := Fin.cases 1 (Fin.cases 0 (fun _ => 0))

def guardMap (n : Nat) : NativeSubstitutionSyntax.Mapping (fo_bound_context (n+2)) (fo_bound_context 1) (fo_bound_context (n+2)) :=
  mapping (arguments (.bvar .here) (.fvar (fo_bound_variable (Fin.last (n+1)))))

def atomMap (n : Nat) (i : Fin 3) : NativeSubstitutionSyntax.Mapping (fo_bound_context (n+2)) (fo_bound_context 3) (fo_bound_context (n+2)) :=
  mapping (arguments (.bvar (fo_bound_variable (leftIndex i))) (.bvar (fo_bound_variable (rightIndex i))))

def atom {n} (R : Source.Formula (n+2)) : Fin 3 → PureSyntaxQuotation.Fm (fo_bound_context 3) (fo_bound_context (n+2)) :=
  Fin.cases (ForcingPreorderCode.atoms R 3) (Fin.cases (ForcingPreorderCode.atoms R 4) (fun _ => ForcingPreorderCode.atoms R 5))

theorem guard_source {n} (R : Source.Formula (n+2)) :
    (source R).substituteMapped emptyMap (guardMap n) = ForcingGuardCode.template true R := by
  unfold guardMap
  rw [source_substitute]
  exact (ForcingGuardCode.relation_template R).symm

/-- The two relation arguments in the reflexivity body are the same bound slot. -/
def diagonalMap (n : Nat) : NativeSubstitutionSyntax.Mapping (fo_bound_context (n+2)) (fo_bound_context 1) (fo_bound_context (n+2)) :=
  mapping (arguments (.bvar .here) (.bvar .here))

theorem diagonal_source {n} (R : Source.Formula (n+2)) :
    (source R).substituteMapped emptyMap (diagonalMap n) = ForcingPreorderCode.reflexiveLeaf R true := by
  unfold diagonalMap
  rw [source_substitute]
  exact (ForcingPreorderCode.reflexive_relation R).symm

theorem atom_source {n} (R : Source.Formula (n+2)) (i : Fin 3) :
    (source R).substituteMapped emptyMap (atomMap n i) = atom R i := by
  unfold atomMap
  rw [source_substitute]
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun i => Fin.elim0 i))) i
  · exact (ForcingPreorderCode.atom_rq R).symm
  · exact (ForcingPreorderCode.atom_qp R).symm
  · exact (ForcingPreorderCode.atom_rp R).symm
end Templates

/-- Both actual substitutions start from the SAME source R quotation. -/
def data {n m} (R : Source.Formula (n+2)) (i : Fin 3) (w z t A f N G B : Fin m) (E : Fin 4 → Fin m) : Formula m :=
  (PureQuotationSyntax.formula (source R) w B).conj
    ((NativeSubstitutionSyntax.environment emptyMap (atomMap n i) w z f A f (E 0) (E 1)).conj
      ((SyntaxMixedFormulaJudgmentSyntax.substituted w (E 0) (E 1) z f A f B N).conj
        ((NativeSubstitutionSyntax.environment emptyMap (guardMap n) w z f t f (E 2) (E 3)).conj
          (SyntaxMixedFormulaJudgmentSyntax.substituted w (E 2) (E 3) z f t f B G))))

theorem data_rename {n m l} (R : Source.Formula (n+2)) (i : Fin 3) (w z t A f N G B : Fin m) (E : Fin 4 → Fin m) (ρ : Fin m → Fin l) :
    (data R i w z t A f N G B E).rename ρ = data R i (ρ w) (ρ z) (ρ t) (ρ A) (ρ f) (ρ N) (ρ G) (ρ B) (fun i => ρ (E i)) := by
  simp only [data, Formula.rename, PureQuotationSyntax.formula_rename, NativeSubstitutionSyntax.environment_rename, SyntaxMixedFormulaJudgmentSyntax.substituted_rename]

private theorem at_codes {n m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (R : Source.Formula (n+2)) (i : Fin 3)
    (w z t A f N G B : Fin m) (E : Fin 4 → Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (SyntaxNumeralSyntax.numeral 0 z))
    (ht : Derives Γ (SyntaxNumeralSyntax.numeral 1 t)) (hA : Derives Γ (SyntaxNumeralSyntax.numeral 3 A))
    (hf : Derives Γ (SyntaxNumeralSyntax.numeral (n+2) f))
    (hB : Derives Γ (PureQuotationSyntax.formula (source R) w B))
    (hN : Derives Γ (PureQuotationSyntax.formula (atom R i) w N))
    (hG : Derives Γ (PureQuotationSyntax.formula (ForcingGuardCode.template true R) w G))
    (he : Derives Γ (NativeSubstitutionSyntax.environment emptyMap (atomMap n i) w z f A f (E 0) (E 1)))
    (hg : Derives Γ (NativeSubstitutionSyntax.environment emptyMap (guardMap n) w z f t f (E 2) (E 3))) :
    Derives Γ (data R i w z t A f N G B E) := by
  have hRaw := of_eq (congrArg (fun input => PureQuotationSyntax.formula input w N) (atom_source R i).symm) hN
  have hGuard := of_eq (congrArg (fun input => PureQuotationSyntax.formula input w G) (guard_source R).symm) hG
  have hf' : Derives Γ (SyntaxNumeralSyntax.numeral (YesMetaZFC.SetTheory.Definitional.Project.fo_bound_context (n+2)).length f) := by
    simpa only [YesMetaZFC.SetTheory.Definitional.Project.fo_bound_context, List.length_replicate] using hf
  have qN := Derives.impE (Derives.conjR (NativeFormulaQuotationCorrespondence.formula_iff hZ (source R) emptyMap (atomMap n i)
    w (E 0) (E 1) z f A f B N hw hz hf' hA hf' he hB)) hRaw
  have qG := Derives.impE (Derives.conjR (NativeFormulaQuotationCorrespondence.formula_iff hZ (source R) emptyMap (guardMap n)
    w (E 2) (E 3) z f t f B G hw hz hf' ht hf' hg hB)) hGuard
  exact Derives.conjI hB (Derives.conjI he (Derives.conjI qN (Derives.conjI hg qG)))


def body {n m} (R : Source.Formula (n+2)) (i : Fin 3) (w z t A f N G : Fin m) : Formula (m+5) :=
  data R i (old 5 w) (old 5 z) (old 5 t) (old 5 A) (old 5 f) (old 5 N) (old 5 G) (slot 5 0) (fun j => slot 5 j.succ)

def produced {n m} (R : Source.Formula (n+2)) (i : Fin 3) (w z t A f N G : Fin m) : Formula m := existsMany 5 (body R i w z t A f N G)

theorem produced_rename {n m l} (R : Source.Formula (n+2)) (i : Fin 3) (w z t A f N G : Fin m) (ρ : Fin m → Fin l) :
    (produced R i w z t A f N G).rename ρ = produced R i (ρ w) (ρ z) (ρ t) (ρ A) (ρ f) (ρ N) (ρ G) := by
  simp only [produced, existsMany_rename, body, data_rename, lift_old, lift_slot]

private structure Inputs {n m} (Γ : Context m) (R : Source.Formula (n+2)) (i : Fin 3) (w z t A f N G : Fin m) : Prop where
  zf : ZFContext.Evidence Γ
  omega : Derives Γ (omega w)
  zero : Derives Γ (SyntaxNumeralSyntax.numeral 0 z)
  one : Derives Γ (SyntaxNumeralSyntax.numeral 1 t)
  three : Derives Γ (SyntaxNumeralSyntax.numeral 3 A)
  free : Derives Γ (SyntaxNumeralSyntax.numeral (n+2) f)
  raw : Derives Γ (PureQuotationSyntax.formula (atom R i) w N)
  guard : Derives Γ (PureQuotationSyntax.formula (ForcingGuardCode.template true R) w G)

private theorem Inputs.in_body {n m} {Γ : Context m} {R : Source.Formula (n+2)} {i : Fin 3} {w z t A f N G : Fin m}
    (h : Inputs Γ R i w z t A f N G) (k : Nat) (E : Formula (m+k)) :
    Inputs (Context.add E (raisedContext k Γ)) R i (old k w) (old k z) (old k t) (old k A) (old k f) (old k N) (old k G) := {
  zf := HornBinderRules.zf_body k h.zf E
  omega := of_eq (omega_rename w (old k)) (HornBinderRules.under_body k h.omega E)
  zero := of_eq (SyntaxNumeralSyntax.numeral_rename 0 z (old k)) (HornBinderRules.under_body k h.zero E)
  one := of_eq (SyntaxNumeralSyntax.numeral_rename 1 t (old k)) (HornBinderRules.under_body k h.one E)
  three := of_eq (SyntaxNumeralSyntax.numeral_rename 3 A (old k)) (HornBinderRules.under_body k h.three E)
  free := of_eq (SyntaxNumeralSyntax.numeral_rename (n+2) f (old k)) (HornBinderRules.under_body k h.free E)
  raw := of_eq (PureQuotationSyntax.formula_rename (atom R i) w N (old k)) (HornBinderRules.under_body k h.raw E)
  guard := of_eq (PureQuotationSyntax.formula_rename (ForcingGuardCode.template true R) w G (old k)) (HornBinderRules.under_body k h.guard E)
}

private theorem generate {n m} {Γ : Context m} {R : Source.Formula (n+2)} {i : Fin 3} {w z t A f N G : Fin m}
    (h : Inputs Γ R i w z t A f N G) : Derives Γ (produced R i w z t A f N G) := by
  have hex := OriginalTreeQuotationExistence.tree_exists h.zf (PureSyntaxQuotation.formulaTree (source R)) w h.omega
  let Q := (Formula.mem (Fin.last m) w.castSucc).conj (PureQuotationSyntax.formula (source R) w.castSucc (Fin.last m))
  let Δ := Context.add Q (raisedContext 1 Γ)
  apply HornBinderRules.eliminate_many 1 Q _ hex
  have hQ : Derives Δ Q := .hyp (Or.inl rfl)
  have h1 := h.in_body 1 Q
  have hf1 : Derives Δ (SyntaxNumeralSyntax.numeral (YesMetaZFC.SetTheory.Definitional.Project.fo_bound_context (n+2)).length (old 1 f)) := by
    simpa only [YesMetaZFC.SetTheory.Definitional.Project.fo_bound_context, List.length_replicate] using h1.free
  have he := NativeSubstitutionEnvironment.exists_environment h1.zf emptyMap (atomMap n i)
    (old 1 w) (old 1 z) (old 1 f) (old 1 A) (old 1 f) h1.omega h1.zero hf1 h1.three hf1
  let E := NativeSubstitutionSyntax.environment emptyMap (atomMap n i) (old 3 w) (old 3 z) (old 3 f) (old 3 A) (old 3 f) (slot 3 1) (slot 3 2)
  let Ξ := Context.add E (raisedContext 2 Δ)
  apply HornBinderRules.eliminate_many 2 E _ he
  have hE : Derives Ξ E := .hyp (Or.inl rfl)
  have h3 := h1.in_body 2 E
  have hB3 := of_eq (PureQuotationSyntax.formula_rename (source R) (old 1 w) (Fin.last m) (old 2)) (HornBinderRules.under_body 2 (Derives.conjR hQ) E)
  have hf3 := of_eq (SyntaxNumeralSyntax.numeral_rename (YesMetaZFC.SetTheory.Definitional.Project.fo_bound_context (n+2)).length (old 1 f) (old 2)) (HornBinderRules.under_body 2 hf1 E)
  have hg := NativeSubstitutionEnvironment.exists_environment h3.zf emptyMap (guardMap n)
    (old 3 w) (old 3 z) (old 3 f) (old 3 t) (old 3 f) h3.omega h3.zero hf3 h3.one hf3
  let F := NativeSubstitutionSyntax.environment emptyMap (guardMap n) (old 5 w) (old 5 z) (old 5 f) (old 5 t) (old 5 f) (slot 5 3) (slot 5 4)
  let Ω := Context.add F (raisedContext 2 Ξ)
  apply HornBinderRules.eliminate_many 2 F _ hg
  have hF : Derives Ω F := .hyp (Or.inl rfl)
  have h5 := h3.in_body 2 F
  have hB5 := of_eq (PureQuotationSyntax.formula_rename (source R) (old 3 w) (slot 3 0) (old 2)) (HornBinderRules.under_body 2 hB3 F)
  have hE5 := of_eq (NativeSubstitutionSyntax.environment_rename emptyMap (atomMap n i) (old 3 w) (old 3 z) (old 3 f) (old 3 A) (old 3 f) (slot 3 1) (slot 3 2) (old 2)) (HornBinderRules.under_body 2 hE F)
  let tables : Fin 4 → Fin (m+5) := Fin.cases (slot 5 1) (Fin.cases (slot 5 2) (Fin.cases (slot 5 3) (fun _ => slot 5 4)))
  have hData := at_codes h5.zf R i (old 5 w) (old 5 z) (old 5 t) (old 5 A) (old 5 f) (old 5 N) (old 5 G) (slot 5 0) tables
    h5.omega h5.zero h5.one h5.three h5.free hB5 h5.raw h5.guard hE5 hF
  have hout : Derives Ω (produced R i (old 5 w) (old 5 z) (old 5 t) (old 5 A) (old 5 f) (old 5 N) (old 5 G)) := by
    apply HornBinderRules.intro_many 5 _ (HornRowFields.five (slot 5 0) (slot 5 1) (slot 5 2) (slot 5 3) (slot 5 4))
    exact of_eq (by simp only [body, data_rename, assign_old, assign_slot] <;> rfl) hData
  exact of_eq (by simp only [produced_rename] <;> rfl) hout

/-- Construct the SAME source quotation and all FOUR actual native image
tables inside ZF; no source quotation/table/query answer is supplied. -/
theorem produce {n m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (R : Source.Formula (n+2)) (i : Fin 3)
    (w z t A f N G : Fin m) (hw : Derives Γ (omega w))
    (hz : Derives Γ (SyntaxNumeralSyntax.numeral 0 z)) (ht : Derives Γ (SyntaxNumeralSyntax.numeral 1 t))
    (hA : Derives Γ (SyntaxNumeralSyntax.numeral 3 A)) (hf : Derives Γ (SyntaxNumeralSyntax.numeral (n+2) f))
    (hN : Derives Γ (PureQuotationSyntax.formula (atom R i) w N))
    (hG : Derives Γ (PureQuotationSyntax.formula (ForcingGuardCode.template true R) w G)) : Derives Γ (produced R i w z t A f N G) :=
  generate ⟨hZ,hw,hz,ht,hA,hf,hN,hG⟩


/-- The three ORIGINAL relation leaves of the literal preorder raw row. -/
def rawSlot : Fin 3 → Fin 16 := Fin.cases 13 (Fin.cases 14 (fun _ => 15))

theorem raw_quotation {n m} {Γ : Context m} (R : Source.Formula (n+2)) (i : Fin 3)
    (w z A1 A2 A3 f : Fin m) (v : Fin 16 → Fin m)
    (hr : Derives Γ (ForcingPreorderCode.rawData R w z A1 A2 A3 f v)) :
    Derives Γ (PureQuotationSyntax.formula (atom R i) w (v (rawSlot i))) := by
  have h0 := Derives.conjL (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hr))))))))))))))
  have h1 := Derives.conjL (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hr)))))))))))))))
  have h2 := Derives.conjL (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hr))))))))))))))))
  refine Fin.cases h0 (Fin.cases h1 (Fin.cases h2 (fun i => Fin.elim0 i))) i

/-- Directly consumes actual rawData and the existing guard compiler matrix.
The shared R quotation and four image tables are internally generated. -/
theorem from_matrix {n m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (R : Source.Formula (n+2)) (i : Fin 3)
    (w z A1 A2 A3 f a head q : Fin m) (v : Fin 16 → Fin m) (g : Fin 4 → Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (SyntaxNumeralSyntax.numeral 0 z))
    (h3 : Derives Γ (SyntaxNumeralSyntax.numeral 3 A3)) (hf : Derives Γ (SyntaxNumeralSyntax.numeral (n+2) f))
    (hr : Derives Γ (ForcingPreorderCode.rawData R w z A1 A2 A3 f v))
    (hg : Derives Γ (ForcingGuardCode.matrix true R w a f head q g)) :
    Derives Γ (produced R i w z (g 0) A3 f (v (rawSlot i)) (g 1)) := by
  exact produce hZ R i w z (g 0) A3 f (v (rawSlot i)) (g 1) hw hz (Derives.conjL hg) h3 hf
    (raw_quotation R i w z A1 A2 A3 f v hr) (Derives.conjL (Derives.conjL (Derives.conjR hg)))

def guardData {n m} (R : Source.Formula (n+2)) (i : Fin 3) (w z A f a head q N : Fin m) (g : Fin 4 → Fin m) : Formula m :=
  (ForcingGuardCode.matrix true R w a f head q g).conj (produced R i w z (g 0) A f N (g 1))

theorem guardData_rename {n m l} (R : Source.Formula (n+2)) (i : Fin 3) (w z A f a head q N : Fin m) (g : Fin 4 → Fin m) (ρ : Fin m → Fin l) :
    (guardData R i w z A f a head q N g).rename ρ = guardData R i (ρ w) (ρ z) (ρ A) (ρ f) (ρ a) (ρ head) (ρ q) (ρ N) (fun i => ρ (g i)) := by
  simp only [guardData, Formula.rename, ForcingGuardCode.matrix_rename, produced_rename]

def guardBody {n m} (R : Source.Formula (n+2)) (i : Fin 3) (w z A f a head q N : Fin m) : Formula (m+4) :=
  guardData R i (old 4 w) (old 4 z) (old 4 A) (old 4 f) (old 4 a) (old 4 head) (old 4 q) (old 4 N) (slot 4)

def guardResult {n m} (R : Source.Formula (n+2)) (i : Fin 3) (w z A f a head q N : Fin m) : Formula m :=
  existsMany 4 (guardBody R i w z A f a head q N)

theorem guardResult_rename {n m l} (R : Source.Formula (n+2)) (i : Fin 3) (w z A f a head q N : Fin m) (ρ : Fin m → Fin l) :
    (guardResult R i w z A f a head q N).rename ρ = guardResult R i (ρ w) (ρ z) (ρ A) (ρ f) (ρ a) (ρ head) (ρ q) (ρ N) := by
  simp only [guardResult, existsMany_rename, guardBody, guardData_rename, lift_old, lift_slot]

/-- Consume the ACTUAL original guard compilation and raw preorder quotation.
All four compiler witnesses and five common-source witnesses are object
existentials. No matrix, source quotation, image table, query or equality
answer is supplied. The guard head, full compiler matrix and arbitrary
INTERNAL guard scope a are retained; no target scope is made standard. -/
theorem from_compiled {n m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (R : Source.Formula (n+2)) (i : Fin 3)
    (w z A1 A2 A3 f a head q : Fin m) (v : Fin 16 → Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (SyntaxNumeralSyntax.numeral 0 z))
    (h3 : Derives Γ (SyntaxNumeralSyntax.numeral 3 A3)) (hf : Derives Γ (SyntaxNumeralSyntax.numeral (n+2) f))
    (hr : Derives Γ (ForcingPreorderCode.rawData R w z A1 A2 A3 f v))
    (hc : Derives Γ (ForcingGuardCode.compiled true R w a f head q)) :
    Derives Γ (guardResult R i w z A3 f a head q (v (rawSlot i))) := by
  let E := ForcingGuardCode.body true R w a f head q
  let Δ := Context.add E (raisedContext 4 Γ)
  apply HornBinderRules.eliminate_many 4 E _ hc
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have hZ4 := HornBinderRules.zf_body 4 hZ E
  have hw4 := of_eq (omega_rename w (old 4)) (HornBinderRules.under_body 4 hw E)
  have hz4 := of_eq (SyntaxNumeralSyntax.numeral_rename 0 z (old 4)) (HornBinderRules.under_body 4 hz E)
  have h34 := of_eq (SyntaxNumeralSyntax.numeral_rename 3 A3 (old 4)) (HornBinderRules.under_body 4 h3 E)
  have hf4 := of_eq (SyntaxNumeralSyntax.numeral_rename (n+2) f (old 4)) (HornBinderRules.under_body 4 hf E)
  have hr4 := of_eq (ForcingPreorderCode.rawData_rename R w z A1 A2 A3 f v (old 4)) (HornBinderRules.under_body 4 hr E)
  have hCommon := from_matrix hZ4 R i (old 4 w) (old 4 z) (old 4 A1) (old 4 A2) (old 4 A3) (old 4 f) (old 4 a) (old 4 head) (old 4 q)
    (fun j => old 4 (v j)) (slot 4) hw4 hz4 h34 hf4 hr4 hE
  have hData : Derives Δ (guardData R i (old 4 w) (old 4 z) (old 4 A3) (old 4 f) (old 4 a) (old 4 head) (old 4 q) (old 4 (v (rawSlot i))) (slot 4)) :=
    Derives.conjI hE hCommon
  have hout : Derives Δ (guardResult R i (old 4 w) (old 4 z) (old 4 A3) (old 4 f) (old 4 a) (old 4 head) (old 4 q) (old 4 (v (rawSlot i)))) := by
    apply HornBinderRules.intro_many 4 _ (slot 4)
    exact of_eq (by simp only [guardBody, guardData_rename, assign_old, assign_slot] <;> rfl) hData
  exact of_eq (guardResult_rename R i w z A3 f a head q (v (rawSlot i)) (old 4)).symm hout

def input {n m} (R : Source.Formula (n+2)) (w z A1 A2 A3 f a head q : Fin m) (v : Fin 16 → Fin m) : Formula m :=
  (omega w).conj ((SyntaxNumeralSyntax.numeral 0 z).conj ((SyntaxNumeralSyntax.numeral 3 A3).conj
    ((SyntaxNumeralSyntax.numeral (n+2) f).conj ((ForcingPreorderCode.rawData R w z A1 A2 A3 f v).conj
      (ForcingGuardCode.compiled true R w a f head q)))))

def sentence {n m} (R : Source.Formula (n+2)) (i : Fin 3) (w z A1 A2 A3 f a head q : Fin m) (v : Fin 16 → Fin m) : Source.Sentence :=
  ((input R w z A1 A2 A3 f a head q v).imp (guardResult R i w z A3 f a head q (v (rawSlot i)))).close

theorem kernel_certificate {n m} (R : Source.Formula (n+2)) (i : Fin 3) (w z A1 A2 A3 f a head q : Fin m) (v : Fin 16 → Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (sentence R i w z A1 A2 A3 f a head q v)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  let E := input R w z A1 A2 A3 f a head q v
  let Γ := Context.add E (Source.SetLanguage.ZF.at m)
  have h : Derives Γ E := .hyp (Or.inl rfl)
  exact from_compiled (ZFContext.add (ZFContext.source_ZF m) E) R i w z A1 A2 A3 f a head q v
    (Derives.conjL h)    (Derives.conjL (Derives.conjR h))    (Derives.conjL (Derives.conjR (Derives.conjR h)))    (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR h))))    (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR h)))))    (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR h)))))

end PPAC.Migration.ForcingRelationSource
