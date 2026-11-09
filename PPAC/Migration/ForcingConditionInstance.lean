import PPAC.Migration.ForcingOpenInstantiate

/-! Pinned negative forcing branch: instantiate at the ACTUAL condition
parameter of the SAME pointwise opening. Internally obtain its real table
field, exact offset code, and original mode2 execution. This is still a term
component of the full formula cancellation, not normalized forcing MP. -/
namespace PPAC.Migration.ForcingConditionInstance
open Internal Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)
open StructuralListFieldSyntax (field field_rename)
open NaturalAdditionSyntax (sum sum_rename)
set_option maxRecDepth 16384
attribute [local irreducible] NaturalRecursionSyntax.matrix

private theorem at_parameter {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w mode z a f T A C R S K H j J P v : Fin m)
    (hw : Derives Γ (omega w)) (hm : Derives Γ (SyntaxNumeralSyntax.numeral 2 mode))
    (hz : Derives Γ (empty z)) (he : Derives Γ (ForcingOpenLayout.environment w z a f T R S))
    (hl : Derives Γ (SyntaxCodedMixedBinderSyntax.lifted w R S a f z T A C K H))
    (hj : Derives Γ (.mem j f)) (hJ : Derives Γ (sum w a j J)) (hP : Derives Γ (field w S j P)) :
    Derives Γ ((ForcingOpenInstantiate.zeroResult w mode z P T C K v).iff (SyntaxVariableSyntax.code false w J v)) := by
  have hLists := ForcingOpenLayout.environment_types w z a f T R S he
  have ht := SyntaxMixedImageCodeFields.field_type w f z T S j P (.conjR hLists) hj hP
  have hc := Derives.impE (.conjL (ForcingOpenLayout.parameters_field hZ w z a f T R S j J P he hj hJ)) hP
  have hrun := ForcingOpenInstantiate.zero_iff hZ w mode z P a f T A C R S K H v hw hm hz ht he hl
  have hcode := AbstractBinderRename.code_iff_equal hZ false w J P v hw hc
  exact SyntaxTypeLocalTransfer.iff_trans hrun (.conjI (.conjR hcode) (.conjL hcode))

private def conditionData {m} (w mode z T C S K j P v : Fin m) : Formula m :=
  (field w S j P).conj (ForcingOpenInstantiate.zeroResult w mode z P T C K v)
private theorem conditionData_rename {m l} (w mode z T C S K j P v : Fin m) (r : Fin m → Fin l) :
    (conditionData w mode z T C S K j P v).rename r = conditionData (r w) (r mode) (r z) (r T) (r C) (r S) (r K) (r j) (r P) (r v) := by
  simp only [conditionData, Formula.rename, field_rename, ForcingOpenInstantiate.zeroResult_rename]

/-- The actual selected condition field and its original new-head/mode2
execution, with the parameter code quantified internally. -/
def conditionResult {m} (w mode z T C S K j v : Fin m) : Formula m := .ex
  (conditionData w.castSucc mode.castSucc z.castSucc T.castSucc C.castSucc S.castSucc K.castSucc j.castSucc (Fin.last m) v.castSucc)

theorem conditionResult_rename {m l} (w mode z T C S K j v : Fin m) (r : Fin m → Fin l) :
    (conditionResult w mode z T C S K j v).rename r = conditionResult (r w) (r mode) (r z) (r T) (r C) (r S) (r K) (r j) (r v) := by
  simp only [conditionResult, Formula.rename, conditionData_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

/-- Identify the result with the EXACT original free-variable code at a+j.
The actual parameter field, intermediate head and Run are not premises. -/
theorem condition_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w mode z a f T A C R S K H j J v : Fin m)
    (hw : Derives Γ (omega w)) (hm : Derives Γ (SyntaxNumeralSyntax.numeral 2 mode))
    (hz : Derives Γ (empty z)) (he : Derives Γ (ForcingOpenLayout.environment w z a f T R S))
    (hl : Derives Γ (SyntaxCodedMixedBinderSyntax.lifted w R S a f z T A C K H))
    (hj : Derives Γ (.mem j f)) (hJ : Derives Γ (sum w a j J)) :
    Derives Γ ((conditionResult w mode z T C S K j v).iff (SyntaxVariableSyntax.code false w J v)) := by
  apply Derives.conjI
  · apply Derives.impI
    let E := conditionResult w mode z T C S K j v
    let B := conditionData w.castSucc mode.castSucc z.castSucc T.castSucc C.castSucc S.castSucc K.castSucc j.castSucc (Fin.last m) v.castSucc
    let Δ := Context.add B (Context.image Formula.raise (Context.add E Γ))
    apply Derives.exE (p := B) (.hyp (Or.inl rfl))
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have hi := at_parameter (ZFContext.under (ZFContext.add hZ E) B)
      w.castSucc mode.castSucc z.castSucc a.castSucc f.castSucc T.castSucc A.castSucc C.castSucc R.castSucc S.castSucc K.castSucc H.castSucc j.castSucc J.castSucc (Fin.last m) v.castSucc
      (of_eq (omega_rename w Fin.castSucc) (under (add hw E) B))
      (of_eq (SyntaxNumeralSyntax.numeral_rename 2 mode Fin.castSucc) (under (add hm E) B))
      (of_eq (empty_rename z Fin.castSucc) (under (add hz E) B))
      (of_eq (ForcingOpenLayout.environment_rename w z a f T R S Fin.castSucc) (under (add he E) B))
      (of_eq (SyntaxCodedMixedBinderSyntax.lifted_rename w R S a f z T A C K H Fin.castSucc) (under (add hl E) B))
      (under (add hj E) B) (of_eq (sum_rename w a j J Fin.castSucc) (under (add hJ E) B)) (.conjL hB)
    exact of_eq (SyntaxVariableSyntax.code_rename false w J v Fin.castSucc).symm (.impE (.conjL hi) (.conjR hB))
  · apply Derives.impI
    let E := SyntaxVariableSyntax.code false w J v
    let B := (Formula.mem (Fin.last m) w.castSucc).conj (field w.castSucc S.castSucc j.castSucc (Fin.last m))
    let Δ := Context.add B (Context.image Formula.raise (Context.add E Γ))
    have hLists := ForcingOpenLayout.environment_types w z a f T R S he
    have hjn := StructuralListTraceOrder.member_member hZ w j f hw (.conjL (.conjR hLists)) hj
    apply Derives.exE (p := B) (add (StructuralListFieldValues.exists_value hZ w S j hw hjn) E)
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have hi := at_parameter (ZFContext.under (ZFContext.add hZ E) B)
      w.castSucc mode.castSucc z.castSucc a.castSucc f.castSucc T.castSucc A.castSucc C.castSucc R.castSucc S.castSucc K.castSucc H.castSucc j.castSucc J.castSucc (Fin.last m) v.castSucc
      (of_eq (omega_rename w Fin.castSucc) (under (add hw E) B))
      (of_eq (SyntaxNumeralSyntax.numeral_rename 2 mode Fin.castSucc) (under (add hm E) B))
      (of_eq (empty_rename z Fin.castSucc) (under (add hz E) B))
      (of_eq (ForcingOpenLayout.environment_rename w z a f T R S Fin.castSucc) (under (add he E) B))
      (of_eq (SyntaxCodedMixedBinderSyntax.lifted_rename w R S a f z T A C K H Fin.castSucc) (under (add hl E) B))
      (under (add hj E) B) (of_eq (sum_rename w a j J Fin.castSucc) (under (add hJ E) B)) (.conjR hB)
    have hv : Derives Δ (SyntaxVariableSyntax.code false w.castSucc J.castSucc v.castSucc) :=
      of_eq (SyntaxVariableSyntax.code_rename false w J v Fin.castSucc) (under (Derives.hyp (Or.inl rfl) : Derives (Context.add E Γ) E) B)
    have ho : Derives Δ (conditionResult w.castSucc mode.castSucc z.castSucc T.castSucc C.castSucc S.castSucc K.castSucc j.castSucc v.castSucc) := by
      apply Derives.exI (Fin.last m)
      exact of_eq (by simp only [Formula.instantiate, conditionData_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]; rfl)
        (.conjI (.conjR hB) (.impE (.conjR hi) hv))
    exact of_eq (conditionResult_rename w mode z T C S K j v Fin.castSucc).symm ho

def totalResult {m} (w mode z a T C S K j v : Fin m) : Formula m := .ex
  ((sum w.castSucc a.castSucc j.castSucc (Fin.last m)).conj
    ((conditionResult w.castSucc mode.castSucc z.castSucc T.castSucc C.castSucc S.castSucc K.castSucc j.castSucc v.castSucc).iff
      (SyntaxVariableSyntax.code false w.castSucc (Fin.last m) v.castSucc)))

theorem totalResult_rename {m l} (w mode z a T C S K j v : Fin m) (r : Fin m → Fin l) :
    (totalResult w mode z a T C S K j v).rename r = totalResult (r w) (r mode) (r z) (r a) (r T) (r C) (r S) (r K) (r j) (r v) := by
  simp only [totalResult, Formula.iff, Formula.rename, sum_rename, conditionResult_rename, SyntaxVariableSyntax.code_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

/-- Generate the offset as well as actual condition parameter, new head and
execution internally, including nonstandard scopes and indices. -/
theorem total {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w mode z a f T A C R S K H j v : Fin m)
    (hw : Derives Γ (omega w)) (hm : Derives Γ (SyntaxNumeralSyntax.numeral 2 mode))
    (hz : Derives Γ (empty z)) (he : Derives Γ (ForcingOpenLayout.environment w z a f T R S))
    (hl : Derives Γ (SyntaxCodedMixedBinderSyntax.lifted w R S a f z T A C K H)) (hj : Derives Γ (.mem j f)) :
    Derives Γ (totalResult w mode z a T C S K j v) := by
  have hLists := ForcingOpenLayout.environment_types w z a f T R S he
  have hjn := StructuralListTraceOrder.member_member hZ w j f hw (.conjL (.conjR hLists)) hj
  let B := (Formula.mem (Fin.last m) w.castSucc).conj (sum w.castSucc a.castSucc j.castSucc (Fin.last m))
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) (ZFArithmetic.add_exists hZ w a j hw (.conjL (.conjL hLists)) hjn)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hi := condition_iff (ZFContext.under hZ B)
    w.castSucc mode.castSucc z.castSucc a.castSucc f.castSucc T.castSucc A.castSucc C.castSucc R.castSucc S.castSucc K.castSucc H.castSucc j.castSucc (Fin.last m) v.castSucc
    (of_eq (omega_rename w Fin.castSucc) (under hw B))
    (of_eq (SyntaxNumeralSyntax.numeral_rename 2 mode Fin.castSucc) (under hm B))
    (of_eq (empty_rename z Fin.castSucc) (under hz B))
    (of_eq (ForcingOpenLayout.environment_rename w z a f T R S Fin.castSucc) (under he B))
    (of_eq (SyntaxCodedMixedBinderSyntax.lifted_rename w R S a f z T A C K H Fin.castSucc) (under hl B)) (under hj B) (.conjR hB)
  have ho : Derives Δ (totalResult w.castSucc mode.castSucc z.castSucc a.castSucc T.castSucc C.castSucc S.castSucc K.castSucc j.castSucc v.castSucc) := by
    apply Derives.exI (Fin.last m)
    exact of_eq (by simp only [Formula.instantiate, Formula.iff, Formula.rename, sum_rename, conditionResult_rename,
      SyntaxVariableSyntax.code_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI (.conjR hB) hi)
  exact of_eq (totalResult_rename w mode z a T C S K j v Fin.castSucc).symm ho

def input {m} (w mode z a f T A C R S K H j : Fin m) : Formula m :=
  (omega w).conj ((SyntaxNumeralSyntax.numeral 2 mode).conj ((empty z).conj
    ((ForcingOpenLayout.environment w z a f T R S).conj
      ((SyntaxCodedMixedBinderSyntax.lifted w R S a f z T A C K H).conj (.mem j f)))))

def sentence {m} (w mode z a f T A C R S K H j v : Fin m) : Source.Sentence :=
  ((input w mode z a f T A C R S K H j).imp (totalResult w mode z a T C S K j v)).close

theorem kernel_certificate {m} (w mode z a f T A C R S K H j v : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (sentence w mode z a f T A C R S K H j v)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  let E := input w mode z a f T A C R S K H j
  let Γ := Context.add E (Source.SetLanguage.ZF.at m)
  have h : Derives Γ E := .hyp (Or.inl rfl)
  exact total (ZFContext.add (ZFContext.source_ZF m) E) w mode z a f T A C R S K H j v
    (.conjL h) (.conjL (.conjR h)) (.conjL (.conjR (.conjR h))) (.conjL (.conjR (.conjR (.conjR h))))
    (.conjL (.conjR (.conjR (.conjR (.conjR h))))) (.conjR (.conjR (.conjR (.conjR (.conjR h)))))

end PPAC.Migration.ForcingConditionInstance
