import PPAC.Migration.ForcingOpenLift
import PPAC.Migration.Internal.InstantiateVariableRun
import PPAC.Migration.Internal.InstantiateVariableSpecialization

/-! Actual lifted opening followed by the ORIGINAL mode2 term execution.
Old images retain their exact codes; the new bound-zero image becomes the
specified parameter. All intermediate codes are object witnesses. This is
not the outstanding full formula rebind/open/InstantiateTop cancellation. -/
namespace PPAC.Migration.ForcingOpenInstantiate
open Internal Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)
open StructuralListFieldSyntax (field field_rename)
set_option maxRecDepth 16384
attribute [local irreducible] NaturalRecursionSyntax.matrix

private theorem closed_run_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w mode z P T q v : Fin m) (hw : Derives Γ (omega w))
    (hm : Derives Γ (SyntaxNumeralSyntax.numeral 2 mode))
    (hd : Derives Γ (OriginalTermTraceSyntax.metadata w z P))
    (hq : Derives Γ (InstantiateOperationFrameSyntax.closedParameter w T q)) :
    Derives Γ ((OriginalTransformRowSyntax.run 1 w mode z P q v).iff (.equal v q)) := by
  let B := SyntaxTermSyntax.branchWitness false w T q
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply SyntaxTermSyntax.eliminate_branch false w T q _
    (InstantiateOperationFrameSyntax.closedParameter_free w T q hq)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hr := InstantiateVariableRun.run_iff (ZFContext.under hZ B) false
    w.castSucc mode.castSucc z.castSucc P.castSucc q.castSucc (Fin.last m) v.castSucc
    (of_eq (omega_rename w Fin.castSucc) (under hw B))
    (of_eq (SyntaxNumeralSyntax.numeral_rename 2 mode Fin.castSucc) (under hm B))
    (of_eq (OriginalTermTraceSyntax.metadata_rename w z P Fin.castSucc) (under hd B)) (.conjR hB)
  exact of_eq (by simp only [Formula.raise, Formula.iff, Formula.rename, OriginalTransformRowSyntax.run_rename, InstantiateVariableValueSyntax.valueSpec, Bool.false_eq_true, ↓reduceIte]) hr

private theorem run_input {m} {Γ : Context m} (w mode z P u q v : Fin m)
    (he : Derives Γ (.equal u q)) (hr : Derives Γ (OriginalTransformRowSyntax.run 1 w mode z P u v)) :
    Derives Γ (OriginalTransformRowSyntax.run 1 w mode z P q v) := by
  let F := OriginalTransformRowSyntax.run 1 w.castSucc mode.castSucc z.castSucc P.castSucc (Fin.last m) v.castSucc
  have hh : Derives Γ (F.instantiate u) := of_eq (by simp only [F, Formula.instantiate, OriginalTransformRowSyntax.run_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hr
  exact of_eq (by simp only [F, Formula.instantiate, OriginalTransformRowSyntax.run_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (Derives.eqSubst F he hh)

private def oldData {m} (bound : Bool) (w mode z P A f K H i I u v : Fin m) : Formula m :=
  ((Formula.mem (if bound then I else i) (SyntaxTermSyntax.limit bound A f)).conj
    (field w (SyntaxIndexMapSyntax.selectMap bound K H) (if bound then I else i) u)).conj
      (OriginalTransformRowSyntax.run 1 w mode z P u v)
private theorem oldData_rename {m l} (bound : Bool) (w mode z P A f K H i I u v : Fin m) (r : Fin m → Fin l) :
    (oldData bound w mode z P A f K H i I u v).rename r = oldData bound (r w) (r mode) (r z) (r P) (r A) (r f) (r K) (r H) (r i) (r I) (r u) (r v) := by
  cases bound <;> simp only [oldData, Formula.rename, SyntaxTermSyntax.limit, SyntaxIndexMapSyntax.selectMap,
    Bool.false_eq_true, ↓reduceIte, field_rename, OriginalTransformRowSyntax.run_rename]

/-- The SAME actual lifted old field, followed by original kind1 mode2 Run.
The intermediate image code is quantified internally. -/
def oldResult {m} (bound : Bool) (w mode z P A f K H i I v : Fin m) : Formula m := .ex
  (oldData bound w.castSucc mode.castSucc z.castSucc P.castSucc A.castSucc f.castSucc K.castSucc H.castSucc i.castSucc I.castSucc (Fin.last m) v.castSucc)

theorem oldResult_rename {m l} (bound : Bool) (w mode z P A f K H i I v : Fin m) (r : Fin m → Fin l) :
    (oldResult bound w mode z P A f K H i I v).rename r = oldResult bound (r w) (r mode) (r z) (r P) (r A) (r f) (r K) (r H) (r i) (r I) (r v) := by
  simp only [oldResult, Formula.rename, oldData_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

/-- Actual old images survive BOTH original operations with exact codes.
No intermediate image, execution, output answer or auxiliary table is assumed. -/
theorem old_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (bound : Bool)
    (w mode z P a f T A C R S K H i I q v : Fin m)
    (hw : Derives Γ (omega w)) (hm : Derives Γ (SyntaxNumeralSyntax.numeral 2 mode))
    (hz : Derives Γ (empty z)) (hP : Derives Γ (SyntaxTermSyntax.term w z T P))
    (he : Derives Γ (ForcingOpenLayout.environment w z a f T R S))
    (hl : Derives Γ (SyntaxCodedMixedBinderSyntax.lifted w R S a f z T A C K H))
    (hi : Derives Γ (.mem i (SyntaxTermSyntax.limit bound a f)))
    (hf : Derives Γ (field w (SyntaxIndexMapSyntax.selectMap bound R S) i q))
    (hs : Derives Γ (ForcingOpenLift.step bound i I)) :
    Derives Γ ((oldResult bound w mode z P A f K H i I v).iff (.equal v q)) := by
  have hLists := ForcingOpenLayout.environment_types w z a f T R S he
  have hList : Derives Γ (SyntaxMixedImageCodeSyntax.termList w (SyntaxTermSyntax.limit bound a f) z T (SyntaxIndexMapSyntax.selectMap bound R S)) := by
    cases bound
    · exact .conjR hLists
    · exact .conjL hLists
  have ht := SyntaxMixedImageCodeFields.field_type w (SyntaxTermSyntax.limit bound a f) z T (SyntaxIndexMapSyntax.selectMap bound R S) i q hList hi hf
  have hd : Derives Γ (OriginalTermTraceSyntax.metadata w z P) := .conjI
    (OmegaStructureAlgebra.zero_member w z (ZFContext.arithmetic hZ).base.extensionality hw hz)
    (SyntaxTerms.range hZ w z T P hw hP)
  have hr := closed_run_iff hZ w mode z P T q v hw hm hd
    (InstantiateOperationFrameSyntax.intro_closedParameter w T q z hz ht)
  apply Derives.conjI
  · apply Derives.impI
    let E := oldResult bound w mode z P A f K H i I v
    let B := oldData bound w.castSucc mode.castSucc z.castSucc P.castSucc A.castSucc f.castSucc K.castSucc H.castSucc i.castSucc I.castSucc (Fin.last m) v.castSucc
    let Δ := Context.add B (Context.image Formula.raise (Context.add E Γ))
    apply Derives.exE (p := B) (.hyp (Or.inl rfl))
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have hfields := ForcingOpenLift.old_fields (ZFContext.under (ZFContext.add hZ E) B) bound
      w.castSucc z.castSucc a.castSucc f.castSucc T.castSucc A.castSucc C.castSucc R.castSucc S.castSucc K.castSucc H.castSucc
      i.castSucc I.castSucc q.castSucc (Fin.last m)
      (of_eq (omega_rename w Fin.castSucc) (under (add hw E) B))
      (of_eq (empty_rename z Fin.castSucc) (under (add hz E) B))
      (of_eq (ForcingOpenLayout.environment_rename w z a f T R S Fin.castSucc) (under (add he E) B))
      (of_eq (SyntaxCodedMixedBinderSyntax.lifted_rename w R S a f z T A C K H Fin.castSucc) (under (add hl E) B))
      (of_eq (by simp only [Formula.raise, Formula.rename, SyntaxTermSyntax.limit_map]) (under (add hi E) B))
      (of_eq (by simp only [Formula.raise, field_rename, SyntaxIndexMapSyntax.selectMap_map]) (under (add hf E) B))
      (of_eq (ForcingOpenLift.step_rename bound i I Fin.castSucc) (under (add hs E) B))
    have hEq := Derives.impE (.conjL hfields) (.conjL hB)
    have hRun := run_input w.castSucc mode.castSucc z.castSucc P.castSucc (Fin.last m) q.castSucc v.castSucc hEq (.conjR hB)
    have hr1 : Derives Δ ((OriginalTransformRowSyntax.run 1 w.castSucc mode.castSucc z.castSucc P.castSucc q.castSucc v.castSucc).iff (.equal v.castSucc q.castSucc)) :=
      of_eq (by simp only [Formula.raise, Formula.iff, Formula.rename, OriginalTransformRowSyntax.run_rename]) (under (add hr E) B)
    exact .impE (.conjL hr1) hRun
  · apply Derives.impI
    let E := Formula.equal v q
    have hE : Derives (Context.add E Γ) E := .hyp (Or.inl rfl)
    have hfields := ForcingOpenLift.old_fields hZ bound w z a f T A C R S K H i I q q hw hz he hl hi hf hs
    have hfq := Derives.impE (.conjR hfields) (Derives.eqRefl q)
    have hrun := Derives.impE (.conjR (add hr E)) hE
    apply Derives.exI q
    exact of_eq (by simp only [oldData_rename, Formula.instantiate, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]; rfl)
      (Derives.conjI (add hfq E) hrun)

private def zeroData {m} (w mode z P T C K n v : Fin m) : Formula m :=
  (SyntaxMixedImageHead.head w C T z n).conj ((field w K z n).conj (OriginalTransformRowSyntax.run 1 w mode z P n v))
private theorem zeroData_rename {m l} (w mode z P T C K n v : Fin m) (r : Fin m → Fin l) :
    (zeroData w mode z P T C K n v).rename r = zeroData (r w) (r mode) (r z) (r P) (r T) (r C) (r K) (r n) (r v) := by
  simp only [zeroData, Formula.rename, SyntaxMixedImageHead.head_rename, field_rename, OriginalTransformRowSyntax.run_rename]

def zeroResult {m} (w mode z P T C K v : Fin m) : Formula m := .ex
  (zeroData w.castSucc mode.castSucc z.castSucc P.castSucc T.castSucc C.castSucc K.castSucc (Fin.last m) v.castSucc)

theorem zeroResult_rename {m l} (w mode z P T C K v : Fin m) (r : Fin m → Fin l) :
    (zeroResult w mode z P T C K v).rename r = zeroResult (r w) (r mode) (r z) (r P) (r T) (r C) (r K) (r v) := by
  simp only [zeroResult, Formula.rename, zeroData_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

private theorem zero_run_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w mode z P n v : Fin m)
    (hw : Derives Γ (omega w)) (hm : Derives Γ (SyntaxNumeralSyntax.numeral 2 mode))
    (hd : Derives Γ (OriginalTermTraceSyntax.metadata w z P)) (hn : Derives Γ (SyntaxVariableSyntax.code true w z n)) :
    Derives Γ ((OriginalTransformRowSyntax.run 1 w mode z P n v).iff (.equal v P)) :=
  SyntaxTypeLocalTransfer.iff_trans (InstantiateVariableRun.run_iff hZ true w mode z P n z v hw hm hd hn)
    (InstantiateVariableSpecialization.at_point_iff hZ w z P z n v (.eqRefl z))

/-- The actual original new head becomes exactly the specified parameter
under original mode2 execution; the head code and execution are generated. -/
theorem zero_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w mode z P a f T A C R S K H v : Fin m)
    (hw : Derives Γ (omega w)) (hm : Derives Γ (SyntaxNumeralSyntax.numeral 2 mode))
    (hz : Derives Γ (empty z)) (hP : Derives Γ (SyntaxTermSyntax.term w z T P))
    (he : Derives Γ (ForcingOpenLayout.environment w z a f T R S))
    (hl : Derives Γ (SyntaxCodedMixedBinderSyntax.lifted w R S a f z T A C K H)) :
    Derives Γ ((zeroResult w mode z P T C K v).iff (.equal v P)) := by
  have hd : Derives Γ (OriginalTermTraceSyntax.metadata w z P) := .conjI
    (OmegaStructureAlgebra.zero_member w z (ZFContext.arithmetic hZ).base.extensionality hw hz)
    (SyntaxTerms.range hZ w z T P hw hP)
  apply Derives.conjI
  · apply Derives.impI
    let E := zeroResult w mode z P T C K v
    let B := zeroData w.castSucc mode.castSucc z.castSucc P.castSucc T.castSucc C.castSucc K.castSucc (Fin.last m) v.castSucc
    let Δ := Context.add B (Context.image Formula.raise (Context.add E Γ))
    apply Derives.exE (p := B) (.hyp (Or.inl rfl))
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have hr := zero_run_iff (ZFContext.under (ZFContext.add hZ E) B)
      w.castSucc mode.castSucc z.castSucc P.castSucc (Fin.last m) v.castSucc
      (of_eq (omega_rename w Fin.castSucc) (under (add hw E) B))
      (of_eq (SyntaxNumeralSyntax.numeral_rename 2 mode Fin.castSucc) (under (add hm E) B))
      (of_eq (OriginalTermTraceSyntax.metadata_rename w z P Fin.castSucc) (under (add hd E) B)) (.conjL (.conjR (.conjL hB)))
    exact .impE (.conjL hr) (.conjR (.conjR hB))
  · apply Derives.impI
    let E := Formula.equal v P
    let B := (SyntaxMixedImageHead.head w.castSucc C.castSucc T.castSucc z.castSucc (Fin.last m)).conj
      (field w.castSucc K.castSucc z.castSucc (Fin.last m))
    let Δ := Context.add B (Context.image Formula.raise (Context.add E Γ))
    apply Derives.exE (p := B) (add (ForcingOpenLift.zero_field hZ w z a f T A C R S K H hw hz he hl) E)
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have hr := zero_run_iff (ZFContext.under (ZFContext.add hZ E) B)
      w.castSucc mode.castSucc z.castSucc P.castSucc (Fin.last m) v.castSucc
      (of_eq (omega_rename w Fin.castSucc) (under (add hw E) B))
      (of_eq (SyntaxNumeralSyntax.numeral_rename 2 mode Fin.castSucc) (under (add hm E) B))
      (of_eq (OriginalTermTraceSyntax.metadata_rename w z P Fin.castSucc) (under (add hd E) B)) (.conjL (.conjR (.conjL hB)))
    have heq : Derives Δ (.equal v.castSucc P.castSucc) := under (Derives.hyp (Or.inl rfl) : Derives (Context.add E Γ) E) B
    have hrun := Derives.impE (.conjR hr) heq
    have ho : Derives Δ (zeroResult w.castSucc mode.castSucc z.castSucc P.castSucc T.castSucc C.castSucc K.castSucc v.castSucc) := by
      apply Derives.exI (Fin.last m)
      exact of_eq (by simp only [Formula.instantiate, zeroData_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]; rfl)
        (.conjI (.conjL hB) (.conjI (.conjR hB) hrun))
    exact of_eq (zeroResult_rename w mode z P T C K v Fin.castSucc).symm ho

def input {m} (bound : Bool) (w mode z P a f T A C R S K H i I q : Fin m) : Formula m :=
  (SyntaxNumeralSyntax.numeral 2 mode).conj ((SyntaxTermSyntax.term w z T P).conj
    (ForcingOpenLift.input bound w z a f T A C R S K H i I q))

def sentence {m} (bound : Bool) (w mode z P a f T A C R S K H i I q v : Fin m) : Source.Sentence :=
  ((input bound w mode z P a f T A C R S K H i I q).imp
    ((oldResult bound w mode z P A f K H i I v).iff (.equal v q))).close

theorem kernel_certificate {m} (bound : Bool) (w mode z P a f T A C R S K H i I q v : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (sentence bound w mode z P a f T A C R S K H i I q v)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  let E := input bound w mode z P a f T A C R S K H i I q
  let Γ := Context.add E (Source.SetLanguage.ZF.at m)
  have h : Derives Γ E := .hyp (Or.inl rfl)
  have hp := Derives.conjL (.conjR h)
  have hb := Derives.conjL (.conjR (.conjR h))
  have hi := Derives.conjR (.conjR (.conjR h))
  exact old_iff (ZFContext.add (ZFContext.source_ZF m) E) bound w mode z P a f T A C R S K H i I q v
    (.conjL hb) (.conjL h) (.conjL (.conjR hb)) hp (.conjL (.conjR (.conjR hb))) (.conjR (.conjR (.conjR hb)))
    (.conjL hi) (.conjL (.conjR hi)) (.conjR (.conjR hi))

def zeroInput {m} (w mode z P a f T A C R S K H : Fin m) : Formula m :=
  (omega w).conj ((SyntaxNumeralSyntax.numeral 2 mode).conj ((empty z).conj ((SyntaxTermSyntax.term w z T P).conj
    ((ForcingOpenLayout.environment w z a f T R S).conj (SyntaxCodedMixedBinderSyntax.lifted w R S a f z T A C K H)))))

def zeroSentence {m} (w mode z P a f T A C R S K H v : Fin m) : Source.Sentence :=
  ((zeroInput w mode z P a f T A C R S K H).imp ((zeroResult w mode z P T C K v).iff (.equal v P))).close

theorem zero_kernel_certificate {m} (w mode z P a f T A C R S K H v : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (zeroSentence w mode z P a f T A C R S K H v)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  let E := zeroInput w mode z P a f T A C R S K H
  let Γ := Context.add E (Source.SetLanguage.ZF.at m)
  have h : Derives Γ E := .hyp (Or.inl rfl)
  exact zero_iff (ZFContext.add (ZFContext.source_ZF m) E) w mode z P a f T A C R S K H v
    (.conjL h) (.conjL (.conjR h)) (.conjL (.conjR (.conjR h))) (.conjL (.conjR (.conjR (.conjR h))))
    (.conjL (.conjR (.conjR (.conjR (.conjR h))))) (.conjR (.conjR (.conjR (.conjR (.conjR h)))))

end PPAC.Migration.ForcingOpenInstantiate
