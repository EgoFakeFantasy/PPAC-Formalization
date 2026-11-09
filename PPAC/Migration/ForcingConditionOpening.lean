import PPAC.Migration.ForcingFormulaCancellation
import PPAC.Migration.ForcingReflexiveImages

/-! Actual rebind/open/original-mode2 cancellation at an ARBITRARY condition.
The direct opening uses the existing Replacement update S[j := P].
The external condition stored in S[j] is unrestricted. No equality answer,
formula-code standardness, new recursion or proof kernel is assumed. -/
namespace PPAC.Migration.ForcingConditionOpening
open Internal Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)
open StructuralListFieldSyntax (field field_rename)
open ForcingRebindOpeningTriangle (intro_old zero_from_field)
set_option maxRecDepth 32768
attribute [local irreducible] NaturalRecursionSyntax.matrix

private structure Inputs {m} (Γ : Context m) (w mode z a f T A C R S D K H j n q P x u t y o : Fin m) (d : Fin 6 → Fin m) : Prop where
  zf : ZFContext.Evidence Γ
  omega : Derives Γ (omega w)
  isMode : Derives Γ (SyntaxNumeralSyntax.numeral 2 mode)
  zero : Derives Γ (empty z)
  opening : Derives Γ (ForcingOpenLayout.environment w z a f T R S)
  lift : Derives Γ (SyntaxCodedMixedBinderSyntax.lifted w R S a f z T A C K H)
  data : Derives Γ (ForcingConditionRebind.data w a f A j n q d)
  condition : Derives Γ (Formula.mem j f)
  parameter : Derives Γ (SyntaxTermSyntax.term w z T P)
  replacement : Derives Γ (ForcingReflexiveImages.replacement w f z T S j P D)
  first : Derives Γ (SyntaxCodedMixedTermSyntax.substituted w (d 3) (d 5) a f A f x u)
  second : Derives Γ (SyntaxCodedMixedTermSyntax.substituted w K H A f C T u t)
  run : Derives Γ (OriginalTransformRowSyntax.run 1 w mode z P t y)
  direct : Derives Γ (SyntaxCodedMixedTermSyntax.substituted w R D a f z T x o)

private theorem Inputs.add {m} {Γ : Context m} {w mode z a f T A C R S D K H j n q P x u t y o : Fin m} {d : Fin 6 → Fin m}
    (h : Inputs Γ w mode z a f T A C R S D K H j n q P x u t y o d) (E : Formula m) : Inputs (Context.add E Γ) w mode z a f T A C R S D K H j n q P x u t y o d := {
  zf := ZFContext.add h.zf E
  omega := SourceLogic.add h.omega E
  isMode := SourceLogic.add h.isMode E
  zero := SourceLogic.add h.zero E
  opening := SourceLogic.add h.opening E
  lift := SourceLogic.add h.lift E
  data := SourceLogic.add h.data E
  condition := SourceLogic.add h.condition E
  parameter := SourceLogic.add h.parameter E
  replacement := SourceLogic.add h.replacement E
  first := SourceLogic.add h.first E
  second := SourceLogic.add h.second E
  run := SourceLogic.add h.run E
  direct := SourceLogic.add h.direct E
}

private theorem Inputs.under {m} {Γ : Context m} {w mode z a f T A C R S D K H j n q P x u t y o : Fin m} {d : Fin 6 → Fin m}
    (h : Inputs Γ w mode z a f T A C R S D K H j n q P x u t y o d) (B : Formula (m+1)) :
    Inputs (Context.add B (Context.image Formula.raise Γ)) w.castSucc mode.castSucc z.castSucc a.castSucc f.castSucc T.castSucc A.castSucc C.castSucc R.castSucc S.castSucc D.castSucc K.castSucc H.castSucc j.castSucc n.castSucc q.castSucc P.castSucc x.castSucc u.castSucc t.castSucc y.castSucc o.castSucc (fun k => (d k).castSucc) := {
  zf := ZFContext.under h.zf B
  omega := of_eq (omega_rename w Fin.castSucc) (SourceLogic.under h.omega B)
  isMode := of_eq (SyntaxNumeralSyntax.numeral_rename 2 mode Fin.castSucc) (SourceLogic.under h.isMode B)
  zero := of_eq (empty_rename z Fin.castSucc) (SourceLogic.under h.zero B)
  opening := of_eq (ForcingOpenLayout.environment_rename w z a f T R S Fin.castSucc) (SourceLogic.under h.opening B)
  lift := of_eq (SyntaxCodedMixedBinderSyntax.lifted_rename w R S a f z T A C K H Fin.castSucc) (SourceLogic.under h.lift B)
  data := of_eq (ForcingConditionRebind.data_rename w a f A j n q d Fin.castSucc) (SourceLogic.under h.data B)
  condition := SourceLogic.under h.condition B
  parameter := of_eq (SyntaxTermSyntax.term_rename w z T P Fin.castSucc) (SourceLogic.under h.parameter B)
  replacement := of_eq (ForcingReflexiveImages.replacement_rename w f z T S j P D Fin.castSucc) (SourceLogic.under h.replacement B)
  first := of_eq (SyntaxCodedMixedTermSyntax.substituted_rename w (d 3) (d 5) a f A f x u Fin.castSucc) (SourceLogic.under h.first B)
  second := of_eq (SyntaxCodedMixedTermSyntax.substituted_rename w K H A f C T u t Fin.castSucc) (SourceLogic.under h.second B)
  run := of_eq (OriginalTransformRowSyntax.run_rename 1 w mode z P t y Fin.castSucc) (SourceLogic.under h.run B)
  direct := of_eq (SyntaxCodedMixedTermSyntax.substituted_rename w R D a f z T x o Fin.castSucc) (SourceLogic.under h.direct B)
}

private theorem bound_point {m} {Γ : Context m} {w mode z a f T A C R S D K H j n q P x u t y o : Fin m} {d : Fin 6 → Fin m}
    (h : Inputs Γ w mode z a f T A C R S D K H j n q P x u t y o d) (i I : Fin m) (hx : Derives Γ (SyntaxVariableSyntax.code true w i x))
    (hs : Derives Γ (successor I i)) : Derives Γ (.equal y o) := by
  have hLists := ForcingOpenLayout.environment_types w z a f T R S h.opening
  have hNew := Derives.conjI (.conjL hLists) (ForcingReflexiveImages.target_type w f z T S j P D h.replacement)
  have hd := Derives.impE (.conjL (SyntaxCodedMixedTermFields.at_field h.zf true w R D a f z T x o i h.omega hNew hx)) h.direct
  have hr := ForcingRebindTerms.from_data h.zf true w a f A j n q x u i I d h.omega h.data hx (.conjL hd) hs
  have hu := Derives.impE (.conjL hr) h.first
  have hOut := SyntaxCodedMixedBinderTyping.output_lists w R S a f z T A C K H h.lift
  have ht := Derives.impE (.conjL (SyntaxCodedMixedTermFields.at_field h.zf true w K H A f C T u t I h.omega hOut hu)) h.second
  have hp := h.parameter
  have ho := intro_old true w mode z P A f K H i I t y ht h.run
  exact .impE (.conjL (ForcingOpenInstantiate.old_iff h.zf true w mode z P a f T A C R S K H i I o y
    h.omega h.isMode h.zero hp h.opening h.lift (.conjL hd) (.conjR hd) hs)) ho

private theorem away_point {m} {Γ : Context m} {w mode z a f T A C R S D K H j n q P x u t y o : Fin m} {d : Fin 6 → Fin m}
    (h : Inputs Γ w mode z a f T A C R S D K H j n q P x u t y o d) (i : Fin m) (hx : Derives Γ (SyntaxVariableSyntax.code false w i x))
    (hne : Derives Γ (Formula.equal i j).neg) : Derives Γ (.equal y o) := by
  have hLists := ForcingOpenLayout.environment_types w z a f T R S h.opening
  have hNew := Derives.conjI (.conjL hLists) (ForcingReflexiveImages.target_type w f z T S j P D h.replacement)
  have hd := Derives.impE (.conjL (SyntaxCodedMixedTermFields.at_field h.zf false w R D a f z T x o i h.omega hNew hx)) h.direct
  have hc := Derives.impE (.conjL (ForcingReflexiveImages.field_iff w f z T S j P D i o h.replacement (.conjL hd))) (.conjR hd)
  have hOld : Derives Γ (field w S i o) := by
    apply Derives.disjE hc
    · exact .botE (.impE (add hne _) (.conjL (.hyp (Or.inl rfl))))
    · exact .conjR (.hyp (Or.inl rfl))
  have hs : Derives Γ (ForcingOpenLift.step false i i) := .impI (.hyp (Or.inl rfl))
  have hr := ForcingRebindTerms.from_data h.zf false w a f A j n q x u i i d h.omega h.data hx (.conjL hd) hs
  have hv := Derives.impE (.conjL hr) h.first
  have hu : Derives Γ (SyntaxVariableSyntax.code false w i u) := by
    apply Derives.disjE hv
    · exact .botE (.impE (add hne _) (.conjL (.hyp (Or.inl rfl))))
    · exact .conjR (.hyp (Or.inl rfl))
  have hOut := SyntaxCodedMixedBinderTyping.output_lists w R S a f z T A C K H h.lift
  have ht := Derives.impE (.conjL (SyntaxCodedMixedTermFields.at_field h.zf false w K H A f C T u t i h.omega hOut hu)) h.second
  have hp := h.parameter
  have ho := intro_old false w mode z P A f K H i i t y ht h.run
  exact .impE (.conjL (ForcingOpenInstantiate.old_iff h.zf false w mode z P a f T A C R S K H i i o y
    h.omega h.isMode h.zero hp h.opening h.lift (.conjL hd) hOld hs)) ho


private theorem selected_point {m} {Γ : Context m} {w mode z a f T A C R S D K H j n q P x u t y o : Fin m} {d : Fin 6 → Fin m}
    (h : Inputs Γ w mode z a f T A C R S D K H j n q P x u t y o d) (i : Fin m) (hx : Derives Γ (SyntaxVariableSyntax.code false w i x))
    (hij : Derives Γ (.equal i j)) : Derives Γ (.equal y o) := by
  have hLists := ForcingOpenLayout.environment_types w z a f T R S h.opening
  have hNew := Derives.conjI (.conjL hLists) (ForcingReflexiveImages.target_type w f z T S j P D h.replacement)
  have hd := Derives.impE (.conjL (SyntaxCodedMixedTermFields.at_field h.zf false w R D a f z T x o i h.omega hNew hx)) h.direct
  have hs : Derives Γ (ForcingOpenLift.step false i i) := .impI (.hyp (Or.inl rfl))
  have hv := Derives.impE (.conjL (ForcingRebindTerms.from_data h.zf false w a f A j n q x u i i d h.omega h.data hx (.conjL hd) hs)) h.first
  have hu : Derives Γ (.equal u (d 1)) := by
    apply Derives.disjE hv
    · exact .conjR (.hyp (Or.inl rfl))
    · exact .botE (.impE (.conjL (.hyp (Or.inl rfl))) (add hij _))
  have hHead := Derives.conjL h.data
  have hzero := OmegaUniversal.empty_unique (d 0) z (ZFContext.arithmetic h.zf).base.extensionality (.conjL hHead) h.zero
  have hcode := AbstractVariableIndex.code_index_subst true w (d 0) z (d 1) hzero (.conjL (.conjR hHead))
  have hU := Derives.impE (.conjR (AbstractBinderRename.code_iff_equal h.zf true w z (d 1) u h.omega hcode)) hu
  have hOut := SyntaxCodedMixedBinderTyping.output_lists w R S a f z T A C K H h.lift
  have ht := Derives.impE (.conjL (SyntaxCodedMixedTermFields.at_field h.zf true w K H A f C T u t z h.omega hOut hU)) h.second
  have hp := h.parameter
  have ho := zero_from_field h.zf w mode z P a f T A C R S K H t y h.omega h.zero h.opening h.lift (.conjR ht) h.run
  have hyp := Derives.impE (.conjL (ForcingOpenInstantiate.zero_iff h.zf w mode z P a f T A C R S K H y h.omega h.isMode h.zero hp h.opening h.lift)) ho
  have hc := Derives.impE (.conjL (ForcingReflexiveImages.field_iff w f z T S j P D i o h.replacement (.conjL hd))) (.conjR hd)
  have hop : Derives Γ (.equal o P) := by
    apply Derives.disjE hc
    · exact .conjR (.hyp (Or.inl rfl))
    · exact .botE (.impE (.conjL (.hyp (Or.inl rfl))) (add hij _))
  exact eq_trans hyp (eq_symm hop)


private theorem excluded {m} {Γ : Context m} (p : Formula m) : Derives Γ (p.disj p.neg) := by
  apply Derives.classical
  let N := (p.disj p.neg).neg
  have hN : Derives (Context.add N Γ) N := .hyp (Or.inl rfl)
  have hn : Derives (Context.add N Γ) p.neg := .impI (.impE (add hN p) (.disjL (.hyp (Or.inl rfl))))
  exact .impE hN (.disjR hn)

private theorem point {m} {Γ : Context m} {w mode z a f T A C R S D K H j n q P x u t y o : Fin m} {d : Fin 6 → Fin m}
    (h : Inputs Γ w mode z a f T A C R S D K H j n q P x u t y o d) (bound : Bool) (i I : Fin m)
    (hx : Derives Γ (SyntaxVariableSyntax.code bound w i x)) (hs : Derives Γ (ForcingOpenLift.step bound i I)) :
    Derives Γ (.equal y o) := by
  cases bound with
  | true => exact bound_point h i I hx hs
  | false =>
    apply Derives.disjE (excluded (Formula.equal i j))
    · exact selected_point (h.add _) i (add hx _) (.hyp (Or.inl rfl))
    · exact away_point (h.add _) i (add hx _) (.hyp (Or.inl rfl))

private theorem all_terms {m} {Γ : Context m} {w mode z a f T A C R S D K H j n q P x u t y o : Fin m} {d : Fin 6 → Fin m}
    (h : Inputs Γ w mode z a f T A C R S D K H j n q P x u t y o d) : Derives Γ (.equal y o) := by
  have hx := SyntaxCodedMixedTermTyping.source_type w R D a f z T x o h.direct
  apply Derives.disjE (.conjR hx)
  · let E := SyntaxTermSyntax.branch true w a x
    let B := SyntaxTermSyntax.branchWitness true w a x
    let Δ := Context.add B (Context.image Formula.raise (Context.add E Γ))
    apply SyntaxTermSyntax.eliminate_branch true w a x _ (.hyp (Or.inl rfl))
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have h1 := (h.add E).under B
    have htype := SyntaxCodedMixedTermTyping.source_type w.castSucc R.castSucc D.castSucc a.castSucc f.castSucc z.castSucc T.castSucc x.castSucc o.castSucc h1.direct
    have hin := StructuralListTraceOrder.member_member h1.zf w.castSucc (Fin.last m) a.castSucc h1.omega (.conjL (.conjL htype)) (.conjL hB)
    let F := (Formula.mem (Fin.last (m+1)) w.castSucc.castSucc).conj (successor (Fin.last (m+1)) (Fin.last m).castSucc)
    let Ξ := Context.add F (Context.image Formula.raise Δ)
    apply Derives.exE (p := F) (OriginalBinderStepSyntax.successor_exists w.castSucc (Fin.last m) h1.omega hin)
    have hF : Derives Ξ F := .hyp (Or.inl rfl)
    have h2 := h1.under F
    have hc : Derives Ξ (SyntaxVariableSyntax.code true w.castSucc.castSucc (Fin.last m).castSucc x.castSucc.castSucc) :=
      of_eq (SyntaxVariableSyntax.code_rename true w.castSucc (Fin.last m) x.castSucc Fin.castSucc) (under (.conjR hB) F)
    exact bound_point h2 (Fin.last m).castSucc (Fin.last (m+1)) hc (.conjR hF)
  · let E := SyntaxTermSyntax.branch false w f x
    let B := SyntaxTermSyntax.branchWitness false w f x
    let Δ := Context.add B (Context.image Formula.raise (Context.add E Γ))
    apply SyntaxTermSyntax.eliminate_branch false w f x _ (.hyp (Or.inl rfl))
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have hs : Derives Δ (ForcingOpenLift.step false (Fin.last m) (Fin.last m)) := .impI (.hyp (Or.inl rfl))
    exact point ((h.add E).under B) false (Fin.last m) (Fin.last m) (.conjR hB) hs

/-- The actual rebind / lifted opening / original mode2 outputs coincide
with direct opening for EVERY legal internal source term. Variable-role,
index and successor witnesses are derived internally, including nonstandard
ones. Inputs are real original operation judgments, not equality answers. -/
theorem term {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w mode z a f T A C R S D K H j n q P x u t y o : Fin m) (d : Fin 6 → Fin m)
    (hw : Derives Γ (omega w)) (hm : Derives Γ (SyntaxNumeralSyntax.numeral 2 mode))
    (hz : Derives Γ (empty z)) (he : Derives Γ (ForcingOpenLayout.environment w z a f T R S))
    (hl : Derives Γ (SyntaxCodedMixedBinderSyntax.lifted w R S a f z T A C K H))
    (hd : Derives Γ (ForcingConditionRebind.data w a f A j n q d))
    (hj : Derives Γ (.mem j f)) (hp : Derives Γ (SyntaxTermSyntax.term w z T P))
    (hD : Derives Γ (ForcingReflexiveImages.replacement w f z T S j P D))
    (hFirst : Derives Γ (SyntaxCodedMixedTermSyntax.substituted w (d 3) (d 5) a f A f x u))
    (hSecond : Derives Γ (SyntaxCodedMixedTermSyntax.substituted w K H A f C T u t))
    (hRun : Derives Γ (OriginalTransformRowSyntax.run 1 w mode z P t y))
    (hDirect : Derives Γ (SyntaxCodedMixedTermSyntax.substituted w R D a f z T x o)) : Derives Γ (.equal y o) :=
  all_terms {
    zf := hZ
    omega := hw
    isMode := hm
    zero := hz
    opening := he
    lift := hl
    data := hd
    condition := hj
    parameter := hp
    replacement := hD
    first := hFirst
    second := hSecond
    run := hRun
    direct := hDirect
  }

private def quad {m} (a b c d : Fin m) : Fin 4 → Fin m :=
  Fin.cases a (Fin.cases b (Fin.cases c (fun _ => d)))

private def runs {m} (w : Fin m) (a b R S : Fin 4 → Fin m) (x u t y o : Fin m) : Formula m :=
  (ForcingTermDiagram.step w a b R S 0 x u).conj
    ((ForcingTermDiagram.step w a b R S 1 u t).conj
      ((ForcingTermDiagram.step w a b R S 2 t y).conj (ForcingTermDiagram.step w a b R S 3 x o)))

theorem term_diagram {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w mode z a f T A C R S D K H j n q P r s : Fin m) (d : Fin 6 → Fin m)
    (hw : Derives Γ (omega w)) (hm : Derives Γ (SyntaxNumeralSyntax.numeral 2 mode)) (hz : Derives Γ (empty z))
    (he : Derives Γ (ForcingOpenLayout.environment w z a f T R S))
    (hl : Derives Γ (SyntaxCodedMixedBinderSyntax.lifted w R S a f z T A C K H))
    (hd : Derives Γ (ForcingConditionRebind.data w a f A j n q d)) (hj : Derives Γ (.mem j f))
    (hp : Derives Γ (SyntaxTermSyntax.term w z T P))
    (hUpdate : Derives Γ (ForcingReflexiveImages.replacement w f z T S j P D))
    (hi : Derives Γ (SyntaxTopCodedEnvironmentSyntax.instantiateCoded w z T C P r s)) :
    Derives Γ (ForcingTermDiagram.diagram w (quad a A C z) (quad f f T T) (quad (d 3) K r R) (quad (d 5) H s D)) := by
  have hf := InstantiateOperationFrameRoot.from_actual_input hZ w mode z P T C r s hw hm hz hi
  apply OriginalUniversalBlock.intro_many 5
  apply Derives.impI
  let B := runs (old 5 w) (fun i => old 5 (quad a A C z i)) (fun i => old 5 (quad f f T T i))
    (fun i => old 5 (quad (d 3) K r R i)) (fun i => old 5 (quad (d 5) H s D i))
    (slot 5 0) (slot 5 1) (slot 5 2) (slot 5 3) (slot 5 4)
  let Δ := Context.add B (raisedContext 5 Γ)
  have hD : Derives Δ B := .hyp (Or.inl rfl)
  have hZ5 := HornBinderRules.zf_body 5 hZ B
  have hw5 := of_eq (omega_rename w (old 5)) (HornBinderRules.under_body 5 hw B)
  have hf5 := of_eq (InstantiateOperationFrameSyntax.frame_rename w mode z P C T z T r s (old 5)) (HornBinderRules.under_body 5 hf B)
  have hr := Derives.conjR (Derives.impE (.conjR (InstantiateFrameTerm.guarded_coded_iff hZ5
    (old 5 w) (old 5 mode) (old 5 z) (old 5 P) (old 5 C) (old 5 T) (old 5 z) (old 5 T) (old 5 r) (old 5 s)
    (slot 5 2) (slot 5 3) hw5 hf5)) (.conjL (.conjR (.conjR hD))))
  exact term hZ5 (old 5 w) (old 5 mode) (old 5 z) (old 5 a) (old 5 f) (old 5 T) (old 5 A) (old 5 C)
    (old 5 R) (old 5 S) (old 5 D) (old 5 K) (old 5 H) (old 5 j) (old 5 n) (old 5 q) (old 5 P)
    (slot 5 0) (slot 5 1) (slot 5 2) (slot 5 3) (slot 5 4) (fun i => old 5 (d i))
    hw5 (of_eq (SyntaxNumeralSyntax.numeral_rename 2 mode (old 5)) (HornBinderRules.under_body 5 hm B))
    (of_eq (empty_rename z (old 5)) (HornBinderRules.under_body 5 hz B))
    (of_eq (ForcingOpenLayout.environment_rename w z a f T R S (old 5)) (HornBinderRules.under_body 5 he B))
    (of_eq (SyntaxCodedMixedBinderSyntax.lifted_rename w R S a f z T A C K H (old 5)) (HornBinderRules.under_body 5 hl B))
    (of_eq (ForcingConditionRebind.data_rename w a f A j n q d (old 5)) (HornBinderRules.under_body 5 hd B))
    (HornBinderRules.under_body 5 hj B)
    (of_eq (SyntaxTermSyntax.term_rename w z T P (old 5)) (HornBinderRules.under_body 5 hp B))
    (of_eq (ForcingReflexiveImages.replacement_rename w f z T S j P D (old 5)) (HornBinderRules.under_body 5 hUpdate B))
    (.conjL hD) (.conjL (.conjR hD)) hr (.conjR (.conjR (.conjR hD)))

theorem formula {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w mode z a f T A C R S D K H j n q I Y O P r s : Fin m) (d : Fin 6 → Fin m)
    (hw : Derives Γ (omega w)) (hm : Derives Γ (SyntaxNumeralSyntax.numeral 2 mode)) (hz : Derives Γ (empty z))
    (he : Derives Γ (ForcingOpenLayout.environment w z a f T R S))
    (hl : Derives Γ (SyntaxCodedMixedBinderSyntax.lifted w R S a f z T A C K H))
    (hd : Derives Γ (ForcingConditionRebind.data w a f A j n q d)) (hj : Derives Γ (.mem j f))
    (hp : Derives Γ (SyntaxTermSyntax.term w z T P))
    (hD : Derives Γ (ForcingReflexiveImages.replacement w f z T S j P D))
    (hi : Derives Γ (SyntaxTopCodedEnvironmentSyntax.instantiateCoded w z T C P r s))
    (hopen : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w K H A f C T q I))
    (hrun : Derives Γ (OriginalTransformRowSyntax.run 3 w mode z P I Y))
    (hdirect : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w R D a f z T n O)) : Derives Γ (.equal Y O) := by
  have hdiagram := term_diagram hZ w mode z a f T A C R S D K H j n q P r s d hw hm hz he hl hd hj hp hD hi
  have htype := SyntaxMixedFormulaJudgment.target_type w K H A f C T q I hopen
  have htop := Derives.impE (.conjL (InstantiateTopFormulaOperation.at_codes_iff hZ w mode z P T C r s I Y hw hm hz hi htype)) hrun
  have hcode := Derives.impE (.conjL (SyntaxTopFormulaCodes.instantiate_at_codes hZ w z T C P I Y r s hw hi)) htop
  have hreb := Derives.conjR (.conjR (.conjR hd))
  exact ForcingFormulaInduction.cancel hZ w (quad a A C z) (quad f f T T) (quad (d 3) K r R) (quad (d 5) H s D)
    n q I Y O hw hdiagram hreb hopen hcode hdirect

theorem from_compiled {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w mode z a f T A C R S D K H j n q I Y O P r s : Fin m)
    (hw : Derives Γ (omega w))
    (hm : Derives Γ (SyntaxNumeralSyntax.numeral 2 mode))
    (hz : Derives Γ (empty z))
    (he : Derives Γ (ForcingOpenLayout.environment w z a f T R S))
    (hl : Derives Γ (SyntaxCodedMixedBinderSyntax.lifted w R S a f z T A C K H))
    (hd : Derives Γ (ForcingConditionRebind.compiled w a f A j n q))
    (hj : Derives Γ (Formula.mem j f))
    (hp : Derives Γ (SyntaxTermSyntax.term w z T P))
    (hD : Derives Γ (ForcingReflexiveImages.replacement w f z T S j P D))
    (hi : Derives Γ (SyntaxTopCodedEnvironmentSyntax.instantiateCoded w z T C P r s))
    (ho : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w K H A f C T q I))
    (hr : Derives Γ (OriginalTransformRowSyntax.run 3 w mode z P I Y))
    (hdir : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w R D a f z T n O)) : Derives Γ (.equal Y O) := by
  let B := ForcingConditionRebind.data (HornBinderSyntax.old 6 w) (HornBinderSyntax.old 6 a) (HornBinderSyntax.old 6 f) (HornBinderSyntax.old 6 A)
    (HornBinderSyntax.old 6 j) (HornBinderSyntax.old 6 n) (HornBinderSyntax.old 6 q) (HornBinderSyntax.slot 6)
  let Δ := Context.add B (HornBinderSyntax.raisedContext 6 Γ)
  apply HornBinderRules.eliminate_many 6 B _ hd
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  exact formula (HornBinderRules.zf_body 6 hZ B)
    (HornBinderSyntax.old 6 w) (HornBinderSyntax.old 6 mode) (HornBinderSyntax.old 6 z) (HornBinderSyntax.old 6 a) (HornBinderSyntax.old 6 f) (HornBinderSyntax.old 6 T) (HornBinderSyntax.old 6 A) (HornBinderSyntax.old 6 C) (HornBinderSyntax.old 6 R) (HornBinderSyntax.old 6 S) (HornBinderSyntax.old 6 D) (HornBinderSyntax.old 6 K) (HornBinderSyntax.old 6 H) (HornBinderSyntax.old 6 j) (HornBinderSyntax.old 6 n) (HornBinderSyntax.old 6 q) (HornBinderSyntax.old 6 I) (HornBinderSyntax.old 6 Y) (HornBinderSyntax.old 6 O) (HornBinderSyntax.old 6 P) (HornBinderSyntax.old 6 r) (HornBinderSyntax.old 6 s) (HornBinderSyntax.slot 6)
    (of_eq (omega_rename w (HornBinderSyntax.old 6)) (HornBinderRules.under_body 6 hw B))
    (of_eq (SyntaxNumeralSyntax.numeral_rename 2 mode (HornBinderSyntax.old 6)) (HornBinderRules.under_body 6 hm B))
    (of_eq (empty_rename z (HornBinderSyntax.old 6)) (HornBinderRules.under_body 6 hz B))
    (of_eq (ForcingOpenLayout.environment_rename w z a f T R S (HornBinderSyntax.old 6)) (HornBinderRules.under_body 6 he B))
    (of_eq (SyntaxCodedMixedBinderSyntax.lifted_rename w R S a f z T A C K H (HornBinderSyntax.old 6)) (HornBinderRules.under_body 6 hl B))
    hB
    (HornBinderRules.under_body 6 hj B)
    (of_eq (SyntaxTermSyntax.term_rename w z T P (HornBinderSyntax.old 6)) (HornBinderRules.under_body 6 hp B))
    (of_eq (ForcingReflexiveImages.replacement_rename w f z T S j P D (HornBinderSyntax.old 6)) (HornBinderRules.under_body 6 hD B))
    (of_eq (SyntaxTopCodedEnvironmentSyntax.instantiateCoded_rename w z T C P r s (HornBinderSyntax.old 6)) (HornBinderRules.under_body 6 hi B))
    (of_eq (SyntaxMixedFormulaJudgmentSyntax.substituted_rename w K H A f C T q I (HornBinderSyntax.old 6)) (HornBinderRules.under_body 6 ho B))
    (of_eq (OriginalTransformRowSyntax.run_rename 3 w mode z P I Y (HornBinderSyntax.old 6)) (HornBinderRules.under_body 6 hr B))
    (of_eq (SyntaxMixedFormulaJudgmentSyntax.substituted_rename w R D a f z T n O (HornBinderSyntax.old 6)) (HornBinderRules.under_body 6 hdir B))

/-- The actual condition-update code and direct formula output are BOTH constructed
internally, using existing Replacement/encoding and full mixed-formula totality. -/
def resultData {m} (w z a f T R S j n P Y D O : Fin m) : Formula m :=
  (ForcingReflexiveImages.replacement w f z T S j P D).conj
    ((SyntaxMixedFormulaJudgmentSyntax.substituted w R D a f z T n O).conj (.equal Y O))

theorem resultData_rename {m l} (w z a f T R S j n P Y D O : Fin m) (ρ : Fin m → Fin l) :
    (resultData w z a f T R S j n P Y D O).rename ρ = resultData (ρ w) (ρ z) (ρ a) (ρ f) (ρ T) (ρ R) (ρ S) (ρ j) (ρ n) (ρ P) (ρ Y) (ρ D) (ρ O) := by
  simp only [resultData, Formula.rename, ForcingReflexiveImages.replacement_rename, SyntaxMixedFormulaJudgmentSyntax.substituted_rename]

def resultBody {m} (w z a f T R S j n P Y : Fin m) : Formula (m+2) :=
  resultData (old 2 w) (old 2 z) (old 2 a) (old 2 f) (old 2 T) (old 2 R) (old 2 S) (old 2 j) (old 2 n) (old 2 P) (old 2 Y) (slot 2 0) (slot 2 1)
def result {m} (w z a f T R S j n P Y : Fin m) : Formula m := existsMany 2 (resultBody w z a f T R S j n P Y)

theorem result_rename {m l} (w z a f T R S j n P Y : Fin m) (ρ : Fin m → Fin l) :
    (result w z a f T R S j n P Y).rename ρ = result (ρ w) (ρ z) (ρ a) (ρ f) (ρ T) (ρ R) (ρ S) (ρ j) (ρ n) (ρ P) (ρ Y) := by
  simp only [result, existsMany_rename, resultBody, resultData_rename, lift_old, lift_slot]

theorem normalize {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w mode z a f T A C R S K H j n q I Y P r s : Fin m)
    (hw : Derives Γ (omega w))
    (hm : Derives Γ (SyntaxNumeralSyntax.numeral 2 mode))
    (hz : Derives Γ (empty z))
    (he : Derives Γ (ForcingOpenLayout.environment w z a f T R S))
    (hl : Derives Γ (SyntaxCodedMixedBinderSyntax.lifted w R S a f z T A C K H))
    (hd : Derives Γ (ForcingConditionRebind.compiled w a f A j n q))
    (hj : Derives Γ (Formula.mem j f))
    (hp : Derives Γ (SyntaxTermSyntax.term w z T P))
    (hn : Derives Γ (FormulaCodeSyntax.formulaCode w n a f))
    (hi : Derives Γ (SyntaxTopCodedEnvironmentSyntax.instantiateCoded w z T C P r s))
    (ho : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w K H A f C T q I))
    (hr : Derives Γ (OriginalTransformRowSyntax.run 3 w mode z P I Y))
    : Derives Γ (result w z a f T R S j n P Y) := by
  have hLists := ForcingOpenLayout.environment_types w z a f T R S he
  let B := ForcingReflexiveImages.replacement w.castSucc f.castSucc z.castSucc T.castSucc S.castSucc j.castSucc P.castSucc (Fin.last m)
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) (ForcingReflexiveImages.exists_replacement hZ w f z T S j P hw (.conjR hLists) hp)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hZ1 := ZFContext.under hZ B
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw B)
  have hn1 := of_eq (FormulaCodeSyntax.formulaCode_rename w n a f Fin.castSucc) (under hn B)
  have hl1 := of_eq (SyntaxMixedImageCodeSyntax.termLists_rename w a f z T R S Fin.castSucc) (under hLists B)
  have hNew := Derives.conjI (.conjL hl1) (ForcingReflexiveImages.target_type w.castSucc f.castSucc z.castSucc T.castSucc S.castSucc j.castSucc P.castSucc (Fin.last m) hB)
  let E := SyntaxMixedFormulaJudgmentSyntax.substituted w.castSucc.castSucc R.castSucc.castSucc (Fin.last m).castSucc a.castSucc.castSucc f.castSucc.castSucc z.castSucc.castSucc T.castSucc.castSucc n.castSucc.castSucc (Fin.last (m+1))
  let Ξ := Context.add E (Context.image Formula.raise Δ)
  apply Derives.exE (p := E) (SyntaxMixedFormulaOutputInduction.actual_exists hZ1 w.castSucc R.castSucc (Fin.last m) a.castSucc f.castSucc z.castSucc T.castSucc n.castSucc hw1 (.conjI hn1 hNew))
  have hE : Derives Ξ E := .hyp (Or.inl rfl)
  have hD := of_eq (ForcingReflexiveImages.replacement_rename w.castSucc f.castSucc z.castSucc T.castSucc S.castSucc j.castSucc P.castSucc (Fin.last m) Fin.castSucc) (under hB E)
  have hw2 : Derives Ξ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (under (under hw B) E)
  have hm2 : Derives Ξ (SyntaxNumeralSyntax.numeral 2 mode.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxNumeralSyntax.numeral_rename]) (under (under hm B) E)
  have hz2 : Derives Ξ (empty z.castSucc.castSucc) := of_eq (by simp only [Formula.raise, empty_rename]) (under (under hz B) E)
  have he2 : Derives Ξ (ForcingOpenLayout.environment w.castSucc.castSucc z.castSucc.castSucc a.castSucc.castSucc f.castSucc.castSucc T.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc) := of_eq (by simp only [Formula.raise, ForcingOpenLayout.environment_rename]) (under (under he B) E)
  have hl2 : Derives Ξ (SyntaxCodedMixedBinderSyntax.lifted w.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc a.castSucc.castSucc f.castSucc.castSucc z.castSucc.castSucc T.castSucc.castSucc A.castSucc.castSucc C.castSucc.castSucc K.castSucc.castSucc H.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxCodedMixedBinderSyntax.lifted_rename]) (under (under hl B) E)
  have hd2 : Derives Ξ (ForcingConditionRebind.compiled w.castSucc.castSucc a.castSucc.castSucc f.castSucc.castSucc A.castSucc.castSucc j.castSucc.castSucc n.castSucc.castSucc q.castSucc.castSucc) := of_eq (by simp only [Formula.raise, ForcingConditionRebind.compiled_rename]) (under (under hd B) E)
  have hj2 : Derives Ξ (Formula.mem j.castSucc.castSucc f.castSucc.castSucc) := (under (under hj B) E)
  have hp2 : Derives Ξ (SyntaxTermSyntax.term w.castSucc.castSucc z.castSucc.castSucc T.castSucc.castSucc P.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxTermSyntax.term_rename]) (under (under hp B) E)
  have hi2 : Derives Ξ (SyntaxTopCodedEnvironmentSyntax.instantiateCoded w.castSucc.castSucc z.castSucc.castSucc T.castSucc.castSucc C.castSucc.castSucc P.castSucc.castSucc r.castSucc.castSucc s.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxTopCodedEnvironmentSyntax.instantiateCoded_rename]) (under (under hi B) E)
  have ho2 : Derives Ξ (SyntaxMixedFormulaJudgmentSyntax.substituted w.castSucc.castSucc K.castSucc.castSucc H.castSucc.castSucc A.castSucc.castSucc f.castSucc.castSucc C.castSucc.castSucc T.castSucc.castSucc q.castSucc.castSucc I.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxMixedFormulaJudgmentSyntax.substituted_rename]) (under (under ho B) E)
  have hr2 : Derives Ξ (OriginalTransformRowSyntax.run 3 w.castSucc.castSucc mode.castSucc.castSucc z.castSucc.castSucc P.castSucc.castSucc I.castSucc.castSucc Y.castSucc.castSucc) := of_eq (by simp only [Formula.raise, OriginalTransformRowSyntax.run_rename]) (under (under hr B) E)
  have hEq := from_compiled (ZFContext.under hZ1 E)
    w.castSucc.castSucc mode.castSucc.castSucc z.castSucc.castSucc a.castSucc.castSucc f.castSucc.castSucc T.castSucc.castSucc A.castSucc.castSucc C.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc (Fin.last m).castSucc K.castSucc.castSucc H.castSucc.castSucc j.castSucc.castSucc n.castSucc.castSucc q.castSucc.castSucc I.castSucc.castSucc Y.castSucc.castSucc (Fin.last (m+1)) P.castSucc.castSucc r.castSucc.castSucc s.castSucc.castSucc
    hw2 hm2 hz2 he2 hl2 hd2 hj2 hp2 hD hi2 ho2 hr2 hE
  have hout : Derives Ξ (result w.castSucc.castSucc z.castSucc.castSucc a.castSucc.castSucc f.castSucc.castSucc T.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc j.castSucc.castSucc n.castSucc.castSucc P.castSucc.castSucc Y.castSucc.castSucc) := by
    apply HornBinderRules.intro_many 2 _ (SetLanguage.args2 (Fin.last m).castSucc (Fin.last (m+1)))
    exact of_eq (by simp only [resultBody, resultData_rename, assign_old, assign_slot]; rfl) (.conjI hD (.conjI hE hEq))
  exact of_eq (by simp only [Formula.raise, result_rename]) hout

def input {m} (w mode z a f T A C R S K H j n q I Y P r s : Fin m) : Formula m :=
  (omega w).conj ((SyntaxNumeralSyntax.numeral 2 mode).conj ((empty z).conj ((ForcingOpenLayout.environment w z a f T R S).conj ((SyntaxCodedMixedBinderSyntax.lifted w R S a f z T A C K H).conj ((ForcingConditionRebind.compiled w a f A j n q).conj ((Formula.mem j f).conj ((SyntaxTermSyntax.term w z T P).conj ((FormulaCodeSyntax.formulaCode w n a f).conj ((SyntaxTopCodedEnvironmentSyntax.instantiateCoded w z T C P r s).conj ((SyntaxMixedFormulaJudgmentSyntax.substituted w K H A f C T q I).conj (OriginalTransformRowSyntax.run 3 w mode z P I Y)))))))))))

def sentence {m} (w mode z a f T A C R S K H j n q I Y P r s : Fin m) : Source.Sentence :=
  ((input w mode z a f T A C R S K H j n q I Y P r s).imp (result w z a f T R S j n P Y)).close

theorem kernel_certificate {m} (w mode z a f T A C R S K H j n q I Y P r s : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (sentence w mode z a f T A C R S K H j n q I Y P r s)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  let E := input w mode z a f T A C R S K H j n q I Y P r s
  let Γ := Context.add E (Source.SetLanguage.ZF.at m)
  have h : Derives Γ E := .hyp (Or.inl rfl)
  exact normalize (ZFContext.add (ZFContext.source_ZF m) E) w mode z a f T A C R S K H j n q I Y P r s
    (.conjL h)
    (.conjL (.conjR h))
    (.conjL (.conjR (.conjR h)))
    (.conjL (.conjR (.conjR (.conjR h))))
    (.conjL (.conjR (.conjR (.conjR (.conjR h)))))
    (.conjL (.conjR (.conjR (.conjR (.conjR (.conjR h))))))
    (.conjL (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR h)))))))
    (.conjL (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR h))))))))
    (.conjL (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR h)))))))))
    (.conjL (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR h))))))))))
    (.conjL (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR h)))))))))))
    (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR h)))))))))))

end PPAC.Migration.ForcingConditionOpening
