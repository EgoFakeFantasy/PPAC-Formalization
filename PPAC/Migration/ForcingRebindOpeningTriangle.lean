import PPAC.Migration.ForcingRebindTerms
import PPAC.Migration.ForcingConditionInstance
import PPAC.Migration.Internal.OriginalBinderStepSyntax

/-! Root term diagram for the SAME actual rebind tables, original lifted
pointwise opening, and ORIGINAL kind1/mode2 execution. Compare their actual
outputs with the direct original opening. Full formula/binder composition
and normalized forcing MP remain separate obligations. -/
namespace PPAC.Migration.ForcingRebindOpeningTriangle
open Internal Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)
open StructuralListFieldSyntax (field field_rename)
set_option maxRecDepth 32768
attribute [local irreducible] NaturalRecursionSyntax.matrix

private structure Inputs {m} (Γ : Context m) (w mode z a f T A C R S K H j n q P x u t y o : Fin m) (d : Fin 6 → Fin m) : Prop where
  zf : ZFContext.Evidence Γ
  omega : Derives Γ (omega w)
  isMode : Derives Γ (SyntaxNumeralSyntax.numeral 2 mode)
  zero : Derives Γ (empty z)
  opening : Derives Γ (ForcingOpenLayout.environment w z a f T R S)
  lift : Derives Γ (SyntaxCodedMixedBinderSyntax.lifted w R S a f z T A C K H)
  data : Derives Γ (ForcingConditionRebind.data w a f A j n q d)
  condition : Derives Γ (Formula.mem j f)
  parameter : Derives Γ (field w S j P)
  first : Derives Γ (SyntaxCodedMixedTermSyntax.substituted w (d 3) (d 5) a f A f x u)
  second : Derives Γ (SyntaxCodedMixedTermSyntax.substituted w K H A f C T u t)
  run : Derives Γ (OriginalTransformRowSyntax.run 1 w mode z P t y)
  direct : Derives Γ (SyntaxCodedMixedTermSyntax.substituted w R S a f z T x o)

private theorem Inputs.add {m} {Γ : Context m} {w mode z a f T A C R S K H j n q P x u t y o : Fin m} {d : Fin 6 → Fin m}
    (h : Inputs Γ w mode z a f T A C R S K H j n q P x u t y o d) (E : Formula m) : Inputs (Context.add E Γ) w mode z a f T A C R S K H j n q P x u t y o d := {
  zf := ZFContext.add h.zf E
  omega := SourceLogic.add h.omega E
  isMode := SourceLogic.add h.isMode E
  zero := SourceLogic.add h.zero E
  opening := SourceLogic.add h.opening E
  lift := SourceLogic.add h.lift E
  data := SourceLogic.add h.data E
  condition := SourceLogic.add h.condition E
  parameter := SourceLogic.add h.parameter E
  first := SourceLogic.add h.first E
  second := SourceLogic.add h.second E
  run := SourceLogic.add h.run E
  direct := SourceLogic.add h.direct E
}

private theorem Inputs.under {m} {Γ : Context m} {w mode z a f T A C R S K H j n q P x u t y o : Fin m} {d : Fin 6 → Fin m}
    (h : Inputs Γ w mode z a f T A C R S K H j n q P x u t y o d) (B : Formula (m+1)) :
    Inputs (Context.add B (Context.image Formula.raise Γ)) w.castSucc mode.castSucc z.castSucc a.castSucc f.castSucc T.castSucc A.castSucc C.castSucc R.castSucc S.castSucc K.castSucc H.castSucc j.castSucc n.castSucc q.castSucc P.castSucc x.castSucc u.castSucc t.castSucc y.castSucc o.castSucc (fun k => (d k).castSucc) := {
  zf := ZFContext.under h.zf B
  omega := of_eq (omega_rename w Fin.castSucc) (SourceLogic.under h.omega B)
  isMode := of_eq (SyntaxNumeralSyntax.numeral_rename 2 mode Fin.castSucc) (SourceLogic.under h.isMode B)
  zero := of_eq (empty_rename z Fin.castSucc) (SourceLogic.under h.zero B)
  opening := of_eq (ForcingOpenLayout.environment_rename w z a f T R S Fin.castSucc) (SourceLogic.under h.opening B)
  lift := of_eq (SyntaxCodedMixedBinderSyntax.lifted_rename w R S a f z T A C K H Fin.castSucc) (SourceLogic.under h.lift B)
  data := of_eq (ForcingConditionRebind.data_rename w a f A j n q d Fin.castSucc) (SourceLogic.under h.data B)
  condition := SourceLogic.under h.condition B
  parameter := of_eq (field_rename w S j P Fin.castSucc) (SourceLogic.under h.parameter B)
  first := of_eq (SyntaxCodedMixedTermSyntax.substituted_rename w (d 3) (d 5) a f A f x u Fin.castSucc) (SourceLogic.under h.first B)
  second := of_eq (SyntaxCodedMixedTermSyntax.substituted_rename w K H A f C T u t Fin.castSucc) (SourceLogic.under h.second B)
  run := of_eq (OriginalTransformRowSyntax.run_rename 1 w mode z P t y Fin.castSucc) (SourceLogic.under h.run B)
  direct := of_eq (SyntaxCodedMixedTermSyntax.substituted_rename w R S a f z T x o Fin.castSucc) (SourceLogic.under h.direct B)
}

theorem intro_old {m} {Γ : Context m} (bound : Bool) (w mode z P A f K H i I t y : Fin m)
    (hf : Derives Γ ((Formula.mem (if bound then I else i) (SyntaxTermSyntax.limit bound A f)).conj
      (field w (SyntaxIndexMapSyntax.selectMap bound K H) (if bound then I else i) t)))
    (hr : Derives Γ (OriginalTransformRowSyntax.run 1 w mode z P t y)) :
    Derives Γ (ForcingOpenInstantiate.oldResult bound w mode z P A f K H i I y) := by
  change Derives Γ (.ex
    (((Formula.mem (if bound then I.castSucc else i.castSucc) (SyntaxTermSyntax.limit bound A.castSucc f.castSucc)).conj
      (field w.castSucc (SyntaxIndexMapSyntax.selectMap bound K.castSucc H.castSucc) (if bound then I.castSucc else i.castSucc) (Fin.last m))).conj
        (OriginalTransformRowSyntax.run 1 w.castSucc mode.castSucc z.castSucc P.castSucc (Fin.last m) y.castSucc)))
  apply Derives.exI t
  exact of_eq (by cases bound <;> simp only [Formula.instantiate, Formula.rename, field_rename, OriginalTransformRowSyntax.run_rename,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq, SyntaxTermSyntax.limit, SyntaxIndexMapSyntax.selectMap, Bool.false_eq_true, ↓reduceIte]) (.conjI hf hr)

private theorem intro_zero {m} {Γ : Context m} (w mode z P T C K t y : Fin m)
    (hh : Derives Γ (SyntaxMixedImageHead.head w C T z t)) (hf : Derives Γ (field w K z t))
    (hr : Derives Γ (OriginalTransformRowSyntax.run 1 w mode z P t y)) :
    Derives Γ (ForcingOpenInstantiate.zeroResult w mode z P T C K y) := by
  change Derives Γ (.ex ((SyntaxMixedImageHead.head w.castSucc C.castSucc T.castSucc z.castSucc (Fin.last m)).conj
    ((field w.castSucc K.castSucc z.castSucc (Fin.last m)).conj (OriginalTransformRowSyntax.run 1 w.castSucc mode.castSucc z.castSucc P.castSucc (Fin.last m) y.castSucc))))
  apply Derives.exI t
  exact of_eq (by simp only [Formula.instantiate, Formula.rename, SyntaxMixedImageHead.head_rename, field_rename,
    OriginalTransformRowSyntax.run_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI hh (.conjI hf hr))

theorem field_index {m} {Γ : Context m} (w S i j x : Fin m)
    (he : Derives Γ (.equal i j)) (hf : Derives Γ (field w S i x)) : Derives Γ (field w S j x) := by
  let F := field w.castSucc S.castSucc (Fin.last m) x.castSucc
  have hh : Derives Γ (F.instantiate i) := of_eq (by simp only [F, Formula.instantiate, field_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hf
  exact of_eq (by simp only [F, Formula.instantiate, field_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (Derives.eqSubst F he hh)

theorem zero_from_field {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w mode z P a f T A C R S K H t y : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (he : Derives Γ (ForcingOpenLayout.environment w z a f T R S))
    (hl : Derives Γ (SyntaxCodedMixedBinderSyntax.lifted w R S a f z T A C K H))
    (hf : Derives Γ (field w K z t)) (hr : Derives Γ (OriginalTransformRowSyntax.run 1 w mode z P t y)) :
    Derives Γ (ForcingOpenInstantiate.zeroResult w mode z P T C K y) := by
  let B := (SyntaxMixedImageHead.head w.castSucc C.castSucc T.castSucc z.castSucc (Fin.last m)).conj
    (field w.castSucc K.castSucc z.castSucc (Fin.last m))
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) (ForcingOpenLift.zero_field hZ w z a f T A C R S K H hw hz he hl)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw B)
  have hz1 := of_eq (empty_rename z Fin.castSucc) (under hz B)
  have hf1 := of_eq (field_rename w K z t Fin.castSucc) (under hf B)
  have hzn := OmegaStructureAlgebra.zero_member w.castSucc z.castSucc (ZFContext.arithmetic (ZFContext.under hZ B)).base.extensionality hw1 hz1
  have hEq := StructuralListFieldValues.unique (ZFContext.under hZ B) w.castSucc K.castSucc z.castSucc (Fin.last m) t.castSucc hw1 hzn (.conjR hB) hf1
  have hc := Derives.impE (.conjR (AbstractBinderRename.code_iff_equal (ZFContext.under hZ B) true w.castSucc z.castSucc (Fin.last m) t.castSucc hw1 (.conjL (.conjR (.conjL hB))))) (eq_symm hEq)
  have ht := SyntaxAtomLogic.term_output_subst w.castSucc C.castSucc T.castSucc (Fin.last m) t.castSucc hEq (.conjR (.conjR (.conjL hB)))
  have hh : Derives Δ (SyntaxMixedImageHead.head w.castSucc C.castSucc T.castSucc z.castSucc t.castSucc) := .conjI (.conjL (.conjL hB)) (.conjI hc ht)
  have ho := intro_zero w.castSucc mode.castSucc z.castSucc P.castSucc T.castSucc C.castSucc K.castSucc t.castSucc y.castSucc hh hf1
    (of_eq (OriginalTransformRowSyntax.run_rename 1 w mode z P t y Fin.castSucc) (under hr B))
  exact of_eq (ForcingOpenInstantiate.zeroResult_rename w mode z P T C K y Fin.castSucc).symm ho

private theorem bound_point {m} {Γ : Context m} {w mode z a f T A C R S K H j n q P x u t y o : Fin m} {d : Fin 6 → Fin m}
    (h : Inputs Γ w mode z a f T A C R S K H j n q P x u t y o d) (i I : Fin m) (hx : Derives Γ (SyntaxVariableSyntax.code true w i x))
    (hs : Derives Γ (successor I i)) : Derives Γ (.equal y o) := by
  have hLists := ForcingOpenLayout.environment_types w z a f T R S h.opening
  have hd := Derives.impE (.conjL (SyntaxCodedMixedTermFields.at_field h.zf true w R S a f z T x o i h.omega hLists hx)) h.direct
  have hr := ForcingRebindTerms.from_data h.zf true w a f A j n q x u i I d h.omega h.data hx (.conjL hd) hs
  have hu := Derives.impE (.conjL hr) h.first
  have hOut := SyntaxCodedMixedBinderTyping.output_lists w R S a f z T A C K H h.lift
  have ht := Derives.impE (.conjL (SyntaxCodedMixedTermFields.at_field h.zf true w K H A f C T u t I h.omega hOut hu)) h.second
  have hp := SyntaxMixedImageCodeFields.field_type w f z T S j P (.conjR hLists) h.condition h.parameter
  have ho := intro_old true w mode z P A f K H i I t y ht h.run
  exact .impE (.conjL (ForcingOpenInstantiate.old_iff h.zf true w mode z P a f T A C R S K H i I o y
    h.omega h.isMode h.zero hp h.opening h.lift (.conjL hd) (.conjR hd) hs)) ho

private theorem away_point {m} {Γ : Context m} {w mode z a f T A C R S K H j n q P x u t y o : Fin m} {d : Fin 6 → Fin m}
    (h : Inputs Γ w mode z a f T A C R S K H j n q P x u t y o d) (i : Fin m) (hx : Derives Γ (SyntaxVariableSyntax.code false w i x))
    (hne : Derives Γ (Formula.equal i j).neg) : Derives Γ (.equal y o) := by
  have hLists := ForcingOpenLayout.environment_types w z a f T R S h.opening
  have hd := Derives.impE (.conjL (SyntaxCodedMixedTermFields.at_field h.zf false w R S a f z T x o i h.omega hLists hx)) h.direct
  have hs : Derives Γ (ForcingOpenLift.step false i i) := .impI (.hyp (Or.inl rfl))
  have hr := ForcingRebindTerms.from_data h.zf false w a f A j n q x u i i d h.omega h.data hx (.conjL hd) hs
  have hv := Derives.impE (.conjL hr) h.first
  have hu : Derives Γ (SyntaxVariableSyntax.code false w i u) := by
    apply Derives.disjE hv
    · exact .botE (.impE (add hne _) (.conjL (.hyp (Or.inl rfl))))
    · exact .conjR (.hyp (Or.inl rfl))
  have hOut := SyntaxCodedMixedBinderTyping.output_lists w R S a f z T A C K H h.lift
  have ht := Derives.impE (.conjL (SyntaxCodedMixedTermFields.at_field h.zf false w K H A f C T u t i h.omega hOut hu)) h.second
  have hp := SyntaxMixedImageCodeFields.field_type w f z T S j P (.conjR hLists) h.condition h.parameter
  have ho := intro_old false w mode z P A f K H i i t y ht h.run
  exact .impE (.conjL (ForcingOpenInstantiate.old_iff h.zf false w mode z P a f T A C R S K H i i o y
    h.omega h.isMode h.zero hp h.opening h.lift (.conjL hd) (.conjR hd) hs)) ho


private theorem selected_point {m} {Γ : Context m} {w mode z a f T A C R S K H j n q P x u t y o : Fin m} {d : Fin 6 → Fin m}
    (h : Inputs Γ w mode z a f T A C R S K H j n q P x u t y o d) (i : Fin m) (hx : Derives Γ (SyntaxVariableSyntax.code false w i x))
    (hij : Derives Γ (.equal i j)) : Derives Γ (.equal y o) := by
  have hLists := ForcingOpenLayout.environment_types w z a f T R S h.opening
  have hd := Derives.impE (.conjL (SyntaxCodedMixedTermFields.at_field h.zf false w R S a f z T x o i h.omega hLists hx)) h.direct
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
  have hp := SyntaxMixedImageCodeFields.field_type w f z T S j P (.conjR hLists) h.condition h.parameter
  have ho := zero_from_field h.zf w mode z P a f T A C R S K H t y h.omega h.zero h.opening h.lift (.conjR ht) h.run
  have hyp := Derives.impE (.conjL (ForcingOpenInstantiate.zero_iff h.zf w mode z P a f T A C R S K H y h.omega h.isMode h.zero hp h.opening h.lift)) ho
  have hjo := field_index w S i j o hij (.conjR hd)
  have hjn := StructuralListTraceOrder.member_member h.zf w j f h.omega (.conjL (.conjR hLists)) h.condition
  have hop := StructuralListFieldValues.unique h.zf w S j o P h.omega hjn hjo h.parameter
  exact eq_trans hyp (eq_symm hop)

private theorem excluded {m} {Γ : Context m} (p : Formula m) : Derives Γ (p.disj p.neg) := by
  apply Derives.classical
  let N := (p.disj p.neg).neg
  have hN : Derives (Context.add N Γ) N := .hyp (Or.inl rfl)
  have hn : Derives (Context.add N Γ) p.neg := .impI (.impE (add hN p) (.disjL (.hyp (Or.inl rfl))))
  exact .impE hN (.disjR hn)

private theorem point {m} {Γ : Context m} {w mode z a f T A C R S K H j n q P x u t y o : Fin m} {d : Fin 6 → Fin m}
    (h : Inputs Γ w mode z a f T A C R S K H j n q P x u t y o d) (bound : Bool) (i I : Fin m)
    (hx : Derives Γ (SyntaxVariableSyntax.code bound w i x)) (hs : Derives Γ (ForcingOpenLift.step bound i I)) :
    Derives Γ (.equal y o) := by
  cases bound with
  | true => exact bound_point h i I hx hs
  | false =>
    apply Derives.disjE (excluded (Formula.equal i j))
    · exact selected_point (h.add _) i (add hx _) (.hyp (Or.inl rfl))
    · exact away_point (h.add _) i (add hx _) (.hyp (Or.inl rfl))

private theorem all_terms {m} {Γ : Context m} {w mode z a f T A C R S K H j n q P x u t y o : Fin m} {d : Fin 6 → Fin m}
    (h : Inputs Γ w mode z a f T A C R S K H j n q P x u t y o d) : Derives Γ (.equal y o) := by
  have hx := SyntaxCodedMixedTermTyping.source_type w R S a f z T x o h.direct
  apply Derives.disjE (.conjR hx)
  · let E := SyntaxTermSyntax.branch true w a x
    let B := SyntaxTermSyntax.branchWitness true w a x
    let Δ := Context.add B (Context.image Formula.raise (Context.add E Γ))
    apply SyntaxTermSyntax.eliminate_branch true w a x _ (.hyp (Or.inl rfl))
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have h1 := (h.add E).under B
    have htype := SyntaxCodedMixedTermTyping.source_type w.castSucc R.castSucc S.castSucc a.castSucc f.castSucc z.castSucc T.castSucc x.castSucc o.castSucc h1.direct
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
    (w mode z a f T A C R S K H j n q P x u t y o : Fin m) (d : Fin 6 → Fin m)
    (hw : Derives Γ (omega w)) (hm : Derives Γ (SyntaxNumeralSyntax.numeral 2 mode))
    (hz : Derives Γ (empty z)) (he : Derives Γ (ForcingOpenLayout.environment w z a f T R S))
    (hl : Derives Γ (SyntaxCodedMixedBinderSyntax.lifted w R S a f z T A C K H))
    (hd : Derives Γ (ForcingConditionRebind.data w a f A j n q d))
    (hj : Derives Γ (.mem j f)) (hp : Derives Γ (field w S j P))
    (hFirst : Derives Γ (SyntaxCodedMixedTermSyntax.substituted w (d 3) (d 5) a f A f x u))
    (hSecond : Derives Γ (SyntaxCodedMixedTermSyntax.substituted w K H A f C T u t))
    (hRun : Derives Γ (OriginalTransformRowSyntax.run 1 w mode z P t y))
    (hDirect : Derives Γ (SyntaxCodedMixedTermSyntax.substituted w R S a f z T x o)) : Derives Γ (.equal y o) :=
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
    first := hFirst
    second := hSecond
    run := hRun
    direct := hDirect
  }

def input {m} (w mode z a f T A C R S K H j n q P x u t y o : Fin m) (d : Fin 6 → Fin m) : Formula m :=
  (omega w).conj ((SyntaxNumeralSyntax.numeral 2 mode).conj ((empty z).conj ((ForcingOpenLayout.environment w z a f T R S).conj ((SyntaxCodedMixedBinderSyntax.lifted w R S a f z T A C K H).conj ((ForcingConditionRebind.data w a f A j n q d).conj ((Formula.mem j f).conj ((field w S j P).conj ((SyntaxCodedMixedTermSyntax.substituted w (d 3) (d 5) a f A f x u).conj ((SyntaxCodedMixedTermSyntax.substituted w K H A f C T u t).conj ((OriginalTransformRowSyntax.run 1 w mode z P t y).conj ((SyntaxCodedMixedTermSyntax.substituted w R S a f z T x o))))))))))))

def sentence {m} (w mode z a f T A C R S K H j n q P x u t y o : Fin m) (d : Fin 6 → Fin m) : Source.Sentence :=
  ((input w mode z a f T A C R S K H j n q P x u t y o d).imp (.equal y o)).close

theorem kernel_certificate {m} (w mode z a f T A C R S K H j n q P x u t y o : Fin m) (d : Fin 6 → Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (sentence w mode z a f T A C R S K H j n q P x u t y o d)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  let E := input w mode z a f T A C R S K H j n q P x u t y o d
  let Γ := Context.add E (Source.SetLanguage.ZF.at m)
  have h : Derives Γ E := .hyp (Or.inl rfl)
  exact term (ZFContext.add (ZFContext.source_ZF m) E) w mode z a f T A C R S K H j n q P x u t y o d
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

end PPAC.Migration.ForcingRebindOpeningTriangle
