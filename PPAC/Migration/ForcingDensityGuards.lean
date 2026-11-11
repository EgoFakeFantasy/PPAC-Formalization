import PPAC.Migration.ForcingDensityInstantiation

/-! Identify the actual member/order guards of a density instance with the
original literal guard queries at the selected condition, on the same table. -/
namespace PPAC.Migration.ForcingDensityGuards
open Internal Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)
open SyntaxMixedFormulaJudgmentSyntax (substituted substituted_rename)
open SyntaxTopFormulaSyntax (instantiated instantiated_rename)
open StructuralListSyntax (consCode consCode_rename)
open StructuralListFieldSyntax (field field_rename)
open NativeProofQuotation (eliminate_objects)
open InternalProofBackground (implication implication_rename)

set_option maxRecDepth 16384

private abbrev test : Formula 1 := OriginalAxiomCodeTest.test false

private theorem guard_scope {k m} {Γ : Context m} (order : Bool) (Reln : Formula (k+2))
    (w A A' f head Q : Fin m) (he : Derives Γ (.equal A A'))
    (h : Derives Γ (ForcingGuardCode.compiled order Reln w A f head Q)) :
    Derives Γ (ForcingGuardCode.compiled order Reln w A' f head Q) := by
  let F := ForcingGuardCode.compiled order Reln w.castSucc (Fin.last m) f.castSucc head.castSucc Q.castSucc
  exact of_eq (by simp only [F, Formula.instantiate, ForcingGuardCode.compiled_rename,
      Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
    (.eqSubst F he (of_eq (by simp only [F, Formula.instantiate, ForcingGuardCode.compiled_rename,
      Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) h))

private theorem instance_scope {m} {Γ : Context m} (w z b C C' p U Y : Fin m)
    (he : Derives Γ (.equal C C')) (h : Derives Γ (instantiated w z b C p U Y)) :
    Derives Γ (instantiated w z b C' p U Y) := by
  let F := instantiated w.castSucc z.castSucc b.castSucc (Fin.last m) p.castSucc U.castSucc Y.castSucc
  exact of_eq (by simp only [F, Formula.instantiate, instantiated_rename,
      Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
    (.eqSubst F he (of_eq (by simp only [F, Formula.instantiate, instantiated_rename,
      Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) h))

private theorem with_guard_query {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (order : Bool)
    (Reln : Formula (k+2)) (w z a A C f b L S K H p D head Q U Y : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (ht : Derives Γ (SyntaxTermSyntax.term w z b p))
    (hl : Derives Γ (SyntaxCodedMixedBinderSyntax.lifted w L S a f z b A C K H))
    (hD : Derives Γ (consCode w p L D))
    (hc : Derives Γ (ForcingGuardCode.compiled order Reln w A f head Q))
    (hU : Derives Γ (substituted w K H A f C b Q U))
    (hY : Derives Γ (instantiated w z b C p U Y)) (out : Formula m)
    (use : ∀ {l} {Δ : Context l} (ρ : Fin m → Fin l), ZFContext.Evidence Δ →
      (∀ {F : Formula m}, Derives Γ F → Derives Δ (F.rename ρ)) →
      Derives Δ (SyntaxMixedImageCodeSyntax.termLists (ρ w) (ρ A) (ρ f) (ρ z) (ρ b) (ρ D) (ρ S)) →
      Derives Δ (field (ρ w) (ρ D) (ρ z) (ρ p)) →
      Derives Δ (substituted (ρ w) (ρ D) (ρ S) (ρ A) (ρ f) (ρ z) (ρ b) (ρ Q) (ρ Y)) →
      Derives Δ (out.rename ρ)) : Derives Γ out := by
  have hin := SyntaxCodedMixedBinderTyping.input_of_lifted w L S a f z b A C K H hl
  have hLists := Derives.conjL hin
  have hb := Derives.conjL hLists
  have hL := Derives.conjL (.conjL (.conjR (.conjR hb)))
  have hp := SyntaxTerms.range hZ w z b p hw ht
  have hd := TypedArgumentListConstruction.cons_list hZ w a A z b p L D hw ht hb hD (.conjL (.conjR hin))
  have hNew : Derives Γ (SyntaxMixedImageCodeSyntax.termLists w A f z b D S) := .conjI hd (.conjR hLists)
  have hField := StructuralListFieldCons.zero_value hZ w p L D z hw hp hL hD hz
  have hType := ForcingGuardCode.compiled_type order Reln w A f head Q hc
  refine eliminate_objects hZ 1 (fun ρ v =>
    substituted (ρ w) (ρ D) (ρ S) (ρ A) (ρ f) (ρ z) (ρ b) (ρ Q) (v 0)) ?_ out ?_
  · exact SyntaxMixedFormulaOutputInduction.actual_exists hZ w D S A f z b Q hw (.conjI hType hNew)
  intro l Δ ρ v hZ1 lift hRaw
  have hw1 := of_eq (omega_rename _ _) (lift hw)
  have hz1 := of_eq (empty_rename _ _) (lift hz)
  have he := ForcingBinderFormula.native hZ1 (ρ w) (ρ z) (ρ a) (ρ f) (ρ b) (ρ A) (ρ C)
    (ρ L) (ρ S) (ρ K) (ρ H) (ρ p) (ρ D) (ρ Q) (ρ U) (ρ Y) (v 0) hw1 hz1
    (of_eq (SyntaxMixedImageCodeSyntax.termLists_rename _ _ _ _ _ _ _ _) (lift hLists))
    (of_eq (SyntaxCodedMixedBinderSyntax.lifted_rename _ _ _ _ _ _ _ _ _ _ _ _) (lift hl))
    (of_eq (consCode_rename _ _ _ _ _) (lift hD))
    (of_eq (substituted_rename _ _ _ _ _ _ _ _ _ _) (lift hU))
    (of_eq (instantiated_rename _ _ _ _ _ _ _ _) (lift hY)) hRaw
  have hSame := SyntaxMixedFormulaJudgmentSubst.subst_q (ρ w) (ρ D) (ρ S) (ρ A) (ρ f)
    (ρ z) (ρ b) (ρ Q) (v 0) (ρ Y) (eq_symm he) hRaw
  exact use ρ hZ1 lift (of_eq (SyntaxMixedImageCodeSyntax.termLists_rename _ _ _ _ _ _ _ _) (lift hNew))
    (of_eq (field_rename _ _ _ _ _) (lift hField)) hSame

private theorem at_guard {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (order : Bool)
    (Reln : Formula (k+2)) (w z a A C f b L S K H p D head Q U Y : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (ht : Derives Γ (SyntaxTermSyntax.term w z b p))
    (hl : Derives Γ (SyntaxCodedMixedBinderSyntax.lifted w L S a f z b A C K H))
    (hD : Derives Γ (consCode w p L D))
    (hh : Derives Γ (SyntaxVariableSyntax.code true w z head))
    (hc : Derives Γ (ForcingGuardCode.compiled order Reln w A f head Q))
    (hU : Derives Γ (substituted w K H A f C b Q U))
    (hY : Derives Γ (instantiated w z b C p U Y)) :
    Derives Γ (ForcingGuardOpening.result order Reln w z f b p S A head Q Y) := by
  let out := ForcingGuardOpening.result order Reln w z f b p S A head Q Y
  apply with_guard_query hZ order Reln w z a A C f b L S K H p D head Q U Y hw hz ht hl hD hc hU hY out
  intro l Δ ρ hZ1 lift hLists hField hSame
  have hw1 := of_eq (omega_rename _ _) (lift hw)
  have hz1 := of_eq (empty_rename _ _) (lift hz)
  exact of_eq (ForcingGuardOpening.result_rename order Reln w z f b p S A head Q Y ρ).symm
    (ForcingRawGuardOpening.from_compiled hZ1 order Reln (ρ w) (ρ z) (ρ A) (ρ f) (ρ b)
      (ρ D) (ρ S) (ρ p) (ρ head) (ρ Q) (ρ Y)
      (.conjI hw1 (.conjI hz1
        (.conjI (of_eq (SyntaxVariableSyntax.code_rename true _ _ _ _) (lift hh))
          (.conjI (of_eq (SyntaxTermSyntax.term_rename _ _ _ _ _) (lift ht))
            (.conjI hLists
              (.conjI hField
                (.conjI (of_eq (ForcingGuardCode.compiled_rename order Reln _ _ _ _ _ _) (lift hc)) hSame))))))))

/-- The original literal guard predicates on the same selected condition and
free table, for the two actual pointwise output codes. -/
def guardPair {k m} (Reln : Formula (k+2)) (w z A f b S p head M O Ym Yo : Fin m) : Formula m :=
  (ForcingGuardOpening.result false Reln w z f b p S A head M Ym).conj
    (ForcingGuardOpening.result true Reln w z f b p S A head O Yo)

theorem guardPair_rename {k m l} (Reln : Formula (k+2)) (w z A f b S p head M O Ym Yo : Fin m)
    (ρ : Fin m → Fin l) :
    (guardPair Reln w z A f b S p head M O Ym Yo).rename ρ =
      guardPair Reln (ρ w) (ρ z) (ρ A) (ρ f) (ρ b) (ρ S) (ρ p) (ρ head) (ρ M) (ρ O) (ρ Ym) (ρ Yo) := by
  simp only [guardPair, Formula.rename, ForcingGuardOpening.result_rename]

private theorem align_guards {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (Reln : Formula (k+2))
    (w z a A A' C f b L S K H p head M O Um Uo Ym Yo : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) (hA : Derives Γ (successor A a))
    (ht : Derives Γ (SyntaxTermSyntax.term w z b p))
    (hl : Derives Γ (SyntaxCodedMixedBinderSyntax.lifted w L S a f z b A' C K H))
    (hh : Derives Γ (SyntaxVariableSyntax.code true w z head))
    (hm : Derives Γ (ForcingGuardCode.compiled false Reln w A f head M))
    (ho : Derives Γ (ForcingGuardCode.compiled true Reln w A f head O))
    (hUm : Derives Γ (substituted w K H A' f C b M Um))
    (hUo : Derives Γ (substituted w K H A' f C b O Uo))
    (hYm : Derives Γ (instantiated w z b C p Um Ym))
    (hYo : Derives Γ (instantiated w z b C p Uo Yo)) :
    Derives Γ (guardPair Reln w z A' f b S p head M O Ym Yo) := by
  have hi := SyntaxCodedMixedBinderTyping.input_of_lifted w L S a f z b A' C K H hl
  have hEq := OmegaUniversal.successor_unique A A' a (ZFContext.arithmetic hZ).base.extensionality hA (.conjL (.conjR hi))
  have hm' := guard_scope false Reln w A A' f head M hEq hm
  have ho' := guard_scope true Reln w A A' f head O hEq ho
  have hp := SyntaxTerms.range hZ w z b p hw ht
  have hL := Derives.conjL (.conjL (.conjR (.conjR (.conjL (.conjL hi)))))
  let P := (Formula.mem (Fin.last m) w.castSucc).conj (consCode w.castSucc p.castSucc L.castSucc (Fin.last m))
  apply Derives.exE (p := P) (StructuralConsCore.exists_cons hZ w p L hw hp hL)
  let Δ := Context.add P (Context.image Formula.raise Γ)
  have hP : Derives Δ P := .hyp (Or.inl rfl)
  have hZ1 := ZFContext.under hZ P
  have hw1 := of_eq (omega_rename _ _) (under hw P)
  have hz1 := of_eq (empty_rename _ _) (under hz P)
  have ht1 := of_eq (SyntaxTermSyntax.term_rename _ _ _ _ _) (under ht P)
  have hl1 := of_eq (SyntaxCodedMixedBinderSyntax.lifted_rename _ _ _ _ _ _ _ _ _ _ _ _) (under hl P)
  have hh1 := of_eq (SyntaxVariableSyntax.code_rename true _ _ _ _) (under hh P)
  have m1 := at_guard hZ1 false Reln w.castSucc z.castSucc a.castSucc A'.castSucc C.castSucc f.castSucc b.castSucc
    L.castSucc S.castSucc K.castSucc H.castSucc p.castSucc (Fin.last m) head.castSucc M.castSucc Um.castSucc Ym.castSucc
    hw1 hz1 ht1 hl1 (.conjR hP) hh1 (of_eq (ForcingGuardCode.compiled_rename false Reln _ _ _ _ _ _) (under hm' P))
    (of_eq (substituted_rename _ _ _ _ _ _ _ _ _ _) (under hUm P))
    (of_eq (instantiated_rename _ _ _ _ _ _ _ _) (under hYm P))
  have o1 := at_guard hZ1 true Reln w.castSucc z.castSucc a.castSucc A'.castSucc C.castSucc f.castSucc b.castSucc
    L.castSucc S.castSucc K.castSucc H.castSucc p.castSucc (Fin.last m) head.castSucc O.castSucc Uo.castSucc Yo.castSucc
    hw1 hz1 ht1 hl1 (.conjR hP) hh1 (of_eq (ForcingGuardCode.compiled_rename true Reln _ _ _ _ _ _) (under ho' P))
    (of_eq (substituted_rename _ _ _ _ _ _ _ _ _ _) (under hUo P))
    (of_eq (instantiated_rename _ _ _ _ _ _ _ _) (under hYo P))
  exact of_eq (guardPair_rename Reln w z A' f b S p head M O Ym Yo Fin.castSucc).symm (.conjI m1 o1)


open FormulaCodeSyntax (formulaCode)
open SyntaxLogicalSyntax (binaryCode)

/-- An internal proof transformer for the exact two guards of the selected
density instance. It takes proof codes under G, never truth of G. -/
def discharge {m} (w z b G M O Tail : Fin m) : Formula m :=
  (implication test w z b G M).imp ((implication test w z b G O).imp (implication test w z b G Tail))

theorem discharge_rename {m l} (w z b G M O Tail : Fin m) (ρ : Fin m → Fin l) :
    (discharge w z b G M O Tail).rename ρ = discharge (ρ w) (ρ z) (ρ b) (ρ G) (ρ M) (ρ O) (ρ Tail) := by
  simp only [discharge, Formula.rename, implication_rename]

private theorem discharge_guards {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z b G M O Mid Tail Whole : Fin m) (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hG : Derives Γ (formulaCode w G z b)) (hWhole : Derives Γ (formulaCode w Whole z b))
    (hM : Derives Γ (binaryCode 2 w M Mid Whole)) (hO : Derives Γ (binaryCode 2 w O Tail Mid))
    (hp : Derives Γ (implication test w z b G Whole)) :
    Derives Γ (discharge w z b G M O Tail) := by
  let P := implication test w z b G M
  let Q := implication test w z b G O
  apply Derives.impI
  apply Derives.impI
  let Δ := Context.add Q (Context.add P Γ)
  have hZ2 := ZFContext.add (ZFContext.add hZ P) Q
  have move {F : Formula m} (hf : Derives Γ F) : Derives Δ F := add (add hf P) Q
  have hm : Derives Δ P := .hyp (Or.inr (Or.inl rfl))
  have ho : Derives Δ Q := .hyp (Or.inl rfl)
  have hMid := Derives.conjR (Derives.conjR
    (Derives.impE (.conjL (FormulaCodeKnownLogical.binary2_iff hZ w z b M Mid Whole hw hM)) hWhole))
  have hPM := ForcingNegMemberProof.discharge hZ2 test w z b G M Mid Whole (move hw) (move hz)
    (move hG) (move hWhole) (move hM) hm (move hp)
  exact ForcingNegMemberProof.discharge hZ2 test w z b G O Tail Mid (move hw) (move hz)
    (move hG) (move hMid) (move hO) ho hPM

/-- Connect the actual raw and native guard records, and discharge the same
two constructors when their internal proofs under G are supplied. -/
theorem from_records {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (Reln : Formula (k+2))
    (w z a A A' C f b L S K H p head G M O Tail I U : Fin m) (u v x : Fin 4 → Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) (hA : Derives Γ (successor A a))
    (hG : Derives Γ (formulaCode w G z b))
    (hl : Derives Γ (SyntaxCodedMixedBinderSyntax.lifted w L S a f z b A' C K H))
    (hh : Derives Γ (SyntaxVariableSyntax.code true w z head))
    (hm : Derives Γ (ForcingGuardCode.compiled false Reln w A f head M))
    (ho : Derives Γ (ForcingGuardCode.compiled true Reln w A f head O))
    (hu : Derives Γ (ForcingRawModalBody.data w K H A' f C b M O Tail I U u))
    (hv : Derives Γ (ForcingDensityInstantiation.pointData w z b U p G (u 1) (u 2) (u 3) (u 0) v))
    (hx : Derives Γ (ForcingRawModalBody.data w (v 2) (v 3) (v 0) b z b (u 1) (u 2) (u 3) (u 0) (v 1) x)) :
    Derives Γ ((guardPair Reln w z A' f b S p head M O (x 1) (x 2)).conj (discharge w z b G (x 1) (x 2) (x 3))) := by
  have hInst : Derives Γ (SyntaxTopFormulaSyntax.instantiateState w z b (v 0) p U (v 1) (v 2) (v 3)) :=
    .conjL (.conjR hv)
  have hCoded := Derives.conjL hInst
  have ht := Derives.conjL (SyntaxTopCodedEnvironmentTyping.instantiate_input w z b (v 0) p (v 2) (v 3) hCoded)
  have hlIn := SyntaxCodedMixedBinderTyping.input_of_lifted w L S a f z b A' C K H hl
  have hCe := OmegaUniversal.successor_unique (v 0) C z (ZFContext.arithmetic hZ).base.extensionality
    (.conjL hv) (.conjR (.conjR hlIn))
  have hmNative := SyntaxTopFormulaSyntax.intro_instantiated w z b (v 0) p (u 1) (x 1) (v 2) (v 3)
    hCoded (.conjL (.conjR (.conjL hx)))
  have hoNative := SyntaxTopFormulaSyntax.intro_instantiated w z b (v 0) p (u 2) (x 2) (v 2) (v 3)
    hCoded (.conjL (.conjR (.conjR hx)))
  have guard := align_guards hZ Reln w z a A A' C f b L S K H p head M O (u 1) (u 2) (x 1) (x 2)
    hw hz hA ht hl hh hm ho (.conjL (.conjR (.conjL hu))) (.conjL (.conjR (.conjR hu)))
    (instance_scope w z b (v 0) C p (u 1) (x 1) hCe hmNative)
    (instance_scope w z b (v 0) C p (u 2) (x 2) hCe hoNative)
  have hType := SyntaxMixedFormulaJudgment.target_type w (v 2) (v 3) (v 0) b z b U (v 1) (.conjR hInst)
  have hTransfer := discharge_guards hZ w z b G (x 1) (x 2) (x 0) (x 3) (v 1)
    hw hz hG hType (.conjL (.conjL hx)) (.conjL (.conjR hx)) (.conjR (.conjR (.conjR hv)))
  exact .conjI guard hTransfer


def input {k m} (Reln : Formula (k+2)) (w z a A A' C f b L S K H p head G M O Tail I U : Fin m)
    (u v x : Fin 4 → Fin m) : Formula m :=
  (omega w).conj ((empty z).conj ((successor A a).conj ((formulaCode w G z b).conj
    ((SyntaxCodedMixedBinderSyntax.lifted w L S a f z b A' C K H).conj
      ((SyntaxVariableSyntax.code true w z head).conj
        ((ForcingGuardCode.compiled false Reln w A f head M).conj
          ((ForcingGuardCode.compiled true Reln w A f head O).conj
            ((ForcingRawModalBody.data w K H A' f C b M O Tail I U u).conj
              ((ForcingDensityInstantiation.pointData w z b U p G (u 1) (u 2) (u 3) (u 0) v).conj
                (ForcingRawModalBody.data w (v 2) (v 3) (v 0) b z b (u 1) (u 2) (u 3) (u 0) (v 1) x))))))))))

def sentence {k m} (Reln : Formula (k+2)) (w z a A A' C f b L S K H p head G M O Tail I U : Fin m)
    (u v x : Fin 4 → Fin m) : Source.Sentence :=
  ((input Reln w z a A A' C f b L S K H p head G M O Tail I U u v x).imp
    ((guardPair Reln w z A' f b S p head M O (x 1) (x 2)).conj (discharge w z b G (x 1) (x 2) (x 3)))).close

theorem kernel_certificate {k m} (Reln : Formula (k+2)) (w z a A A' C f b L S K H p head G M O Tail I U : Fin m)
    (u v x : Fin 4 → Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence
      (sentence Reln w z a A A' C f b L S K H p head G M O Tail I U u v x)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  let P := input Reln w z a A A' C f b L S K H p head G M O Tail I U u v x
  have h : Derives (Context.add P (SetLanguage.ZF.at m)) P := .hyp (Or.inl rfl)
  have h2 := Derives.conjR h
  have h3 := Derives.conjR h2
  have h4 := Derives.conjR h3
  have h5 := Derives.conjR h4
  have h6 := Derives.conjR h5
  have h7 := Derives.conjR h6
  have h8 := Derives.conjR h7
  have h9 := Derives.conjR h8
  have h10 := Derives.conjR h9
  exact from_records (ZFContext.add (ZFContext.source_ZF m) P) Reln w z a A A' C f b L S K H
    p head G M O Tail I U u v x (.conjL h) (.conjL h2) (.conjL h3) (.conjL h4) (.conjL h5) (.conjL h6)
    (.conjL h7) (.conjL h8) (.conjL h9) (.conjL h10) (.conjR h10)


/-- Consume the existing internal proof of the same literal membership of
the chosen condition. Its conclusion is the actual pointwise guard. -/
theorem member_from_proof {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (Reln : Formula (k+2))
    (w z a A C f b L S K H p D head Q U Y i V G Member : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (ht : Derives Γ (SyntaxTermSyntax.term w z b p))
    (hl : Derives Γ (SyntaxCodedMixedBinderSyntax.lifted w L S a f z b A C K H))
    (hD : Derives Γ (consCode w p L D)) (hh : Derives Γ (SyntaxVariableSyntax.code true w z head))
    (hc : Derives Γ (ForcingGuardCode.compiled false Reln w A f head Q))
    (hU : Derives Γ (substituted w K H A f C b Q U))
    (hY : Derives Γ (instantiated w z b C p U Y))
    (hi : Derives Γ (SyntaxNumeralSyntax.numeral k i)) (hV : Derives Γ (field w S i V))
    (hm : Derives Γ (ForcingMemberGuardOpening.result w p V Member))
    (hp : Derives Γ (implication test w z b G Member)) :
    Derives Γ (implication test w z b G Y) := by
  apply with_guard_query hZ false Reln w z a A C f b L S K H p D head Q U Y hw hz ht hl hD hc hU hY
    (implication test w z b G Y)
  intro l Δ ρ hZ1 lift _ hField hSame
  have hw1 := of_eq (omega_rename _ _) (lift hw)
  have hActual := ForcingRawModalBody.member_query hZ1 Reln (ρ w) (ρ z) (ρ D) (ρ S) (ρ A) (ρ f)
    (ρ b) (ρ head) (ρ p) (ρ i) (ρ V) (ρ Q) (ρ Y) hw1 (of_eq (empty_rename _ _) (lift hz))
    (of_eq (SyntaxVariableSyntax.code_rename true _ _ _ _) (lift hh)) hField
    (of_eq (SyntaxNumeralSyntax.numeral_rename _ _ _) (lift hi)) (of_eq (field_rename _ _ _ _ _) (lift hV))
    (of_eq (ForcingGuardCode.compiled_rename false Reln _ _ _ _ _ _) (lift hc)) hSame
  have he := ForcingPreorderMember.same_result hZ1 (ρ w) (ρ p) (ρ V) (ρ Member) (ρ Y) hw1
    (of_eq (ForcingMemberGuardOpening.result_rename _ _ _ _ _) (lift hm)) hActual
  have hp1 := of_eq (implication_rename _ _ _ _ _ _ _) (lift hp)
  let P := implication test (ρ w).castSucc (ρ z).castSucc (ρ b).castSucc (ρ G).castSucc (Fin.last l)
  apply of_eq (implication_rename test w z b G Y ρ).symm
  exact of_eq (by simp only [P, Formula.instantiate, implication_rename,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
    (.eqSubst P he (of_eq (by simp only [P, Formula.instantiate, implication_rename,
      Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hp1))

end PPAC.Migration.ForcingDensityGuards
