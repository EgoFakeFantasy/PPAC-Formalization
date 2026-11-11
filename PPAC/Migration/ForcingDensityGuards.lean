import PPAC.Migration.ForcingDensityInstantiation
import PPAC.Migration.ForcingAtomicMono

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

private theorem with_direct_query {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z a A C f b L S K H p D Q U Y : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (ht : Derives Γ (SyntaxTermSyntax.term w z b p))
    (hl : Derives Γ (SyntaxCodedMixedBinderSyntax.lifted w L S a f z b A C K H))
    (hD : Derives Γ (consCode w p L D))
    (hType : Derives Γ (FormulaCodeSyntax.formulaCode w Q A f))
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
  apply with_direct_query hZ w z a A C f b L S K H p D Q U Y hw hz ht hl hD
    (ForcingGuardCode.compiled_type order Reln w A f head Q hc) hU hY out
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


private theorem member_at_instance {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (Reln : Formula (k+2))
    (w z a A C f b L S K H p D head Q U Y i V : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (ht : Derives Γ (SyntaxTermSyntax.term w z b p))
    (hl : Derives Γ (SyntaxCodedMixedBinderSyntax.lifted w L S a f z b A C K H))
    (hD : Derives Γ (consCode w p L D)) (hh : Derives Γ (SyntaxVariableSyntax.code true w z head))
    (hc : Derives Γ (ForcingGuardCode.compiled false Reln w A f head Q))
    (hU : Derives Γ (substituted w K H A f C b Q U))
    (hY : Derives Γ (instantiated w z b C p U Y))
    (hi : Derives Γ (SyntaxNumeralSyntax.numeral k i)) (hV : Derives Γ (field w S i V)) :
    Derives Γ (ForcingMemberGuardOpening.result w p V Y) := by
  apply with_direct_query hZ w z a A C f b L S K H p D Q U Y hw hz ht hl hD
    (ForcingGuardCode.compiled_type false Reln w A f head Q hc) hU hY
    (ForcingMemberGuardOpening.result w p V Y)
  intro l Δ ρ hZ1 lift _ hField hSame
  have hw1 := of_eq (omega_rename _ _) (lift hw)
  have hActual := ForcingRawModalBody.member_query hZ1 Reln (ρ w) (ρ z) (ρ D) (ρ S) (ρ A) (ρ f)
    (ρ b) (ρ head) (ρ p) (ρ i) (ρ V) (ρ Q) (ρ Y) hw1 (of_eq (empty_rename _ _) (lift hz))
    (of_eq (SyntaxVariableSyntax.code_rename true _ _ _ _) (lift hh)) hField
    (of_eq (SyntaxNumeralSyntax.numeral_rename _ _ _) (lift hi)) (of_eq (field_rename _ _ _ _ _) (lift hV))
    (of_eq (ForcingGuardCode.compiled_rename false Reln _ _ _ _ _ _) (lift hc)) hSame
  exact of_eq (ForcingMemberGuardOpening.result_rename w p V Y ρ).symm hActual

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
  have hActual := member_at_instance hZ Reln w z a A C f b L S K H p D head Q U Y i V
    hw hz ht hl hD hh hc hU hY hi hV
  have he := ForcingPreorderMember.same_result hZ w p V Member Y hw hm hActual
  let P := implication test w.castSucc z.castSucc b.castSucc G.castSucc (Fin.last m)
  exact of_eq (by simp only [P, Formula.instantiate, implication_rename,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
    (.eqSubst P he (of_eq (by simp only [P, Formula.instantiate, implication_rename,
      Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hp))

/-- Open the density premise at the current row condition q. Project the
original preorder and q-membership from its canonical background. Transfer
the membership to the exact compiled guard and use the actual guarded
reflexivity instance to discharge the order guard. -/
theorem tail_from_row {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (Reln : Formula (k+2))
    (w z a A C f b L Base S K Bnd D head Q Um Ym Yo Tail I j V Extra A1 A2 A3 Cr Bd Refl Pre
      Dm Do FRefl : Fin m)
    (raw : Fin 16 → Fin m) (Gb : Fin 5 → Fin m) (H layout : Fin 6 → Fin m)
    (U F P : Fin 3 → Fin m) (N : Fin 5 → Fin m) (Ds : Fin 3 → Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (ht : Derives Γ (SyntaxTermSyntax.term w z b (P 1)))
    (hl : Derives Γ (SyntaxCodedMixedBinderSyntax.lifted w L S a f z b A C K Bnd))
    (hD : Derives Γ (consCode w (P 1) L D)) (hh : Derives Γ (SyntaxVariableSyntax.code true w z head))
    (hc : Derives Γ (ForcingGuardCode.compiled false Reln w A f head Q))
    (hUm : Derives Γ (substituted w K Bnd A f C b Q Um))
    (hYm : Derives Γ (instantiated w z b C (P 1) Um Ym))
    (hI : Derives Γ (SyntaxNumeralSyntax.numeral k I))
    (hf : Derives Γ (SyntaxNumeralSyntax.numeral (k+2) f))
    (hj : Derives Γ (SyntaxNumeralSyntax.numeral (k+1) j))
    (hReplace : Derives Γ (ForcingReflexiveImages.replacement w f z b Base j (P 1) S))
    (hV : Derives Γ (field w Base I V))
    (hA1 : Derives Γ (SyntaxNumeralSyntax.numeral 1 A1))
    (hA2 : Derives Γ (SyntaxNumeralSyntax.numeral 2 A2))
    (hRow : Derives Γ (ForcingPreorderLeaves.data test Reln w z A1 A2 A3 f b Cr Bd Base Refl Pre raw Gb H U F P N Ds))
    (hExtra : Derives Γ (formulaCode w Extra z b))
    (hLayout : Derives Γ (ForcingProofContext.layoutData w z b Extra Pre H layout))
    (hAll : Derives Γ (SyntaxLogicalSyntax.singleCode 9 w FRefl Refl))
    (hBody : Derives Γ (binaryCode 2 w Dm Do FRefl))
    (hiM : Derives Γ (instantiated w z b Cr (P 1) Dm Ym))
    (hiO : Derives Γ (instantiated w z b Cr (P 1) Do Yo))
    (hTail : Derives Γ (discharge w z b (layout 3) Ym Yo Tail)) :
    Derives Γ (implication test w z b (layout 3) Tail) := by
  have projected := ForcingAtomicMono.layout_proofs hZ w z b Extra Pre H layout hw hz hExtra hLayout
  have hMember : Derives Γ (ForcingMemberGuardOpening.result w (P 1) V (H 1)) :=
    ForcingPreorderMember.raw_from_data hZ test Reln 1 w z A1 A2 A3 f b Cr Bd Base Refl Pre I V
      raw Gb H U F P N Ds hw hz hA1 hA2 hI hRow hV
  have hCarrier := ForcingPreorderGuardTables.carrier_field hZ w f z b Base j (P 1) S I V hf hj hI hReplace hV
  have pMem := member_from_proof hZ Reln w z a A C f b L S K Bnd (P 1) D head Q Um Ym I V
    (layout 3) (H 1) hw hz ht hl hD hh hc hUm hYm hI hCarrier hMember (.conjL (.conjR projected))
  have hRowCore := Derives.conjL (.conjL (.conjR hRow))
  have hAnd : Derives Γ (binaryCode 0 w Refl (U 0) Pre) := .conjL (.conjR hRowCore)
  have l2 := Derives.conjL (.conjR (.conjR hLayout))
  have l3 := Derives.conjL (.conjR (.conjR (.conjR hLayout)))
  have hG := Derives.conjR l3
  have hPre := Derives.conjL (.conjR (.impE
    (.conjL (FormulaCodeKnownLogical.binary0_iff hZ w z b Pre (layout 1) (layout 2) hw (.conjL l2)))
    (.conjR l2)))
  have tRefl := Derives.conjR (.impE
    (.conjL (FormulaCodeKnownLogical.binary0_iff hZ w z b Refl (U 0) Pre hw hAnd)) hPre)
  have hRefl := Derives.conjL tRefl
  have hU := Derives.conjR tRefl
  have pPreRefl := ForcingRelationGuardProof.project hZ test false w z b Refl (U 0) Pre
    hw hz hRefl hU hPre hAnd
  have pRefl := ForcingRelationGuardProof.chain hZ test w z b (layout 3) Pre Refl
    hw hz hG hPre hRefl (.conjL projected) pPreRefl
  let p := P 1
  have tDm := SyntaxTopFormulaTyping.instantiate_source_type hZ w z b Cr p Dm Ym hw hiM
  have tDo := SyntaxTopFormulaTyping.instantiate_source_type hZ w z b Cr p Do Yo hw hiO
  have tBody := Derives.impE (.conjR (FormulaCodeKnownLogical.binary2_iff hZ w Cr b Dm Do FRefl hw hBody))
    (.conjI (.conjR (FormulaCodeProperties.guards w Dm Cr b tDm)) (.conjI tDm tDo))
  have tm := SyntaxTopFormulaTyping.instantiate_target_type w z b Cr p Dm Ym hiM
  have to := SyntaxTopFormulaTyping.instantiate_target_type w z b Cr p Do Yo hiO
  have tInstance := FormulaCodeConstructors.binary2 hZ w z b Ym Yo hw
    (.conjI (.conjR (FormulaCodeProperties.guards w Ym z b tm)) (.conjI tm to))
  let out := implication test w z b (layout 3) Tail
  refine eliminate_objects hZ 1 (fun r v =>
    (Formula.mem (v 0) (r w)).conj
      (FormulaCodeConstructSyntax.typedAt 2 7 (r w) (SyntaxAtomSyntax.two (r Ym) (r Yo)) (v 0) (r z) (r b))) ?_ out ?_
  · exact FormulaCodeConstruct.exists_of_fiber 2 7 w (SyntaxAtomSyntax.two Ym Yo) z b tInstance
  intro l Δ r v hZ1 lift hWitness
  have hInst := Derives.conjR hWitness
  have hw1 := of_eq (omega_rename _ _) (lift hw)
  have hz1 := of_eq (empty_rename _ _) (lift hz)
  have hiM1 := of_eq (instantiated_rename _ _ _ _ _ _ _ _) (lift hiM)
  have hiO1 := of_eq (instantiated_rename _ _ _ _ _ _ _ _) (lift hiO)
  have hAll1 := of_eq (SyntaxLogicalSyntax.singleCode_rename _ _ _ _ _) (lift hAll)
  have hBody1 := of_eq (SyntaxLogicalSyntax.binaryCode_rename _ _ _ _ _ _) (lift hBody)
  have hCtor : Derives Δ (binaryCode 2 (r w) (r Ym) (r Yo) (v 0)) := .conjL hInst
  have hAt := Derives.impE (.conjR (SyntaxTopFormulaLogicalEndpoints.instantiate_binary_iff hZ1 2
    (r w) (r z) (r b) (r Cr) (r p) (r FRefl) (v 0) (r Dm) (r Do) (r Ym) (r Yo) hw1
    (.conjI (SyntaxTopFormulaTyping.instantiate_environment (r w) (r z) (r b) (r Cr) (r p) (r Dm) (r Ym) hiM1)
      (of_eq (FormulaCodeSyntax.formulaCode_rename _ _ _ _ _) (lift tBody))) hBody1 hCtor))
    (.conjI hiM1 hiO1)
  have hG1 := of_eq (FormulaCodeSyntax.formulaCode_rename _ _ _ _ _) (lift hG)
  have pAt := ForcingRelationGuardProof.instantiate hZ1 test (r w) (r z) (r b) (r Cr) (r FRefl) (r p)
    (v 0) (r Refl) (r (layout 3)) hw1 hz1 hG1 (.conjR hInst) hAt hAll1
    (of_eq (implication_rename _ _ _ _ _ _ _) (lift pRefl))
  have pMem1 := of_eq (implication_rename _ _ _ _ _ _ _) (lift pMem)
  have pOrder := ForcingNegMemberProof.discharge hZ1 test (r w) (r z) (r b) (r (layout 3)) (r Ym) (r Yo)
    (v 0) hw1 hz1 hG1 (.conjR hInst) hCtor pMem1 pAt
  have hTail1 := of_eq (discharge_rename _ _ _ _ _ _ _ r) (lift hTail)
  exact of_eq (implication_rename _ _ _ _ _ _ _).symm (.impE (.impE hTail1 pMem1) pOrder)

private theorem with_tree_quote {m} {Γ : Context m}
    (hZ : ZFContext.Evidence Γ) (tree : PureSyntaxQuotation.Original.Tree) (w : Fin m)
    (hw : Derives Γ (omega w)) (out : Formula m)
    (use : ∀ {l} {Δ : Context l} (r : Fin m → Fin l), ZFContext.Evidence Δ →
      (∀ {p : Formula m}, Derives Γ p → Derives Δ (p.rename r)) →
      ∀ x : Fin l, Derives Δ (OriginalTreeQuotationSyntax.tree tree (r w) x) →
      Derives Δ (out.rename r)) : Derives Γ out := by
  refine eliminate_objects hZ 1 (fun r v =>
    (Formula.mem (v 0) (r w)).conj (OriginalTreeQuotationSyntax.tree tree (r w) (v 0))) ?_ out ?_
  · exact OriginalTreeQuotationExistence.tree_exists hZ tree w hw
  intro l Δ r v hZ1 lift hx
  exact use r hZ1 lift (v 0) (.conjR hx)

private theorem reflexive_member_at_query {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (Reln : Formula (k+2)) (w z A f b D Base p head M Im i V : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hh : Derives Γ (SyntaxVariableSyntax.code true w z head))
    (hi : Derives Γ (SyntaxNumeralSyntax.numeral k i))
    (hField : Derives Γ (field w D z p)) (hV : Derives Γ (field w Base i V))
    (hM : Derives Γ (PureQuotationSyntax.formula (ForcingPreorderCode.reflexiveLeaf Reln false) w M))
    (hQuery : Derives Γ (substituted w D Base A f z b M Im)) :
    Derives Γ (ForcingMemberGuardOpening.result w p V Im) := by
  let zero := PureSyntaxQuotation.Original.leaf 0
  let bound := YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree.node 0 [zero]
  let carrier := YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree.node 1 [PureSyntaxQuotation.Original.leaf k]
  let out := ForcingMemberGuardOpening.result w p V Im
  refine with_tree_quote hZ zero w hw out ?_
  intro l Δ r hZ1 lift sym hSym
  have hw1 := of_eq (omega_rename w r) (lift hw)
  refine with_tree_quote hZ1 carrier (r w) hw1 (out.rename r) ?_
  intro l' Δ' s hZ2 lift2 var hVar
  let ρ := s ∘ r
  have carry {P : Formula m} (h : Derives Γ P) :=
    of_eq (SourceAlgebra.rename_comp P r s) (lift2 (lift h))
  have hw2 := of_eq (omega_rename w ρ) (carry hw)
  have hz2 := of_eq (empty_rename z ρ) (carry hz)
  have hh2 := of_eq (SyntaxVariableSyntax.code_rename true w z head ρ) (carry hh)
  have hi2 := of_eq (SyntaxNumeralSyntax.numeral_rename k i ρ) (carry hi)
  have hSym2 := of_eq (OriginalTreeQuotationSyntax.tree_rename zero (r w) sym s) (lift2 hSym)
  have hHead := OriginalQuotationVariableFields.tree_of_variable true 0 (ρ w) (ρ z) (ρ head) hz2 hh2
  have hRaw := of_eq (PureQuotationSyntax.formula_rename _ w M ρ) (carry hM)
  have hTree : Derives Δ' (OriginalTreeQuotationSyntax.tree
      (YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree.node 2 [zero, bound, carrier]) (ρ w) (ρ M)) :=
    of_eq (congrArg (fun tree => OriginalTreeQuotationSyntax.tree tree (ρ w) (ρ M))
      (ForcingPreorderCode.reflexive_member_tree Reln)) hRaw
  have hCode := OriginalQuotationNodeFields.tree_to_constructor hZ2 2 [zero, bound, carrier]
    (ρ w) (ρ M) (SyntaxAtomSyntax.three (s sym) (ρ head) var) hw2
    (.conjI hSym2 (.conjI hHead (.conjI hVar (.eqRefl (ρ w))))) hTree
  have hData : Derives Δ' (ForcingMemberGuard.data (ρ w) (ρ head) (ρ M) (ρ i) (s sym) var) :=
    .conjI (OriginalQuotationNodeFields.tree_to_constructor hZ2 0 [] (ρ w) (s sym) Fin.elim0 hw2
      (.eqRefl (ρ w)) hSym2)
      (.conjI (OriginalQuotationVariableFields.variable_of_tree hZ2 false k (ρ w) (ρ i) var hw2 hi2 hVar) hCode)
  have result := ForcingRawModalBody.member_atom hZ2 (ρ w) (ρ z) (ρ D) (ρ Base) (ρ A) (ρ f)
    (ρ b) (ρ head) (ρ p) (ρ i) (ρ V) (ρ M) (ρ Im) (s sym) var hw2 hz2 hh2
    (of_eq (field_rename w D z p ρ) (carry hField)) (SyntaxNumerals.range hZ2 k (ρ w) (ρ i) hw2 hi2)
    (of_eq (field_rename w Base i V ρ) (carry hV)) hData
    (of_eq (substituted_rename w D Base A f z b M Im ρ) (carry hQuery))
  simpa only [out, ρ, SourceAlgebra.rename_comp, Function.comp_def, ForcingMemberGuardOpening.result_rename] using result

private theorem reflexive_member_at_instance {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (Reln : Formula (k+2)) (w z A C f b B Base K H p head M Dm Im i V : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hp : Derives Γ (SyntaxTermSyntax.term w z b p))
    (hl : Derives Γ (SyntaxCodedMixedBinderSyntax.lifted w B Base z f z b A C K H))
    (hh : Derives Γ (SyntaxVariableSyntax.code true w z head))
    (hi : Derives Γ (SyntaxNumeralSyntax.numeral k i)) (hV : Derives Γ (field w Base i V))
    (hM : Derives Γ (PureQuotationSyntax.formula (ForcingPreorderCode.reflexiveLeaf Reln false) w M))
    (hBody : Derives Γ (substituted w K H A f C b M Dm))
    (hInst : Derives Γ (instantiated w z b C p Dm Im)) :
    Derives Γ (ForcingMemberGuardOpening.result w p V Im) := by
  have hin := SyntaxCodedMixedBinderTyping.input_of_lifted w B Base z f z b A C K H hl
  have hB := Derives.conjL (.conjL (.conjR (.conjR (.conjL (.conjL hin)))))
  let out := ForcingMemberGuardOpening.result w p V Im
  refine eliminate_objects hZ 1 (fun r x =>
    (Formula.mem (x 0) (r w)).conj (consCode (r w) (r p) (r B) (x 0))) ?_ out ?_
  · exact StructuralConsCore.exists_cons hZ w p B hw (SyntaxTerms.range hZ w z b p hw hp) hB
  intro l Δ r x hZ1 lift hD
  have hw1 := of_eq (omega_rename w r) (lift hw)
  have hz1 := of_eq (empty_rename z r) (lift hz)
  have hBody1 := of_eq (substituted_rename w K H A f C b M Dm r) (lift hBody)
  have hType := SyntaxMixedFormulaJudgmentTyping.source_type hZ1 (r w) (r K) (r H) (r A)
    (r f) (r C) (r b) (r M) (r Dm) hw1 hBody1
  refine with_direct_query hZ1 (r w) (r z) (r z) (r A) (r C) (r f) (r b) (r B) (r Base)
    (r K) (r H) (r p) (x 0) (r M) (r Dm) (r Im) hw1 hz1
    (of_eq (SyntaxTermSyntax.term_rename _ _ _ _ r) (lift hp))
    (of_eq (SyntaxCodedMixedBinderSyntax.lifted_rename _ _ _ _ _ _ _ _ _ _ _ r) (lift hl))
    (.conjR hD) hType hBody1 (of_eq (instantiated_rename _ _ _ _ _ _ _ r) (lift hInst)) _ ?_
  intro l' Δ' s hZ2 lift2 _ hField hQuery
  let ρ := s ∘ r
  have carry {P : Formula m} (h : Derives Γ P) :=
    of_eq (SourceAlgebra.rename_comp P r s) (lift2 (lift h))
  have result := reflexive_member_at_query hZ2 Reln (ρ w) (ρ z) (ρ A) (ρ f) (ρ b) (s (x 0))
    (ρ Base) (ρ p) (ρ head) (ρ M) (ρ Im) (ρ i) (ρ V)
    (of_eq (omega_rename w ρ) (carry hw)) (of_eq (empty_rename z ρ) (carry hz))
    (of_eq (SyntaxVariableSyntax.code_rename true w z head ρ) (carry hh))
    (of_eq (SyntaxNumeralSyntax.numeral_rename k i ρ) (carry hi)) hField
    (of_eq (field_rename w Base i V ρ) (carry hV))
    (of_eq (PureQuotationSyntax.formula_rename _ w M ρ) (carry hM)) hQuery
  simpa only [out, ρ, SourceAlgebra.rename_comp, Function.comp_def, ForcingMemberGuardOpening.result_rename] using result

/-- The native reflexivity member instance and the actual pointwise density
member guard are the same literal formula. The table update preserves the
carrier and the two atom queries use the same selected condition. -/
theorem reflexive_member_agrees {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (Reln : Formula (k+2)) (w z a A C f b L Base S K H p D head Q U Ym Ar Cr B Kr Hr M Dm Im i j V : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hp : Derives Γ (SyntaxTermSyntax.term w z b p))
    (hh : Derives Γ (SyntaxVariableSyntax.code true w z head))
    (hf : Derives Γ (SyntaxNumeralSyntax.numeral (k+2) f))
    (hi : Derives Γ (SyntaxNumeralSyntax.numeral k i))
    (hj : Derives Γ (SyntaxNumeralSyntax.numeral (k+1) j))
    (hV : Derives Γ (field w Base i V))
    (hReplace : Derives Γ (ForcingReflexiveImages.replacement w f z b Base j p S))
    (hl : Derives Γ (SyntaxCodedMixedBinderSyntax.lifted w L S a f z b A C K H))
    (hD : Derives Γ (consCode w p L D))
    (hc : Derives Γ (ForcingGuardCode.compiled false Reln w A f head Q))
    (hU : Derives Γ (substituted w K H A f C b Q U))
    (hYm : Derives Γ (instantiated w z b C p U Ym))
    (hlr : Derives Γ (SyntaxCodedMixedBinderSyntax.lifted w B Base z f z b Ar Cr Kr Hr))
    (hM : Derives Γ (PureQuotationSyntax.formula (ForcingPreorderCode.reflexiveLeaf Reln false) w M))
    (hDm : Derives Γ (substituted w Kr Hr Ar f Cr b M Dm))
    (hIm : Derives Γ (instantiated w z b Cr p Dm Im)) : Derives Γ (.equal Im Ym) := by
  have hV' := ForcingPreorderGuardTables.carrier_field hZ w f z b Base j p S i V hf hj hi hReplace hV
  have hLeft := reflexive_member_at_instance hZ Reln w z Ar Cr f b B Base Kr Hr p head M Dm Im i V
    hw hz hp hlr hh hi hV hM hDm hIm
  have hRight := member_at_instance hZ Reln w z a A C f b L S K H p D head Q U Ym i V
    hw hz hp hl hD hh hc hU hYm hi hV'
  exact ForcingPreorderMember.same_result hZ w p V Im Ym hw hLeft hRight

private theorem with_reflexive_outputs {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z f b B Base Raw Refl X M O : Fin m)
    (hw : Derives Γ (omega w))
    (hRun : Derives Γ (substituted w B Base z f z b Raw Refl))
    (hAll : Derives Γ (SyntaxLogicalSyntax.singleCode 9 w X Raw))
    (hImp : Derives Γ (binaryCode 2 w M O X)) (out : Formula m)
    (use : ∀ {l} {Δ : Context l} (r : Fin m → Fin l), ZFContext.Evidence Δ →
      (∀ {p : Formula m}, Derives Γ p → Derives Δ (p.rename r)) →
      ∀ A C K H F Dm Do : Fin l,
      Derives Δ (SyntaxCodedMixedBinderSyntax.lifted (r w) (r B) (r Base) (r z) (r f) (r z) (r b) A C K H) →
      Derives Δ (SyntaxLogicalSyntax.singleCode 9 (r w) F (r Refl)) →
      Derives Δ (ForcingFormulaDiagram.binaryData 2 (r w) K H A (r f) C (r b) (r M) (r O) F Dm Do) →
      Derives Δ (out.rename r)) : Derives Γ out := by
  have output := ForcingMixedUnary.single_output hZ 9 true (.inr (.inl ⟨rfl, rfl⟩))
    w B Base z f z b Raw X Refl hw hAll hRun
  refine eliminate_objects hZ 1 (fun r v =>
    (SyntaxLogicalSyntax.singleCode 9 (r w) (v 0) (r Refl)).conj
      (SyntaxMixedFormulaRecursiveSyntax.advanced (r w) (r X) (r B) (r Base) (r z) (r f) (r z) (r b) (v 0)))
    output out ?_
  intro l Δ r v hZ1 lift hOutput
  refine eliminate_objects hZ1 4 (fun s u =>
    (SyntaxCodedMixedBinderSyntax.lifted (s (r w)) (s (r B)) (s (r Base)) (s (r z)) (s (r f))
      (s (r z)) (s (r b)) (u 0) (u 1) (u 2) (u 3)).conj
    (substituted (s (r w)) (u 2) (u 3) (u 0) (s (r f)) (u 1) (s (r b)) (s (r X)) (s (v 0))))
    (.conjR hOutput) (out.rename r) ?_
  intro l' Δ' s u hZ2 lift2 hBody
  let ρ := s ∘ r
  have hw2 := of_eq (omega_rename w ρ) (of_eq (SourceAlgebra.rename_comp _ r s) (lift2 (lift hw)))
  have hImp2 := of_eq (SyntaxLogicalSyntax.binaryCode_rename 2 w M O X ρ)
    (of_eq (SourceAlgebra.rename_comp _ r s) (lift2 (lift hImp)))
  have hAll2 := of_eq (SyntaxLogicalSyntax.singleCode_rename 9 (r w) (v 0) (r Refl) s)
    (lift2 (.conjL hOutput))
  have children := ForcingFormulaDiagram.binary_output hZ2 2 (ρ w) (u 2) (u 3) (u 0) (ρ f)
    (u 1) (ρ b) (ρ X) (ρ M) (ρ O) (s (v 0)) hw2 hImp2 (.conjR hBody)
  refine eliminate_objects hZ2 2 (fun t y =>
    ForcingFormulaDiagram.binaryData 2 (t (ρ w)) (t (u 2)) (t (u 3)) (t (u 0)) (t (ρ f))
      (t (u 1)) (t (ρ b)) (t (ρ M)) (t (ρ O)) (t (s (v 0))) (y 0) (y 1))
    children ((out.rename r).rename s) ?_
  intro l'' Δ'' t y hZ3 lift3 hChildren
  have carry {p : Formula m} (hp : Derives Γ p) : Derives Δ'' (p.rename (t ∘ ρ)) :=
    of_eq (SourceAlgebra.rename_comp p ρ t) (lift3 (of_eq (SourceAlgebra.rename_comp p r s) (lift2 (lift hp))))
  have hLift := of_eq (SyntaxCodedMixedBinderSyntax.lifted_rename _ _ _ _ _ _ _ _ _ _ _ t)
    (lift3 (.conjL hBody))
  have hAll3 := of_eq (SyntaxLogicalSyntax.singleCode_rename _ _ _ _ t) (lift3 hAll2)
  have result := use (t ∘ ρ) hZ3 carry (t (u 0)) (t (u 1)) (t (u 2)) (t (u 3)) (t (s (v 0)))
    (y 0) (y 1) hLift hAll3 hChildren
  simpa only [ρ, SourceAlgebra.rename_comp, Function.comp_def] using result

/-- Read the actual compiled reflexive universal and its two implication
children, then instantiate both at the selected row condition. The queries use
the original base table and the same lifted
tables of the recorded substitution. -/
theorem with_reflexive_instances {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (Reln : Formula (k+2)) (w z A1 A2 A3 f b B Base Cr Pre Refl U0 : Fin m)
    (raw : Fin 16 → Fin m) (P : Fin 3 → Fin m) (hw : Derives Γ (omega w))
    (hRaw : Derives Γ (ForcingPreorderCode.rawData Reln w z A1 A2 A3 f raw))
    (hTarget : Derives Γ (ForcingPreorderInstances.targetData test w z f b Cr B Base
      (raw 0) (raw 1) (raw 2) P Pre Refl U0))
    (hp : Derives Γ (SyntaxTermSyntax.term w z b (P 1))) (out : Formula m)
    (use : ∀ {l} {Δ : Context l} (r : Fin m → Fin l), ZFContext.Evidence Δ →
      (∀ {p : Formula m}, Derives Γ p → Derives Δ (p.rename r)) →
      ∀ M O A C K H F Dm Do Im Io : Fin l,
      Derives Δ (PureQuotationSyntax.formula (ForcingPreorderCode.reflexiveLeaf Reln false) (r w) M) →
      Derives Δ (PureQuotationSyntax.formula (ForcingPreorderCode.reflexiveLeaf Reln true) (r w) O) →
      Derives Δ (SyntaxCodedMixedBinderSyntax.lifted (r w) (r B) (r Base) (r z) (r f) (r z) (r b) A C K H) →
      Derives Δ (SyntaxLogicalSyntax.singleCode 9 (r w) F (r Refl)) →
      Derives Δ (ForcingFormulaDiagram.binaryData 2 (r w) K H A (r f) C (r b) M O F Dm Do) →
      Derives Δ (instantiated (r w) (r z) (r b) C (r (P 1)) Dm Im) →
      Derives Δ (instantiated (r w) (r z) (r b) C (r (P 1)) Do Io) →
      Derives Δ (out.rename r)) : Derives Γ out := by
  let Raw := raw 1
  have hQuote : Derives Γ (PureQuotationSyntax.formula (ForcingPreorderCode.reflexive Reln) w Raw) :=
    .conjL (.conjL (.conjR hRaw))
  have hRun : Derives Γ (substituted w B Base z f z b Raw Refl) :=
    .conjL (.conjR (.conjR (.conjR hTarget)))
  let body := ForcingPreorderCode.reflexiveBody Reln
  let member := ForcingPreorderCode.reflexiveLeaf Reln false
  let order := ForcingPreorderCode.reflexiveLeaf Reln true
  refine with_tree_quote hZ (PureSyntaxQuotation.formulaTree body) w hw out ?_
  intro l Δ r hZ1 lift X hX
  have hw1 := of_eq (omega_rename w r) (lift hw)
  refine with_tree_quote hZ1 (PureSyntaxQuotation.formulaTree member) (r w) hw1 (out.rename r) ?_
  intro l' Δ' s hZ2 lift2 M hM
  have hw2 := of_eq (omega_rename (r w) s) (lift2 hw1)
  refine with_tree_quote hZ2 (PureSyntaxQuotation.formulaTree order) (s (r w)) hw2 ((out.rename r).rename s) ?_
  intro l'' Δ'' t hZ3 lift3 O hO
  let ρ := t ∘ s ∘ r
  have carry {p : Formula m} (hp : Derives Γ p) : Derives Δ'' (p.rename ρ) := by
    simpa only [ρ, SourceAlgebra.rename_comp, Function.comp_def] using lift3 (lift2 (lift hp))
  have hw3 := of_eq (omega_rename w ρ) (carry hw)
  have hQuote3 := of_eq (PureQuotationSyntax.formula_rename _ _ _ ρ) (carry hQuote)
  have hRun3 := of_eq (substituted_rename w B Base z f z b Raw Refl ρ) (carry hRun)
  have hX3 := of_eq (PureQuotationSyntax.formula_rename _ _ _ (t ∘ s))
    (of_eq (SourceAlgebra.rename_comp _ s t) (lift3 (lift2 hX)))
  have hM3 := of_eq (PureQuotationSyntax.formula_rename _ _ _ t) (lift3 hM)
  have shape := ForcingPreorderCode.reflexive_fields hZ3 Reln (ρ w) (ρ Raw) (t (s X)) (t M) O
    hw3 hQuote3 hX3 hM3 hO
  refine with_reflexive_outputs hZ3 (ρ w) (ρ z) (ρ f) (ρ b) (ρ B) (ρ Base) (ρ Raw) (ρ Refl)
    (t (s X)) (t M) O hw3 hRun3 (.conjL shape) (.conjR shape) _ ?_
  intro l''' Δ''' u hZ4 lift4 A C K H F Dm Do hLift hAll hChildren
  have hM4 := of_eq (PureQuotationSyntax.formula_rename _ _ _ u) (lift4 hM3)
  have hO4 := of_eq (PureQuotationSyntax.formula_rename _ _ _ u) (lift4 hO)
  have carry4 {p : Formula m} (hp : Derives Γ p) :=
    of_eq (SourceAlgebra.rename_comp p ρ u) (lift4 (carry hp))
  let σ := u ∘ ρ
  have hw4 := of_eq (omega_rename w σ) (carry4 hw)
  have hp4 := of_eq (SyntaxTermSyntax.term_rename w z b (P 1) σ) (carry4 hp)
  have hC := Derives.conjR (.conjR
    (SyntaxCodedMixedBinderTyping.input_of_lifted (σ w) (σ B) (σ Base) (σ z) (σ f) (σ z) (σ b)
      A C K H hLift))
  have hEnv := Derives.conjI hp4 hC
  have htM := SyntaxMixedFormulaJudgment.target_type (σ w) K H A (σ f) C (σ b) (u (t M)) Dm
    (.conjL (.conjR hChildren))
  have htO := SyntaxMixedFormulaJudgment.target_type (σ w) K H A (σ f) C (σ b) (u O) Do
    (.conjR (.conjR hChildren))
  have instM := SyntaxTopFormulaExistence.instantiate_exists hZ4 (σ w) (σ z) (σ b) C (σ (P 1)) Dm
    hw4 (.conjI hEnv htM)
  refine eliminate_objects hZ4 1 (fun v x =>
    instantiated (v (σ w)) (v (σ z)) (v (σ b)) (v C) (v (σ (P 1))) (v Dm) (x 0))
    instM _ ?_
  intro l5 Δ5 v x hZ5 lift5 hIM
  have hw5 := of_eq (omega_rename _ v) (lift5 hw4)
  have hEnv5 := of_eq (SyntaxTopEnvironmentSyntax.instantiateInput_rename _ _ _ _ _ v) (lift5 hEnv)
  have htO5 := of_eq (FormulaCodeSyntax.formulaCode_rename _ _ _ _ v) (lift5 htO)
  have instO := SyntaxTopFormulaExistence.instantiate_exists hZ5 (v (σ w)) (v (σ z)) (v (σ b))
    (v C) (v (σ (P 1))) (v Do) hw5 (.conjI hEnv5 htO5)
  refine eliminate_objects hZ5 1 (fun d y =>
    instantiated (d (v (σ w))) (d (v (σ z))) (d (v (σ b))) (d (v C)) (d (v (σ (P 1)))) (d (v Do)) (y 0))
    instO _ ?_
  intro l6 Δ6 d y hZ6 lift6 hIO
  let τ := d ∘ v
  have carry6 {p : Formula m} (h : Derives Γ p) : Derives Δ6 (p.rename (τ ∘ σ)) := by
    simpa only [τ, σ, SourceAlgebra.rename_comp, Function.comp_def] using lift6 (lift5 (carry4 h))
  have take {p : Formula l'''} (h : Derives Δ''' p) : Derives Δ6 (p.rename τ) :=
    of_eq (SourceAlgebra.rename_comp p v d) (lift6 (lift5 h))
  have result := use (τ ∘ σ) hZ6 carry6 (τ (u (t M))) (τ (u O)) (τ A) (τ C) (τ K) (τ H)
    (τ F) (τ Dm) (τ Do) (d (x 0)) (y 0)
    (of_eq (PureQuotationSyntax.formula_rename _ _ _ τ) (take hM4))
    (of_eq (PureQuotationSyntax.formula_rename _ _ _ τ) (take hO4))
    (of_eq (SyntaxCodedMixedBinderSyntax.lifted_rename _ _ _ _ _ _ _ _ _ _ _ τ) (take hLift))
    (of_eq (SyntaxLogicalSyntax.singleCode_rename _ _ _ _ τ) (take hAll))
    (of_eq (ForcingFormulaDiagram.binaryData_rename 2 (σ w) K H A (σ f) C (σ b) (u (t M)) (u O) F Dm Do τ) (take hChildren))
    (of_eq (instantiated_rename _ _ _ _ _ _ _ d) (lift6 hIM)) hIO
  simpa only [τ, σ, ρ, SourceAlgebra.rename_comp, Function.comp_def] using result

end PPAC.Migration.ForcingDensityGuards
