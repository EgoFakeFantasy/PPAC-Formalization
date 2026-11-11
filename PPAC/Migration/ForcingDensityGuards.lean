import PPAC.Migration.ForcingDensityInstantiation
import PPAC.Migration.ForcingAtomicMono
import PPAC.Migration.ForcingFreshOpeningInverse
import PPAC.Migration.Internal.StructuralConsUnique

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


private theorem member_guard_at_singleton {k m} {Γ : Context m}
    (hZ : ZFContext.Evidence Γ) (Reln : Formula (k+2))
    (w z t f b D Base p M Y i V : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hi : Derives Γ (SyntaxNumeralSyntax.numeral k i)) (hV : Derives Γ (field w Base i V))
    (hForest : Derives Γ (SyntaxForestSyntax.forest 1 w (fun _ => p) D))
    (hQuote : Derives Γ (PureQuotationSyntax.formula (ForcingGuardCode.template false Reln) w M))
    (hQuery : Derives Γ (substituted w D Base t f z b M Y)) :
    Derives Γ (ForcingMemberGuardOpening.result w p V Y) := by
  let bound : PureSyntaxQuotation.Original.Tree := .node 0 [PureSyntaxQuotation.Original.leaf 0]
  let out := ForcingMemberGuardOpening.result w p V Y
  have hField := Derives.impE (.conjR (SyntaxForestFieldValues.field_at hZ 1 w (fun _ => p)
    D 0 z p hw hForest hz)) (.eqRefl p)
  have hRaw : Derives Γ (PureQuotationSyntax.formula (ForcingPreorderCode.reflexiveLeaf Reln false) w M) :=
    of_eq (congrArg (fun tree => OriginalTreeQuotationSyntax.tree tree w M)
      ((ForcingGuardCode.member_template_tree Reln).trans (ForcingPreorderCode.reflexive_member_tree Reln).symm)) hQuote
  refine with_tree_quote hZ bound w hw out ?_
  intro l Δ r hZ1 lift head hHead
  have hw1 := of_eq (omega_rename w r) (lift hw)
  have hz1 := of_eq (empty_rename z r) (lift hz)
  apply of_eq (ForcingMemberGuardOpening.result_rename w p V Y r).symm
  exact reflexive_member_at_query hZ1 Reln (r w) (r z) (r t) (r f) (r b) (r D) (r Base)
    (r p) head (r M) (r Y) (r i) (r V) hw1 hz1
    (OriginalQuotationVariableFields.variable_of_tree hZ1 true 0 (r w) (r z) head hw1 hz1 hHead)
    (of_eq (SyntaxNumeralSyntax.numeral_rename _ _ r) (lift hi))
    (of_eq (field_rename _ _ _ _ r) (lift hField)) (of_eq (field_rename _ _ _ _ r) (lift hV))
    (of_eq (PureQuotationSyntax.formula_rename _ _ _ r) (lift hRaw))
    (of_eq (substituted_rename _ _ _ _ _ _ _ _ _ r) (lift hQuery))

private theorem member_guard_result {k m} {Γ : Context m}
    (hZ : ZFContext.Evidence Γ) (Reln : Formula (k+2))
    (w z f b p Base A head M Y i V : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hi : Derives Γ (SyntaxNumeralSyntax.numeral k i)) (hV : Derives Γ (field w Base i V))
    (hGuard : Derives Γ (ForcingGuardOpening.result false Reln w z f b p Base A head M Y)) :
    Derives Γ (ForcingMemberGuardOpening.result w p V Y) := by
  let out := ForcingMemberGuardOpening.result w p V Y
  refine eliminate_objects hZ 4 (fun r u => ForcingGuardOpening.data false Reln
    (r w) (r z) (r f) (r b) (r p) (r Base) (r A) (r head) (r M) (r Y) u) hGuard out ?_
  intro l Δ r u hZ1 lift hData
  refine eliminate_objects hZ1 1 (fun s v =>
    (SyntaxForestSyntax.forest 1 (s (r w)) (fun _ => s (r p)) (v 0)).conj
      (substituted (s (r w)) (v 0) (s (r Base)) (s (u 0)) (s (r f)) (s (r z)) (s (r b))
        (s (u 1)) (s (r Y)))) (.conjR hData) (out.rename r) ?_
  intro l' Ξ s v hZ2 move hBody
  let ρ := s ∘ r
  have carry {F : Formula m} (h : Derives Γ F) : Derives Ξ (F.rename ρ) :=
    of_eq (SourceAlgebra.rename_comp F r s) (move (lift h))
  have hQuote := Derives.conjL (.conjL (.conjR (.conjL hData)))
  have hResult := member_guard_at_singleton hZ2 Reln (ρ w) (ρ z) (s (u 0)) (ρ f) (ρ b) (v 0)
    (ρ Base) (ρ p) (s (u 1)) (ρ Y) (ρ i) (ρ V)
    (of_eq (omega_rename w ρ) (carry hw)) (of_eq (empty_rename z ρ) (carry hz))
    (of_eq (SyntaxNumeralSyntax.numeral_rename _ i ρ) (carry hi))
    (of_eq (field_rename _ _ _ _ ρ) (carry hV)) (.conjL hBody)
    (of_eq (PureQuotationSyntax.formula_rename _ _ _ s) (move hQuote)) (.conjR hBody)
  simpa only [out, ρ, SourceAlgebra.rename_comp, Function.comp_def, ForcingMemberGuardOpening.result_rename] using hResult

private theorem witness_member_from_carrier {k m} {Γ : Context m}
    (hZ : ZFContext.Evidence Γ) (Reln : Formula (k+2)) (j : Fin 3)
    (w z A1 A2 A3 f b C R0 Base Selected Refl Pre A head M Y i : Fin m)
    (raw : Fin 16 → Fin m) (G : Fin 5 → Fin m) (H : Fin 6 → Fin m)
    (U I P : Fin 3 → Fin m) (N : Fin 5 → Fin m) (V : Fin 3 → Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hA1 : Derives Γ (SyntaxNumeralSyntax.numeral 1 A1))
    (hA2 : Derives Γ (SyntaxNumeralSyntax.numeral 2 A2))
    (hf : Derives Γ (SyntaxNumeralSyntax.numeral (k+2) f))
    (hi : Derives Γ (SyntaxNumeralSyntax.numeral k i))
    (hBase : Derives Γ (SyntaxMixedImageCodeSyntax.termList w f z b Base))
    (hRow : Derives Γ (ForcingPreorderLeaves.data test Reln w z A1 A2 A3 f b C R0 Base Refl Pre raw G H U I P N V))
    (hGuard : Derives Γ (ForcingGuardOpening.result false Reln w z f b (P j) Selected A head M Y))
    (carrier : ∀ {l} {Δ : Context l} (r : Fin m → Fin l) (V : Fin l), ZFContext.Evidence Δ →
      (∀ {F : Formula m}, Derives Γ F → Derives Δ (F.rename r)) →
      Derives Δ (field (r w) (r Base) (r i) V) → Derives Δ (field (r w) (r Selected) (r i) V)) :
    Derives Γ (.equal (H (ForcingPreorderMember.memberPosition j)) Y) := by
  let leaf := ForcingPreorderMember.memberPosition j
  let out := Formula.equal (H leaf) Y
  have hIf := SyntaxNumeralMembers.index_member hZ (k+2) (Fin.last k).castSucc f i hf hi
  have hiW := StructuralListTraceOrder.member_member hZ w i f hw (.conjL hBase) hIf
  refine eliminate_objects hZ 1 (fun r x => (Formula.mem (x 0) (r w)).conj (field (r w) (r Base) (r i) (x 0)))
    (StructuralListFieldValues.exists_value hZ w Base i hw hiW) out ?_
  intro l Δ r x hZ1 lift hField
  have hw1 := of_eq (omega_rename w r) (lift hw)
  have hz1 := of_eq (empty_rename z r) (lift hz)
  have hi1 := of_eq (SyntaxNumeralSyntax.numeral_rename _ i r) (lift hi)
  have hOld := ForcingPreorderMember.raw_from_data hZ1 test Reln j (r w) (r z) (r A1) (r A2) (r A3)
    (r f) (r b) (r C) (r R0) (r Base) (r Refl) (r Pre) (r i) (x 0)
    (r ∘ raw) (r ∘ G) (r ∘ H) (r ∘ U) (r ∘ I) (r ∘ P) (r ∘ N) (r ∘ V)
    hw1 hz1 (of_eq (SyntaxNumeralSyntax.numeral_rename _ A1 r) (lift hA1))
    (of_eq (SyntaxNumeralSyntax.numeral_rename _ A2 r) (lift hA2)) hi1
    (of_eq (ForcingPreorderLeaves.data_rename test Reln _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ r) (lift hRow))
    (.conjR hField)
  have hNew := member_guard_result hZ1 Reln (r w) (r z) (r f) (r b) (r (P j)) (r Selected) (r A)
    (r head) (r M) (r Y) (r i) (x 0) hw1 hz1 hi1 (carrier r (x 0) hZ1 lift (.conjR hField))
    (of_eq (ForcingGuardOpening.result_rename false Reln _ _ _ _ _ _ _ _ _ _ r) (lift hGuard))
  exact ForcingPreorderMember.same_result hZ1 (r w) (r (P j)) (x 0) (r (H leaf)) (r Y) hw1 hOld hNew

/-- The membership guard at an opened condition and the corresponding
original preorder row have the same literal member code. Both read the
same actual carrier field from the retained free table. -/
theorem witness_member_from_row {k m} {Γ : Context m}
    (hZ : ZFContext.Evidence Γ) (Reln : Formula (k+2)) (j : Fin 3)
    (w z A1 A2 A3 f b C R0 Base Refl Pre A head M Y i : Fin m)
    (raw : Fin 16 → Fin m) (G : Fin 5 → Fin m) (H : Fin 6 → Fin m)
    (U I P : Fin 3 → Fin m) (N : Fin 5 → Fin m) (V : Fin 3 → Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hA1 : Derives Γ (SyntaxNumeralSyntax.numeral 1 A1))
    (hA2 : Derives Γ (SyntaxNumeralSyntax.numeral 2 A2))
    (hf : Derives Γ (SyntaxNumeralSyntax.numeral (k+2) f))
    (hi : Derives Γ (SyntaxNumeralSyntax.numeral k i))
    (hBase : Derives Γ (SyntaxMixedImageCodeSyntax.termList w f z b Base))
    (hRow : Derives Γ (ForcingPreorderLeaves.data test Reln w z A1 A2 A3 f b C R0 Base Refl Pre raw G H U I P N V))
    (hGuard : Derives Γ (ForcingGuardOpening.result false Reln w z f b (P j) Base A head M Y)) :
    Derives Γ (.equal (H (ForcingPreorderMember.memberPosition j)) Y) :=
  witness_member_from_carrier hZ Reln j w z A1 A2 A3 f b C R0 Base Base Refl Pre A head M Y i
    raw G H U I P N V hw hz hA1 hA2 hf hi hBase hRow hGuard (fun _ _ _ _ h => h)

/-- The actual selected condition changes only the last column. Compare
membership through the unchanged carrier field of the same two tables. -/
theorem witness_member_from_updated_row {k m} {Γ : Context m}
    (hZ : ZFContext.Evidence Γ) (Reln : Formula (k+2)) (j : Fin 3)
    (w z A1 A2 A3 f b C R0 Base Selected Refl Pre A head M Y i condition p : Fin m)
    (raw : Fin 16 → Fin m) (G : Fin 5 → Fin m) (H : Fin 6 → Fin m)
    (U I P : Fin 3 → Fin m) (N : Fin 5 → Fin m) (V : Fin 3 → Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hA1 : Derives Γ (SyntaxNumeralSyntax.numeral 1 A1))
    (hA2 : Derives Γ (SyntaxNumeralSyntax.numeral 2 A2))
    (hf : Derives Γ (SyntaxNumeralSyntax.numeral (k+2) f))
    (hi : Derives Γ (SyntaxNumeralSyntax.numeral k i))
    (hBase : Derives Γ (SyntaxMixedImageCodeSyntax.termList w f z b Base))
    (hRow : Derives Γ (ForcingPreorderLeaves.data test Reln w z A1 A2 A3 f b C R0 Base Refl Pre raw G H U I P N V))
    (hCondition : Derives Γ (SyntaxNumeralSyntax.numeral (k+1) condition))
    (hUpdate : Derives Γ (ForcingReflexiveImages.replacement w f z b Base condition p Selected))
    (hGuard : Derives Γ (ForcingGuardOpening.result false Reln w z f b (P j) Selected A head M Y)) :
    Derives Γ (.equal (H (ForcingPreorderMember.memberPosition j)) Y) :=
  witness_member_from_carrier hZ Reln j w z A1 A2 A3 f b C R0 Base Selected Refl Pre A head M Y i
    raw G H U I P N V hw hz hA1 hA2 hf hi hBase hRow hGuard (fun r value hZ1 lift hField =>
      ForcingPreorderGuardTables.carrier_field hZ1 (r w) (r f) (r z) (r b) (r Base) (r condition)
        (r p) (r Selected) (r i) value
        (of_eq (SyntaxNumeralSyntax.numeral_rename _ _ r) (lift hf))
        (of_eq (SyntaxNumeralSyntax.numeral_rename _ _ r) (lift hCondition))
        (of_eq (SyntaxNumeralSyntax.numeral_rename _ _ r) (lift hi))
        (of_eq (ForcingReflexiveImages.replacement_rename _ _ _ _ _ _ _ _ r) (lift hUpdate)) hField)

private theorem with_reflexive_direct {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z A C f b B Base K H p M Dm Im : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hp : Derives Γ (SyntaxTermSyntax.term w z b p))
    (hl : Derives Γ (SyntaxCodedMixedBinderSyntax.lifted w B Base z f z b A C K H))
    (hBody : Derives Γ (substituted w K H A f C b M Dm))
    (hInst : Derives Γ (instantiated w z b C p Dm Im)) (out : Formula m)
    (use : ∀ {l} {Δ : Context l} (r : Fin m → Fin l), ZFContext.Evidence Δ →
      (∀ {P : Formula m}, Derives Γ P → Derives Δ (P.rename r)) →
      ∀ D : Fin l, Derives Δ (field (r w) D (r z) (r p)) →
      Derives Δ (substituted (r w) D (r Base) (r A) (r f) (r z) (r b) (r M) (r Im)) →
      Derives Δ (out.rename r)) : Derives Γ out := by
  have hin := SyntaxCodedMixedBinderTyping.input_of_lifted w B Base z f z b A C K H hl
  have hB := Derives.conjL (.conjL (.conjR (.conjR (.conjL (.conjL hin)))))
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
  have result := use ρ hZ2 carry (s (x 0)) hField hQuery
  simpa only [ρ, SourceAlgebra.rename_comp, Function.comp_def] using result

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
  let out := ForcingMemberGuardOpening.result w p V Im
  apply with_reflexive_direct hZ w z A C f b B Base K H p M Dm Im hw hz hp hl hBody hInst out
  intro l Δ ρ hZ1 lift D hField hQuery
  have result := reflexive_member_at_query hZ1 Reln (ρ w) (ρ z) (ρ A) (ρ f) (ρ b) D
    (ρ Base) (ρ p) (ρ head) (ρ M) (ρ Im) (ρ i) (ρ V)
    (of_eq (omega_rename w ρ) (lift hw)) (of_eq (empty_rename z ρ) (lift hz))
    (of_eq (SyntaxVariableSyntax.code_rename true w z head ρ) (lift hh))
    (of_eq (SyntaxNumeralSyntax.numeral_rename k i ρ) (lift hi)) hField
    (of_eq (field_rename w Base i V ρ) (lift hV))
    (of_eq (PureQuotationSyntax.formula_rename _ w M ρ) (lift hM)) hQuery
  exact of_eq (ForcingMemberGuardOpening.result_rename w p V Im ρ).symm result

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
private theorem with_reflexive_query_instances {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (Reln : Formula (k+2)) (w z A1 A2 A3 f b B Base Refl : Fin m)
    (raw : Fin 16 → Fin m) (P : Fin 3 → Fin m) (hw : Derives Γ (omega w))
    (hRaw : Derives Γ (ForcingPreorderCode.rawData Reln w z A1 A2 A3 f raw))
    (hRun : Derives Γ (substituted w B Base z f z b (raw 1) Refl))
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
      Derives Δ (out.rename r)) : Derives Γ out :=
  with_reflexive_query_instances hZ Reln w z A1 A2 A3 f b B Base Refl raw P hw hRaw
    (.conjL (.conjR (.conjR (.conjR hTarget)))) hp out use

-- The two finite source shapes specialize this helper, so both raw queries
-- start from one actual quotation of the original relation.
section OrderQueries
attribute [local implicit_reducible] YesMetaZFC.SetTheory.signature

private theorem with_native_relation_query {k m} {Γ : Context m}
    (hZ : ZFContext.Evidence Γ) (R : Formula (k+2))
    (map : NativeSubstitutionSyntax.Mapping
      (YesMetaZFC.SetTheory.Definitional.Project.fo_bound_context (k+2))
      (YesMetaZFC.SetTheory.Definitional.Project.fo_bound_context 1)
      (YesMetaZFC.SetTheory.Definitional.Project.fo_bound_context (k+2)))
    (w z A f Bare Raw : Fin m) (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hA : Derives Γ (SyntaxNumeralSyntax.numeral 1 A))
    (hf : Derives Γ (SyntaxNumeralSyntax.numeral (k+2) f))
    (hBare : Derives Γ (PureQuotationSyntax.formula (ForcingRelationSource.source R) w Bare))
    (hRaw : Derives Γ (PureQuotationSyntax.formula
      ((ForcingRelationSource.source R).substituteMapped ForcingRelationSource.emptyMap map) w Raw))
    (out : Formula m)
    (use : ∀ {l} {Δ : Context l} (r : Fin m → Fin l), ZFContext.Evidence Δ →
      (∀ {F : Formula m}, Derives Γ F → Derives Δ (F.rename r)) →
      ∀ B F : Fin l,
      Derives Δ (NativeSubstitutionSyntax.environment ForcingRelationSource.emptyMap map
        (r w) (r z) (r f) (r A) (r f) B F) →
      Derives Δ (substituted (r w) B F (r z) (r f) (r A) (r f) (r Bare) (r Raw)) →
      Derives Δ (out.rename r)) : Derives Γ out := by
  have hf' : Derives Γ (SyntaxNumeralSyntax.numeral
      (YesMetaZFC.SetTheory.Definitional.Project.fo_bound_context (k+2)).length f) := by
    simpa only [YesMetaZFC.SetTheory.Definitional.Project.fo_bound_context, List.length_replicate] using hf
  refine eliminate_objects hZ 2 (fun r v =>
    NativeSubstitutionSyntax.environment ForcingRelationSource.emptyMap map
      (r w) (r z) (r f) (r A) (r f) (v 0) (v 1)) ?_ out ?_
  · exact NativeSubstitutionEnvironment.exists_environment hZ ForcingRelationSource.emptyMap map
      w z f A f hw hz hf' hA hf'
  intro l Δ r v hZ1 lift hEnv
  have hf1 := of_eq (SyntaxNumeralSyntax.numeral_rename _ f r) (lift hf')
  have hIff := NativeFormulaQuotationCorrespondence.formula_iff hZ1 (ForcingRelationSource.source R)
    ForcingRelationSource.emptyMap map (r w) (v 0) (v 1) (r z) (r f) (r A) (r f) (r Bare) (r Raw)
    (of_eq (omega_rename w r) (lift hw)) (of_eq (empty_rename z r) (lift hz))
    hf1 (of_eq (SyntaxNumeralSyntax.numeral_rename 1 A r) (lift hA)) hf1 hEnv
    (of_eq (PureQuotationSyntax.formula_rename _ w Bare r) (lift hBare))
  exact use r hZ1 lift (v 0) (v 1) hEnv
    (.impE (.conjR hIff) (of_eq (PureQuotationSyntax.formula_rename _ w Raw r) (lift hRaw)))

open SyntaxMixedImageCodeSyntax (termList termList_rename)
open ForcingReflexiveImages (replacement replacement_rename)

private theorem reflexive_order_to_direct {k m} {Γ : Context m}
    (hZ : ZFContext.Evidence Γ) (Reln : Formula (k+2))
    (w z f b A Base p B0 V O Io N i j M D : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hf : Derives Γ (SyntaxNumeralSyntax.numeral (k+2) f))
    (hA : Derives Γ (SyntaxNumeralSyntax.numeral 1 A))
    (hB0 : Derives Γ (termList w z z b B0))
    (hData : Derives Γ (ForcingRelationImages.data k w f z b Base p p i j M D))
    (hV : Derives Γ (field w V z p))
    (hN : Derives Γ (PureQuotationSyntax.formula (ForcingRelationSource.source Reln) w N))
    (hO : Derives Γ (PureQuotationSyntax.formula (ForcingPreorderCode.reflexiveLeaf Reln true) w O))
    (hIo : Derives Γ (substituted w V Base A f z b O Io)) :
    Derives Γ (substituted w B0 D z f z b N Io) := by
  let out := substituted w B0 D z f z b N Io
  have hQuote := of_eq (congrArg (fun φ => PureQuotationSyntax.formula φ w O)
    (ForcingRelationSource.diagonal_source Reln).symm) hO
  apply with_native_relation_query hZ Reln (ForcingRelationSource.diagonalMap k)
    w z A f N O hw hz hA hf hN hQuote out
  intro l Δ r hZ1 lift B F hEnv hFirst
  have hw1 := of_eq (omega_rename w r) (lift hw)
  have hz1 := of_eq (empty_rename z r) (lift hz)
  have hf1 := of_eq (SyntaxNumeralSyntax.numeral_rename (k+2) f r) (lift hf)
  have hd1 := of_eq (ForcingRelationImages.data_rename k w f z b Base p p i j M D r) (lift hData)
  have hDT := ForcingRelationImages.target_type k (r w) (r f) (r z) (r b) (r Base)
    (r p) (r p) (r i) (r j) (r M) (r D) hd1
  have hV1 := of_eq (field_rename w V z p r) (lift hV)
  apply of_eq (substituted_rename w B0 D z f z b N Io r).symm
  apply ForcingRelationGuardFormula.to_direct_from_terms hZ1
    (r w) (r z) (r f) (r A) (r z) (r b) B F (r V) (r Base) (r B0) (r D) (r N) (r O) (r Io)
    hw1 hz1 (SyntaxNumerals.range hZ1 (k+2) (r w) (r f) hw1 hf1)
    (of_eq (termList_rename w z z b B0 r) (lift hB0)) hDT hFirst
    (of_eq (substituted_rename w V Base A f z b O Io r) (lift hIo))
  intro l' Δ' s hZ2 lift2 x u v y hPath
  exact ForcingRelationImages.diagonal_term hZ2 (s (r w)) (s (r z)) (s (r f)) (s (r A))
    (s (r z)) (s (r b)) (s (r Base)) (s (r p)) (s (r i)) (s (r j)) (s (r M)) (s (r D))
    (s B) (s F) (s (r V)) (s (r B0)) x u v y
    (of_eq (omega_rename _ s) (lift2 hw1)) (of_eq (empty_rename _ s) (lift2 hz1))
    (of_eq (SyntaxNumeralSyntax.numeral_rename _ _ s) (lift2 hf1))
    (of_eq (NativeSubstitutionSyntax.environment_rename ForcingRelationSource.emptyMap
      (ForcingRelationSource.diagonalMap k) _ _ _ _ _ _ _ s) (lift2 hEnv))
    (of_eq (ForcingRelationImages.data_rename k _ _ _ _ _ _ _ _ _ _ _ s) (lift2 hd1))
    (of_eq (field_rename _ _ _ _ s) (lift2 hV1)) hPath

private theorem density_order_to_direct {k m} {Γ : Context m}
    (hZ : ZFContext.Evidence Γ) (Reln : Formula (k+2))
    (w z f b t Base S p B0 V O Yo N i j M D : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hf : Derives Γ (SyntaxNumeralSyntax.numeral (k+2) f))
    (ht : Derives Γ (SyntaxNumeralSyntax.numeral 1 t))
    (hB0 : Derives Γ (termList w z z b B0))
    (hData : Derives Γ (ForcingRelationImages.data k w f z b Base p p i j M D))
    (hUpdate : Derives Γ (replacement w f z b Base j p S))
    (hV : Derives Γ (SyntaxForestSyntax.forest 1 w (fun _ => p) V))
    (hN : Derives Γ (PureQuotationSyntax.formula (ForcingRelationSource.source Reln) w N))
    (hO : Derives Γ (PureQuotationSyntax.formula (ForcingGuardCode.template true Reln) w O))
    (hYo : Derives Γ (substituted w V S t f z b O Yo)) :
    Derives Γ (substituted w B0 D z f z b N Yo) := by
  let out := substituted w B0 D z f z b N Yo
  have hQuote := of_eq (congrArg (fun φ => PureQuotationSyntax.formula φ w O)
    (ForcingRelationSource.guard_source Reln).symm) hO
  apply with_native_relation_query hZ Reln (ForcingRelationSource.guardMap k)
    w z t f N O hw hz ht hf hN hQuote out
  intro l Δ r hZ1 lift B F hEnv hFirst
  have hFrame : Derives Δ (ForcingRelationImages.guardFrame (k := k) (r w) (r z) (r f) (r t)
      (r z) (r b) (r Base) (r p) (r p) (r i) (r j) (r M) (r D) B F (r V) (r S)) :=
    .conjI (of_eq (omega_rename w r) (lift hw)) (.conjI (of_eq (empty_rename z r) (lift hz))
      (.conjI (of_eq (SyntaxNumeralSyntax.numeral_rename _ f r) (lift hf)) (.conjI hEnv
        (.conjI (of_eq (ForcingRelationImages.data_rename k w f z b Base p p i j M D r) (lift hData))
          (.conjI (of_eq (SyntaxForestSyntax.forest_rename 1 w (fun _ => p) V r) (lift hV))
            (of_eq (replacement_rename w f z b Base j p S r) (lift hUpdate)))))))
  exact of_eq (substituted_rename w B0 D z f z b N Yo r).symm
    (ForcingRelationGuardFormula.to_direct hZ1 (r w) (r z) (r f) (r t) (r z) (r b)
      (r Base) (r p) (r p) (r i) (r j) (r M) (r D) B F (r V) (r S) (r B0) (r N) (r O) (r Yo)
      hFrame (of_eq (termList_rename w z z b B0 r) (lift hB0)) hFirst
      (of_eq (substituted_rename w V S t f z b O Yo r) (lift hYo)))


/-- Normalize the opened inner order guard to the original bare relation.
The left slot reads r from the replacement, and the right slot reads q
from the singleton bound table. -/
private theorem reverse_order_to_direct {k m} {Γ : Context m}
    (hZ : ZFContext.Evidence Γ) (Reln : Formula (k+2))
    (w z f b t Base F P Q B0 V O Yo N i j M D : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hf : Derives Γ (SyntaxNumeralSyntax.numeral (k+2) f))
    (ht : Derives Γ (SyntaxNumeralSyntax.numeral 1 t))
    (hB0 : Derives Γ (termList w z z b B0))
    (hData : Derives Γ (ForcingRelationImages.data k w f z b Base P Q i j M D))
    (hUpdate : Derives Γ (replacement w f z b Base j P F))
    (hV : Derives Γ (SyntaxForestSyntax.forest 1 w (fun _ => Q) V))
    (hN : Derives Γ (PureQuotationSyntax.formula (ForcingRelationSource.source Reln) w N))
    (hO : Derives Γ (PureQuotationSyntax.formula
      (ForcingGuardCode.template true (ForcingExistGuardsCode.reverseOrder Reln)) w O))
    (hYo : Derives Γ (substituted w V F t f z b O Yo)) :
    Derives Γ (substituted w B0 D z f z b N Yo) := by
  let out := substituted w B0 D z f z b N Yo
  have hQuote := of_eq (congrArg (fun φ => PureQuotationSyntax.formula φ w O)
    (ForcingRelationSource.reverse_guard_source Reln).symm) hO
  apply with_native_relation_query hZ Reln (ForcingRelationSource.reverseGuardMap k)
    w z t f N O hw hz ht hf hN hQuote out
  intro l Δ r hZ1 lift B Env hEnv hFirst
  have hw1 := of_eq (omega_rename w r) (lift hw)
  have hz1 := of_eq (empty_rename z r) (lift hz)
  have hf1 := of_eq (SyntaxNumeralSyntax.numeral_rename _ f r) (lift hf)
  have hData1 := of_eq (ForcingRelationImages.data_rename k w f z b Base P Q i j M D r) (lift hData)
  have hUpdate1 := of_eq (replacement_rename w f z b Base j P F r) (lift hUpdate)
  have hV1 := of_eq (SyntaxForestSyntax.forest_rename 1 w (fun _ => Q) V r) (lift hV)
  have hLast := of_eq (substituted_rename w V F t f z b O Yo r) (lift hYo)
  refine of_eq (substituted_rename w B0 D z f z b N Yo r).symm
    (ForcingRelationGuardFormula.to_direct_from_terms hZ1 (r w) (r z) (r f) (r t) (r z) (r b)
      B Env (r V) (r F) (r B0) (r D) (r N) (r O) (r Yo) hw1 hz1
      (SyntaxNumerals.range hZ1 (k+2) (r w) (r f) hw1 hf1)
      (of_eq (termList_rename w z z b B0 r) (lift hB0))
      (ForcingRelationImages.target_type k (r w) (r f) (r z) (r b) (r Base) (r P) (r Q)
        (r i) (r j) (r M) (r D) hData1) hFirst hLast ?_)
  intro l' Ξ s hZ2 move x u v y hPath
  exact ForcingRelationImages.reverse_guard_term hZ2 (s (r w)) (s (r z)) (s (r f)) (s (r t))
    (s (r z)) (s (r b)) (s (r Base)) (s (r P)) (s (r Q)) (s (r i)) (s (r j)) (s (r M)) (s (r D))
    (s B) (s Env) (s (r V)) (s (r F)) (s (r B0)) x u v y
    (of_eq (omega_rename _ s) (move hw1)) (of_eq (empty_rename _ s) (move hz1))
    (of_eq (SyntaxNumeralSyntax.numeral_rename _ _ s) (move hf1))
    (of_eq (NativeSubstitutionSyntax.environment_rename _ _ _ _ _ _ _ _ _ s) (move hEnv))
    (of_eq (ForcingRelationImages.data_rename k _ _ _ _ _ _ _ _ _ _ _ s) (move hData1))
    (of_eq (SyntaxForestSyntax.forest_rename 1 _ _ _ s) (move hV1))
    (of_eq (replacement_rename _ _ _ _ _ _ _ _ s) (move hUpdate1)) hPath

private theorem witness_order_agrees {k m} {Γ : Context m}
    (hZ : ZFContext.Evidence Γ) (Reln : Formula (k+2)) (leaf : Fin 3)
    (w z A1 A2 A3 g f b R0 Base F A head Nguard Raw Forward Bare Yrow Yguard j : Fin m)
    (E a n q : Fin 4 → Fin m) (P V : Fin 3 → Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hA1 : Derives Γ (SyntaxNumeralSyntax.numeral 1 A1))
    (hA2 : Derives Γ (SyntaxNumeralSyntax.numeral 2 A2))
    (hf : Derives Γ (SyntaxNumeralSyntax.numeral (k+2) f))
    (hj : Derives Γ (SyntaxNumeralSyntax.numeral (k+1) j))
    (hTerm : ∀ i, Derives Γ (SyntaxTermSyntax.term w z b (P i)))
    (hR0 : Derives Γ (termList w z z b R0)) (hBase : Derives Γ (termList w f z b Base))
    (hSource : Derives Γ (ForcingRelationSource.data Reln leaf w z g A3 f Raw Forward Bare E))
    (hPrefix : Derives Γ (ForcingPreorderPrefix.data w z f b R0 Base a n q P V))
    (hRow : Derives Γ (substituted w (V 2) Base A3 f z b Raw Yrow))
    (hUpdate : Derives Γ (replacement w f z b Base j (P (ForcingRelationRawTerms.reversed id (ForcingRelationSource.leftIndex leaf))) F))
    (hGuard : Derives Γ (ForcingGuardOpening.result true (ForcingExistGuardsCode.reverseOrder Reln)
      w z f b (P (ForcingRelationRawTerms.reversed id (ForcingRelationSource.rightIndex leaf))) F A head Nguard Yguard)) : Derives Γ (.equal Yrow Yguard) := by
  let out := Formula.equal Yrow Yguard
  let left := ForcingRelationRawTerms.reversed id (ForcingRelationSource.leftIndex leaf)
  let right := ForcingRelationRawTerms.reversed id (ForcingRelationSource.rightIndex leaf)
  have hExists := ForcingRelationImages.produce hZ k w f z b Base (P (left)) (P (right)) hw hBase (hTerm (left)) (hTerm (right))
  refine eliminate_objects hZ 4 (fun r d => ForcingRelationImages.data k (r w) (r f) (r z) (r b)
    (r Base) (r (P (left))) (r (P (right))) (d 0) (d 1) (d 2) (d 3)) hExists out ?_
  intro l Δ r d hZ1 lift hData
  have hw1 := of_eq (omega_rename w r) (lift hw)
  have hz1 := of_eq (empty_rename z r) (lift hz)
  have hf1 := of_eq (SyntaxNumeralSyntax.numeral_rename _ f r) (lift hf)
  have hj1 := of_eq (SyntaxNumeralSyntax.numeral_rename _ j r) (lift hj)
  have hSlot := SyntaxNumerals.unique hZ1 (k+1) (r j) (d 1) hj1 (.conjL (.conjR hData))
  have hUpdate1 := ForcingPreorderGuardTables.replacement_index (r w) (r f) (r z) (r b)
    (r Base) (r j) (r (P (left))) (r F) (d 1) hSlot (of_eq (replacement_rename _ _ _ _ _ _ _ _ r) (lift hUpdate))
  have hSource1 := of_eq (ForcingRelationSource.data_rename Reln leaf w z g A3 f Raw Forward Bare E r) (lift hSource)
  have hRev (i : Fin 3) : (r ∘ P) (ForcingRelationRawTerms.reversed id i) =
      ForcingRelationRawTerms.reversed (r ∘ P) i := by
    exact Fin.cases rfl (Fin.cases rfl (fun _ => rfl)) i
  have hImages : Derives Δ (ForcingRelationImages.data k (r w) (r f) (r z) (r b) (r Base)
      (ForcingRelationRawTerms.reversed (r ∘ P) (ForcingRelationSource.leftIndex leaf))
      (ForcingRelationRawTerms.reversed (r ∘ P) (ForcingRelationSource.rightIndex leaf))
      (d 0) (d 1) (d 2) (d 3)) := by
    rw [← hRev, ← hRev]
    exact hData
  have hRow1 := ForcingRelationRawFormula.from_prefix hZ1 Reln leaf (r w) (r z) (r A1) (r A2) (r A3) (r g)
    (r f) (r b) (r R0) (r Base) (r Raw) (r Forward) (r Bare) (d 0) (d 1) (d 2) (d 3) (r Yrow)
    (r ∘ E) (r ∘ a) (r ∘ n) (r ∘ q) (r ∘ P) (r ∘ V) hw1 hz1
    (of_eq (SyntaxNumeralSyntax.numeral_rename 1 A1 r) (lift hA1))
    (of_eq (SyntaxNumeralSyntax.numeral_rename 2 A2 r) (lift hA2)) hf1 hSource1
    (of_eq (ForcingPreorderPrefix.data_rename w z f b R0 Base a n q P V r) (lift hPrefix))
    (of_eq (termList_rename _ _ _ _ _ r) (lift hR0))
    (fun i => lift (SyntaxTerms.range hZ w z b (P i) hw (hTerm i))) hImages
    (of_eq (substituted_rename _ _ _ _ _ _ _ _ _ r) (lift hRow))
  let rev := ForcingExistGuardsCode.reverseOrder Reln
  refine eliminate_objects hZ1 4 (fun s u =>
    ForcingGuardOpening.data true rev (s (r w)) (s (r z)) (s (r f)) (s (r b)) (s (r (P (right))))
      (s (r F)) (s (r A)) (s (r head)) (s (r Nguard)) (s (r Yguard)) u)
    (of_eq (ForcingGuardOpening.result_rename true rev _ _ _ _ _ _ _ _ _ _ r) (lift hGuard)) (out.rename r) ?_
  intro l' Δ' s u hZ2 lift2 hG
  refine eliminate_objects hZ2 1 (fun t v =>
    (SyntaxForestSyntax.forest 1 (t (s (r w))) (fun _ => t (s (r (P (right))))) (v 0)).conj
      (substituted (t (s (r w))) (v 0) (t (s (r F))) (t (u 0)) (t (s (r f))) (t (s (r z)))
        (t (s (r b))) (t (u 1)) (t (s (r Yguard))))) (.conjR hG) ((out.rename r).rename s) ?_
  intro l'' Δ'' t v hZ3 lift3 hV
  let ρ := t ∘ s ∘ r
  let σ := t ∘ s
  have carry {G : Formula l} (h : Derives Δ G) : Derives Δ'' (G.rename σ) :=
    of_eq (SourceAlgebra.rename_comp G s t) (lift3 (lift2 h))
  have hMatrix := of_eq (ForcingGuardCode.matrix_rename true rev _ _ _ _ _ u t) (lift3 (.conjL hG))
  have hw3 := of_eq (omega_rename (r w) σ) (carry hw1)
  have hGuard3 := reverse_order_to_direct hZ3 Reln (ρ w) (ρ z) (ρ f) (ρ b) (t (u 0))
    (ρ Base) (ρ F) (ρ (P (left))) (ρ (P (right))) (ρ R0) (v 0) (t (u 1)) (ρ Yguard) (ρ Bare)
    (σ (d 0)) (σ (d 1)) (σ (d 2)) (σ (d 3)) hw3
    (of_eq (empty_rename (r z) σ) (carry hz1))
    (of_eq (SyntaxNumeralSyntax.numeral_rename _ (r f) σ) (carry hf1)) (.conjL hMatrix)
    (of_eq (termList_rename _ _ _ _ _ ρ)
      (of_eq (SourceAlgebra.rename_comp _ r σ) (carry (lift hR0))))
    (of_eq (ForcingRelationImages.data_rename k _ _ _ _ _ _ _ _ _ _ _ σ) (carry hData))
    (of_eq (replacement_rename _ _ _ _ _ _ _ _ σ) (carry hUpdate1)) (.conjL hV)
    (of_eq (PureQuotationSyntax.formula_rename _ (r w) (r Bare) σ) (carry (.conjL hSource1)))
    (.conjL (.conjL (.conjR hMatrix))) (.conjR hV)
  have hEq := SyntaxMixedFormulaOutputInduction.unique hZ3 (ρ w) (ρ R0) (σ (d 3))
    (ρ z) (ρ f) (ρ z) (ρ b) (ρ Bare) (ρ Yrow) (ρ Yguard) hw3
    (of_eq (substituted_rename _ _ _ _ _ _ _ _ _ σ) (carry hRow1)) hGuard3
  simpa only [out, ρ, Formula.rename, Function.comp_def] using hEq


/-- Identify the actual opened order guard with the matching leaf of the
inherited preorder row. Both queries use the same original relation. -/
theorem order_from_row {k m} {Γ : Context m}
    (hZ : ZFContext.Evidence Γ) (Reln : Formula (k+2)) (leaf : Fin 3)
    (w z A1 A2 A3 f b C R0 Base Refl Pre F A head Nguard Y j : Fin m)
    (raw : Fin 16 → Fin m) (G : Fin 5 → Fin m) (H : Fin 6 → Fin m)
    (U I P : Fin 3 → Fin m) (N : Fin 5 → Fin m) (V : Fin 3 → Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hA1 : Derives Γ (SyntaxNumeralSyntax.numeral 1 A1))
    (hA2 : Derives Γ (SyntaxNumeralSyntax.numeral 2 A2))
    (hA3 : Derives Γ (SyntaxNumeralSyntax.numeral 3 A3))
    (hf : Derives Γ (SyntaxNumeralSyntax.numeral (k+2) f))
    (hj : Derives Γ (SyntaxNumeralSyntax.numeral (k+1) j))
    (hTerm : ∀ i, Derives Γ (SyntaxTermSyntax.term w z b (P i)))
    (hR0 : Derives Γ (termList w z z b R0)) (hBase : Derives Γ (termList w f z b Base))
    (hRow : Derives Γ (ForcingPreorderLeaves.data test Reln w z A1 A2 A3 f b C R0 Base Refl Pre raw G H U I P N V))
    (hUpdate : Derives Γ (replacement w f z b Base j (P (ForcingRelationRawTerms.reversed id (ForcingRelationSource.leftIndex leaf))) F))
    (hGuard : Derives Γ (ForcingGuardOpening.result true (ForcingExistGuardsCode.reverseOrder Reln)
      w z f b (P (ForcingRelationRawTerms.reversed id (ForcingRelationSource.rightIndex leaf))) F A head Nguard Y)) : Derives Γ (.equal (H (ForcingPreorderLeaves.relationPosition leaf)) Y) := by
  let out := Formula.equal (H (ForcingPreorderLeaves.relationPosition leaf)) Y
  let φ := ForcingGuardCode.template true Reln
  refine with_tree_quote hZ (PureSyntaxQuotation.formulaTree φ) w hw out ?_
  intro l Δ r hZ1 lift Forward hQuote
  have hw1 := of_eq (omega_rename w r) (lift hw)
  have hz1 := of_eq (empty_rename z r) (lift hz)
  have hf1 := of_eq (SyntaxNumeralSyntax.numeral_rename _ f r) (lift hf)
  have hRaw := of_eq (ForcingPreorderCode.rawData_rename Reln w z A1 A2 A3 f raw r) (lift (.conjL hRow))
  have hAtom := ForcingRelationSource.raw_quotation Reln leaf (r w) (r z) (r A1) (r A2) (r A3) (r f) (r ∘ raw) hRaw
  have hSource := ForcingRelationSource.produce hZ1 Reln leaf (r w) (r z) (r A1) (r A3) (r f) (r (raw (ForcingRelationSource.rawSlot leaf))) Forward
    hw1 hz1 (of_eq (SyntaxNumeralSyntax.numeral_rename _ A1 r) (lift hA1))
    (of_eq (SyntaxNumeralSyntax.numeral_rename _ A3 r) (lift hA3)) hf1 hAtom hQuote
  refine eliminate_objects hZ1 5 (fun s u => ForcingRelationSource.data Reln leaf (s (r w)) (s (r z))
    (s (r A1)) (s (r A3)) (s (r f)) (s (r (raw (ForcingRelationSource.rawSlot leaf)))) (s Forward) (u 0) (fun i => u i.succ))
    hSource (out.rename r) ?_
  intro l' Ξ s u hZ2 move hSrc
  let ρ := s ∘ r
  have carry {J : Formula m} (h : Derives Γ J) : Derives Ξ (J.rename ρ) :=
    of_eq (SourceAlgebra.rename_comp J r s) (move (lift h))
  have row := of_eq (ForcingPreorderLeaves.data_rename test Reln w z A1 A2 A3 f b C R0 Base Refl Pre raw G H U I P N V ρ)
    (carry hRow)
  have hQ : Derives Ξ (substituted (ρ w) (ρ (V 2)) (ρ Base) (ρ A3) (ρ f) (ρ z) (ρ b)
      (ρ (raw (ForcingRelationSource.rawSlot leaf))) (ρ (H (ForcingPreorderLeaves.relationPosition leaf)))) := by
    rw [← ForcingPreorderLeaves.relation_slot]
    exact ForcingPreorderLeaves.leaf_at (ρ w) (ρ (V 2)) (ρ Base) (ρ A3) (ρ f) (ρ z) (ρ b)
      (ρ ∘ raw) (ρ ∘ H) (ρ ∘ N) (ForcingPreorderLeaves.relationPosition leaf) (.conjR (.conjR (.conjR (.conjR row))))
  have hPre := Derives.conjL (.conjR (.conjR (.conjR row)))
  have hEq := witness_order_agrees hZ2 Reln leaf (ρ w) (ρ z) (ρ A1) (ρ A2) (ρ A3) (ρ A1) (ρ f) (ρ b)
    (ρ R0) (ρ Base) (ρ F) (ρ A) (ρ head) (ρ Nguard) (ρ (raw (ForcingRelationSource.rawSlot leaf))) (s Forward) (u 0) (ρ (H (ForcingPreorderLeaves.relationPosition leaf))) (ρ Y) (ρ j)
    (fun i => u i.succ) _ _ _ (ρ ∘ P) (ρ ∘ V)
    (of_eq (omega_rename w ρ) (carry hw)) (of_eq (empty_rename z ρ) (carry hz))
    (of_eq (SyntaxNumeralSyntax.numeral_rename _ A1 ρ) (carry hA1))
    (of_eq (SyntaxNumeralSyntax.numeral_rename _ A2 ρ) (carry hA2))
    (of_eq (SyntaxNumeralSyntax.numeral_rename _ f ρ) (carry hf))
    (of_eq (SyntaxNumeralSyntax.numeral_rename _ j ρ) (carry hj))
    (fun i => of_eq (SyntaxTermSyntax.term_rename w z b (P i) ρ) (carry (hTerm i)))
    (of_eq (termList_rename _ _ _ _ _ ρ) (carry hR0))
    (of_eq (termList_rename _ _ _ _ _ ρ) (carry hBase)) hSrc hPre hQ
    (of_eq (replacement_rename _ _ _ _ _ _ _ _ ρ) (carry hUpdate))
    (of_eq (ForcingGuardOpening.result_rename true (ForcingExistGuardsCode.reverseOrder Reln)
      _ _ _ _ _ _ _ _ _ _ ρ) (carry hGuard))
  simpa only [out, ρ, Formula.rename, Function.comp_def] using hEq

/-- The r≤q leaf in the original negative density proof. -/
theorem witness_order_from_row {k m} {Γ : Context m}
    (hZ : ZFContext.Evidence Γ) (Reln : Formula (k+2))
    (w z A1 A2 A3 f b C R0 Base Refl Pre F A head Nguard Y j : Fin m)
    (raw : Fin 16 → Fin m) (G : Fin 5 → Fin m) (H : Fin 6 → Fin m)
    (U I P : Fin 3 → Fin m) (N : Fin 5 → Fin m) (V : Fin 3 → Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hA1 : Derives Γ (SyntaxNumeralSyntax.numeral 1 A1))
    (hA2 : Derives Γ (SyntaxNumeralSyntax.numeral 2 A2))
    (hA3 : Derives Γ (SyntaxNumeralSyntax.numeral 3 A3))
    (hf : Derives Γ (SyntaxNumeralSyntax.numeral (k+2) f))
    (hj : Derives Γ (SyntaxNumeralSyntax.numeral (k+1) j))
    (hTerm : ∀ i, Derives Γ (SyntaxTermSyntax.term w z b (P i)))
    (hR0 : Derives Γ (termList w z z b R0)) (hBase : Derives Γ (termList w f z b Base))
    (hRow : Derives Γ (ForcingPreorderLeaves.data test Reln w z A1 A2 A3 f b C R0 Base Refl Pre raw G H U I P N V))
    (hUpdate : Derives Γ (replacement w f z b Base j (P 1) F))
    (hGuard : Derives Γ (ForcingGuardOpening.result true (ForcingExistGuardsCode.reverseOrder Reln)
      w z f b (P 2) F A head Nguard Y)) : Derives Γ (.equal (H 4) Y) :=
  order_from_row hZ Reln 1 w z A1 A2 A3 f b C R0 Base Refl Pre F A head Nguard Y j raw G H U I P N V
    hw hz hA1 hA2 hA3 hf hj hTerm hR0 hBase hRow hUpdate hGuard

private theorem order_eq_on_direct {k m} {Γ : Context m}
    (hZ : ZFContext.Evidence Γ) (Reln : Formula (k+2))
    (w z f b A t Base S p B0 Vr Vg Or Og Io Yo j : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hf : Derives Γ (SyntaxNumeralSyntax.numeral (k+2) f))
    (hA : Derives Γ (SyntaxNumeralSyntax.numeral 1 A)) (ht : Derives Γ (SyntaxNumeralSyntax.numeral 1 t))
    (hj : Derives Γ (SyntaxNumeralSyntax.numeral (k+1) j))
    (hp : Derives Γ (SyntaxTermSyntax.term w z b p))
    (hB0 : Derives Γ (termList w z z b B0)) (hBase : Derives Γ (termList w f z b Base))
    (hUpdate : Derives Γ (replacement w f z b Base j p S))
    (hVr : Derives Γ (field w Vr z p))
    (hVg : Derives Γ (SyntaxForestSyntax.forest 1 w (fun _ => p) Vg))
    (hr : Derives Γ (PureQuotationSyntax.formula (ForcingPreorderCode.reflexiveLeaf Reln true) w Or))
    (hg : Derives Γ (PureQuotationSyntax.formula (ForcingGuardCode.template true Reln) w Og))
    (hIo : Derives Γ (substituted w Vr Base A f z b Or Io))
    (hYo : Derives Γ (substituted w Vg S t f z b Og Yo)) :
    Derives Γ (.equal Io Yo) := by
  let out := Formula.equal Io Yo
  have hExists := ForcingRelationImages.produce hZ k w f z b Base p p hw hBase hp hp
  refine eliminate_objects hZ 4 (fun r d =>
    ForcingRelationImages.data k (r w) (r f) (r z) (r b) (r Base) (r p) (r p)
      (d 0) (d 1) (d 2) (d 3)) hExists out ?_
  intro l Δ r d hZ1 lift hData
  have hw1 := of_eq (omega_rename w r) (lift hw)
  have hj1 := of_eq (SyntaxNumeralSyntax.numeral_rename (k+1) j r) (lift hj)
  have hJ := SyntaxNumerals.unique hZ1 (k+1) (r j) (d 1) hj1 (.conjL (.conjR hData))
  have hUpdate1 := ForcingPreorderGuardTables.replacement_index
    (r w) (r f) (r z) (r b) (r Base) (r j) (r p) (r S) (d 1) hJ
    (of_eq (replacement_rename w f z b Base j p S r) (lift hUpdate))
  refine with_tree_quote hZ1 (PureSyntaxQuotation.formulaTree (ForcingRelationSource.source Reln))
    (r w) hw1 (out.rename r) ?_
  intro l' Δ' s hZ2 lift2 N hN
  let ρ := s ∘ r
  have carry {F : Formula m} (h : Derives Γ F) :=
    of_eq (SourceAlgebra.rename_comp F r s) (lift2 (lift h))
  have hw2 := of_eq (omega_rename w ρ) (carry hw)
  have hz2 := of_eq (empty_rename z ρ) (carry hz)
  have hf2 := of_eq (SyntaxNumeralSyntax.numeral_rename (k+2) f ρ) (carry hf)
  have hB02 := of_eq (termList_rename w z z b B0 ρ) (carry hB0)
  have hData2 := of_eq (ForcingRelationImages.data_rename k _ _ _ _ _ _ _ _ _ _ _ s) (lift2 hData)
  have hIo' := reflexive_order_to_direct hZ2 Reln (ρ w) (ρ z) (ρ f) (ρ b) (ρ A)
    (ρ Base) (ρ p) (ρ B0) (ρ Vr) (ρ Or) (ρ Io) N (s (d 0)) (s (d 1)) (s (d 2)) (s (d 3))
    hw2 hz2 hf2 (of_eq (SyntaxNumeralSyntax.numeral_rename 1 A ρ) (carry hA)) hB02 hData2
    (of_eq (field_rename w Vr z p ρ) (carry hVr)) hN
    (of_eq (PureQuotationSyntax.formula_rename _ w Or ρ) (carry hr))
    (of_eq (substituted_rename w Vr Base A f z b Or Io ρ) (carry hIo))
  have hYo' := density_order_to_direct hZ2 Reln (ρ w) (ρ z) (ρ f) (ρ b) (ρ t)
    (ρ Base) (ρ S) (ρ p) (ρ B0) (ρ Vg) (ρ Og) (ρ Yo) N (s (d 0)) (s (d 1)) (s (d 2)) (s (d 3))
    hw2 hz2 hf2 (of_eq (SyntaxNumeralSyntax.numeral_rename 1 t ρ) (carry ht)) hB02 hData2
    (of_eq (replacement_rename _ _ _ _ _ _ _ _ s) (lift2 hUpdate1))
    (of_eq (SyntaxForestSyntax.forest_rename 1 w (fun _ => p) Vg ρ) (carry hVg)) hN
    (of_eq (PureQuotationSyntax.formula_rename _ w Og ρ) (carry hg))
    (of_eq (substituted_rename w Vg S t f z b Og Yo ρ) (carry hYo))
  exact SyntaxMixedFormulaOutputInduction.unique hZ2 (ρ w) (ρ B0) (s (d 3))
    (ρ z) (ρ f) (ρ z) (ρ b) N (ρ Io) (ρ Yo) hw2 hIo' hYo'

/-- The actual reflexivity order instance and the actual density order guard
have the same code. Both paths start from the pinned source relation and
read the selected condition in each of its two argument slots. -/
theorem reflexive_order_agrees {k m} {Γ : Context m}
    (hZ : ZFContext.Evidence Γ) (Reln : Formula (k+2))
    (w z f b A Base S p head Q Yo Ar Cr B Kr Hr O Do Io j : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hf : Derives Γ (SyntaxNumeralSyntax.numeral (k+2) f))
    (hj : Derives Γ (SyntaxNumeralSyntax.numeral (k+1) j))
    (hp : Derives Γ (SyntaxTermSyntax.term w z b p))
    (hUpdate : Derives Γ (replacement w f z b Base j p S))
    (hGuard : Derives Γ (ForcingGuardOpening.result true Reln w z f b p S A head Q Yo))
    (hlr : Derives Γ (SyntaxCodedMixedBinderSyntax.lifted w B Base z f z b Ar Cr Kr Hr))
    (hO : Derives Γ (PureQuotationSyntax.formula (ForcingPreorderCode.reflexiveLeaf Reln true) w O))
    (hDo : Derives Γ (substituted w Kr Hr Ar f Cr b O Do))
    (hIo : Derives Γ (instantiated w z b Cr p Do Io)) :
    Derives Γ (.equal Io Yo) := by
  let out := Formula.equal Io Yo
  have hInput := SyntaxCodedMixedBinderTyping.input_of_lifted w B Base z f z b Ar Cr Kr Hr hlr
  have hB := Derives.conjL (.conjL hInput)
  have hBase := Derives.conjR (.conjL hInput)
  have hAr := SyntaxNumeralSyntax.intro_succ 0 Ar z hz (.conjL (.conjR hInput))
  apply with_reflexive_direct hZ w z Ar Cr f b B Base Kr Hr p O Do Io hw hz hp hlr hDo hIo out
  intro l Δ r hZ1 lift Vr hVr hDirect
  have hGuard1 := of_eq (ForcingGuardOpening.result_rename true Reln w z f b p S A head Q Yo r) (lift hGuard)
  refine eliminate_objects hZ1 4 (fun s u =>
    ForcingGuardOpening.data true Reln (s (r w)) (s (r z)) (s (r f)) (s (r b)) (s (r p))
      (s (r S)) (s (r A)) (s (r head)) (s (r Q)) (s (r Yo)) u) hGuard1 (out.rename r) ?_
  intro l' Δ' s u hZ2 lift2 hG
  refine eliminate_objects hZ2 1 (fun t v =>
    (SyntaxForestSyntax.forest 1 (t (s (r w))) (fun _ => t (s (r p))) (v 0)).conj
      (substituted (t (s (r w))) (v 0) (t (s (r S))) (t (u 0)) (t (s (r f))) (t (s (r z)))
        (t (s (r b))) (t (u 1)) (t (s (r Yo))))) (.conjR hG) ((out.rename r).rename s) ?_
  intro l'' Δ'' t v hZ3 lift3 hV
  let ρ := t ∘ s ∘ r
  have carry {F : Formula m} (h : Derives Γ F) : Derives Δ'' (F.rename ρ) := by
    simpa only [ρ, SourceAlgebra.rename_comp, Function.comp_def] using lift3 (lift2 (lift h))
  have carry1 {F : Formula l} (h : Derives Δ F) : Derives Δ'' (F.rename (t ∘ s)) :=
    of_eq (SourceAlgebra.rename_comp F s t) (lift3 (lift2 h))
  have hMatrix := of_eq (ForcingGuardCode.matrix_rename true Reln _ _ _ _ _ u t) (lift3 (.conjL hG))
  have result := order_eq_on_direct hZ3 Reln (ρ w) (ρ z) (ρ f) (ρ b) (ρ Ar) (t (u 0))
    (ρ Base) (ρ S) (ρ p) (ρ B) (t (s Vr)) (v 0) (ρ O) (t (u 1)) (ρ Io) (ρ Yo) (ρ j)
    (of_eq (omega_rename w ρ) (carry hw)) (of_eq (empty_rename z ρ) (carry hz))
    (of_eq (SyntaxNumeralSyntax.numeral_rename _ _ ρ) (carry hf))
    (of_eq (SyntaxNumeralSyntax.numeral_rename _ _ ρ) (carry hAr)) (.conjL hMatrix)
    (of_eq (SyntaxNumeralSyntax.numeral_rename _ _ ρ) (carry hj))
    (of_eq (SyntaxTermSyntax.term_rename _ _ _ _ ρ) (carry hp))
    (of_eq (termList_rename _ _ _ _ _ ρ) (carry hB))
    (of_eq (termList_rename _ _ _ _ _ ρ) (carry hBase))
    (of_eq (replacement_rename _ _ _ _ _ _ _ _ ρ) (carry hUpdate))
    (of_eq (field_rename _ _ _ _ (t ∘ s)) (carry1 hVr)) (.conjL hV)
    (of_eq (PureQuotationSyntax.formula_rename _ _ _ ρ) (carry hO))
    (.conjL (.conjL (.conjR hMatrix)))
    (of_eq (substituted_rename _ _ _ _ _ _ _ _ _ (t ∘ s)) (carry1 hDirect)) (.conjR hV)
  simpa only [out, ρ, Formula.rename, SourceAlgebra.rename_comp, Function.comp_def] using result

private theorem instance_value {m} {Γ : Context m} (w z b C p X Y Y' : Fin m)
    (h : Derives Γ (instantiated w z b C p X Y)) (he : Derives Γ (.equal Y Y')) :
    Derives Γ (instantiated w z b C p X Y') := by
  let F := instantiated w.castSucc z.castSucc b.castSucc C.castSucc p.castSucc X.castSucc (Fin.last m)
  exact of_eq (by simp only [F, Formula.instantiate, instantiated_rename,
      Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
    (.eqSubst F he (of_eq (by simp only [F, Formula.instantiate, instantiated_rename,
      Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) h))

/-- Discharge both guards of the pointwise density premise from the actual
preorder and guard records. The reflexivity child queries and their equality
with the two density guards are constructed here. -/
private theorem tail_from_reflexive_query {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (Reln : Formula (k+2))
    (w z a A C f b L Base S K Bnd D head Q Um Ym Qo Yo Tail I j V Extra A1 A2 A3 Cr Bd Refl Pre : Fin m)
    (raw : Fin 16 → Fin m) (Gb : Fin 5 → Fin m) (H layout : Fin 6 → Fin m)
    (U F P : Fin 3 → Fin m) (N : Fin 5 → Fin m) (Ds : Fin 3 → Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (ht : Derives Γ (SyntaxTermSyntax.term w z b (P 1)))
    (hl : Derives Γ (SyntaxCodedMixedBinderSyntax.lifted w L S a f z b A C K Bnd))
    (hD : Derives Γ (consCode w (P 1) L D)) (hh : Derives Γ (SyntaxVariableSyntax.code true w z head))
    (hc : Derives Γ (ForcingGuardCode.compiled false Reln w A f head Q))
    (hUm : Derives Γ (substituted w K Bnd A f C b Q Um))
    (hYm : Derives Γ (instantiated w z b C (P 1) Um Ym))
    (hOrder : Derives Γ (ForcingGuardOpening.result true Reln w z f b (P 1) S A head Qo Yo))
    (hI : Derives Γ (SyntaxNumeralSyntax.numeral k I))
    (hf : Derives Γ (SyntaxNumeralSyntax.numeral (k+2) f))
    (hj : Derives Γ (SyntaxNumeralSyntax.numeral (k+1) j))
    (hReplace : Derives Γ (replacement w f z b Base j (P 1) S))
    (hV : Derives Γ (field w Base I V))
    (hA1 : Derives Γ (SyntaxNumeralSyntax.numeral 1 A1))
    (hA2 : Derives Γ (SyntaxNumeralSyntax.numeral 2 A2))
    (hRow : Derives Γ (ForcingPreorderLeaves.data test Reln w z A1 A2 A3 f b Cr Bd Base Refl Pre raw Gb H U F P N Ds))
    (hRun : Derives Γ (substituted w Bd Base z f z b (raw 1) Refl))
    (hExtra : Derives Γ (formulaCode w Extra z b))
    (hLayout : Derives Γ (ForcingProofContext.layoutData w z b Extra Pre H layout))
    (hTail : Derives Γ (discharge w z b (layout 3) Ym Yo Tail)) :
    Derives Γ (implication test w z b (layout 3) Tail) := by
  have hCore : Derives Γ (ForcingTransitiveGuardProof.row w z b Cr Refl Pre Gb H U F P N) :=
    .conjL (.conjL (.conjR hRow))
  have hFirst : Derives Γ (instantiated w z b Cr (P 0) (F 0) (U 1)) :=
    .conjL (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR hCore))))))))
  have hCr := Derives.conjR (SyntaxTopFormulaTyping.instantiate_environment w z b Cr (P 0) (F 0) (U 1) hFirst)
  apply with_reflexive_query_instances hZ Reln w z A1 A2 A3 f b Bd Base Refl raw P hw
    (.conjL hRow) hRun ht (implication test w z b (layout 3) Tail)
  intro l Δ r hZ1 lift M O Ar Cr' Kr Hr Fr Dm Do Im Io hM hO hlr hAll hBody hIm hIo
  have hw1 := of_eq (omega_rename w r) (lift hw)
  have hz1 := of_eq (empty_rename z r) (lift hz)
  have ht1 := of_eq (SyntaxTermSyntax.term_rename _ _ _ _ r) (lift ht)
  have hl1 := of_eq (SyntaxCodedMixedBinderSyntax.lifted_rename _ _ _ _ _ _ _ _ _ _ _ r) (lift hl)
  have hD1 := of_eq (consCode_rename _ _ _ _ r) (lift hD)
  have hh1 := of_eq (SyntaxVariableSyntax.code_rename true _ _ _ r) (lift hh)
  have hc1 := of_eq (ForcingGuardCode.compiled_rename false Reln _ _ _ _ _ r) (lift hc)
  have hUm1 := of_eq (substituted_rename _ _ _ _ _ _ _ _ _ r) (lift hUm)
  have hYm1 := of_eq (instantiated_rename _ _ _ _ _ _ _ r) (lift hYm)
  have hI1 := of_eq (SyntaxNumeralSyntax.numeral_rename _ _ r) (lift hI)
  have hf1 := of_eq (SyntaxNumeralSyntax.numeral_rename _ _ r) (lift hf)
  have hj1 := of_eq (SyntaxNumeralSyntax.numeral_rename _ _ r) (lift hj)
  have hReplace1 := of_eq (replacement_rename _ _ _ _ _ _ _ _ r) (lift hReplace)
  have hV1 := of_eq (field_rename _ _ _ _ r) (lift hV)
  have hMemEq := reflexive_member_agrees hZ1 Reln
    (r w) (r z) (r a) (r A) (r C) (r f) (r b) (r L) (r Base) (r S) (r K) (r Bnd)
    (r (P 1)) (r D) (r head) (r Q) (r Um) (r Ym) Ar Cr' (r Bd) Kr Hr M Dm Im (r I) (r j) (r V)
    hw1 hz1 ht1 hh1 hf1 hI1 hj1 hV1 hReplace1 hl1 hD1 hc1 hUm1 hYm1 hlr hM
    (.conjL (.conjR hBody)) hIm
  have hOrderEq := reflexive_order_agrees hZ1 Reln
    (r w) (r z) (r f) (r b) (r A) (r Base) (r S) (r (P 1)) (r head) (r Qo) (r Yo)
    Ar Cr' (r Bd) Kr Hr O Do Io (r j) hw1 hz1 hf1 hj1 ht1 hReplace1
    (of_eq (ForcingGuardOpening.result_rename true Reln _ _ _ _ _ _ _ _ _ _ r) (lift hOrder))
    hlr hO (.conjR (.conjR hBody)) hIo
  have hCr' := Derives.conjR (.conjR
    (SyntaxCodedMixedBinderTyping.input_of_lifted (r w) (r Bd) (r Base) (r z) (r f) (r z) (r b)
      Ar Cr' Kr Hr hlr))
  have hScope := OmegaUniversal.successor_unique Cr' (r Cr) (r z)
    (ZFContext.arithmetic hZ1).base.extensionality hCr' (of_eq (successor_rename _ _ r) (lift hCr))
  have hm := instance_scope (r w) (r z) (r b) Cr' (r Cr) (r (P 1)) Dm (r Ym) hScope
    (instance_value (r w) (r z) (r b) Cr' (r (P 1)) Dm Im (r Ym) hIm hMemEq)
  have ho := instance_scope (r w) (r z) (r b) Cr' (r Cr) (r (P 1)) Do (r Yo) hScope
    (instance_value (r w) (r z) (r b) Cr' (r (P 1)) Do Io (r Yo) hIo hOrderEq)
  apply of_eq (implication_rename test w z b (layout 3) Tail r).symm
  exact tail_from_row hZ1 Reln
    (r w) (r z) (r a) (r A) (r C) (r f) (r b) (r L) (r Base) (r S) (r K) (r Bnd) (r D)
    (r head) (r Q) (r Um) (r Ym) (r Yo) (r Tail) (r I) (r j) (r V) (r Extra) (r A1) (r A2) (r A3)
    (r Cr) (r Bd) (r Refl) (r Pre) Dm Do Fr
    (r ∘ raw) (r ∘ Gb) (r ∘ H) (r ∘ layout) (r ∘ U) (r ∘ F) (r ∘ P) (r ∘ N) (r ∘ Ds)
    hw1 hz1 ht1 hl1 hD1 hh1 hc1 hUm1 hYm1 hI1 hf1 hj1 hReplace1 hV1
    (of_eq (SyntaxNumeralSyntax.numeral_rename _ _ r) (lift hA1))
    (of_eq (SyntaxNumeralSyntax.numeral_rename _ _ r) (lift hA2))
    (of_eq (ForcingPreorderLeaves.data_rename test Reln w z A1 A2 A3 f b Cr Bd Base Refl Pre raw Gb H U F P N Ds r) (lift hRow))
    (of_eq (FormulaCodeSyntax.formulaCode_rename _ _ _ _ r) (lift hExtra))
    (of_eq (ForcingProofContext.layoutData_rename _ _ _ _ _ _ _ r) (lift hLayout))
    hAll (.conjL hBody) hm ho (of_eq (discharge_rename _ _ _ _ _ _ _ r) (lift hTail))

theorem tail_from_compilers {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (Reln : Formula (k+2))
    (w z a A C f b L Base S K Bnd D head Q Um Ym Qo Yo Tail I j V Extra A1 A2 A3 Cr Bd Refl Pre : Fin m)
    (raw : Fin 16 → Fin m) (Gb : Fin 5 → Fin m) (H layout : Fin 6 → Fin m)
    (U F P : Fin 3 → Fin m) (N : Fin 5 → Fin m) (Ds : Fin 3 → Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (ht : Derives Γ (SyntaxTermSyntax.term w z b (P 1)))
    (hl : Derives Γ (SyntaxCodedMixedBinderSyntax.lifted w L S a f z b A C K Bnd))
    (hD : Derives Γ (consCode w (P 1) L D)) (hh : Derives Γ (SyntaxVariableSyntax.code true w z head))
    (hc : Derives Γ (ForcingGuardCode.compiled false Reln w A f head Q))
    (hUm : Derives Γ (substituted w K Bnd A f C b Q Um))
    (hYm : Derives Γ (instantiated w z b C (P 1) Um Ym))
    (hOrder : Derives Γ (ForcingGuardOpening.result true Reln w z f b (P 1) S A head Qo Yo))
    (hI : Derives Γ (SyntaxNumeralSyntax.numeral k I))
    (hf : Derives Γ (SyntaxNumeralSyntax.numeral (k+2) f))
    (hj : Derives Γ (SyntaxNumeralSyntax.numeral (k+1) j))
    (hReplace : Derives Γ (replacement w f z b Base j (P 1) S))
    (hV : Derives Γ (field w Base I V))
    (hA1 : Derives Γ (SyntaxNumeralSyntax.numeral 1 A1))
    (hA2 : Derives Γ (SyntaxNumeralSyntax.numeral 2 A2))
    (hRow : Derives Γ (ForcingPreorderLeaves.data test Reln w z A1 A2 A3 f b Cr Bd Base Refl Pre raw Gb H U F P N Ds))
    (hTarget : Derives Γ (ForcingPreorderInstances.targetData test w z f b Cr Bd Base
      (raw 0) (raw 1) (raw 2) P Pre Refl (U 0)))
    (hExtra : Derives Γ (formulaCode w Extra z b))
    (hLayout : Derives Γ (ForcingProofContext.layoutData w z b Extra Pre H layout))
    (hTail : Derives Γ (discharge w z b (layout 3) Ym Yo Tail)) :
    Derives Γ (implication test w z b (layout 3) Tail) :=
  tail_from_reflexive_query hZ Reln w z a A C f b L Base S K Bnd D head Q Um Ym Qo Yo Tail I j V Extra A1 A2 A3
    Cr Bd Refl Pre raw Gb H layout U F P N Ds hw hz ht hl hD hh hc hUm hYm hOrder hI hf hj hReplace hV hA1 hA2 hRow
    (.conjL (.conjR (.conjR (.conjR hTarget)))) hExtra hLayout hTail

open SyntaxLogicalSyntax (singleCode singleCode_rename binaryCode_rename) in
open SyntaxMixedFormulaRecursiveSyntax (check) in
set_option maxHeartbeats 1200000 in
/-- Read the witness body of the actual instantiated density existential.
The last conjunction field is the very same falsum code as in the compiler. -/
private theorem with_falsum_tail {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z b D S A f Raw X Y M O N Tail : Fin m)
    (hw : Derives Γ (omega w))
    (hN : Derives Γ (SyntaxNodeSyntax.constructor 0 0 w Fin.elim0 N))
    (hcEx : Derives Γ (SyntaxLogicalSyntax.singleCode 10 w X Raw))
    (hcBody : Derives Γ (binaryCode 0 w M Y X))
    (hcMid : Derives Γ (binaryCode 0 w O N Y))
    (hq : Derives Γ (substituted w D S A f z b Raw Tail))
    (out : Formula m)
    (use : ∀ {l} {Δ : Context l} (r : Fin m → Fin l) (C X' M' Y' O' : Fin l),
      ZFContext.Evidence Δ →
      (∀ {F : Formula m}, Derives Γ F → Derives Δ (F.rename r)) →
      Derives Δ (successor C (r z)) →
      Derives Δ (SyntaxLogicalSyntax.singleCode 10 (r w) X' (r Tail)) →
      Derives Δ (binaryCode 0 (r w) M' Y' X') →
      Derives Δ (binaryCode 0 (r w) O' (r N) Y') →
      Derives Δ (formulaCode (r w) M' C (r b)) →
      Derives Δ (formulaCode (r w) O' C (r b)) →
      Derives Δ (formulaCode (r w) (r N) C (r b)) →
      Derives Δ (out.rename r)) :
    Derives Γ out := by
  refine eliminate_objects hZ 1 (fun r u =>
    (singleCode 10 (r w) (u 0) (r Tail)).conj
      (check true (r w) (r X) (r D) (r S) (r A) (r f) (r z) (r b) (u 0)))
    (ForcingMixedUnary.single_output hZ 10 true (Or.inr (Or.inr ⟨rfl, rfl⟩))
      w D S A f z b Raw X Tail hw hcEx hq) out ?_
  intro l Δ r u hZ1 lift hEx
  refine eliminate_objects hZ1 4 (fun s v =>
    (SyntaxCodedMixedBinderSyntax.lifted (s (r w)) (s (r D)) (s (r S)) (s (r A))
      (s (r f)) (s (r z)) (s (r b)) (v 0) (v 1) (v 2) (v 3)).conj
      (substituted (s (r w)) (v 2) (v 3) (v 0) (s (r f)) (v 1) (s (r b)) (s (r X)) (s (u 0))))
    (.conjR hEx) (out.rename r) ?_
  intro l1 Δ1 s v hZ2 lift1 hLift
  let t := s ∘ r
  have move {F : Formula m} (h : Derives Γ F) : Derives Δ1 (F.rename t) :=
    of_eq (SourceAlgebra.rename_comp F r s) (lift1 (lift h))
  have hw1 := of_eq (omega_rename _ _) (move hw)
  have hBody := ForcingFormulaDiagram.binary_output hZ2 0 (t w) (v 2) (v 3) (v 0) (t f)
    (v 1) (t b) (t X) (t M) (t Y) (s (u 0)) hw1 (of_eq (binaryCode_rename _ _ _ _ _ _) (move hcBody)) (.conjR hLift)
  refine of_eq (SourceAlgebra.rename_comp out r s).symm ?_
  refine eliminate_objects hZ2 2 (fun e x =>
    ForcingFormulaDiagram.binaryData 0 (e (t w)) (e (v 2)) (e (v 3)) (e (v 0)) (e (t f))
      (e (v 1)) (e (t b)) (e (t M)) (e (t Y)) (e (s (u 0))) (x 0) (x 1)) hBody (out.rename t) ?_
  intro l2 Δ2 e x hZ3 lift2 hX
  let te := e ∘ t
  have move2 {F : Formula m} (h : Derives Γ F) : Derives Δ2 (F.rename te) :=
    of_eq (SourceAlgebra.rename_comp F t e) (lift2 (move h))
  have hw2 := of_eq (omega_rename _ _) (move2 hw)
  have hMid := ForcingFormulaDiagram.binary_output hZ3 0 (te w) (e (v 2)) (e (v 3)) (e (v 0)) (te f)
    (e (v 1)) (te b) (te Y) (te O) (te N) (x 1) hw2 (of_eq (binaryCode_rename _ _ _ _ _ _) (move2 hcMid))
    (.conjR (.conjR hX))
  refine eliminate_objects hZ3 2 (fun d y =>
    ForcingFormulaDiagram.binaryData 0 (d (te w)) (d (e (v 2))) (d (e (v 3))) (d (e (v 0))) (d (te f))
      (d (e (v 1))) (d (te b)) (d (te O)) (d (te N)) (d (x 1)) (y 0) (y 1)) hMid
    ((out.rename t).rename e) ?_
  intro l3 Δ3 d y hZ4 lift3 hY
  let R := d ∘ te
  have move3 {F : Formula m} (h : Derives Γ F) : Derives Δ3 (F.rename R) :=
    of_eq (SourceAlgebra.rename_comp F te d) (lift3 (move2 h))
  have hw3 := of_eq (omega_rename _ _) (move3 hw)
  have hN3 : Derives Δ3 (SyntaxNodeSyntax.constructor 0 0 (R w) Fin.elim0 (R N)) :=
    of_eq (by simp only [SyntaxNodeSyntax.constructor_rename, SyntaxAtomSyntax.zero_map]) (move3 hN)
  have hM3 := of_eq (substituted_rename _ _ _ _ _ _ _ _ _ _) (lift3 (.conjL (.conjR hX)))
  have hO3 := Derives.conjL (.conjR hY)
  have hSubN := Derives.conjR (.conjR hY)
  have heq := SyntaxMixedFormulaNullary.unique hZ4 false (R w) (d (e (v 2))) (d (e (v 3)))
    (d (e (v 0))) (R f) (d (e (v 1))) (R b) (R N) (y 1) hw3 hN3 hSubN
  have hMid3 := SyntaxMixedFormulaLogicalSubst.binary_y 0 (R w) (y 0) (y 1) (d (x 1)) (R N) heq (.conjL hY)
  have hl3 := of_eq (SyntaxCodedMixedBinderSyntax.lifted_rename _ _ _ _ _ _ _ _ _ _ _ _)
    (of_eq (SourceAlgebra.rename_comp _ e d) (lift3 (lift2 (.conjL hLift))))
  have hs3 := Derives.conjR (.conjR (SyntaxCodedMixedBinderTyping.input_of_lifted
    (R w) (R D) (R S) (R A) (R f) (R z) (R b) (d (e (v 0))) (d (e (v 1))) (d (e (v 2))) (d (e (v 3))) hl3))
  have hEx2 := of_eq (singleCode_rename _ _ _ _ _) (lift1 (.conjL hEx))
  have hEx3 := of_eq (singleCode_rename _ _ _ _ _) (lift2 hEx2)
  have hEx4 := of_eq (singleCode_rename _ _ _ _ _) (lift3 hEx3)
  have hBody3 := of_eq (binaryCode_rename _ _ _ _ _ _) (lift3 (.conjL hX))
  have hMT := SyntaxMixedFormulaJudgment.target_type _ _ _ _ _ _ _ _ _ hM3
  have hOT := SyntaxMixedFormulaJudgment.target_type _ _ _ _ _ _ _ _ _ hO3
  have hNT := FormulaCodeTransport.code_root (R w) (y 1) (d (e (v 1))) (R b) (R N) heq
    (SyntaxMixedFormulaJudgment.target_type _ _ _ _ _ _ _ _ _ hSubN)
  exact of_eq (congrArg (fun F => F.rename d) (SourceAlgebra.rename_comp out t e)).symm
    (of_eq (SourceAlgebra.rename_comp out te d).symm
      (use R (d (e (v 1))) (d (e (s (u 0)))) (d (x 0)) (d (x 1)) (y 0) hZ4 move3 hs3
        hEx4 hBody3 hMid3 hMT hOT hNT))

end OrderQueries

section FalsumElimination

open SyntaxLogicalSyntax (singleCode singleCode_rename binaryCode_rename)
open InternalProofConjunction (proved proved_rename)
open FormulaCodeSyntax (formulaCode_rename)
attribute [local irreducible] NaturalRecursionSyntax.matrix
set_option maxHeartbeats 1200000

private theorem with_binary_formula {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (imp : Bool) (w b f X Y : Fin m) (hw : Derives Γ (omega w))
    (hX : Derives Γ (formulaCode w X b f)) (hY : Derives Γ (formulaCode w Y b f))
    (out : Formula m)
    (use : ∀ {l} {Δ : Context l} (r : Fin m → Fin l) (C : Fin l), ZFContext.Evidence Δ →
      (∀ {F : Formula m}, Derives Γ F → Derives Δ (F.rename r)) →
      Derives Δ (binaryCode (if imp then 2 else 0) (r w) (r X) (r Y) C) →
      Derives Δ (formulaCode (r w) C (r b) (r f)) →
      Derives Δ (out.rename r)) : Derives Γ out := by
  let tag := SyntaxLogicalSyntax.binaryTag (if imp then 2 else 0)
  let xs := SyntaxAtomSyntax.two X Y
  have hNat := SyntaxForestSyntax.intro_inputs 2 w xs
    (fun i => Fin.cases (.conjL (FormulaCodeProperties.guards w X b f hX))
      (fun j => Fin.cases (.conjL (FormulaCodeProperties.guards w Y b f hY)) (fun q => Fin.elim0 q) j) i)
  have hCtx := Derives.conjR (FormulaCodeProperties.guards w X b f hX)
  have hTypes : Derives Γ (FormulaCodeBranchSyntax.binaryTypes w b f X Y) :=
    .conjI hCtx (.conjI hX hY)
  have law : Derives Γ (FormulaCodeConstructSyntax.law 2 tag w xs b f) := by
    cases imp
    · exact FormulaCodeConstructors.binary0_law hZ w b f X Y hw hTypes
    · exact FormulaCodeConstructors.binary2_law hZ w b f X Y hw hTypes
  have he := FormulaCodeConstruct.actual_fiber hZ 2 tag w xs b f hw hNat law
  refine eliminate_objects hZ 1 (fun r v =>
    (Formula.mem (v 0) (r w)).conj (FormulaCodeConstructSyntax.typedAt 2 tag (r w)
      (fun i => r (xs i)) (v 0) (r b) (r f)))
    (FormulaCodeConstruct.exists_of_fiber 2 tag w xs b f he) out ?_
  intro l Δ r v hZ1 lift hc
  have hc0 := of_eq (congrArg (fun fields => SyntaxNodeSyntax.constructor 2 tag (r w) fields (v 0))
    (SyntaxAtomSyntax.two_map X Y r)) (.conjL (.conjR hc))
  exact use r (v 0) hZ1 lift hc0 (.conjR (.conjR hc))

private theorem with_opened_operand {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z b A B t F : Fin m) (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hA : Derives Γ (successor A z)) (hB : Derives Γ (successor B b))
    (hf : Derives Γ (SyntaxVariableSyntax.code false w z t))
    (ht : Derives Γ (SyntaxTermSyntax.term w z B t))
    (hF : Derives Γ (formulaCode w F A b))
    (out : Formula m)
    (use : ∀ {l} {Δ : Context l} (r : Fin m → Fin l) (V : Fin l), ZFContext.Evidence Δ →
      (∀ {P : Formula m}, Derives Γ P → Derives Δ (P.rename r)) →
      Derives Δ (SyntaxTopFormulaSyntax.abstracted (r w) (r z) (r b) (r A) (r B) V (r F)) →
      Derives Δ (formulaCode (r w) V (r z) (r B)) →
      Derives Δ (out.rename r)) : Derives Γ out := by
  let E := SyntaxWeakenFreeSyntax.weakened w.castSucc A.castSucc b.castSucc B.castSucc F.castSucc (Fin.last m)
  let Δ := Context.add E (Context.image Formula.raise Γ)
  have he : Derives Γ (.ex E) :=
    SyntaxWeakenFreeOutput.exists_output hZ w A b B F hw (.conjI hF hB)
  apply Derives.exE (p := E) he
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw E)
  have hA1 := of_eq (successor_rename A z Fin.castSucc) (under hA E)
  have ht1 := of_eq (SyntaxTermSyntax.term_rename w z B t Fin.castSucc) (under ht E)
  have hUT := SyntaxWeakenFreeOutput.target_type w.castSucc A.castSucc b.castSucc B.castSucc F.castSucc
    (Fin.last m) hE
  let P := instantiated w.castSucc.castSucc z.castSucc.castSucc B.castSucc.castSucc A.castSucc.castSucc
    t.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
  let Ξ := Context.add P (Context.image Formula.raise Δ)
  have hp : Derives Δ (.ex P) := SyntaxTopFormulaExistence.instantiate_exists
    (ZFContext.under hZ E) w.castSucc z.castSucc B.castSucc A.castSucc t.castSucc (Fin.last m)
    hw1 (.conjI (.conjI ht1 hA1) hUT)
  apply Derives.exE (p := P) hp
  have hP : Derives Ξ P := .hyp (Or.inl rfl)
  let R : Fin m → Fin (m+2) := fun i => i.castSucc.castSucc
  have move {F : Formula m} (h : Derives Γ F) : Derives Ξ (F.rename R) :=
    of_eq (SourceAlgebra.rename_comp F Fin.castSucc Fin.castSucc) (under (under h E) P)
  have hw2 := of_eq (omega_rename w R) (move hw)
  have hz2 := of_eq (empty_rename z R) (move hz)
  have hA2 := of_eq (successor_rename A z R) (move hA)
  have hf2 := of_eq (SyntaxVariableSyntax.code_rename false w z t R) (move hf)
  have hE2 := of_eq (SyntaxWeakenFreeSyntax.weakened_rename w.castSucc A.castSucc b.castSucc B.castSucc F.castSucc
    (Fin.last m) Fin.castSucc) (under hE P)
  have hIn : Derives Ξ (ForcingFreshOpeningInverse.input (R w) (R z) (R b) (R A) (R B) (R t)
      (R F) (Fin.last m).castSucc (Fin.last (m+1))) :=
    .conjI hw2 (.conjI hz2 (.conjI hA2 (.conjI hf2 (.conjI hE2 hP))))
  have hZ2 := ZFContext.under (ZFContext.under hZ E) P
  have ha := ForcingFreshOpeningInverse.derive hZ2 (R w) (R z) (R b) (R A) (R B) (R t)
    (R F) (Fin.last m).castSucc (Fin.last (m+1)) hIn
  have hV := SyntaxTopFormulaTyping.instantiate_target_type (R w) (R z) (R B) (R A) (R t)
    (Fin.last m).castSucc (Fin.last (m+1)) hP
  exact of_eq (SourceAlgebra.rename_comp out Fin.castSucc Fin.castSucc).symm
    (use R (Fin.last (m+1)) hZ2 move ha hV)

private theorem with_exists_elimination_axiom {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z b A B Open X N Branch All Tail : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hN : Derives Γ (formulaCode w N z b)) (hNB : Derives Γ (formulaCode w N A b))
    (hAllT : Derives Γ (formulaCode w All z b)) (hTailT : Derives Γ (formulaCode w Tail z b))
    (ha : Derives Γ (SyntaxTopFormulaSyntax.abstracted w z b A B Open X))
    (hBranch : Derives Γ (binaryCode 2 w X N Branch))
    (hAll : Derives Γ (singleCode 9 w Branch All))
    (hTail : Derives Γ (singleCode 10 w X Tail))
    (out : Formula m)
    (use : ∀ {l} {Δ : Context l} (r : Fin m → Fin l) (C Ax : Fin l),
      ZFContext.Evidence Δ → (∀ {P : Formula m}, Derives Γ P → Derives Δ (P.rename r)) →
      Derives Δ (binaryCode 2 (r w) (r Tail) (r N) C) →
      Derives Δ (formulaCode (r w) C (r z) (r b)) →
      Derives Δ (binaryCode 2 (r w) (r All) C Ax) →
      Derives Δ (proved test (r w) (r z) (r b) Ax) →
      Derives Δ (out.rename r)) : Derives Γ out := by
  refine with_binary_formula hZ true w z b Tail N hw hTailT hN out ?_
  intro l Δ r C hZ1 lift hc hCT
  have hw1 := of_eq (omega_rename _ _) (lift hw)
  have hAT := of_eq (formulaCode_rename _ _ _ _ _) (lift hAllT)
  refine with_binary_formula hZ1 true (r w) (r z) (r b) (r All) C hw1 hAT hCT (out.rename r) ?_
  intro l1 Δ1 s Ax hZ2 lift1 hAx _
  let R := s ∘ r
  have move {P : Formula m} (h : Derives Γ P) : Derives Δ1 (P.rename R) :=
    of_eq (SourceAlgebra.rename_comp P r s) (lift1 (lift h))
  have hw2 := of_eq (omega_rename _ _) (move hw)
  have hz2 := of_eq (empty_rename _ _) (move hz)
  have hc2 := of_eq (binaryCode_rename _ _ _ _ _ _) (lift1 hc)
  have hProof := InternalProofTemplates.exists_elimination_axiom hZ2 test
    (R w) (R z) (R b) (R A) (R B) (R Open) (R X) (R N) (R Branch) (R All) (R Tail) (s C) Ax
    hw2 hz2 (of_eq (SyntaxTopFormulaSyntax.abstracted_rename _ _ _ _ _ _ _ _) (move ha))
    (of_eq (formulaCode_rename _ _ _ _ _) (move hN)) (of_eq (formulaCode_rename _ _ _ _ _) (move hNB))
    (of_eq (binaryCode_rename _ _ _ _ _ _) (move hBranch))
    (of_eq (singleCode_rename _ _ _ _ _) (move hAll))
    (of_eq (singleCode_rename _ _ _ _ _) (move hTail)) hc2 hAx
  exact of_eq (SourceAlgebra.rename_comp out r s).symm
    (use R (s C) Ax hZ2 move hc2 (of_eq (formulaCode_rename _ _ _ _ _) (lift1 hCT)) hAx hProof)

private theorem eliminate_exists_from_all {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z b A B Open X N Branch All Tail : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hN : Derives Γ (formulaCode w N z b)) (hNB : Derives Γ (formulaCode w N A b))
    (hAllT : Derives Γ (formulaCode w All z b)) (hTailT : Derives Γ (formulaCode w Tail z b))
    (ha : Derives Γ (SyntaxTopFormulaSyntax.abstracted w z b A B Open X))
    (hBranch : Derives Γ (binaryCode 2 w X N Branch))
    (hAll : Derives Γ (singleCode 9 w Branch All))
    (hTail : Derives Γ (singleCode 10 w X Tail))
    (hp : Derives Γ (proved test w z b All)) : Derives Γ (implication test w z b Tail N) := by
  refine with_exists_elimination_axiom hZ w z b A B Open X N Branch All Tail
    hw hz hN hNB hAllT hTailT ha hBranch hAll hTail (implication test w z b Tail N) ?_
  intro l Δ r C Ax hZ1 lift hc hCT hAx hProof
  have hResult := InternalProofConjunction.modus_ponens hZ1 test (r w) (r z) (r b) (r All) C Ax
    (of_eq (omega_rename _ _) (lift hw)) (of_eq (empty_rename _ _) (lift hz))
    (of_eq (formulaCode_rename _ _ _ _ _) (lift hAllT)) hCT hAx
    (of_eq (proved_rename _ _ _ _ _ _) (lift hp)) hProof
  refine of_eq (implication_rename test _ _ _ _ _ r).symm ?_
  apply Derives.exI C
  exact of_eq (by simp only [Formula.instantiate, Formula.rename, SyntaxNodeSyntax.constructor_rename,
    SyntaxAtomSyntax.two_map, proved_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]; rfl)
    (.conjI hc hResult)

set_option maxHeartbeats 800000 in
/-- Discharge an actual opened existential under the outer background.
The conclusion is abstracted back to its original scope before elimination. -/
theorem witness_discharge {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z b A B G Extra Body Bound Tail Local Result Raised : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hG : Derives Γ (formulaCode w G z b))
    (hWeak : Derives Γ (SyntaxWeakenFreeSyntax.weakened w z b B G Extra))
    (ha : Derives Γ (SyntaxTopFormulaSyntax.abstracted w z b A B Body Bound))
    (he : Derives Γ (singleCode 10 w Bound Tail))
    (hLocal : Derives Γ (binaryCode 0 w Extra Body Local))
    (hResult : Derives Γ (formulaCode w Result z b))
    (hResultBound : Derives Γ (formulaCode w Result A b))
    (hRaised : Derives Γ (formulaCode w Raised z B))
    (hAbsResult : Derives Γ (SyntaxTopFormulaSyntax.abstracted w z b A B Raised Result))
    (pTail : Derives Γ (implication test w z b G Tail))
    (pResult : Derives Γ (implication test w z B Local Raised)) :
    Derives Γ (implication test w z b G Result) := by
  have hEnv := SyntaxTopFormulaTyping.abstract_environment w z b A B Body Bound ha
  have hA := Derives.conjL (.conjR hEnv)
  have hBody := SyntaxTopFormulaTyping.abstract_source_type hZ w z b A B Body Bound hw ha
  have hBound := SyntaxTopFormulaTyping.abstract_target_type w z b A B Body Bound ha
  have hTail := Derives.impE (.conjR (FormulaCodeKnownLogical.quantified_iff hZ false w z b Bound Tail A hw he hA))
    (.conjI (.conjL hEnv) hBound)
  have hCtxNew := Derives.conjR (FormulaCodeProperties.guards w Body z B hBody)
  have hExtra := SyntaxWeakenFreeOutput.target_type w z b B G Extra hWeak
  have hAbsG := ForcingFreshBackground.derive hZ w z b A B G Extra
    (.conjI hw (.conjI hz (.conjI hA hWeak)))
  have hCurry := InternalProofCurry.from_implication hZ test w z B Extra Body Local Raised
    hw hz hExtra hBody hRaised hLocal pResult
  let out := implication test w z b G Result
  refine eliminate_objects hZ 1 (fun r u =>
    (binaryCode 2 (r w) (r Body) (r Raised) (u 0)).conj (implication test (r w) (r z) (r B) (r Extra) (u 0)))
    hCurry out ?_
  intro l Δ r u hZ1 lift hF
  have hw1 := of_eq (omega_rename _ _) (lift hw)
  refine with_binary_formula hZ1 true (r w) (r A) (r b) (r Bound) (r Result) hw1
    (of_eq (formulaCode_rename _ _ _ _ _) (lift hBound))
    (of_eq (formulaCode_rename _ _ _ _ _) (lift hResultBound)) (out.rename r) ?_
  intro l1 Δ1 s Branch hZ2 move hBranch hBranchT
  let R := s ∘ r
  let F := s (u 0)
  have carry {P : Formula m} (h : Derives Γ P) : Derives Δ1 (P.rename R) :=
    of_eq (SourceAlgebra.rename_comp P r s) (move (lift h))
  have hw2 := of_eq (omega_rename _ _) (carry hw)
  have hz2 := of_eq (empty_rename _ _) (carry hz)
  have hFCode := of_eq (binaryCode_rename 2 _ _ _ _ s) (move (.conjL hF))
  have hFT := Derives.impE (.conjR (FormulaCodeKnownLogical.binary2_iff hZ2 (R w) (R z) (R B)
    (R Body) (R Raised) F hw2 hFCode))
    (.conjI (of_eq (SyntaxTermSyntax.contexts_rename _ _ _ _) (carry hCtxNew))
      (.conjI (of_eq (formulaCode_rename _ _ _ _ _) (carry hBody))
        (of_eq (formulaCode_rename _ _ _ _ _) (carry hRaised))))
  have hAbsF := Derives.impE (.conjR (SyntaxTopFormulaLogicalEndpoints.abstract_binary_iff hZ2 2
    (R w) (R z) (R b) (R A) (R B) F Branch (R Body) (R Raised) (R Bound) (R Result) hw2
    (.conjI (of_eq (SyntaxTopEnvironmentSyntax.abstractInput_rename _ _ _ _ _ _) (carry hEnv)) hFT)
    hFCode hBranch))
    (.conjI (of_eq (SyntaxTopFormulaSyntax.abstracted_rename _ _ _ _ _ _ _ _) (carry ha))
      (of_eq (SyntaxTopFormulaSyntax.abstracted_rename _ _ _ _ _ _ _ _) (carry hAbsResult)))
  have hAll := ForcingProofUniversal.generalize_body hZ2 test (R w) (R z) (R b) (R A) (R B)
    (R G) (R Extra) (R Body) (R Raised) F Branch hw2 hz2
    (of_eq (formulaCode_rename _ _ _ _ _) (carry hG))
    (of_eq (SyntaxTopFormulaSyntax.abstracted_rename _ _ _ _ _ _ _ _) (carry hAbsG))
    (.conjI hFCode (.conjI hFT (.conjI
      (of_eq (implication_rename _ _ _ _ _ _ s) (move (.conjR hF))) (.conjI hAbsF hBranchT))))
  apply of_eq (SourceAlgebra.rename_comp out r s).symm
  refine eliminate_objects hZ2 1 (fun t x => (singleCode 9 (t (R w)) (t Branch) (x 0)).conj
    (implication test (t (R w)) (t (R z)) (t (R b)) (t (R G)) (x 0))) hAll (out.rename R) ?_
  intro l2 Δ2 t x hZ3 move2 hQuant
  let S := t ∘ R
  have carry2 {P : Formula m} (h : Derives Γ P) : Derives Δ2 (P.rename S) :=
    of_eq (SourceAlgebra.rename_comp P R t) (move2 (carry h))
  have hw3 := of_eq (omega_rename _ _) (carry2 hw)
  have hz3 := of_eq (empty_rename _ _) (carry2 hz)
  have hAllT := Derives.impE (.conjR (FormulaCodeKnownLogical.quantified_iff hZ3 true
    (S w) (S z) (S b) (t Branch) (x 0) (S A) hw3 (.conjL hQuant)
    (of_eq (successor_rename _ _ _) (carry2 hA))))
    (.conjI (of_eq (SyntaxTermSyntax.contexts_rename _ _ _ _) (carry2 (.conjL hEnv)))
      (of_eq (formulaCode_rename _ _ _ _ _) (move2 hBranchT)))
  apply of_eq (SourceAlgebra.rename_comp out R t).symm
  refine with_exists_elimination_axiom hZ3 (S w) (S z) (S b) (S A) (S B) (S Body) (S Bound) (S Result)
    (t Branch) (x 0) (S Tail) hw3 hz3
    (of_eq (formulaCode_rename _ _ _ _ _) (carry2 hResult))
    (of_eq (formulaCode_rename _ _ _ _ _) (carry2 hResultBound)) hAllT
    (of_eq (formulaCode_rename _ _ _ _ _) (carry2 hTail))
    (of_eq (SyntaxTopFormulaSyntax.abstracted_rename _ _ _ _ _ _ _ _) (carry2 ha))
    (of_eq (binaryCode_rename _ _ _ _ _ _) (move2 hBranch)) (.conjL hQuant)
    (of_eq (singleCode_rename _ _ _ _ _) (carry2 he)) (out.rename S) ?_
  intro l3 Δ3 v C Ax hZ4 move3 hC hCT hAx hpAx
  let T := v ∘ S
  have carry3 {P : Formula m} (h : Derives Γ P) : Derives Δ3 (P.rename T) :=
    of_eq (SourceAlgebra.rename_comp P S v) (move3 (carry2 h))
  have pAx : Derives Δ3 (implication test (T w) (T z) (T b) (v (x 0)) C) := by
    apply Derives.exI Ax
    exact of_eq (by simp only [Formula.instantiate, Formula.rename, SyntaxNodeSyntax.constructor_rename,
      SyntaxAtomSyntax.two_map, proved_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]; rfl)
      (.conjI hAx hpAx)
  have hw4 := of_eq (omega_rename _ _) (carry3 hw)
  have hz4 := of_eq (empty_rename _ _) (carry3 hz)
  have hG4 := of_eq (formulaCode_rename _ _ _ _ _) (carry3 hG)
  have pC := ForcingRelationGuardProof.chain hZ4 test (T w) (T z) (T b) (T G) (v (x 0)) C
    hw4 hz4 hG4 (of_eq (formulaCode_rename _ _ _ _ _) (move3 hAllT)) hCT
    (of_eq (implication_rename _ _ _ _ _ _ _) (move3 (.conjR hQuant))) pAx
  exact of_eq (SourceAlgebra.rename_comp out S v).symm
    (of_eq (implication_rename test _ _ _ _ _ T).symm
      (ForcingNegMemberProof.discharge hZ4 test (T w) (T z) (T b) (T G) (T Tail) (T Result) C
        hw4 hz4 hG4 hCT hC (of_eq (implication_rename _ _ _ _ _ _ _) (carry3 pTail)) pC))

set_option maxHeartbeats 800000 in
/-- Discharge the actual opened existential after deriving falsum from its
body together with the weakened outer background. -/
theorem negative_witness_discharge {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z b A B G Extra Body Bound Tail Local Bot : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hG : Derives Γ (formulaCode w G z b))
    (hWeak : Derives Γ (SyntaxWeakenFreeSyntax.weakened w z b B G Extra))
    (ha : Derives Γ (SyntaxTopFormulaSyntax.abstracted w z b A B Body Bound))
    (he : Derives Γ (singleCode 10 w Bound Tail))
    (hLocal : Derives Γ (binaryCode 0 w Extra Body Local))
    (hBot : Derives Γ (SyntaxNodeSyntax.constructor 0 0 w Fin.elim0 Bot))
    (pTail : Derives Γ (implication test w z b G Tail))
    (pBot : Derives Γ (implication test w z B Local Bot)) :
    Derives Γ (implication test w z b G Bot) := by
  have hEnv := SyntaxTopFormulaTyping.abstract_environment w z b A B Body Bound ha
  have bot_type (a b : Fin m) (hc : Derives Γ (SyntaxTermSyntax.contexts w a b)) :
      Derives Γ (formulaCode w Bot a b) :=
    .impE (.conjR (FormulaCodeKnownAtomic.nullary_iff hZ false w a b Bot hw hBot)) hc
  have hBotOld := bot_type z b (.conjL hEnv)
  have hBound := SyntaxTopFormulaTyping.abstract_target_type w z b A B Body Bound ha
  have hBotBound := bot_type A b (.conjR (FormulaCodeProperties.guards w Bound A b hBound))
  have hBody := SyntaxTopFormulaTyping.abstract_source_type hZ w z b A B Body Bound hw ha
  have hCtxNew := Derives.conjR (FormulaCodeProperties.guards w Body z B hBody)
  have hBotNew := bot_type z B hCtxNew
  have hAbsBot := Derives.impE (.conjR (SyntaxTopFormulaLogicalEndpoints.abstract_nullary_iff hZ false
    w z b A B Bot Bot hw (.conjI hEnv hBotNew) hBot)) (.eqRefl Bot)
  exact witness_discharge hZ w z b A B G Extra Body Bound Tail Local Bot Bot
    hw hz hG hWeak ha he hLocal hBotOld hBotBound hBotNew hAbsBot pTail pBot

private theorem eliminate_exists_from_body {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z b A B Open X OpenedN N Tail : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hN : Derives Γ (formulaCode w N z b)) (hNB : Derives Γ (formulaCode w N A b))
    (hNF : Derives Γ (formulaCode w OpenedN z B))
    (ha : Derives Γ (SyntaxTopFormulaSyntax.abstracted w z b A B Open X))
    (haN : Derives Γ (SyntaxTopFormulaSyntax.abstracted w z b A B OpenedN N))
    (hTail : Derives Γ (singleCode 10 w X Tail))
    (hP : Derives Γ (implication test w z B Open OpenedN)) :
    Derives Γ (implication test w z b Tail N) := by
  let out := implication test w z b Tail N
  have hEnv := SyntaxTopFormulaTyping.abstract_environment w z b A B Open X ha
  have hA := Derives.conjL (.conjR hEnv)
  have hX := SyntaxTopFormulaTyping.abstract_target_type w z b A B Open X ha
  have hXT := SyntaxTopFormulaTyping.abstract_source_type hZ w z b A B Open X hw ha
  have hTailT := Derives.impE (.conjR (FormulaCodeKnownLogical.quantified_iff hZ false w z b X Tail A hw hTail hA))
    (.conjI (.conjL hEnv) hX)
  refine with_binary_formula hZ true w A b X N hw hX hNB out ?_
  intro l Δ r Branch hZ1 lift hc hBT
  refine of_eq (implication_rename test w z b Tail N r).symm ?_
  refine eliminate_objects hZ1 1 (fun s u =>
    (binaryCode 2 (s (r w)) (s (r Open)) (s (r OpenedN)) (u 0)).conj
      (proved test (s (r w)) (s (r z)) (s (r B)) (u 0)))
    (of_eq (implication_rename test w z B Open OpenedN r) (lift hP)) (implication test (r w) (r z) (r b) (r Tail) (r N)) ?_
  intro l1 Δ1 s u hZ2 lift1 hU
  let R := s ∘ r
  have move {P : Formula m} (h : Derives Γ P) : Derives Δ1 (P.rename R) :=
    of_eq (SourceAlgebra.rename_comp P r s) (lift1 (lift h))
  have hw2 := of_eq (omega_rename _ _) (move hw)
  have hz2 := of_eq (empty_rename _ _) (move hz)
  have hXT2 := of_eq (formulaCode_rename _ _ _ _ _) (move hXT)
  have hN2 := of_eq (formulaCode_rename _ _ _ _ _) (move hNF)
  have hAbs2 := of_eq (SyntaxTopFormulaSyntax.abstracted_rename _ _ _ _ _ _ _ _) (move ha)
  have hAbsN2 := of_eq (SyntaxTopFormulaSyntax.abstracted_rename _ _ _ _ _ _ _ _) (move haN)
  have hEnv2 := of_eq (SyntaxTopEnvironmentSyntax.abstractInput_rename _ _ _ _ _ _) (move hEnv)
  have hCtx := Derives.conjR (FormulaCodeProperties.guards _ _ _ _ hXT2)
  have hUT := Derives.impE (.conjR (FormulaCodeKnownLogical.binary2_iff hZ2
    (R w) (R z) (R B) (R Open) (R OpenedN) (u 0) hw2 (.conjL hU))) (.conjI hCtx (.conjI hXT2 hN2))
  have hc2 := of_eq (binaryCode_rename _ _ _ _ _ _) (lift1 hc)
  have hAbs := Derives.impE (.conjR (SyntaxTopFormulaLogicalEndpoints.abstract_binary_iff hZ2 2
    (R w) (R z) (R b) (R A) (R B) (u 0) (s Branch) (R Open) (R OpenedN) (R X) (R N)
    hw2 (.conjI hEnv2 hUT) (.conjL hU) hc2)) (.conjI hAbs2 hAbsN2)
  have hForall := InternalProofUniversal.generalize hZ2 test
    (R w) (R z) (R b) (R A) (R B) (u 0) (s Branch) hw2 hz2 hAbs (.conjR hU)
  refine of_eq (implication_rename test (r w) (r z) (r b) (r Tail) (r N) s).symm ?_
  refine eliminate_objects hZ2 1 (fun t q =>
    (singleCode 9 (t (R w)) (t (s Branch)) (q 0)).conj
      (proved test (t (R w)) (t (R z)) (t (R b)) (q 0))) hForall (implication test (R w) (R z) (R b) (R Tail) (R N)) ?_
  intro l2 Δ2 t q hZ3 lift2 hAll
  let S := t ∘ R
  have move2 {P : Formula m} (h : Derives Γ P) : Derives Δ2 (P.rename S) :=
    of_eq (SourceAlgebra.rename_comp P R t) (lift2 (move h))
  have hw3 := of_eq (omega_rename _ _) (move2 hw)
  have hz3 := of_eq (empty_rename _ _) (move2 hz)
  have hAllT := Derives.impE (.conjR (FormulaCodeKnownLogical.quantified_iff hZ3 true
    (S w) (S z) (S b) (t (s Branch)) (q 0) (S A) hw3 (.conjL hAll)
    (of_eq (successor_rename _ _ _) (move2 hA))))
    (.conjI (of_eq (SyntaxTermSyntax.contexts_rename _ _ _ _) (move2 (.conjL hEnv)))
      (of_eq (formulaCode_rename _ _ _ _ _) (of_eq (SourceAlgebra.rename_comp _ s t) (lift2 (lift1 hBT)))))
  exact of_eq (implication_rename test (R w) (R z) (R b) (R Tail) (R N) t).symm
    (eliminate_exists_from_all hZ3 (S w) (S z) (S b) (S A) (S B) (S Open) (S X) (S N) (t (s Branch)) (q 0) (S Tail)
      hw3 hz3 (of_eq (formulaCode_rename _ _ _ _ _) (move2 hN)) (of_eq (formulaCode_rename _ _ _ _ _) (move2 hNB))
      hAllT (of_eq (formulaCode_rename _ _ _ _ _) (move2 hTailT))
      (of_eq (SyntaxTopFormulaSyntax.abstracted_rename _ _ _ _ _ _ _ _) (move2 ha))
      (of_eq (binaryCode_rename _ _ _ _ _ _) (lift2 hc2)) (.conjL hAll)
      (of_eq (singleCode_rename _ _ _ _ _) (move2 hTail)) (.conjR hAll))

private theorem falsum_from_open_parts {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z b A B MO OO M O N Y X Tail : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (he : Derives Γ (SyntaxTopEnvironmentSyntax.abstractInput w z b A B))
    (hM : Derives Γ (SyntaxTopFormulaSyntax.abstracted w z b A B MO M))
    (hO : Derives Γ (SyntaxTopFormulaSyntax.abstracted w z b A B OO O))
    (hMT : Derives Γ (formulaCode w MO z B)) (hOT : Derives Γ (formulaCode w OO z B))
    (hN : Derives Γ (SyntaxNodeSyntax.constructor 0 0 w Fin.elim0 N))
    (hN0 : Derives Γ (formulaCode w N z b)) (hNB : Derives Γ (formulaCode w N A b))
    (hN1 : Derives Γ (formulaCode w N z B))
    (hY : Derives Γ (binaryCode 0 w O N Y)) (hX : Derives Γ (binaryCode 0 w M Y X))
    (hTail : Derives Γ (singleCode 10 w X Tail)) : Derives Γ (implication test w z b Tail N) := by
  have hAbsN := Derives.impE (.conjR (SyntaxTopFormulaLogicalEndpoints.abstract_nullary_iff hZ false
    w z b A B N N hw (.conjI he hN1) hN)) (.eqRefl N)
  refine with_binary_formula hZ false w z B OO N hw hOT hN1 _ ?_
  intro l Δ r V hZ1 lift hV hVT
  have hw1 := of_eq (omega_rename _ _) (lift hw)
  have he1 := of_eq (SyntaxTopEnvironmentSyntax.abstractInput_rename _ _ _ _ _ _) (lift he)
  have hAbsN1 := of_eq (SyntaxTopFormulaSyntax.abstracted_rename _ _ _ _ _ _ _ _) (lift hAbsN)
  have hAbsV := Derives.impE (.conjR (SyntaxTopFormulaLogicalEndpoints.abstract_binary_iff hZ1 0
    (r w) (r z) (r b) (r A) (r B) V (r Y) (r OO) (r N) (r O) (r N) hw1
    (.conjI he1 hVT) hV (of_eq (binaryCode_rename _ _ _ _ _ _) (lift hY))))
    (.conjI (of_eq (SyntaxTopFormulaSyntax.abstracted_rename _ _ _ _ _ _ _ _) (lift hO)) hAbsN1)
  refine of_eq (implication_rename test w z b Tail N r).symm ?_
  refine with_binary_formula hZ1 false (r w) (r z) (r B) (r MO) V hw1
    (of_eq (formulaCode_rename _ _ _ _ _) (lift hMT)) hVT _ ?_
  intro l1 Δ1 s U hZ2 lift1 hU hUT
  let R := s ∘ r
  have move {P : Formula m} (h : Derives Γ P) : Derives Δ1 (P.rename R) :=
    of_eq (SourceAlgebra.rename_comp P r s) (lift1 (lift h))
  have hw2 := of_eq (omega_rename _ _) (move hw)
  have hz2 := of_eq (empty_rename _ _) (move hz)
  have hVT2 := of_eq (formulaCode_rename _ _ _ _ _) (lift1 hVT)
  have hNT2 := of_eq (formulaCode_rename _ _ _ _ _) (move hN1)
  have hAbsU := Derives.impE (.conjR (SyntaxTopFormulaLogicalEndpoints.abstract_binary_iff hZ2 0
    (R w) (R z) (R b) (R A) (R B) U (R X) (R MO) (s V) (R M) (R Y) hw2
    (.conjI (of_eq (SyntaxTopEnvironmentSyntax.abstractInput_rename _ _ _ _ _ _) (move he)) hUT)
    hU (of_eq (binaryCode_rename _ _ _ _ _ _) (move hX))))
    (.conjI (of_eq (SyntaxTopFormulaSyntax.abstracted_rename _ _ _ _ _ _ _ _) (move hM))
      (of_eq (SyntaxTopFormulaSyntax.abstracted_rename _ _ _ _ _ _ _ _) (lift1 hAbsV)))
  have h1 := ForcingRelationGuardProof.project hZ2 test true (R w) (R z) (R B) (R MO) (s V) U hw2 hz2
    (of_eq (formulaCode_rename _ _ _ _ _) (move hMT)) hVT2 hUT hU
  have h2 := ForcingRelationGuardProof.project hZ2 test true (R w) (R z) (R B) (R OO) (R N) (s V) hw2 hz2
    (of_eq (formulaCode_rename _ _ _ _ _) (move hOT)) hNT2 hVT2
    (of_eq (binaryCode_rename _ _ _ _ _ _) (lift1 hV))
  have hP := ForcingRelationGuardProof.chain hZ2 test (R w) (R z) (R B) U (s V) (R N) hw2 hz2 hUT hVT2 hNT2 h1 h2
  exact of_eq (implication_rename test (r w) (r z) (r b) (r Tail) (r N) s).symm
    (eliminate_exists_from_body hZ2 (R w) (R z) (R b) (R A) (R B) U (R X) (R N) (R N) (R Tail) hw2 hz2
      (of_eq (formulaCode_rename _ _ _ _ _) (move hN0)) (of_eq (formulaCode_rename _ _ _ _ _) (move hNB))
      hNT2 hAbsU (of_eq (SyntaxTopFormulaSyntax.abstracted_rename _ _ _ _ _ _ _ _) (move hAbsN))
      (of_eq (singleCode_rename _ _ _ _ _) (move hTail)) hP)

private theorem falsum_at_fresh_term {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z b A B t M O N Y X Tail : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (he : Derives Γ (SyntaxTopEnvironmentSyntax.abstractInput w z b A B))
    (hf : Derives Γ (SyntaxVariableSyntax.code false w z t)) (ht : Derives Γ (SyntaxTermSyntax.term w z B t))
    (hM : Derives Γ (formulaCode w M A b)) (hO : Derives Γ (formulaCode w O A b))
    (hN : Derives Γ (SyntaxNodeSyntax.constructor 0 0 w Fin.elim0 N))
    (hN0 : Derives Γ (formulaCode w N z b)) (hNB : Derives Γ (formulaCode w N A b))
    (hY : Derives Γ (binaryCode 0 w O N Y)) (hX : Derives Γ (binaryCode 0 w M Y X))
    (hTail : Derives Γ (singleCode 10 w X Tail)) : Derives Γ (implication test w z b Tail N) := by
  have hA := Derives.conjL (.conjR he)
  have hB := Derives.conjR (.conjR he)
  refine with_opened_operand hZ w z b A B t M hw hz hA hB hf ht hM _ ?_
  intro l Δ r MO hZ1 lift hAM hMT
  refine of_eq (implication_rename test w z b Tail N r).symm ?_
  refine with_opened_operand hZ1 (r w) (r z) (r b) (r A) (r B) (r t) (r O)
    (of_eq (omega_rename _ _) (lift hw)) (of_eq (empty_rename _ _) (lift hz))
    (of_eq (successor_rename _ _ _) (lift hA)) (of_eq (successor_rename _ _ _) (lift hB))
    (of_eq (SyntaxVariableSyntax.code_rename false _ _ _ _) (lift hf))
    (of_eq (SyntaxTermSyntax.term_rename _ _ _ _ _) (lift ht))
    (of_eq (formulaCode_rename _ _ _ _ _) (lift hO)) _ ?_
  intro l1 Δ1 s OO hZ2 lift1 hAO hOT
  let R := s ∘ r
  have move {P : Formula m} (h : Derives Γ P) : Derives Δ1 (P.rename R) :=
    of_eq (SourceAlgebra.rename_comp P r s) (lift1 (lift h))
  have hw2 := of_eq (omega_rename _ _) (move hw)
  have hz2 := of_eq (empty_rename _ _) (move hz)
  have hN2 : Derives Δ1 (SyntaxNodeSyntax.constructor 0 0 (R w) Fin.elim0 (R N)) :=
    of_eq (by simp only [SyntaxNodeSyntax.constructor_rename, SyntaxAtomSyntax.zero_map]) (move hN)
  have ht2 := of_eq (SyntaxTermSyntax.term_rename _ _ _ _ _) (move ht)
  have hN1 := Derives.impE (.conjR (FormulaCodeKnownAtomic.nullary_iff hZ2 false
    (R w) (R z) (R B) (R N) hw2 hN2)) (.conjL ht2)
  exact of_eq (implication_rename test (r w) (r z) (r b) (r Tail) (r N) s).symm
    (falsum_from_open_parts hZ2 (R w) (R z) (R b) (R A) (R B) (s MO) OO (R M) (R O)
      (R N) (R Y) (R X) (R Tail) hw2 hz2
      (of_eq (SyntaxTopEnvironmentSyntax.abstractInput_rename _ _ _ _ _ _) (move he))
      (of_eq (SyntaxTopFormulaSyntax.abstracted_rename _ _ _ _ _ _ _ _) (lift1 hAM)) hAO
      (of_eq (formulaCode_rename _ _ _ _ _) (lift1 hMT)) hOT hN2
      (of_eq (formulaCode_rename _ _ _ _ _) (move hN0)) (of_eq (formulaCode_rename _ _ _ _ _) (move hNB)) hN1
      (of_eq (binaryCode_rename _ _ _ _ _ _) (move hY)) (of_eq (binaryCode_rename _ _ _ _ _ _) (move hX))
      (of_eq (singleCode_rename _ _ _ _ _) (move hTail)))

private theorem falsum_from_body {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z b A M O N Y X Tail : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) (hA : Derives Γ (successor A z))
    (hN : Derives Γ (SyntaxNodeSyntax.constructor 0 0 w Fin.elim0 N))
    (hNB : Derives Γ (formulaCode w N A b))
    (hM : Derives Γ (formulaCode w M A b)) (hO : Derives Γ (formulaCode w O A b))
    (hY : Derives Γ (binaryCode 0 w O N Y)) (hX : Derives Γ (binaryCode 0 w M Y X))
    (hTail : Derives Γ (singleCode 10 w X Tail)) : Derives Γ (implication test w z b Tail N) := by
  let out := implication test w z b Tail N
  have hzN := SyntaxNumerals.range hZ 0 w z hw hz
  have hbN := Derives.conjR (.conjR (FormulaCodeProperties.guards w N A b hNB))
  have hCtx : Derives Γ (SyntaxTermSyntax.contexts w z b) := .conjI hzN hbN
  have hN0 := Derives.impE (.conjR (FormulaCodeKnownAtomic.nullary_iff hZ false w z b N hw hN)) hCtx
  refine eliminate_objects hZ 1 (fun r v => (Formula.mem (v 0) (r w)).conj (successor (v 0) (r b)))
    (.impE (OmegaSyntax.step_at w b (.conjL hw)) hbN) out ?_
  intro l Δ r v hZ1 lift hB
  have hw1 := of_eq (omega_rename _ _) (lift hw)
  have hz1 := of_eq (empty_rename _ _) (lift hz)
  have hzB := SyntaxIndexLiftOrder.zero_member hZ1 (r w) (r b) (v 0) (r z) hw1 (lift hbN) (.conjR hB) hz1
  have hFresh := SyntaxTerms.exists_at hZ1 false (r w) (r z) (v 0) (r z) hw1
    (.conjI (.conjI (lift hzN) (.conjL hB)) hzB)
  refine of_eq (implication_rename test w z b Tail N r).symm ?_
  refine eliminate_objects hZ1 1 (fun s u => (Formula.mem (u 0) (s (r w))).conj
    ((SyntaxVariableSyntax.code false (s (r w)) (s (r z)) (u 0)).conj
      (SyntaxTermSyntax.term (s (r w)) (s (r z)) (s (v 0)) (u 0)))) hFresh
    (implication test (r w) (r z) (r b) (r Tail) (r N)) ?_
  intro l1 Δ1 s u hZ2 lift1 hTerm
  let R := s ∘ r
  have move {P : Formula m} (h : Derives Γ P) : Derives Δ1 (P.rename R) :=
    of_eq (SourceAlgebra.rename_comp P r s) (lift1 (lift h))
  have he : Derives Δ1 (SyntaxTopEnvironmentSyntax.abstractInput (R w) (R z) (R b) (R A) (s (v 0))) :=
    .conjI (of_eq (SyntaxTermSyntax.contexts_rename _ _ _ _) (move hCtx))
      (.conjI (of_eq (successor_rename _ _ _) (move hA)) (of_eq (successor_rename _ _ _) (lift1 (.conjR hB))))
  have hN2 : Derives Δ1 (SyntaxNodeSyntax.constructor 0 0 (R w) Fin.elim0 (R N)) :=
    of_eq (by simp only [SyntaxNodeSyntax.constructor_rename, SyntaxAtomSyntax.zero_map]) (move hN)
  exact of_eq (implication_rename test (r w) (r z) (r b) (r Tail) (r N) s).symm
    (falsum_at_fresh_term hZ2 (R w) (R z) (R b) (R A) (s (v 0)) (u 0) (R M) (R O) (R N) (R Y) (R X) (R Tail)
      (of_eq (omega_rename _ _) (move hw)) (of_eq (empty_rename _ _) (move hz)) he (.conjL (.conjR hTerm)) (.conjR (.conjR hTerm))
      (of_eq (formulaCode_rename _ _ _ _ _) (move hM)) (of_eq (formulaCode_rename _ _ _ _ _) (move hO))
      hN2 (of_eq (formulaCode_rename _ _ _ _ _) (move hN0)) (of_eq (formulaCode_rename _ _ _ _ _) (move hNB))
      (of_eq (binaryCode_rename _ _ _ _ _ _) (move hY)) (of_eq (binaryCode_rename _ _ _ _ _ _) (move hX))
      (of_eq (singleCode_rename _ _ _ _ _) (move hTail)))

/-- The falsum case of the original density witness elimination. The same
instantiated existential and its original falsum are used in the output. -/
private theorem falsum_from_query {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z b D S A f Raw X Y M O N Tail : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hN : Derives Γ (SyntaxNodeSyntax.constructor 0 0 w Fin.elim0 N))
    (hcEx : Derives Γ (singleCode 10 w X Raw))
    (hcBody : Derives Γ (binaryCode 0 w M Y X))
    (hcMid : Derives Γ (binaryCode 0 w O N Y))
    (hq : Derives Γ (substituted w D S A f z b Raw Tail)) :
    Derives Γ (implication test w z b Tail N) := by
  apply with_falsum_tail hZ w z b D S A f Raw X Y M O N Tail hw hN hcEx hcBody hcMid hq
  intro l Δ r C X' M' Y' O' hZ1 lift hs hEx hBody hMid hMT hOT hNT
  have hN1 : Derives Δ (SyntaxNodeSyntax.constructor 0 0 (r w) Fin.elim0 (r N)) :=
    of_eq (by simp only [SyntaxNodeSyntax.constructor_rename, SyntaxAtomSyntax.zero_map]) (lift hN)
  exact of_eq (implication_rename test w z b Tail N r).symm
    (falsum_from_body hZ1 (r w) (r z) (r b) C M' O' (r N) Y' X' (r Tail)
      (of_eq (omega_rename _ _) (lift hw)) (of_eq (empty_rename _ _) (lift hz)) hs hN1 hNT hMT hOT hMid hBody hEx)

/-- Eliminate the falsum witness of the same selected density instance
whose member and order guards have already been discharged. -/
theorem falsum_from_density_records {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z a A B C f b L S K H D p G M O rM rO N Raw I U : Fin m)
    (shell : Fin 5 → Fin m) (u v x : Fin 4 → Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hN : Derives Γ (SyntaxNodeSyntax.constructor 0 0 w Fin.elim0 N))
    (hG : Derives Γ (formulaCode w G z b))
    (hShell : Derives Γ (ForcingDensityCode.shellData w a A B f M O rM rO N Raw shell))
    (hl : Derives Γ (SyntaxCodedMixedBinderSyntax.lifted w L S a f z b A C K H))
    (hD : Derives Γ (consCode w p L D))
    (hu : Derives Γ (ForcingRawModalBody.data w K H A f C b M O (shell 2) I U u))
    (hv : Derives Γ (ForcingDensityInstantiation.pointData w z b U p G (u 1) (u 2) (u 3) (u 0) v))
    (hx : Derives Γ (ForcingRawModalBody.data w (v 2) (v 3) (v 0) b z b (u 1) (u 2) (u 3) (u 0) (v 1) x))
    (hPoint : Derives Γ (implication test w z b G (x 3))) :
    Derives Γ (implication test w z b G N) := by
  have hInst := Derives.conjL (.conjR hv)
  have hCoded := Derives.conjL hInst
  have ht := Derives.conjL (SyntaxTopCodedEnvironmentTyping.instantiate_input w z b (v 0) p (v 2) (v 3) hCoded)
  have hlIn := SyntaxCodedMixedBinderTyping.input_of_lifted w L S a f z b A C K H hl
  have hCe := OmegaUniversal.successor_unique (v 0) C z (ZFContext.arithmetic hZ).base.extensionality
    (.conjL hv) (.conjR (.conjR hlIn))
  have hU : Derives Γ (substituted w K H A f C b (shell 2) (u 3)) :=
    .conjR (.conjR (.conjR hu))
  have hNative := SyntaxTopFormulaSyntax.intro_instantiated w z b (v 0) p (u 3) (x 3) (v 2) (v 3)
    hCoded (.conjR (.conjR (.conjR hx)))
  have hY := instance_scope w z b (v 0) C p (u 3) (x 3) hCe hNative
  have hRawType : Derives Γ (formulaCode w (shell 2) A f) := .conjR (.conjL (.conjR (.conjR hShell)))
  have hEx : Derives Γ (singleCode 10 w (shell 1) (shell 2)) := .conjL (.conjL (.conjR (.conjR hShell)))
  have hcBody : Derives Γ (binaryCode 0 w rM (shell 0) (shell 1)) := .conjL (.conjL (.conjR hShell))
  have hcMid : Derives Γ (binaryCode 0 w rO N (shell 0)) := .conjL (.conjL hShell)
  apply with_direct_query hZ w z a A C f b L S K H p D (shell 2) (u 3) (x 3)
    hw hz ht hl hD hRawType hU hY (implication test w z b G N)
  intro l Δ r hZ1 lift _ _ hq
  have hw1 := of_eq (omega_rename _ _) (lift hw)
  have hz1 := of_eq (empty_rename _ _) (lift hz)
  have hG1 := of_eq (formulaCode_rename _ _ _ _ _) (lift hG)
  have hN1 : Derives Δ (SyntaxNodeSyntax.constructor 0 0 (r w) Fin.elim0 (r N)) :=
    of_eq (by simp only [SyntaxNodeSyntax.constructor_rename, SyntaxAtomSyntax.zero_map]) (lift hN)
  have hNT := Derives.impE (.conjR (FormulaCodeKnownAtomic.nullary_iff hZ1 false (r w) (r z) (r b) (r N) hw1 hN1))
    (.conjR (FormulaCodeProperties.guards (r w) (r G) (r z) (r b) hG1))
  have hTailT := SyntaxMixedFormulaJudgment.target_type (r w) (r D) (r S) (r A) (r f) (r z) (r b)
    (r (shell 2)) (r (x 3)) hq
  have hFalsum := falsum_from_query hZ1 (r w) (r z) (r b) (r D) (r S) (r A) (r f) (r (shell 2))
    (r (shell 1)) (r (shell 0)) (r rM) (r rO) (r N) (r (x 3)) hw1 hz1 hN1
    (of_eq (singleCode_rename _ _ _ _ _) (lift hEx)) (of_eq (binaryCode_rename _ _ _ _ _ _) (lift hcBody))
    (of_eq (binaryCode_rename _ _ _ _ _ _) (lift hcMid)) hq
  exact of_eq (implication_rename test w z b G N r).symm
    (ForcingRelationGuardProof.chain hZ1 test (r w) (r z) (r b) (r G) (r (x 3)) (r N) hw1 hz1 hG1 hTailT hNT
      (of_eq (implication_rename _ _ _ _ _ _ _) (lift hPoint)) hFalsum)

end FalsumElimination

section ConjunctionWitness

set_option maxHeartbeats 1600000
attribute [local irreducible] NaturalRecursionSyntax.matrix
open SyntaxLogicalSyntax (singleCode singleCode_rename binaryCode_rename)
open FormulaCodeSyntax (formulaCode_rename)
open InternalProofConjunction (proved proved_rename)

/-- Introduce the original existential from the proof of its actual instance. -/
theorem introduce_from_instance {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z b A t Parent ChildBody ChildBound ChildEx : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hParentT : Derives Γ (formulaCode w Parent z b))
    (hi : Derives Γ (instantiated w z b A t ChildBound ChildBody))
    (he : Derives Γ (singleCode 10 w ChildBound ChildEx))
    (pChildBody : Derives Γ (implication test w z b Parent ChildBody)) :
    Derives Γ (implication test w z b Parent ChildEx) := by
  have hCtx := Derives.conjR (FormulaCodeProperties.guards w Parent z b hParentT)
  have hChildBodyT := SyntaxTopFormulaTyping.instantiate_target_type w z b A t ChildBound ChildBody hi
  have hBoundT := SyntaxTopFormulaTyping.instantiate_source_type hZ w z b A t ChildBound ChildBody hw hi
  have hs := Derives.conjR (SyntaxTopFormulaTyping.instantiate_environment w z b A t ChildBound ChildBody hi)
  have hChildExT := Derives.impE (.conjR (FormulaCodeKnownLogical.quantified_iff hZ false
    w z b ChildBound ChildEx A hw he hs)) (.conjI hCtx hBoundT)
  refine with_binary_formula hZ true w z b ChildBody ChildEx hw hChildBodyT hChildExT _ ?_
  intro l Δ r I hZ1 lift hI _
  have hw1 := of_eq (omega_rename _ _) (lift hw)
  have hz1 := of_eq (empty_rename _ _) (lift hz)
  have hAxiom := InternalProofTemplates.existential_introduction_axiom hZ1 test
    (r w) (r z) (r b) (r A) (r ChildBound) (r t) (r ChildBody) (r ChildEx) I hw1 hz1
    (of_eq (instantiated_rename _ _ _ _ _ _ _ _) (lift hi)) (of_eq (singleCode_rename _ _ _ _ _) (lift he)) hI
  have hIntroduced : Derives Δ (implication test (r w) (r z) (r b) (r ChildBody) (r ChildEx)) := by
    apply Derives.exI I
    exact of_eq (by simp only [Formula.instantiate, Formula.rename, SyntaxNodeSyntax.constructor_rename,
      SyntaxAtomSyntax.two_map, proved_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]; rfl)
      (.conjI hI hAxiom : Derives Δ ((binaryCode 2 (r w) (r ChildBody) (r ChildEx) I).conj
        (proved test (r w) (r z) (r b) I)))
  exact of_eq (implication_rename test w z b Parent ChildEx r).symm
    (ForcingRelationGuardProof.chain hZ1 test (r w) (r z) (r b) (r Parent) (r ChildBody) (r ChildEx) hw1 hz1
      (of_eq (formulaCode_rename _ _ _ _ _) (lift hParentT)) (of_eq (formulaCode_rename _ _ _ _ _) (lift hChildBodyT))
      (of_eq (formulaCode_rename _ _ _ _ _) (lift hChildExT))
      (of_eq (implication_rename _ _ _ _ _ _ _) (lift pChildBody)) hIntroduced)

/-- Preserve both density guards and project one conjunct at the same
witness. The child existential is introduced from its actual instance. -/
private theorem conjunction_witness_at_instance {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (right : Bool) (w z b A t M O P Q Pair Mid Parent ChildMid ChildBody ChildBound ChildEx : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hM : Derives Γ (formulaCode w M z b)) (hO : Derives Γ (formulaCode w O z b))
    (hP : Derives Γ (formulaCode w P z b)) (hQ : Derives Γ (formulaCode w Q z b))
    (hPair : Derives Γ (binaryCode 0 w P Q Pair))
    (hMid : Derives Γ (binaryCode 0 w O Pair Mid))
    (hParent : Derives Γ (binaryCode 0 w M Mid Parent))
    (hChildMid : Derives Γ (binaryCode 0 w O (if right then Q else P) ChildMid))
    (hChildBody : Derives Γ (binaryCode 0 w M ChildMid ChildBody))
    (hi : Derives Γ (instantiated w z b A t ChildBound ChildBody))
    (he : Derives Γ (singleCode 10 w ChildBound ChildEx)) :
    Derives Γ (implication test w z b Parent ChildEx) := by
  have hCtx := Derives.conjR (FormulaCodeProperties.guards w M z b hM)
  have hPairT := Derives.impE (.conjR (FormulaCodeKnownLogical.binary0_iff hZ w z b P Q Pair hw hPair))
    (.conjI hCtx (.conjI hP hQ))
  have hMidT := Derives.impE (.conjR (FormulaCodeKnownLogical.binary0_iff hZ w z b O Pair Mid hw hMid))
    (.conjI hCtx (.conjI hO hPairT))
  have hParentT := Derives.impE (.conjR (FormulaCodeKnownLogical.binary0_iff hZ w z b M Mid Parent hw hParent))
    (.conjI hCtx (.conjI hM hMidT))
  let Selected := if right then Q else P
  have hSelected : Derives Γ (formulaCode w Selected z b) := by cases right <;> assumption
  have hChildMidT := Derives.impE (.conjR (FormulaCodeKnownLogical.binary0_iff hZ w z b O Selected ChildMid hw hChildMid))
    (.conjI hCtx (.conjI hO hSelected))
  have pM := ForcingRelationGuardProof.project hZ test false w z b M Mid Parent hw hz hM hMidT hParentT hParent
  have pMid := ForcingRelationGuardProof.project hZ test true w z b M Mid Parent hw hz hM hMidT hParentT hParent
  have mO := ForcingRelationGuardProof.project hZ test false w z b O Pair Mid hw hz hO hPairT hMidT hMid
  have mPair := ForcingRelationGuardProof.project hZ test true w z b O Pair Mid hw hz hO hPairT hMidT hMid
  have qSelected := ForcingRelationGuardProof.project hZ test right w z b P Q Pair hw hz hP hQ hPairT hPair
  have pO := ForcingRelationGuardProof.chain hZ test w z b Parent Mid O hw hz hParentT hMidT hO pMid mO
  have pPair := ForcingRelationGuardProof.chain hZ test w z b Parent Mid Pair hw hz hParentT hMidT hPairT pMid mPair
  have pSelected := ForcingRelationGuardProof.chain hZ test w z b Parent Pair Selected hw hz hParentT hPairT hSelected pPair qSelected
  have pChildMid := ForcingProofContext.join hZ test w z b Parent O Selected ChildMid hw hz hParentT hO hSelected hChildMid pO pSelected
  have pChildBody := ForcingProofContext.join hZ test w z b Parent M ChildMid ChildBody hw hz hParentT hM hChildMidT hChildBody pM pChildMid
  exact introduce_from_instance hZ w z b A t Parent ChildBody ChildBound ChildEx
    hw hz hParentT hi he pChildBody

/-- Project one conjunct at the same witness and transport the resulting
existential back across the actual fresh opening. -/
theorem conjunction_exists_from_witness {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (right : Bool) (w z b A B t M O P Q Pair Mid Parent ChildMid ChildBody ChildBound
      ChildExOpen ChildEx ParentBound ParentEx : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hM : Derives Γ (formulaCode w M z B)) (hO : Derives Γ (formulaCode w O z B))
    (hP : Derives Γ (formulaCode w P z B)) (hQ : Derives Γ (formulaCode w Q z B))
    (hPair : Derives Γ (binaryCode 0 w P Q Pair))
    (hMid : Derives Γ (binaryCode 0 w O Pair Mid))
    (hParent : Derives Γ (binaryCode 0 w M Mid Parent))
    (hChildMid : Derives Γ (binaryCode 0 w O (if right then Q else P) ChildMid))
    (hChildBody : Derives Γ (binaryCode 0 w M ChildMid ChildBody))
    (hi : Derives Γ (instantiated w z B A t ChildBound ChildBody))
    (hChildEx : Derives Γ (singleCode 10 w ChildBound ChildExOpen))
    (hChildWeak : Derives Γ (SyntaxWeakenFreeSyntax.weakened w z b B ChildEx ChildExOpen))
    (hParentAbs : Derives Γ (SyntaxTopFormulaSyntax.abstracted w z b A B Parent ParentBound))
    (hParentEx : Derives Γ (singleCode 10 w ParentBound ParentEx)) :
    Derives Γ (implication test w z b ParentEx ChildEx) := by
  have hp := conjunction_witness_at_instance hZ right w z B A t M O P Q Pair Mid Parent
    ChildMid ChildBody ChildBound ChildExOpen hw hz hM hO hP hQ hPair hMid hParent hChildMid hChildBody hi hChildEx
  have hA := Derives.conjL (.conjR (SyntaxTopFormulaTyping.abstract_environment w z b A B Parent ParentBound hParentAbs))
  have ha := ForcingFreshBackground.derive hZ w z b A B ChildEx ChildExOpen
    (.conjI hw (.conjI hz (.conjI hA hChildWeak)))
  have hT := SyntaxWeakenFreeOutput.source_type hZ w z b B ChildEx ChildExOpen hw hChildWeak
  have hB := SyntaxTopFormulaTyping.abstract_target_type w z b A B ChildExOpen ChildEx ha
  have hOpen := SyntaxWeakenFreeOutput.target_type w z b B ChildEx ChildExOpen hChildWeak
  exact eliminate_exists_from_body hZ w z b A B Parent ParentBound ChildExOpen ChildEx ParentEx hw hz
    hT hB hOpen hParentAbs ha hParentEx hp

private theorem conjunction_from_shared_queries {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (right : Bool) (w z alpha f b A B t D S M O P Q Pair Mid ChildMid RawParent RawChild
      Parent Child ChildBound ChildWeak ChildEx ParentBound ParentEx : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hPair : Derives Γ (binaryCode 0 w P Q Pair))
    (hMid : Derives Γ (binaryCode 0 w O Pair Mid))
    (hRawParent : Derives Γ (binaryCode 0 w M Mid RawParent))
    (hChildMid : Derives Γ (binaryCode 0 w O (if right then Q else P) ChildMid))
    (hRawChild : Derives Γ (binaryCode 0 w M ChildMid RawChild))
    (hParent : Derives Γ (substituted w D S alpha f z B RawParent Parent))
    (hChild : Derives Γ (substituted w D S alpha f z B RawChild Child))
    (hi : Derives Γ (instantiated w z B A t ChildBound Child))
    (he : Derives Γ (singleCode 10 w ChildBound ChildWeak))
    (hWeak : Derives Γ (SyntaxWeakenFreeSyntax.weakened w z b B ChildEx ChildWeak))
    (hAbs : Derives Γ (SyntaxTopFormulaSyntax.abstracted w z b A B Parent ParentBound))
    (hEx : Derives Γ (singleCode 10 w ParentBound ParentEx)) :
    Derives Γ (implication test w z b ParentEx ChildEx) := by
  let out := implication test w z b ParentEx ChildEx
  have hPO := ForcingRawModalBody.nested_from_query hZ 0 w D S alpha f z B M O Pair Mid RawParent Parent
    hw hRawParent hMid hParent
  refine eliminate_objects hZ 4 (fun r v => ForcingRawModalBody.nestedData 0 (r w) (r D) (r S)
    (r alpha) (r f) (r z) (r B) (r M) (r O) (r Pair) (r Mid) (r Parent) v) hPO out ?_
  intro l Δ r v hZ1 lift hp
  have hw1 := of_eq (omega_rename _ _) (lift hw)
  have hPair1 := ForcingFormulaDiagram.binary_output hZ1 0 (r w) (r D) (r S) (r alpha) (r f) (r z) (r B)
    (r Pair) (r P) (r Q) (v 3) hw1 (of_eq (binaryCode_rename _ _ _ _ _ _) (lift hPair)) (.conjR (.conjR (.conjR hp)))
  refine eliminate_objects hZ1 2 (fun s x => ForcingFormulaDiagram.binaryData 0 (s (r w)) (s (r D)) (s (r S))
    (s (r alpha)) (s (r f)) (s (r z)) (s (r B)) (s (r P)) (s (r Q)) (s (v 3)) (x 0) (x 1))
    hPair1 (out.rename r) ?_
  intro l1 Δ1 s x hZ2 lift1 hPair2
  let R := s ∘ r
  have move {F : Formula m} (h : Derives Γ F) : Derives Δ1 (F.rename R) :=
    of_eq (SourceAlgebra.rename_comp F r s) (lift1 (lift h))
  let Selected := if right then Q else P
  have hCO := ForcingRawModalBody.nested_from_query hZ2 0 (R w) (R D) (R S) (R alpha) (R f) (R z) (R B)
    (R M) (R O) (R Selected) (R ChildMid) (R RawChild) (R Child)
    (of_eq (omega_rename _ _) (move hw))
    (of_eq (binaryCode_rename _ _ _ _ _ _) (move hRawChild))
    (of_eq (binaryCode_rename _ _ _ _ _ _) (move hChildMid))
    (of_eq (substituted_rename _ _ _ _ _ _ _ _ _ _) (move hChild))
  refine of_eq (SourceAlgebra.rename_comp out r s).symm ?_
  refine eliminate_objects hZ2 4 (fun e u => ForcingRawModalBody.nestedData 0 (e (R w)) (e (R D)) (e (R S))
    (e (R alpha)) (e (R f)) (e (R z)) (e (R B)) (e (R M)) (e (R O))
    (e (R Selected)) (e (R ChildMid)) (e (R Child)) u) hCO (out.rename R) ?_
  intro l2 Δ2 e u hZ3 lift2 hChild2
  let E := e ∘ R
  have move2 {F : Formula m} (h : Derives Γ F) : Derives Δ2 (F.rename E) :=
    of_eq (SourceAlgebra.rename_comp F R e) (lift2 (move h))
  have hw2 := of_eq (omega_rename _ _) (move2 hw)
  have hz2 := of_eq (empty_rename _ _) (move2 hz)
  have hp2 := of_eq (ForcingRawModalBody.nestedData_rename 0 (r w) (r D) (r S) (r alpha) (r f)
    (r z) (r B) (r M) (r O) (r Pair) (r Mid) (r Parent) v (e ∘ s))
    (of_eq (SourceAlgebra.rename_comp _ s e) (lift2 (lift1 hp)))
  have hPQ := of_eq (ForcingFormulaDiagram.binaryData_rename 0 (R w) (R D) (R S) (R alpha) (R f)
    (R z) (R B) (R P) (R Q) (s (v 3)) (x 0) (x 1) e) (lift2 hPair2)
  have hM := Derives.conjL (.conjR (.conjL hp2))
  have hO := Derives.conjL (.conjR (.conjR hp2))
  have hP := Derives.conjL (.conjR hPQ)
  have hQ := Derives.conjR (.conjR hPQ)
  let result := if right then e (x 1) else e (x 0)
  have hSelected : Derives Δ2 (substituted (E w) (E D) (E S) (E alpha) (E f) (E z) (E B)
      (E Selected) result) := by
    cases right
    · exact hP
    · exact hQ
  have same {F X Y : Fin l2}
      (hX : Derives Δ2 (substituted (E w) (E D) (E S) (E alpha) (E f) (E z) (E B) F X))
      (hY : Derives Δ2 (substituted (E w) (E D) (E S) (E alpha) (E f) (E z) (E B) F Y)) :
      Derives Δ2 (.equal X Y) :=
    SyntaxMixedFormulaOutputInduction.unique hZ3 (E w) (E D) (E S) (E alpha) (E f) (E z) (E B) F X Y hw2 hX hY
  have hmEq := same (.conjL (.conjR (.conjL hChild2))) hM
  have hoEq := same (.conjL (.conjR (.conjR hChild2))) hO
  have hsEq := same (.conjR (.conjR (.conjR hChild2))) hSelected
  have hChildMid2 := SyntaxMixedFormulaLogicalSubst.binary_x 0 (E w) (u 2) (u 3) (u 0) (e (s (v 2)))
    hoEq (.conjL (.conjR hChild2))
  have hChildMid3 := SyntaxMixedFormulaLogicalSubst.binary_y 0 (E w) (e (s (v 2))) (u 3) (u 0) result hsEq hChildMid2
  have hChild3 := SyntaxMixedFormulaLogicalSubst.binary_x 0 (E w) (u 1) (u 0) (E Child) (e (s (v 1)))
    hmEq (.conjL (.conjL hChild2))
  have type_of {F X : Fin l2}
      (h : Derives Δ2 (substituted (E w) (E D) (E S) (E alpha) (E f) (E z) (E B) F X)) :
      Derives Δ2 (formulaCode (E w) X (E z) (E B)) :=
    SyntaxMixedFormulaJudgment.target_type _ _ _ _ _ _ _ _ _ h
  exact of_eq (SourceAlgebra.rename_comp out R e).symm
    (of_eq (implication_rename test w z b ParentEx ChildEx E).symm
      (conjunction_exists_from_witness hZ3 right (E w) (E z) (E b) (E A) (E B) (E t)
        (e (s (v 1))) (e (s (v 2))) (e (x 0)) (e (x 1)) (e (s (v 3))) (e (s (v 0)))
        (E Parent) (u 0) (E Child) (E ChildBound) (E ChildWeak) (E ChildEx) (E ParentBound) (E ParentEx)
        hw2 hz2 (type_of hM) (type_of hO) (type_of hP) (type_of hQ)
        (.conjL hPQ) (.conjL (.conjR hp2)) (.conjL (.conjL hp2)) hChildMid3 hChild3
        (of_eq (instantiated_rename _ _ _ _ _ _ _ _) (move2 hi))
        (of_eq (singleCode_rename _ _ _ _ _) (move2 he))
        (of_eq (SyntaxWeakenFreeSyntax.weakened_rename _ _ _ _ _ _ _) (move2 hWeak))
        (of_eq (SyntaxTopFormulaSyntax.abstracted_rename _ _ _ _ _ _ _ _) (move2 hAbs))
        (of_eq (singleCode_rename _ _ _ _ _) (move2 hEx))))

private theorem conjunction_from_opening_records {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (right : Bool) (w z a f alpha b A B t R S NP NC XP XC EP EC M O P Q Pair MP MC : Fin m)
    (v : Fin 10 → Fin m) (u c : Fin 9 → Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (ht : Derives Γ (SyntaxTermSyntax.term w z B t))
    (hPair : Derives Γ (binaryCode 0 w P Q Pair))
    (hMP : Derives Γ (binaryCode 0 w O Pair MP))
    (hXP : Derives Γ (binaryCode 0 w M MP XP))
    (hMC : Derives Γ (binaryCode 0 w O (if right then Q else P) MC))
    (hXC : Derives Γ (binaryCode 0 w M MC XC))
    (hc : Derives Γ (singleCode 10 w XC NC))
    (hOldChild : Derives Γ (substituted w R S a f z b NC EC))
    (hp : Derives Γ (ForcingFreshParentOpening.quantifiedData false w z a f alpha b A B t R S NP XP EP v u))
    (hq : Derives Γ (ForcingFreshParentOpening.quantifiedData false w z a f alpha b A B t R S NC XC EC v c)) :
    Derives Γ (implication test w z b EP EC) := by
  have images := Derives.conjL (.conjR hq)
  have c3 := Derives.conjR (.conjR (.conjR hq))
  have hLift := Derives.conjL c3
  have c5 := Derives.conjR (.conjR c3)
  have hCBody := Derives.conjL c5
  have c6 := Derives.conjR c5
  have hCWhole := Derives.conjL c6
  have c7 := Derives.conjR c6
  have hCCons := Derives.conjL c7
  have c8 := Derives.conjR c7
  have hCOpen := Derives.conjL c8
  have c10 := Derives.conjR (.conjR c8)
  have hInv := Derives.conjL c10
  have hI := Derives.conjR (.conjR (.conjR (.conjR (.conjR hInv))))
  have p7 := Derives.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR hp))))))
  have hPCons := Derives.conjL p7
  have p8 := Derives.conjR p7
  have hPOpen := Derives.conjL p8
  have p9 := Derives.conjR p8
  have hPEx := Derives.conjL p9
  have hPAbs := Derives.conjR (.conjR p9)
  have hInput := SyntaxMixedFormulaOutput.input_of_substituted hZ w (v 8) (v 9) a f z B NC (c 6) hw hCWhole
  have hL := Derives.conjL (.conjR hInput)
  have hList := Derives.conjL (.conjL (.conjR (.conjR hL)))
  have hTN := SyntaxTerms.range hZ w z B t hw ht
  have heq := StructuralConsUnique.unique hZ w t (v 8) (c 7) (u 7) hw hTN hList hCCons hPCons
  have hSame := SyntaxMixedFormulaJudgmentSubst.subst_r w (c 7) (v 9) alpha f z B XC (c 8) (u 7) heq hCOpen
  have hWeak := ForcingWeakenedImages.from_queries hZ w a f z b B R S NC EC (c 6) v
    (.conjI images (.conjI hOldChild hCWhole))
  have hCEx := ForcingMixedUnary.quantified_constructor hZ false w (v 8) (v 9) a f z B NC XC (c 6) (c 5)
    alpha A (c 2) (c 3) hw hInput hc hCWhole hLift hCBody
  exact conjunction_from_shared_queries hZ right w z alpha f b A B t (u 7) (v 9) M O P Q Pair MP MC XP XC
    (u 8) (c 8) (c 5) (c 6) EC (u 4) EP hw hz hPair hMP hXP hMC hXC hPOpen hSame hI hCEx hWeak hPAbs hPEx

/-- Execute both quantified openings on one generated weakened mixed table. -/
private theorem with_shared_quantified_openings {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (universal : Bool) (w z a f alpha b A B t R S L X P K Y C : Fin m)
    (hl : Derives Γ (ForcingFreshParentOpening.quantifiedInput universal w z a f alpha b A B t R S L X P))
    (hr : Derives Γ (ForcingFreshParentOpening.quantifiedInput universal w z a f alpha b A B t R S K Y C))
    (out : Formula m)
    (use : ∀ {l} {Δ : Context l} (r : Fin m → Fin l) (v : Fin 10 → Fin l) (p c : Fin 9 → Fin l),
      ZFContext.Evidence Δ →
      (∀ {F : Formula m}, Derives Γ F → Derives Δ (F.rename r)) →
      Derives Δ (ForcingFreshParentOpening.quantifiedData universal
        (r w) (r z) (r a) (r f) (r alpha) (r b) (r A) (r B) (r t) (r R) (r S) (r L) (r X) (r P) v p) →
      Derives Δ (ForcingFreshParentOpening.quantifiedData universal
        (r w) (r z) (r a) (r f) (r alpha) (r b) (r A) (r B) (r t) (r R) (r S) (r K) (r Y) (r C) v c) →
      Derives Δ (out.rename r)) : Derives Γ out := by
  have hw := Derives.conjL hl
  have h4 := Derives.conjR (.conjR (.conjR (.conjR hl)))
  have hB := Derives.conjL h4
  have hL := Derives.conjR (.conjR (.conjR (.conjR h4)))
  have hIn := Derives.conjR (SyntaxMixedFormulaOutput.input_of_substituted hZ w R S a f z b L P hw hL)
  refine eliminate_objects hZ 10 (fun r v => ForcingWeakenedImages.data (r w) (r a) (r f)
    (r z) (r b) (r B) (r R) (r S) v)
    (ForcingWeakenedImages.produce hZ w a f z b B R S (.conjI hw (.conjI hB hIn))) out ?_
  intro l Δ r v hZ1 lift hv
  have hp := ForcingFreshParentOpening.produce_quantified_at_images hZ1 universal
    (r w) (r z) (r a) (r f) (r alpha) (r b) (r A) (r B) (r t) (r R) (r S) (r L) (r X) (r P) v
    (of_eq (ForcingFreshParentOpening.quantifiedInput_rename universal w z a f alpha b A B t R S L X P r) (lift hl)) hv
  have hc := ForcingFreshParentOpening.produce_quantified_at_images hZ1 universal
    (r w) (r z) (r a) (r f) (r alpha) (r b) (r A) (r B) (r t) (r R) (r S) (r K) (r Y) (r C) v
    (of_eq (ForcingFreshParentOpening.quantifiedInput_rename universal w z a f alpha b A B t R S K Y C r) (lift hr)) hv
  refine eliminate_objects hZ1 9 (fun s p => ForcingFreshParentOpening.quantifiedData universal
    (s (r w)) (s (r z)) (s (r a)) (s (r f)) (s (r alpha)) (s (r b)) (s (r A)) (s (r B)) (s (r t))
    (s (r R)) (s (r S)) (s (r L)) (s (r X)) (s (r P)) (s ∘ v) p) hp (out.rename r) ?_
  intro l1 Δ1 s p hZ2 lift1 hp1
  let ρ := s ∘ r
  have move {F : Formula m} (h : Derives Γ F) : Derives Δ1 (F.rename ρ) :=
    of_eq (SourceAlgebra.rename_comp F r s) (lift1 (lift h))
  refine of_eq (SourceAlgebra.rename_comp out r s).symm ?_
  refine eliminate_objects hZ2 9 (fun e c => ForcingFreshParentOpening.quantifiedData universal
    (e (ρ w)) (e (ρ z)) (e (ρ a)) (e (ρ f)) (e (ρ alpha)) (e (ρ b)) (e (ρ A)) (e (ρ B)) (e (ρ t))
    (e (ρ R)) (e (ρ S)) (e (ρ K)) (e (ρ Y)) (e (ρ C)) (e ∘ s ∘ v) c)
    (of_eq (ForcingFreshParentOpening.quantifiedAtImages_rename universal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s) (lift1 hc))
    (out.rename ρ) ?_
  intro l2 Δ2 e c hZ3 lift2 hc2
  let E := e ∘ ρ
  have move2 {F : Formula m} (h : Derives Γ F) : Derives Δ2 (F.rename E) :=
    of_eq (SourceAlgebra.rename_comp F ρ e) (lift2 (move h))
  have hp2 := of_eq (ForcingFreshParentOpening.quantifiedData_rename universal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ e)
    (lift2 hp1)
  exact of_eq (SourceAlgebra.rename_comp out ρ e).symm
    (use E (e ∘ s ∘ v) (e ∘ p) c hZ3 move2 hp2 hc2)


private theorem conjunction_from_exists_queries {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (right : Bool) (w z a f alpha b A B t R S NP NC XP XC EP EC M O P Q Pair MP MC : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (ha : Derives Γ (successor alpha a)) (hA : Derives Γ (successor A z)) (hB : Derives Γ (successor B b))
    (hf : Derives Γ (SyntaxVariableSyntax.code false w z t))
    (ht : Derives Γ (SyntaxTermSyntax.term w z B t))
    (hp : Derives Γ (singleCode 10 w XP NP)) (hc : Derives Γ (singleCode 10 w XC NC))
    (hPQuery : Derives Γ (substituted w R S a f z b NP EP))
    (hCQuery : Derives Γ (substituted w R S a f z b NC EC))
    (hPair : Derives Γ (binaryCode 0 w P Q Pair))
    (hMP : Derives Γ (binaryCode 0 w O Pair MP)) (hXP : Derives Γ (binaryCode 0 w M MP XP))
    (hMC : Derives Γ (binaryCode 0 w O (if right then Q else P) MC))
    (hXC : Derives Γ (binaryCode 0 w M MC XC)) :
    Derives Γ (implication test w z b EP EC) := by
  have input {N X E : Fin m}
      (hX : Derives Γ (singleCode 10 w X N)) (hE : Derives Γ (substituted w R S a f z b N E)) :
      Derives Γ (ForcingFreshParentOpening.quantifiedInput false w z a f alpha b A B t R S N X E) :=
    .conjI hw (.conjI hz (.conjI ha (.conjI hA (.conjI hB (.conjI hf (.conjI ht (.conjI hX hE)))))))
  refine with_shared_quantified_openings hZ false w z a f alpha b A B t R S NP XP EP NC XC EC
    (input hp hPQuery) (input hc hCQuery) (implication test w z b EP EC) ?_
  intro l Δ r images p c hZ1 lift hPO hCO
  have hMC1 : Derives Δ (binaryCode 0 (r w) (r O) (if right then r Q else r P) (r MC)) := by
    cases right <;> exact of_eq (binaryCode_rename _ _ _ _ _ _) (lift hMC)
  exact of_eq (implication_rename test w z b EP EC r).symm
    (conjunction_from_opening_records hZ1 right (r w) (r z) (r a) (r f) (r alpha) (r b) (r A) (r B)
      (r t) (r R) (r S) (r NP) (r NC) (r XP) (r XC) (r EP) (r EC) (r M) (r O) (r P) (r Q)
      (r Pair) (r MP) (r MC) images p c
      (of_eq (omega_rename _ _) (lift hw)) (of_eq (empty_rename _ _) (lift hz))
      (of_eq (SyntaxTermSyntax.term_rename _ _ _ _ _) (lift ht))
      (of_eq (binaryCode_rename _ _ _ _ _ _) (lift hPair)) (of_eq (binaryCode_rename _ _ _ _ _ _) (lift hMP))
      (of_eq (binaryCode_rename _ _ _ _ _ _) (lift hXP)) hMC1
      (of_eq (binaryCode_rename _ _ _ _ _ _) (lift hXC)) (of_eq (singleCode_rename _ _ _ _ _) (lift hc))
      (of_eq (substituted_rename _ _ _ _ _ _ _ _ _ _) (lift hCQuery)) hPO hCO)

/-- Read the two original density shells and transport their existential tails
using the same fresh witness and mixed substitution tables. -/
theorem conjunction_exists_from_compiler_shells {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (right : Bool) (w z a A B f b C D t R S qM qO rM rO P Q Pair ParentRaw ChildRaw EP EC : Fin m)
    (u v : Fin 5 → Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hB : Derives Γ (successor B A))
    (hC : Derives Γ (successor C z)) (hD : Derives Γ (successor D b))
    (hf : Derives Γ (SyntaxVariableSyntax.code false w z t))
    (ht : Derives Γ (SyntaxTermSyntax.term w z D t))
    (hParentShell : Derives Γ (ForcingDensityCode.shellData w a A B f qM qO rM rO Pair ParentRaw u))
    (hChildShell : Derives Γ (ForcingDensityCode.shellData w a A B f qM qO rM rO
      (if right then Q else P) ChildRaw v))
    (hPair : Derives Γ (binaryCode 0 w P Q Pair))
    (hParentQuery : Derives Γ (substituted w R S A f z b (u 2) EP))
    (hChildQuery : Derives Γ (substituted w R S A f z b (v 2) EC)) :
    Derives Γ (implication test w z b EP EC) := by
  have hParentMid := Derives.conjL (.conjL hParentShell)
  have hParentBody := Derives.conjL (.conjL (.conjR hParentShell))
  have hParentEx := Derives.conjL (.conjL (.conjR (.conjR hParentShell)))
  have hChildMid := Derives.conjL (.conjL hChildShell)
  have hChildBody := Derives.conjL (.conjL (.conjR hChildShell))
  have hChildEx := Derives.conjL (.conjL (.conjR (.conjR hChildShell)))
  exact conjunction_from_exists_queries hZ right w z A f B b C D t R S (u 2) (v 2) (u 1) (v 1) EP EC rM rO
    P Q Pair (u 0) (v 0) hw hz hB hC hD hf ht hParentEx hChildEx hParentQuery hChildQuery
    hPair hParentMid hParentBody hChildMid hChildBody

private theorem implication_intro {m} {Γ : Context m} (w z b A B I : Fin m)
    (hI : Derives Γ (binaryCode 2 w A B I)) (hp : Derives Γ (proved test w z b I)) :
    Derives Γ (implication test w z b A B) := by
  apply Derives.exI I
  exact of_eq (by simp only [Formula.instantiate, Formula.rename, SyntaxNodeSyntax.constructor_rename,
    SyntaxAtomSyntax.two_map, proved_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]; rfl)
    (.conjI hI hp : Derives Γ ((binaryCode 2 w A B I).conj (proved test w z b I)))

private theorem implication_type {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z b A B I : Fin m) (hw : Derives Γ (omega w))
    (hA : Derives Γ (formulaCode w A z b)) (hB : Derives Γ (formulaCode w B z b))
    (hI : Derives Γ (binaryCode 2 w A B I)) : Derives Γ (formulaCode w I z b) :=
  .impE (.conjR (FormulaCodeKnownLogical.binary2_iff hZ w z b A B I hw hI))
    (.conjI (.conjR (FormulaCodeProperties.guards w A z b hA)) (.conjI hA hB))

private theorem implication_exists {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z b A B : Fin m) (hw : Derives Γ (omega w))
    (hA : Derives Γ (formulaCode w A z b)) (hB : Derives Γ (formulaCode w B z b)) :
    Derives Γ (FormulaCodeConstructSyntax.typedExists 2 7 w (SyntaxAtomSyntax.two A B) z b) :=
  FormulaCodeConstruct.exists_of_fiber 2 7 w (SyntaxAtomSyntax.two A B) z b
    (FormulaCodeConstructors.binary2 hZ w z b A B hw
      (.conjI (.conjR (FormulaCodeProperties.guards w A z b hA)) (.conjI hA hB)))

/-- K and S transport the actual implication from one tail to the other under
the same antecedent. The antecedent itself need not be provable. -/
private theorem transport_under_guard_at_proof {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z b G A B U V I : Fin m) (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hG : Derives Γ (formulaCode w G z b)) (hA : Derives Γ (formulaCode w A z b))
    (hB : Derives Γ (formulaCode w B z b))
    (hU : Derives Γ (binaryCode 2 w G A U)) (hV : Derives Γ (binaryCode 2 w G B V))
    (hI : Derives Γ (binaryCode 2 w A B I)) (hp : Derives Γ (proved test w z b I)) :
    Derives Γ (implication test w z b U V) := by
  let out := implication test w z b U V
  have hIT := implication_type hZ w z b A B I hw hA hB hI
  have hUT := implication_type hZ w z b G A U hw hG hA hU
  have hVT := implication_type hZ w z b G B V hw hG hB hV
  refine eliminate_objects hZ 1 (fun r v => (Formula.mem (v 0) (r w)).conj
    (FormulaCodeConstructSyntax.typedAt 2 7 (r w) (SyntaxAtomSyntax.two (r G) (r I)) (v 0) (r z) (r b)))
    (implication_exists hZ w z b G I hw hG hIT) out ?_
  intro l Δ r v hZ1 lift hK
  have hw1 := of_eq (omega_rename _ _) (lift hw)
  have hUT1 := of_eq (formulaCode_rename _ _ _ _ _) (lift hUT)
  have hVT1 := of_eq (formulaCode_rename _ _ _ _ _) (lift hVT)
  have hGK : Derives Δ (binaryCode 2 (r w) (r G) (r I) (v 0)) := .conjL (.conjR hK)
  have hKP := InternalProofImplication.weaken_proof hZ1 test (r w) (r z) (r b) (r G) (r I) (v 0)
    hw1 (of_eq (empty_rename _ _) (lift hz)) (of_eq (formulaCode_rename _ _ _ _ _) (lift hG))
    (of_eq (formulaCode_rename _ _ _ _ _) (lift hIT)) hGK (of_eq (proved_rename _ _ _ _ _ _) (lift hp))
  refine of_eq (implication_rename test w z b U V r).symm ?_
  refine eliminate_objects hZ1 1 (fun s d => (Formula.mem (d 0) (s (r w))).conj
    (FormulaCodeConstructSyntax.typedAt 2 7 (s (r w)) (SyntaxAtomSyntax.two (s (r U)) (s (r V)))
      (d 0) (s (r z)) (s (r b)))) (implication_exists hZ1 (r w) (r z) (r b) (r U) (r V) hw1 hUT1 hVT1)
    (implication test (r w) (r z) (r b) (r U) (r V)) ?_
  intro l1 Δ1 s d hZ2 lift1 hD
  let R := s ∘ r
  have move {F : Formula m} (h : Derives Γ F) : Derives Δ1 (F.rename R) :=
    of_eq (SourceAlgebra.rename_comp F r s) (lift1 (lift h))
  have hDst : Derives Δ1 (binaryCode 2 (R w) (R U) (R V) (d 0)) := .conjL (.conjR hD)
  have hDP := InternalProofImplication.map_from_left hZ2 test
    (R w) (R z) (R b) (R G) (R A) (R B) (R U) (R I) (R V) (s (v 0)) (d 0)
    (of_eq (omega_rename _ _) (move hw)) (of_eq (empty_rename _ _) (move hz))
    (of_eq (formulaCode_rename _ _ _ _ _) (move hG)) (of_eq (formulaCode_rename _ _ _ _ _) (move hA))
    (of_eq (formulaCode_rename _ _ _ _ _) (move hB)) (of_eq (binaryCode_rename _ _ _ _ _ _) (move hU))
    (of_eq (binaryCode_rename _ _ _ _ _ _) (move hI)) (of_eq (binaryCode_rename _ _ _ _ _ _) (move hV))
    (of_eq (binaryCode_rename _ _ _ _ _ _) (lift1 hGK)) hDst
    (of_eq (proved_rename _ _ _ _ _ _) (lift1 hKP))
  exact of_eq (implication_rename test (r w) (r z) (r b) (r U) (r V) s).symm
    (implication_intro (R w) (R z) (R b) (R U) (R V) (d 0) hDst hDP)

private theorem transport_under_guard {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z b G A B U V : Fin m) (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hG : Derives Γ (formulaCode w G z b)) (hA : Derives Γ (formulaCode w A z b))
    (hB : Derives Γ (formulaCode w B z b))
    (hU : Derives Γ (binaryCode 2 w G A U)) (hV : Derives Γ (binaryCode 2 w G B V))
    (hp : Derives Γ (implication test w z b A B)) :
    Derives Γ (implication test w z b U V) := by
  refine eliminate_objects hZ 1 (fun r v =>
    (binaryCode 2 (r w) (r A) (r B) (v 0)).conj (proved test (r w) (r z) (r b) (v 0)))
    hp (implication test w z b U V) ?_
  intro l Δ r v hZ1 lift hI
  exact of_eq (implication_rename test w z b U V r).symm
    (transport_under_guard_at_proof hZ1 (r w) (r z) (r b) (r G) (r A) (r B) (r U) (r V) (v 0)
      (of_eq (omega_rename _ _) (lift hw)) (of_eq (empty_rename _ _) (lift hz))
      (of_eq (formulaCode_rename _ _ _ _ _) (lift hG)) (of_eq (formulaCode_rename _ _ _ _ _) (lift hA))
      (of_eq (formulaCode_rename _ _ _ _ _) (lift hB)) (of_eq (binaryCode_rename _ _ _ _ _ _) (lift hU))
      (of_eq (binaryCode_rename _ _ _ _ _ _) (lift hV)) (.conjL hI) (.conjR hI))


private theorem universal_instance_implication {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z b A t F P Y : Fin m) (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hP : Derives Γ (formulaCode w P z b))
    (hAll : Derives Γ (singleCode 9 w F P))
    (hInst : Derives Γ (SyntaxTopFormulaSyntax.instantiated w z b A t F Y)) :
    Derives Γ (implication test w z b P Y) := by
  have hY := SyntaxTopFormulaTyping.instantiate_target_type w z b A t F Y hInst
  refine eliminate_objects hZ 1 (fun r v => (Formula.mem (v 0) (r w)).conj
    (FormulaCodeConstructSyntax.typedAt 2 7 (r w) (SyntaxAtomSyntax.two (r P) (r Y)) (v 0) (r z) (r b)))
    (implication_exists hZ w z b P Y hw hP hY) (implication test w z b P Y) ?_
  intro l Δ r v hZ1 lift hI
  have hCode : Derives Δ (binaryCode 2 (r w) (r P) (r Y) (v 0)) := .conjL (.conjR hI)
  have hp := InternalProofQuantifier.universal_axiom hZ1 test
    (r w) (r z) (r b) (r A) (r F) (r t) (r Y) (r P) (v 0)
    (of_eq (omega_rename _ _) (lift hw)) (of_eq (empty_rename _ _) (lift hz))
    (of_eq (SyntaxTopFormulaSyntax.instantiated_rename _ _ _ _ _ _ _ _) (lift hInst))
    (of_eq (singleCode_rename _ _ _ _ _) (lift hAll)) hCode
  exact of_eq (implication_rename test w z b P Y r).symm
    (implication_intro (r w) (r z) (r b) (r P) (r Y) (v 0) hCode hp)

private theorem match_generalized_universal {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z b G J C : Fin m) (hw : Derives Γ (omega w))
    (hC : Derives Γ (singleCode 9 w J C))
    (hp : Derives Γ (InternalProofUniversal.guarded test w z b G J)) :
    Derives Γ (implication test w z b G C) := by
  refine eliminate_objects hZ 1 (fun r v => (singleCode 9 (r w) (r J) (v 0)).conj
    (implication test (r w) (r z) (r b) (r G) (v 0))) hp (implication test w z b G C) ?_
  intro l Δ r v hZ1 lift h
  have he := SyntaxLogicalFields.single_unique hZ1 9 (r w) (r J) (v 0) (r C)
    (of_eq (omega_rename _ _) (lift hw)) (.conjL h) (of_eq (singleCode_rename _ _ _ _ _) (lift hC))
  let F := implication test (r w).castSucc (r z).castSucc (r b).castSucc (r G).castSucc (Fin.last l)
  have eval (i : Fin l) : F.instantiate i = implication test (r w) (r z) (r b) (r G) i := by
    simp only [F, Formula.instantiate, implication_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact of_eq (implication_rename test w z b G C r).symm
    (of_eq (eval (r C)) (.eqSubst F he (of_eq (eval (v 0)).symm (.conjR h))))

private theorem generalize_actual_implication {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z b A B G W Y J C : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hG : Derives Γ (formulaCode w G z b))
    (hW : Derives Γ (SyntaxTopFormulaSyntax.abstracted w z b A B W G))
    (hY : Derives Γ (SyntaxTopFormulaSyntax.abstracted w z b A B Y J))
    (hC : Derives Γ (singleCode 9 w J C))
    (hp : Derives Γ (implication test w z B W Y)) :
    Derives Γ (implication test w z b G C) := by
  refine eliminate_objects hZ 1 (fun r v =>
    (binaryCode 2 (r w) (r W) (r Y) (v 0)).conj (proved test (r w) (r z) (r B) (v 0)))
    hp (implication test w z b G C) ?_
  intro l Δ r v hZ1 lift hI
  have hw1 := of_eq (omega_rename _ _) (lift hw)
  have hx : Derives Δ (InternalProofUniversal.input test
      (r w) (r z) (r b) (r A) (r B) (r G) (r W) (r Y) (r J) (v 0)) :=
    .conjI hw1 (.conjI (of_eq (empty_rename _ _) (lift hz))
      (.conjI (of_eq (formulaCode_rename _ _ _ _ _) (lift hG))
        (.conjI (of_eq (SyntaxTopFormulaSyntax.abstracted_rename _ _ _ _ _ _ _ _) (lift hW))
          (.conjI (of_eq (SyntaxTopFormulaSyntax.abstracted_rename _ _ _ _ _ _ _ _) (lift hY)) hI))))
  have hAll := InternalProofUniversal.guarded_generalize hZ1 test
    (r w) (r z) (r b) (r A) (r B) (r G) (r W) (r Y) (r J) (v 0) hx
  exact of_eq (implication_rename test w z b G C r).symm
    (match_generalized_universal hZ1 (r w) (r z) (r b) (r G) (r J) (r C) hw1
      (of_eq (singleCode_rename _ _ _ _ _) (lift hC)) hAll)

/-- Apply the rule-20 instance to the weakened parent, then generalize the
actual pointwise proof to the exact original child universal. -/
private theorem transport_universal_at_point {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z b A B t P PW PF PY CY CF C : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hP : Derives Γ (formulaCode w P z b))
    (hPA : Derives Γ (SyntaxTopFormulaSyntax.abstracted w z b A B PW P))
    (hPAll : Derives Γ (singleCode 9 w PF PW))
    (hPI : Derives Γ (SyntaxTopFormulaSyntax.instantiated w z B A t PF PY))
    (hCA : Derives Γ (SyntaxTopFormulaSyntax.abstracted w z b A B CY CF))
    (hCAll : Derives Γ (singleCode 9 w CF C))
    (hp : Derives Γ (implication test w z B PY CY)) :
    Derives Γ (implication test w z b P C) := by
  have hPWT := SyntaxTopFormulaTyping.abstract_source_type hZ w z b A B PW P hw hPA
  have hPYT := SyntaxTopFormulaTyping.instantiate_target_type w z B A t PF PY hPI
  have hCYT := SyntaxTopFormulaTyping.abstract_source_type hZ w z b A B CY CF hw hCA
  have hInst := universal_instance_implication hZ w z B A t PF PW PY hw hz hPWT hPAll hPI
  have hPoint := ForcingRelationGuardProof.chain hZ test w z B PW PY CY hw hz hPWT hPYT hCYT hInst hp
  exact generalize_actual_implication hZ w z b A B P PW CY CF C hw hz hP hPA hCA hCAll hPoint


private theorem conjunction_from_pointwise_records {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (right : Bool) (w z a A B f T C D t R S qM qO rM rO P Q Pair ParentRaw ChildRaw PY CY : Fin m)
    (u v : Fin 5 → Fin m) (p c : Fin 4 → Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hB : Derives Γ (successor B A)) (hC : Derives Γ (successor C z))
    (hD : Derives Γ (successor D T))
    (hf : Derives Γ (SyntaxVariableSyntax.code false w z t))
    (ht : Derives Γ (SyntaxTermSyntax.term w z D t))
    (hParentShell : Derives Γ (ForcingDensityCode.shellData w a A B f qM qO rM rO Pair ParentRaw u))
    (hChildShell : Derives Γ (ForcingDensityCode.shellData w a A B f qM qO rM rO
      (if right then Q else P) ChildRaw v))
    (hPair : Derives Γ (binaryCode 0 w P Q Pair))
    (hParent : Derives Γ (ForcingRawModalBody.nestedData 2 w R S A f z T qM qO (u 2) (u 3) PY p))
    (hChild : Derives Γ (ForcingRawModalBody.nestedData 2 w R S A f z T qM qO (v 2) (v 3) CY c)) :
    Derives Γ (implication test w z T PY CY) := by
  have hPM := Derives.conjL (.conjR (.conjL hParent))
  have hPO := Derives.conjL (.conjR (.conjR hParent))
  have hPT := Derives.conjR (.conjR (.conjR hParent))
  have hCM := Derives.conjL (.conjR (.conjL hChild))
  have hCO := Derives.conjL (.conjR (.conjR hChild))
  have hCT := Derives.conjR (.conjR (.conjR hChild))
  have heM := SyntaxMixedFormulaOutputInduction.unique hZ w R S A f z T qM (c 1) (p 1) hw hCM hPM
  have heO := SyntaxMixedFormulaOutputInduction.unique hZ w R S A f z T qO (c 2) (p 2) hw hCO hPO
  have hcM := SyntaxMixedFormulaLogicalSubst.binary_x 2 w (c 1) (c 0) CY (p 1) heM (.conjL (.conjL hChild))
  have hcO := SyntaxMixedFormulaLogicalSubst.binary_x 2 w (c 2) (c 3) (c 0) (p 2) heO (.conjL (.conjR hChild))
  have type_of {F X : Fin m} (h : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w R S A f z T F X)) :
      Derives Γ (formulaCode w X z T) :=
    SyntaxMixedFormulaJudgment.target_type w R S A f z T F X h
  have hMP := type_of hPM
  have hOP := type_of hPO
  have hTP := type_of hPT
  have hTC := type_of hCT
  have hpO := Derives.conjL (.conjR hParent)
  have hpM := Derives.conjL (.conjL hParent)
  have hTail := conjunction_exists_from_compiler_shells hZ right w z a A B f T C D t R S
    qM qO rM rO P Q Pair ParentRaw ChildRaw (p 3) (c 3) u v
    hw hz hB hC hD hf ht hParentShell hChildShell hPair hPT hCT
  have hOrder := transport_under_guard hZ w z T (p 2) (p 3) (c 3) (p 0) (c 0)
    hw hz hOP hTP hTC hpO hcO hTail
  exact transport_under_guard hZ w z T (p 1) (p 0) (c 0) PY CY hw hz hMP
    (implication_type hZ w z T (p 2) (p 3) (p 0) hw hOP hTP hpO)
    (implication_type hZ w z T (p 2) (c 3) (c 0) hw hOP hTC hcO)
    hpM hcM hOrder


private theorem conjunction_from_outer_queries {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (right : Bool) (w z a A B f T C D t R S qM qO rM rO P Q Pair ParentRaw ChildRaw PY CY : Fin m)
    (u v : Fin 5 → Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hB : Derives Γ (successor B A)) (hC : Derives Γ (successor C z)) (hD : Derives Γ (successor D T))
    (hf : Derives Γ (SyntaxVariableSyntax.code false w z t))
    (ht : Derives Γ (SyntaxTermSyntax.term w z D t))
    (hPS : Derives Γ (ForcingDensityCode.shellData w a A B f qM qO rM rO Pair ParentRaw u))
    (hCS : Derives Γ (ForcingDensityCode.shellData w a A B f qM qO rM rO (if right then Q else P) ChildRaw v))
    (hPair : Derives Γ (binaryCode 0 w P Q Pair))
    (hP : Derives Γ (substituted w R S A f z T (u 4) PY))
    (hY : Derives Γ (substituted w R S A f z T (v 4) CY)) :
    Derives Γ (implication test w z T PY CY) := by
  have hP5 := Derives.conjR (.conjR (.conjR hPS))
  have hY5 := Derives.conjR (.conjR (.conjR hCS))
  have hNP := ForcingRawModalBody.from_query hZ w R S A f z T qM qO (u 2) (u 3) (u 4) PY hw
    (.conjL (.conjL (.conjR hP5))) (.conjL (.conjL hP5)) hP
  have hNY := ForcingRawModalBody.from_query hZ w R S A f z T qM qO (v 2) (v 3) (v 4) CY hw
    (.conjL (.conjL (.conjR hY5))) (.conjL (.conjL hY5)) hY
  let out := implication test w z T PY CY
  refine eliminate_objects hZ 4 (fun r p => ForcingRawModalBody.data
    (r w) (r R) (r S) (r A) (r f) (r z) (r T) (r qM) (r qO) (r (u 2)) (r (u 3)) (r PY) p)
    hNP out ?_
  intro l Δ r p hZ1 lift hp
  refine eliminate_objects hZ1 4 (fun s c => ForcingRawModalBody.data
    (s (r w)) (s (r R)) (s (r S)) (s (r A)) (s (r f)) (s (r z)) (s (r T)) (s (r qM)) (s (r qO))
    (s (r (v 2))) (s (r (v 3))) (s (r CY)) c)
    (of_eq (ForcingRawModalBody.outputs_rename _ _ _ _ _ _ _ _ _ _ _ _ r) (lift hNY)) (out.rename r) ?_
  intro l1 Δ1 s c hZ2 lift1 hc
  let E := s ∘ r
  have move {F : Formula m} (h : Derives Γ F) : Derives Δ1 (F.rename E) :=
    of_eq (SourceAlgebra.rename_comp F r s) (lift1 (lift h))
  have hCS2 : Derives Δ1 (ForcingDensityCode.shellData (E w) (E a) (E A) (E B) (E f)
      (E qM) (E qO) (E rM) (E rO) (if right then E Q else E P) (E ChildRaw) (E ∘ v)) := by
    cases right <;> exact of_eq (ForcingDensityCode.shellData_rename _ _ _ _ _ _ _ _ _ _ _ _ _) (move hCS)
  have hP2 := of_eq (ForcingRawModalBody.data_rename _ _ _ _ _ _ _ _ _ _ _ _ _ s) (lift1 hp)
  exact of_eq (SourceAlgebra.rename_comp out r s).symm
    (of_eq (implication_rename test w z T PY CY E).symm
      (conjunction_from_pointwise_records hZ2 right (E w) (E z) (E a) (E A) (E B) (E f) (E T)
        (E C) (E D) (E t) (E R) (E S) (E qM) (E qO) (E rM) (E rO) (E P) (E Q) (E Pair)
        (E ParentRaw) (E ChildRaw) (E PY) (E CY) (E ∘ u) (E ∘ v) (s ∘ p) c
        (of_eq (omega_rename _ _) (move hw)) (of_eq (empty_rename _ _) (move hz))
        (of_eq (successor_rename _ _ _) (move hB)) (of_eq (successor_rename _ _ _) (move hC))
        (of_eq (successor_rename _ _ _) (move hD)) (of_eq (SyntaxVariableSyntax.code_rename _ _ _ _ _) (move hf))
        (of_eq (SyntaxTermSyntax.term_rename _ _ _ _ _) (move ht))
        (of_eq (ForcingDensityCode.shellData_rename _ _ _ _ _ _ _ _ _ _ _ _ _) (move hPS)) hCS2
        (of_eq (binaryCode_rename _ _ _ _ _ _) (move hPair)) hP2 hc))

private theorem conjunction_from_actual_universal_records {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (right : Bool) (w z a A B f b C T D t rTerm R S qM qO rM rO P Q Pair ParentRaw ChildRaw Parent Child : Fin m)
    (u v : Fin 5 → Fin m) (images : Fin 10 → Fin m) (p c : Fin 9 → Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hB : Derives Γ (successor B A)) (hC : Derives Γ (successor C z)) (hD : Derives Γ (successor D T))
    (ht : Derives Γ (SyntaxTermSyntax.term w z T t))
    (hf2 : Derives Γ (SyntaxVariableSyntax.code false w z rTerm))
    (ht2 : Derives Γ (SyntaxTermSyntax.term w z D rTerm))
    (hPS : Derives Γ (ForcingDensityCode.shellData w a A B f qM qO rM rO Pair ParentRaw u))
    (hCS : Derives Γ (ForcingDensityCode.shellData w a A B f qM qO rM rO (if right then Q else P) ChildRaw v))
    (hPair : Derives Γ (binaryCode 0 w P Q Pair))
    (hPQ : Derives Γ (substituted w R S a f z b ParentRaw Parent))
    (hp : Derives Γ (ForcingFreshParentOpening.quantifiedData true
      w z a f A b C T t R S ParentRaw (u 4) Parent images p))
    (hc : Derives Γ (ForcingFreshParentOpening.quantifiedData true
      w z a f A b C T t R S ChildRaw (v 4) Child images c)) :
    Derives Γ (implication test w z b Parent Child) := by
  have p3 := Derives.conjR (.conjR (.conjR hp))
  have p5 := Derives.conjR (.conjR p3)
  have p6 := Derives.conjR p5
  have p7 := Derives.conjR p6
  have p8 := Derives.conjR p7
  have p9 := Derives.conjR p8
  have pInv := Derives.conjL (.conjR p9)
  have pInst := Derives.conjR (.conjR (.conjR (.conjR (.conjR pInv))))
  have c7 := Derives.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR hc))))))
  have c8 := Derives.conjR c7
  have c9 := Derives.conjR c8
  have hPWeakQuery := Derives.conjL p6
  have hPInput := SyntaxMixedFormulaOutput.input_of_substituted hZ w (images 8) (images 9)
    a f z T ParentRaw (p 6) hw hPWeakQuery
  have hL := Derives.conjL (.conjR hPInput)
  have hNat := Derives.conjL (.conjL (.conjR (.conjR hL)))
  have hTN := SyntaxTerms.range hZ w z T t hw ht
  have hCons := StructuralConsUnique.unique hZ w t (images 8) (c 7) (p 7) hw hTN hNat (.conjL c7) (.conjL p7)
  have hChildQuery := SyntaxMixedFormulaJudgmentSubst.subst_r w (c 7) (images 9) A f z T (v 4) (c 8) (p 7)
    hCons (.conjL c8)
  have hRaw := conjunction_from_outer_queries hZ right w z a A B f T C D rTerm (p 7) (images 9)
    qM qO rM rO P Q Pair ParentRaw ChildRaw (p 8) (c 8) u v hw hz hB hC hD hf2 ht2 hPS hCS hPair
    (.conjL p8) hChildQuery
  have hPS7 := Derives.conjR (.conjR (.conjR (.conjR (.conjR hPS))))
  have hWeakAll := ForcingMixedUnary.quantified_constructor hZ true w (images 8) (images 9) a f z T
    ParentRaw (u 4) (p 6) (p 5) A C (p 2) (p 3) hw hPInput (.conjL hPS7)
    hPWeakQuery (.conjL p3) (.conjL p5)
  have hWeak := ForcingWeakenedImages.from_queries hZ w a f z b T R S ParentRaw Parent (p 6) images
    (.conjI (.conjL (.conjR hp)) (.conjI hPQ hPWeakQuery))
  have hPA := ForcingFreshBackground.derive hZ w z b C T Parent (p 6) (.conjI hw (.conjI hz (.conjI hC hWeak)))
  exact transport_universal_at_point hZ w z b C T t Parent (p 6) (p 5) (p 8) (c 8) (c 4) Child hw hz
    (SyntaxMixedFormulaJudgment.target_type w R S a f z b ParentRaw Parent hPQ)
    hPA hWeakAll pInst (.conjR (.conjR c9)) (.conjL c9) hRaw


private theorem conjunction_all_at_fresh {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (right : Bool) (w z a A B f b C T D t rTerm R S qM qO rM rO P Q Pair ParentRaw ChildRaw Parent Child : Fin m)
    (u v : Fin 5 → Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hA : Derives Γ (successor A a)) (hB : Derives Γ (successor B A))
    (hC : Derives Γ (successor C z)) (hT : Derives Γ (successor T b)) (hD : Derives Γ (successor D T))
    (hf : Derives Γ (SyntaxVariableSyntax.code false w z t))
    (ht : Derives Γ (SyntaxTermSyntax.term w z T t))
    (hf2 : Derives Γ (SyntaxVariableSyntax.code false w z rTerm))
    (ht2 : Derives Γ (SyntaxTermSyntax.term w z D rTerm))
    (hPS : Derives Γ (ForcingDensityCode.shellData w a A B f qM qO rM rO Pair ParentRaw u))
    (hCS : Derives Γ (ForcingDensityCode.shellData w a A B f qM qO rM rO (if right then Q else P) ChildRaw v))
    (hPair : Derives Γ (binaryCode 0 w P Q Pair))
    (hPQ : Derives Γ (substituted w R S a f z b ParentRaw Parent))
    (hCQ : Derives Γ (substituted w R S a f z b ChildRaw Child)) :
    Derives Γ (implication test w z b Parent Child) := by
  have hPS7 := Derives.conjR (.conjR (.conjR (.conjR (.conjR hPS))))
  have hCS7 := Derives.conjR (.conjR (.conjR (.conjR (.conjR hCS))))
  have input {N X Y : Fin m} (hN : Derives Γ (singleCode 9 w X N))
      (hY : Derives Γ (substituted w R S a f z b N Y)) :
      Derives Γ (ForcingFreshParentOpening.quantifiedInput true w z a f A b C T t R S N X Y) :=
    .conjI hw (.conjI hz (.conjI hA (.conjI hC (.conjI hT (.conjI hf (.conjI ht (.conjI hN hY)))))))
  refine with_shared_quantified_openings hZ true w z a f A b C T t R S ParentRaw (u 4) Parent ChildRaw (v 4) Child
    (input (.conjL hPS7) hPQ) (input (.conjL hCS7) hCQ) (implication test w z b Parent Child) ?_
  intro l Δ e images p c hZ1 lift hp hc
  have hCS1 : Derives Δ (ForcingDensityCode.shellData (e w) (e a) (e A) (e B) (e f)
      (e qM) (e qO) (e rM) (e rO) (if right then e Q else e P) (e ChildRaw) (e ∘ v)) := by
    cases right <;> exact of_eq (ForcingDensityCode.shellData_rename _ _ _ _ _ _ _ _ _ _ _ _ _) (lift hCS)
  exact of_eq (implication_rename test w z b Parent Child e).symm
    (conjunction_from_actual_universal_records hZ1 right (e w) (e z) (e a) (e A) (e B) (e f) (e b)
      (e C) (e T) (e D) (e t) (e rTerm) (e R) (e S) (e qM) (e qO) (e rM) (e rO)
      (e P) (e Q) (e Pair) (e ParentRaw) (e ChildRaw) (e Parent) (e Child)
      (e ∘ u) (e ∘ v) images p c (of_eq (omega_rename _ _) (lift hw)) (of_eq (empty_rename _ _) (lift hz))
      (of_eq (successor_rename _ _ _) (lift hB)) (of_eq (successor_rename _ _ _) (lift hC))
      (of_eq (successor_rename _ _ _) (lift hD)) (of_eq (SyntaxTermSyntax.term_rename _ _ _ _ _) (lift ht))
      (of_eq (SyntaxVariableSyntax.code_rename _ _ _ _ _) (lift hf2))
      (of_eq (SyntaxTermSyntax.term_rename _ _ _ _ _) (lift ht2))
      (of_eq (ForcingDensityCode.shellData_rename _ _ _ _ _ _ _ _ _ _ _ _ _) (lift hPS)) hCS1
      (of_eq (binaryCode_rename _ _ _ _ _ _) (lift hPair)) (of_eq (substituted_rename _ _ _ _ _ _ _ _ _ _) (lift hPQ))
      hp hc)

private theorem with_fresh_free_term {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z b : Fin m) (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hb : Derives Γ (.mem b w)) (out : Formula m)
    (use : ∀ {l} {Δ : Context l} (r : Fin m → Fin l) (B t : Fin l), ZFContext.Evidence Δ →
      (∀ {F : Formula m}, Derives Γ F → Derives Δ (F.rename r)) →
      Derives Δ (.mem B (r w)) → Derives Δ (successor B (r b)) →
      Derives Δ (SyntaxVariableSyntax.code false (r w) (r z) t) →
      Derives Δ (SyntaxTermSyntax.term (r w) (r z) B t) → Derives Δ (out.rename r)) :
    Derives Γ out := by
  have hzN := SyntaxNumerals.range hZ 0 w z hw hz
  refine eliminate_objects hZ 1 (fun r v => (Formula.mem (v 0) (r w)).conj (successor (v 0) (r b)))
    (.impE (OmegaSyntax.step_at w b (.conjL hw)) hb) out ?_
  intro l Δ r v hZ1 lift hv
  have hw1 := of_eq (omega_rename _ _) (lift hw)
  have hz1 := of_eq (empty_rename _ _) (lift hz)
  have hZero := SyntaxIndexLiftOrder.zero_member hZ1 (r w) (r b) (v 0) (r z) hw1 (lift hb) (.conjR hv) hz1
  have hFresh := SyntaxTerms.exists_at hZ1 false (r w) (r z) (v 0) (r z) hw1
    (.conjI (.conjI (lift hzN) (.conjL hv)) hZero)
  refine eliminate_objects hZ1 1 (fun s u => (Formula.mem (u 0) (s (r w))).conj
    ((SyntaxVariableSyntax.code false (s (r w)) (s (r z)) (u 0)).conj
      (SyntaxTermSyntax.term (s (r w)) (s (r z)) (s (v 0)) (u 0)))) hFresh (out.rename r) ?_
  intro l1 Δ1 s u hZ2 lift1 ht
  let E := s ∘ r
  have move {F : Formula m} (h : Derives Γ F) : Derives Δ1 (F.rename E) :=
    of_eq (SourceAlgebra.rename_comp F r s) (lift1 (lift h))
  exact of_eq (SourceAlgebra.rename_comp out r s).symm
    (use E (s (v 0)) (u 0) hZ2 move (lift1 (.conjL hv))
      (of_eq (successor_rename _ _ _) (lift1 (.conjR hv))) (.conjL (.conjR ht)) (.conjR (.conjR ht)))


/-- Transport the original density universal from a conjunction to either
child. Both compiler shells, both quantified opens and all proof witnesses
belong to the object theory, including both fresh target free scopes. -/
theorem conjunction_all_from_compiler_shells {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (right : Bool) (w z a A B f b R S qM qO rM rO P Q Pair ParentRaw ChildRaw Parent Child : Fin m)
    (u v : Fin 5 → Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hA : Derives Γ (successor A a)) (hB : Derives Γ (successor B A))
    (hPS : Derives Γ (ForcingDensityCode.shellData w a A B f qM qO rM rO Pair ParentRaw u))
    (hCS : Derives Γ (ForcingDensityCode.shellData w a A B f qM qO rM rO (if right then Q else P) ChildRaw v))
    (hPair : Derives Γ (binaryCode 0 w P Q Pair))
    (hPQ : Derives Γ (substituted w R S a f z b ParentRaw Parent))
    (hCQ : Derives Γ (substituted w R S a f z b ChildRaw Child)) :
    Derives Γ (implication test w z b Parent Child) := by
  let out := implication test w z b Parent Child
  have hPT := SyntaxMixedFormulaJudgment.target_type w R S a f z b ParentRaw Parent hPQ
  have hb := Derives.conjR (.conjR (FormulaCodeProperties.guards w Parent z b hPT))
  have hzN := SyntaxNumerals.range hZ 0 w z hw hz
  refine eliminate_objects hZ 1 (fun r v => (Formula.mem (v 0) (r w)).conj (successor (v 0) (r z)))
    (.impE (OmegaSyntax.step_at w z (.conjL hw)) hzN) out ?_
  intro l Δ r k hZ1 lift hC
  refine with_fresh_free_term hZ1 (r w) (r z) (r b)
    (of_eq (omega_rename _ _) (lift hw)) (of_eq (empty_rename _ _) (lift hz))
    (lift hb) (out.rename r) ?_
  intro l1 Δ1 s T t hZ2 lift1 hTn hT hf ht
  let F := s ∘ r
  have move {X : Formula m} (h : Derives Γ X) : Derives Δ1 (X.rename F) :=
    of_eq (SourceAlgebra.rename_comp X r s) (lift1 (lift h))
  refine of_eq (SourceAlgebra.rename_comp out r s).symm ?_
  refine with_fresh_free_term hZ2 (F w) (F z) T
    (of_eq (omega_rename _ _) (move hw)) (of_eq (empty_rename _ _) (move hz)) hTn (out.rename F) ?_
  intro l2 Δ2 e D rTerm hZ3 lift2 _ hD hf2 ht2
  let E := e ∘ F
  have move2 {X : Formula m} (h : Derives Γ X) : Derives Δ2 (X.rename E) :=
    of_eq (SourceAlgebra.rename_comp X F e) (lift2 (move h))
  have hCS2 : Derives Δ2 (ForcingDensityCode.shellData (E w) (E a) (E A) (E B) (E f)
      (E qM) (E qO) (E rM) (E rO) (if right then E Q else E P) (E ChildRaw) (E ∘ v)) := by
    cases right <;> exact of_eq (ForcingDensityCode.shellData_rename _ _ _ _ _ _ _ _ _ _ _ _ _) (move2 hCS)
  exact of_eq (SourceAlgebra.rename_comp out F e).symm
    (of_eq (implication_rename test w z b Parent Child E).symm
      (conjunction_all_at_fresh hZ3 right (E w) (E z) (E a) (E A) (E B) (E f) (E b)
        (e (s (k 0))) (e T) D (e t) rTerm (E R) (E S) (E qM) (E qO) (E rM) (E rO)
        (E P) (E Q) (E Pair) (E ParentRaw) (E ChildRaw) (E Parent) (E Child) (E ∘ u) (E ∘ v)
        (of_eq (omega_rename _ _) (move2 hw)) (of_eq (empty_rename _ _) (move2 hz))
        (of_eq (successor_rename _ _ _) (move2 hA)) (of_eq (successor_rename _ _ _) (move2 hB))
        (of_eq (successor_rename _ _ (e ∘ s))
          (of_eq (SourceAlgebra.rename_comp _ s e) (lift2 (lift1 (.conjR hC)))))
        (of_eq (successor_rename _ _ _) (lift2 hT)) hD
        (of_eq (SyntaxVariableSyntax.code_rename _ _ _ _ _) (lift2 hf))
        (of_eq (SyntaxTermSyntax.term_rename _ _ _ _ _) (lift2 ht)) hf2 ht2
        (of_eq (ForcingDensityCode.shellData_rename _ _ _ _ _ _ _ _ _ _ _ _ _) (move2 hPS)) hCS2
        (of_eq (binaryCode_rename _ _ _ _ _ _) (move2 hPair))
        (of_eq (substituted_rename _ _ _ _ _ _ _ _ _ _) (move2 hPQ))
        (of_eq (substituted_rename _ _ _ _ _ _ _ _ _ _) (move2 hCQ))))


private theorem conjunction_all_from_shells {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (right : Bool) (w z a A B f b R S qM qO rM rO P Q Pair ParentRaw ChildRaw Parent Child : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hA : Derives Γ (successor A a)) (hB : Derives Γ (successor B A))
    (hPS : Derives Γ (ForcingDensityCode.shell w a A B f qM qO rM rO Pair ParentRaw))
    (hCS : Derives Γ (ForcingDensityCode.shell w a A B f qM qO rM rO (if right then Q else P) ChildRaw))
    (hPair : Derives Γ (binaryCode 0 w P Q Pair))
    (hPQ : Derives Γ (substituted w R S a f z b ParentRaw Parent))
    (hCQ : Derives Γ (substituted w R S a f z b ChildRaw Child)) :
    Derives Γ (implication test w z b Parent Child) := by
  let Selected := if right then Q else P
  let out := implication test w z b Parent Child
  refine eliminate_objects hZ 5 (fun r u => ForcingDensityCode.shellData
    (r w) (r a) (r A) (r B) (r f) (r qM) (r qO) (r rM) (r rO) (r Pair) (r ParentRaw) u) hPS out ?_
  intro l Δ r u hZ1 lift hp
  refine eliminate_objects hZ1 5 (fun s v => ForcingDensityCode.shellData
    (s (r w)) (s (r a)) (s (r A)) (s (r B)) (s (r f)) (s (r qM)) (s (r qO)) (s (r rM)) (s (r rO))
    (s (r Selected)) (s (r ChildRaw)) v)
    (of_eq (ForcingDensityCode.shell_rename _ _ _ _ _ _ _ _ _ _ _ r) (lift hCS)) (out.rename r) ?_
  intro l1 Δ1 s v hZ2 lift1 hc
  let E := s ∘ r
  have move {F : Formula m} (h : Derives Γ F) : Derives Δ1 (F.rename E) :=
    of_eq (SourceAlgebra.rename_comp F r s) (lift1 (lift h))
  have hc2 : Derives Δ1 (ForcingDensityCode.shellData (E w) (E a) (E A) (E B) (E f)
      (E qM) (E qO) (E rM) (E rO) (if right then E Q else E P) (E ChildRaw) v) := by
    cases right <;> exact hc
  exact of_eq (SourceAlgebra.rename_comp out r s).symm
    (of_eq (implication_rename test w z b Parent Child E).symm
      (conjunction_all_from_compiler_shells hZ2 right (E w) (E z) (E a) (E A) (E B) (E f) (E b)
        (E R) (E S) (E qM) (E qO) (E rM) (E rO) (E P) (E Q) (E Pair)
        (E ParentRaw) (E ChildRaw) (E Parent) (E Child) (s ∘ u) v
        (of_eq (omega_rename _ _) (move hw)) (of_eq (empty_rename _ _) (move hz))
        (of_eq (successor_rename _ _ _) (move hA)) (of_eq (successor_rename _ _ _) (move hB))
        (of_eq (ForcingDensityCode.shellData_rename _ _ _ _ _ _ _ _ _ _ _ _ s) (lift1 hp)) hc2
        (of_eq (binaryCode_rename _ _ _ _ _ _) (move hPair))
        (of_eq (substituted_rename _ _ _ _ _ _ _ _ _ _) (move hPQ))
        (of_eq (substituted_rename _ _ _ _ _ _ _ _ _ _) (move hCQ))))

/-- Generate the selected child's original compiler, compute its actual
substitution on the parent's table and transport the parent density proof. -/
theorem with_conjunct_density_proof {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (Reln : Formula (k+2)) (right : Bool) (w z a A B f b j R S N P Q ParentRaw Parent G : Fin m)
    (v : Fin 7 → Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hA : Derives Γ (successor A a)) (hB : Derives Γ (successor B A))
    (hN : Derives Γ (formulaCode w N a f)) (hG : Derives Γ (formulaCode w G z b))
    (hPair : Derives Γ (binaryCode 0 w P Q N))
    (hData : Derives Γ (ForcingDensityCode.data Reln w a A B f j N ParentRaw v))
    (hPQ : Derives Γ (substituted w R S a f z b ParentRaw Parent))
    (hPD : Derives Γ (implication test w z b G Parent))
    (out : Formula m)
    (use : ∀ {l} {Δ : Context l} (r : Fin m → Fin l) (ChildRaw Child : Fin l) (c : Fin 7 → Fin l),
      ZFContext.Evidence Δ →
      (∀ {F : Formula m}, Derives Γ F → Derives Δ (F.rename r)) →
      Derives Δ (ForcingDensityCode.data Reln (r w) (r a) (r A) (r B) (r f) (r j)
        (r (if right then Q else P)) ChildRaw c) →
      Derives Δ (substituted (r w) (r R) (r S) (r a) (r f) (r z) (r b) ChildRaw Child) →
      Derives Δ (implication test (r w) (r z) (r b) (r G) Child) →
      Derives Δ (out.rename r)) : Derives Γ out := by
  refine ForcingDensityCode.with_conjunct_compiler hZ Reln right w a A B f j N P Q ParentRaw v
    hw hA hB hN hPair hData out ?_
  intro l Δ r YP YQ ChildRaw hZ1 lift hPair1 hCD
  let C := if right then Q else P
  let c : Fin 7 → Fin l := Fin.lastCases (if right then YQ else YP) (fun i : Fin 6 => r (v i.castSucc))
  have hw1 := of_eq (omega_rename _ _) (lift hw)
  have hP1 := of_eq (ForcingDensityCode.data_rename _ _ _ _ _ _ _ _ _ _ r) (lift hData)
  have hCS := Derives.conjR (.conjR (.conjR (.conjR (.conjR (.conjR hCD)))))
  have hPS := Derives.conjR (.conjR (.conjR (.conjR (.conjR (.conjR hP1)))))
  have hCompiled : Derives Δ (ForcingDensityCode.compiled Reln (r w) (r a) (r A) (r B) (r f) (r j) (r C) ChildRaw) := by
    apply HornBinderRules.intro_many 7 (ForcingDensityCode.body Reln _ _ _ _ _ _ _ _) c
    exact of_eq (by simp only [ForcingDensityCode.body, ForcingDensityCode.data_rename, assign_old, assign_slot, C, c]) hCD
  have hCQType := ForcingDensityCode.compiled_type Reln (r w) (r a) (r A) (r B) (r f) (r j) (r C) ChildRaw hCompiled
  have hPQuery := of_eq (substituted_rename _ _ _ _ _ _ _ _ _ _) (lift hPQ)
  have hLists := Derives.conjR (SyntaxMixedFormulaOutput.input_of_substituted hZ1 (r w)
    (r R) (r S) (r a) (r f) (r z) (r b) (r ParentRaw) (r Parent) hw1 hPQuery)
  refine eliminate_objects hZ1 1 (fun s u => substituted (s (r w)) (s (r R)) (s (r S)) (s (r a)) (s (r f))
    (s (r z)) (s (r b)) (s ChildRaw) (u 0))
    (SyntaxMixedFormulaOutputInduction.actual_exists hZ1 (r w) (r R) (r S) (r a) (r f) (r z) (r b) ChildRaw
      hw1 (.conjI hCQType hLists)) (out.rename r) ?_
  intro l1 Δ1 s u hZ2 lift1 hCQ
  let E := s ∘ r
  have move {F : Formula m} (h : Derives Γ F) : Derives Δ1 (F.rename E) :=
    of_eq (SourceAlgebra.rename_comp F r s) (lift1 (lift h))
  have hw2 := of_eq (omega_rename _ _) (move hw)
  have hz2 := of_eq (empty_rename _ _) (move hz)
  have hPQ2 := of_eq (substituted_rename _ _ _ _ _ _ _ _ _ _) (move hPQ)
  have hCS2 : Derives Δ1 (ForcingDensityCode.shell (E w) (E a) (E A) (E B) (E f)
      (E (v 2)) (E (v 3)) (E (v 4)) (E (v 5)) (if right then s YQ else s YP) (s ChildRaw)) := by
    cases right <;> exact of_eq (ForcingDensityCode.shell_rename _ _ _ _ _ _ _ _ _ _ _ s) (lift1 hCS)
  have hTransfer := conjunction_all_from_shells hZ2 right (E w) (E z) (E a) (E A) (E B) (E f) (E b)
    (E R) (E S) (E (v 2)) (E (v 3)) (E (v 4)) (E (v 5)) (s YP) (s YQ) (E (v 6))
    (E ParentRaw) (s ChildRaw) (E Parent) (u 0) hw2 hz2
    (of_eq (successor_rename _ _ _) (move hA)) (of_eq (successor_rename _ _ _) (move hB))
    (of_eq (ForcingDensityCode.shell_rename _ _ _ _ _ _ _ _ _ _ _ s) (lift1 hPS)) hCS2
    (of_eq (binaryCode_rename _ _ _ _ _ _) (lift1 hPair1)) hPQ2 hCQ
  have hProof := ForcingRelationGuardProof.chain hZ2 test (E w) (E z) (E b) (E G) (E Parent) (u 0) hw2 hz2
    (of_eq (formulaCode_rename _ _ _ _ _) (move hG))
    (SyntaxMixedFormulaJudgment.target_type _ _ _ _ _ _ _ _ _ hPQ2)
    (SyntaxMixedFormulaJudgment.target_type _ _ _ _ _ _ _ _ _ hCQ)
    (of_eq (implication_rename _ _ _ _ _ _ _) (move hPD)) hTransfer
  exact of_eq (SourceAlgebra.rename_comp out r s).symm
    (use E (s ChildRaw) (u 0) (s ∘ c) hZ2 move
      (of_eq (ForcingDensityCode.data_rename _ _ _ _ _ _ _ _ _ _ s) (lift1 hCD)) hCQ hProof)

end ConjunctionWitness


section FalsumFromCompiler

open ForcingReflexiveImages (replacement replacement_rename)
open SyntaxLogicalSyntax (singleCode_rename binaryCode_rename)
open FormulaCodeSyntax (formulaCode_rename)
open SyntaxNumeralSyntax (numeral numeral_rename)
attribute [local irreducible] NaturalRecursionSyntax.matrix
set_option maxHeartbeats 1600000

private structure ReflexiveRuntime (m : Nat) where
  w : Fin m
  z : Fin m
  f : Fin m
  b : Fin m
  j : Fin m
  base : Fin m
  carrierIndex : Fin m
  carrier : Fin m
  extra : Fin m
  one : Fin m
  two : Fin m
  three : Fin m
  bound : Fin m
  boundTable : Fin m
  reflCode : Fin m
  pre : Fin m
  raw : Fin 16 → Fin m
  gb : Fin 5 → Fin m
  guards : Fin 6 → Fin m
  layout : Fin 6 → Fin m
  instances : Fin 3 → Fin m
  bodies : Fin 3 → Fin m
  terms : Fin 3 → Fin m
  inner : Fin 5 → Fin m
  prefixed : Fin 3 → Fin m

private abbrev ReflexiveRuntime.p {m} (q : ReflexiveRuntime m) : Fin m := q.terms 1
private abbrev ReflexiveRuntime.G {m} (q : ReflexiveRuntime m) : Fin m := q.layout 3

private def ReflexiveRuntime.map {m l} (q : ReflexiveRuntime m) (r : Fin m → Fin l) : ReflexiveRuntime l :=
  ⟨r q.w, r q.z, r q.f, r q.b, r q.j, r q.base, r q.carrierIndex, r q.carrier, r q.extra,
    r q.one, r q.two, r q.three, r q.bound, r q.boundTable, r q.reflCode, r q.pre,
    r ∘ q.raw, r ∘ q.gb, r ∘ q.guards, r ∘ q.layout, r ∘ q.instances, r ∘ q.bodies, r ∘ q.terms,
    r ∘ q.inner, r ∘ q.prefixed⟩

private structure ReflexiveEvidence {k m} (Γ : Context m) (Reln : Formula (k+2)) (q : ReflexiveRuntime m)
    (S : Fin m) : Prop where
  omega : Derives Γ (omega q.w)
  zero : Derives Γ (empty q.z)
  term : Derives Γ (SyntaxTermSyntax.term q.w q.z q.b q.p)
  background : Derives Γ (formulaCode q.w q.G q.z q.b)
  carrierIndex : Derives Γ (numeral k q.carrierIndex)
  freeScope : Derives Γ (numeral (k+2) q.f)
  conditionIndex : Derives Γ (numeral (k+1) q.j)
  updated : Derives Γ (replacement q.w q.f q.z q.b q.base q.j q.p S)
  carrier : Derives Γ (field q.w q.base q.carrierIndex q.carrier)
  one : Derives Γ (numeral 1 q.one)
  two : Derives Γ (numeral 2 q.two)
  row : Derives Γ (ForcingPreorderLeaves.data test Reln q.w q.z q.one q.two q.three q.f q.b
    q.bound q.boundTable q.base q.reflCode q.pre q.raw q.gb q.guards q.instances q.bodies q.terms q.inner q.prefixed)
  reflexive : Derives Γ (substituted q.w q.boundTable q.base q.z q.f q.z q.b (q.raw 1) q.reflCode)
  extra : Derives Γ (formulaCode q.w q.extra q.z q.b)
  layout : Derives Γ (ForcingProofContext.layoutData q.w q.z q.b q.extra q.pre q.guards q.layout)

private theorem ReflexiveEvidence.map {k m l} {Γ : Context m} {Δ : Context l} {Reln : Formula (k+2)}
    {q : ReflexiveRuntime m} {S : Fin m} (h : ReflexiveEvidence Γ Reln q S)
    (r : Fin m → Fin l) (lift : ∀ {F : Formula m}, Derives Γ F → Derives Δ (F.rename r)) :
    ReflexiveEvidence Δ Reln (q.map r) (r S) :=
  ⟨of_eq (omega_rename _ _) (lift h.omega), of_eq (empty_rename _ _) (lift h.zero),
    of_eq (SyntaxTermSyntax.term_rename _ _ _ _ _) (lift h.term), of_eq (formulaCode_rename _ _ _ _ _) (lift h.background),
    of_eq (numeral_rename _ _ _) (lift h.carrierIndex), of_eq (numeral_rename _ _ _) (lift h.freeScope),
    of_eq (numeral_rename _ _ _) (lift h.conditionIndex), of_eq (replacement_rename _ _ _ _ _ _ _ _ _) (lift h.updated),
    of_eq (field_rename _ _ _ _ _) (lift h.carrier), of_eq (numeral_rename _ _ _) (lift h.one),
    of_eq (numeral_rename _ _ _) (lift h.two),
    of_eq (ForcingPreorderLeaves.data_rename test Reln _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ r) (lift h.row),
    of_eq (substituted_rename _ _ _ _ _ _ _ _ _ r) (lift h.reflexive),
    of_eq (formulaCode_rename _ _ _ _ _) (lift h.extra),
    of_eq (ForcingProofContext.layoutData_rename _ _ _ _ _ _ _ _) (lift h.layout)⟩

private theorem with_reflexive_tail_at_instance {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    {Reln : Formula (k+2)} {q : ReflexiveRuntime m} {S : Fin m} (h : ReflexiveEvidence Γ Reln q S)
    (a A L Pfx HeadZero Head Member Order Tail Inner Local : Fin m)
    (o : Fin 5 → Fin m) (u v x : Fin 4 → Fin m)
    (hA : Derives Γ (successor A a))
    (hHeadZero : Derives Γ (empty HeadZero))
    (hHeadCode : Derives Γ (SyntaxVariableSyntax.code true q.w HeadZero Head))
    (hm : Derives Γ (ForcingGuardCode.compiled false Reln q.w A q.f Head Member))
    (ho : Derives Γ (ForcingGuardCode.compiled true Reln q.w A q.f Head Order))
    (hl : Derives Γ (SyntaxCodedMixedBinderSyntax.lifted q.w L S a q.f q.z q.b (o 1) (o 2) (o 3) (o 4)))
    (hPfx : Derives Γ (consCode q.w q.p L Pfx))
    (hu : Derives Γ (ForcingRawModalBody.data q.w (o 3) (o 4) (o 1) q.f (o 2) q.b Member Order
      Tail Inner (o 0) u))
    (hv : Derives Γ (ForcingDensityInstantiation.pointData q.w q.z q.b (o 0) q.p Local (u 1) (u 2) (u 3) (u 0) v))
    (hx : Derives Γ (ForcingRawModalBody.data q.w (v 2) (v 3) (v 0) q.b q.z q.b (u 1) (u 2) (u 3) (u 0) (v 1) x))
    (hLocal : Derives Γ (formulaCode q.w Local q.z q.b))
    (pGlobal : Derives Γ (implication test q.w q.z q.b Local q.G))
    (out : Formula m)
    (use : ∀ {l} {Δ : Context l} (r : Fin m → Fin l), ZFContext.Evidence Δ →
      (∀ {F : Formula m}, Derives Γ F → Derives Δ (F.rename r)) →
      Derives Δ (substituted (r q.w) (r Pfx) (r S) (r (o 1)) (r q.f) (r q.z) (r q.b) (r Tail) (r (x 3))) →
      Derives Δ (implication test (r q.w) (r q.z) (r q.b) (r Local) (r (x 3))) →
      Derives Δ (out.rename r)) : Derives Γ out := by
  have eZero := OmegaUniversal.empty_unique HeadZero q.z (ZFContext.arithmetic hZ).base.extensionality
    hHeadZero h.zero
  have hh := SyntaxVariableImagePoint.code_subst_index true q.w HeadZero Head q.z eZero hHeadCode
  have hGuard := from_records hZ Reln q.w q.z a A (o 1) (o 2) q.f q.b L S (o 3) (o 4) q.p
    Head Local Member Order Tail Inner (o 0) u v x h.omega h.zero hA hLocal hl hh hm ho hu hv hx
  have hEnv := SyntaxCodedMixedBinderTyping.input_of_lifted q.w L S a q.f q.z q.b (o 1) (o 2) (o 3) (o 4) hl
  have hA' := Derives.conjL (.conjR hEnv)
  have eA := OmegaUniversal.successor_unique A (o 1) a (ZFContext.arithmetic hZ).base.extensionality hA hA'
  have eC := OmegaUniversal.successor_unique (v 0) (o 2) q.z (ZFContext.arithmetic hZ).base.extensionality
    (.conjL hv) (.conjR (.conjR hEnv))
  have hm' := guard_scope false Reln q.w A (o 1) q.f Head Member eA hm
  have hCoded := Derives.conjL (.conjL (.conjR hv))
  have hmQuery := Derives.conjL (.conjR (.conjL hu))
  have hmPoint := Derives.conjL (.conjR (.conjL hx))
  have hoPoint := Derives.conjL (.conjR (.conjR hx))
  have hTailPoint := Derives.conjR (.conjR (.conjR hx))
  have hTailQuery := Derives.conjR (.conjR (.conjR hu))
  have hmInst := SyntaxTopFormulaSyntax.intro_instantiated q.w q.z q.b (v 0) q.p (u 1) (x 1) (v 2) (v 3)
    hCoded hmPoint
  have hmNative := instance_scope q.w q.z q.b (v 0) (o 2) q.p (u 1) (x 1) eC hmInst
  have hMember := member_from_proof hZ Reln q.w q.z a (o 1) (o 2) q.f q.b L S (o 3) (o 4)
    q.p Pfx Head Member (u 1) (x 1) q.carrierIndex q.carrier q.G (q.guards 1)
    h.omega h.zero h.term hl hPfx hh hm' hmQuery hmNative h.carrierIndex
    (ForcingPreorderGuardTables.carrier_field hZ q.w q.f q.z q.b q.base q.j q.p S
      q.carrierIndex q.carrier h.freeScope h.conditionIndex h.carrierIndex h.updated h.carrier)
    (ForcingPreorderMember.raw_from_data hZ test Reln 1 q.w q.z q.one q.two q.three q.f q.b
      q.bound q.boundTable q.base q.reflCode q.pre q.carrierIndex q.carrier q.raw q.gb q.guards
      q.instances q.bodies q.terms q.inner q.prefixed h.omega h.zero h.one h.two h.carrierIndex h.row h.carrier)
    (.conjL (.conjR (ForcingAtomicMono.layout_proofs hZ q.w q.z q.b q.extra q.pre q.guards q.layout
      h.omega h.zero h.extra h.layout)))
  have hOrder : Derives Γ (implication test q.w q.z q.b q.G (x 2)) :=
    tail_from_reflexive_query hZ Reln q.w q.z a (o 1) (o 2) q.f q.b L q.base S (o 3) (o 4) Pfx
      Head Member (u 1) (x 1) Order (x 2) (x 2) q.carrierIndex q.j q.carrier q.extra
      q.one q.two q.three q.bound q.boundTable q.reflCode q.pre q.raw q.gb q.guards q.layout
      q.instances q.bodies q.terms q.inner q.prefixed h.omega h.zero h.term hl hPfx hh hm' hmQuery hmNative
      (.conjR (.conjL hGuard)) h.carrierIndex h.freeScope h.conditionIndex h.updated h.carrier
      h.one h.two h.row h.reflexive h.extra h.layout (.impI (.impI (.hyp (Or.inl rfl))))
  have hmType := SyntaxMixedFormulaJudgment.target_type q.w (v 2) (v 3) (v 0) q.b q.z q.b (u 1) (x 1) hmPoint
  have hoType := SyntaxMixedFormulaJudgment.target_type q.w (v 2) (v 3) (v 0) q.b q.z q.b (u 2) (x 2) hoPoint
  have pM := ForcingRelationGuardProof.chain hZ test q.w q.z q.b Local q.G (x 1)
    h.omega h.zero hLocal h.background hmType pGlobal hMember
  have pO := ForcingRelationGuardProof.chain hZ test q.w q.z q.b Local q.G (x 2)
    h.omega h.zero hLocal h.background hoType pGlobal hOrder
  have pTail := Derives.impE (.impE (.conjR hGuard) pM) pO
  have hTailInst := SyntaxTopFormulaSyntax.intro_instantiated q.w q.z q.b (v 0) q.p (u 3) (x 3) (v 2) (v 3)
    hCoded hTailPoint
  have hTailNative := instance_scope q.w q.z q.b (v 0) (o 2) q.p (u 3) (x 3) eC hTailInst
  have hSource := SyntaxMixedFormulaJudgmentTyping.source_type hZ q.w (o 3) (o 4) (o 1) q.f (o 2) q.b
    Tail (u 3) h.omega hTailQuery
  exact with_direct_query hZ q.w q.z a (o 1) (o 2) q.f q.b L S (o 3) (o 4) q.p Pfx Tail
    (u 3) (x 3) h.omega h.zero h.term hl hPfx hSource hTailQuery hTailNative out
    (fun r hZ1 lift _ _ hDirect =>
      use r hZ1 lift hDirect (of_eq (implication_rename test _ _ _ _ _ r) (lift pTail)))

/-- Instantiate the original negative or existential outer shell at its own
condition. The inherited preorder supplies both guards and the tail keeps
its actual raw query in the prefixed table. -/
theorem with_reflexive_outer_tail {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (Reln : Formula (k+2)) (w z a A f b j L S Base K Extra A1 A2 A3 Cr Bd Refl Pre
      Parent ParentOut HeadZero Head Member Order Tail Inner Body Local : Fin m)
    (raw : Fin 16 → Fin m) (Gb : Fin 5 → Fin m) (H layout : Fin 6 → Fin m)
    (U F P : Fin 3 → Fin m) (I : Fin 5 → Fin m) (Ds : Fin 3 → Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hA : Derives Γ (successor A a))
    (ht : Derives Γ (SyntaxTermSyntax.term w z b (P 1)))
    (hi : Derives Γ (numeral k K)) (hf : Derives Γ (numeral (k+2) f)) (hj : Derives Γ (numeral (k+1) j))
    (hBase : Derives Γ (SyntaxMixedImageCodeSyntax.termList w f z b Base))
    (hUpdate : Derives Γ (replacement w f z b Base j (P 1) S))
    (hA1 : Derives Γ (numeral 1 A1)) (hA2 : Derives Γ (numeral 2 A2))
    (hRow : Derives Γ (ForcingPreorderLeaves.data test Reln w z A1 A2 A3 f b Cr Bd Base Refl Pre raw Gb H U F P I Ds))
    (hPre : Derives Γ (substituted w Bd Base z f z b (raw 0) Pre))
    (hExtra : Derives Γ (formulaCode w Extra z b))
    (hLayout : Derives Γ (ForcingProofContext.layoutData w z b Extra Pre H layout))
    (hHeadZero : Derives Γ (empty HeadZero))
    (hHeadCode : Derives Γ (SyntaxVariableSyntax.code true w HeadZero Head))
    (hm : Derives Γ (ForcingGuardCode.compiled false Reln w A f Head Member))
    (ho : Derives Γ (ForcingGuardCode.compiled true Reln w A f Head Order))
    (hShell : Derives Γ (ForcingRawModalBody.shell w Parent Member Order Tail Inner Body))
    (hQuery : Derives Γ (substituted w L S a f z b Parent ParentOut))
    (hLocal : Derives Γ (formulaCode w Local z b))
    (pGlobal : Derives Γ (implication test w z b Local (layout 3)))
    (pParent : Derives Γ (implication test w z b Local ParentOut))
    (out : Formula m)
    (use : ∀ {l} {Δ : Context l} (r : Fin m → Fin l) (A' Pfx TailOut : Fin l), ZFContext.Evidence Δ →
      (∀ {G : Formula m}, Derives Γ G → Derives Δ (G.rename r)) →
      Derives Δ (successor A' (r a)) →
      Derives Δ (consCode (r w) (r (P 1)) (r L) Pfx) →
      Derives Δ (substituted (r w) Pfx (r S) A' (r f) (r z) (r b) (r Tail) TailOut) →
      Derives Δ (implication test (r w) (r z) (r b) (r Local) TailOut) →
      Derives Δ (out.rename r)) : Derives Γ out := by
  have hCore := Derives.conjL (.conjL (.conjR hRow))
  have hAnd : Derives Γ (binaryCode 0 w Refl (U 0) Pre) := .conjL (.conjR hCore)
  have hRun := ForcingPreorderInstances.reflexive_query hZ Reln w z A1 A2 A3 f b Bd Base Pre Refl (U 0) raw
    hw (.conjL hRow) hPre hAnd
  have hG := Derives.conjR (.conjL (.conjR (.conjR (.conjR hLayout))))
  have hIndex := SyntaxNumeralMembers.index_member hZ (k+2) (Fin.last k).castSucc f K hf hi
  have hIndexW := StructuralListTraceOrder.member_member hZ w K f hw (.conjL hBase) hIndex
  refine eliminate_objects hZ 1 (fun r x => (Formula.mem (x 0) (r w)).conj (field (r w) (r Base) (r K) (x 0)))
    (StructuralListFieldValues.exists_value hZ w Base K hw hIndexW) out ?_
  intro l Δ r x hZ1 lift hV
  let q : ReflexiveRuntime l := ⟨r w,r z,r f,r b,r j,r Base,r K,x 0,r Extra,r A1,r A2,r A3,
    r Cr,r Bd,r Refl,r Pre,r ∘ raw,r ∘ Gb,r ∘ H,r ∘ layout,r ∘ U,r ∘ F,r ∘ P,r ∘ I,r ∘ Ds⟩
  let h : ReflexiveEvidence Δ Reln q (r S) :=
    ⟨of_eq (omega_rename _ _) (lift hw), of_eq (empty_rename _ _) (lift hz),
      of_eq (SyntaxTermSyntax.term_rename _ _ _ _ r) (lift ht), of_eq (formulaCode_rename _ _ _ _ r) (lift hG),
      of_eq (numeral_rename _ _ r) (lift hi), of_eq (numeral_rename _ _ r) (lift hf),
      of_eq (numeral_rename _ _ r) (lift hj), of_eq (replacement_rename _ _ _ _ _ _ _ _ r) (lift hUpdate),
      .conjR hV, of_eq (numeral_rename _ _ r) (lift hA1), of_eq (numeral_rename _ _ r) (lift hA2),
      of_eq (ForcingPreorderLeaves.data_rename test Reln _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ r) (lift hRow),
      of_eq (substituted_rename _ _ _ _ _ _ _ _ _ r) (lift hRun),
      of_eq (formulaCode_rename _ _ _ _ r) (lift hExtra),
      of_eq (ForcingProofContext.layoutData_rename _ _ _ _ _ _ _ r) (lift hLayout)⟩
  refine ForcingDensityInstantiation.with_outer_instance hZ1 (r w) (r z) (r a) (r f) (r b) (r L) (r S)
    (r Parent) (r ParentOut) (r (P 1)) (r Local) (r Member) (r Order) (r Tail) (r Inner) (r Body)
    h.omega h.zero h.term (of_eq (formulaCode_rename _ _ _ _ r) (lift hLocal))
    (of_eq (implication_rename test _ _ _ _ _ r) (lift pParent))
    (of_eq (ForcingRawModalBody.shell_rename _ _ _ _ _ _ _ r) (lift hShell))
    (of_eq (substituted_rename _ _ _ _ _ _ _ _ _ r) (lift hQuery)) (out.rename r) ?_
  intro l2 Ξ s o u v y hZ2 move hLift hRaw hPoint hDirect
  let e := s ∘ r
  have carry {G : Formula m} (p : Derives Γ G) : Derives Ξ (G.rename e) :=
    of_eq (SourceAlgebra.rename_comp G r s) (move (lift p))
  have h2 := h.map s move
  have hEnv := SyntaxCodedMixedBinderTyping.input_of_lifted (e w) (e L) (e S) (e a) (e f) (e z) (e b)
    (o 1) (o 2) (o 3) (o 4) hLift
  have hL := Derives.conjL (.conjL (.conjR (.conjR (.conjL (.conjL hEnv)))))
  have hTerm := SyntaxTerms.range hZ2 (e w) (e z) (e b) (e (P 1)) h2.omega h2.term
  apply of_eq (SourceAlgebra.rename_comp out r s).symm
  refine eliminate_objects hZ2 1 (fun t x => (Formula.mem (x 0) (t (e w))).conj
    (consCode (t (e w)) (t (e (P 1))) (t (e L)) (x 0)))
    (StructuralConsCore.exists_cons hZ2 (e w) (e (P 1)) (e L) h2.omega hTerm hL) (out.rename e) ?_
  intro l3 Ω t pfx hZ3 move2 hPfx
  let ρ := t ∘ e
  have lift2 {G : Formula m} (p : Derives Γ G) : Derives Ω (G.rename ρ) :=
    of_eq (SourceAlgebra.rename_comp G e t) (move2 (carry p))
  refine of_eq (SourceAlgebra.rename_comp out e t).symm ?_
  have hLift3 := of_eq (SyntaxCodedMixedBinderSyntax.lifted_rename _ _ _ _ _ _ _ _ _ _ _ t) (move2 hLift)
  have hScope := Derives.conjL (.conjR
    (SyntaxCodedMixedBinderTyping.input_of_lifted (ρ w) (ρ L) (ρ S) (ρ a) (ρ f) (ρ z) (ρ b)
      (t (o 1)) (t (o 2)) (t (o 3)) (t (o 4)) hLift3))
  refine with_reflexive_tail_at_instance hZ3 (h2.map t move2) (ρ a) (ρ A) (ρ L) (pfx 0) (ρ HeadZero) (ρ Head)
    (ρ Member) (ρ Order) (ρ Tail) (ρ Inner) (ρ Local) (t ∘ o) (t ∘ u) (t ∘ v) (t ∘ y)
    (of_eq (successor_rename _ _ ρ) (lift2 hA))
    (of_eq (empty_rename _ _) (lift2 hHeadZero))
    (of_eq (SyntaxVariableSyntax.code_rename _ _ _ _ ρ) (lift2 hHeadCode))
    (of_eq (ForcingGuardCode.compiled_rename false Reln _ _ _ _ _ ρ) (lift2 hm))
    (of_eq (ForcingGuardCode.compiled_rename true Reln _ _ _ _ _ ρ) (lift2 ho))
    hLift3 (.conjR hPfx)
    (of_eq (ForcingRawModalBody.data_rename _ _ _ _ _ _ _ _ _ _ _ _ u t) (move2 hRaw))
    (of_eq (ForcingDensityInstantiation.pointData_rename _ _ _ _ _ _ _ _ _ _ v t) (move2 hPoint))
    (of_eq (ForcingRawModalBody.data_rename _ _ _ _ _ _ _ _ _ _ _ _ y t) (move2 hDirect))
    (of_eq (formulaCode_rename _ _ _ _ ρ) (lift2 hLocal))
    (of_eq (implication_rename test _ _ _ _ _ ρ) (lift2 pGlobal)) (out.rename ρ) ?_
  intro l4 Δ4 g hZ4 move3 hTailQuery pTail
  let R := g ∘ ρ
  have lift3 {F : Formula m} (h : Derives Γ F) : Derives Δ4 (F.rename R) :=
    of_eq (SourceAlgebra.rename_comp F ρ g) (move3 (lift2 h))
  exact of_eq (SourceAlgebra.rename_comp out ρ g).symm
    (use R (g (t (o 1))) (g (pfx 0)) (g (t (y 3))) hZ4 lift3
      (of_eq (successor_rename _ _ g) (move3 hScope))
      (of_eq (consCode_rename _ _ _ _ g) (move3 (.conjR hPfx))) hTailQuery pTail)

/-- The original negative witness at r is instantiated at that same r.
Its actual guards are proved from the inherited preorder, and its rebound
operand is the very same positive query. Original Root MP yields falsum. -/
theorem negative_reflexive_contradiction {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (Reln : Formula (k+2)) (w z a A f b j L S Base K Extra A1 A2 A3 Cr Bd Refl Pre
      Child Neg AtR NegR Local : Fin m)
    (raw : Fin 16 → Fin m) (Gb : Fin 5 → Fin m) (H layout : Fin 6 → Fin m)
    (U F P : Fin 3 → Fin m) (I : Fin 5 → Fin m) (Ds : Fin 3 → Fin m)
    (cv : Fin 5 → Fin m) (sv : Fin 4 → Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hA : Derives Γ (successor A a))
    (ht : Derives Γ (SyntaxTermSyntax.term w z b (P 1)))
    (hi : Derives Γ (numeral k K)) (hf : Derives Γ (numeral (k+2) f)) (hj : Derives Γ (numeral (k+1) j))
    (hBase : Derives Γ (SyntaxMixedImageCodeSyntax.termList w f z b Base))
    (hUpdate : Derives Γ (replacement w f z b Base j (P 1) S))
    (hA1 : Derives Γ (numeral 1 A1)) (hA2 : Derives Γ (numeral 2 A2))
    (hRow : Derives Γ (ForcingPreorderLeaves.data test Reln w z A1 A2 A3 f b Cr Bd Base Refl Pre raw Gb H U F P I Ds))
    (hPre : Derives Γ (substituted w Bd Base z f z b (raw 0) Pre))
    (hExtra : Derives Γ (formulaCode w Extra z b))
    (hLayout : Derives Γ (ForcingProofContext.layoutData w z b Extra Pre H layout))
    (hc : Derives Γ (ForcingNegCode.data Reln w a A f j Child Neg cv))
    (hs : Derives Γ (ForcingNegCode.shellData w a A f (cv 3) (cv 4) (cv 2) Neg sv))
    (hAtR : Derives Γ (substituted w L S a f z b Child AtR))
    (hNegR : Derives Γ (substituted w L S a f z b Neg NegR))
    (hLocal : Derives Γ (formulaCode w Local z b))
    (pGlobal : Derives Γ (implication test w z b Local (layout 3)))
    (pAtR : Derives Γ (implication test w z b Local AtR))
    (pNeg : Derives Γ (implication test w z b Local NegR)) :
    Derives Γ (implication test w z b Local (sv 0)) := by
  have hHead := Derives.conjL hc
  have hShell : Derives Γ (ForcingRawModalBody.shell w Neg (cv 3) (cv 4) (sv 1) (sv 2) (sv 3)) :=
    .conjI (.conjL (.conjR (.conjR (.conjR (.conjR hs)))))
      (.conjI (.conjL (.conjL (.conjR (.conjR (.conjR hs))))) (.conjL (.conjL (.conjR (.conjR hs)))))
  refine with_reflexive_outer_tail hZ Reln w z a A f b j L S Base K Extra A1 A2 A3 Cr Bd Refl Pre
    Neg NegR (cv 0) (cv 1) (cv 3) (cv 4) (sv 1) (sv 2) (sv 3) Local
    raw Gb H layout U F P I Ds hw hz hA ht hi hf hj hBase hUpdate hA1 hA2 hRow hPre hExtra hLayout
    (.conjL hHead) (.conjL (.conjR hHead)) (.conjL (.conjR (.conjR hc)))
    (.conjL (.conjR (.conjR (.conjR hc)))) hShell hNegR hLocal pGlobal pNeg
    (implication test w z b Local (sv 0)) ?_
  intro l Δ r A' Pfx Tail hZ1 lift hA' hPfx hTail pTail
  have hw1 := of_eq (omega_rename _ _) (lift hw)
  have hz1 := of_eq (empty_rename _ _) (lift hz)
  have ht1 := of_eq (SyntaxTermSyntax.term_rename _ _ _ _ r) (lift ht)
  have hReplace := of_eq (replacement_rename _ _ _ _ _ _ _ _ r) (lift hUpdate)
  have eA := OmegaUniversal.successor_unique (r A) A' (r a) (ZFContext.arithmetic hZ1).base.extensionality
    (of_eq (successor_rename _ _ r) (lift hA)) hA'
  let Rebind := ForcingConditionRebind.compiled (r w).castSucc (r a).castSucc (r f).castSucc (Fin.last l)
    (r j).castSucc (r Child).castSucc (r (cv 2)).castSucc
  have rebindAt (i : Fin l) : Rebind.instantiate i =
      ForcingConditionRebind.compiled (r w) (r a) (r f) i (r j) (r Child) (r (cv 2)) := by
    simp only [Rebind, Formula.instantiate, ForcingConditionRebind.compiled_rename,
      Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have hComp := of_eq (ForcingConditionRebind.compiled_rename _ _ _ _ _ _ _ r) (lift (.conjL (.conjR hc)))
  have hRebind := of_eq (rebindAt A') (.eqSubst Rebind eA (of_eq (rebindAt (r A)).symm hComp))
  have hBot : Derives Δ (SyntaxNodeSyntax.constructor 0 0 (r w) Fin.elim0 (r (sv 0))) :=
    of_eq (by simp only [SyntaxNodeSyntax.constructor_rename, SyntaxAtomSyntax.zero_map])
      (lift (.conjL (.conjL hs)))
  have hAtR1 := of_eq (substituted_rename _ _ _ _ _ _ _ _ _ r) (lift hAtR)
  have hTailCode := ForcingRawNegTail.canonical_code hZ1 (r w) (r z) (r a) A' (r f) (r b)
    (r L) Pfx (r S) (r Base) (r j) (r (P 1)) (r (P 1)) (r S) (r Child)
    (r (cv 2)) (r (sv 0)) (r (sv 1)) Tail (r AtR) (r (sv 0)) hw1 hz1 ht1 hPfx hReplace hReplace
    hRebind (of_eq (binaryCode_rename 2 _ _ _ _ r) (lift (.conjL (.conjL (.conjR hs))))) hBot hTail hAtR1 hBot
  have hTailType := SyntaxMixedFormulaJudgment.target_type (r w) Pfx (r S) A' (r f) (r z) (r b)
    (r (sv 1)) Tail hTail
  exact of_eq (implication_rename test _ _ _ _ _ r).symm
    (ForcingNegMemberProof.discharge hZ1 test (r w) (r z) (r b) (r Local) (r AtR) (r (sv 0)) Tail
      hw1 hz1 (of_eq (formulaCode_rename _ _ _ _ r) (lift hLocal)) hTailType hTailCode
      (of_eq (implication_rename test _ _ _ _ _ r) (lift pAtR)) pTail)

/-- The source existential branch instantiates the same compiled universal
at its selected condition. Read the second witness and name binders from
the resulting tail while retaining the proof of that exact tail. -/
theorem with_existential_at_reflexive {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (Reln : Formula (k+2)) (Dom : Formula (k+1))
    (w z a A B C f b j L S Base K Extra A1 A2 A3 Cr Bd Refl Pre Child Parent ParentOut Local : Fin m)
    (raw : Fin 16 → Fin m) (Gb : Fin 5 → Fin m) (H layout : Fin 6 → Fin m)
    (U F P : Fin 3 → Fin m) (I : Fin 5 → Fin m) (Ds : Fin 3 → Fin m)
    (cv : Fin 8 → Fin m) (sv : Fin 7 → Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hA : Derives Γ (successor A a))
    (ht : Derives Γ (SyntaxTermSyntax.term w z b (P 1)))
    (hi : Derives Γ (numeral k K)) (hf : Derives Γ (numeral (k+2) f)) (hj : Derives Γ (numeral (k+1) j))
    (hBase : Derives Γ (SyntaxMixedImageCodeSyntax.termList w f z b Base))
    (hUpdate : Derives Γ (replacement w f z b Base j (P 1) S))
    (hA1 : Derives Γ (numeral 1 A1)) (hA2 : Derives Γ (numeral 2 A2))
    (hRow : Derives Γ (ForcingPreorderLeaves.data test Reln w z A1 A2 A3 f b Cr Bd Base Refl Pre raw Gb H U F P I Ds))
    (hPre : Derives Γ (substituted w Bd Base z f z b (raw 0) Pre))
    (hExtra : Derives Γ (formulaCode w Extra z b))
    (hLayout : Derives Γ (ForcingProofContext.layoutData w z b Extra Pre H layout))
    (hc : Derives Γ (ForcingExistCode.data Reln Dom w a A B C f j Child Parent cv))
    (hs : Derives Γ (ForcingExistCode.shellData w a A B C f (cv 2) (cv 3) (cv 4) (cv 5) (cv 6) (cv 7) Parent sv))
    (hQuery : Derives Γ (substituted w L S a f z b Parent ParentOut))
    (hLocal : Derives Γ (formulaCode w Local z b))
    (pGlobal : Derives Γ (implication test w z b Local (layout 3)))
    (pParent : Derives Γ (implication test w z b Local ParentOut))
    (out : Formula m)
    (use : ∀ {l} {Δ : Context l} (r : Fin m → Fin l) (Pfx Tail : Fin l), ZFContext.Evidence Δ →
      (∀ {G : Formula m}, Derives Γ G → Derives Δ (G.rename r)) →
      Derives Δ (consCode (r w) (r (P 1)) (r L) Pfx) →
      Derives Δ (substituted (r w) Pfx (r S) (r A) (r f) (r z) (r b) (r (sv 4)) Tail) →
      Derives Δ (ForcingExistTailOpening.scopeResult (r w) Pfx (r S) (r A) (r f) (r z) (r b) Tail
        (r Base) (r j) (r (P 1)) (ForcingExistTailOpening.shellCodes (r (cv 4)) (r (cv 5))
          (r (cv 6)) (r (cv 7)) (r ∘ sv))) →
      Derives Δ (implication test (r w) (r z) (r b) (r Local) Tail) →
      Derives Δ (out.rename r)) : Derives Γ out := by
  have hHead := Derives.conjL hc
  have hOuter := Derives.conjR (.conjR (.conjR (.conjR (.conjR hs))))
  have hShell : Derives Γ (ForcingRawModalBody.shell w Parent (cv 2) (cv 3) (sv 4) (sv 5) (sv 6)) :=
    .conjI (.conjL (.conjR (.conjR hOuter)))
      (.conjI (.conjL (.conjL (.conjR hOuter))) (.conjL (.conjL hOuter)))
  refine with_reflexive_outer_tail hZ Reln w z a A f b j L S Base K Extra A1 A2 A3 Cr Bd Refl Pre
    Parent ParentOut (cv 0) (cv 1) (cv 2) (cv 3) (sv 4) (sv 5) (sv 6) Local
    raw Gb H layout U F P I Ds hw hz hA ht hi hf hj hBase hUpdate hA1 hA2 hRow hPre hExtra hLayout
    (.conjL hHead) (.conjL (.conjR hHead)) (.conjL (.conjR hc)) (.conjL (.conjR (.conjR hc)))
    hShell hQuery hLocal pGlobal pParent out ?_
  intro l Δ r A' Pfx Tail hZ1 lift hA' hPfx hTail pTail
  have eA := OmegaUniversal.successor_unique A' (r A) (r a) (ZFContext.arithmetic hZ1).base.extensionality
    hA' (of_eq (successor_rename _ _ r) (lift hA))
  have hTailAtA := SyntaxMixedFormulaJudgmentSubst.subst_a (r w) Pfx (r S) A' (r f) (r z) (r b)
    (r (sv 4)) Tail (r A) eA hTail
  have hPrepared := ForcingExistTailOpening.prepare_shell hZ1 (r w) (r a) (r A) (r B) (r C) (r f)
    (r (cv 2)) (r (cv 3)) (r (cv 4)) (r (cv 5)) (r (cv 6)) (r (cv 7))
    (r Parent) Pfx (r S) (r z) (r b) Tail (r Base) (r j) (r (P 1)) (r ∘ sv)
    (of_eq (omega_rename _ _) (lift hw)) (of_eq (empty_rename _ _) (lift hz))
    (of_eq (replacement_rename _ _ _ _ _ _ _ _ r) (lift hUpdate))
    (of_eq (ForcingExistCode.shellData_rename _ _ _ _ _ _ _ _ _ _ _ _ _ sv r) (lift hs)) hTailAtA
  exact use r Pfx Tail hZ1 lift hPfx hTailAtA hPrepared pTail

private theorem falsum_at_instance_with_prefix {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    {Reln : Formula (k+2)} {q : ReflexiveRuntime m} {S : Fin m} (h : ReflexiveEvidence Γ Reln q S)
    (a A B L D N Pfx : Fin m) (d : Fin 7 → Fin m) (s o : Fin 5 → Fin m) (u v x : Fin 4 → Fin m)
    (hA : Derives Γ (successor A a))
    (hN : Derives Γ (SyntaxNodeSyntax.constructor 0 0 q.w Fin.elim0 N))
    (hd : Derives Γ (ForcingDensityCode.data Reln q.w a A B q.f q.j N D d))
    (hs : Derives Γ (ForcingDensityCode.shellData q.w a A B q.f (d 2) (d 3) (d 4) (d 5) (d 6) D s))
    (hl : Derives Γ (SyntaxCodedMixedBinderSyntax.lifted q.w L S a q.f q.z q.b (o 1) (o 2) (o 3) (o 4)))
    (hPfx : Derives Γ (consCode q.w q.p L Pfx))
    (hu : Derives Γ (ForcingRawModalBody.data q.w (o 3) (o 4) (o 1) q.f (o 2) q.b (d 2) (d 3)
      (s 2) (s 3) (o 0) u))
    (hv : Derives Γ (ForcingDensityInstantiation.pointData q.w q.z q.b (o 0) q.p q.G (u 1) (u 2) (u 3) (u 0) v))
    (hx : Derives Γ (ForcingRawModalBody.data q.w (v 2) (v 3) (v 0) q.b q.z q.b (u 1) (u 2) (u 3) (u 0) (v 1) x)) :
    Derives Γ (implication test q.w q.z q.b q.G N) := by
  have head := Derives.conjL hd
  have hZero := OmegaUniversal.empty_unique (d 0) q.z (ZFContext.arithmetic hZ).base.extensionality (.conjL head) h.zero
  have hh := SyntaxVariableImagePoint.code_subst_index true q.w (d 0) (d 1) q.z hZero (.conjL (.conjR head))
  have hm := Derives.conjL (.conjR hd)
  have ho := Derives.conjL (.conjR (.conjR hd))
  have hGuard := from_records hZ Reln q.w q.z a A (o 1) (o 2) q.f q.b L S (o 3) (o 4) q.p
    (d 1) q.G (d 2) (d 3) (s 2) (s 3) (o 0) u v x h.omega h.zero hA h.background hl hh hm ho hu hv hx
  have hin := SyntaxCodedMixedBinderTyping.input_of_lifted q.w L S a q.f q.z q.b (o 1) (o 2) (o 3) (o 4) hl
  have hAe := OmegaUniversal.successor_unique A (o 1) a (ZFContext.arithmetic hZ).base.extensionality
    hA (.conjL (.conjR hin))
  have hm' := guard_scope false Reln q.w A (o 1) q.f (d 1) (d 2) hAe hm
  have hCe := OmegaUniversal.successor_unique (v 0) (o 2) q.z (ZFContext.arithmetic hZ).base.extensionality
    (.conjL hv) (.conjR (.conjR hin))
  have hYm := SyntaxTopFormulaSyntax.intro_instantiated q.w q.z q.b (v 0) q.p (u 1) (x 1) (v 2) (v 3)
    (.conjL (.conjL (.conjR hv))) (.conjL (.conjR (.conjL hx)))
  have hTail := tail_from_reflexive_query hZ Reln q.w q.z a (o 1) (o 2) q.f q.b L q.base S (o 3) (o 4) Pfx
    (d 1) (d 2) (u 1) (x 1) (d 3) (x 2) (x 3) q.carrierIndex q.j q.carrier q.extra q.one q.two q.three
    q.bound q.boundTable q.reflCode q.pre q.raw q.gb q.guards q.layout q.instances q.bodies q.terms q.inner q.prefixed
    h.omega h.zero h.term hl hPfx hh hm' (.conjL (.conjR (.conjL hu)))
    (instance_scope q.w q.z q.b (v 0) (o 2) q.p (u 1) (x 1) hCe hYm)
    (.conjR (.conjL hGuard)) h.carrierIndex h.freeScope h.conditionIndex h.updated h.carrier
    h.one h.two h.row h.reflexive h.extra h.layout (.conjR hGuard)
  have hRebound := Derives.conjL (.conjR (.conjR (.conjR (.conjR (.conjR hd)))))
  have heq := ForcingDensityCode.rebound_nullary hZ false q.w a A B q.f q.j N (d 6) h.omega hN hRebound
  let C := SyntaxNodeSyntax.constructor 0 0 q.w.castSucc Fin.elim0 (Fin.last m)
  have const (i : Fin m) : C.instantiate i = SyntaxNodeSyntax.constructor 0 0 q.w Fin.elim0 i := by
    simp only [C, Formula.instantiate, SyntaxNodeSyntax.constructor_rename, SyntaxAtomSyntax.zero_map,
      Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have hFalse := of_eq (const (d 6)) (.eqSubst C (eq_symm heq) (of_eq (const N).symm hN))

  let Shell := ForcingDensityCode.shellData q.w.castSucc a.castSucc (Fin.last m) B.castSucc q.f.castSucc
    (d 2).castSucc (d 3).castSucc (d 4).castSucc (d 5).castSucc (d 6).castSucc D.castSucc (Fin.castSucc ∘ s)
  have shell (i : Fin m) : Shell.instantiate i =
      ForcingDensityCode.shellData q.w a i B q.f (d 2) (d 3) (d 4) (d 5) (d 6) D s := by
    simp only [Shell, Formula.instantiate, ForcingDensityCode.shellData_rename, Fin.lastCases_last,
      Fin.lastCases_castSucc, id_eq, Function.comp_def]
  have hs' := of_eq (shell (o 1)) (.eqSubst Shell hAe (of_eq (shell A).symm hs))
  have hp := falsum_from_density_records hZ q.w q.z a (o 1) B (o 2) q.f q.b L S (o 3) (o 4) Pfx q.p q.G
    (d 2) (d 3) (d 4) (d 5) (d 6) D (s 3) (o 0) s u v x h.omega h.zero hFalse h.background hs' hl hPfx hu hv hx hTail
  let F := implication test q.w.castSucc q.z.castSucc q.b.castSucc q.G.castSucc (Fin.last m)
  have inst (i : Fin m) : F.instantiate i = implication test q.w q.z q.b q.G i := by
    simp only [F, Formula.instantiate, implication_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact of_eq (inst N) (.eqSubst F heq (of_eq (inst (d 6)).symm hp))


private theorem falsum_at_instance {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    {Reln : Formula (k+2)} {q : ReflexiveRuntime m} {S : Fin m} (h : ReflexiveEvidence Γ Reln q S)
    (a A B L D N : Fin m) (d : Fin 7 → Fin m) (s o : Fin 5 → Fin m) (u v x : Fin 4 → Fin m)
    (hA : Derives Γ (successor A a))
    (hN : Derives Γ (SyntaxNodeSyntax.constructor 0 0 q.w Fin.elim0 N))
    (hd : Derives Γ (ForcingDensityCode.data Reln q.w a A B q.f q.j N D d))
    (hs : Derives Γ (ForcingDensityCode.shellData q.w a A B q.f (d 2) (d 3) (d 4) (d 5) (d 6) D s))
    (hl : Derives Γ (SyntaxCodedMixedBinderSyntax.lifted q.w L S a q.f q.z q.b (o 1) (o 2) (o 3) (o 4)))
    (hu : Derives Γ (ForcingRawModalBody.data q.w (o 3) (o 4) (o 1) q.f (o 2) q.b (d 2) (d 3)
      (s 2) (s 3) (o 0) u))
    (hv : Derives Γ (ForcingDensityInstantiation.pointData q.w q.z q.b (o 0) q.p q.G (u 1) (u 2) (u 3) (u 0) v))
    (hx : Derives Γ (ForcingRawModalBody.data q.w (v 2) (v 3) (v 0) q.b q.z q.b (u 1) (u 2) (u 3) (u 0) (v 1) x)) :
    Derives Γ (implication test q.w q.z q.b q.G N) := by
  have hi := SyntaxCodedMixedBinderTyping.input_of_lifted q.w L S a q.f q.z q.b (o 1) (o 2) (o 3) (o 4) hl
  have hL := Derives.conjL (.conjL (.conjR (.conjR (.conjL (.conjL hi)))))
  have hp := SyntaxTerms.range hZ q.w q.z q.b q.p h.omega h.term
  refine eliminate_objects hZ 1 (fun r v => (Formula.mem (v 0) (r q.w)).conj (consCode (r q.w) (r q.p) (r L) (v 0)))
    (StructuralConsCore.exists_cons hZ q.w q.p L h.omega hp hL) (implication test q.w q.z q.b q.G N) ?_
  intro l Δ r pfx hZ1 lift he
  have hN1 : Derives Δ (SyntaxNodeSyntax.constructor 0 0 (r q.w) Fin.elim0 (r N)) :=
    of_eq (by simp only [SyntaxNodeSyntax.constructor_rename, SyntaxAtomSyntax.zero_map]) (lift hN)
  exact of_eq (implication_rename test q.w q.z q.b q.G N r).symm
    (falsum_at_instance_with_prefix hZ1 (h.map r lift) (r a) (r A) (r B) (r L) (r D) (r N) (pfx 0)
      (r ∘ d) (r ∘ s) (r ∘ o) (r ∘ u) (r ∘ v) (r ∘ x) (of_eq (successor_rename _ _ _) (lift hA)) hN1
      (of_eq (ForcingDensityCode.data_rename Reln _ _ _ _ _ _ _ _ d r) (lift hd))
      (of_eq (ForcingDensityCode.shellData_rename _ _ _ _ _ _ _ _ _ _ _ s r) (lift hs))
      (of_eq (SyntaxCodedMixedBinderSyntax.lifted_rename _ _ _ _ _ _ _ _ _ _ _ r) (lift hl))
      (.conjR he) (of_eq (ForcingRawModalBody.data_rename _ _ _ _ _ _ _ _ _ _ _ _ u r) (lift hu))
      (of_eq (ForcingDensityInstantiation.pointData_rename _ _ _ _ _ _ _ _ _ _ v r) (lift hv))
      (of_eq (ForcingRawModalBody.data_rename _ _ _ _ _ _ _ _ _ _ _ _ x r) (lift hx)))

private theorem falsum_from_query_at_reflexive_term {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    {Reln : Formula (k+2)} {q : ReflexiveRuntime m} {S : Fin m} (h : ReflexiveEvidence Γ Reln q S)
    (a A B L D E N Y : Fin m)
    (hA : Derives Γ (successor A a))
    (hN : Derives Γ (SyntaxNodeSyntax.constructor 0 0 q.w Fin.elim0 N))
    (hD : Derives Γ (ForcingDensityCode.queryData Reln q.w a A B q.f q.j N q.z q.b L S D E))
    (hP : Derives Γ (implication test q.w q.z q.b q.G E))
    (hY : Derives Γ (substituted q.w L S a q.f q.z q.b N Y)) :
    Derives Γ (implication test q.w q.z q.b q.G Y) := by
  have hi := ForcingDensityInstantiation.from_query hZ Reln q.w q.z a A B q.f q.j N q.b L S D E q.p q.G
    h.omega h.zero h.term h.background hP hD
  have hp : Derives Γ (implication test q.w q.z q.b q.G N) := by
    refine ForcingDensityInstantiation.with_instance_records hZ Reln q.w q.z a A B q.f q.j N q.b L S D E q.p q.G hi
      (implication test q.w q.z q.b q.G N) ?_
    intro l Δ r d s o u v x hZ1 lift hd hs hl hu hv hx
    have hN1 : Derives Δ (SyntaxNodeSyntax.constructor 0 0 (r q.w) Fin.elim0 (r N)) :=
      of_eq (by simp only [SyntaxNodeSyntax.constructor_rename, SyntaxAtomSyntax.zero_map]) (lift hN)
    exact of_eq (implication_rename test q.w q.z q.b q.G N r).symm
      (falsum_at_instance hZ1 (h.map r lift) (r a) (r A) (r B) (r L) (r D) (r N) d s o u v x
        (of_eq (successor_rename _ _ _) (lift hA)) hN1 hd hs hl hu hv hx)
  have he := SyntaxMixedFormulaNullary.unique hZ false q.w L S a q.f q.z q.b N Y h.omega hN hY
  let F := implication test q.w.castSucc q.z.castSucc q.b.castSucc q.G.castSucc (Fin.last m)
  have inst (i : Fin m) : F.instantiate i = implication test q.w q.z q.b q.G i := by
    simp only [F, Formula.instantiate, implication_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact of_eq (inst Y) (.eqSubst F (eq_symm he) (of_eq (inst N).symm hp))

/-- The source falsum branch at the selected condition. Instantiate the actual
density universal at that condition, discharge the two original guards by
reflexivity, and eliminate its existential to obtain the exact forcing output. -/
theorem falsum_from_reflexive_query {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (Reln : Formula (k+2))
    (w z a A B f b j L S Base carrierIndex carrier Extra A1 A2 A3 Cr Bd Refl Pre D E N Y : Fin m)
    (raw : Fin 16 → Fin m) (Gb : Fin 5 → Fin m) (H layout : Fin 6 → Fin m)
    (U F P : Fin 3 → Fin m) (I : Fin 5 → Fin m) (Ds : Fin 3 → Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) (hA : Derives Γ (successor A a))
    (ht : Derives Γ (SyntaxTermSyntax.term w z b (P 1)))
    (hG : Derives Γ (formulaCode w (layout 3) z b))
    (hIndex : Derives Γ (numeral k carrierIndex))
    (hf : Derives Γ (numeral (k+2) f)) (hj : Derives Γ (numeral (k+1) j))
    (hUpdate : Derives Γ (replacement w f z b Base j (P 1) S))
    (hV : Derives Γ (field w Base carrierIndex carrier))
    (hA1 : Derives Γ (numeral 1 A1)) (hA2 : Derives Γ (numeral 2 A2))
    (hRow : Derives Γ (ForcingPreorderLeaves.data test Reln w z A1 A2 A3 f b Cr Bd Base Refl Pre raw Gb H U F P I Ds))
    (hRun : Derives Γ (substituted w Bd Base z f z b (raw 1) Refl))
    (hExtra : Derives Γ (formulaCode w Extra z b))
    (hLayout : Derives Γ (ForcingProofContext.layoutData w z b Extra Pre H layout))
    (hN : Derives Γ (SyntaxNodeSyntax.constructor 0 0 w Fin.elim0 N))
    (hD : Derives Γ (ForcingDensityCode.queryData Reln w a A B f j N z b L S D E))
    (hP : Derives Γ (implication test w z b (layout 3) E))
    (hY : Derives Γ (substituted w L S a f z b N Y)) :
    Derives Γ (implication test w z b (layout 3) Y) := by
  let q : ReflexiveRuntime m := ⟨w,z,f,b,j,Base,carrierIndex,carrier,Extra,A1,A2,A3,Cr,Bd,Refl,Pre,
    raw,Gb,H,layout,U,F,P,I,Ds⟩
  let hr : ReflexiveEvidence Γ Reln q S :=
    ⟨hw,hz,ht,hG,hIndex,hf,hj,hUpdate,hV,hA1,hA2,hRow,hRun,hExtra,hLayout⟩
  exact falsum_from_query_at_reflexive_term hZ hr a A B L D E N Y hA hN hD hP hY

theorem falsum_from_compiled_query {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (Reln : Formula (k+2))
    (w z a A B f b j L S Base carrierIndex carrier Extra A1 A2 A3 Cr Bd Refl Pre D E N Y : Fin m)
    (raw : Fin 16 → Fin m) (Gb : Fin 5 → Fin m) (H layout : Fin 6 → Fin m)
    (U F P : Fin 3 → Fin m) (I : Fin 5 → Fin m) (Ds : Fin 3 → Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) (hA : Derives Γ (successor A a))
    (ht : Derives Γ (SyntaxTermSyntax.term w z b (P 1)))
    (hG : Derives Γ (formulaCode w (layout 3) z b))
    (hIndex : Derives Γ (numeral k carrierIndex))
    (hf : Derives Γ (numeral (k+2) f)) (hj : Derives Γ (numeral (k+1) j))
    (hUpdate : Derives Γ (replacement w f z b Base j (P 1) S))
    (hV : Derives Γ (field w Base carrierIndex carrier))
    (hA1 : Derives Γ (numeral 1 A1)) (hA2 : Derives Γ (numeral 2 A2))
    (hRow : Derives Γ (ForcingPreorderLeaves.data test Reln w z A1 A2 A3 f b Cr Bd Base Refl Pre raw Gb H U F P I Ds))
    (hTarget : Derives Γ (ForcingPreorderInstances.targetData test w z f b Cr Bd Base
      (raw 0) (raw 1) (raw 2) P Pre Refl (U 0)))
    (hExtra : Derives Γ (formulaCode w Extra z b))
    (hLayout : Derives Γ (ForcingProofContext.layoutData w z b Extra Pre H layout))
    (hN : Derives Γ (SyntaxNodeSyntax.constructor 0 0 w Fin.elim0 N))
    (hD : Derives Γ (ForcingDensityCode.queryData Reln w a A B f j N z b L S D E))
    (hP : Derives Γ (implication test w z b (layout 3) E))
    (hY : Derives Γ (substituted w L S a f z b N Y)) :
    Derives Γ (implication test w z b (layout 3) Y) :=
  falsum_from_reflexive_query hZ Reln w z a A B f b j L S Base carrierIndex carrier Extra A1 A2 A3
    Cr Bd Refl Pre D E N Y raw Gb H layout U F P I Ds hw hz hA ht hG hIndex hf hj hUpdate hV hA1 hA2 hRow
    (.conjL (.conjR (.conjR (.conjR hTarget)))) hExtra hLayout hN hD hP hY

end FalsumFromCompiler
end PPAC.Migration.ForcingDensityGuards
