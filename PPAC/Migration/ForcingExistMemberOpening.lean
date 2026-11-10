import PPAC.Migration.ForcingMemberGuard
import PPAC.Migration.ForcingOpenLift
import PPAC.Migration.ForcingReflexiveImages
import PPAC.Migration.Internal.StructuralListFieldValues

/-! Pinned Force.ex inner member guard: r remains BOUND. Read the ORIGINAL
complete member compiler and actual mixed atom output. Updating free p at
slot k+1 preserves the carrier at slot k; no guard truth or desired output
code is supplied. Original field, atom and lifting producers are reused. -/
namespace PPAC.Migration.ForcingExistMemberOpening
open Internal Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)
open StructuralListFieldSyntax (field field_rename)
set_option maxRecDepth 32768
set_option maxHeartbeats 2500000
attribute [local irreducible] NaturalRecursionSyntax.matrix

def frame {m} (k : Nat) (w z a f T A c R S K H Base j p I x : Fin m) : Formula m :=
  (omega w).conj ((empty z).conj ((SyntaxMixedImageCodeSyntax.termLists w a f z T R S).conj ((SyntaxCodedMixedBinderSyntax.lifted w R S a f z T A c K H).conj ((ForcingReflexiveImages.replacement w f c T Base j p S).conj ((SyntaxNumeralSyntax.numeral k I).conj ((SyntaxNumeralSyntax.numeral (k+1) j).conj (SyntaxVariableSyntax.code true w z x)))))))

theorem frame_rename {m l} (k : Nat) (w z a f T A c R S K H Base j p I x : Fin m) (r : Fin m → Fin l) :
    (frame k w z a f T A c R S K H Base j p I x).rename r = frame k (r w) (r z) (r a) (r f) (r T) (r A) (r c) (r R) (r S) (r K) (r H) (r Base) (r j) (r p) (r I) (r x) := by
  simp only [frame, Formula.rename, omega_rename, empty_rename, SyntaxMixedImageCodeSyntax.termLists_rename,
    SyntaxCodedMixedBinderSyntax.lifted_rename, ForcingReflexiveImages.replacement_rename,
    SyntaxNumeralSyntax.numeral_rename, SyntaxVariableSyntax.code_rename]

def data {m} (w z Base I Y sym X V : Fin m) : Formula m :=
  (SyntaxAtomSyntax.zeroScalar w sym).conj ((SyntaxVariableSyntax.code true w z X).conj
    ((field w Base I V).conj (SyntaxAtomSyntax.memberCode w sym X V Y)))

theorem data_rename {m l} (w z Base I Y sym X V : Fin m) (r : Fin m → Fin l) :
    (data w z Base I Y sym X V).rename r = data (r w) (r z) (r Base) (r I) (r Y) (r sym) (r X) (r V) := by
  simp only [data, Formula.rename, SyntaxAtomSyntax.zeroScalar_rename, SyntaxVariableSyntax.code_rename, field_rename, SyntaxAtomSyntax.memberCode_rename]

def body {m} (w z Base I Y : Fin m) : Formula (m+3) :=
  data (old 3 w) (old 3 z) (old 3 Base) (old 3 I) (old 3 Y) (slot 3 0) (slot 3 1) (slot 3 2)
def result {m} (w z Base I Y : Fin m) : Formula m := existsMany 3 (body w z Base I Y)
theorem result_rename {m l} (w z Base I Y : Fin m) (r : Fin m → Fin l) :
    (result w z Base I Y).rename r = result (r w) (r z) (r Base) (r I) (r Y) := by
  simp only [result, existsMany_rename, body, data_rename, lift_old, lift_slot]

/-- Recover the SAME base carrier field from the ACTUAL lifted free image.
One lookup witness is generated and erased internally, and k != k+1 is
proved from the original numeral judgments. -/
private theorem carrier {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z a f T A c R S K H Base j p I x raw V : Fin m) (hf : Derives Γ (frame k w z a f T A c R S K H Base j p I x))
    (hraw : Derives Γ (SyntaxVariableSyntax.code false w I raw))
    (hq : Derives Γ (SyntaxCodedMixedTermSyntax.substituted w K H A f c T raw V)) :
    Derives Γ (field w Base I V) := by
  have hw := Derives.conjL (hf)
  have hI := Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (hf))))))
  have hj := Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (hf)))))))
  have hl := Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (hf))))
  have hLists := Derives.conjL (Derives.conjR (Derives.conjR (hf)))
  have hFields := Derives.impE (.conjL (SyntaxCodedMixedTermFields.at_field hZ false w K H A f c T raw V I hw
    (SyntaxCodedMixedBinderTyping.output_lists _ _ _ _ _ _ _ _ _ _ _ hl) hraw)) hq
  have hiNat := SyntaxNumerals.range hZ k w I hw hI
  let B := (Formula.mem (Fin.last m) w.castSucc).conj (field w.castSucc Base.castSucc I.castSucc (Fin.last m))
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) (StructuralListFieldValues.exists_value hZ w Base I hw hiNat)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hf1 := of_eq (frame_rename k w z a f T A c R S K H Base j p I x Fin.castSucc) (under hf B)
  have hZ1 := ZFContext.under hZ B
  have hw1 := Derives.conjL (hf1)
  have hz1 := Derives.conjL (Derives.conjR (hf1))
  have hi1 := Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (hf1))))))
  have hj1 := Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (hf1)))))))
  have hLift1 := Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (hf1))))
  have hClosed1 := Derives.conjL (Derives.conjR (Derives.conjR (hf1)))
  have hRep1 := Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (hf1)))))
  have hne := SyntaxNumerals.different hZ1 k (k+1) (Nat.ne_of_lt (Nat.lt_succ_self k)) I.castSucc j.castSucc hi1 hj1
  have hfld : Derives Δ ((Formula.mem I.castSucc f.castSucc).conj (field w.castSucc H.castSucc I.castSucc V.castSucc)) :=
    of_eq (by simp only [Formula.raise, Formula.rename, field_rename, SyntaxTermSyntax.limit, SyntaxIndexMapSyntax.selectMap, Bool.false_eq_true, ↓reduceIte]) (under hFields B)
  have hS := Derives.impE (.conjR (ForcingReflexiveImages.field_iff w.castSucc f.castSucc c.castSucc T.castSucc Base.castSucc j.castSucc p.castSucc S.castSucc I.castSucc (Fin.last m) hRep1 (.conjL hfld)))
    (.disjR (.conjI hne (.conjR hB)))
  have step : Derives Δ (ForcingOpenLift.step false I.castSucc I.castSucc) := .impI (.hyp (Or.inl rfl))
  have he := Derives.impE (.conjL (ForcingOpenLift.old_fields_from_lists hZ1 false w.castSucc z.castSucc a.castSucc f.castSucc T.castSucc A.castSucc c.castSucc R.castSucc S.castSucc K.castSucc H.castSucc I.castSucc I.castSucc (Fin.last m) V.castSucc
    hw1 hz1 hClosed1 hLift1 (.conjL hfld) hS step)) hfld
  let F := field w.castSucc.castSucc Base.castSucc.castSucc I.castSucc.castSucc (Fin.last (m+1))
  have ho : Derives Δ (field w.castSucc Base.castSucc I.castSucc V.castSucc) :=
    of_eq (by simp only [F, Formula.instantiate, field_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
      (Derives.eqSubst F (eq_symm he) (of_eq (by simp only [F, Formula.instantiate, field_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjR hB)))
  exact of_eq (field_rename w Base I V Fin.castSucc).symm ho

private theorem at_operands {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z a f T A c R S K H Base j p I x M Y sym raw X V : Fin m) (hf : Derives Γ (frame k w z a f T A c R S K H Base j p I x))
    (hd : Derives Γ (ForcingMemberGuard.data w x M I sym raw))
    (ha : Derives Γ (ForcingFormulaAtoms.atomData true w sym K H A f c T x raw Y X V)) :
    Derives Γ (result w z Base I Y) := by
  have hw := Derives.conjL (hf)
  have hl := Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (hf))))
  have hzero := Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (hf)))))))
  have hbound := Derives.impE (.conjL (SyntaxCodedMixedTermFields.at_field hZ true w K H A f c T x X z hw
    (SyntaxCodedMixedBinderTyping.output_lists _ _ _ _ _ _ _ _ _ _ _ hl) hzero)) (.conjL (.conjR ha))
  have hX := ForcingOpenLift.zero_code_from_lists hZ w z a f T A c R S K H X hw (Derives.conjL (Derives.conjR (hf))) (Derives.conjL (Derives.conjR (Derives.conjR (hf)))) hl hbound
  have hV := carrier hZ w z a f T A c R S K H Base j p I x raw V hf (.conjL (.conjR hd)) (.conjR (.conjR ha))
  apply HornBinderRules.intro_many 3 _ (SetLanguage.args3 sym X V)
  have hdata : Derives Γ (data w z Base I Y sym X V) := .conjI (.conjL hd) (.conjI hX (.conjI hV (.conjL ha)))
  exact of_eq (by simp only [body, data_rename, assign_old, assign_slot]; rfl) hdata

private theorem at_record {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z a f T A c R S K H Base j p I x M Y sym raw : Fin m) (hf : Derives Γ (frame k w z a f T A c R S K H Base j p I x))
    (hd : Derives Γ (ForcingMemberGuard.data w x M I sym raw))
    (ho : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w K H A f c T M Y)) :
    Derives Γ (result w z Base I Y) := by
  have he := ForcingFormulaAtoms.atom_output hZ true w sym K H A f c T M x raw Y (Derives.conjL (hf)) (.conjR (.conjR hd)) ho
  let B := ForcingFormulaAtoms.atomBody true w sym K H A f c T x raw Y
  let Δ := Context.add B (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 B _ he
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hf2 := of_eq (frame_rename k w z a f T A c R S K H Base j p I x (old 2)) (HornBinderRules.under_body 2 hf B)
  have hd2 := of_eq (ForcingMemberGuard.data_rename w x M I sym raw (old 2)) (HornBinderRules.under_body 2 hd B)
  have hout := at_operands (HornBinderRules.zf_body 2 hZ B) (old 2 w) (old 2 z) (old 2 a) (old 2 f) (old 2 T) (old 2 A) (old 2 c) (old 2 R) (old 2 S) (old 2 K) (old 2 H) (old 2 Base) (old 2 j) (old 2 p) (old 2 I) (old 2 x) (old 2 M) (old 2 Y) (old 2 sym) (old 2 raw) (slot 2 0) (slot 2 1) hf2 hd2 hB
  exact of_eq (result_rename w z Base I Y (old 2)).symm hout

/-- Consume the complete original member compiler and actual mixed query.
All original compiler/quotation fields, source atom and output operands are
object-bound; the returned normal code reads the same ORIGINAL base table. -/
theorem from_compiled {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (Reln : Source.Formula (k+2))
    (w z a f T A c R S K H Base j p I x M Y : Fin m) (hf : Derives Γ (frame k w z a f T A c R S K H Base j p I x))
    (hc : Derives Γ (ForcingGuardCode.compiled false Reln w A f x M))
    (ho : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w K H A f c T M Y)) :
    Derives Γ (result w z Base I Y) := by
  have he := ForcingMemberGuard.from_compiled hZ Reln w z A f x M I (Derives.conjL (hf)) (Derives.conjL (Derives.conjR (hf))) (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (hf))))))) hc
  let B := ForcingMemberGuard.body w x M I
  let Δ := Context.add B (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 B _ he
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hf2 := of_eq (frame_rename k w z a f T A c R S K H Base j p I x (old 2)) (HornBinderRules.under_body 2 hf B)
  have ho2 := of_eq (SyntaxMixedFormulaJudgmentSyntax.substituted_rename w K H A f c T M Y (old 2)) (HornBinderRules.under_body 2 ho B)
  have hout := at_record (HornBinderRules.zf_body 2 hZ B) (old 2 w) (old 2 z) (old 2 a) (old 2 f) (old 2 T) (old 2 A) (old 2 c) (old 2 R) (old 2 S) (old 2 K) (old 2 H) (old 2 Base) (old 2 j) (old 2 p) (old 2 I) (old 2 x) (old 2 M) (old 2 Y) (slot 2 0) (slot 2 1) hf2 hB ho2
  exact of_eq (result_rename w z Base I Y (old 2)).symm hout

private theorem at_normal_records {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z Base I Y Y1 : Fin m) (v u : Fin 3 → Fin m) (hw : Derives Γ (omega w)) (hi : Derives Γ (.mem I w))
    (hv : Derives Γ (data w z Base I Y (v 0) (v 1) (v 2)))
    (hu : Derives Γ (data w z Base I Y1 (u 0) (u 1) (u 2))) : Derives Γ (.equal Y Y1) := by
  have hs := SyntaxZeroScalar.unique hZ w (v 0) (u 0) hw (.conjL hv) (.conjL hu)
  have hx := SyntaxVariables.unique hZ true w z (v 1) (u 1) hw (.conjL (.conjR hv)) (.conjL (.conjR hu))
  have hV := StructuralListFieldValues.unique hZ w Base I (v 2) (u 2) hw hi (.conjL (.conjR (.conjR hv))) (.conjL (.conjR (.conjR hu)))
  have h0 := SyntaxAtomUnique.symbol_subst w (v 0) (u 0) (v 1) (v 2) Y hs (.conjR (.conjR (.conjR hv)))
  have h1 := SyntaxRenameAtomicSubst.member_x w (u 0) (v 1) (v 2) Y (u 1) hx h0
  have h2 := SyntaxRenameAtomicSubst.member_y w (u 0) (u 1) (v 2) Y (u 2) hV h1
  exact SyntaxConstructors.unique hZ 3 2 w (SyntaxAtomSyntax.three (u 0) (u 1) (u 2)) Y Y1 hw h2 (.conjR (.conjR (.conjR hu)))

private theorem normal_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z Base I Y Y1 : Fin m) (hw : Derives Γ (omega w)) (hi : Derives Γ (.mem I w))
    (hy : Derives Γ (result w z Base I Y)) (hy1 : Derives Γ (result w z Base I Y1)) : Derives Γ (.equal Y Y1) := by
  let B := body w z Base I Y
  let Δ := Context.add B (raisedContext 3 Γ)
  apply HornBinderRules.eliminate_many 3 B _ hy
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hy13 := of_eq (result_rename w z Base I Y1 (old 3)) (HornBinderRules.under_body 3 hy1 B)
  let C := body (old 3 w) (old 3 z) (old 3 Base) (old 3 I) (old 3 Y1)
  let Ξ := Context.add C (raisedContext 3 Δ)
  apply HornBinderRules.eliminate_many 3 C _ hy13
  have hC : Derives Ξ C := .hyp (Or.inl rfl)
  have hB6 := of_eq (by simp only [B, body, data_rename]; rfl) (HornBinderRules.under_body 3 hB C)
  have hw6 := of_eq (by simp only [omega_rename]; rfl) (HornBinderRules.under_body 3 (HornBinderRules.under_body 3 hw B) C)
  have hi6 := HornBinderRules.under_body 3 (HornBinderRules.under_body 3 hi B) C
  exact at_normal_records (HornBinderRules.zf_body 3 (HornBinderRules.zf_body 3 hZ B) C)
    (old 6 w) (old 6 z) (old 6 Base) (old 6 I) (old 6 Y) (old 6 Y1) (fun i => old 3 (slot 3 i)) (slot 3) hw6 hi6 hB6 hC

/-- Actual still-bound member guard outputs agree after two different
outer-condition updates of the SAME base. Neither equality nor guard truth
is a premise; both whole original compilers are actually consumed. -/
theorem compare {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (Reln : Source.Formula (k+2))
    (w z a f T A c R S K H Base j p I x M Y S1 K1 H1 q M1 Y1 : Fin m)
    (hf : Derives Γ (frame k w z a f T A c R S K H Base j p I x))
    (hg : Derives Γ (frame k w z a f T A c R S1 K1 H1 Base j q I x))
    (hc : Derives Γ (ForcingGuardCode.compiled false Reln w A f x M))
    (hd : Derives Γ (ForcingGuardCode.compiled false Reln w A f x M1))
    (hy : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w K H A f c T M Y))
    (hy1 : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w K1 H1 A f c T M1 Y1)) : Derives Γ (.equal Y Y1) := by
  have h0 := from_compiled hZ Reln w z a f T A c R S K H Base j p I x M Y hf hc hy
  have h1 := from_compiled hZ Reln w z a f T A c R S1 K1 H1 Base j q I x M1 Y1 hg hd hy1
  exact normal_unique hZ w z Base I Y Y1 (Derives.conjL (hf))
    (SyntaxNumerals.range hZ k w I (Derives.conjL hf) (.conjL (.conjR (.conjR (.conjR (.conjR (.conjR hf))))))) h0 h1


def input {k m} (Reln : Source.Formula (k+2)) (w z a f T A c R S K H Base j p I x M Y S1 K1 H1 q M1 Y1 : Fin m) : Formula m :=
  (frame k w z a f T A c R S K H Base j p I x).conj ((frame k w z a f T A c R S1 K1 H1 Base j q I x).conj ((ForcingGuardCode.compiled false Reln w A f x M).conj ((ForcingGuardCode.compiled false Reln w A f x M1).conj ((SyntaxMixedFormulaJudgmentSyntax.substituted w K H A f c T M Y).conj (SyntaxMixedFormulaJudgmentSyntax.substituted w K1 H1 A f c T M1 Y1)))))
def sentence {k m} (Reln : Source.Formula (k+2)) (w z a f T A c R S K H Base j p I x M Y S1 K1 H1 q M1 Y1 : Fin m) : Source.Sentence :=
  ((input Reln w z a f T A c R S K H Base j p I x M Y S1 K1 H1 q M1 Y1).imp (.equal Y Y1)).close

theorem kernel_certificate {k m} (Reln : Source.Formula (k+2)) (w z a f T A c R S K H Base j p I x M Y S1 K1 H1 q M1 Y1 : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (sentence Reln w z a f T A c R S K H Base j p I x M Y S1 K1 H1 q M1 Y1)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  let G := input Reln w z a f T A c R S K H Base j p I x M Y S1 K1 H1 q M1 Y1
  let Γ := Context.add G (Source.SetLanguage.ZF.at m)
  have hG : Derives Γ G := .hyp (Or.inl rfl)
  exact compare (ZFContext.add (ZFContext.source_ZF m) G) Reln w z a f T A c R S K H Base j p I x M Y S1 K1 H1 q M1 Y1
    (Derives.conjL (hG))
    (Derives.conjL (Derives.conjR (hG)))
    (Derives.conjL (Derives.conjR (Derives.conjR (hG))))
    (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (hG)))))
    (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (hG))))))
    (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (hG))))))

end PPAC.Migration.ForcingExistMemberOpening
