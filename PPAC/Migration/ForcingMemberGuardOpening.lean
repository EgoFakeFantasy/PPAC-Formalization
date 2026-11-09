import PPAC.Migration.ForcingMemberGuard
import PPAC.Migration.ForcingRebindOpeningTriangle

/-! The same actual original member guard, lifted opening and native
InstantiateTop result give the literal membership of P in the ACTUAL original
P-slot opening field. No guard truth or proof is assumed or concluded. -/
namespace PPAC.Migration.ForcingMemberGuardOpening
open Internal Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)
set_option maxRecDepth 32768
attribute [local irreducible] NaturalRecursionSyntax.matrix

def frame {m} (w mode z a f T A C R S K H P r s : Fin m) : Formula m :=
  (omega w).conj ((SyntaxNumeralSyntax.numeral 2 mode).conj ((empty z).conj ((ForcingOpenLayout.environment w z a f T R S).conj ((SyntaxCodedMixedBinderSyntax.lifted w R S a f z T A C K H).conj ((SyntaxTopCodedEnvironmentSyntax.instantiateCoded w z T C P r s).conj (SyntaxTermSyntax.term w z T P))))))
theorem frame_rename {m l} (w mode z a f T A C R S K H P r s : Fin m) (ρ : Fin m → Fin l) :
    (frame w mode z a f T A C R S K H P r s).rename ρ = frame (ρ w) (ρ mode) (ρ z) (ρ a) (ρ f) (ρ T) (ρ A) (ρ C) (ρ R) (ρ S) (ρ K) (ρ H) (ρ P) (ρ r) (ρ s) := by
  simp only [frame, Formula.rename, omega_rename, SyntaxNumeralSyntax.numeral_rename, empty_rename,
    ForcingOpenLayout.environment_rename, SyntaxCodedMixedBinderSyntax.lifted_rename,
    SyntaxTopCodedEnvironmentSyntax.instantiateCoded_rename, SyntaxTermSyntax.term_rename]

private theorem zero_image {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w mode z a f T A C R S K H P r s x X Y : Fin m)
    (hf : Derives Γ (frame w mode z a f T A C R S K H P r s))
    (hx : Derives Γ (SyntaxVariableSyntax.code true w z x))
    (h0 : Derives Γ (SyntaxCodedMixedTermSyntax.substituted w K H A f C T x X))
    (h1 : Derives Γ (SyntaxCodedMixedTermSyntax.substituted w r s C T z T X Y)) : Derives Γ (.equal Y P) := by
  have hw := (Derives.conjL hf)
  have hm := (Derives.conjL (Derives.conjR hf))
  have hz := (Derives.conjL (Derives.conjR (Derives.conjR hf)))
  have he := (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR hf))))
  have hl := (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hf)))))
  have hi := (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hf))))))
  have hp := (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hf))))))
  have hLists := Derives.conjL (SyntaxCodedMixedTermTyping.input_of_substituted w K H A f C T x X h0)
  have hfield := Derives.impE (.conjL (SyntaxCodedMixedTermFields.at_field hZ true w K H A f C T x X z hw hLists hx)) h0
  have hn := ForcingOpenLift.zero_field hZ w z a f T A C R S K H hw hz he hl
  let B := (SyntaxMixedImageHead.head w.castSucc C.castSucc T.castSucc z.castSucc (Fin.last m)).conj
    (StructuralListFieldSyntax.field w.castSucc K.castSucc z.castSucc (Fin.last m))
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) hn
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hZ1 := ZFContext.under hZ B
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw B)
  have hz1 := of_eq (empty_rename z Fin.castSucc) (under hz B)
  have hfield1 := of_eq (StructuralListFieldSyntax.field_rename w K z X Fin.castSucc) (under (.conjR hfield) B)
  have hzW := OmegaStructureAlgebra.zero_member w.castSucc z.castSucc (ZFContext.arithmetic hZ1).base.extensionality hw1 hz1
  have heq := StructuralListFieldValues.unique hZ1 w.castSucc K.castSucc z.castSucc X.castSucc (Fin.last m) hw1 hzW hfield1 (.conjR hB)
  have h11 := of_eq (SyntaxCodedMixedTermSyntax.substituted_rename w r s C T z T X Y Fin.castSucc) (under h1 B)
  have hnew := SyntaxMixedFormulaAtomicSubst.term_source w.castSucc r.castSucc s.castSucc C.castSucc T.castSucc z.castSucc T.castSucc X.castSucc Y.castSucc (Fin.last m) heq h11
  have hL1 := Derives.conjL (SyntaxCodedMixedTermTyping.input_of_substituted w.castSucc r.castSucc s.castSucc C.castSucc T.castSucc z.castSucc T.castSucc (Fin.last m) Y.castSucc hnew)
  have hactual := Derives.impE (.conjL (SyntaxCodedMixedTermFields.at_field hZ1 true w.castSucc r.castSucc s.castSucc C.castSucc T.castSucc z.castSucc T.castSucc (Fin.last m) Y.castSucc z.castSucc hw1 hL1 (.conjL (.conjR (.conjL hB))))) hnew
  have hi1 := of_eq (SyntaxTopCodedEnvironmentSyntax.instantiateCoded_rename w z T C P r s Fin.castSucc) (under hi B)
  exact of_eq (by rfl) (Derives.impE (.conjL (SyntaxTopCodedEnvironmentFields.instantiate_zero hZ1 w.castSucc z.castSucc T.castSucc C.castSucc P.castSucc r.castSucc s.castSucc z.castSucc Y.castSucc hw1 hi1 hz1)) hactual)

private theorem free_image {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w mode z a f T A C R S K H P r s i V x X Y : Fin m)
    (hf : Derives Γ (frame w mode z a f T A C R S K H P r s))
    (hx : Derives Γ (SyntaxVariableSyntax.code false w i x))
    (hv : Derives Γ (StructuralListFieldSyntax.field w S i V))
    (h0 : Derives Γ (SyntaxCodedMixedTermSyntax.substituted w K H A f C T x X))
    (h1 : Derives Γ (SyntaxCodedMixedTermSyntax.substituted w r s C T z T X Y)) : Derives Γ (.equal Y V) := by
  have hw := (Derives.conjL hf)
  have hm := (Derives.conjL (Derives.conjR hf))
  have hz := (Derives.conjL (Derives.conjR (Derives.conjR hf)))
  have he := (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR hf))))
  have hl := (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hf)))))
  have hi := (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hf))))))
  have hp := (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hf))))))
  have hLists := Derives.conjL (SyntaxCodedMixedTermTyping.input_of_substituted w K H A f C T x X h0)
  have hfield := Derives.impE (.conjL (SyntaxCodedMixedTermFields.at_field hZ false w K H A f C T x X i hw hLists hx)) h0
  have ht := SyntaxCodedMixedTermTyping.source_type w r s C T z T X Y h1
  have hrun := Derives.impE (.conjR (InstantiateTopTermOperation.coded_iff hZ w mode z P T C r s X Y hw hm hz hi ht)) h1
  have hres := ForcingRebindOpeningTriangle.intro_old false w mode z P A f K H i i X Y hfield hrun
  have hs : Derives Γ (ForcingOpenLift.step false i i) := .impI (.hyp (Or.inl rfl))
  exact Derives.impE (.conjL (ForcingOpenInstantiate.old_iff hZ false w mode z P a f T A C R S K H i i V Y hw hm hz hp he hl (.conjL hfield) hv hs)) hres

private theorem point {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w mode z a f T A C R S K H P r s i V sym x y Q U Z : Fin m)
    (hf : Derives Γ (frame w mode z a f T A C R S K H P r s))
    (hx : Derives Γ (SyntaxVariableSyntax.code true w z x))
    (hy : Derives Γ (SyntaxVariableSyntax.code false w i y))
    (hv : Derives Γ (StructuralListFieldSyntax.field w S i V))
    (hc : Derives Γ (SyntaxAtomSyntax.memberCode w sym x y Q))
    (ho : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w K H A f C T Q U))
    (hi : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w r s C T z T U Z)) :
    Derives Γ (SyntaxAtomSyntax.memberCode w sym P V Z) := by
  have he0 := ForcingFormulaAtoms.atom_output hZ true w sym K H A f C T Q x y U (.conjL hf) hc ho
  let E0 := ForcingFormulaAtoms.atomBody true w sym K H A f C T x y U
  let Δ1 := Context.add E0 (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 E0 _ he0
  have hE0 : Derives Δ1 E0 := .hyp (Or.inl rfl)
  have hf2 := of_eq (frame_rename w mode z a f T A C R S K H P r s (old 2)) (HornBinderRules.under_body 2 hf E0)
  have hi2 := of_eq (SyntaxMixedFormulaJudgmentSyntax.substituted_rename w r s C T z T U Z (old 2)) (HornBinderRules.under_body 2 hi E0)
  have he1 := ForcingFormulaAtoms.atom_output (HornBinderRules.zf_body 2 hZ E0) true
    (old 2 w) (old 2 sym) (old 2 r) (old 2 s) (old 2 C) (old 2 T) (old 2 z) (old 2 T) (old 2 U)
    (slot 2 0) (slot 2 1) (old 2 Z) (.conjL hf2) (.conjL hE0) hi2
  let E1 := ForcingFormulaAtoms.atomBody true (old 2 w) (old 2 sym) (old 2 r) (old 2 s) (old 2 C) (old 2 T) (old 2 z) (old 2 T) (slot 2 0) (slot 2 1) (old 2 Z)
  let Δ2 := Context.add E1 (raisedContext 2 Δ1)
  apply HornBinderRules.eliminate_many 2 E1 _ he1
  have hE1 : Derives Δ2 E1 := .hyp (Or.inl rfl)
  have hZ4 := HornBinderRules.zf_body 2 (HornBinderRules.zf_body 2 hZ E0) E1
  have hf4 := of_eq (frame_rename (old 2 w) (old 2 mode) (old 2 z) (old 2 a) (old 2 f) (old 2 T) (old 2 A) (old 2 C) (old 2 R) (old 2 S) (old 2 K) (old 2 H) (old 2 P) (old 2 r) (old 2 s) (old 2)) (HornBinderRules.under_body 2 hf2 E1)
  have hx4 : Derives Δ2 (SyntaxVariableSyntax.code true (old 4 w) (old 4 z) (old 4 x)) :=
    of_eq (by simp only [SyntaxVariableSyntax.code_rename]; rfl) (HornBinderRules.under_body 2 (HornBinderRules.under_body 2 hx E0) E1)
  have hy4 : Derives Δ2 (SyntaxVariableSyntax.code false (old 4 w) (old 4 i) (old 4 y)) :=
    of_eq (by simp only [SyntaxVariableSyntax.code_rename]; rfl) (HornBinderRules.under_body 2 (HornBinderRules.under_body 2 hy E0) E1)
  have hv4 : Derives Δ2 (StructuralListFieldSyntax.field (old 4 w) (old 4 S) (old 4 i) (old 4 V)) :=
    of_eq (by simp only [StructuralListFieldSyntax.field_rename]; rfl) (HornBinderRules.under_body 2 (HornBinderRules.under_body 2 hv E0) E1)
  have hFirst := HornBinderRules.under_body 2 hE0 E1
  have eqX := zero_image hZ4 (old 4 w) (old 4 mode) (old 4 z) (old 4 a) (old 4 f) (old 4 T) (old 4 A) (old 4 C) (old 4 R) (old 4 S) (old 4 K) (old 4 H) (old 4 P) (old 4 r) (old 4 s) (old 4 x) (old 2 (slot 2 0)) (slot 2 0) hf4 hx4
    (of_eq (by simp only [SyntaxCodedMixedTermSyntax.substituted_rename]; rfl) (.conjL (.conjR hFirst))) (.conjL (.conjR hE1))
  have eqY := free_image hZ4 (old 4 w) (old 4 mode) (old 4 z) (old 4 a) (old 4 f) (old 4 T) (old 4 A) (old 4 C) (old 4 R) (old 4 S) (old 4 K) (old 4 H) (old 4 P) (old 4 r) (old 4 s) (old 4 i) (old 4 V) (old 4 y) (old 2 (slot 2 1)) (slot 2 1) hf4 hy4 hv4
    (of_eq (by simp only [SyntaxCodedMixedTermSyntax.substituted_rename]; rfl) (.conjR (.conjR hFirst))) (.conjR (.conjR hE1))
  have hout := SyntaxRenameAtomicSubst.member_y (old 4 w) (old 4 sym) (old 4 P) (slot 2 1) (old 4 Z) (old 4 V) eqY
    (SyntaxRenameAtomicSubst.member_x (old 4 w) (old 4 sym) (slot 2 0) (slot 2 1) (old 4 Z) (old 4 P) eqX (.conjL hE1))
  exact of_eq (by simp only [SyntaxAtomSyntax.memberCode_rename]; rfl) hout

def result {m} (w P V Z : Fin m) : Formula m := .ex
  ((SyntaxAtomSyntax.zeroScalar w.castSucc (Fin.last m)).conj
    (SyntaxAtomSyntax.memberCode w.castSucc (Fin.last m) P.castSucc V.castSucc Z.castSucc))
theorem result_rename {m l} (w P V Z : Fin m) (ρ : Fin m → Fin l) :
    (result w P V Z).rename ρ = result (ρ w) (ρ P) (ρ V) (ρ Z) := by
  simp only [result, Formula.rename, SyntaxAtomSyntax.zeroScalar_rename, SyntaxAtomSyntax.memberCode_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

/-- The same real guard compiler and both actual mixed operations yield the
literal member code P∈V. V is the ACTUAL original P-slot opening field, with
its name-prefix offset retained. No output code shape is a premise. -/
theorem from_compiled {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (Reln : Source.Formula (k+2))
    (w mode z a f T A C R S K H P r s i V x Q U Z : Fin m)
    (hf : Derives Γ (frame w mode z a f T A C R S K H P r s))
    (hn : Derives Γ (SyntaxNumeralSyntax.numeral k i))
    (hx : Derives Γ (SyntaxVariableSyntax.code true w z x))
    (hv : Derives Γ (StructuralListFieldSyntax.field w S i V))
    (hc : Derives Γ (ForcingGuardCode.compiled false Reln w A f x Q))
    (ho : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w K H A f C T Q U))
    (hi : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w r s C T z T U Z)) :
    Derives Γ (result w P V Z) := by
  have hraw := ForcingMemberGuard.from_compiled hZ Reln w z A f x Q i (.conjL hf)
    (Derives.conjL (Derives.conjR (Derives.conjR hf))) hn hc
  let E := ForcingMemberGuard.body w x Q i
  let Δ := Context.add E (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 E _ hraw
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have hf2 := of_eq (frame_rename w mode z a f T A C R S K H P r s (old 2)) (HornBinderRules.under_body 2 hf E)
  have hx2 := of_eq (SyntaxVariableSyntax.code_rename true w z x (old 2)) (HornBinderRules.under_body 2 hx E)
  have hv2 := of_eq (StructuralListFieldSyntax.field_rename w S i V (old 2)) (HornBinderRules.under_body 2 hv E)
  have ho2 := of_eq (SyntaxMixedFormulaJudgmentSyntax.substituted_rename w K H A f C T Q U (old 2)) (HornBinderRules.under_body 2 ho E)
  have hi2 := of_eq (SyntaxMixedFormulaJudgmentSyntax.substituted_rename w r s C T z T U Z (old 2)) (HornBinderRules.under_body 2 hi E)
  have hp := point (HornBinderRules.zf_body 2 hZ E) (old 2 w) (old 2 mode) (old 2 z) (old 2 a) (old 2 f) (old 2 T) (old 2 A) (old 2 C) (old 2 R) (old 2 S) (old 2 K) (old 2 H) (old 2 P) (old 2 r) (old 2 s)
    (old 2 i) (old 2 V) (slot 2 0) (old 2 x) (slot 2 1) (old 2 Q) (old 2 U) (old 2 Z)
    hf2 hx2 (.conjL (.conjR hE)) hv2 (.conjR (.conjR hE)) ho2 hi2
  have hout : Derives Δ (result (old 2 w) (old 2 P) (old 2 V) (old 2 Z)) := by
    apply Derives.exI (slot 2 0)
    exact of_eq (by simp only [Formula.instantiate, SyntaxAtomSyntax.zeroScalar_rename,
      SyntaxAtomSyntax.memberCode_rename, Formula.rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
      (.conjI (.conjL hE) hp)
  exact of_eq (result_rename w P V Z (old 2)).symm hout

/-- The compiler's OWN head index is internally identified with the root
zero. No pre-aligned bound-zero variable code has to be supplied. -/
theorem from_head {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (Reln : Source.Formula (k+2))
    (w mode z a f T A C R S K H P r s i V u x Q U Z : Fin m)
    (hf : Derives Γ (frame w mode z a f T A C R S K H P r s))
    (hn : Derives Γ (SyntaxNumeralSyntax.numeral k i))
    (hh : Derives Γ (SyntaxMixedImageHead.head w A f u x))
    (hv : Derives Γ (StructuralListFieldSyntax.field w S i V))
    (hc : Derives Γ (ForcingGuardCode.compiled false Reln w A f x Q))
    (ho : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w K H A f C T Q U))
    (hi : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w r s C T z T U Z)) :
    Derives Γ (result w P V Z) := by
  have hz := Derives.conjL (Derives.conjR (Derives.conjR hf))
  have heq := OmegaUniversal.empty_unique u z (ZFContext.arithmetic hZ).base.extensionality (.conjL hh) hz
  have hx := SyntaxVariableImagePoint.code_subst_index true w u x z heq (.conjL (.conjR hh))
  exact from_compiled hZ Reln w mode z a f T A C R S K H P r s i V x Q U Z hf hn hx hv hc ho hi

/-- Consume the native InstantiateTop judgment from the original rule20
instance, using its SAME actual coded environment. -/
theorem from_instance {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (Reln : Source.Formula (k+2))
    (w mode z a f T A C R S K H P r s i V x Q U Z : Fin m)
    (hf : Derives Γ (frame w mode z a f T A C R S K H P r s))
    (hn : Derives Γ (SyntaxNumeralSyntax.numeral k i))
    (hx : Derives Γ (SyntaxVariableSyntax.code true w z x))
    (hv : Derives Γ (StructuralListFieldSyntax.field w S i V))
    (hc : Derives Γ (ForcingGuardCode.compiled false Reln w A f x Q))
    (ho : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w K H A f C T Q U))
    (hi : Derives Γ (SyntaxTopFormulaSyntax.instantiated w z T C P U Z)) :
    Derives Γ (result w P V Z) := by
  have henv := (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hf))))))
  have hcode := Derives.impE (.conjL (SyntaxTopFormulaCodes.instantiate_at_codes hZ w z T C P U Z r s (.conjL hf) henv)) hi
  exact from_compiled hZ Reln w mode z a f T A C R S K H P r s i V x Q U Z hf hn hx hv hc ho hcode

def input {k m} (Reln : Source.Formula (k+2)) (w mode z a f T A C R S K H P r s i V x Q U Z : Fin m) : Formula m :=
  (frame w mode z a f T A C R S K H P r s).conj ((SyntaxNumeralSyntax.numeral k i).conj
    ((SyntaxVariableSyntax.code true w z x).conj ((StructuralListFieldSyntax.field w S i V).conj
      ((ForcingGuardCode.compiled false Reln w A f x Q).conj
        ((SyntaxMixedFormulaJudgmentSyntax.substituted w K H A f C T Q U).conj
          (SyntaxTopFormulaSyntax.instantiated w z T C P U Z))))))
def sentence {k m} (Reln : Source.Formula (k+2)) (w mode z a f T A C R S K H P r s i V x Q U Z : Fin m) : Source.Sentence :=
  ((input Reln w mode z a f T A C R S K H P r s i V x Q U Z).imp (result w P V Z)).close

theorem kernel_certificate {k m} (Reln : Source.Formula (k+2)) (w mode z a f T A C R S K H P r s i V x Q U Z : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (sentence Reln w mode z a f T A C R S K H P r s i V x Q U Z)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  let E := input Reln w mode z a f T A C R S K H P r s i V x Q U Z
  let Γ := Context.add E (Source.SetLanguage.ZF.at m)
  have h : Derives Γ E := .hyp (Or.inl rfl)
  exact from_instance (ZFContext.add (ZFContext.source_ZF m) E) Reln w mode z a f T A C R S K H P r s i V x Q U Z
    (Derives.conjL h) (Derives.conjL (Derives.conjR h)) (Derives.conjL (Derives.conjR (Derives.conjR h))) (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR h)))) (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR h))))) (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR h)))))) (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR h))))))

end PPAC.Migration.ForcingMemberGuardOpening
