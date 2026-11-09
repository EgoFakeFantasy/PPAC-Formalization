import PPAC.Migration.InternalProofBackground
import PPAC.Migration.ForcingGuardOpening

/-! Actual member guard internal proofs for the pinned forcing negation shell.
The SAME original compiler/head, lifted opening, native InstantiateTop and
actual P-slot field are consumed. The canonical common background depends
only on B/P/V/scopes, never on the current source formula or guard candidate.
Original rule13 constructs G→M; neither G nor M is assumed proved or true.
This is the member guard step, not relation guard, forcing MP or final Con. -/
namespace PPAC.Migration.ForcingMemberGuardProof
open Internal Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)
open FormulaCodeSyntax (formulaCode formulaCode_rename)
set_option maxRecDepth 32768
attribute [local irreducible] NaturalRecursionSyntax.matrix

def data {m} (test : Formula 1) (w z b P V B M sym E G : Fin m) : Formula m :=
  (InternalProofBackground.data w z b P V B sym E G).conj
    (InternalProofBackground.implication test w z b G M)

theorem data_rename {m l} (test : Formula 1) (w z b P V B M sym E G : Fin m) (ρ : Fin m → Fin l) :
    (data test w z b P V B M sym E G).rename ρ = data test (ρ w) (ρ z) (ρ b) (ρ P) (ρ V) (ρ B) (ρ M) (ρ sym) (ρ E) (ρ G) := by
  simp only [data, Formula.rename, InternalProofBackground.data_rename, InternalProofBackground.implication_rename]

def body {m} (test : Formula 1) (w z b P V B M : Fin m) : Formula (m+3) :=
  data test (old 3 w) (old 3 z) (old 3 b) (old 3 P) (old 3 V) (old 3 B) (old 3 M) (slot 3 0) (slot 3 1) (slot 3 2)

def result {m} (test : Formula 1) (w z b P V B M : Fin m) : Formula m :=
  existsMany 3 (body test w z b P V B M)

theorem result_rename {m l} (test : Formula 1) (w z b P V B M : Fin m) (ρ : Fin m → Fin l) :
    (result test w z b P V B M).rename ρ = result test (ρ w) (ρ z) (ρ b) (ρ P) (ρ V) (ρ B) (ρ M) := by
  simp only [result, existsMany_rename, body, data_rename, lift_old, lift_slot]

/-- For ANY candidate of the SAME canonical background, consume the actual
member code and produce its original internal proof. No proof of G is input. -/
theorem at_background {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1)
    (w z b P V B M sym E G : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hd : Derives Γ (InternalProofBackground.data w z b P V B sym E G))
    (hm : Derives Γ (ForcingMemberGuardOpening.result w P V M)) :
    Derives Γ (InternalProofBackground.implication test w z b G M) := by
  let Q := (SyntaxAtomSyntax.zeroScalar w.castSucc (Fin.last m)).conj
    (SyntaxAtomSyntax.memberCode w.castSucc (Fin.last m) P.castSucc V.castSucc M.castSucc)
  let Δ := Context.add Q (Context.image Formula.raise Γ)
  apply Derives.exE (p := Q) hm
  have hQ : Derives Δ Q := .hyp (Or.inl rfl)
  have hout := InternalProofBackground.project_member (ZFContext.under hZ Q) test
    w.castSucc z.castSucc b.castSucc P.castSucc V.castSucc B.castSucc sym.castSucc E.castSucc G.castSucc (Fin.last m) M.castSucc
    (of_eq (omega_rename w Fin.castSucc) (under hw Q))
    (of_eq (empty_rename z Fin.castSucc) (under hz Q))
    (of_eq (InternalProofBackground.data_rename w z b P V B sym E G Fin.castSucc) (under hd Q)) (.conjL hQ) (.conjR hQ)
  exact of_eq (InternalProofBackground.implication_rename test w z b G M Fin.castSucc).symm hout

private theorem at_member {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1)
    (w z b P V B M symM : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hB : Derives Γ (formulaCode w B z b)) (hMT : Derives Γ (formulaCode w M z b))
    (hSym : Derives Γ (SyntaxAtomSyntax.zeroScalar w symM))
    (hM : Derives Γ (SyntaxAtomSyntax.memberCode w symM P V M)) :
    Derives Γ (result test w z b P V B M) := by
  have hTypes := Derives.impE (.conjL (FormulaCodeKnownAtomic.member_iff hZ w z b symM P V M hw hM)) hMT
  have hBG := InternalProofBackground.background_exists hZ w z b P V B hw hB (.conjL (.conjR hTypes)) (.conjR (.conjR hTypes))
  let Q := InternalProofBackground.body w z b P V B
  let Δ := Context.add Q (raisedContext 3 Γ)
  apply HornBinderRules.eliminate_many 3 Q _ hBG
  have hQ : Derives Δ Q := .hyp (Or.inl rfl)
  have hp := InternalProofBackground.project_member (HornBinderRules.zf_body 3 hZ Q) test
    (old 3 w) (old 3 z) (old 3 b) (old 3 P) (old 3 V) (old 3 B) (slot 3 0) (slot 3 1) (slot 3 2) (old 3 symM) (old 3 M)
    (of_eq (omega_rename w (old 3)) (HornBinderRules.under_body 3 hw Q))
    (of_eq (empty_rename z (old 3)) (HornBinderRules.under_body 3 hz Q)) hQ
    (of_eq (SyntaxAtomSyntax.zeroScalar_rename w symM (old 3)) (HornBinderRules.under_body 3 hSym Q))
    (of_eq (SyntaxAtomSyntax.memberCode_rename w symM P V M (old 3)) (HornBinderRules.under_body 3 hM Q))
  have hout : Derives Δ (result test (old 3 w) (old 3 z) (old 3 b) (old 3 P) (old 3 V) (old 3 B) (old 3 M)) := by
    apply HornBinderRules.intro_many 3 _ (slot 3)
    exact of_eq (by simp only [body, data_rename, assign_old, assign_slot]; rfl) (.conjI hQ hp)
  exact of_eq (result_rename test w z b P V B M (old 3)).symm hout

/-- Build the common background using term typing recovered from the ACTUAL
member output; do not assume an opening field type or a guard proof. -/
theorem from_member {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1)
    (w z b P V B M : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hB : Derives Γ (formulaCode w B z b)) (hMT : Derives Γ (formulaCode w M z b))
    (hm : Derives Γ (ForcingMemberGuardOpening.result w P V M)) :
    Derives Γ (result test w z b P V B M) := by
  let Q := (SyntaxAtomSyntax.zeroScalar w.castSucc (Fin.last m)).conj
    (SyntaxAtomSyntax.memberCode w.castSucc (Fin.last m) P.castSucc V.castSucc M.castSucc)
  let Δ := Context.add Q (Context.image Formula.raise Γ)
  apply Derives.exE (p := Q) hm
  have hQ : Derives Δ Q := .hyp (Or.inl rfl)
  have hout := at_member (ZFContext.under hZ Q) test w.castSucc z.castSucc b.castSucc P.castSucc V.castSucc B.castSucc M.castSucc (Fin.last m)
    (of_eq (omega_rename w Fin.castSucc) (under hw Q)) (of_eq (empty_rename z Fin.castSucc) (under hz Q))
    (of_eq (formulaCode_rename w B z b Fin.castSucc) (under hB Q))
    (of_eq (formulaCode_rename w M z b Fin.castSucc) (under hMT Q)) (.conjL hQ) (.conjR hQ)
  exact of_eq (result_rename test w z b P V B M Fin.castSucc).symm hout

/-- All source judgments are the ACTUAL original guard operations. -/
def input {k m} (Reln : Source.Formula (k+2)) (w mode z a f T A C R S K H P r s i V u head q U M B : Fin m) : Formula m :=
  (ForcingGuardOpening.input false Reln w mode z a f T A C R S K H P r s u head q U M).conj
    ((SyntaxNumeralSyntax.numeral k i).conj ((StructuralListFieldSyntax.field w S i V).conj (formulaCode w B z T)))

private theorem member_from_input {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (Reln : Source.Formula (k+2))
    (w mode z a f T A C R S K H P r s i V u head q U M B : Fin m)
    (h : Derives Γ (input Reln w mode z a f T A C R S K H P r s i V u head q U M B)) :
    Derives Γ (ForcingMemberGuardOpening.result w P V M) := by
  have ho := Derives.conjL h
  have hf := Derives.conjL ho
  have hh := Derives.conjL (.conjR ho)
  have heq := OmegaUniversal.empty_unique u z (ZFContext.arithmetic hZ).base.extensionality (.conjL hh) (.conjL (.conjR (.conjR hf)))
  have hx := SyntaxVariableImagePoint.code_subst_index true w u head z heq (.conjL (.conjR hh))
  exact ForcingMemberGuardOpening.from_instance hZ Reln w mode z a f T A C R S K H P r s i V head q U M
    hf (.conjL (.conjR h)) hx (.conjL (.conjR (.conjR h)))
    (.conjL (.conjR (.conjR ho))) (.conjL (.conjR (.conjR (.conjR ho)))) (.conjR (.conjR (.conjR (.conjR ho))))

/-- Consume the actual original source instance for ANY fixed candidate G of
our canonical background. This is not a formula-dependent choice of G. -/
theorem from_instance_at_background {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1) (Reln : Source.Formula (k+2))
    (w mode z a f T A C R S K H P r s i V u head q U M B sym E G : Fin m)
    (h : Derives Γ (input Reln w mode z a f T A C R S K H P r s i V u head q U M B))
    (hd : Derives Γ (InternalProofBackground.data w z T P V B sym E G)) :
    Derives Γ (InternalProofBackground.implication test w z T G M) := by
  have hf := Derives.conjL (.conjL h)
  exact at_background hZ test w z T P V B M sym E G (.conjL hf) (.conjL (.conjR (.conjR hf))) hd
    (member_from_input hZ Reln w mode z a f T A C R S K H P r s i V u head q U M B h)

theorem from_instance {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1) (Reln : Source.Formula (k+2))
    (w mode z a f T A C R S K H P r s i V u head q U M B : Fin m)
    (h : Derives Γ (input Reln w mode z a f T A C R S K H P r s i V u head q U M B)) :
    Derives Γ (result test w z T P V B M) := by
  have ho := Derives.conjL h
  have hf := Derives.conjL ho
  have hi := Derives.conjR (.conjR (.conjR (.conjR ho)))
  exact from_member hZ test w z T P V B M (.conjL hf) (.conjL (.conjR (.conjR hf)))
    (.conjR (.conjR (.conjR h))) (SyntaxTopFormulaTyping.instantiate_target_type w z T C P U M hi)
    (member_from_input hZ Reln w mode z a f T A C R S K H P r s i V u head q U M B h)

def sentence {k m} (target : Bool) (Reln : Source.Formula (k+2)) (w mode z a f T A C R S K H P r s i V u head q U M B : Fin m) : Source.Sentence :=
  ((input Reln w mode z a f T A C R S K H P r s i V u head q U M B).imp (result (OriginalAxiomCodeTest.test target) w z T P V B M)).close

theorem kernel_certificate {k m} (target : Bool) (Reln : Source.Formula (k+2)) (w mode z a f T A C R S K H P r s i V u head q U M B : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (sentence target Reln w mode z a f T A C R S K H P r s i V u head q U M B)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  let Premise := input Reln w mode z a f T A C R S K H P r s i V u head q U M B
  let Γ := Context.add Premise (Source.SetLanguage.ZF.at m)
  have h : Derives Γ Premise := .hyp (Or.inl rfl)
  exact from_instance (ZFContext.add (ZFContext.source_ZF m) Premise) (OriginalAxiomCodeTest.test target) Reln w mode z a f T A C R S K H P r s i V u head q U M B h

def sentence_at_background {k m} (target : Bool) (Reln : Source.Formula (k+2)) (w mode z a f T A C R S K H P r s i V u head q U M B sym E G : Fin m) : Source.Sentence :=
  (((input Reln w mode z a f T A C R S K H P r s i V u head q U M B).conj (InternalProofBackground.data w z T P V B sym E G)).imp (InternalProofBackground.implication (OriginalAxiomCodeTest.test target) w z T G M)).close

theorem kernel_certificate_at_background {k m} (target : Bool) (Reln : Source.Formula (k+2)) (w mode z a f T A C R S K H P r s i V u head q U M B sym E G : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (sentence_at_background target Reln w mode z a f T A C R S K H P r s i V u head q U M B sym E G)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  let Premise := (input Reln w mode z a f T A C R S K H P r s i V u head q U M B).conj (InternalProofBackground.data w z T P V B sym E G)
  let Γ := Context.add Premise (Source.SetLanguage.ZF.at m)
  have h : Derives Γ Premise := .hyp (Or.inl rfl)
  exact from_instance_at_background (ZFContext.add (ZFContext.source_ZF m) Premise) (OriginalAxiomCodeTest.test target) Reln w mode z a f T A C R S K H P r s i V u head q U M B sym E G (.conjL h) (.conjR h)

end PPAC.Migration.ForcingMemberGuardProof
