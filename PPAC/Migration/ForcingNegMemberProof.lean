import PPAC.Migration.ForcingMemberGuardProof
import PPAC.Migration.ForcingNegNormalization
import PPAC.Migration.InternalProofImplication

/-! Consume the ACTUAL full original negative compiler and both real mixed
operations. The canonical member-guard proof removes its SAME final member
antecedent using the EXISTING original S/MP producer. All 21 original compiler,
shell and two-stage field witnesses remain internal and are eliminated.
The relation guard is retained; no relation validity, regularity, normalized
forcing MP or final Con is asserted. G is never assumed true or proved. -/
namespace PPAC.Migration.ForcingNegMemberProof
open Internal Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)
open FormulaCodeSyntax (formulaCode formulaCode_rename)
open InternalProofBackground (implication implication_rename)
open InternalProofConjunction (proved proved_rename)
set_option maxRecDepth 32768
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem discharge {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1)
    (w z b G M Rest Y : Fin m) (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hG : Derives Γ (formulaCode w G z b)) (hY : Derives Γ (formulaCode w Y z b))
    (hCtor : Derives Γ (SyntaxNodeSyntax.constructor 2 7 w (SyntaxAtomSyntax.two M Rest) Y))
    (hm : Derives Γ (implication test w z b G M))
    (hp : Derives Γ (implication test w z b G Y)) :
    Derives Γ (implication test w z b G Rest) := by
  have hTypes := Derives.impE (.conjL (FormulaCodeKnownLogical.binary2_iff hZ w z b M Rest Y hw hCtor)) hY
  have hMT := Derives.conjL (.conjR hTypes)
  have hRT := Derives.conjR (.conjR hTypes)
  let I := (SyntaxNodeSyntax.constructor 2 7 w.castSucc (SyntaxAtomSyntax.two G.castSucc M.castSucc) (Fin.last m)).conj
    (proved test w.castSucc z.castSucc b.castSucc (Fin.last m))
  let Δ1 := Context.add I (Context.image Formula.raise Γ)
  apply Derives.exE (p := I) hm
  have hI : Derives Δ1 I := .hyp (Or.inl rfl)
  let L := (SyntaxNodeSyntax.constructor 2 7 w.castSucc.castSucc (SyntaxAtomSyntax.two G.castSucc.castSucc Y.castSucc.castSucc) (Fin.last (m+1))).conj
    (proved test w.castSucc.castSucc z.castSucc.castSucc b.castSucc.castSucc (Fin.last (m+1)))
  let Δ2 := Context.add L (Context.image Formula.raise Δ1)
  apply Derives.exE (p := L) (of_eq (implication_rename test w z b G Y Fin.castSucc) (under hp I))
  have hL : Derives Δ2 L := .hyp (Or.inl rfl)
  have hZ2 := ZFContext.under (ZFContext.under hZ I) L
  have hw2 : Derives Δ2 (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (under (under hw I) L)
  have hG2 : Derives Δ2 (formulaCode w.castSucc.castSucc G.castSucc.castSucc z.castSucc.castSucc b.castSucc.castSucc) := of_eq (by simp only [Formula.raise, formulaCode_rename]) (under (under hG I) L)
  have hRT2 : Derives Δ2 (formulaCode w.castSucc.castSucc Rest.castSucc.castSucc z.castSucc.castSucc b.castSucc.castSucc) := of_eq (by simp only [Formula.raise, formulaCode_rename]) (under (under hRT I) L)
  have he := SyntaxConstructors.exists_constructor hZ2 2 7 w.castSucc.castSucc (SyntaxAtomSyntax.two G.castSucc.castSucc Rest.castSucc.castSucc) hw2
    (.conjI (.conjL (FormulaCodeProperties.guards _ _ _ _ hG2)) (.conjI (.conjL (FormulaCodeProperties.guards _ _ _ _ hRT2)) (.eqRefl _)))
  let K := (Formula.mem (Fin.last (m+2)) w.castSucc.castSucc.castSucc).conj
    (SyntaxNodeSyntax.constructor 2 7 w.castSucc.castSucc.castSucc (SyntaxAtomSyntax.two G.castSucc.castSucc.castSucc Rest.castSucc.castSucc.castSucc) (Fin.last (m+2)))
  let Δ3 := Context.add K (Context.image Formula.raise Δ2)
  apply Derives.exE (p := K) he
  have hK : Derives Δ3 K := .hyp (Or.inl rfl)
  have hI3 := under (under hI L) K
  have hL3 := under hL K
  have lift3 {X : Formula m} (hX : Derives Γ X) : Derives Δ3 X.raise.raise.raise := under (under (under hX I) L) K
  have hProof := InternalProofImplication.distribute (ZFContext.under hZ2 K) test
    w.castSucc.castSucc.castSucc z.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc
    G.castSucc.castSucc.castSucc M.castSucc.castSucc.castSucc Rest.castSucc.castSucc.castSucc
    (Fin.last m).castSucc.castSucc Y.castSucc.castSucc.castSucc (Fin.last (m+2)) (Fin.last (m+1)).castSucc
    (of_eq (by simp only [Formula.raise, omega_rename]) (lift3 hw))
    (of_eq (by simp only [Formula.raise, empty_rename]) (lift3 hz))
    (of_eq (by simp only [Formula.raise, formulaCode_rename]) (lift3 hG))
    (of_eq (by simp only [Formula.raise, formulaCode_rename]) (lift3 hMT))
    (of_eq (by simp only [Formula.raise, formulaCode_rename]) (lift3 hRT))
    (of_eq (by simp only [SyntaxNodeSyntax.constructor_rename, SyntaxAtomSyntax.two_map]) (.conjL hI3))
    (of_eq (by simp only [Formula.raise, SyntaxNodeSyntax.constructor_rename, SyntaxAtomSyntax.two_map]) (lift3 hCtor))
    (.conjR hK)
    (of_eq (by simp only [SyntaxNodeSyntax.constructor_rename, SyntaxAtomSyntax.two_map]) (.conjL hL3))
    (of_eq (by simp only [proved_rename]) (.conjR hL3))
    (of_eq (by simp only [proved_rename]) (.conjR hI3))
  have hout : Derives Δ3 (implication test w.castSucc.castSucc.castSucc z.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc G.castSucc.castSucc.castSucc Rest.castSucc.castSucc.castSucc) := by
    apply Derives.exI (Fin.last (m+2))
    exact of_eq (by simp only [Formula.instantiate, Formula.rename, SyntaxNodeSyntax.constructor_rename, SyntaxAtomSyntax.two_map, proved_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI (.conjR hK) hProof)
  exact of_eq (by simp only [Formula.raise, implication_rename]) hout

def data {m} (test : Formula 1) (w z T G Y D : Fin m) (v : Fin 5 → Fin m) : Formula m :=
  (SyntaxAtomSyntax.zeroScalar w (v 4)).conj
    ((SyntaxLogicalSyntax.binaryCode 2 w (v 0) (v 3) Y).conj
      ((SyntaxLogicalSyntax.binaryCode 2 w (v 1) (v 2) (v 3)).conj
        ((SyntaxLogicalSyntax.binaryCode 2 w D (v 4) (v 2)).conj (implication test w z T G (v 3)))))

theorem data_rename {m l} (test : Formula 1) (w z T G Y D : Fin m) (v : Fin 5 → Fin m) (ρ : Fin m → Fin l) :
    (data test w z T G Y D v).rename ρ = data test (ρ w) (ρ z) (ρ T) (ρ G) (ρ Y) (ρ D) (fun i => ρ (v i)) := by
  simp only [data, Formula.rename, SyntaxAtomSyntax.zeroScalar_rename, SyntaxLogicalSyntax.binaryCode_rename, implication_rename]

def body {m} (test : Formula 1) (w z T G Y D : Fin m) : Formula (m+5) :=
  data test (old 5 w) (old 5 z) (old 5 T) (old 5 G) (old 5 Y) (old 5 D) (slot 5)

def result {m} (test : Formula 1) (w z T G Y D : Fin m) : Formula m := existsMany 5 (body test w z T G Y D)

theorem result_rename {m l} (test : Formula 1) (w z T G Y D : Fin m) (ρ : Fin m → Fin l) :
    (result test w z T G Y D).rename ρ = result test (ρ w) (ρ z) (ρ T) (ρ G) (ρ Y) (ρ D) := by
  simp only [result, existsMany_rename, body, data_rename, lift_old, lift_slot]

private theorem point {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1) (Reln : Source.Formula (k+2))
    (w mode z a f T A C R S K H P r s i V own head M O q Bottom F Y D B sym E G : Fin m) (v u : Fin 6 → Fin m)
    (hf : Derives Γ (ForcingMemberGuardOpening.frame w mode z a f T A C R S K H P r s))
    (hn : Derives Γ (SyntaxNumeralSyntax.numeral k i)) (hv : Derives Γ (StructuralListFieldSyntax.field w S i V))
    (hh : Derives Γ (SyntaxMixedImageHead.head w A f own head))
    (hc : Derives Γ (ForcingGuardCode.compiled false Reln w A f head M))
    (hfirst : Derives Γ (ForcingNegShell.chainData w K H A f C T M O q Bottom F v))
    (hlast : Derives Γ (ForcingNegShell.finalData w r s C T z Y D Bottom v u))
    (hBottom : Derives Γ (SyntaxAtomSyntax.zeroScalar w Bottom))
    (hBG : Derives Γ (InternalProofBackground.data w z T P V B sym E G))
    (hY : Derives Γ (formulaCode w Y z T)) (hp : Derives Γ (implication test w z T G Y)) :
    Derives Γ (result test w z T G Y D) := by
  have hLast := Derives.conjL hlast
  have hm := ForcingMemberGuardOpening.from_head hZ Reln w mode z a f T A C R S K H P r s i V own head M (v 0) (u 0)
    hf hn hh hv hc (.conjL (.conjR (.conjR (.conjR hfirst)))) (.conjL (.conjR (.conjR (.conjR hLast))))
  have hmp := ForcingMemberGuardProof.at_background hZ test w z T P V B (u 0) sym E G
    (.conjL hf) (.conjL (.conjR (.conjR hf))) hBG hm
  have hG := Derives.conjR (.conjR (.conjR (.conjR hBG)))
  have hproof := discharge hZ test w z T G (u 0) (u 5) Y (.conjL hf) (.conjL (.conjR (.conjR hf))) hG hY (.conjL hLast) hmp hp
  have hInner := SyntaxMixedFormulaLogicalSubst.binary_y 2 w D (u 3) (u 4) Bottom (.conjR (.conjR hlast))
    (SyntaxMixedFormulaLogicalSubst.binary_x 2 w (u 2) (u 3) (u 4) D (.conjL (.conjR hlast)) (.conjL (.conjR (.conjR hLast))))
  let fields : Fin 5 → Fin m := Fin.cases (u 0) (Fin.cases (u 1) (Fin.cases (u 4) (Fin.cases (u 5) (fun _ => Bottom))))
  apply HornBinderRules.intro_many 5 _ fields
  exact of_eq (by simp only [body, data_rename, assign_old, assign_slot]; rfl)
    (.conjI hBottom (.conjI (.conjL hLast) (.conjI (.conjL (.conjR hLast)) (.conjI hInner hproof))))


private theorem from_normalized {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1) (Reln : Source.Formula (k+2))
    (w mode z a f T A C R S K H P r s i V own head M O q Bottom F Y D B sym E G : Fin m)
    (hf : Derives Γ (ForcingMemberGuardOpening.frame w mode z a f T A C R S K H P r s))
    (hn : Derives Γ (SyntaxNumeralSyntax.numeral k i)) (hv : Derives Γ (StructuralListFieldSyntax.field w S i V))
    (hh : Derives Γ (SyntaxMixedImageHead.head w A f own head))
    (hc : Derives Γ (ForcingGuardCode.compiled false Reln w A f head M))
    (hnorm : Derives Γ (ForcingNegShell.normalized w K H A f C T M O q Bottom F r s z Y D))
    (hBottom : Derives Γ (SyntaxAtomSyntax.zeroScalar w Bottom))
    (hBG : Derives Γ (InternalProofBackground.data w z T P V B sym E G))
    (hY : Derives Γ (formulaCode w Y z T)) (hp : Derives Γ (implication test w z T G Y)) :
    Derives Γ (result test w z T G Y D) := by
  let X := ForcingNegShell.normalizedBody w K H A f C T M O q Bottom F r s z Y D
  let Δ1 := Context.add X (raisedContext 6 Γ)
  apply HornBinderRules.eliminate_many 6 X _ hnorm
  have hX : Derives Δ1 X := .hyp (Or.inl rfl)
  let Z := ForcingNegShell.finalBody (old 6 w) (old 6 r) (old 6 s) (old 6 C) (old 6 T) (old 6 z) (old 6 Y) (old 6 D) (old 6 Bottom) (slot 6)
  let Δ2 := Context.add Z (raisedContext 6 Δ1)
  have hout : Derives Δ1 (result test (old 6 w) (old 6 z) (old 6 T) (old 6 G) (old 6 Y) (old 6 D)) := by
    apply HornBinderRules.eliminate_many 6 Z _ (.conjR hX)
    have hZf : Derives Δ2 Z := .hyp (Or.inl rfl)
    have lift12 {Q : Formula m} (hQ : Derives Γ Q) := HornBinderRules.under_body 6 (HornBinderRules.under_body 6 hQ X) Z
    have hpoint := point (HornBinderRules.zf_body 6 (HornBinderRules.zf_body 6 hZ X) Z) test Reln
      (old 12 w) (old 12 mode) (old 12 z) (old 12 a) (old 12 f) (old 12 T) (old 12 A) (old 12 C) (old 12 R) (old 12 S) (old 12 K) (old 12 H) (old 12 P) (old 12 r) (old 12 s) (old 12 i) (old 12 V) (old 12 own) (old 12 head) (old 12 M) (old 12 O) (old 12 q) (old 12 Bottom) (old 12 F) (old 12 Y) (old 12 D) (old 12 B) (old 12 sym) (old 12 E) (old 12 G) (fun j => old 6 (slot 6 j)) (slot 6)
      (of_eq (by simp only [ForcingMemberGuardOpening.frame_rename]; all_goals rfl) (lift12 hf))
      (of_eq (by simp only [SyntaxNumeralSyntax.numeral_rename]; all_goals rfl) (lift12 hn))
      (of_eq (by simp only [StructuralListFieldSyntax.field_rename]; all_goals rfl) (lift12 hv))
      (of_eq (by simp only [SyntaxMixedImageHead.head_rename]; all_goals rfl) (lift12 hh))
      (of_eq (by simp only [ForcingGuardCode.compiled_rename]; all_goals rfl) (lift12 hc))
      (of_eq (ForcingNegShell.chainData_rename (old 6 w) (old 6 K) (old 6 H) (old 6 A) (old 6 f) (old 6 C) (old 6 T) (old 6 M) (old 6 O) (old 6 q) (old 6 Bottom) (old 6 F) (slot 6) (old 6)) (.conjL (HornBinderRules.under_body 6 hX Z))) hZf
      (of_eq (by simp only [SyntaxAtomSyntax.zeroScalar_rename]; all_goals rfl) (lift12 hBottom))
      (of_eq (by simp only [InternalProofBackground.data_rename]; all_goals rfl) (lift12 hBG))
      (of_eq (by simp only [formulaCode_rename]; all_goals rfl) (lift12 hY))
      (of_eq (by simp only [implication_rename]; all_goals rfl) (lift12 hp))
    exact of_eq (result_rename test (old 6 w) (old 6 z) (old 6 T) (old 6 G) (old 6 Y) (old 6 D) (old 6)).symm hpoint
  exact of_eq (result_rename test w z T G Y D (old 6)).symm hout

private theorem from_shell {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1) (Reln : Source.Formula (k+2))
    (w mode z a f T A C R S K H P r s i V own head M O q F Y D B sym E G Q : Fin m)
    (hf : Derives Γ (ForcingMemberGuardOpening.frame w mode z a f T A C R S K H P r s))
    (hn : Derives Γ (SyntaxNumeralSyntax.numeral k i)) (hv : Derives Γ (StructuralListFieldSyntax.field w S i V))
    (hh : Derives Γ (SyntaxMixedImageHead.head w A f own head))
    (hc : Derives Γ (ForcingGuardCode.compiled false Reln w A f head M))
    (hshell : Derives Γ (ForcingNegNormalization.shellResult w a A f M O q Q K H C T F r s z Y D))
    (hBG : Derives Γ (InternalProofBackground.data w z T P V B sym E G))
    (hY : Derives Γ (formulaCode w Y z T)) (hp : Derives Γ (implication test w z T G Y)) :
    Derives Γ (result test w z T G Y D) := by
  let X := ForcingNegNormalization.shellResultBody w a A f M O q Q K H C T F r s z Y D
  let Δ := Context.add X (raisedContext 4 Γ)
  apply HornBinderRules.eliminate_many 4 X _ hshell
  have hX : Derives Δ X := .hyp (Or.inl rfl)
  have hout := from_normalized (HornBinderRules.zf_body 4 hZ X) test Reln
    (old 4 w) (old 4 mode) (old 4 z) (old 4 a) (old 4 f) (old 4 T) (old 4 A) (old 4 C) (old 4 R) (old 4 S) (old 4 K) (old 4 H) (old 4 P) (old 4 r) (old 4 s) (old 4 i) (old 4 V) (old 4 own) (old 4 head) (old 4 M) (old 4 O) (old 4 q) (slot 4 0) (old 4 F) (old 4 Y) (old 4 D) (old 4 B) (old 4 sym) (old 4 E) (old 4 G)
    (of_eq (by simp only [ForcingMemberGuardOpening.frame_rename]; all_goals rfl) (HornBinderRules.under_body 4 hf X))
    (of_eq (by simp only [SyntaxNumeralSyntax.numeral_rename]; all_goals rfl) (HornBinderRules.under_body 4 hn X))
    (of_eq (by simp only [StructuralListFieldSyntax.field_rename]; all_goals rfl) (HornBinderRules.under_body 4 hv X))
    (of_eq (by simp only [SyntaxMixedImageHead.head_rename]; all_goals rfl) (HornBinderRules.under_body 4 hh X))
    (of_eq (by simp only [ForcingGuardCode.compiled_rename]; all_goals rfl) (HornBinderRules.under_body 4 hc X))
    (.conjR hX) (.conjL (.conjL (.conjL hX)))
    (of_eq (by simp only [InternalProofBackground.data_rename]; all_goals rfl) (HornBinderRules.under_body 4 hBG X))
    (of_eq (by simp only [formulaCode_rename]; all_goals rfl) (HornBinderRules.under_body 4 hY X))
    (of_eq (by simp only [implication_rename]; all_goals rfl) (HornBinderRules.under_body 4 hp X))
  exact of_eq (result_rename test w z T G Y D (old 4)).symm hout

private theorem from_compiled_data {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1) (Reln : Source.Formula (k+2))
    (w mode z a f T A C R S K H P r s i V F Y D B sym E G j n Q : Fin m)
    (hf : Derives Γ (ForcingMemberGuardOpening.frame w mode z a f T A C R S K H P r s))
    (hn : Derives Γ (SyntaxNumeralSyntax.numeral k i)) (hv : Derives Γ (StructuralListFieldSyntax.field w S i V))
    (hcompiled : Derives Γ (ForcingNegNormalization.compiled Reln w a A f j n Q K H C T F r s z Y D))
    (hBG : Derives Γ (InternalProofBackground.data w z T P V B sym E G))
    (hY : Derives Γ (formulaCode w Y z T)) (hp : Derives Γ (implication test w z T G Y)) :
    Derives Γ (result test w z T G Y D) := by
  let X := ForcingNegNormalization.compiledBody Reln w a A f j n Q K H C T F r s z Y D
  let Δ := Context.add X (raisedContext 5 Γ)
  apply HornBinderRules.eliminate_many 5 X _ hcompiled
  have hX : Derives Δ X := .hyp (Or.inl rfl)
  have hout := from_shell (HornBinderRules.zf_body 5 hZ X) test Reln
    (old 5 w) (old 5 mode) (old 5 z) (old 5 a) (old 5 f) (old 5 T) (old 5 A) (old 5 C) (old 5 R) (old 5 S) (old 5 K) (old 5 H) (old 5 P) (old 5 r) (old 5 s) (old 5 i) (old 5 V) (slot 5 0) (slot 5 1) (slot 5 3) (slot 5 4) (slot 5 2) (old 5 F) (old 5 Y) (old 5 D) (old 5 B) (old 5 sym) (old 5 E) (old 5 G) (old 5 Q)
    (of_eq (by simp only [ForcingMemberGuardOpening.frame_rename]; all_goals rfl) (HornBinderRules.under_body 5 hf X))
    (of_eq (by simp only [SyntaxNumeralSyntax.numeral_rename]; all_goals rfl) (HornBinderRules.under_body 5 hn X))
    (of_eq (by simp only [StructuralListFieldSyntax.field_rename]; all_goals rfl) (HornBinderRules.under_body 5 hv X))
    (.conjL hX) (.conjL (.conjR (.conjR hX))) (.conjR (.conjR (.conjR (.conjR hX))))
    (of_eq (by simp only [InternalProofBackground.data_rename]; all_goals rfl) (HornBinderRules.under_body 5 hBG X))
    (of_eq (by simp only [formulaCode_rename]; all_goals rfl) (HornBinderRules.under_body 5 hY X))
    (of_eq (by simp only [implication_rename]; all_goals rfl) (HornBinderRules.under_body 5 hp X))
  exact of_eq (result_rename test w z T G Y D (old 5)).symm hout

def input {k m} (test : Formula 1) (Reln : Source.Formula (k+2)) (w mode z a f T A C R S K H j n P r s D Q J F Y i V B sym E G : Fin m) : Formula m :=
  (ForcingNegNormalization.input Reln w mode z a f T A C R S K H j n P r s D Q J F Y).conj
    ((SyntaxNumeralSyntax.numeral k i).conj ((StructuralListFieldSyntax.field w S i V).conj
      ((InternalProofBackground.data w z T P V B sym E G).conj (implication test w z T G Y))))

/-- The full actual original compiler and native instance are the inputs.
No shell, member proof, guard truth or proof of G is supplied. -/
theorem derive {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1) (Reln : Source.Formula (k+2))
    (w mode z a f T A C R S K H j n P r s D Q J F Y i V B sym E G : Fin m)
    (h : Derives Γ (input test Reln w mode z a f T A C R S K H j n P r s D Q J F Y i V B sym E G)) : Derives Γ (result test w z T G Y D) := by
  have hN := Derives.conjL h
  have hop := Derives.conjL hN
  have hw := Derives.conjL hop
  have hm := Derives.conjL (.conjR hop)
  have hz := Derives.conjL (.conjR (.conjR hop))
  have he := Derives.conjL (.conjR (.conjR (.conjR hop)))
  have hl := Derives.conjL (.conjR (.conjR (.conjR (.conjR hop))))
  have hj := Derives.conjL (.conjR (.conjR (.conjR (.conjR (.conjR hop)))))
  have hP := Derives.conjL (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR hop))))))
  have ht := Derives.conjL (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR hop)))))))
  have hPtype := SyntaxMixedImageCodeFields.field_type w f z T S j P (.conjR (ForcingOpenLayout.environment_types w z a f T R S he)) hj hP
  have hf : Derives Γ (ForcingMemberGuardOpening.frame w mode z a f T A C R S K H P r s) :=
    .conjI hw (.conjI hm (.conjI hz (.conjI he (.conjI hl (.conjI ht hPtype)))))
  have hi := Derives.conjR (.conjR (.conjR (.conjR hN)))
  have hcompiled := ForcingNegNormalization.from_instance hZ Reln w mode z a f T A C R S K H j n P r s D Q J F Y
    hop (.conjL (.conjR hN)) (.conjL (.conjR (.conjR hN))) (.conjL (.conjR (.conjR (.conjR hN)))) hi
  exact from_compiled_data hZ test Reln
    w mode z a f T A C R S K H P r s i V F Y D B sym E G j n Q
    hf (.conjL (.conjR h)) (.conjL (.conjR (.conjR h))) hcompiled
    (.conjL (.conjR (.conjR (.conjR h)))) (SyntaxTopFormulaTyping.instantiate_target_type w z T C P F Y hi)
    (.conjR (.conjR (.conjR (.conjR h))))

def sentence {k m} (target : Bool) (Reln : Source.Formula (k+2)) (w mode z a f T A C R S K H j n P r s D Q J F Y i V B sym E G : Fin m) : Source.Sentence :=
  ((input (OriginalAxiomCodeTest.test target) Reln w mode z a f T A C R S K H j n P r s D Q J F Y i V B sym E G).imp (result (OriginalAxiomCodeTest.test target) w z T G Y D)).close

theorem kernel_certificate {k m} (target : Bool) (Reln : Source.Formula (k+2)) (w mode z a f T A C R S K H j n P r s D Q J F Y i V B sym E G : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (sentence target Reln w mode z a f T A C R S K H j n P r s D Q J F Y i V B sym E G)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  let Premise := input (OriginalAxiomCodeTest.test target) Reln w mode z a f T A C R S K H j n P r s D Q J F Y i V B sym E G
  let Γ := Context.add Premise (Source.SetLanguage.ZF.at m)
  have h : Derives Γ Premise := .hyp (Or.inl rfl)
  exact derive (ZFContext.add (ZFContext.source_ZF m) Premise) (OriginalAxiomCodeTest.test target) Reln w mode z a f T A C R S K H j n P r s D Q J F Y i V B sym E G h

end PPAC.Migration.ForcingNegMemberProof
