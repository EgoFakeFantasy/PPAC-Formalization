import PPAC.Migration.ForcingRelationGuardProof

/-! Remove BOTH actual guards in the complete original negative instance,
under ONE fixed condition background. Original compiler/head, lifted mixed
opening, native instance, and original falsum are retained. Guard proofs are
produced by existing projection/rule20/S/MP, not supplied as premises.
This does not assert uniform regularity, normalized forcing MP or final Con. -/
namespace PPAC.Migration.ForcingNegGuardProof
open Internal Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)
open FormulaCodeSyntax (formulaCode formulaCode_rename)
open InternalProofBackground (implication implication_rename)
set_option maxRecDepth 32768
attribute [local irreducible] NaturalRecursionSyntax.matrix

/-- Fixed context tuple: Rest,Dm,Do,I,All,Mref,Oref,own,head,Qorder,Uorder.
It is independent of the current operand formula or its full negative output.
G remains the SAME candidate throughout the original proof rule. -/
def fixed {k m} (Reln : Source.Formula (k+2)) (w mode z a f T A C R S K H P r s V B sym E G : Fin m) (c : Fin 11 → Fin m) : Formula m :=
  (ForcingGuardOpening.input true Reln w mode z a f T A C R S K H P r s (c 7) (c 8) (c 9) (c 10) (c 6)).conj
    (ForcingRelationGuardProof.row w z T C P V (c 0) B sym E G (c 1) (c 2) (c 3) (c 4) (c 5) (c 6))

theorem fixed_rename {k m l} (Reln : Source.Formula (k+2)) (w mode z a f T A C R S K H P r s V B sym E G : Fin m) (c : Fin 11 → Fin m) (ρ : Fin m → Fin l) :
    (fixed Reln w mode z a f T A C R S K H P r s V B sym E G c).rename ρ =
      fixed Reln (ρ w) (ρ mode) (ρ z) (ρ a) (ρ f) (ρ T) (ρ A) (ρ C) (ρ R) (ρ S) (ρ K) (ρ H) (ρ P) (ρ r) (ρ s) (ρ V) (ρ B) (ρ sym) (ρ E) (ρ G) (fun j => ρ (c j)) := by
  simp only [fixed, ForcingGuardOpening.input, Formula.rename,
    ForcingMemberGuardOpening.frame_rename, SyntaxMixedImageHead.head_rename,
    ForcingGuardCode.compiled_rename, SyntaxMixedFormulaJudgmentSyntax.substituted_rename,
    SyntaxTopFormulaSyntax.instantiated_rename, ForcingRelationGuardProof.row_rename]

private theorem compiler_head_subst {k m} {Γ : Context m} (Reln : Source.Formula (k+2)) (w A f x y Q : Fin m)
    (he : Derives Γ (.equal x y)) (hc : Derives Γ (ForcingGuardCode.compiled true Reln w A f x Q)) :
    Derives Γ (ForcingGuardCode.compiled true Reln w A f y Q) := by
  let B := ForcingGuardCode.compiled true Reln w.castSucc A.castSucc f.castSucc (Fin.last m) Q.castSucc
  have hx : B.instantiate x = ForcingGuardCode.compiled true Reln w A f x Q := by
    simp only [B, Formula.instantiate, ForcingGuardCode.compiled_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have hy : B.instantiate y = ForcingGuardCode.compiled true Reln w A f y Q := by
    simp only [B, Formula.instantiate, ForcingGuardCode.compiled_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact of_eq hy (.eqSubst B he (of_eq hx.symm hc))

/-- Align independent compiler/head/opening/native-instance witnesses with
one fixed ACTUAL original order guard. Every equality is produced by existing
original uniqueness; no output equation or guard proof is a premise. -/
private theorem order_output_unique {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (Reln : Source.Formula (k+2))
    (w mode z a f T A C R S K H P r s own head Q U O ownRef headRef QRef URef ORef : Fin m)
    (hf : Derives Γ (ForcingMemberGuardOpening.frame w mode z a f T A C R S K H P r s))
    (hh : Derives Γ (SyntaxMixedImageHead.head w A f own head))
    (hc : Derives Γ (ForcingGuardCode.compiled true Reln w A f head Q))
    (ho : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w K H A f C T Q U))
    (hi : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w r s C T z T U O))
    (href : Derives Γ (ForcingGuardOpening.input true Reln w mode z a f T A C R S K H P r s ownRef headRef QRef URef ORef)) :
    Derives Γ (.equal O ORef) := by
  have hw := Derives.conjL hf
  have hhRef := Derives.conjL (.conjR href)
  have heq := OmegaUniversal.empty_unique own ownRef (ZFContext.arithmetic hZ).base.extensionality (.conjL hh) (.conjL hhRef)
  have hx := SyntaxVariableImagePoint.code_subst_index true w own head ownRef heq (.conjL (.conjR hh))
  have hHead := SyntaxVariables.unique hZ true w ownRef head headRef hw hx (.conjL (.conjR hhRef))
  have hQ := ForcingGuardCode.unique hZ true Reln w A f headRef Q QRef hw
    (compiler_head_subst Reln w A f head headRef Q hHead hc) (.conjL (.conjR (.conjR href)))
  have hU := SyntaxMixedFormulaOutputInduction.unique hZ w K H A f C T QRef U URef hw
    (SyntaxMixedFormulaJudgmentSubst.subst_n w K H A f C T Q U QRef hQ ho) (.conjL (.conjR (.conjR (.conjR href))))
  have ht := Derives.conjL (.conjR (.conjR (.conjR (.conjR (.conjR hf)))))
  have hIRef := Derives.impE (.conjL (SyntaxTopFormulaCodes.instantiate_at_codes hZ w z T C P URef ORef r s hw ht))
    (.conjR (.conjR (.conjR (.conjR href))))
  exact SyntaxMixedFormulaOutputInduction.unique hZ w r s C T z T URef O ORef hw
    (SyntaxMixedFormulaJudgmentSubst.subst_n w r s C T z T U O URef hU hi) hIRef

private theorem implication_target_subst {m} {Γ : Context m} (test : Formula 1) (w z T G O Q : Fin m)
    (he : Derives Γ (.equal O Q)) (hp : Derives Γ (implication test w z T G O)) :
    Derives Γ (implication test w z T G Q) := by
  let B := implication test w.castSucc z.castSucc T.castSucc G.castSucc (Fin.last m)
  have hx : B.instantiate O = implication test w z T G O := by
    simp only [B, Formula.instantiate, implication_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have hy : B.instantiate Q = implication test w z T G Q := by
    simp only [B, Formula.instantiate, implication_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact of_eq hy (.eqSubst B he (of_eq hx.symm hp))

def data {m} (test : Formula 1) (w z T G Y D : Fin m) (v : Fin 2 → Fin m) : Formula m :=
  (formulaCode w Y z T).conj ((SyntaxAtomSyntax.zeroScalar w (v 0)).conj
    ((SyntaxLogicalSyntax.binaryCode 2 w D (v 0) (v 1)).conj (implication test w z T G (v 1))))

theorem data_rename {m l} (test : Formula 1) (w z T G Y D : Fin m) (v : Fin 2 → Fin m) (ρ : Fin m → Fin l) :
    (data test w z T G Y D v).rename ρ = data test (ρ w) (ρ z) (ρ T) (ρ G) (ρ Y) (ρ D) (fun j => ρ (v j)) := by
  simp only [data, Formula.rename, formulaCode_rename, SyntaxAtomSyntax.zeroScalar_rename,
    SyntaxLogicalSyntax.binaryCode_rename, implication_rename]

def body {m} (test : Formula 1) (w z T G Y D : Fin m) : Formula (m+2) :=
  data test (old 2 w) (old 2 z) (old 2 T) (old 2 G) (old 2 Y) (old 2 D) (slot 2)

def result {m} (test : Formula 1) (w z T G Y D : Fin m) : Formula m := existsMany 2 (body test w z T G Y D)

theorem result_rename {m l} (test : Formula 1) (w z T G Y D : Fin m) (ρ : Fin m → Fin l) :
    (result test w z T G Y D).rename ρ = result test (ρ w) (ρ z) (ρ T) (ρ G) (ρ Y) (ρ D) := by
  simp only [result, existsMany_rename, body, data_rename, lift_old, lift_slot]

private theorem point {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1) (Reln : Source.Formula (k+2))
    (w mode z a f T A C R S K H P r s i V own head M O q Bottom F Y D B sym E G : Fin m) (v u : Fin 6 → Fin m) (ctx : Fin 11 → Fin m)
    (hf : Derives Γ (ForcingMemberGuardOpening.frame w mode z a f T A C R S K H P r s))
    (hn : Derives Γ (SyntaxNumeralSyntax.numeral k i)) (hv : Derives Γ (StructuralListFieldSyntax.field w S i V))
    (hh : Derives Γ (SyntaxMixedImageHead.head w A f own head))
    (hc : Derives Γ (ForcingGuardCode.compiled false Reln w A f head M))
    (hco : Derives Γ (ForcingGuardCode.compiled true Reln w A f head O))
    (hfirst : Derives Γ (ForcingNegShell.chainData w K H A f C T M O q Bottom F v))
    (hlast : Derives Γ (ForcingNegShell.finalData w r s C T z Y D Bottom v u))
    (hBottom : Derives Γ (SyntaxAtomSyntax.zeroScalar w Bottom))
    (hFixed : Derives Γ (fixed Reln w mode z a f T A C R S K H P r s V B sym E G ctx))
    (hY : Derives Γ (formulaCode w Y z T)) (hp : Derives Γ (implication test w z T G Y)) :
    Derives Γ (result test w z T G Y D) := by
  have hLast := Derives.conjL hlast
  have hRow := Derives.conjR hFixed
  have hBG := Derives.conjL hRow
  have hw := Derives.conjL hf
  have hz := Derives.conjL (.conjR (.conjR hf))
  have hG := Derives.conjR (.conjR (.conjR (.conjR hBG)))
  have hm := ForcingMemberGuardOpening.from_head hZ Reln w mode z a f T A C R S K H P r s i V own head M (v 0) (u 0)
    hf hn hh hv hc (.conjL (.conjR (.conjR (.conjR hfirst)))) (.conjL (.conjR (.conjR (.conjR hLast))))
  have hpM := ForcingMemberGuardProof.at_background hZ test w z T P V B (u 0) sym E G hw hz hBG hm
  have hpRest := ForcingNegMemberProof.discharge hZ test w z T G (u 0) (u 5) Y hw hz hG hY (.conjL hLast) hpM hp
  have hOrderEq := order_output_unique hZ Reln w mode z a f T A C R S K H P r s own head O (v 1) (u 1) (ctx 7) (ctx 8) (ctx 9) (ctx 10) (ctx 6)
    hf hh hco (.conjL (.conjR (.conjR (.conjR (.conjR hfirst))))) (.conjL (.conjR (.conjR (.conjR (.conjR hLast))))) (.conjL hFixed)
  have hpOrderRef := ForcingRelationGuardProof.at_background hZ test w z T C P V (ctx 0) B sym E G (ctx 1) (ctx 2) (ctx 3) (ctx 4) (ctx 5) (ctx 6) hw hz hRow
  have hpOrder := implication_target_subst test w z T G (ctx 6) (u 1) (eq_symm hOrderEq) hpOrderRef
  have hTypes := Derives.impE (.conjL (FormulaCodeKnownLogical.binary2_iff hZ w z T (u 0) (u 5) Y hw (.conjL hLast))) hY
  have hRest := Derives.conjR (.conjR hTypes)
  have hpInner := ForcingNegMemberProof.discharge hZ test w z T G (u 1) (u 4) (u 5) hw hz hG hRest (.conjL (.conjR hLast)) hpOrder hpRest
  have hInner := SyntaxMixedFormulaLogicalSubst.binary_y 2 w D (u 3) (u 4) Bottom (.conjR (.conjR hlast))
    (SyntaxMixedFormulaLogicalSubst.binary_x 2 w (u 2) (u 3) (u 4) D (.conjL (.conjR hlast)) (.conjL (.conjR (.conjR hLast))))
  apply HornBinderRules.intro_many 2 _ (SyntaxAtomSyntax.two Bottom (u 4))
  exact of_eq (by simp only [body, data_rename, assign_old, assign_slot]; rfl)
    (.conjI hY (.conjI hBottom (.conjI hInner hpInner)))

private theorem from_normalized {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1) (Reln : Source.Formula (k+2))
    (w mode z a f T A C R S K H P r s i V own head M O q Bottom F Y D B sym E G : Fin m) (ctx : Fin 11 → Fin m)
    (hf : Derives Γ (ForcingMemberGuardOpening.frame w mode z a f T A C R S K H P r s))
    (hn : Derives Γ (SyntaxNumeralSyntax.numeral k i)) (hv : Derives Γ (StructuralListFieldSyntax.field w S i V))
    (hh : Derives Γ (SyntaxMixedImageHead.head w A f own head))
    (hc : Derives Γ (ForcingGuardCode.compiled false Reln w A f head M))
    (hco : Derives Γ (ForcingGuardCode.compiled true Reln w A f head O))
    (hnorm : Derives Γ (ForcingNegShell.normalized w K H A f C T M O q Bottom F r s z Y D))
    (hBottom : Derives Γ (SyntaxAtomSyntax.zeroScalar w Bottom))
    (hFixed : Derives Γ (fixed Reln w mode z a f T A C R S K H P r s V B sym E G ctx))
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
      (old 12 w) (old 12 mode) (old 12 z) (old 12 a) (old 12 f) (old 12 T) (old 12 A) (old 12 C) (old 12 R) (old 12 S) (old 12 K) (old 12 H) (old 12 P) (old 12 r) (old 12 s) (old 12 i) (old 12 V) (old 12 own) (old 12 head) (old 12 M) (old 12 O) (old 12 q) (old 12 Bottom) (old 12 F) (old 12 Y) (old 12 D) (old 12 B) (old 12 sym) (old 12 E) (old 12 G) (fun j => old 6 (slot 6 j)) (slot 6) (fun j => old 12 (ctx j))
      (of_eq (by simp only [ForcingMemberGuardOpening.frame_rename]; all_goals rfl) (lift12 hf))
      (of_eq (by simp only [SyntaxNumeralSyntax.numeral_rename]; all_goals rfl) (lift12 hn))
      (of_eq (by simp only [StructuralListFieldSyntax.field_rename]; all_goals rfl) (lift12 hv))
      (of_eq (by simp only [SyntaxMixedImageHead.head_rename]; all_goals rfl) (lift12 hh))
      (of_eq (by simp only [ForcingGuardCode.compiled_rename]; all_goals rfl) (lift12 hc))
      (of_eq (by simp only [ForcingGuardCode.compiled_rename]; all_goals rfl) (lift12 hco))
      (of_eq (ForcingNegShell.chainData_rename (old 6 w) (old 6 K) (old 6 H) (old 6 A) (old 6 f) (old 6 C) (old 6 T) (old 6 M) (old 6 O) (old 6 q) (old 6 Bottom) (old 6 F) (slot 6) (old 6)) (.conjL (HornBinderRules.under_body 6 hX Z))) hZf
      (of_eq (by simp only [SyntaxAtomSyntax.zeroScalar_rename]; all_goals rfl) (lift12 hBottom))
      (of_eq (by simp only [fixed_rename]; all_goals rfl) (lift12 hFixed))
      (of_eq (by simp only [formulaCode_rename]; all_goals rfl) (lift12 hY))
      (of_eq (by simp only [implication_rename]; all_goals rfl) (lift12 hp))
    exact of_eq (result_rename test (old 6 w) (old 6 z) (old 6 T) (old 6 G) (old 6 Y) (old 6 D) (old 6)).symm hpoint
  exact of_eq (result_rename test w z T G Y D (old 6)).symm hout

private theorem from_shell {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1) (Reln : Source.Formula (k+2))
    (w mode z a f T A C R S K H P r s i V own head M O q F Y D B sym E G Q : Fin m) (ctx : Fin 11 → Fin m)
    (hf : Derives Γ (ForcingMemberGuardOpening.frame w mode z a f T A C R S K H P r s))
    (hn : Derives Γ (SyntaxNumeralSyntax.numeral k i)) (hv : Derives Γ (StructuralListFieldSyntax.field w S i V))
    (hh : Derives Γ (SyntaxMixedImageHead.head w A f own head))
    (hc : Derives Γ (ForcingGuardCode.compiled false Reln w A f head M))
    (hco : Derives Γ (ForcingGuardCode.compiled true Reln w A f head O))
    (hshell : Derives Γ (ForcingNegNormalization.shellResult w a A f M O q Q K H C T F r s z Y D))
    (hFixed : Derives Γ (fixed Reln w mode z a f T A C R S K H P r s V B sym E G ctx))
    (hY : Derives Γ (formulaCode w Y z T)) (hp : Derives Γ (implication test w z T G Y)) :
    Derives Γ (result test w z T G Y D) := by
  let X := ForcingNegNormalization.shellResultBody w a A f M O q Q K H C T F r s z Y D
  let Δ := Context.add X (raisedContext 4 Γ)
  apply HornBinderRules.eliminate_many 4 X _ hshell
  have hX : Derives Δ X := .hyp (Or.inl rfl)
  have hout := from_normalized (HornBinderRules.zf_body 4 hZ X) test Reln
    (old 4 w) (old 4 mode) (old 4 z) (old 4 a) (old 4 f) (old 4 T) (old 4 A) (old 4 C) (old 4 R) (old 4 S) (old 4 K) (old 4 H) (old 4 P) (old 4 r) (old 4 s) (old 4 i) (old 4 V) (old 4 own) (old 4 head) (old 4 M) (old 4 O) (old 4 q) (slot 4 0) (old 4 F) (old 4 Y) (old 4 D) (old 4 B) (old 4 sym) (old 4 E) (old 4 G) (fun j => old 4 (ctx j))
    (of_eq (by simp only [ForcingMemberGuardOpening.frame_rename]; all_goals rfl) (HornBinderRules.under_body 4 hf X))
    (of_eq (by simp only [SyntaxNumeralSyntax.numeral_rename]; all_goals rfl) (HornBinderRules.under_body 4 hn X))
    (of_eq (by simp only [StructuralListFieldSyntax.field_rename]; all_goals rfl) (HornBinderRules.under_body 4 hv X))
    (of_eq (by simp only [SyntaxMixedImageHead.head_rename]; all_goals rfl) (HornBinderRules.under_body 4 hh X))
    (of_eq (by simp only [ForcingGuardCode.compiled_rename]; all_goals rfl) (HornBinderRules.under_body 4 hc X))
    (of_eq (by simp only [ForcingGuardCode.compiled_rename]; all_goals rfl) (HornBinderRules.under_body 4 hco X))
    (.conjR hX) (.conjL (.conjL (.conjL hX)))
    (of_eq (by simp only [fixed_rename]; all_goals rfl) (HornBinderRules.under_body 4 hFixed X))
    (of_eq (by simp only [formulaCode_rename]; all_goals rfl) (HornBinderRules.under_body 4 hY X))
    (of_eq (by simp only [implication_rename]; all_goals rfl) (HornBinderRules.under_body 4 hp X))
  exact of_eq (result_rename test w z T G Y D (old 4)).symm hout

private theorem from_compiled_data {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1) (Reln : Source.Formula (k+2))
    (w mode z a f T A C R S K H P r s i V F Y D B sym E G j n Q : Fin m) (ctx : Fin 11 → Fin m)
    (hf : Derives Γ (ForcingMemberGuardOpening.frame w mode z a f T A C R S K H P r s))
    (hn : Derives Γ (SyntaxNumeralSyntax.numeral k i)) (hv : Derives Γ (StructuralListFieldSyntax.field w S i V))
    (hcompiled : Derives Γ (ForcingNegNormalization.compiled Reln w a A f j n Q K H C T F r s z Y D))
    (hFixed : Derives Γ (fixed Reln w mode z a f T A C R S K H P r s V B sym E G ctx))
    (hY : Derives Γ (formulaCode w Y z T)) (hp : Derives Γ (implication test w z T G Y)) :
    Derives Γ (result test w z T G Y D) := by
  let X := ForcingNegNormalization.compiledBody Reln w a A f j n Q K H C T F r s z Y D
  let Δ := Context.add X (raisedContext 5 Γ)
  apply HornBinderRules.eliminate_many 5 X _ hcompiled
  have hX : Derives Δ X := .hyp (Or.inl rfl)
  have hout := from_shell (HornBinderRules.zf_body 5 hZ X) test Reln
    (old 5 w) (old 5 mode) (old 5 z) (old 5 a) (old 5 f) (old 5 T) (old 5 A) (old 5 C) (old 5 R) (old 5 S) (old 5 K) (old 5 H) (old 5 P) (old 5 r) (old 5 s) (old 5 i) (old 5 V) (slot 5 0) (slot 5 1) (slot 5 3) (slot 5 4) (slot 5 2) (old 5 F) (old 5 Y) (old 5 D) (old 5 B) (old 5 sym) (old 5 E) (old 5 G) (old 5 Q) (fun j => old 5 (ctx j))
    (of_eq (by simp only [ForcingMemberGuardOpening.frame_rename]; all_goals rfl) (HornBinderRules.under_body 5 hf X))
    (of_eq (by simp only [SyntaxNumeralSyntax.numeral_rename]; all_goals rfl) (HornBinderRules.under_body 5 hn X))
    (of_eq (by simp only [StructuralListFieldSyntax.field_rename]; all_goals rfl) (HornBinderRules.under_body 5 hv X))
    (.conjL hX) (.conjL (.conjR (.conjR hX))) (.conjL (.conjR (.conjR (.conjR hX)))) (.conjR (.conjR (.conjR (.conjR hX))))
    (of_eq (by simp only [fixed_rename]; all_goals rfl) (HornBinderRules.under_body 5 hFixed X))
    (of_eq (by simp only [formulaCode_rename]; all_goals rfl) (HornBinderRules.under_body 5 hY X))
    (of_eq (by simp only [implication_rename]; all_goals rfl) (HornBinderRules.under_body 5 hp X))
  exact of_eq (result_rename test w z T G Y D (old 5)).symm hout
def input {k m} (test : Formula 1) (Reln : Source.Formula (k+2)) (w mode z a f T A C R S K H j n P r s D Q J F Y i V B sym E G : Fin m) (ctx : Fin 11 → Fin m) : Formula m :=
  (ForcingNegNormalization.input Reln w mode z a f T A C R S K H j n P r s D Q J F Y).conj
    ((SyntaxNumeralSyntax.numeral k i).conj ((StructuralListFieldSyntax.field w S i V).conj
      ((fixed Reln w mode z a f T A C R S K H P r s V B sym E G ctx).conj (implication test w z T G Y))))

/-- The full actual original compiler and native instance are the inputs.
Both guard proofs are generated from the SAME fixed context; no shell,
guard truth, guard proof or proof of G is supplied. -/
theorem derive {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1) (Reln : Source.Formula (k+2))
    (w mode z a f T A C R S K H j n P r s D Q J F Y i V B sym E G : Fin m) (ctx : Fin 11 → Fin m)
    (h : Derives Γ (input test Reln w mode z a f T A C R S K H j n P r s D Q J F Y i V B sym E G ctx)) : Derives Γ (result test w z T G Y D) := by
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
    w mode z a f T A C R S K H P r s i V F Y D B sym E G j n Q ctx
    hf (.conjL (.conjR h)) (.conjL (.conjR (.conjR h))) hcompiled
    (.conjL (.conjR (.conjR (.conjR h)))) (SyntaxTopFormulaTyping.instantiate_target_type w z T C P F Y hi)
    (.conjR (.conjR (.conjR (.conjR h))))

def sentence {k m} (target : Bool) (Reln : Source.Formula (k+2)) (w mode z a f T A C R S K H j n P r s D Q J F Y i V B sym E G : Fin m) (ctx : Fin 11 → Fin m) : Source.Sentence :=
  ((input (OriginalAxiomCodeTest.test target) Reln w mode z a f T A C R S K H j n P r s D Q J F Y i V B sym E G ctx).imp (result (OriginalAxiomCodeTest.test target) w z T G Y D)).close

theorem kernel_certificate {k m} (target : Bool) (Reln : Source.Formula (k+2)) (w mode z a f T A C R S K H j n P r s D Q J F Y i V B sym E G : Fin m) (ctx : Fin 11 → Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (sentence target Reln w mode z a f T A C R S K H j n P r s D Q J F Y i V B sym E G ctx)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  let Premise := input (OriginalAxiomCodeTest.test target) Reln w mode z a f T A C R S K H j n P r s D Q J F Y i V B sym E G ctx
  let Γ := Context.add Premise (Source.SetLanguage.ZF.at m)
  have h : Derives Γ Premise := .hyp (Or.inl rfl)
  exact derive (ZFContext.add (ZFContext.source_ZF m) Premise) (OriginalAxiomCodeTest.test target) Reln w mode z a f T A C R S K H j n P r s D Q J F Y i V B sym E G ctx h

end PPAC.Migration.ForcingNegGuardProof
