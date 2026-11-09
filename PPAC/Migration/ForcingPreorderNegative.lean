import PPAC.Migration.ForcingPreorderGuardTables
import PPAC.Migration.InternalProofCurry

/-! Consume the original COMPLETE negative compiler/opening/native instance,
identify both guards with the SAME original preorder leaves, and use the
existing original internal proof rules to discharge them. No guard truth,
desired guard equality or replacement proof kernel is supplied. -/
namespace PPAC.Migration.ForcingPreorderNegative
open Internal Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)
open SyntaxMixedFormulaJudgmentSyntax (substituted substituted_rename)
set_option maxRecDepth 32768
set_option maxHeartbeats 2500000
attribute [local irreducible] NaturalRecursionSyntax.matrix

def basis {k m} (test : Formula 1) (R : Source.Formula (k+2))
    (w z A1 A2 A3 f T C B S Refl Pre I j Sg mode a A Rb K Hm r s n L Target Y Extra Ctx : Fin m) (v : Fin 16 → Fin m) (Gb : Fin 5 → Fin m) (H : Fin 6 → Fin m) (U : Fin 3 → Fin m) (F : Fin 3 → Fin m) (P : Fin 3 → Fin m) (N : Fin 5 → Fin m) (D : Fin 3 → Fin m) : Formula m :=
  (SyntaxNumeralSyntax.numeral 1 A1).conj ((SyntaxNumeralSyntax.numeral 2 A2).conj ((SyntaxNumeralSyntax.numeral 3 A3).conj ((SyntaxNumeralSyntax.numeral (k+2) f).conj ((SyntaxNumeralSyntax.numeral (k+1) j).conj ((SyntaxNumeralSyntax.numeral k I).conj ((ForcingPreorderLeaves.data test R w z A1 A2 A3 f T C B S Refl Pre v Gb H U F P N D).conj ((ForcingReflexiveImages.replacement w f z T S j (P 2) Sg).conj ((ForcingNegCondition.operations w mode z a f T A C Rb Sg K Hm j n (P 0) r s L Target).conj ((FormulaCodeSyntax.formulaCode w Ctx z T).conj ((SyntaxLogicalSyntax.binaryCode 0 w Extra (Gb 0) Ctx).conj ((FormulaCodeSyntax.formulaCode w Y z T).conj ((InternalProofBackground.implication test w z T Ctx Y)))))))))))))

theorem basis_rename {k m l} (test : Formula 1) (R : Source.Formula (k+2))
    (w z A1 A2 A3 f T C B S Refl Pre I j Sg mode a A Rb K Hm r s n L Target Y Extra Ctx : Fin m) (v : Fin 16 → Fin m) (Gb : Fin 5 → Fin m) (H : Fin 6 → Fin m) (U : Fin 3 → Fin m) (F : Fin 3 → Fin m) (P : Fin 3 → Fin m) (N : Fin 5 → Fin m) (D : Fin 3 → Fin m) (ρ : Fin m → Fin l) :
    (basis test R w z A1 A2 A3 f T C B S Refl Pre I j Sg mode a A Rb K Hm r s n L Target Y Extra Ctx v Gb H U F P N D).rename ρ = basis test R (ρ w) (ρ z) (ρ A1) (ρ A2) (ρ A3) (ρ f) (ρ T) (ρ C) (ρ B) (ρ S) (ρ Refl) (ρ Pre) (ρ I) (ρ j) (ρ Sg) (ρ mode) (ρ a) (ρ A) (ρ Rb) (ρ K) (ρ Hm) (ρ r) (ρ s) (ρ n) (ρ L) (ρ Target) (ρ Y) (ρ Extra) (ρ Ctx) (fun i => ρ (v i)) (fun i => ρ (Gb i)) (fun i => ρ (H i)) (fun i => ρ (U i)) (fun i => ρ (F i)) (fun i => ρ (P i)) (fun i => ρ (N i)) (fun i => ρ (D i)) := by
  simp only [basis, Formula.rename, SyntaxNumeralSyntax.numeral_rename,
    ForcingPreorderLeaves.data_rename, ForcingReflexiveImages.replacement_rename,
    ForcingNegCondition.operations_rename, FormulaCodeSyntax.formulaCode_rename,
    SyntaxLogicalSyntax.binaryCode_rename, InternalProofBackground.implication_rename]

def resultBody {m} (test : Formula 1) (w z T Ctx Target Extra Local : Fin m) : Formula (m+2) :=
  (ForcingTransitiveGuardProof.negativeResult test (old 2 w) (old 2 z) (old 2 T) (old 2 Ctx)
    (old 2 Target) (slot 2 0) (slot 2 1)).conj
    (InternalProofCurry.negativeCurried test (old 2 w) (old 2 z) (old 2 T) (old 2 Extra) (old 2 Local)
      (old 2 Target) (slot 2 0) (slot 2 1))
def result {m} (test : Formula 1) (w z T Ctx Target Extra Local : Fin m) : Formula m :=
  existsMany 2 (resultBody test w z T Ctx Target Extra Local)
theorem result_rename {m l} (test : Formula 1) (w z T Ctx Target Extra Local : Fin m) (ρ : Fin m → Fin l) :
    (result test w z T Ctx Target Extra Local).rename ρ = result test (ρ w) (ρ z) (ρ T) (ρ Ctx) (ρ Target) (ρ Extra) (ρ Local) := by
  simp only [result, existsMany_rename, resultBody, Formula.rename,
    ForcingTransitiveGuardProof.negativeResult_rename, InternalProofCurry.negativeCurried_rename, lift_old, lift_slot]

private structure Inputs {k m} (Γ : Context m) (test : Formula 1) (R : Source.Formula (k+2))
    (w z A1 A2 A3 f T C B S Refl Pre I j Sg mode a A Rb K Hm r s n L Target Y Extra Ctx : Fin m) (v : Fin 16 → Fin m) (Gb : Fin 5 → Fin m) (H : Fin 6 → Fin m) (U : Fin 3 → Fin m) (F : Fin 3 → Fin m) (P : Fin 3 → Fin m) (N : Fin 5 → Fin m) (D : Fin 3 → Fin m) : Prop where
  zf : ZFContext.Evidence Γ
  hb : Derives Γ (basis test R w z A1 A2 A3 f T C B S Refl Pre I j Sg mode a A Rb K Hm r s n L Target Y Extra Ctx v Gb H U F P N D)

private theorem Inputs.in_body {k m l} {Γ : Context m} {test : Formula 1} {R : Source.Formula (k+2)}
    {w z A1 A2 A3 f T C B S Refl Pre I j Sg mode a A Rb K Hm r s n L Target Y Extra Ctx : Fin m} {v : Fin 16 → Fin m} {Gb : Fin 5 → Fin m} {H : Fin 6 → Fin m} {U : Fin 3 → Fin m} {F : Fin 3 → Fin m} {P : Fin 3 → Fin m} {N : Fin 5 → Fin m} {D : Fin 3 → Fin m}
    (h : Inputs Γ test R w z A1 A2 A3 f T C B S Refl Pre I j Sg mode a A Rb K Hm r s n L Target Y Extra Ctx v Gb H U F P N D) (E : Formula (m+l)) :
    Inputs (Context.add E (raisedContext l Γ)) test R (old l w) (old l z) (old l A1) (old l A2) (old l A3) (old l f) (old l T) (old l C) (old l B) (old l S) (old l Refl) (old l Pre) (old l I) (old l j) (old l Sg) (old l mode) (old l a) (old l A) (old l Rb) (old l K) (old l Hm) (old l r) (old l s) (old l n) (old l L) (old l Target) (old l Y) (old l Extra) (old l Ctx) (fun i => old l (v i)) (fun i => old l (Gb i)) (fun i => old l (H i)) (fun i => old l (U i)) (fun i => old l (F i)) (fun i => old l (P i)) (fun i => old l (N i)) (fun i => old l (D i)) :=
  ⟨HornBinderRules.zf_body l h.zf E,
    of_eq (basis_rename test R w z A1 A2 A3 f T C B S Refl Pre I j Sg mode a A Rb K Hm r s n L Target Y Extra Ctx v Gb H U F P N D (old l)) (HornBinderRules.under_body l h.hb E)⟩

private theorem at_final {k m} {Γ : Context m} (test : Formula 1) (R : Source.Formula (k+2))
    (w z A1 A2 A3 f T C B S Refl Pre I j Sg mode a A Rb K Hm r s n L Target Y Extra Ctx uHead head M O operand Bottom Open : Fin m) (v : Fin 16 → Fin m) (Gb : Fin 5 → Fin m) (H : Fin 6 → Fin m) (U : Fin 3 → Fin m) (F : Fin 3 → Fin m) (P : Fin 3 → Fin m) (N : Fin 5 → Fin m) (D : Fin 3 → Fin m)
    (first final : Fin 6 → Fin m)
    (h : Inputs Γ test R w z A1 A2 A3 f T C B S Refl Pre I j Sg mode a A Rb K Hm r s n L Target Y Extra Ctx v Gb H U F P N D)
    (hh : Derives Γ (SyntaxMixedImageHead.head w A f uHead head))
    (hM : Derives Γ (ForcingGuardCode.compiled false R w A f head M))
    (hO : Derives Γ (ForcingGuardCode.compiled true R w A f head O))
    (hBottom : Derives Γ (SyntaxAtomSyntax.zeroScalar w Bottom))
    (hFirst : Derives Γ (ForcingNegShell.chainData w K Hm A f C T M O operand Bottom Open first))
    (hFinal : Derives Γ (ForcingNegShell.finalData w r s C T z Y Target Bottom first final)) :
    Derives Γ (result test w z T Ctx Target Extra (Gb 0)) := by
  have b0 := Derives.conjL (h.hb)
  have b1 := Derives.conjL (Derives.conjR (h.hb))
  have b2 := Derives.conjL (Derives.conjR (Derives.conjR (h.hb)))
  have b3 := Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (h.hb))))
  have b4 := Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (h.hb)))))
  have b5 := Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (h.hb))))))
  have b6 := Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (h.hb)))))))
  have b7 := Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (h.hb))))))))
  have b8 := Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (h.hb)))))))))
  have b9 := Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (h.hb))))))))))
  have b10 := Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (h.hb)))))))))))
  have b11 := Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (h.hb))))))))))))
  have b12 := Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (h.hb))))))))))))
  have hw := Derives.conjL (b8)
  have hz := Derives.conjL (Derives.conjR (Derives.conjR (b8)))
  have hInst := Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (b8)))))))))
  have hFrame : Derives Γ (ForcingMemberGuardOpening.frame w mode z a f T A C Rb Sg K Hm (P 0) r s) :=
    .conjI hw (.conjI (Derives.conjL (Derives.conjR (b8))) (.conjI hz (.conjI (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (b8)))))
      (.conjI (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (b8)))))) (.conjI hInst (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (b8)))))))))))))
  have hLast := Derives.conjL hFinal
  have hMemberInst := Derives.impE (.conjR (SyntaxTopFormulaCodes.instantiate_at_codes h.zf w z T C (P 0) (first 0) (final 0) r s hw hInst)) (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (hLast)))))
  have hOrderInst := Derives.impE (.conjR (SyntaxTopFormulaCodes.instantiate_at_codes h.zf w z T C (P 0) (first 1) (final 1) r s hw hInst)) (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (hLast))))))
  have hMember := ForcingPreorderGuardTables.member_from_instance h.zf test R 0
    w z A1 A2 A3 f T C B S Refl Pre I j (P 2) Sg mode a A Rb K Hm r s uHead head M (first 0) (final 0)
    v Gb H U F P N D b0 b1 b3 b4 b5 b6 b7 hFrame hh hM (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (hFirst))))) hMemberInst
  have hOrder := ForcingPreorderGuardTables.relation_from_instance h.zf test R
    w z A1 A2 A3 f T C B S Refl Pre j Sg mode a A Rb K Hm r s uHead head O (first 1) (final 1)
    v Gb H U F P N D b0 b1 b2 b3 b4 b6 b7 hFrame hh hO (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (hFirst)))))) hOrderInst
  have hOuter := SyntaxRenameLogicalSubst.binary_x 2 w (final 0) (final 5) Y (H 0) (eq_symm hMember) (Derives.conjL (hLast))
  have hOrderCode := SyntaxRenameLogicalSubst.binary_x 2 w (final 1) (final 4) (final 5) (H 5) (eq_symm hOrder) (Derives.conjL (Derives.conjR (hLast)))
  have hRest := SyntaxRenameLogicalSubst.binary_y 2 w Target (final 3) (final 4) Bottom (.conjR (.conjR hFinal))
    (SyntaxRenameLogicalSubst.binary_x 2 w (final 2) (final 3) (final 4) Target (.conjL (.conjR hFinal)) (Derives.conjL (Derives.conjR (Derives.conjR (hLast)))))
  have hRow := Derives.conjL (Derives.conjL (Derives.conjR b6))
  have hp := ForcingTransitiveGuardProof.at_negative_under h.zf test w z T C Refl Pre Extra Ctx Target Bottom (final 4) (final 5) Y
    Gb H U F P N hw hz hRow b9 b10 b11 hOuter hOrderCode hRest hBottom b12
  have hLocalType := Derives.conjL hRow
  have hExtraType := Derives.conjL (Derives.conjR (Derives.impE
    (.conjL (FormulaCodeKnownLogical.binary0_iff h.zf w z T Extra (Gb 0) Ctx hw b10)) b9))
  have hMiddleType := Derives.conjR (Derives.conjR (Derives.impE
    (.conjL (FormulaCodeKnownLogical.binary2_iff h.zf w z T (H 0) (final 5) Y hw hOuter)) b11))
  have hRestType := Derives.conjR (Derives.conjR (Derives.impE
    (.conjL (FormulaCodeKnownLogical.binary2_iff h.zf w z T (H 5) (final 4) (final 5) hw hOrderCode)) hMiddleType))
  have hCurry := InternalProofCurry.from_implication h.zf test w z T Extra (Gb 0) Ctx (final 4)
    hw hz hExtraType hLocalType hRestType b10 (.conjR (.conjR hp))
  have hCurried : Derives Γ (InternalProofCurry.negativeCurried test w z T Extra (Gb 0) Target Bottom (final 4)) :=
    .conjI hRest (.conjI hBottom hCurry)
  apply HornBinderRules.intro_many 2 _ (SyntaxAtomSyntax.two Bottom (final 4))
  exact of_eq (by simp only [resultBody, Formula.rename, ForcingTransitiveGuardProof.negativeResult_rename, InternalProofCurry.negativeCurried_rename, assign_old, assign_slot]; rfl) (.conjI hp hCurried)


private structure GuardInputs {k m} (Γ : Context m) (test : Formula 1) (R : Source.Formula (k+2))
    (w z A1 A2 A3 f T C B S Refl Pre I j Sg mode a A Rb K Hm r s n L Target Y Extra Ctx uHead head M O Bottom : Fin m) (v : Fin 16 → Fin m) (Gb : Fin 5 → Fin m) (H : Fin 6 → Fin m) (U : Fin 3 → Fin m) (F : Fin 3 → Fin m) (P : Fin 3 → Fin m) (N : Fin 5 → Fin m) (D : Fin 3 → Fin m) : Prop where
  base : Inputs Γ test R w z A1 A2 A3 f T C B S Refl Pre I j Sg mode a A Rb K Hm r s n L Target Y Extra Ctx v Gb H U F P N D
  hh : Derives Γ (SyntaxMixedImageHead.head w A f uHead head)
  hM : Derives Γ (ForcingGuardCode.compiled false R w A f head M)
  hO : Derives Γ (ForcingGuardCode.compiled true R w A f head O)
  hBottom : Derives Γ (SyntaxAtomSyntax.zeroScalar w Bottom)

private theorem GuardInputs.in_body {k m l} {Γ : Context m} {test : Formula 1} {R : Source.Formula (k+2)}
    {w z A1 A2 A3 f T C B S Refl Pre I j Sg mode a A Rb K Hm r s n L Target Y Extra Ctx uHead head M O Bottom : Fin m} {v : Fin 16 → Fin m} {Gb : Fin 5 → Fin m} {H : Fin 6 → Fin m} {U : Fin 3 → Fin m} {F : Fin 3 → Fin m} {P : Fin 3 → Fin m} {N : Fin 5 → Fin m} {D : Fin 3 → Fin m}
    (h : GuardInputs Γ test R w z A1 A2 A3 f T C B S Refl Pre I j Sg mode a A Rb K Hm r s n L Target Y Extra Ctx uHead head M O Bottom v Gb H U F P N D) (E : Formula (m+l)) :
    GuardInputs (Context.add E (raisedContext l Γ)) test R
      (old l w) (old l z) (old l A1) (old l A2) (old l A3) (old l f) (old l T) (old l C) (old l B) (old l S) (old l Refl) (old l Pre) (old l I) (old l j) (old l Sg) (old l mode) (old l a) (old l A) (old l Rb) (old l K) (old l Hm) (old l r) (old l s) (old l n) (old l L) (old l Target) (old l Y) (old l Extra) (old l Ctx) (old l uHead) (old l head) (old l M) (old l O) (old l Bottom)
      (fun i => old l (v i)) (fun i => old l (Gb i)) (fun i => old l (H i)) (fun i => old l (U i)) (fun i => old l (F i)) (fun i => old l (P i)) (fun i => old l (N i)) (fun i => old l (D i)) := by
  exact ⟨h.base.in_body E,
    of_eq (SyntaxMixedImageHead.head_rename w A f uHead head (old l)) (HornBinderRules.under_body l h.hh E),
    of_eq (ForcingGuardCode.compiled_rename false R w A f head M (old l)) (HornBinderRules.under_body l h.hM E),
    of_eq (ForcingGuardCode.compiled_rename true R w A f head O (old l)) (HornBinderRules.under_body l h.hO E),
    of_eq (SyntaxAtomSyntax.zeroScalar_rename w Bottom (old l)) (HornBinderRules.under_body l h.hBottom E)⟩

private theorem from_final_fields {k m} {Γ : Context m} (test : Formula 1) (R : Source.Formula (k+2))
    (w z A1 A2 A3 f T C B S Refl Pre I j Sg mode a A Rb K Hm r s n L Target Y Extra Ctx uHead head M O operand Bottom Open : Fin m) (v : Fin 16 → Fin m) (Gb : Fin 5 → Fin m) (H : Fin 6 → Fin m) (U : Fin 3 → Fin m) (F : Fin 3 → Fin m) (P : Fin 3 → Fin m) (N : Fin 5 → Fin m) (D : Fin 3 → Fin m) (first : Fin 6 → Fin m)
    (h : GuardInputs Γ test R w z A1 A2 A3 f T C B S Refl Pre I j Sg mode a A Rb K Hm r s n L Target Y Extra Ctx uHead head M O Bottom v Gb H U F P N D)
    (hFirst : Derives Γ (ForcingNegShell.chainData w K Hm A f C T M O operand Bottom Open first))
    (hFinal : Derives Γ (ForcingNegShell.finalFields w r s C T z Y Target Bottom first)) :
    Derives Γ (result test w z T Ctx Target Extra (Gb 0)) := by
  let E := ForcingNegShell.finalBody w r s C T z Y Target Bottom first
  let Δ := Context.add E (raisedContext 6 Γ)
  apply HornBinderRules.eliminate_many 6 E _ hFinal
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have h6 := h.in_body E
  have hFirst6 := of_eq (ForcingNegShell.chainData_rename w K Hm A f C T M O operand Bottom Open first (old 6)) (HornBinderRules.under_body 6 hFirst E)
  have hout := at_final test R (old 6 w) (old 6 z) (old 6 A1) (old 6 A2) (old 6 A3) (old 6 f) (old 6 T) (old 6 C) (old 6 B) (old 6 S) (old 6 Refl) (old 6 Pre) (old 6 I) (old 6 j) (old 6 Sg) (old 6 mode) (old 6 a) (old 6 A) (old 6 Rb) (old 6 K) (old 6 Hm) (old 6 r) (old 6 s) (old 6 n) (old 6 L) (old 6 Target) (old 6 Y) (old 6 Extra) (old 6 Ctx)
    (old 6 uHead) (old 6 head) (old 6 M) (old 6 O) (old 6 operand) (old 6 Bottom) (old 6 Open)
    (fun i => old 6 (v i)) (fun i => old 6 (Gb i)) (fun i => old 6 (H i)) (fun i => old 6 (U i)) (fun i => old 6 (F i)) (fun i => old 6 (P i)) (fun i => old 6 (N i)) (fun i => old 6 (D i))
    (fun i => old 6 (first i)) (slot 6) h6.base h6.hh h6.hM h6.hO h6.hBottom hFirst6 hE
  exact of_eq (result_rename test w z T Ctx Target Extra (Gb 0) (old 6)).symm hout

private theorem from_normalized {k m} {Γ : Context m} (test : Formula 1) (R : Source.Formula (k+2))
    (w z A1 A2 A3 f T C B S Refl Pre I j Sg mode a A Rb K Hm r s n L Target Y Extra Ctx uHead head M O operand Bottom Open : Fin m) (v : Fin 16 → Fin m) (Gb : Fin 5 → Fin m) (H : Fin 6 → Fin m) (U : Fin 3 → Fin m) (F : Fin 3 → Fin m) (P : Fin 3 → Fin m) (N : Fin 5 → Fin m) (D : Fin 3 → Fin m)
    (h : GuardInputs Γ test R w z A1 A2 A3 f T C B S Refl Pre I j Sg mode a A Rb K Hm r s n L Target Y Extra Ctx uHead head M O Bottom v Gb H U F P N D)
    (hn : Derives Γ (ForcingNegShell.normalized w K Hm A f C T M O operand Bottom Open r s z Y Target)) :
    Derives Γ (result test w z T Ctx Target Extra (Gb 0)) := by
  let E := ForcingNegShell.normalizedBody w K Hm A f C T M O operand Bottom Open r s z Y Target
  let Δ := Context.add E (raisedContext 6 Γ)
  apply HornBinderRules.eliminate_many 6 E _ hn
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have h6 := h.in_body E
  have hout := from_final_fields test R (old 6 w) (old 6 z) (old 6 A1) (old 6 A2) (old 6 A3) (old 6 f) (old 6 T) (old 6 C) (old 6 B) (old 6 S) (old 6 Refl) (old 6 Pre) (old 6 I) (old 6 j) (old 6 Sg) (old 6 mode) (old 6 a) (old 6 A) (old 6 Rb) (old 6 K) (old 6 Hm) (old 6 r) (old 6 s) (old 6 n) (old 6 L) (old 6 Target) (old 6 Y) (old 6 Extra) (old 6 Ctx)
    (old 6 uHead) (old 6 head) (old 6 M) (old 6 O) (old 6 operand) (old 6 Bottom) (old 6 Open)
    (fun i => old 6 (v i)) (fun i => old 6 (Gb i)) (fun i => old 6 (H i)) (fun i => old 6 (U i)) (fun i => old 6 (F i)) (fun i => old 6 (P i)) (fun i => old 6 (N i)) (fun i => old 6 (D i))
    (slot 6) h6 (.conjL hE) (.conjR hE)
  exact of_eq (result_rename test w z T Ctx Target Extra (Gb 0) (old 6)).symm hout

private theorem from_shell {k m} {Γ : Context m} (test : Formula 1) (R : Source.Formula (k+2))
    (w z A1 A2 A3 f T C B S Refl Pre I j Sg mode a A Rb K Hm r s n L Target Y Extra Ctx uHead head M O operand Q Open : Fin m) (v : Fin 16 → Fin m) (Gb : Fin 5 → Fin m) (H : Fin 6 → Fin m) (U : Fin 3 → Fin m) (F : Fin 3 → Fin m) (P : Fin 3 → Fin m) (N : Fin 5 → Fin m) (D : Fin 3 → Fin m)
    (h : Inputs Γ test R w z A1 A2 A3 f T C B S Refl Pre I j Sg mode a A Rb K Hm r s n L Target Y Extra Ctx v Gb H U F P N D)
    (hh : Derives Γ (SyntaxMixedImageHead.head w A f uHead head))
    (hM : Derives Γ (ForcingGuardCode.compiled false R w A f head M))
    (hO : Derives Γ (ForcingGuardCode.compiled true R w A f head O))
    (hs : Derives Γ (ForcingNegNormalization.shellResult w a A f M O operand Q K Hm C T Open r s z Y Target)) :
    Derives Γ (result test w z T Ctx Target Extra (Gb 0)) := by
  let E := ForcingNegNormalization.shellResultBody w a A f M O operand Q K Hm C T Open r s z Y Target
  let Δ := Context.add E (raisedContext 4 Γ)
  apply HornBinderRules.eliminate_many 4 E _ hs
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have h4 := h.in_body E
  have hh4 := of_eq (SyntaxMixedImageHead.head_rename w A f uHead head (old 4)) (HornBinderRules.under_body 4 hh E)
  have hM4 := of_eq (ForcingGuardCode.compiled_rename false R w A f head M (old 4)) (HornBinderRules.under_body 4 hM E)
  have hO4 := of_eq (ForcingGuardCode.compiled_rename true R w A f head O (old 4)) (HornBinderRules.under_body 4 hO E)
  have hShell := Derives.conjL hE
  have hBottom : Derives Δ (SyntaxAtomSyntax.zeroScalar (old 4 w) (slot 4 0)) := .conjL (.conjL hShell)
  have hGuard : GuardInputs Δ test R (old 4 w) (old 4 z) (old 4 A1) (old 4 A2) (old 4 A3) (old 4 f) (old 4 T) (old 4 C) (old 4 B) (old 4 S) (old 4 Refl) (old 4 Pre) (old 4 I) (old 4 j) (old 4 Sg) (old 4 mode) (old 4 a) (old 4 A) (old 4 Rb) (old 4 K) (old 4 Hm) (old 4 r) (old 4 s) (old 4 n) (old 4 L) (old 4 Target) (old 4 Y) (old 4 Extra) (old 4 Ctx)
      (old 4 uHead) (old 4 head) (old 4 M) (old 4 O) (slot 4 0)
      (fun i => old 4 (v i)) (fun i => old 4 (Gb i)) (fun i => old 4 (H i)) (fun i => old 4 (U i)) (fun i => old 4 (F i)) (fun i => old 4 (P i)) (fun i => old 4 (N i)) (fun i => old 4 (D i)) := ⟨h4,hh4,hM4,hO4,hBottom⟩
  have hout := from_normalized test R (old 4 w) (old 4 z) (old 4 A1) (old 4 A2) (old 4 A3) (old 4 f) (old 4 T) (old 4 C) (old 4 B) (old 4 S) (old 4 Refl) (old 4 Pre) (old 4 I) (old 4 j) (old 4 Sg) (old 4 mode) (old 4 a) (old 4 A) (old 4 Rb) (old 4 K) (old 4 Hm) (old 4 r) (old 4 s) (old 4 n) (old 4 L) (old 4 Target) (old 4 Y) (old 4 Extra) (old 4 Ctx)
    (old 4 uHead) (old 4 head) (old 4 M) (old 4 O) (old 4 operand) (slot 4 0) (old 4 Open)
    (fun i => old 4 (v i)) (fun i => old 4 (Gb i)) (fun i => old 4 (H i)) (fun i => old 4 (U i)) (fun i => old 4 (F i)) (fun i => old 4 (P i)) (fun i => old 4 (N i)) (fun i => old 4 (D i))
    hGuard (.conjR hE)
  exact of_eq (result_rename test w z T Ctx Target Extra (Gb 0) (old 4)).symm hout

private theorem from_compiled {k m} {Γ : Context m} (test : Formula 1) (R : Source.Formula (k+2))
    (w z A1 A2 A3 f T C B S Refl Pre I j Sg mode a A Rb K Hm r s n L Target Y Extra Ctx Q Open : Fin m) (v : Fin 16 → Fin m) (Gb : Fin 5 → Fin m) (H : Fin 6 → Fin m) (U : Fin 3 → Fin m) (F : Fin 3 → Fin m) (P : Fin 3 → Fin m) (N : Fin 5 → Fin m) (D : Fin 3 → Fin m) (h : Inputs Γ test R w z A1 A2 A3 f T C B S Refl Pre I j Sg mode a A Rb K Hm r s n L Target Y Extra Ctx v Gb H U F P N D)
    (hc : Derives Γ (ForcingNegNormalization.compiled R w a A f j n Q K Hm C T Open r s z Y Target)) :
    Derives Γ (result test w z T Ctx Target Extra (Gb 0)) := by
  let E := ForcingNegNormalization.compiledBody R w a A f j n Q K Hm C T Open r s z Y Target
  let Δ := Context.add E (raisedContext 5 Γ)
  apply HornBinderRules.eliminate_many 5 E _ hc
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have h5 := h.in_body E
  have hout := from_shell test R (old 5 w) (old 5 z) (old 5 A1) (old 5 A2) (old 5 A3) (old 5 f) (old 5 T) (old 5 C) (old 5 B) (old 5 S) (old 5 Refl) (old 5 Pre) (old 5 I) (old 5 j) (old 5 Sg) (old 5 mode) (old 5 a) (old 5 A) (old 5 Rb) (old 5 K) (old 5 Hm) (old 5 r) (old 5 s) (old 5 n) (old 5 L) (old 5 Target) (old 5 Y) (old 5 Extra) (old 5 Ctx)
    (slot 5 0) (slot 5 1) (slot 5 3) (slot 5 4) (slot 5 2) (old 5 Q) (old 5 Open)
    (fun i => old 5 (v i)) (fun i => old 5 (Gb i)) (fun i => old 5 (H i)) (fun i => old 5 (U i)) (fun i => old 5 (F i)) (fun i => old 5 (P i)) (fun i => old 5 (N i)) (fun i => old 5 (D i))
    h5 (.conjL hE) (.conjL (.conjR (.conjR hE))) (.conjL (.conjR (.conjR (.conjR hE))))
    (.conjR (.conjR (.conjR (.conjR hE))))
  exact of_eq (result_rename test w z T Ctx Target Extra (Gb 0) (old 5)).symm hout


/-- Directly consume the original complete compiler and the actual body
opening/native InstantiateTop. The SAME preorder supplies both guard proofs;
all 5+4+6+6 original witnesses are eliminated internally. The supplied parent
is an INTERNAL proof under Ctx, never a truth assumption for Ctx or a guard. -/
theorem derive {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (test : Formula 1) (R : Source.Formula (k+2))
    (w z A1 A2 A3 f T C B S Refl Pre I j Sg mode a A Rb K Hm r s n L Target Y Extra Ctx Q J Open : Fin m) (v : Fin 16 → Fin m) (Gb : Fin 5 → Fin m) (H : Fin 6 → Fin m) (U : Fin 3 → Fin m) (F : Fin 3 → Fin m) (P : Fin 3 → Fin m) (N : Fin 5 → Fin m) (D : Fin 3 → Fin m)
    (h1 : Derives Γ (SyntaxNumeralSyntax.numeral 1 A1))
    (h2 : Derives Γ (SyntaxNumeralSyntax.numeral 2 A2))
    (h3 : Derives Γ (SyntaxNumeralSyntax.numeral 3 A3))
    (hf : Derives Γ (SyntaxNumeralSyntax.numeral (k+2) f))
    (hj : Derives Γ (SyntaxNumeralSyntax.numeral (k+1) j))
    (hI : Derives Γ (SyntaxNumeralSyntax.numeral k I))
    (hd : Derives Γ (ForcingPreorderLeaves.data test R w z A1 A2 A3 f T C B S Refl Pre v Gb H U F P N D))
    (hr : Derives Γ (ForcingReflexiveImages.replacement w f z T S j (P 2) Sg))
    (hop : Derives Γ (ForcingNegCondition.operations w mode z a f T A C Rb Sg K Hm j n (P 0) r s L Target))
    (hCtx : Derives Γ (FormulaCodeSyntax.formulaCode w Ctx z T))
    (hAnd : Derives Γ (SyntaxLogicalSyntax.binaryCode 0 w Extra (Gb 0) Ctx))
    (hp : Derives Γ (InternalProofBackground.implication test w z T Ctx Y))
    (hc : Derives Γ (ForcingNegCode.compiled R w a A f j n Q))
    (hJ : Derives Γ (SyntaxLogicalSyntax.singleCode 9 w J Q))
    (ho : Derives Γ (substituted w K Hm A f C T J Open))
    (hi : Derives Γ (SyntaxTopFormulaSyntax.instantiated w z T C (P 0) Open Y)) :
    Derives Γ (result test w z T Ctx Target Extra (Gb 0)) := by
  have hY := SyntaxTopFormulaTyping.instantiate_target_type w z T C (P 0) Open Y hi
  have hb : Derives Γ (basis test R w z A1 A2 A3 f T C B S Refl Pre I j Sg mode a A Rb K Hm r s n L Target Y Extra Ctx v Gb H U F P N D) := .conjI h1 (.conjI h2 (.conjI h3 (.conjI hf (.conjI hj (.conjI hI (.conjI hd (.conjI hr (.conjI hop (.conjI hCtx (.conjI hAnd (.conjI hY (hp))))))))))))
  have hComplete := ForcingNegCondition.from_instance hZ R w mode z a f T A C Rb Sg K Hm j n (P 0) r s L Target Q J Open Y
    hop hc hJ ho hi
  exact from_compiled test R w z A1 A2 A3 f T C B S Refl Pre I j Sg mode a A Rb K Hm r s n L Target Y Extra Ctx Q Open v Gb H U F P N D ⟨hZ,hb⟩ hComplete

def input {k m} (test : Formula 1) (R : Source.Formula (k+2))
    (w z A1 A2 A3 f T C B S Refl Pre I j Sg mode a A Rb K Hm r s n L Target Y Extra Ctx Q J Open : Fin m) (v : Fin 16 → Fin m) (Gb : Fin 5 → Fin m) (H : Fin 6 → Fin m) (U : Fin 3 → Fin m) (F : Fin 3 → Fin m) (P : Fin 3 → Fin m) (N : Fin 5 → Fin m) (D : Fin 3 → Fin m) : Formula m :=
  (SyntaxNumeralSyntax.numeral 1 A1).conj ((SyntaxNumeralSyntax.numeral 2 A2).conj ((SyntaxNumeralSyntax.numeral 3 A3).conj ((SyntaxNumeralSyntax.numeral (k+2) f).conj ((SyntaxNumeralSyntax.numeral (k+1) j).conj ((SyntaxNumeralSyntax.numeral k I).conj ((ForcingPreorderLeaves.data test R w z A1 A2 A3 f T C B S Refl Pre v Gb H U F P N D).conj ((ForcingReflexiveImages.replacement w f z T S j (P 2) Sg).conj ((ForcingNegCondition.operations w mode z a f T A C Rb Sg K Hm j n (P 0) r s L Target).conj ((FormulaCodeSyntax.formulaCode w Ctx z T).conj ((SyntaxLogicalSyntax.binaryCode 0 w Extra (Gb 0) Ctx).conj ((InternalProofBackground.implication test w z T Ctx Y).conj ((ForcingNegCode.compiled R w a A f j n Q).conj ((SyntaxLogicalSyntax.singleCode 9 w J Q).conj ((substituted w K Hm A f C T J Open).conj ((SyntaxTopFormulaSyntax.instantiated w z T C (P 0) Open Y))))))))))))))))

def sentence {k m} (test : Formula 1) (R : Source.Formula (k+2))
    (w z A1 A2 A3 f T C B S Refl Pre I j Sg mode a A Rb K Hm r s n L Target Y Extra Ctx Q J Open : Fin m) (v : Fin 16 → Fin m) (Gb : Fin 5 → Fin m) (H : Fin 6 → Fin m) (U : Fin 3 → Fin m) (F : Fin 3 → Fin m) (P : Fin 3 → Fin m) (N : Fin 5 → Fin m) (D : Fin 3 → Fin m) : Source.Sentence :=
  ((input test R w z A1 A2 A3 f T C B S Refl Pre I j Sg mode a A Rb K Hm r s n L Target Y Extra Ctx Q J Open v Gb H U F P N D).imp (result test w z T Ctx Target Extra (Gb 0))).close

theorem kernel_certificate {k m} (test : Formula 1) (R : Source.Formula (k+2))
    (w z A1 A2 A3 f T C B S Refl Pre I j Sg mode a A Rb K Hm r s n L Target Y Extra Ctx Q J Open : Fin m) (v : Fin 16 → Fin m) (Gb : Fin 5 → Fin m) (H : Fin 6 → Fin m) (U : Fin 3 → Fin m) (F : Fin 3 → Fin m) (P : Fin 3 → Fin m) (N : Fin 5 → Fin m) (D : Fin 3 → Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (sentence test R w z A1 A2 A3 f T C B S Refl Pre I j Sg mode a A Rb K Hm r s n L Target Y Extra Ctx Q J Open v Gb H U F P N D)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  let E := input test R w z A1 A2 A3 f T C B S Refl Pre I j Sg mode a A Rb K Hm r s n L Target Y Extra Ctx Q J Open v Gb H U F P N D
  let Γ := Context.add E (Source.SetLanguage.ZF.at m)
  have h : Derives Γ E := .hyp (Or.inl rfl)
  exact derive (ZFContext.add (ZFContext.source_ZF m) E) test R w z A1 A2 A3 f T C B S Refl Pre I j Sg mode a A Rb K Hm r s n L Target Y Extra Ctx Q J Open v Gb H U F P N D
    (Derives.conjL (h))
    (Derives.conjL (Derives.conjR (h)))
    (Derives.conjL (Derives.conjR (Derives.conjR (h))))
    (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (h)))))
    (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (h))))))
    (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (h)))))))
    (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (h))))))))
    (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (h)))))))))
    (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (h))))))))))
    (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (h)))))))))))
    (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (h))))))))))))
    (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (h)))))))))))))
    (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (h))))))))))))))
    (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (h)))))))))))))))
    (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (h))))))))))))))))
    (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (h))))))))))))))))

end PPAC.Migration.ForcingPreorderNegative
