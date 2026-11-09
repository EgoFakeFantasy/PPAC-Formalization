import PPAC.Migration.ForcingExistCode
import PPAC.Migration.ForcingPreorderGuardTables
import PPAC.Migration.InternalProofCurry

/-! Consume the SAME complete original existential compiler and its actual
opening/native instance. Outer guard readout reuses original mixed binary
outputs and the same raw preorder/internal proof producers. This does not
assert the remaining tail invariance or the final uniform forcing theorem. -/
namespace PPAC.Migration.ForcingPreorderExistential
open Internal Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)
open SyntaxMixedFormulaJudgmentSyntax (substituted substituted_rename)
set_option maxRecDepth 32768
set_option maxHeartbeats 2500000
attribute [local irreducible] NaturalRecursionSyntax.matrix

private def chainData {m} (w R S a b c d M O Tail Q : Fin m) (v : Fin 4 → Fin m) : Formula m :=
  (SyntaxLogicalSyntax.binaryCode 2 w (v 0) (v 3) Q).conj
    ((SyntaxLogicalSyntax.binaryCode 2 w (v 1) (v 2) (v 3)).conj
      ((substituted w R S a b c d M (v 0)).conj
        ((substituted w R S a b c d O (v 1)).conj (substituted w R S a b c d Tail (v 2)))))
private theorem chainData_rename {m l} (w R S a b c d M O Tail Q : Fin m) (v : Fin 4 → Fin m) (ρ : Fin m → Fin l) :
    (chainData w R S a b c d M O Tail Q v).rename ρ =
      chainData (ρ w) (ρ R) (ρ S) (ρ a) (ρ b) (ρ c) (ρ d) (ρ M) (ρ O) (ρ Tail) (ρ Q) (fun i => ρ (v i)) := by
  simp only [chainData, Formula.rename, SyntaxLogicalSyntax.binaryCode_rename, substituted_rename]
private def chainBody {m} (w R S a b c d M O Tail Q : Fin m) : Formula (m+4) :=
  chainData (old 4 w) (old 4 R) (old 4 S) (old 4 a) (old 4 b) (old 4 c) (old 4 d)
    (old 4 M) (old 4 O) (old 4 Tail) (old 4 Q) (slot 4)
private def chain {m} (w R S a b c d M O Tail Q : Fin m) : Formula m :=
  existsMany 4 (chainBody w R S a b c d M O Tail Q)
private theorem chain_rename {m l} (w R S a b c d M O Tail Q : Fin m) (ρ : Fin m → Fin l) :
    (chain w R S a b c d M O Tail Q).rename ρ =
      chain (ρ w) (ρ R) (ρ S) (ρ a) (ρ b) (ρ c) (ρ d) (ρ M) (ρ O) (ρ Tail) (ρ Q) := by
  simp only [chain, existsMany_rename, chainBody, chainData_rename, lift_old, lift_slot]

/-- Two calls to the EXISTING mixed binary-output theorem, not a new
compiler, checker, recursion or induction. All four outputs are object-bound. -/
private theorem transform {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w R S a b c d M O Tail Inner Parent Q : Fin m)
    (hw : Derives Γ (omega w))
    (hInner : Derives Γ (SyntaxLogicalSyntax.binaryCode 2 w O Tail Inner))
    (hOuter : Derives Γ (SyntaxLogicalSyntax.binaryCode 2 w M Inner Parent))
    (hp : Derives Γ (substituted w R S a b c d Parent Q)) :
    Derives Γ (chain w R S a b c d M O Tail Q) := by
  have he0 := ForcingFormulaDiagram.binary_output hZ 2 w R S a b c d Parent M Inner Q hw hOuter hp
  let E0 := ForcingFormulaDiagram.binaryBody 2 w R S a b c d M Inner Q
  let Δ1 := Context.add E0 (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 E0 _ he0
  have hE0 : Derives Δ1 E0 := .hyp (Or.inl rfl)
  have hZ1 := HornBinderRules.zf_body 2 hZ E0
  have hw1 := of_eq (omega_rename w (old 2)) (HornBinderRules.under_body 2 hw E0)
  have hInner1 := of_eq (SyntaxLogicalSyntax.binaryCode_rename 2 w O Tail Inner (old 2)) (HornBinderRules.under_body 2 hInner E0)
  have he1 := ForcingFormulaDiagram.binary_output hZ1 2 (old 2 w) (old 2 R) (old 2 S) (old 2 a) (old 2 b) (old 2 c) (old 2 d)
    (old 2 Inner) (old 2 O) (old 2 Tail) (slot 2 1) hw1 hInner1 (.conjR (.conjR hE0))
  let E1 := ForcingFormulaDiagram.binaryBody 2 (old 2 w) (old 2 R) (old 2 S) (old 2 a) (old 2 b) (old 2 c) (old 2 d)
    (old 2 O) (old 2 Tail) (slot 2 1)
  let Δ2 := Context.add E1 (raisedContext 2 Δ1)
  apply HornBinderRules.eliminate_many 2 E1 _ he1
  have hE1 : Derives Δ2 E1 := .hyp (Or.inl rfl)
  have hOld : Derives Δ2 (ForcingFormulaDiagram.binaryData 2 (old 4 w) (old 4 R) (old 4 S)
      (old 4 a) (old 4 b) (old 4 c) (old 4 d) (old 4 M) (old 4 Inner) (old 4 Q)
      (old 2 (slot 2 0)) (old 2 (slot 2 1))) :=
    of_eq (by simp only [E0, ForcingFormulaDiagram.binaryBody, ForcingFormulaDiagram.binaryData_rename]; rfl)
      (HornBinderRules.under_body 2 hE0 E1)
  let values : Fin 4 → Fin (m+4) :=
    Fin.cases (old 2 (slot 2 0)) (Fin.cases (slot 2 0) (Fin.cases (slot 2 1) (fun _ => old 2 (slot 2 1))))
  have hout : Derives Δ2 (chain (old 4 w) (old 4 R) (old 4 S) (old 4 a) (old 4 b) (old 4 c) (old 4 d)
      (old 4 M) (old 4 O) (old 4 Tail) (old 4 Q)) := by
    apply HornBinderRules.intro_many 4 _ values
    exact of_eq (by simp only [chainBody, chainData_rename, assign_old, assign_slot]; rfl)
      (.conjI (.conjL hOld) (.conjI (.conjL hE1)
        (.conjI (.conjL (.conjR hOld)) (.conjI (.conjL (.conjR hE1)) (.conjR (.conjR hE1))))))
  exact of_eq (by simp only [chain_rename]; rfl) hout


def basis {k m} (test : Formula 1) (R : Source.Formula (k+2))
    (w z A1 A2 A3 f T C B S Refl Pre I j Sg mode a A Rb K Hm r s Y Extra Ctx : Fin m) (v : Fin 16 → Fin m) (Gb : Fin 5 → Fin m) (H : Fin 6 → Fin m) (U : Fin 3 → Fin m) (F : Fin 3 → Fin m) (P : Fin 3 → Fin m) (N : Fin 5 → Fin m) (D : Fin 3 → Fin m) : Formula m :=
  (SyntaxNumeralSyntax.numeral 1 A1).conj ((SyntaxNumeralSyntax.numeral 2 A2).conj ((SyntaxNumeralSyntax.numeral 3 A3).conj ((SyntaxNumeralSyntax.numeral (k+2) f).conj ((SyntaxNumeralSyntax.numeral (k+1) j).conj ((SyntaxNumeralSyntax.numeral k I).conj ((ForcingPreorderLeaves.data test R w z A1 A2 A3 f T C B S Refl Pre v Gb H U F P N D).conj ((ForcingReflexiveImages.replacement w f z T S j (P 2) Sg).conj ((ForcingMemberGuardOpening.frame w mode z a f T A C Rb Sg K Hm (P 0) r s).conj ((FormulaCodeSyntax.formulaCode w Ctx z T).conj ((SyntaxLogicalSyntax.binaryCode 0 w Extra (Gb 0) Ctx).conj ((FormulaCodeSyntax.formulaCode w Y z T).conj ((InternalProofBackground.implication test w z T Ctx Y)))))))))))))
theorem basis_rename {k m l} (test : Formula 1) (R : Source.Formula (k+2))
    (w z A1 A2 A3 f T C B S Refl Pre I j Sg mode a A Rb K Hm r s Y Extra Ctx : Fin m) (v : Fin 16 → Fin m) (Gb : Fin 5 → Fin m) (H : Fin 6 → Fin m) (U : Fin 3 → Fin m) (F : Fin 3 → Fin m) (P : Fin 3 → Fin m) (N : Fin 5 → Fin m) (D : Fin 3 → Fin m) (ρ : Fin m → Fin l) :
    (basis test R w z A1 A2 A3 f T C B S Refl Pre I j Sg mode a A Rb K Hm r s Y Extra Ctx v Gb H U F P N D).rename ρ = basis test R (ρ w) (ρ z) (ρ A1) (ρ A2) (ρ A3) (ρ f) (ρ T) (ρ C) (ρ B) (ρ S) (ρ Refl) (ρ Pre) (ρ I) (ρ j) (ρ Sg) (ρ mode) (ρ a) (ρ A) (ρ Rb) (ρ K) (ρ Hm) (ρ r) (ρ s) (ρ Y) (ρ Extra) (ρ Ctx) (fun i => ρ (v i)) (fun i => ρ (Gb i)) (fun i => ρ (H i)) (fun i => ρ (U i)) (fun i => ρ (F i)) (fun i => ρ (P i)) (fun i => ρ (N i)) (fun i => ρ (D i)) := by
  simp only [basis, Formula.rename, SyntaxNumeralSyntax.numeral_rename,
    ForcingPreorderLeaves.data_rename, ForcingReflexiveImages.replacement_rename,
    ForcingMemberGuardOpening.frame_rename, FormulaCodeSyntax.formulaCode_rename,
    SyntaxLogicalSyntax.binaryCode_rename, InternalProofBackground.implication_rename]

def resultData {m} (test : Formula 1) (w z T Y Ctx Extra Local M O Tail Middle : Fin m) : Formula m :=
  (SyntaxLogicalSyntax.binaryCode 2 w M Middle Y).conj
    ((SyntaxLogicalSyntax.binaryCode 2 w O Tail Middle).conj
      ((FormulaCodeSyntax.formulaCode w Tail z T).conj
        ((InternalProofBackground.implication test w z T Ctx Tail).conj
          (InternalProofCurry.result test w z T Extra Local Tail))))
theorem resultData_rename {m l} (test : Formula 1) (w z T Y Ctx Extra Local M O Tail Middle : Fin m) (ρ : Fin m → Fin l) :
    (resultData test w z T Y Ctx Extra Local M O Tail Middle).rename ρ =
      resultData test (ρ w) (ρ z) (ρ T) (ρ Y) (ρ Ctx) (ρ Extra) (ρ Local) (ρ M) (ρ O) (ρ Tail) (ρ Middle) := by
  simp only [resultData, Formula.rename, SyntaxLogicalSyntax.binaryCode_rename,
    FormulaCodeSyntax.formulaCode_rename, InternalProofBackground.implication_rename, InternalProofCurry.result_rename]
def resultBody {m} (test : Formula 1) (w z T Y Ctx Extra Local M O : Fin m) : Formula (m+2) :=
  resultData test (old 2 w) (old 2 z) (old 2 T) (old 2 Y) (old 2 Ctx) (old 2 Extra) (old 2 Local)
    (old 2 M) (old 2 O) (slot 2 0) (slot 2 1)
def result {m} (test : Formula 1) (w z T Y Ctx Extra Local M O : Fin m) : Formula m :=
  existsMany 2 (resultBody test w z T Y Ctx Extra Local M O)
theorem result_rename {m l} (test : Formula 1) (w z T Y Ctx Extra Local M O : Fin m) (ρ : Fin m → Fin l) :
    (result test w z T Y Ctx Extra Local M O).rename ρ =
      result test (ρ w) (ρ z) (ρ T) (ρ Y) (ρ Ctx) (ρ Extra) (ρ Local) (ρ M) (ρ O) := by
  simp only [result, existsMany_rename, resultBody, resultData_rename, lift_old, lift_slot]

private structure Inputs {k m} (Γ : Context m) (test : Formula 1) (R : Source.Formula (k+2))
    (w z A1 A2 A3 f T C B S Refl Pre I j Sg mode a A Rb K Hm r s Y Extra Ctx : Fin m) (v : Fin 16 → Fin m) (Gb : Fin 5 → Fin m) (H : Fin 6 → Fin m) (U : Fin 3 → Fin m) (F : Fin 3 → Fin m) (P : Fin 3 → Fin m) (N : Fin 5 → Fin m) (D : Fin 3 → Fin m) : Prop where
  zf : ZFContext.Evidence Γ
  hb : Derives Γ (basis test R w z A1 A2 A3 f T C B S Refl Pre I j Sg mode a A Rb K Hm r s Y Extra Ctx v Gb H U F P N D)
private theorem Inputs.in_body {k m l} {Γ : Context m} {test : Formula 1} {R : Source.Formula (k+2)}
    {w z A1 A2 A3 f T C B S Refl Pre I j Sg mode a A Rb K Hm r s Y Extra Ctx : Fin m} {v : Fin 16 → Fin m} {Gb : Fin 5 → Fin m} {H : Fin 6 → Fin m} {U : Fin 3 → Fin m} {F : Fin 3 → Fin m} {P : Fin 3 → Fin m} {N : Fin 5 → Fin m} {D : Fin 3 → Fin m}
    (h : Inputs Γ test R w z A1 A2 A3 f T C B S Refl Pre I j Sg mode a A Rb K Hm r s Y Extra Ctx v Gb H U F P N D) (E : Formula (m+l)) :
    Inputs (Context.add E (raisedContext l Γ)) test R (old l w) (old l z) (old l A1) (old l A2) (old l A3) (old l f) (old l T) (old l C) (old l B) (old l S) (old l Refl) (old l Pre) (old l I) (old l j) (old l Sg) (old l mode) (old l a) (old l A) (old l Rb) (old l K) (old l Hm) (old l r) (old l s) (old l Y) (old l Extra) (old l Ctx) (fun i => old l (v i)) (fun i => old l (Gb i)) (fun i => old l (H i)) (fun i => old l (U i)) (fun i => old l (F i)) (fun i => old l (P i)) (fun i => old l (N i)) (fun i => old l (D i)) :=
  ⟨HornBinderRules.zf_body l h.zf E,
    of_eq (basis_rename test R w z A1 A2 A3 f T C B S Refl Pre I j Sg mode a A Rb K Hm r s Y Extra Ctx v Gb H U F P N D (old l)) (HornBinderRules.under_body l h.hb E)⟩

/-- The old head is bound-zero; recover actual source scope typing from
the SAME lifted opening. Neither target A nor any runtime scope is standard. -/
private theorem head_at_body {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w mode z a f T A C Rb Sg K Hm p r s Cex uHead head : Fin m)
    (hf : Derives Γ (ForcingMemberGuardOpening.frame w mode z a f T A C Rb Sg K Hm p r s))
    (hh : Derives Γ (SyntaxMixedImageHead.head w Cex f uHead head)) :
    Derives Γ (SyntaxMixedImageHead.head w A f uHead head) := by
  have hw := Derives.conjL hf
  have hLift := Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (hf)))))
  have hi := SyntaxCodedMixedBinderTyping.input_of_lifted w Rb Sg a f z T A C K Hm hLift
  have ha := Derives.conjL (Derives.conjL (Derives.conjL hi))
  have hfree := Derives.conjL (Derives.conjR (Derives.conjL hi))
  have hA := Derives.conjL (Derives.conjR hi)
  have ht := SyntaxMixedImageHead.term_at_zero hZ w a A f uHead head hw ha hfree hA (.conjL hh) (.conjL (.conjR hh))
  exact .conjI (.conjL hh) (.conjI (.conjL (.conjR hh)) ht)

private theorem at_final {k m} {Γ : Context m} (test : Formula 1) (R : Source.Formula (k+2))
    (w z A1 A2 A3 f T C B S Refl Pre I j Sg mode a A Rb K Hm r s Y Extra Ctx uHead head M O Tail Open : Fin m) (v : Fin 16 → Fin m) (Gb : Fin 5 → Fin m) (H : Fin 6 → Fin m) (U : Fin 3 → Fin m) (F : Fin 3 → Fin m) (P : Fin 3 → Fin m) (N : Fin 5 → Fin m) (D : Fin 3 → Fin m) (first final : Fin 4 → Fin m)
    (h : Inputs Γ test R w z A1 A2 A3 f T C B S Refl Pre I j Sg mode a A Rb K Hm r s Y Extra Ctx v Gb H U F P N D)
    (hh : Derives Γ (SyntaxMixedImageHead.head w A f uHead head))
    (hM : Derives Γ (ForcingGuardCode.compiled false R w A f head M))
    (hO : Derives Γ (ForcingGuardCode.compiled true R w A f head O))
    (hFirst : Derives Γ (chainData w K Hm A f C T M O Tail Open first))
    (hLast : Derives Γ (chainData w r s C T z T (first 0) (first 1) (first 2) Y final)) :
    Derives Γ (result test w z T Y Ctx Extra (Gb 0) (H 0) (H 5)) := by
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
  have hw := Derives.conjL b8
  have hz := Derives.conjL (Derives.conjR (Derives.conjR (b8)))
  have hInst := Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (b8))))))
  have hMemberInst := Derives.impE (.conjR (SyntaxTopFormulaCodes.instantiate_at_codes h.zf w z T C (P 0) (first 0) (final 0) r s hw hInst)) (Derives.conjL (Derives.conjR (Derives.conjR (hLast))))
  have hOrderInst := Derives.impE (.conjR (SyntaxTopFormulaCodes.instantiate_at_codes h.zf w z T C (P 0) (first 1) (final 1) r s hw hInst)) (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (hLast)))))
  have hMember := ForcingPreorderGuardTables.member_from_instance h.zf test R 0
    w z A1 A2 A3 f T C B S Refl Pre I j (P 2) Sg mode a A Rb K Hm r s uHead head M (first 0) (final 0)
    v Gb H U F P N D b0 b1 b3 b4 b5 b6 b7 b8 hh hM (Derives.conjL (Derives.conjR (Derives.conjR (hFirst)))) hMemberInst
  have hOrder := ForcingPreorderGuardTables.relation_from_instance h.zf test R
    w z A1 A2 A3 f T C B S Refl Pre j Sg mode a A Rb K Hm r s uHead head O (first 1) (final 1)
    v Gb H U F P N D b0 b1 b2 b3 b4 b6 b7 b8 hh hO (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (hFirst))))) hOrderInst
  have hOuter := SyntaxRenameLogicalSubst.binary_x 2 w (final 0) (final 3) Y (H 0) (eq_symm hMember) (Derives.conjL (hLast))
  have hInner := SyntaxRenameLogicalSubst.binary_x 2 w (final 1) (final 2) (final 3) (H 5) (eq_symm hOrder) (Derives.conjL (Derives.conjR (hLast)))
  have hRow := Derives.conjL (Derives.conjL (Derives.conjR b6))
  have hProofs := ForcingTransitiveGuardProof.at_background h.zf test w z T C Refl Pre Gb H U F P N hw hz hRow
  have hLocalType := Derives.conjL hRow
  have hExtraType := Derives.conjL (Derives.conjR (Derives.impE
    (.conjL (FormulaCodeKnownLogical.binary0_iff h.zf w z T Extra (Gb 0) Ctx hw b10)) b9))
  have hOuterType := Derives.impE (.conjL (FormulaCodeKnownLogical.binary2_iff h.zf w z T (H 0) (final 3) Y hw hOuter)) b11
  have hMemberType := Derives.conjL (Derives.conjR hOuterType)
  have hMiddleType := Derives.conjR (Derives.conjR hOuterType)
  have hInnerType := Derives.impE (.conjL (FormulaCodeKnownLogical.binary2_iff h.zf w z T (H 5) (final 2) (final 3) hw hInner)) hMiddleType
  have hOrderType := Derives.conjL (Derives.conjR hInnerType)
  have hTailType := Derives.conjR (Derives.conjR hInnerType)
  have pCtx := ForcingRelationGuardProof.project h.zf test true w z T Extra (Gb 0) Ctx hw hz hExtraType hLocalType b9 b10
  have pMember := ForcingRelationGuardProof.chain h.zf test w z T Ctx (Gb 0) (H 0) hw hz b9 hLocalType hMemberType pCtx (.conjL hProofs)
  have pOrder := ForcingRelationGuardProof.chain h.zf test w z T Ctx (Gb 0) (H 5) hw hz b9 hLocalType hOrderType pCtx (.conjR hProofs)
  have pMiddle := ForcingNegMemberProof.discharge h.zf test w z T Ctx (H 0) (final 3) Y hw hz b9 b11 hOuter pMember b12
  have pTail := ForcingNegMemberProof.discharge h.zf test w z T Ctx (H 5) (final 2) (final 3) hw hz b9 hMiddleType hInner pOrder pMiddle
  have hCurry := InternalProofCurry.from_implication h.zf test w z T Extra (Gb 0) Ctx (final 2)
    hw hz hExtraType hLocalType hTailType b10 pTail
  apply HornBinderRules.intro_many 2 _ (SyntaxAtomSyntax.two (final 2) (final 3))
  exact of_eq (by simp only [resultBody, resultData_rename, assign_old, assign_slot]; rfl)
    (.conjI hOuter (.conjI hInner (.conjI hTailType (.conjI pTail hCurry))))


private structure GuardInputs {k m} (Γ : Context m) (test : Formula 1) (R : Source.Formula (k+2))
    (w z A1 A2 A3 f T C B S Refl Pre I j Sg mode a A Rb K Hm r s Y Extra Ctx uHead head M O Open : Fin m) (v : Fin 16 → Fin m) (Gb : Fin 5 → Fin m) (H : Fin 6 → Fin m) (U : Fin 3 → Fin m) (F : Fin 3 → Fin m) (P : Fin 3 → Fin m) (N : Fin 5 → Fin m) (D : Fin 3 → Fin m) : Prop where
  base : Inputs Γ test R w z A1 A2 A3 f T C B S Refl Pre I j Sg mode a A Rb K Hm r s Y Extra Ctx v Gb H U F P N D
  hh : Derives Γ (SyntaxMixedImageHead.head w A f uHead head)
  hM : Derives Γ (ForcingGuardCode.compiled false R w A f head M)
  hO : Derives Γ (ForcingGuardCode.compiled true R w A f head O)
  hNative : Derives Γ (substituted w r s C T z T Open Y)
private theorem GuardInputs.in_body {k m l} {Γ : Context m} {test : Formula 1} {R : Source.Formula (k+2)}
    {w z A1 A2 A3 f T C B S Refl Pre I j Sg mode a A Rb K Hm r s Y Extra Ctx uHead head M O Open : Fin m} {v : Fin 16 → Fin m} {Gb : Fin 5 → Fin m} {H : Fin 6 → Fin m} {U : Fin 3 → Fin m} {F : Fin 3 → Fin m} {P : Fin 3 → Fin m} {N : Fin 5 → Fin m} {D : Fin 3 → Fin m}
    (h : GuardInputs Γ test R w z A1 A2 A3 f T C B S Refl Pre I j Sg mode a A Rb K Hm r s Y Extra Ctx uHead head M O Open v Gb H U F P N D) (E : Formula (m+l)) :
    GuardInputs (Context.add E (raisedContext l Γ)) test R (old l w) (old l z) (old l A1) (old l A2) (old l A3) (old l f) (old l T) (old l C) (old l B) (old l S) (old l Refl) (old l Pre) (old l I) (old l j) (old l Sg) (old l mode) (old l a) (old l A) (old l Rb) (old l K) (old l Hm) (old l r) (old l s) (old l Y) (old l Extra) (old l Ctx)
      (old l uHead) (old l head) (old l M) (old l O) (old l Open) (fun i => old l (v i)) (fun i => old l (Gb i)) (fun i => old l (H i)) (fun i => old l (U i)) (fun i => old l (F i)) (fun i => old l (P i)) (fun i => old l (N i)) (fun i => old l (D i)) := by
  exact ⟨h.base.in_body E,
    of_eq (SyntaxMixedImageHead.head_rename w A f uHead head (old l)) (HornBinderRules.under_body l h.hh E),
    of_eq (ForcingGuardCode.compiled_rename false R w A f head M (old l)) (HornBinderRules.under_body l h.hM E),
    of_eq (ForcingGuardCode.compiled_rename true R w A f head O (old l)) (HornBinderRules.under_body l h.hO E),
    of_eq (substituted_rename w r s C T z T Open Y (old l)) (HornBinderRules.under_body l h.hNative E)⟩

private theorem from_first {k m} {Γ : Context m} (test : Formula 1) (R : Source.Formula (k+2))
    (w z A1 A2 A3 f T C B S Refl Pre I j Sg mode a A Rb K Hm r s Y Extra Ctx uHead head M O Tail Open : Fin m) (v : Fin 16 → Fin m) (Gb : Fin 5 → Fin m) (H : Fin 6 → Fin m) (U : Fin 3 → Fin m) (F : Fin 3 → Fin m) (P : Fin 3 → Fin m) (N : Fin 5 → Fin m) (D : Fin 3 → Fin m) (first : Fin 4 → Fin m)
    (h : GuardInputs Γ test R w z A1 A2 A3 f T C B S Refl Pre I j Sg mode a A Rb K Hm r s Y Extra Ctx uHead head M O Open v Gb H U F P N D)
    (hFirst : Derives Γ (chainData w K Hm A f C T M O Tail Open first)) :
    Derives Γ (result test w z T Y Ctx Extra (Gb 0) (H 0) (H 5)) := by
  have hw := Derives.conjL (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (h.base.hb))))))))))
  have he := transform h.base.zf w r s C T z T (first 0) (first 1) (first 2) (first 3) Open Y
    hw (.conjL (.conjR hFirst)) (.conjL hFirst) h.hNative
  let E := chainBody w r s C T z T (first 0) (first 1) (first 2) Y
  let Δ := Context.add E (raisedContext 4 Γ)
  apply HornBinderRules.eliminate_many 4 E _ he
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have h4 := h.in_body E
  have hFirst4 := of_eq (chainData_rename w K Hm A f C T M O Tail Open first (old 4)) (HornBinderRules.under_body 4 hFirst E)
  have hout := at_final test R (old 4 w) (old 4 z) (old 4 A1) (old 4 A2) (old 4 A3) (old 4 f) (old 4 T) (old 4 C) (old 4 B) (old 4 S) (old 4 Refl) (old 4 Pre) (old 4 I) (old 4 j) (old 4 Sg) (old 4 mode) (old 4 a) (old 4 A) (old 4 Rb) (old 4 K) (old 4 Hm) (old 4 r) (old 4 s) (old 4 Y) (old 4 Extra) (old 4 Ctx)
    (old 4 uHead) (old 4 head) (old 4 M) (old 4 O) (old 4 Tail) (old 4 Open)
    (fun i => old 4 (v i)) (fun i => old 4 (Gb i)) (fun i => old 4 (H i)) (fun i => old 4 (U i)) (fun i => old 4 (F i)) (fun i => old 4 (P i)) (fun i => old 4 (N i)) (fun i => old 4 (D i))
    (fun i => old 4 (first i)) (slot 4) h4.base h4.hh h4.hM h4.hO hFirst4 hE
  exact of_eq (result_rename test w z T Y Ctx Extra (Gb 0) (H 0) (H 5) (old 4)).symm hout

private theorem from_shell_data {k m} {Γ : Context m} (test : Formula 1) (R : Source.Formula (k+2))
    (w z A1 A2 A3 f T C B S Refl Pre I j Sg mode a A Rb K Hm r s Y Extra Ctx Bex Cex uHead head M O rM rO DomainCode ChildCode Q J Open : Fin m)
    (v : Fin 16 → Fin m) (Gb : Fin 5 → Fin m) (H : Fin 6 → Fin m) (U : Fin 3 → Fin m) (F : Fin 3 → Fin m) (P : Fin 3 → Fin m) (N : Fin 5 → Fin m) (D : Fin 3 → Fin m) (shell : Fin 7 → Fin m)
    (h : GuardInputs Γ test R w z A1 A2 A3 f T C B S Refl Pre I j Sg mode a A Rb K Hm r s Y Extra Ctx uHead head M O Open v Gb H U F P N D)
    (hs : Derives Γ (ForcingExistCode.shellData w a A Bex Cex f M O rM rO DomainCode ChildCode Q shell))
    (hJ : Derives Γ (SyntaxLogicalSyntax.singleCode 9 w J Q))
    (ho : Derives Γ (substituted w K Hm A f C T J Open)) :
    Derives Γ (result test w z T Y Ctx Extra (Gb 0) (H 0) (H 5)) := by
  have hw := Derives.conjL (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (h.base.hb))))))))))
  have hAll := Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (hs))))))))
  have hInner := Derives.conjL (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (hs)))))))
  have hOuter := Derives.conjL (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (hs))))))))
  have heq := SyntaxLogicalFields.single_fields h.base.zf 9 w J (shell 6) Q hw hJ hAll
  have hOpening := SyntaxMixedFormulaJudgmentSubst.subst_n w K Hm A f C T J Open (shell 6) heq ho
  have he := transform h.base.zf w K Hm A f C T M O (shell 4) (shell 5) (shell 6) Open hw hInner hOuter hOpening
  let E := chainBody w K Hm A f C T M O (shell 4) Open
  let Δ := Context.add E (raisedContext 4 Γ)
  apply HornBinderRules.eliminate_many 4 E _ he
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have h4 := h.in_body E
  have hout := from_first test R (old 4 w) (old 4 z) (old 4 A1) (old 4 A2) (old 4 A3) (old 4 f) (old 4 T) (old 4 C) (old 4 B) (old 4 S) (old 4 Refl) (old 4 Pre) (old 4 I) (old 4 j) (old 4 Sg) (old 4 mode) (old 4 a) (old 4 A) (old 4 Rb) (old 4 K) (old 4 Hm) (old 4 r) (old 4 s) (old 4 Y) (old 4 Extra) (old 4 Ctx)
    (old 4 uHead) (old 4 head) (old 4 M) (old 4 O) (old 4 (shell 4)) (old 4 Open)
    (fun i => old 4 (v i)) (fun i => old 4 (Gb i)) (fun i => old 4 (H i)) (fun i => old 4 (U i)) (fun i => old 4 (F i)) (fun i => old 4 (P i)) (fun i => old 4 (N i)) (fun i => old 4 (D i))
    (slot 4) h4 hE
  exact of_eq (result_rename test w z T Y Ctx Extra (Gb 0) (H 0) (H 5) (old 4)).symm hout

private theorem from_shell {k m} {Γ : Context m} (test : Formula 1) (R : Source.Formula (k+2))
    (w z A1 A2 A3 f T C B S Refl Pre I j Sg mode a A Rb K Hm r s Y Extra Ctx Bex Cex uHead head M O rM rO DomainCode ChildCode Q J Open : Fin m)
    (v : Fin 16 → Fin m) (Gb : Fin 5 → Fin m) (H : Fin 6 → Fin m) (U : Fin 3 → Fin m) (F : Fin 3 → Fin m) (P : Fin 3 → Fin m) (N : Fin 5 → Fin m) (D : Fin 3 → Fin m)
    (h : GuardInputs Γ test R w z A1 A2 A3 f T C B S Refl Pre I j Sg mode a A Rb K Hm r s Y Extra Ctx uHead head M O Open v Gb H U F P N D)
    (hs : Derives Γ (existsMany 7 (ForcingExistCode.shellBody w a A Bex Cex f M O rM rO DomainCode ChildCode Q)))
    (hJ : Derives Γ (SyntaxLogicalSyntax.singleCode 9 w J Q))
    (ho : Derives Γ (substituted w K Hm A f C T J Open)) :
    Derives Γ (result test w z T Y Ctx Extra (Gb 0) (H 0) (H 5)) := by
  let E := ForcingExistCode.shellBody w a A Bex Cex f M O rM rO DomainCode ChildCode Q
  let Δ := Context.add E (raisedContext 7 Γ)
  apply HornBinderRules.eliminate_many 7 E _ hs
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have h7 := h.in_body E
  have hJ7 := of_eq (SyntaxLogicalSyntax.singleCode_rename 9 w J Q (old 7)) (HornBinderRules.under_body 7 hJ E)
  have ho7 := of_eq (substituted_rename w K Hm A f C T J Open (old 7)) (HornBinderRules.under_body 7 ho E)
  have hout := from_shell_data test R (old 7 w) (old 7 z) (old 7 A1) (old 7 A2) (old 7 A3) (old 7 f) (old 7 T) (old 7 C) (old 7 B) (old 7 S) (old 7 Refl) (old 7 Pre) (old 7 I) (old 7 j) (old 7 Sg) (old 7 mode) (old 7 a) (old 7 A) (old 7 Rb) (old 7 K) (old 7 Hm) (old 7 r) (old 7 s) (old 7 Y) (old 7 Extra) (old 7 Ctx)
    (old 7 Bex) (old 7 Cex) (old 7 uHead) (old 7 head) (old 7 M) (old 7 O) (old 7 rM) (old 7 rO) (old 7 DomainCode) (old 7 ChildCode) (old 7 Q) (old 7 J) (old 7 Open)
    (fun i => old 7 (v i)) (fun i => old 7 (Gb i)) (fun i => old 7 (H i)) (fun i => old 7 (U i)) (fun i => old 7 (F i)) (fun i => old 7 (P i)) (fun i => old 7 (N i)) (fun i => old 7 (D i))
    (slot 7) h7 hE hJ7 ho7
  exact of_eq (result_rename test w z T Y Ctx Extra (Gb 0) (H 0) (H 5) (old 7)).symm hout

private theorem from_compiled {k m} {Γ : Context m} (test : Formula 1) (R : Source.Formula (k+2))
    (Domain : Source.Formula (k+1)) (w z A1 A2 A3 f T C B S Refl Pre I j Sg mode a A Rb K Hm r s Y Extra Ctx Bex Cex n Q J Open : Fin m)
    (v : Fin 16 → Fin m) (Gb : Fin 5 → Fin m) (H : Fin 6 → Fin m) (U : Fin 3 → Fin m) (F : Fin 3 → Fin m) (P : Fin 3 → Fin m) (N : Fin 5 → Fin m) (D : Fin 3 → Fin m) (h : Inputs Γ test R w z A1 A2 A3 f T C B S Refl Pre I j Sg mode a A Rb K Hm r s Y Extra Ctx v Gb H U F P N D)
    (hc : Derives Γ (ForcingExistCode.compiled R Domain w a A Bex Cex f j n Q))
    (hJ : Derives Γ (SyntaxLogicalSyntax.singleCode 9 w J Q))
    (ho : Derives Γ (substituted w K Hm A f C T J Open))
    (hi : Derives Γ (substituted w r s C T z T Open Y)) :
    Derives Γ (result test w z T Y Ctx Extra (Gb 0) (H 0) (H 5)) := by
  let E := ForcingExistCode.body R Domain w a A Bex Cex f j n Q
  let Δ := Context.add E (raisedContext 8 Γ)
  apply HornBinderRules.eliminate_many 8 E _ (.conjR hc)
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have h8 := h.in_body E
  have hJ8 := of_eq (SyntaxLogicalSyntax.singleCode_rename 9 w J Q (old 8)) (HornBinderRules.under_body 8 hJ E)
  have ho8 := of_eq (substituted_rename w K Hm A f C T J Open (old 8)) (HornBinderRules.under_body 8 ho E)
  have hi8 := of_eq (substituted_rename w r s C T z T Open Y (old 8)) (HornBinderRules.under_body 8 hi E)
  have hFrame8 := Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (h8.hb)))))))))
  have hh8 := head_at_body h8.zf (old 8 w) (old 8 mode) (old 8 z) (old 8 a) (old 8 f) (old 8 T)
    (old 8 A) (old 8 C) (old 8 Rb) (old 8 Sg) (old 8 K) (old 8 Hm) (old 8 (P 0)) (old 8 r) (old 8 s)
    (old 8 Cex) (slot 8 0) (slot 8 1) hFrame8 (.conjL hE)
  have hGuard : GuardInputs Δ test R (old 8 w) (old 8 z) (old 8 A1) (old 8 A2) (old 8 A3) (old 8 f) (old 8 T) (old 8 C) (old 8 B) (old 8 S) (old 8 Refl) (old 8 Pre) (old 8 I) (old 8 j) (old 8 Sg) (old 8 mode) (old 8 a) (old 8 A) (old 8 Rb) (old 8 K) (old 8 Hm) (old 8 r) (old 8 s) (old 8 Y) (old 8 Extra) (old 8 Ctx)
      (slot 8 0) (slot 8 1) (slot 8 2) (slot 8 3) (old 8 Open) (fun i => old 8 (v i)) (fun i => old 8 (Gb i)) (fun i => old 8 (H i)) (fun i => old 8 (U i)) (fun i => old 8 (F i)) (fun i => old 8 (P i)) (fun i => old 8 (N i)) (fun i => old 8 (D i)) :=
    ⟨h8,hh8,.conjL (.conjR hE),.conjL (.conjR (.conjR hE)),hi8⟩
  have hout := from_shell test R (old 8 w) (old 8 z) (old 8 A1) (old 8 A2) (old 8 A3) (old 8 f) (old 8 T) (old 8 C) (old 8 B) (old 8 S) (old 8 Refl) (old 8 Pre) (old 8 I) (old 8 j) (old 8 Sg) (old 8 mode) (old 8 a) (old 8 A) (old 8 Rb) (old 8 K) (old 8 Hm) (old 8 r) (old 8 s) (old 8 Y) (old 8 Extra) (old 8 Ctx)
    (old 8 Bex) (old 8 Cex) (slot 8 0) (slot 8 1) (slot 8 2) (slot 8 3) (slot 8 4) (slot 8 5) (slot 8 6) (slot 8 7) (old 8 Q) (old 8 J) (old 8 Open)
    (fun i => old 8 (v i)) (fun i => old 8 (Gb i)) (fun i => old 8 (H i)) (fun i => old 8 (U i)) (fun i => old 8 (F i)) (fun i => old 8 (P i)) (fun i => old 8 (N i)) (fun i => old 8 (D i))
    hGuard (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (hE)))))))) hJ8 ho8
  exact of_eq (result_rename test w z T Y Ctx Extra (Gb 0) (H 0) (H 5) (old 8)).symm hout


/-- Actual COMPLETE original existential compiler, actual body opening and
native InstantiateTop. Its SAME 8+7 compiler/shell and 4+4 mixed witnesses
are eliminated internally; both guards are discharged and the SAME local
G0 is curried by existing producers. This does not prove cross-condition
invariance of the remaining existential tail or fresh forall introduction. -/
theorem derive {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (test : Formula 1) (R : Source.Formula (k+2)) (Domain : Source.Formula (k+1))
    (w z A1 A2 A3 f T C B S Refl Pre I j Sg mode a A Rb K Hm r s Y Extra Ctx Bex Cex n Q J Open : Fin m) (v : Fin 16 → Fin m) (Gb : Fin 5 → Fin m) (H : Fin 6 → Fin m) (U : Fin 3 → Fin m) (F : Fin 3 → Fin m) (P : Fin 3 → Fin m) (N : Fin 5 → Fin m) (D : Fin 3 → Fin m)
    (h1 : Derives Γ (SyntaxNumeralSyntax.numeral 1 A1))
    (h2 : Derives Γ (SyntaxNumeralSyntax.numeral 2 A2))
    (h3 : Derives Γ (SyntaxNumeralSyntax.numeral 3 A3))
    (hf : Derives Γ (SyntaxNumeralSyntax.numeral (k+2) f))
    (hj : Derives Γ (SyntaxNumeralSyntax.numeral (k+1) j))
    (hI : Derives Γ (SyntaxNumeralSyntax.numeral k I))
    (hd : Derives Γ (ForcingPreorderLeaves.data test R w z A1 A2 A3 f T C B S Refl Pre v Gb H U F P N D))
    (hr : Derives Γ (ForcingReflexiveImages.replacement w f z T S j (P 2) Sg))
    (hFrame : Derives Γ (ForcingMemberGuardOpening.frame w mode z a f T A C Rb Sg K Hm (P 0) r s))
    (hCtx : Derives Γ (FormulaCodeSyntax.formulaCode w Ctx z T))
    (hAnd : Derives Γ (SyntaxLogicalSyntax.binaryCode 0 w Extra (Gb 0) Ctx))
    (hp : Derives Γ (InternalProofBackground.implication test w z T Ctx Y))
    (hc : Derives Γ (ForcingExistCode.compiled R Domain w a A Bex Cex f j n Q))
    (hJ : Derives Γ (SyntaxLogicalSyntax.singleCode 9 w J Q))
    (ho : Derives Γ (substituted w K Hm A f C T J Open))
    (hi : Derives Γ (SyntaxTopFormulaSyntax.instantiated w z T C (P 0) Open Y)) :
    Derives Γ (result test w z T Y Ctx Extra (Gb 0) (H 0) (H 5)) := by
  have hY := SyntaxTopFormulaTyping.instantiate_target_type w z T C (P 0) Open Y hi
  have hb : Derives Γ (basis test R w z A1 A2 A3 f T C B S Refl Pre I j Sg mode a A Rb K Hm r s Y Extra Ctx v Gb H U F P N D) :=
    .conjI h1 (.conjI h2 (.conjI h3 (.conjI hf (.conjI hj (.conjI hI (.conjI hd (.conjI hr (.conjI hFrame (.conjI hCtx (.conjI hAnd (.conjI hY (hp))))))))))))
  have hw := Derives.conjL hFrame
  have hInst := Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (hFrame))))))
  have hNative := Derives.impE (.conjL (SyntaxTopFormulaCodes.instantiate_at_codes hZ w z T C (P 0) Open Y r s hw hInst)) hi
  exact from_compiled test R Domain w z A1 A2 A3 f T C B S Refl Pre I j Sg mode a A Rb K Hm r s Y Extra Ctx Bex Cex n Q J Open v Gb H U F P N D ⟨hZ,hb⟩ hc hJ ho hNative

def input {k m} (test : Formula 1) (R : Source.Formula (k+2)) (Domain : Source.Formula (k+1))
    (w z A1 A2 A3 f T C B S Refl Pre I j Sg mode a A Rb K Hm r s Y Extra Ctx Bex Cex n Q J Open : Fin m) (v : Fin 16 → Fin m) (Gb : Fin 5 → Fin m) (H : Fin 6 → Fin m) (U : Fin 3 → Fin m) (F : Fin 3 → Fin m) (P : Fin 3 → Fin m) (N : Fin 5 → Fin m) (D : Fin 3 → Fin m) : Formula m :=
  (SyntaxNumeralSyntax.numeral 1 A1).conj ((SyntaxNumeralSyntax.numeral 2 A2).conj ((SyntaxNumeralSyntax.numeral 3 A3).conj ((SyntaxNumeralSyntax.numeral (k+2) f).conj ((SyntaxNumeralSyntax.numeral (k+1) j).conj ((SyntaxNumeralSyntax.numeral k I).conj ((ForcingPreorderLeaves.data test R w z A1 A2 A3 f T C B S Refl Pre v Gb H U F P N D).conj ((ForcingReflexiveImages.replacement w f z T S j (P 2) Sg).conj ((ForcingMemberGuardOpening.frame w mode z a f T A C Rb Sg K Hm (P 0) r s).conj ((FormulaCodeSyntax.formulaCode w Ctx z T).conj ((SyntaxLogicalSyntax.binaryCode 0 w Extra (Gb 0) Ctx).conj ((InternalProofBackground.implication test w z T Ctx Y).conj ((ForcingExistCode.compiled R Domain w a A Bex Cex f j n Q).conj ((SyntaxLogicalSyntax.singleCode 9 w J Q).conj ((substituted w K Hm A f C T J Open).conj ((SyntaxTopFormulaSyntax.instantiated w z T C (P 0) Open Y))))))))))))))))
def sentence {k m} (test : Formula 1) (R : Source.Formula (k+2)) (Domain : Source.Formula (k+1))
    (w z A1 A2 A3 f T C B S Refl Pre I j Sg mode a A Rb K Hm r s Y Extra Ctx Bex Cex n Q J Open : Fin m) (v : Fin 16 → Fin m) (Gb : Fin 5 → Fin m) (H : Fin 6 → Fin m) (U : Fin 3 → Fin m) (F : Fin 3 → Fin m) (P : Fin 3 → Fin m) (N : Fin 5 → Fin m) (D : Fin 3 → Fin m) : Source.Sentence :=
  ((input test R Domain w z A1 A2 A3 f T C B S Refl Pre I j Sg mode a A Rb K Hm r s Y Extra Ctx Bex Cex n Q J Open v Gb H U F P N D).imp (result test w z T Y Ctx Extra (Gb 0) (H 0) (H 5))).close
theorem kernel_certificate {k m} (test : Formula 1) (R : Source.Formula (k+2)) (Domain : Source.Formula (k+1))
    (w z A1 A2 A3 f T C B S Refl Pre I j Sg mode a A Rb K Hm r s Y Extra Ctx Bex Cex n Q J Open : Fin m) (v : Fin 16 → Fin m) (Gb : Fin 5 → Fin m) (H : Fin 6 → Fin m) (U : Fin 3 → Fin m) (F : Fin 3 → Fin m) (P : Fin 3 → Fin m) (N : Fin 5 → Fin m) (D : Fin 3 → Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (sentence test R Domain w z A1 A2 A3 f T C B S Refl Pre I j Sg mode a A Rb K Hm r s Y Extra Ctx Bex Cex n Q J Open v Gb H U F P N D)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  let E := input test R Domain w z A1 A2 A3 f T C B S Refl Pre I j Sg mode a A Rb K Hm r s Y Extra Ctx Bex Cex n Q J Open v Gb H U F P N D
  let Γ := Context.add E (Source.SetLanguage.ZF.at m)
  have h : Derives Γ E := .hyp (Or.inl rfl)
  exact derive (ZFContext.add (ZFContext.source_ZF m) E) test R Domain w z A1 A2 A3 f T C B S Refl Pre I j Sg mode a A Rb K Hm r s Y Extra Ctx Bex Cex n Q J Open v Gb H U F P N D
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

end PPAC.Migration.ForcingPreorderExistential
