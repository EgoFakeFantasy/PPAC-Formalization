import PPAC.Migration.ForcingRelationGuardProof
import PPAC.Migration.ForcingNegCondition

/-! Original preorder transitivity: THREE carrier guards, then r≤q, q≤p.
The three original ALL/native instantiations and all literal IMP/AND codes
are data. No proof/truth of the background, guards, preorder or target is
assumed. The LOCAL background includes r; it must be curried before forall.
This is not yet uniform forcing monotonicity or final Con. -/
namespace PPAC.Migration.ForcingTransitiveGuardProof
open Internal Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)
open FormulaCodeSyntax (formulaCode formulaCode_rename)
open InternalProofBackground (implication implication_rename)
open ForcingRelationGuardProof (project chain instantiate)
set_option maxRecDepth 32768
attribute [local irreducible] NaturalRecursionSyntax.matrix

/-- H0,H1,H2 are the r/q/p carrier guards; H3=R(r,q), H4=R(q,p),
H5=R(r,p). Pre=Refl∧U0 and G0=Pre∧(H0∧(H1∧(H2∧(H3∧H4)))).
U0,U1,U2 are the three actual quantified states; N0..N4 the five IMP nodes. -/
def row {m} (w z T C Refl Pre : Fin m) (G : Fin 5 → Fin m) (H : Fin 6 → Fin m) (U F P : Fin 3 → Fin m) (N : Fin 5 → Fin m) : Formula m :=
  (formulaCode w (G 0) z T).conj ((SyntaxLogicalSyntax.binaryCode 0 w Refl (U 0) Pre).conj ((SyntaxLogicalSyntax.binaryCode 0 w (Pre) (G 1) (G 0)).conj ((SyntaxLogicalSyntax.binaryCode 0 w (H 0) (G 2) (G 1)).conj ((SyntaxLogicalSyntax.binaryCode 0 w (H 1) (G 3) (G 2)).conj ((SyntaxLogicalSyntax.binaryCode 0 w (H 2) (G 4) (G 3)).conj ((SyntaxLogicalSyntax.binaryCode 0 w (H 3) (H 4) (G 4)).conj ((SyntaxLogicalSyntax.singleCode 9 w (F 0) (U 0)).conj ((SyntaxTopFormulaSyntax.instantiated w z T C (P 0) (F 0) (U 1)).conj ((SyntaxLogicalSyntax.singleCode 9 w (F 1) (U 1)).conj ((SyntaxTopFormulaSyntax.instantiated w z T C (P 1) (F 1) (U 2)).conj ((SyntaxLogicalSyntax.singleCode 9 w (F 2) (U 2)).conj ((SyntaxTopFormulaSyntax.instantiated w z T C (P 2) (F 2) (N 0)).conj ((SyntaxLogicalSyntax.binaryCode 2 w (H 0) (N 1) (N 0)).conj ((SyntaxLogicalSyntax.binaryCode 2 w (H 1) (N 2) (N 1)).conj ((SyntaxLogicalSyntax.binaryCode 2 w (H 2) (N 3) (N 2)).conj ((SyntaxLogicalSyntax.binaryCode 2 w (H 3) (N 4) (N 3)).conj ((SyntaxLogicalSyntax.binaryCode 2 w (H 4) (H 5) (N 4)))))))))))))))))))

theorem row_rename {m l} (w z T C Refl Pre : Fin m) (G : Fin 5 → Fin m) (H : Fin 6 → Fin m) (U F P : Fin 3 → Fin m) (N : Fin 5 → Fin m) (ρ : Fin m → Fin l) :
    (row w z T C Refl Pre G H U F P N).rename ρ = row (ρ w) (ρ z) (ρ T) (ρ C) (ρ Refl) (ρ Pre) (fun i => ρ (G i)) (fun i => ρ (H i)) (fun i => ρ (U i)) (fun i => ρ (F i)) (fun i => ρ (P i)) (fun i => ρ (N i)) := by
  simp only [row, Formula.rename, formulaCode_rename, SyntaxLogicalSyntax.binaryCode_rename, SyntaxLogicalSyntax.singleCode_rename, SyntaxTopFormulaSyntax.instantiated_rename]

theorem at_background {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1)
    (w z T C Refl Pre : Fin m) (G : Fin 5 → Fin m) (H : Fin 6 → Fin m) (U F P : Fin 3 → Fin m) (N : Fin 5 → Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hr : Derives Γ (row w z T C Refl Pre G H U F P N)) :
    Derives Γ ((implication test w z T (G 0) (H 0)).conj (implication test w z T (G 0) (H 5))) := by
  have r0 := (Derives.conjL hr)
  have r1 := (Derives.conjL (Derives.conjR hr))
  have r2 := (Derives.conjL (Derives.conjR (Derives.conjR hr)))
  have r3 := (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR hr))))
  have r4 := (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hr)))))
  have r5 := (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hr))))))
  have r6 := (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hr)))))))
  have r7 := (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hr))))))))
  have r8 := (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hr)))))))))
  have r9 := (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hr))))))))))
  have r10 := (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hr)))))))))))
  have r11 := (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hr))))))))))))
  have r12 := (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hr)))))))))))))
  have r13 := (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hr))))))))))))))
  have r14 := (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hr)))))))))))))))
  have r15 := (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hr))))))))))))))))
  have r16 := (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hr)))))))))))))))))
  have r17 := (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hr)))))))))))))))))
  have hG0 := r0
  have t0 := Derives.impE (Derives.conjL (FormulaCodeKnownLogical.binary0_iff hZ w z T (Pre) (G 1) (G 0) hw r2)) hG0
  have hHead0 := Derives.conjL (Derives.conjR t0)
  have hG1 := Derives.conjR (Derives.conjR t0)
  have t1 := Derives.impE (Derives.conjL (FormulaCodeKnownLogical.binary0_iff hZ w z T (H 0) (G 2) (G 1) hw r3)) hG1
  have hHead1 := Derives.conjL (Derives.conjR t1)
  have hG2 := Derives.conjR (Derives.conjR t1)
  have t2 := Derives.impE (Derives.conjL (FormulaCodeKnownLogical.binary0_iff hZ w z T (H 1) (G 3) (G 2) hw r4)) hG2
  have hHead2 := Derives.conjL (Derives.conjR t2)
  have hG3 := Derives.conjR (Derives.conjR t2)
  have t3 := Derives.impE (Derives.conjL (FormulaCodeKnownLogical.binary0_iff hZ w z T (H 2) (G 4) (G 3) hw r5)) hG3
  have hHead3 := Derives.conjL (Derives.conjR t3)
  have hG4 := Derives.conjR (Derives.conjR t3)
  have t4 := Derives.impE (Derives.conjL (FormulaCodeKnownLogical.binary0_iff hZ w z T (H 3) (H 4) (G 4) hw r6)) hG4
  have hHead4 := Derives.conjL (Derives.conjR t4)
  have hH4 := Derives.conjR (Derives.conjR t4)
  have tp := Derives.impE (Derives.conjL (FormulaCodeKnownLogical.binary0_iff hZ w z T Refl (U 0) Pre hw r1)) hHead0
  have hRefl := Derives.conjL (Derives.conjR tp)
  have hU0 := Derives.conjR (Derives.conjR tp)
  have pPre := project hZ test false w z T Pre (G 1) (G 0) hw hz hHead0 hG1 hG0 r2
  have pU := project hZ test true w z T Refl (U 0) Pre hw hz hRefl hU0 hHead0 r1
  have p0 := chain hZ test w z T (G 0) Pre (U 0) hw hz hG0 hHead0 hU0 pPre pU
  have hQ0 := SyntaxTopFormulaTyping.instantiate_target_type w z T C (P 0) (F 0) (U 1) r8
  have p1 := instantiate hZ test w z T C (F 0) (P 0) (U 1) (U 0) (G 0) hw hz hG0 hQ0 r8 r7 p0
  have hQ1 := SyntaxTopFormulaTyping.instantiate_target_type w z T C (P 1) (F 1) (U 2) r10
  have p2 := instantiate hZ test w z T C (F 1) (P 1) (U 2) (U 1) (G 0) hw hz hG0 hQ1 r10 r9 p1
  have hQ2 := SyntaxTopFormulaTyping.instantiate_target_type w z T C (P 2) (F 2) (N 0) r12
  have p3 := instantiate hZ test w z T C (F 2) (P 2) (N 0) (U 2) (G 0) hw hz hG0 hQ2 r12 r11 p2
  have d1 := project hZ test true w z T Pre (G 1) (G 0) hw hz hHead0 hG1 hG0 r2
  have l1 := project hZ test false w z T (H 0) (G 2) (G 1) hw hz hHead1 hG2 hG1 r3
  have e0 := chain hZ test w z T (G 0) (G 1) (H 0) hw hz hG0 hG1 hHead1 d1 l1
  have q1 := project hZ test true w z T (H 0) (G 2) (G 1) hw hz hHead1 hG2 hG1 r3
  have d2 := chain hZ test w z T (G 0) (G 1) (G 2) hw hz hG0 hG1 hG2 d1 q1
  have l2 := project hZ test false w z T (H 1) (G 3) (G 2) hw hz hHead2 hG3 hG2 r4
  have e1 := chain hZ test w z T (G 0) (G 2) (H 1) hw hz hG0 hG2 hHead2 d2 l2
  have q2 := project hZ test true w z T (H 1) (G 3) (G 2) hw hz hHead2 hG3 hG2 r4
  have d3 := chain hZ test w z T (G 0) (G 2) (G 3) hw hz hG0 hG2 hG3 d2 q2
  have l3 := project hZ test false w z T (H 2) (G 4) (G 3) hw hz hHead3 hG4 hG3 r5
  have e2 := chain hZ test w z T (G 0) (G 3) (H 2) hw hz hG0 hG3 hHead3 d3 l3
  have q3 := project hZ test true w z T (H 2) (G 4) (G 3) hw hz hHead3 hG4 hG3 r5
  have d4 := chain hZ test w z T (G 0) (G 3) (G 4) hw hz hG0 hG3 hG4 d3 q3
  have l4 := project hZ test false w z T (H 3) (H 4) (G 4) hw hz hHead4 hH4 hG4 r6
  have e3 := chain hZ test w z T (G 0) (G 4) (H 3) hw hz hG0 hG4 hHead4 d4 l4
  have q4 := project hZ test true w z T (H 3) (H 4) (G 4) hw hz hHead4 hH4 hG4 r6
  have e4 := chain hZ test w z T (G 0) (G 4) (H 4) hw hz hG0 hG4 hH4 d4 q4
  have hn0 := hQ2
  have tN0 := Derives.impE (Derives.conjL (FormulaCodeKnownLogical.binary2_iff hZ w z T (H 0) (N 1) (N 0) hw r13)) hn0
  have hn1 := Derives.conjR (Derives.conjR tN0)
  have b0 := ForcingNegMemberProof.discharge hZ test w z T (G 0) (H 0) (N 1) (N 0) hw hz hG0 hn0 r13 e0 p3
  have tN1 := Derives.impE (Derives.conjL (FormulaCodeKnownLogical.binary2_iff hZ w z T (H 1) (N 2) (N 1) hw r14)) hn1
  have hn2 := Derives.conjR (Derives.conjR tN1)
  have b1 := ForcingNegMemberProof.discharge hZ test w z T (G 0) (H 1) (N 2) (N 1) hw hz hG0 hn1 r14 e1 b0
  have tN2 := Derives.impE (Derives.conjL (FormulaCodeKnownLogical.binary2_iff hZ w z T (H 2) (N 3) (N 2) hw r15)) hn2
  have hn3 := Derives.conjR (Derives.conjR tN2)
  have b2 := ForcingNegMemberProof.discharge hZ test w z T (G 0) (H 2) (N 3) (N 2) hw hz hG0 hn2 r15 e2 b1
  have tN3 := Derives.impE (Derives.conjL (FormulaCodeKnownLogical.binary2_iff hZ w z T (H 3) (N 4) (N 3) hw r16)) hn3
  have hn4 := Derives.conjR (Derives.conjR tN3)
  have b3 := ForcingNegMemberProof.discharge hZ test w z T (G 0) (H 3) (N 4) (N 3) hw hz hG0 hn3 r16 e3 b2
  have b4 := ForcingNegMemberProof.discharge hZ test w z T (G 0) (H 4) (H 5) (N 4) hw hz hG0 hn4 r17 e4 b3
  exact .conjI e0 b4

def negativeResult {m} (test : Formula 1) (w z T G D Bottom Rest : Fin m) : Formula m :=
  (SyntaxLogicalSyntax.binaryCode 2 w D Bottom Rest).conj
    ((SyntaxAtomSyntax.zeroScalar w Bottom).conj (implication test w z T G Rest))

theorem negativeResult_rename {m l} (test : Formula 1) (w z T G D Bottom Rest : Fin m) (ρ : Fin m → Fin l) :
    (negativeResult test w z T G D Bottom Rest).rename ρ = negativeResult test (ρ w) (ρ z) (ρ T) (ρ G) (ρ D) (ρ Bottom) (ρ Rest) := by
  simp only [negativeResult, Formula.rename, SyntaxLogicalSyntax.binaryCode_rename, SyntaxAtomSyntax.zeroScalar_rename, implication_rename]

theorem at_negative {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1)
    (w z T C Refl Pre D Bottom Rest I Y : Fin m) (G : Fin 5 → Fin m) (H : Fin 6 → Fin m) (U F P : Fin 3 → Fin m) (N : Fin 5 → Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hr : Derives Γ (row w z T C Refl Pre G H U F P N))
    (hY : Derives Γ (formulaCode w Y z T))
    (hOuter : Derives Γ (SyntaxLogicalSyntax.binaryCode 2 w (H 0) I Y))
    (hOrder : Derives Γ (SyntaxLogicalSyntax.binaryCode 2 w (H 5) Rest I))
    (hRest : Derives Γ (SyntaxLogicalSyntax.binaryCode 2 w D Bottom Rest))
    (hBottom : Derives Γ (SyntaxAtomSyntax.zeroScalar w Bottom))
    (hp : Derives Γ (implication test w z T (G 0) Y)) :
    Derives Γ (negativeResult test w z T (G 0) D Bottom Rest) := by
  have hs := at_background hZ test w z T C Refl Pre G H U F P N hw hz hr
  have hG := Derives.conjL hr
  have hI := Derives.conjR (Derives.conjR (Derives.impE (Derives.conjL (FormulaCodeKnownLogical.binary2_iff hZ w z T (H 0) I Y hw hOuter)) hY))
  have hm := ForcingNegMemberProof.discharge hZ test w z T (G 0) (H 0) I Y hw hz hG hY hOuter (.conjL hs) hp
  have hOut := ForcingNegMemberProof.discharge hZ test w z T (G 0) (H 5) Rest I hw hz hG hI hOrder (.conjR hs) hm
  exact .conjI hRest (.conjI hBottom hOut)

def input {m} (w z T C Refl Pre : Fin m) (G : Fin 5 → Fin m) (H : Fin 6 → Fin m) (U F P : Fin 3 → Fin m) (N : Fin 5 → Fin m) : Formula m :=
  (omega w).conj ((empty z).conj (row w z T C Refl Pre G H U F P N))

def sentence {m} (target : Bool) (w z T C Refl Pre : Fin m) (G : Fin 5 → Fin m) (H : Fin 6 → Fin m) (U F P : Fin 3 → Fin m) (N : Fin 5 → Fin m) : Source.Sentence :=
  ((input w z T C Refl Pre G H U F P N).imp ((implication (OriginalAxiomCodeTest.test target) w z T (G 0) (H 0)).conj (implication (OriginalAxiomCodeTest.test target) w z T (G 0) (H 5)))).close

theorem kernel_certificate {m} (target : Bool) (w z T C Refl Pre : Fin m) (G : Fin 5 → Fin m) (H : Fin 6 → Fin m) (U F P : Fin 3 → Fin m) (N : Fin 5 → Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (sentence target w z T C Refl Pre G H U F P N)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  let E := input w z T C Refl Pre G H U F P N
  let Γ := Context.add E (Source.SetLanguage.ZF.at m)
  have h : Derives Γ E := .hyp (Or.inl rfl)
  exact at_background (ZFContext.add (ZFContext.source_ZF m) E) (OriginalAxiomCodeTest.test target) w z T C Refl Pre G H U F P N (.conjL h) (.conjL (.conjR h)) (.conjR (.conjR h))

def negativeInput {m} (test : Formula 1) (w z T C Refl Pre D Bottom Rest I Y : Fin m) (G : Fin 5 → Fin m) (H : Fin 6 → Fin m) (U F P : Fin 3 → Fin m) (N : Fin 5 → Fin m) : Formula m :=
  (input w z T C Refl Pre G H U F P N).conj ((formulaCode w Y z T).conj ((SyntaxLogicalSyntax.binaryCode 2 w (H 0) I Y).conj ((SyntaxLogicalSyntax.binaryCode 2 w (H 5) Rest I).conj ((SyntaxLogicalSyntax.binaryCode 2 w D Bottom Rest).conj ((SyntaxAtomSyntax.zeroScalar w Bottom).conj ((implication test w z T (G 0) Y)))))))

def negativeSentence {m} (target : Bool) (w z T C Refl Pre D Bottom Rest I Y : Fin m) (G : Fin 5 → Fin m) (H : Fin 6 → Fin m) (U F P : Fin 3 → Fin m) (N : Fin 5 → Fin m) : Source.Sentence :=
  ((negativeInput (OriginalAxiomCodeTest.test target) w z T C Refl Pre D Bottom Rest I Y G H U F P N).imp (negativeResult (OriginalAxiomCodeTest.test target) w z T (G 0) D Bottom Rest)).close

theorem negative_kernel_certificate {m} (target : Bool) (w z T C Refl Pre D Bottom Rest I Y : Fin m) (G : Fin 5 → Fin m) (H : Fin 6 → Fin m) (U F P : Fin 3 → Fin m) (N : Fin 5 → Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (negativeSentence target w z T C Refl Pre D Bottom Rest I Y G H U F P N)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  let E := negativeInput (OriginalAxiomCodeTest.test target) w z T C Refl Pre D Bottom Rest I Y G H U F P N
  let Γ := Context.add E (Source.SetLanguage.ZF.at m)
  have h : Derives Γ E := .hyp (Or.inl rfl)
  have hBase := Derives.conjL h
  exact at_negative (ZFContext.add (ZFContext.source_ZF m) E) (OriginalAxiomCodeTest.test target) w z T C Refl Pre D Bottom Rest I Y G H U F P N
    (.conjL hBase) (.conjL (.conjR hBase)) (.conjR (.conjR hBase))
    (.conjL (.conjR h))
    (.conjL (.conjR (.conjR h)))
    (.conjL (.conjR (.conjR (.conjR h))))
    (.conjL (.conjR (.conjR (.conjR (.conjR h)))))
    (.conjL (.conjR (.conjR (.conjR (.conjR (.conjR h))))))
    (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR h))))))

/-- Keep ANY additional fixed source/system/proof background Extra. The actual
local conjunction Ctx=Extra AND G0 is used for both the parent and both guards.
No context-projection proof or desired guard proof is supplied. Ctx still has
local antecedents and must be curried before forall introduction. -/
theorem at_negative_under {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1)
    (w z T C Refl Pre Extra Ctx D Bottom Rest I Y : Fin m) (G : Fin 5 → Fin m) (H : Fin 6 → Fin m) (U F P : Fin 3 → Fin m) (N : Fin 5 → Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hr : Derives Γ (row w z T C Refl Pre G H U F P N))
    (hCtx : Derives Γ (formulaCode w Ctx z T))
    (hConj : Derives Γ (SyntaxLogicalSyntax.binaryCode 0 w Extra (G 0) Ctx))
    (hY : Derives Γ (formulaCode w Y z T))
    (hOuter : Derives Γ (SyntaxLogicalSyntax.binaryCode 2 w (H 0) I Y))
    (hOrder : Derives Γ (SyntaxLogicalSyntax.binaryCode 2 w (H 5) Rest I))
    (hRest : Derives Γ (SyntaxLogicalSyntax.binaryCode 2 w D Bottom Rest))
    (hBottom : Derives Γ (SyntaxAtomSyntax.zeroScalar w Bottom))
    (hp : Derives Γ (implication test w z T Ctx Y)) :
    Derives Γ (negativeResult test w z T Ctx D Bottom Rest) := by
  have hs := at_background hZ test w z T C Refl Pre G H U F P N hw hz hr
  have hG := Derives.conjL hr
  have hExtra := Derives.conjL (Derives.conjR (Derives.impE (Derives.conjL (FormulaCodeKnownLogical.binary0_iff hZ w z T Extra (G 0) Ctx hw hConj)) hCtx))
  have pCtx := project hZ test true w z T Extra (G 0) Ctx hw hz hExtra hG hCtx hConj
  have hH0 := Derives.conjL (Derives.conjR (Derives.impE (Derives.conjL (FormulaCodeKnownLogical.binary2_iff hZ w z T (H 0) I Y hw hOuter)) hY))
  have hI := Derives.conjR (Derives.conjR (Derives.impE (Derives.conjL (FormulaCodeKnownLogical.binary2_iff hZ w z T (H 0) I Y hw hOuter)) hY))
  have hH5 := Derives.conjL (Derives.conjR (Derives.impE (Derives.conjL (FormulaCodeKnownLogical.binary2_iff hZ w z T (H 5) Rest I hw hOrder)) hI))
  have pMember := chain hZ test w z T Ctx (G 0) (H 0) hw hz hCtx hG hH0 pCtx (.conjL hs)
  have pOrder := chain hZ test w z T Ctx (G 0) (H 5) hw hz hCtx hG hH5 pCtx (.conjR hs)
  have hm := ForcingNegMemberProof.discharge hZ test w z T Ctx (H 0) I Y hw hz hCtx hY hOuter pMember hp
  have hout := ForcingNegMemberProof.discharge hZ test w z T Ctx (H 5) Rest I hw hz hCtx hI hOrder pOrder hm
  exact .conjI hRest (.conjI hBottom hout)

def ambientInput {m} (test : Formula 1) (w z T C Refl Pre Extra Ctx D Bottom Rest I Y : Fin m) (G : Fin 5 → Fin m) (H : Fin 6 → Fin m) (U F P : Fin 3 → Fin m) (N : Fin 5 → Fin m) : Formula m :=
  (input w z T C Refl Pre G H U F P N).conj ((formulaCode w Ctx z T).conj ((SyntaxLogicalSyntax.binaryCode 0 w Extra (G 0) Ctx).conj ((formulaCode w Y z T).conj ((SyntaxLogicalSyntax.binaryCode 2 w (H 0) I Y).conj ((SyntaxLogicalSyntax.binaryCode 2 w (H 5) Rest I).conj ((SyntaxLogicalSyntax.binaryCode 2 w D Bottom Rest).conj ((SyntaxAtomSyntax.zeroScalar w Bottom).conj ((implication test w z T Ctx Y)))))))))

def ambientSentence {m} (target : Bool) (w z T C Refl Pre Extra Ctx D Bottom Rest I Y : Fin m) (G : Fin 5 → Fin m) (H : Fin 6 → Fin m) (U F P : Fin 3 → Fin m) (N : Fin 5 → Fin m) : Source.Sentence :=
  ((ambientInput (OriginalAxiomCodeTest.test target) w z T C Refl Pre Extra Ctx D Bottom Rest I Y G H U F P N).imp (negativeResult (OriginalAxiomCodeTest.test target) w z T Ctx D Bottom Rest)).close

theorem ambient_kernel_certificate {m} (target : Bool) (w z T C Refl Pre Extra Ctx D Bottom Rest I Y : Fin m) (G : Fin 5 → Fin m) (H : Fin 6 → Fin m) (U F P : Fin 3 → Fin m) (N : Fin 5 → Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (ambientSentence target w z T C Refl Pre Extra Ctx D Bottom Rest I Y G H U F P N)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  let E := ambientInput (OriginalAxiomCodeTest.test target) w z T C Refl Pre Extra Ctx D Bottom Rest I Y G H U F P N
  let Γ := Context.add E (Source.SetLanguage.ZF.at m)
  have h : Derives Γ E := .hyp (Or.inl rfl)
  have hBase := Derives.conjL h
  exact at_negative_under (ZFContext.add (ZFContext.source_ZF m) E) (OriginalAxiomCodeTest.test target) w z T C Refl Pre Extra Ctx D Bottom Rest I Y G H U F P N
    (.conjL hBase) (.conjL (.conjR hBase)) (.conjR (.conjR hBase))
    (.conjL (.conjR h))
    (.conjL (.conjR (.conjR h)))
    (.conjL (.conjR (.conjR (.conjR h))))
    (.conjL (.conjR (.conjR (.conjR (.conjR h)))))
    (.conjL (.conjR (.conjR (.conjR (.conjR (.conjR h))))))
    (.conjL (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR h)))))))
    (.conjL (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR h))))))))
    (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR h))))))))

end PPAC.Migration.ForcingTransitiveGuardProof
