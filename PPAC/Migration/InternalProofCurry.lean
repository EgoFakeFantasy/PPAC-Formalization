import PPAC.Migration.InternalProofImplication
import PPAC.Migration.InternalProofBackground
import PPAC.Migration.ForcingTransitiveGuardProof

/-! Original K/S/AND11 proof production discharges a LOCAL conjunction.
All intermediate formula codes and proof witnesses are constructed internally.
No G/A/D truth, desired output code or desired proof is supplied. -/
namespace PPAC.Migration.InternalProofCurry
open Internal Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)
open FormulaCodeSyntax (formulaCode formulaCode_rename)
open InternalProofConjunction (proved proved_rename)
open InternalProofBackground (implication implication_rename)
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000
attribute [local irreducible] NaturalRecursionSyntax.matrix

def data {m} (w G A C D I : Fin m) (v : Fin 6 → Fin m) : Formula m :=
  (SyntaxLogicalSyntax.binaryCode 2 w (A) (C) (v 0)).conj ((SyntaxLogicalSyntax.binaryCode 2 w (A) (D) (v 1)).conj ((SyntaxLogicalSyntax.binaryCode 2 w (A) (I) (v 2)).conj ((SyntaxLogicalSyntax.binaryCode 2 w (v 0) (v 1) (v 3)).conj ((SyntaxLogicalSyntax.binaryCode 2 w (G) (v 0) (v 4)).conj ((SyntaxLogicalSyntax.binaryCode 2 w (G) (v 1) (v 5)))))))

theorem data_rename {m l} (w G A C D I : Fin m) (v : Fin 6 → Fin m) (ρ : Fin m → Fin l) :
    (data w G A C D I v).rename ρ = data (ρ w) (ρ G) (ρ A) (ρ C) (ρ D) (ρ I) (fun i => ρ (v i)) := by
  simp only [data, Formula.rename, SyntaxLogicalSyntax.binaryCode_rename]

theorem at_codes {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1)
    (w z b G A C D I : Fin m) (v : Fin 6 → Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hG : Derives Γ (formulaCode w G z b)) (hA : Derives Γ (formulaCode w A z b))
    (hD : Derives Γ (formulaCode w D z b))
    (hC : Derives Γ (SyntaxLogicalSyntax.binaryCode 0 w G A C))
    (hI : Derives Γ (SyntaxLogicalSyntax.binaryCode 2 w C D I))
    (hp : Derives Γ (proved test w z b I))
    (hc : Derives Γ (data w G A C D I v)) : Derives Γ (proved test w z b (v 5)) := by
  have c0 := (Derives.conjL hc)
  have c1 := (Derives.conjL (Derives.conjR hc))
  have c2 := (Derives.conjL (Derives.conjR (Derives.conjR hc)))
  have c3 := (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR hc))))
  have c4 := (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hc)))))
  have c5 := (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hc)))))
  have hCt := Derives.impE (.conjR (FormulaCodeKnownLogical.binary0_iff hZ w z b G A C hw hC)) (.conjI (.conjR (FormulaCodeProperties.guards w G z b hG)) (.conjI hG hA))
  have hIt := Derives.impE (.conjR (FormulaCodeKnownLogical.binary2_iff hZ w z b C D I hw hI)) (.conjI (.conjR (FormulaCodeProperties.guards w C z b hCt)) (.conjI hCt hD))
  have ht0 := Derives.impE (.conjR (FormulaCodeKnownLogical.binary2_iff hZ w z b A C (v 0) hw c0)) (.conjI (.conjR (FormulaCodeProperties.guards w A z b hA)) (.conjI hA hCt))
  have ht1 := Derives.impE (.conjR (FormulaCodeKnownLogical.binary2_iff hZ w z b A D (v 1) hw c1)) (.conjI (.conjR (FormulaCodeProperties.guards w A z b hA)) (.conjI hA hD))
  have pK := InternalProofImplication.weaken_proof hZ test w z b A I (v 2) hw hz hA hIt c2 hp
  have pS := InternalProofImplication.map_from_left hZ test w z b A C D (v 0) I (v 1) (v 2) (v 3) hw hz hA hCt hD c0 hI c1 c2 c3 pK
  have pAnd := InternalProofConjunction.conjunction_axiom hZ test w z b G A C (v 0) (v 4) hw hz hG hA hC c0 c4
  exact InternalProofImplication.compose hZ test w z b G (v 0) (v 1) (v 4) (v 3) (v 5) hw hz hG ht0 ht1 c4 c3 c5 pAnd pS

def result {m} (test : Formula 1) (w z b G A D : Fin m) : Formula m := .ex
  ((SyntaxLogicalSyntax.binaryCode 2 w.castSucc A.castSucc D.castSucc (Fin.last m)).conj
    (implication test w.castSucc z.castSucc b.castSucc G.castSucc (Fin.last m)))

theorem result_rename {m l} (test : Formula 1) (w z b G A D : Fin m) (ρ : Fin m → Fin l) :
    (result test w z b G A D).rename ρ = result test (ρ w) (ρ z) (ρ b) (ρ G) (ρ A) (ρ D) := by
  simp only [result, Formula.rename, SyntaxLogicalSyntax.binaryCode_rename, implication_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem produce {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1)
    (w z b G A C D I : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hG : Derives Γ (formulaCode w G z b)) (hA : Derives Γ (formulaCode w A z b))
    (hD : Derives Γ (formulaCode w D z b))
    (hC : Derives Γ (SyntaxLogicalSyntax.binaryCode 0 w G A C))
    (hI : Derives Γ (SyntaxLogicalSyntax.binaryCode 2 w C D I))
    (hp : Derives Γ (proved test w z b I)) : Derives Γ (result test w z b G A D) := by
  have hCt := Derives.impE (.conjR (FormulaCodeKnownLogical.binary0_iff hZ w z b G A C hw hC)) (.conjI (.conjR (FormulaCodeProperties.guards w G z b hG)) (.conjI hG hA))
  have hIt := Derives.impE (.conjR (FormulaCodeKnownLogical.binary2_iff hZ w z b C D I hw hI)) (.conjI (.conjR (FormulaCodeProperties.guards w C z b hCt)) (.conjI hCt hD))
  have nG := Derives.conjL (FormulaCodeProperties.guards w G z b hG)
  have nA := Derives.conjL (FormulaCodeProperties.guards w A z b hA)
  have nC := Derives.conjL (FormulaCodeProperties.guards w C z b hCt)
  have nD := Derives.conjL (FormulaCodeProperties.guards w D z b hD)
  have nI := Derives.conjL (FormulaCodeProperties.guards w I z b hIt)
  let Δ0 : Context m := Γ
  let E0 : Formula (m+1) := (Formula.mem (slot 1 0) (old 1 w)).conj (SyntaxNodeSyntax.constructor 2 7 (old 1 w) (SyntaxAtomSyntax.two (old 1 A) (old 1 C)) (slot 1 0))
  let Δ1 : Context (m+1) := Context.add E0 (Context.image Formula.raise Δ0)
  have hw0 : Derives Δ0 (omega (old 0 w)) := of_eq (by rfl) hw
  have nL0 : Derives Δ0 (.mem (old 0 A) (old 0 w)) := of_eq (by rfl) nA
  have nR0 : Derives Δ0 (.mem (old 0 C) (old 0 w)) := of_eq (by rfl) nC
  apply Derives.exE (p := E0) (SyntaxConstructors.exists_constructor hZ 2 7 (old 0 w) (SyntaxAtomSyntax.two (old 0 A) (old 0 C)) hw0 (.conjI nL0 (.conjI nR0 (.eqRefl (old 0 w)))))
  have hE0 : Derives Δ1 E0 := .hyp (Or.inl rfl)
  let E1 : Formula (m+2) := (Formula.mem (slot 2 1) (old 2 w)).conj (SyntaxNodeSyntax.constructor 2 7 (old 2 w) (SyntaxAtomSyntax.two (old 2 A) (old 2 D)) (slot 2 1))
  let Δ2 : Context (m+2) := Context.add E1 (Context.image Formula.raise Δ1)
  have hw1 : Derives Δ1 (omega (old 1 w)) := of_eq (by simp only [Formula.raise, omega_rename] <;> rfl) (under hw E0)
  have nL1 : Derives Δ1 (.mem (old 1 A) (old 1 w)) := of_eq (by rfl) (under nA E0)
  have nR1 : Derives Δ1 (.mem (old 1 D) (old 1 w)) := of_eq (by rfl) (under nD E0)
  apply Derives.exE (p := E1) (SyntaxConstructors.exists_constructor (ZFContext.under hZ E0) 2 7 (old 1 w) (SyntaxAtomSyntax.two (old 1 A) (old 1 D)) hw1 (.conjI nL1 (.conjI nR1 (.eqRefl (old 1 w)))))
  have hE1 : Derives Δ2 E1 := .hyp (Or.inl rfl)
  let E2 : Formula (m+3) := (Formula.mem (slot 3 2) (old 3 w)).conj (SyntaxNodeSyntax.constructor 2 7 (old 3 w) (SyntaxAtomSyntax.two (old 3 A) (old 3 I)) (slot 3 2))
  let Δ3 : Context (m+3) := Context.add E2 (Context.image Formula.raise Δ2)
  have hw2 : Derives Δ2 (omega (old 2 w)) := of_eq (by simp only [Formula.raise, omega_rename] <;> rfl) (under (under hw E0) E1)
  have nL2 : Derives Δ2 (.mem (old 2 A) (old 2 w)) := of_eq (by rfl) (under (under nA E0) E1)
  have nR2 : Derives Δ2 (.mem (old 2 I) (old 2 w)) := of_eq (by rfl) (under (under nI E0) E1)
  apply Derives.exE (p := E2) (SyntaxConstructors.exists_constructor (ZFContext.under (ZFContext.under hZ E0) E1) 2 7 (old 2 w) (SyntaxAtomSyntax.two (old 2 A) (old 2 I)) hw2 (.conjI nL2 (.conjI nR2 (.eqRefl (old 2 w)))))
  have hE2 : Derives Δ3 E2 := .hyp (Or.inl rfl)
  let E3 : Formula (m+4) := (Formula.mem (slot 4 3) (old 4 w)).conj (SyntaxNodeSyntax.constructor 2 7 (old 4 w) (SyntaxAtomSyntax.two (slot 4 0) (slot 4 1)) (slot 4 3))
  let Δ4 : Context (m+4) := Context.add E3 (Context.image Formula.raise Δ3)
  have hw3 : Derives Δ3 (omega (old 3 w)) := of_eq (by simp only [Formula.raise, omega_rename] <;> rfl) (under (under (under hw E0) E1) E2)
  have nL3 : Derives Δ3 (.mem (slot 3 0) (old 3 w)) := of_eq (by rfl) (Derives.conjL (under (under hE0 E1) E2))
  have nR3 : Derives Δ3 (.mem (slot 3 1) (old 3 w)) := of_eq (by rfl) (Derives.conjL (under hE1 E2))
  apply Derives.exE (p := E3) (SyntaxConstructors.exists_constructor (ZFContext.under (ZFContext.under (ZFContext.under hZ E0) E1) E2) 2 7 (old 3 w) (SyntaxAtomSyntax.two (slot 3 0) (slot 3 1)) hw3 (.conjI nL3 (.conjI nR3 (.eqRefl (old 3 w)))))
  have hE3 : Derives Δ4 E3 := .hyp (Or.inl rfl)
  let E4 : Formula (m+5) := (Formula.mem (slot 5 4) (old 5 w)).conj (SyntaxNodeSyntax.constructor 2 7 (old 5 w) (SyntaxAtomSyntax.two (old 5 G) (slot 5 0)) (slot 5 4))
  let Δ5 : Context (m+5) := Context.add E4 (Context.image Formula.raise Δ4)
  have hw4 : Derives Δ4 (omega (old 4 w)) := of_eq (by simp only [Formula.raise, omega_rename] <;> rfl) (under (under (under (under hw E0) E1) E2) E3)
  have nL4 : Derives Δ4 (.mem (old 4 G) (old 4 w)) := of_eq (by rfl) (under (under (under (under nG E0) E1) E2) E3)
  have nR4 : Derives Δ4 (.mem (slot 4 0) (old 4 w)) := of_eq (by rfl) (Derives.conjL (under (under (under hE0 E1) E2) E3))
  apply Derives.exE (p := E4) (SyntaxConstructors.exists_constructor (ZFContext.under (ZFContext.under (ZFContext.under (ZFContext.under hZ E0) E1) E2) E3) 2 7 (old 4 w) (SyntaxAtomSyntax.two (old 4 G) (slot 4 0)) hw4 (.conjI nL4 (.conjI nR4 (.eqRefl (old 4 w)))))
  have hE4 : Derives Δ5 E4 := .hyp (Or.inl rfl)
  let E5 : Formula (m+6) := (Formula.mem (slot 6 5) (old 6 w)).conj (SyntaxNodeSyntax.constructor 2 7 (old 6 w) (SyntaxAtomSyntax.two (old 6 G) (slot 6 1)) (slot 6 5))
  let Δ6 : Context (m+6) := Context.add E5 (Context.image Formula.raise Δ5)
  have hw5 : Derives Δ5 (omega (old 5 w)) := of_eq (by simp only [Formula.raise, omega_rename] <;> rfl) (under (under (under (under (under hw E0) E1) E2) E3) E4)
  have nL5 : Derives Δ5 (.mem (old 5 G) (old 5 w)) := of_eq (by rfl) (under (under (under (under (under nG E0) E1) E2) E3) E4)
  have nR5 : Derives Δ5 (.mem (slot 5 1) (old 5 w)) := of_eq (by rfl) (Derives.conjL (under (under (under hE1 E2) E3) E4))
  apply Derives.exE (p := E5) (SyntaxConstructors.exists_constructor (ZFContext.under (ZFContext.under (ZFContext.under (ZFContext.under (ZFContext.under hZ E0) E1) E2) E3) E4) 2 7 (old 5 w) (SyntaxAtomSyntax.two (old 5 G) (slot 5 1)) hw5 (.conjI nL5 (.conjI nR5 (.eqRefl (old 5 w)))))
  have hE5 : Derives Δ6 E5 := .hyp (Or.inl rfl)
  have hw6 : Derives Δ6 (omega (old 6 w)) := of_eq (by simp only [Formula.raise, omega_rename] <;> rfl) (under (under (under (under (under (under hw E0) E1) E2) E3) E4) E5)
  have hz6 : Derives Δ6 (empty (old 6 z)) := of_eq (by simp only [Formula.raise, empty_rename] <;> rfl) (under (under (under (under (under (under hz E0) E1) E2) E3) E4) E5)
  have hG6 : Derives Δ6 (formulaCode (old 6 w) (old 6 G) (old 6 z) (old 6 b)) := of_eq (by simp only [Formula.raise, formulaCode_rename] <;> rfl) (under (under (under (under (under (under hG E0) E1) E2) E3) E4) E5)
  have hA6 : Derives Δ6 (formulaCode (old 6 w) (old 6 A) (old 6 z) (old 6 b)) := of_eq (by simp only [Formula.raise, formulaCode_rename] <;> rfl) (under (under (under (under (under (under hA E0) E1) E2) E3) E4) E5)
  have hD6 : Derives Δ6 (formulaCode (old 6 w) (old 6 D) (old 6 z) (old 6 b)) := of_eq (by simp only [Formula.raise, formulaCode_rename] <;> rfl) (under (under (under (under (under (under hD E0) E1) E2) E3) E4) E5)
  have hC6 : Derives Δ6 (SyntaxLogicalSyntax.binaryCode 0 (old 6 w) (old 6 G) (old 6 A) (old 6 C)) := of_eq (by simp only [Formula.raise, SyntaxLogicalSyntax.binaryCode_rename] <;> rfl) (under (under (under (under (under (under hC E0) E1) E2) E3) E4) E5)
  have hI6 : Derives Δ6 (SyntaxLogicalSyntax.binaryCode 2 (old 6 w) (old 6 C) (old 6 D) (old 6 I)) := of_eq (by simp only [Formula.raise, SyntaxLogicalSyntax.binaryCode_rename] <;> rfl) (under (under (under (under (under (under hI E0) E1) E2) E3) E4) E5)
  have hp6 : Derives Δ6 (proved test (old 6 w) (old 6 z) (old 6 b) (old 6 I)) := of_eq (by simp only [Formula.raise, proved_rename] <;> rfl) (under (under (under (under (under (under hp E0) E1) E2) E3) E4) E5)
  have c0 : Derives Δ6 (SyntaxLogicalSyntax.binaryCode 2 (old 6 w) (old 6 A) (old 6 C) (slot 6 0)) := of_eq (by simp only [SyntaxNodeSyntax.constructor_rename, SyntaxAtomSyntax.two_map] <;> rfl) (Derives.conjR (under (under (under (under (under hE0 E1) E2) E3) E4) E5))
  have c1 : Derives Δ6 (SyntaxLogicalSyntax.binaryCode 2 (old 6 w) (old 6 A) (old 6 D) (slot 6 1)) := of_eq (by simp only [SyntaxNodeSyntax.constructor_rename, SyntaxAtomSyntax.two_map] <;> rfl) (Derives.conjR (under (under (under (under hE1 E2) E3) E4) E5))
  have c2 : Derives Δ6 (SyntaxLogicalSyntax.binaryCode 2 (old 6 w) (old 6 A) (old 6 I) (slot 6 2)) := of_eq (by simp only [SyntaxNodeSyntax.constructor_rename, SyntaxAtomSyntax.two_map] <;> rfl) (Derives.conjR (under (under (under hE2 E3) E4) E5))
  have c3 : Derives Δ6 (SyntaxLogicalSyntax.binaryCode 2 (old 6 w) (slot 6 0) (slot 6 1) (slot 6 3)) := of_eq (by simp only [SyntaxNodeSyntax.constructor_rename, SyntaxAtomSyntax.two_map] <;> rfl) (Derives.conjR (under (under hE3 E4) E5))
  have c4 : Derives Δ6 (SyntaxLogicalSyntax.binaryCode 2 (old 6 w) (old 6 G) (slot 6 0) (slot 6 4)) := of_eq (by simp only [SyntaxNodeSyntax.constructor_rename, SyntaxAtomSyntax.two_map] <;> rfl) (Derives.conjR (under hE4 E5))
  have c5 : Derives Δ6 (SyntaxLogicalSyntax.binaryCode 2 (old 6 w) (old 6 G) (slot 6 1) (slot 6 5)) := of_eq (by rfl) (Derives.conjR hE5)
  have hProof := at_codes (ZFContext.under (ZFContext.under (ZFContext.under (ZFContext.under (ZFContext.under (ZFContext.under hZ E0) E1) E2) E3) E4) E5) test (old 6 w) (old 6 z) (old 6 b) (old 6 G) (old 6 A) (old 6 C) (old 6 D) (old 6 I) (slot 6) hw6 hz6 hG6 hA6 hD6 hC6 hI6 hp6 (.conjI c0 (.conjI c1 (.conjI c2 (.conjI c3 (.conjI c4 c5)))))
  have hImp : Derives Δ6 (implication test (old 6 w) (old 6 z) (old 6 b) (old 6 G) (slot 6 1)) := by
    apply Derives.exI (slot 6 5)
    exact of_eq (by simp only [Formula.instantiate, Formula.rename, SyntaxNodeSyntax.constructor_rename, SyntaxAtomSyntax.two_map, proved_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] <;> rfl) (.conjI c5 hProof)
  have hout : Derives Δ6 (result test (old 6 w) (old 6 z) (old 6 b) (old 6 G) (old 6 A) (old 6 D)) := by
    apply Derives.exI (slot 6 1)
    exact of_eq (by simp only [Formula.instantiate, Formula.rename, SyntaxLogicalSyntax.binaryCode_rename, implication_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] <;> rfl) (.conjI c1 hImp)
  exact of_eq (by simp only [Formula.raise, result_rename] <;> rfl) hout

/-- Consume the legitimate existential parent proof directly; no proof-code
witness or final implication code is chosen outside the object theory. -/
theorem from_implication {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1)
    (w z b G A C D : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hG : Derives Γ (formulaCode w G z b)) (hA : Derives Γ (formulaCode w A z b))
    (hD : Derives Γ (formulaCode w D z b))
    (hC : Derives Γ (SyntaxLogicalSyntax.binaryCode 0 w G A C))
    (hp : Derives Γ (implication test w z b C D)) : Derives Γ (result test w z b G A D) := by
  let E := (SyntaxNodeSyntax.constructor 2 7 w.castSucc (SyntaxAtomSyntax.two C.castSucc D.castSucc) (Fin.last m)).conj
    (proved test w.castSucc z.castSucc b.castSucc (Fin.last m))
  let Δ := Context.add E (Context.image Formula.raise Γ)
  apply Derives.exE (p := E) hp
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have hOut := produce (ZFContext.under hZ E) test w.castSucc z.castSucc b.castSucc G.castSucc A.castSucc C.castSucc D.castSucc (Fin.last m)
    (of_eq (omega_rename w Fin.castSucc) (under hw E)) (of_eq (empty_rename z Fin.castSucc) (under hz E))
    (of_eq (formulaCode_rename w G z b Fin.castSucc) (under hG E)) (of_eq (formulaCode_rename w A z b Fin.castSucc) (under hA E))
    (of_eq (formulaCode_rename w D z b Fin.castSucc) (under hD E))
    (of_eq (SyntaxLogicalSyntax.binaryCode_rename 0 w G A C Fin.castSucc) (under hC E)) (.conjL hE) (.conjR hE)
  exact of_eq (by simp only [Formula.raise, result_rename]) hOut

def doubleData {m} (test : Formula 1) (w z b G A B D J K : Fin m) : Formula m :=
  (SyntaxLogicalSyntax.binaryCode 2 w B D J).conj
    ((SyntaxLogicalSyntax.binaryCode 2 w A J K).conj (implication test w z b G K))

theorem doubleData_rename {m l} (test : Formula 1) (w z b G A B D J K : Fin m) (ρ : Fin m → Fin l) :
    (doubleData test w z b G A B D J K).rename ρ = doubleData test (ρ w) (ρ z) (ρ b) (ρ G) (ρ A) (ρ B) (ρ D) (ρ J) (ρ K) := by
  simp only [doubleData, Formula.rename, SyntaxLogicalSyntax.binaryCode_rename, implication_rename]

def doubleBody {m} (test : Formula 1) (w z b G A B D : Fin m) : Formula (m+2) :=
  doubleData test (old 2 w) (old 2 z) (old 2 b) (old 2 G) (old 2 A) (old 2 B) (old 2 D) (slot 2 0) (slot 2 1)
def doubleResult {m} (test : Formula 1) (w z b G A B D : Fin m) : Formula m := existsMany 2 (doubleBody test w z b G A B D)

theorem doubleResult_rename {m l} (test : Formula 1) (w z b G A B D : Fin m) (ρ : Fin m → Fin l) :
    (doubleResult test w z b G A B D).rename ρ = doubleResult test (ρ w) (ρ z) (ρ b) (ρ G) (ρ A) (ρ B) (ρ D) := by
  simp only [doubleResult, existsMany_rename, doubleBody, doubleData_rename, lift_old, lift_slot]

/-- Discharge BOTH local antecedents in their source order. Fixed G is kept
unchanged; native mode3/forall can subsequently check actual freshness. -/
theorem twice {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1)
    (w z b G A B C1 C2 D : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hG : Derives Γ (formulaCode w G z b)) (hA : Derives Γ (formulaCode w A z b))
    (hB : Derives Γ (formulaCode w B z b)) (hD : Derives Γ (formulaCode w D z b))
    (hc1 : Derives Γ (SyntaxLogicalSyntax.binaryCode 0 w G A C1))
    (hc2 : Derives Γ (SyntaxLogicalSyntax.binaryCode 0 w C1 B C2))
    (hp : Derives Γ (implication test w z b C2 D)) : Derives Γ (doubleResult test w z b G A B D) := by
  have hC1 := Derives.impE (.conjR (FormulaCodeKnownLogical.binary0_iff hZ w z b G A C1 hw hc1)) (.conjI (.conjR (FormulaCodeProperties.guards w G z b hG)) (.conjI hG hA))
  have he := from_implication hZ test w z b C1 B C2 D hw hz hC1 hB hD hc2 hp
  let E := (SyntaxLogicalSyntax.binaryCode 2 w.castSucc B.castSucc D.castSucc (Fin.last m)).conj
    (implication test w.castSucc z.castSucc b.castSucc C1.castSucc (Fin.last m))
  let Δ := Context.add E (Context.image Formula.raise Γ)
  apply Derives.exE (p := E) he
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw E)
  have hB1 := of_eq (formulaCode_rename w B z b Fin.castSucc) (under hB E)
  have hD1 := of_eq (formulaCode_rename w D z b Fin.castSucc) (under hD E)
  have hJ := Derives.impE (.conjR (FormulaCodeKnownLogical.binary2_iff (ZFContext.under hZ E) w.castSucc z.castSucc b.castSucc B.castSucc D.castSucc (Fin.last m) hw1 (.conjL hE))) (.conjI (.conjR (FormulaCodeProperties.guards w.castSucc B.castSucc z.castSucc b.castSucc hB1)) (.conjI hB1 hD1))
  have hNext := from_implication (ZFContext.under hZ E) test w.castSucc z.castSucc b.castSucc G.castSucc A.castSucc C1.castSucc (Fin.last m) hw1
    (of_eq (empty_rename z Fin.castSucc) (under hz E))
    (of_eq (formulaCode_rename w G z b Fin.castSucc) (under hG E)) (of_eq (formulaCode_rename w A z b Fin.castSucc) (under hA E)) hJ
    (of_eq (SyntaxLogicalSyntax.binaryCode_rename 0 w G A C1 Fin.castSucc) (under hc1 E)) (.conjR hE)
  let F := (SyntaxLogicalSyntax.binaryCode 2 w.castSucc.castSucc A.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))).conj
    (implication test w.castSucc.castSucc z.castSucc.castSucc b.castSucc.castSucc G.castSucc.castSucc (Fin.last (m+1)))
  let Ξ := Context.add F (Context.image Formula.raise Δ)
  apply Derives.exE (p := F) hNext
  have hF : Derives Ξ F := .hyp (Or.inl rfl)
  have hE2 : Derives Ξ ((SyntaxLogicalSyntax.binaryCode 2 w.castSucc.castSucc B.castSucc.castSucc D.castSucc.castSucc (Fin.last m).castSucc).conj
      (implication test w.castSucc.castSucc z.castSucc.castSucc b.castSucc.castSucc C1.castSucc.castSucc (Fin.last m).castSucc)) :=
    of_eq (by simp only [E, Formula.raise, Formula.rename, SyntaxLogicalSyntax.binaryCode_rename, implication_rename]) (under hE F)
  have hout : Derives Ξ (doubleResult test w.castSucc.castSucc z.castSucc.castSucc b.castSucc.castSucc G.castSucc.castSucc A.castSucc.castSucc B.castSucc.castSucc D.castSucc.castSucc) := by
    apply HornBinderRules.intro_many 2 _ (SetLanguage.args2 (Fin.last m).castSucc (Fin.last (m+1)))
    exact of_eq (by simp only [doubleBody, doubleData_rename, assign_old, assign_slot]; rfl) (.conjI (.conjL hE2) hF)
  exact of_eq (by simp only [Formula.raise, doubleResult_rename]) hout

def input {m} (test : Formula 1) (w z b G A C D : Fin m) : Formula m :=
  (omega w).conj ((empty z).conj ((formulaCode w G z b).conj ((formulaCode w A z b).conj ((formulaCode w D z b).conj ((SyntaxLogicalSyntax.binaryCode 0 w G A C).conj ((implication test w z b C D)))))))

def sentence {m} (target : Bool) (w z b G A C D : Fin m) : Source.Sentence :=
  ((input (OriginalAxiomCodeTest.test target) w z b G A C D).imp (result (OriginalAxiomCodeTest.test target) w z b G A D)).close

theorem kernel_certificate {m} (target : Bool) (w z b G A C D : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (sentence target w z b G A C D)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  let E := input (OriginalAxiomCodeTest.test target) w z b G A C D
  let Γ := Context.add E (Source.SetLanguage.ZF.at m)
  have h : Derives Γ E := .hyp (Or.inl rfl)
  exact from_implication (ZFContext.add (ZFContext.source_ZF m) E) (OriginalAxiomCodeTest.test target) w z b G A C D
    (.conjL h)
    (.conjL (.conjR h))
    (.conjL (.conjR (.conjR h)))
    (.conjL (.conjR (.conjR (.conjR h))))
    (.conjL (.conjR (.conjR (.conjR (.conjR h)))))
    (.conjL (.conjR (.conjR (.conjR (.conjR (.conjR h))))))
    (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR h))))))

def doubleInput {m} (test : Formula 1) (w z b G A B C1 C2 D : Fin m) : Formula m :=
  (omega w).conj ((empty z).conj ((formulaCode w G z b).conj ((formulaCode w A z b).conj ((formulaCode w B z b).conj ((formulaCode w D z b).conj ((SyntaxLogicalSyntax.binaryCode 0 w G A C1).conj ((SyntaxLogicalSyntax.binaryCode 0 w C1 B C2).conj ((implication test w z b C2 D)))))))))

def doubleSentence {m} (target : Bool) (w z b G A B C1 C2 D : Fin m) : Source.Sentence :=
  ((doubleInput (OriginalAxiomCodeTest.test target) w z b G A B C1 C2 D).imp (doubleResult (OriginalAxiomCodeTest.test target) w z b G A B D)).close

theorem double_kernel_certificate {m} (target : Bool) (w z b G A B C1 C2 D : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (doubleSentence target w z b G A B C1 C2 D)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  let E := doubleInput (OriginalAxiomCodeTest.test target) w z b G A B C1 C2 D
  let Γ := Context.add E (Source.SetLanguage.ZF.at m)
  have h : Derives Γ E := .hyp (Or.inl rfl)
  exact twice (ZFContext.add (ZFContext.source_ZF m) E) (OriginalAxiomCodeTest.test target) w z b G A B C1 C2 D
    (.conjL h)
    (.conjL (.conjR h))
    (.conjL (.conjR (.conjR h)))
    (.conjL (.conjR (.conjR (.conjR h))))
    (.conjL (.conjR (.conjR (.conjR (.conjR h)))))
    (.conjL (.conjR (.conjR (.conjR (.conjR (.conjR h))))))
    (.conjL (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR h)))))))
    (.conjL (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR h))))))))
    (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR h))))))))

def negativeCurried {m} (test : Formula 1) (w z T Extra Local D Bottom Rest : Fin m) : Formula m :=
  (SyntaxLogicalSyntax.binaryCode 2 w D Bottom Rest).conj
    ((SyntaxAtomSyntax.zeroScalar w Bottom).conj (result test w z T Extra Local Rest))

theorem negativeCurried_rename {m l} (test : Formula 1) (w z T Extra Local D Bottom Rest : Fin m) (ρ : Fin m → Fin l) :
    (negativeCurried test w z T Extra Local D Bottom Rest).rename ρ = negativeCurried test (ρ w) (ρ z) (ρ T) (ρ Extra) (ρ Local) (ρ D) (ρ Bottom) (ρ Rest) := by
  simp only [negativeCurried, Formula.rename, SyntaxLogicalSyntax.binaryCode_rename, SyntaxAtomSyntax.zeroScalar_rename, result_rename]

/-- The actual accepted local negative consumer feeds the currying operator.
Extra stays EXACTLY the same; the entire local row G0 moves to an implication
antecedent. Actual source-row identification and final forall freshness are
separate obligations, never assumed as target-proof answers here. -/
theorem from_local_negative {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1)
    (w z T C Refl Pre Extra Ctx D Bottom Rest I Y : Fin m) (G : Fin 5 → Fin m) (H : Fin 6 → Fin m) (U F P : Fin 3 → Fin m) (N : Fin 5 → Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hr : Derives Γ (ForcingTransitiveGuardProof.row w z T C Refl Pre G H U F P N))
    (hCtx : Derives Γ (formulaCode w Ctx z T))
    (hConj : Derives Γ (SyntaxLogicalSyntax.binaryCode 0 w Extra (G 0) Ctx))
    (hY : Derives Γ (formulaCode w Y z T))
    (hOuter : Derives Γ (SyntaxLogicalSyntax.binaryCode 2 w (H 0) I Y))
    (hOrder : Derives Γ (SyntaxLogicalSyntax.binaryCode 2 w (H 5) Rest I))
    (hRest : Derives Γ (SyntaxLogicalSyntax.binaryCode 2 w D Bottom Rest))
    (hBottom : Derives Γ (SyntaxAtomSyntax.zeroScalar w Bottom))
    (hp : Derives Γ (implication test w z T Ctx Y)) :
    Derives Γ (negativeCurried test w z T Extra (G 0) D Bottom Rest) := by
  have hLocal := ForcingTransitiveGuardProof.at_negative_under hZ test w z T C Refl Pre Extra Ctx D Bottom Rest I Y G H U F P N hw hz hr hCtx hConj hY hOuter hOrder hRest hBottom hp
  have hG := Derives.conjL hr
  have hExtra := Derives.conjL (Derives.conjR (Derives.impE (Derives.conjL (FormulaCodeKnownLogical.binary0_iff hZ w z T Extra (G 0) Ctx hw hConj)) hCtx))
  have hI := Derives.conjR (Derives.conjR (Derives.impE (Derives.conjL (FormulaCodeKnownLogical.binary2_iff hZ w z T (H 0) I Y hw hOuter)) hY))
  have hRt := Derives.conjR (Derives.conjR (Derives.impE (Derives.conjL (FormulaCodeKnownLogical.binary2_iff hZ w z T (H 5) Rest I hw hOrder)) hI))
  have hCurry := from_implication hZ test w z T Extra (G 0) Ctx Rest hw hz hExtra hG hRt hConj (.conjR (.conjR hLocal))
  exact .conjI hRest (.conjI hBottom hCurry)

def negativeInput {m} (test : Formula 1) (w z T C Refl Pre Extra Ctx D Bottom Rest I Y : Fin m) (G : Fin 5 → Fin m) (H : Fin 6 → Fin m) (U F P : Fin 3 → Fin m) (N : Fin 5 → Fin m) : Formula m :=
  ForcingTransitiveGuardProof.ambientInput test w z T C Refl Pre Extra Ctx D Bottom Rest I Y G H U F P N

def negativeSentence {m} (target : Bool) (w z T C Refl Pre Extra Ctx D Bottom Rest I Y : Fin m) (G : Fin 5 → Fin m) (H : Fin 6 → Fin m) (U F P : Fin 3 → Fin m) (N : Fin 5 → Fin m) : Source.Sentence :=
  ((negativeInput (OriginalAxiomCodeTest.test target) w z T C Refl Pre Extra Ctx D Bottom Rest I Y G H U F P N).imp (negativeCurried (OriginalAxiomCodeTest.test target) w z T Extra (G 0) D Bottom Rest)).close

theorem negative_kernel_certificate {m} (target : Bool) (w z T C Refl Pre Extra Ctx D Bottom Rest I Y : Fin m) (G : Fin 5 → Fin m) (H : Fin 6 → Fin m) (U F P : Fin 3 → Fin m) (N : Fin 5 → Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (negativeSentence target w z T C Refl Pre Extra Ctx D Bottom Rest I Y G H U F P N)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  let E := negativeInput (OriginalAxiomCodeTest.test target) w z T C Refl Pre Extra Ctx D Bottom Rest I Y G H U F P N
  let Γ := Context.add E (Source.SetLanguage.ZF.at m)
  have h : Derives Γ E := .hyp (Or.inl rfl)
  have hBase := Derives.conjL h
  exact from_local_negative (ZFContext.add (ZFContext.source_ZF m) E) (OriginalAxiomCodeTest.test target) w z T C Refl Pre Extra Ctx D Bottom Rest I Y G H U F P N
    (.conjL hBase) (.conjL (.conjR hBase)) (.conjR (.conjR hBase))
    (.conjL (.conjR h))
    (.conjL (.conjR (.conjR h)))
    (.conjL (.conjR (.conjR (.conjR h))))
    (.conjL (.conjR (.conjR (.conjR (.conjR h)))))
    (.conjL (.conjR (.conjR (.conjR (.conjR (.conjR h))))))
    (.conjL (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR h)))))))
    (.conjL (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR h))))))))
    (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR h))))))))

end PPAC.Migration.InternalProofCurry
