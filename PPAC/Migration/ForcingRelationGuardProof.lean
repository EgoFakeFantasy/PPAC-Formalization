import PPAC.Migration.ForcingReflexiveDiagram
import PPAC.Migration.ForcingNegMemberProof
import PPAC.Migration.InternalProofQuantifier
import PPAC.Migration.Internal.SyntaxTopFormulaLogicalEndpoints

/-! Actual guarded reflexivity proofs in the original internal proof system.
The common background contains the CARRIER-GUARDED reflexivity row, together
with the actual P-in-V member. No proof or truth of that background is used.
All code and proof witnesses are internal; no new proof kernel is introduced. -/
namespace PPAC.Migration.ForcingRelationGuardProof
open Internal Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)
open FormulaCodeSyntax (formulaCode formulaCode_rename)
open InternalProofBackground (implication implication_rename)
open InternalProofConjunction (proved proved_rename)
set_option maxRecDepth 32768
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem project {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1) (right : Bool)
    (w z b A B C : Fin m) (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hA : Derives Γ (formulaCode w A z b)) (hB : Derives Γ (formulaCode w B z b))
    (hC : Derives Γ (formulaCode w C z b))
    (hc : Derives Γ (SyntaxNodeSyntax.constructor 2 5 w (SyntaxAtomSyntax.two A B) C)) :
    Derives Γ (implication test w z b C (if right then B else A)) := by
  cases right
  · change Derives Γ (implication test w z b C A)
    let Q0 := (Formula.mem (Fin.last m) w.castSucc).conj (SyntaxNodeSyntax.constructor 2 7 w.castSucc (SyntaxAtomSyntax.two C.castSucc A.castSucc) (Fin.last m))
    let Δ1 := Context.add Q0 (Context.image Formula.raise Γ)
    apply Derives.exE (p := Q0) (SyntaxConstructors.exists_constructor hZ 2 7 w (SyntaxAtomSyntax.two C A) hw (.conjI (.conjL (FormulaCodeProperties.guards w C z b hC)) (.conjI (.conjL (FormulaCodeProperties.guards w A z b hA)) (.eqRefl w))))
    have hQ0 : Derives Δ1 Q0 := .hyp (Or.inl rfl)
    have hProof := InternalProofTemplates.projection_axiom (ZFContext.under hZ Q0) test false w.castSucc z.castSucc b.castSucc A.castSucc B.castSucc C.castSucc (Fin.last m) (by simpa only [Formula.raise, omega_rename] using (under hw Q0)) (by simpa only [Formula.raise, empty_rename] using (under hz Q0)) (by simpa only [Formula.raise, formulaCode_rename] using (under hA Q0)) (by simpa only [Formula.raise, formulaCode_rename] using (under hB Q0)) (by simpa only [Formula.raise, SyntaxNodeSyntax.constructor_rename, SyntaxAtomSyntax.two_map] using (under hc Q0)) (.conjR hQ0)
    have hout : Derives Δ1 (implication test w.castSucc z.castSucc b.castSucc C.castSucc A.castSucc) := by
      apply Derives.exI (Fin.last m)
      have hPair : Derives Δ1 ((SyntaxNodeSyntax.constructor 2 7 w.castSucc (SyntaxAtomSyntax.two C.castSucc A.castSucc) (Fin.last m)).conj (proved test w.castSucc z.castSucc b.castSucc (Fin.last m))) := .conjI (.conjR hQ0) hProof
      exact of_eq (by simp only [Formula.instantiate, Formula.rename, SyntaxNodeSyntax.constructor_rename, SyntaxAtomSyntax.two_map, proved_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hPair
    exact of_eq (by simp only [Formula.raise, implication_rename]) hout

  · change Derives Γ (implication test w z b C B)
    let Q0 := (Formula.mem (Fin.last m) w.castSucc).conj (SyntaxNodeSyntax.constructor 2 7 w.castSucc (SyntaxAtomSyntax.two C.castSucc B.castSucc) (Fin.last m))
    let Δ1 := Context.add Q0 (Context.image Formula.raise Γ)
    apply Derives.exE (p := Q0) (SyntaxConstructors.exists_constructor hZ 2 7 w (SyntaxAtomSyntax.two C B) hw (.conjI (.conjL (FormulaCodeProperties.guards w C z b hC)) (.conjI (.conjL (FormulaCodeProperties.guards w B z b hB)) (.eqRefl w))))
    have hQ0 : Derives Δ1 Q0 := .hyp (Or.inl rfl)
    have hProof := InternalProofTemplates.projection_axiom (ZFContext.under hZ Q0) test true w.castSucc z.castSucc b.castSucc A.castSucc B.castSucc C.castSucc (Fin.last m) (by simpa only [Formula.raise, omega_rename] using (under hw Q0)) (by simpa only [Formula.raise, empty_rename] using (under hz Q0)) (by simpa only [Formula.raise, formulaCode_rename] using (under hA Q0)) (by simpa only [Formula.raise, formulaCode_rename] using (under hB Q0)) (by simpa only [Formula.raise, SyntaxNodeSyntax.constructor_rename, SyntaxAtomSyntax.two_map] using (under hc Q0)) (.conjR hQ0)
    have hout : Derives Δ1 (implication test w.castSucc z.castSucc b.castSucc C.castSucc B.castSucc) := by
      apply Derives.exI (Fin.last m)
      have hPair : Derives Δ1 ((SyntaxNodeSyntax.constructor 2 7 w.castSucc (SyntaxAtomSyntax.two C.castSucc B.castSucc) (Fin.last m)).conj (proved test w.castSucc z.castSucc b.castSucc (Fin.last m))) := .conjI (.conjR hQ0) hProof
      exact of_eq (by simp only [Formula.instantiate, Formula.rename, SyntaxNodeSyntax.constructor_rename, SyntaxAtomSyntax.two_map, proved_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hPair
    exact of_eq (by simp only [Formula.raise, implication_rename]) hout

theorem chain {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1)
    (w z b A B C : Fin m) (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hA : Derives Γ (formulaCode w A z b)) (hB : Derives Γ (formulaCode w B z b)) (hC : Derives Γ (formulaCode w C z b))
    (hp : Derives Γ (implication test w z b A B)) (hq : Derives Γ (implication test w z b B C)) :
    Derives Γ (implication test w z b A C) := by
  let Q0 := (SyntaxNodeSyntax.constructor 2 7 w.castSucc (SyntaxAtomSyntax.two A.castSucc B.castSucc) (Fin.last m)).conj (proved test w.castSucc z.castSucc b.castSucc (Fin.last m))
  let Δ1 := Context.add Q0 (Context.image Formula.raise Γ)
  apply Derives.exE (p := Q0) hp
  have hQ0 : Derives Δ1 Q0 := .hyp (Or.inl rfl)
  let Q1 := (SyntaxNodeSyntax.constructor 2 7 w.castSucc.castSucc (SyntaxAtomSyntax.two B.castSucc.castSucc C.castSucc.castSucc) (Fin.last (m+1))).conj (proved test w.castSucc.castSucc z.castSucc.castSucc b.castSucc.castSucc (Fin.last (m+1)))
  let Δ2 := Context.add Q1 (Context.image Formula.raise Δ1)
  apply Derives.exE (p := Q1) (of_eq (implication_rename test w z b B C Fin.castSucc) (under hq Q0))
  have hQ1 : Derives Δ2 Q1 := .hyp (Or.inl rfl)
  let Q2 := (Formula.mem (Fin.last (m+2)) w.castSucc.castSucc.castSucc).conj (SyntaxNodeSyntax.constructor 2 7 w.castSucc.castSucc.castSucc (SyntaxAtomSyntax.two A.castSucc.castSucc.castSucc C.castSucc.castSucc.castSucc) (Fin.last (m+2)))
  let Δ3 := Context.add Q2 (Context.image Formula.raise Δ2)
  apply Derives.exE (p := Q2) (SyntaxConstructors.exists_constructor (ZFContext.under (ZFContext.under hZ Q0) Q1) 2 7 w.castSucc.castSucc (SyntaxAtomSyntax.two A.castSucc.castSucc C.castSucc.castSucc) (by simpa only [Formula.raise, omega_rename] using (under (under hw Q0) Q1)) (.conjI (.conjL (FormulaCodeProperties.guards w.castSucc.castSucc A.castSucc.castSucc z.castSucc.castSucc b.castSucc.castSucc (by simpa only [Formula.raise, formulaCode_rename] using (under (under hA Q0) Q1)))) (.conjI (.conjL (FormulaCodeProperties.guards w.castSucc.castSucc C.castSucc.castSucc z.castSucc.castSucc b.castSucc.castSucc (by simpa only [Formula.raise, formulaCode_rename] using (under (under hC Q0) Q1)))) (.eqRefl w.castSucc.castSucc))))
  have hQ2 : Derives Δ3 Q2 := .hyp (Or.inl rfl)
  have hProof := InternalProofImplication.compose (ZFContext.under (ZFContext.under (ZFContext.under hZ Q0) Q1) Q2) test w.castSucc.castSucc.castSucc z.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc A.castSucc.castSucc.castSucc B.castSucc.castSucc.castSucc C.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc (Fin.last (m+2)) (by simpa only [Formula.raise, omega_rename] using (under (under (under hw Q0) Q1) Q2)) (by simpa only [Formula.raise, empty_rename] using (under (under (under hz Q0) Q1) Q2)) (by simpa only [Formula.raise, formulaCode_rename] using (under (under (under hA Q0) Q1) Q2)) (by simpa only [Formula.raise, formulaCode_rename] using (under (under (under hB Q0) Q1) Q2)) (by simpa only [Formula.raise, formulaCode_rename] using (under (under (under hC Q0) Q1) Q2)) (by simpa only [Formula.raise, SyntaxNodeSyntax.constructor_rename, SyntaxAtomSyntax.two_map] using (under (under (.conjL hQ0) Q1) Q2)) (by simpa only [Formula.raise, SyntaxNodeSyntax.constructor_rename, SyntaxAtomSyntax.two_map] using (under (.conjL hQ1) Q2)) (.conjR hQ2) (by simpa only [Formula.raise, proved_rename] using (under (under (.conjR hQ0) Q1) Q2)) (by simpa only [Formula.raise, proved_rename] using (under (.conjR hQ1) Q2))
  have hout : Derives Δ3 (implication test w.castSucc.castSucc.castSucc z.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc A.castSucc.castSucc.castSucc C.castSucc.castSucc.castSucc) := by
    apply Derives.exI (Fin.last (m+2))
    have hPair : Derives Δ3 ((SyntaxNodeSyntax.constructor 2 7 w.castSucc.castSucc.castSucc (SyntaxAtomSyntax.two A.castSucc.castSucc.castSucc C.castSucc.castSucc.castSucc) (Fin.last (m+2))).conj (proved test w.castSucc.castSucc.castSucc z.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc (Fin.last (m+2)))) := .conjI (.conjR hQ2) hProof
    exact of_eq (by simp only [Formula.instantiate, Formula.rename, SyntaxNodeSyntax.constructor_rename, SyntaxAtomSyntax.two_map, proved_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hPair
  exact of_eq (by simp only [Formula.raise, implication_rename]) hout

theorem instantiate {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1)
    (w z b A F term N U G : Fin m) (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hG : Derives Γ (formulaCode w G z b)) (hN : Derives Γ (formulaCode w N z b))
    (hi : Derives Γ (SyntaxTopFormulaSyntax.instantiated w z b A term F N))
    (hu : Derives Γ (SyntaxLogicalSyntax.singleCode 9 w F U))
    (hp : Derives Γ (implication test w z b G U)) :
    Derives Γ (implication test w z b G N) := by
  let Q0 := (SyntaxNodeSyntax.constructor 2 7 w.castSucc (SyntaxAtomSyntax.two G.castSucc U.castSucc) (Fin.last m)).conj (proved test w.castSucc z.castSucc b.castSucc (Fin.last m))
  let Δ1 := Context.add Q0 (Context.image Formula.raise Γ)
  apply Derives.exE (p := Q0) hp
  have hQ0 : Derives Δ1 Q0 := .hyp (Or.inl rfl)
  let Q1 := (Formula.mem (Fin.last (m+1)) w.castSucc.castSucc).conj (SyntaxNodeSyntax.constructor 2 7 w.castSucc.castSucc (SyntaxAtomSyntax.two G.castSucc.castSucc N.castSucc.castSucc) (Fin.last (m+1)))
  let Δ2 := Context.add Q1 (Context.image Formula.raise Δ1)
  apply Derives.exE (p := Q1) (SyntaxConstructors.exists_constructor (ZFContext.under hZ Q0) 2 7 w.castSucc (SyntaxAtomSyntax.two G.castSucc N.castSucc) (by simpa only [Formula.raise, omega_rename] using (under hw Q0)) (.conjI (.conjL (FormulaCodeProperties.guards w.castSucc G.castSucc z.castSucc b.castSucc (by simpa only [Formula.raise, formulaCode_rename] using (under hG Q0)))) (.conjI (.conjL (FormulaCodeProperties.guards w.castSucc N.castSucc z.castSucc b.castSucc (by simpa only [Formula.raise, formulaCode_rename] using (under hN Q0)))) (.eqRefl w.castSucc))))
  have hQ1 : Derives Δ2 Q1 := .hyp (Or.inl rfl)
  have hProof := InternalProofQuantifier.guarded_eliminate (ZFContext.under (ZFContext.under hZ Q0) Q1) test w.castSucc.castSucc z.castSucc.castSucc b.castSucc.castSucc A.castSucc.castSucc F.castSucc.castSucc term.castSucc.castSucc N.castSucc.castSucc U.castSucc.castSucc G.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) (by simpa only [Formula.raise, omega_rename] using (under (under hw Q0) Q1)) (by simpa only [Formula.raise, empty_rename] using (under (under hz Q0) Q1)) (by simpa only [Formula.raise, SyntaxTopFormulaSyntax.instantiated_rename] using (under (under hi Q0) Q1)) (by simpa only [Formula.raise, SyntaxLogicalSyntax.singleCode_rename] using (under (under hu Q0) Q1)) (by simpa only [Formula.raise, formulaCode_rename] using (under (under hG Q0) Q1)) (by simpa only [Formula.raise, SyntaxNodeSyntax.constructor_rename, SyntaxAtomSyntax.two_map] using (under (.conjL hQ0) Q1)) (.conjR hQ1) (by simpa only [Formula.raise, proved_rename] using (under (.conjR hQ0) Q1))
  have hout : Derives Δ2 (implication test w.castSucc.castSucc z.castSucc.castSucc b.castSucc.castSucc G.castSucc.castSucc N.castSucc.castSucc) := by
    apply Derives.exI (Fin.last (m+1))
    have hPair : Derives Δ2 ((SyntaxNodeSyntax.constructor 2 7 w.castSucc.castSucc (SyntaxAtomSyntax.two G.castSucc.castSucc N.castSucc.castSucc) (Fin.last (m+1))).conj (proved test w.castSucc.castSucc z.castSucc.castSucc b.castSucc.castSucc (Fin.last (m+1)))) := .conjI (.conjR hQ1) hProof
    exact of_eq (by simp only [Formula.instantiate, Formula.rename, SyntaxNodeSyntax.constructor_rename, SyntaxAtomSyntax.two_map, proved_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hPair
  exact of_eq (by simp only [Formula.raise, implication_rename]) hout

/-- Code data for the SAME common background. U is ALL(Dm -> Do), and
B is Rest AND U. Both native instances are the actual original guard outputs.
This describes codes, never truth or provability of G, B, U, M or O. -/
def row {m} (w z T C P V Rest B sym E G Dm Do F U M O : Fin m) : Formula m :=
  (InternalProofBackground.data w z T P V B sym E G).conj
    ((SyntaxNodeSyntax.constructor 2 5 w (SyntaxAtomSyntax.two Rest U) B).conj
      ((SyntaxLogicalSyntax.singleCode 9 w F U).conj
        ((SyntaxLogicalSyntax.binaryCode 2 w Dm Do F).conj
          ((SyntaxTopFormulaSyntax.instantiated w z T C P Dm M).conj
            ((SyntaxTopFormulaSyntax.instantiated w z T C P Do O).conj
              (ForcingMemberGuardOpening.result w P V M))))))

theorem row_rename {m l} (w z T C P V Rest B sym E G Dm Do F U M O : Fin m) (ρ : Fin m → Fin l) :
    (row w z T C P V Rest B sym E G Dm Do F U M O).rename ρ =
      row (ρ w) (ρ z) (ρ T) (ρ C) (ρ P) (ρ V) (ρ Rest) (ρ B) (ρ sym) (ρ E) (ρ G) (ρ Dm) (ρ Do) (ρ F) (ρ U) (ρ M) (ρ O) := by
  simp only [row, Formula.rename, InternalProofBackground.data_rename,
    SyntaxNodeSyntax.constructor_rename, SyntaxAtomSyntax.two_map, SyntaxLogicalSyntax.singleCode_rename,
    SyntaxLogicalSyntax.binaryCode_rename, SyntaxTopFormulaSyntax.instantiated_rename, ForcingMemberGuardOpening.result_rename]

private theorem at_implication {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1)
    (w z T C P V Rest B sym E G Dm Do F U M O N : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hr : Derives Γ (row w z T C P V Rest B sym E G Dm Do F U M O))
    (hcN : Derives Γ (SyntaxLogicalSyntax.binaryCode 2 w M O N)) :
    Derives Γ (implication test w z T G O) := by
  have hBG := Derives.conjL hr
  have hcB := Derives.conjL (.conjR hr)
  have hcU := Derives.conjL (.conjR (.conjR hr))
  have hcF := Derives.conjL (.conjR (.conjR (.conjR hr)))
  have hiM := Derives.conjL (.conjR (.conjR (.conjR (.conjR hr))))
  have hiO := Derives.conjL (.conjR (.conjR (.conjR (.conjR (.conjR hr)))))
  have hm := Derives.conjR (.conjR (.conjR (.conjR (.conjR (.conjR hr)))))
  have hB := Derives.conjL hBG
  have hE := Derives.conjR (.conjL (.conjR (.conjR hBG)))
  have hG := Derives.conjR (.conjR (.conjR (.conjR hBG)))
  have hBc := Derives.impE (.conjL (FormulaCodeKnownLogical.binary0_iff hZ w z T Rest U B hw hcB)) hB
  have hRest := Derives.conjL (.conjR hBc)
  have hU := Derives.conjR (.conjR hBc)
  have hDm := SyntaxTopFormulaTyping.instantiate_source_type hZ w z T C P Dm M hw hiM
  have hDo := SyntaxTopFormulaTyping.instantiate_source_type hZ w z T C P Do O hw hiO
  have hF := Derives.impE (.conjR (FormulaCodeKnownLogical.binary2_iff hZ w C T Dm Do F hw hcF))
    (.conjI (.conjR (FormulaCodeProperties.guards w Dm C T hDm)) (.conjI hDm hDo))
  have hM := SyntaxTopFormulaTyping.instantiate_target_type w z T C P Dm M hiM
  have hO := SyntaxTopFormulaTyping.instantiate_target_type w z T C P Do O hiO
  have hN := Derives.impE (.conjR (FormulaCodeKnownLogical.binary2_iff hZ w z T M O N hw hcN))
    (.conjI (.conjR (FormulaCodeProperties.guards w M z T hM)) (.conjI hM hO))
  have hiF := Derives.impE (.conjR (SyntaxTopFormulaLogicalEndpoints.instantiate_binary_iff hZ 2 w z T C P F N Dm Do M O hw
    (.conjI (SyntaxTopFormulaTyping.instantiate_environment w z T C P Dm M hiM) hF) hcF hcN)) (.conjI hiM hiO)
  have hpGB := project hZ test false w z T B E G hw hz hB hE hG (.conjL (.conjR (.conjR (.conjR hBG))))
  have hpBU := project hZ test true w z T Rest U B hw hz hRest hU hB hcB
  have hpGU := chain hZ test w z T G B U hw hz hG hB hU hpGB hpBU
  have hpGN := instantiate hZ test w z T C F P N U G hw hz hG hN hiF hcU hpGU
  have hpGM := ForcingMemberGuardProof.at_background hZ test w z T P V B M sym E G hw hz hBG hm
  exact ForcingNegMemberProof.discharge hZ test w z T G M O N hw hz hG hN hcN hpGM hpGN

/-- Actual original internal proof G -> O under the SAME canonical member
background. The instance implication code is BUILT internally. Projection,
rule20, S and MP are the existing original proof producers; G is not proved. -/
theorem at_background {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1)
    (w z T C P V Rest B sym E G Dm Do F U M O : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hr : Derives Γ (row w z T C P V Rest B sym E G Dm Do F U M O)) :
    Derives Γ (implication test w z T G O) := by
  have hiM := Derives.conjL (.conjR (.conjR (.conjR (.conjR hr))))
  have hiO := Derives.conjL (.conjR (.conjR (.conjR (.conjR (.conjR hr)))))
  have hM := SyntaxTopFormulaTyping.instantiate_target_type w z T C P Dm M hiM
  have hO := SyntaxTopFormulaTyping.instantiate_target_type w z T C P Do O hiO
  have he := SyntaxConstructors.exists_constructor hZ 2 7 w (SyntaxAtomSyntax.two M O) hw
    (.conjI (.conjL (FormulaCodeProperties.guards w M z T hM)) (.conjI (.conjL (FormulaCodeProperties.guards w O z T hO)) (.eqRefl w)))
  let Q := (Formula.mem (Fin.last m) w.castSucc).conj
    (SyntaxNodeSyntax.constructor 2 7 w.castSucc (SyntaxAtomSyntax.two M.castSucc O.castSucc) (Fin.last m))
  let Δ := Context.add Q (Context.image Formula.raise Γ)
  apply Derives.exE (p := Q) he
  have hQ : Derives Δ Q := .hyp (Or.inl rfl)
  have hout := at_implication (ZFContext.under hZ Q) test
    w.castSucc z.castSucc T.castSucc C.castSucc P.castSucc V.castSucc Rest.castSucc B.castSucc sym.castSucc E.castSucc G.castSucc Dm.castSucc Do.castSucc F.castSucc U.castSucc M.castSucc O.castSucc (Fin.last m)
    (of_eq (omega_rename w Fin.castSucc) (under hw Q)) (of_eq (empty_rename z Fin.castSucc) (under hz Q))
    (of_eq (row_rename w z T C P V Rest B sym E G Dm Do F U M O Fin.castSucc) (under hr Q)) (.conjR hQ)
  exact of_eq (implication_rename test w z T G O Fin.castSucc).symm hout

def data {m} (test : Formula 1) (w z T C P V Rest M O Dm Do F U B sym E G : Fin m) : Formula m :=
  (row w z T C P V Rest B sym E G Dm Do F U M O).conj
    ((implication test w z T G M).conj (implication test w z T G O))

theorem data_rename {m l} (test : Formula 1) (w z T C P V Rest M O Dm Do F U B sym E G : Fin m) (ρ : Fin m → Fin l) :
    (data test w z T C P V Rest M O Dm Do F U B sym E G).rename ρ =
      data test (ρ w) (ρ z) (ρ T) (ρ C) (ρ P) (ρ V) (ρ Rest) (ρ M) (ρ O) (ρ Dm) (ρ Do) (ρ F) (ρ U) (ρ B) (ρ sym) (ρ E) (ρ G) := by
  simp only [data, Formula.rename, row_rename, implication_rename]

def body {m} (test : Formula 1) (w z T C P V Rest M O Dm Do : Fin m) : Formula (m+6) :=
  data test (old 6 w) (old 6 z) (old 6 T) (old 6 C) (old 6 P) (old 6 V) (old 6 Rest) (old 6 M) (old 6 O) (old 6 Dm) (old 6 Do)
    (slot 6 0) (slot 6 1) (slot 6 2) (slot 6 3) (slot 6 4) (slot 6 5)

def result {m} (test : Formula 1) (w z T C P V Rest M O Dm Do : Fin m) : Formula m :=
  existsMany 6 (body test w z T C P V Rest M O Dm Do)

theorem result_rename {m l} (test : Formula 1) (w z T C P V Rest M O Dm Do : Fin m) (ρ : Fin m → Fin l) :
    (result test w z T C P V Rest M O Dm Do).rename ρ =
      result test (ρ w) (ρ z) (ρ T) (ρ C) (ρ P) (ρ V) (ρ Rest) (ρ M) (ρ O) (ρ Dm) (ρ Do) := by
  simp only [result, existsMany_rename, body, data_rename, lift_old, lift_slot]

/-- Generate ALL code/background/proof witnesses internally from the two
actual native guard instances. U has precisely the body Dm -> Do and bound
successor C, so it retains the member guard and never asserts unguarded Rqq. -/
theorem from_bodies {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1)
    (w z T C P V Rest M O Dm Do : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hRest : Derives Γ (formulaCode w Rest z T))
    (hiM : Derives Γ (SyntaxTopFormulaSyntax.instantiated w z T C P Dm M))
    (hiO : Derives Γ (SyntaxTopFormulaSyntax.instantiated w z T C P Do O))
    (hm : Derives Γ (ForcingMemberGuardOpening.result w P V M)) :
    Derives Γ (result test w z T C P V Rest M O Dm Do) := by
  have tag2 : SyntaxLogicalSyntax.binaryTag (2 : Fin 4) = 7 := rfl
  have hDm := SyntaxTopFormulaTyping.instantiate_source_type hZ w z T C P Dm M hw hiM
  have hDo := SyntaxTopFormulaTyping.instantiate_source_type hZ w z T C P Do O hw hiO
  have hC := Derives.conjR (SyntaxTopFormulaTyping.instantiate_environment w z T C P Dm M hiM)
  let Q0 := (Formula.mem (Fin.last m) w.castSucc).conj (FormulaCodeConstructSyntax.typedAt 2 7 w.castSucc (SyntaxAtomSyntax.two Dm.castSucc Do.castSucc) (Fin.last m) C.castSucc T.castSucc)
  let Δ1 := Context.add Q0 (Context.image Formula.raise Γ)
  apply Derives.exE (p := Q0) (FormulaCodeConstruct.exists_of_fiber 2 7 w (SyntaxAtomSyntax.two Dm Do) C T (FormulaCodeConstructors.binary2 hZ w C T Dm Do hw (.conjI (.conjR (FormulaCodeProperties.guards w Dm C T hDm)) (.conjI hDm hDo))))
  have hQ0 : Derives Δ1 Q0 := .hyp (Or.inl rfl)
  have hF : Derives Δ1 (formulaCode w.castSucc (Fin.last m) C.castSucc T.castSucc) := .conjR (.conjR hQ0)
  have hAdvanced := Derives.impE (.conjR (FormulaCodeBranchSyntax.at_successor (ZFContext.under hZ Q0) w.castSucc (Fin.last m) z.castSucc T.castSucc C.castSucc (by simpa only [old, SyntaxLogicalSyntax.singleCode, SyntaxLogicalSyntax.binaryCode, tag2, Formula.raise, successor_rename] using (under hC Q0)))) hF
  have hAll := FormulaCodeConstructors.universal (ZFContext.under hZ Q0) w.castSucc z.castSucc T.castSucc (Fin.last m) (by simpa only [old, SyntaxLogicalSyntax.singleCode, SyntaxLogicalSyntax.binaryCode, tag2, Formula.raise, omega_rename] using (under hw Q0)) (.conjI (.conjR (FormulaCodeProperties.guards w.castSucc Rest.castSucc z.castSucc T.castSucc (by simpa only [old, SyntaxLogicalSyntax.singleCode, SyntaxLogicalSyntax.binaryCode, tag2, Formula.raise, formulaCode_rename] using (under hRest Q0)))) hAdvanced)
  let Q1 := (Formula.mem (Fin.last (m+1)) w.castSucc.castSucc).conj (FormulaCodeConstructSyntax.typedAt 1 9 w.castSucc.castSucc (fun _ => (Fin.last m).castSucc) (Fin.last (m+1)) z.castSucc.castSucc T.castSucc.castSucc)
  let Δ2 := Context.add Q1 (Context.image Formula.raise Δ1)
  apply Derives.exE (p := Q1) (FormulaCodeConstruct.exists_of_fiber 1 9 w.castSucc (fun _ => (Fin.last m)) z.castSucc T.castSucc hAll)
  have hQ1 : Derives Δ2 Q1 := .hyp (Or.inl rfl)
  have hU : Derives Δ2 (formulaCode w.castSucc.castSucc (Fin.last (m+1)) z.castSucc.castSucc T.castSucc.castSucc) := .conjR (.conjR hQ1)
  have hConj := FormulaCodeConstructors.binary0 (ZFContext.under (ZFContext.under hZ Q0) Q1) w.castSucc.castSucc z.castSucc.castSucc T.castSucc.castSucc Rest.castSucc.castSucc (Fin.last (m+1)) (by simpa only [old, SyntaxLogicalSyntax.singleCode, SyntaxLogicalSyntax.binaryCode, tag2, Formula.raise, omega_rename] using (under (under hw Q0) Q1)) (.conjI (.conjR (FormulaCodeProperties.guards w.castSucc.castSucc Rest.castSucc.castSucc z.castSucc.castSucc T.castSucc.castSucc (by simpa only [old, SyntaxLogicalSyntax.singleCode, SyntaxLogicalSyntax.binaryCode, tag2, Formula.raise, formulaCode_rename] using (under (under hRest Q0) Q1)))) (.conjI (by simpa only [old, SyntaxLogicalSyntax.singleCode, SyntaxLogicalSyntax.binaryCode, tag2, Formula.raise, formulaCode_rename] using (under (under hRest Q0) Q1)) hU))
  let Q2 := (Formula.mem (Fin.last (m+2)) w.castSucc.castSucc.castSucc).conj (FormulaCodeConstructSyntax.typedAt 2 5 w.castSucc.castSucc.castSucc (SyntaxAtomSyntax.two Rest.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc) (Fin.last (m+2)) z.castSucc.castSucc.castSucc T.castSucc.castSucc.castSucc)
  let Δ3 := Context.add Q2 (Context.image Formula.raise Δ2)
  apply Derives.exE (p := Q2) (FormulaCodeConstruct.exists_of_fiber 2 5 w.castSucc.castSucc (SyntaxAtomSyntax.two Rest.castSucc.castSucc (Fin.last (m+1))) z.castSucc.castSucc T.castSucc.castSucc hConj)
  have hQ2 : Derives Δ3 Q2 := .hyp (Or.inl rfl)
  have hB : Derives Δ3 (formulaCode w.castSucc.castSucc.castSucc (Fin.last (m+2)) z.castSucc.castSucc.castSucc T.castSucc.castSucc.castSucc) := .conjR (.conjR hQ2)
  have hM := SyntaxTopFormulaTyping.instantiate_target_type w.castSucc.castSucc.castSucc z.castSucc.castSucc.castSucc T.castSucc.castSucc.castSucc C.castSucc.castSucc.castSucc P.castSucc.castSucc.castSucc Dm.castSucc.castSucc.castSucc M.castSucc.castSucc.castSucc (by simpa only [old, SyntaxLogicalSyntax.singleCode, SyntaxLogicalSyntax.binaryCode, tag2, Formula.raise, SyntaxTopFormulaSyntax.instantiated_rename] using (under (under (under hiM Q0) Q1) Q2))
  have hBG := ForcingMemberGuardProof.from_member (ZFContext.under (ZFContext.under (ZFContext.under hZ Q0) Q1) Q2) test w.castSucc.castSucc.castSucc z.castSucc.castSucc.castSucc T.castSucc.castSucc.castSucc P.castSucc.castSucc.castSucc V.castSucc.castSucc.castSucc (Fin.last (m+2)) M.castSucc.castSucc.castSucc (by simpa only [old, SyntaxLogicalSyntax.singleCode, SyntaxLogicalSyntax.binaryCode, tag2, Formula.raise, omega_rename] using (under (under (under hw Q0) Q1) Q2)) (by simpa only [old, SyntaxLogicalSyntax.singleCode, SyntaxLogicalSyntax.binaryCode, tag2, Formula.raise, empty_rename] using (under (under (under hz Q0) Q1) Q2)) hB hM (by simpa only [old, SyntaxLogicalSyntax.singleCode, SyntaxLogicalSyntax.binaryCode, tag2, Formula.raise, ForcingMemberGuardOpening.result_rename] using (under (under (under hm Q0) Q1) Q2))
  let Q3 := ForcingMemberGuardProof.body test w.castSucc.castSucc.castSucc z.castSucc.castSucc.castSucc T.castSucc.castSucc.castSucc P.castSucc.castSucc.castSucc V.castSucc.castSucc.castSucc (Fin.last (m+2)) M.castSucc.castSucc.castSucc
  let Δ6 := Context.add Q3 (raisedContext 3 Δ3)
  apply HornBinderRules.eliminate_many 3 Q3 _ hBG
  have hQ3 : Derives Δ6 Q3 := .hyp (Or.inl rfl)
  have map3 {n} (x y : Fin n) : (fun i => (SyntaxAtomSyntax.two x y i).castSucc.castSucc.castSucc) = SyntaxAtomSyntax.two x.castSucc.castSucc.castSucc y.castSucc.castSucc.castSucc := SyntaxAtomSyntax.two_map x y (fun t => t.castSucc.castSucc.castSucc)
  have hr : Derives Δ6 (row (w.castSucc.castSucc.castSucc).castSucc.castSucc.castSucc (z.castSucc.castSucc.castSucc).castSucc.castSucc.castSucc (T.castSucc.castSucc.castSucc).castSucc.castSucc.castSucc (C.castSucc.castSucc.castSucc).castSucc.castSucc.castSucc (P.castSucc.castSucc.castSucc).castSucc.castSucc.castSucc (V.castSucc.castSucc.castSucc).castSucc.castSucc.castSucc (Rest.castSucc.castSucc.castSucc).castSucc.castSucc.castSucc ((Fin.last (m+2))).castSucc.castSucc.castSucc (slot 3 0) (slot 3 1) (slot 3 2) (Dm.castSucc.castSucc.castSucc).castSucc.castSucc.castSucc (Do.castSucc.castSucc.castSucc).castSucc.castSucc.castSucc ((Fin.last m).castSucc.castSucc).castSucc.castSucc.castSucc ((Fin.last (m+1)).castSucc).castSucc.castSucc.castSucc (M.castSucc.castSucc.castSucc).castSucc.castSucc.castSucc (O.castSucc.castSucc.castSucc).castSucc.castSucc.castSucc) := .conjI (.conjL hQ3) (.conjI (by simpa only [old, SyntaxLogicalSyntax.singleCode, SyntaxLogicalSyntax.binaryCode, tag2, Formula.raise, FormulaCodeConstructSyntax.typedAt, SyntaxNodeSyntax.constructor_rename, SyntaxAtomSyntax.two_map, map3] using (HornBinderRules.under_body 3 (.conjL (.conjR hQ2)) Q3)) (.conjI (by simpa only [old, SyntaxLogicalSyntax.singleCode, SyntaxLogicalSyntax.binaryCode, tag2, Formula.raise, FormulaCodeConstructSyntax.typedAt, SyntaxNodeSyntax.constructor_rename] using (HornBinderRules.under_body 3 (under (.conjL (.conjR hQ1)) Q2) Q3)) (.conjI (by simpa only [old, SyntaxLogicalSyntax.singleCode, SyntaxLogicalSyntax.binaryCode, tag2, Formula.raise, FormulaCodeConstructSyntax.typedAt, SyntaxNodeSyntax.constructor_rename, SyntaxAtomSyntax.two_map, map3] using (HornBinderRules.under_body 3 (under (under (.conjL (.conjR hQ0)) Q1) Q2) Q3)) (.conjI (by simpa only [old, SyntaxLogicalSyntax.singleCode, SyntaxLogicalSyntax.binaryCode, tag2, Formula.raise, SyntaxTopFormulaSyntax.instantiated_rename] using (HornBinderRules.under_body 3 (under (under (under hiM Q0) Q1) Q2) Q3)) (.conjI (by simpa only [old, SyntaxLogicalSyntax.singleCode, SyntaxLogicalSyntax.binaryCode, tag2, Formula.raise, SyntaxTopFormulaSyntax.instantiated_rename] using (HornBinderRules.under_body 3 (under (under (under hiO Q0) Q1) Q2) Q3)) (by simpa only [old, SyntaxLogicalSyntax.singleCode, SyntaxLogicalSyntax.binaryCode, tag2, Formula.raise, ForcingMemberGuardOpening.result_rename] using (HornBinderRules.under_body 3 (under (under (under hm Q0) Q1) Q2) Q3)))))))
  have hpO := at_background (HornBinderRules.zf_body 3 (ZFContext.under (ZFContext.under (ZFContext.under hZ Q0) Q1) Q2) Q3) test (w.castSucc.castSucc.castSucc).castSucc.castSucc.castSucc (z.castSucc.castSucc.castSucc).castSucc.castSucc.castSucc (T.castSucc.castSucc.castSucc).castSucc.castSucc.castSucc (C.castSucc.castSucc.castSucc).castSucc.castSucc.castSucc (P.castSucc.castSucc.castSucc).castSucc.castSucc.castSucc (V.castSucc.castSucc.castSucc).castSucc.castSucc.castSucc (Rest.castSucc.castSucc.castSucc).castSucc.castSucc.castSucc ((Fin.last (m+2))).castSucc.castSucc.castSucc (slot 3 0) (slot 3 1) (slot 3 2) (Dm.castSucc.castSucc.castSucc).castSucc.castSucc.castSucc (Do.castSucc.castSucc.castSucc).castSucc.castSucc.castSucc ((Fin.last m).castSucc.castSucc).castSucc.castSucc.castSucc ((Fin.last (m+1)).castSucc).castSucc.castSucc.castSucc (M.castSucc.castSucc.castSucc).castSucc.castSucc.castSucc (O.castSucc.castSucc.castSucc).castSucc.castSucc.castSucc (by simpa only [old, SyntaxLogicalSyntax.singleCode, SyntaxLogicalSyntax.binaryCode, tag2, Formula.raise, omega_rename] using (HornBinderRules.under_body 3 (under (under (under hw Q0) Q1) Q2) Q3)) (by simpa only [old, SyntaxLogicalSyntax.singleCode, SyntaxLogicalSyntax.binaryCode, tag2, Formula.raise, empty_rename] using (HornBinderRules.under_body 3 (under (under (under hz Q0) Q1) Q2) Q3)) hr
  have hout : Derives Δ6 (result test (w.castSucc.castSucc.castSucc).castSucc.castSucc.castSucc (z.castSucc.castSucc.castSucc).castSucc.castSucc.castSucc (T.castSucc.castSucc.castSucc).castSucc.castSucc.castSucc (C.castSucc.castSucc.castSucc).castSucc.castSucc.castSucc (P.castSucc.castSucc.castSucc).castSucc.castSucc.castSucc (V.castSucc.castSucc.castSucc).castSucc.castSucc.castSucc (Rest.castSucc.castSucc.castSucc).castSucc.castSucc.castSucc (M.castSucc.castSucc.castSucc).castSucc.castSucc.castSucc (O.castSucc.castSucc.castSucc).castSucc.castSucc.castSucc (Dm.castSucc.castSucc.castSucc).castSucc.castSucc.castSucc (Do.castSucc.castSucc.castSucc).castSucc.castSucc.castSucc) := by
    apply HornBinderRules.intro_many 6 _ (Fin.cases (((Fin.last m).castSucc.castSucc).castSucc.castSucc.castSucc) (Fin.cases (((Fin.last (m+1)).castSucc).castSucc.castSucc.castSucc) (Fin.cases (((Fin.last (m+2))).castSucc.castSucc.castSucc) (Fin.cases (slot 3 0) (Fin.cases (slot 3 1) (Fin.cases (slot 3 2) (fun e => Fin.elim0 e)))))))
    have hData : Derives Δ6 (data test (w.castSucc.castSucc.castSucc).castSucc.castSucc.castSucc (z.castSucc.castSucc.castSucc).castSucc.castSucc.castSucc (T.castSucc.castSucc.castSucc).castSucc.castSucc.castSucc (C.castSucc.castSucc.castSucc).castSucc.castSucc.castSucc (P.castSucc.castSucc.castSucc).castSucc.castSucc.castSucc (V.castSucc.castSucc.castSucc).castSucc.castSucc.castSucc (Rest.castSucc.castSucc.castSucc).castSucc.castSucc.castSucc (M.castSucc.castSucc.castSucc).castSucc.castSucc.castSucc (O.castSucc.castSucc.castSucc).castSucc.castSucc.castSucc (Dm.castSucc.castSucc.castSucc).castSucc.castSucc.castSucc (Do.castSucc.castSucc.castSucc).castSucc.castSucc.castSucc ((Fin.last m).castSucc.castSucc).castSucc.castSucc.castSucc ((Fin.last (m+1)).castSucc).castSucc.castSucc.castSucc ((Fin.last (m+2))).castSucc.castSucc.castSucc (slot 3 0) (slot 3 1) (slot 3 2)) := .conjI hr (.conjI (.conjR hQ3) hpO)
    exact of_eq (by simp only [body, data_rename, assign_old, assign_slot]; rfl) hData
  exact of_eq (by simp only [Formula.raise, result_rename]; all_goals rfl) hout

private theorem at_diagonal {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1) (Reln : Source.Formula (k+2))
    (w mode z a f T A C R S K H P r s own head i V j Qm Qo Um Uo M O Rest bzero D Dm Do : Fin m)
    (hf : Derives Γ (ForcingMemberGuardOpening.frame w mode z a f T A C R S K H P r s))
    (hh : Derives Γ (SyntaxMixedImageHead.head w A f own head))
    (hcm : Derives Γ (ForcingGuardCode.compiled false Reln w A f head Qm))
    (hco : Derives Γ (ForcingGuardCode.compiled true Reln w A f head Qo))
    (hom : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w K H A f C T Qm Um))
    (hoo : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w K H A f C T Qo Uo))
    (him : Derives Γ (SyntaxTopFormulaSyntax.instantiated w z T C P Um M))
    (hio : Derives Γ (SyntaxTopFormulaSyntax.instantiated w z T C P Uo O))
    (hni : Derives Γ (SyntaxNumeralSyntax.numeral k i))
    (hV : Derives Γ (StructuralListFieldSyntax.field w S i V))
    (_hnj : Derives Γ (SyntaxNumeralSyntax.numeral (k+1) j))
    (hj : Derives Γ (StructuralListFieldSyntax.field w S j P))
    (hRest : Derives Γ (formulaCode w Rest z T))
    (hdm : Derives Γ (ForcingReflexiveImages.diagonalData w z f T A C K H j Qm bzero D Dm))
    (hdo : Derives Γ (ForcingReflexiveImages.diagonalData w z f T A C K H j Qo bzero D Do)) :
    Derives Γ (result test w z T C P V Rest M O Dm Do) := by
  have hiM := ForcingReflexiveDiagram.at_body hZ false Reln w mode z a f T A C R S K H P r s own head j Qm Um M bzero D Dm hf hh hcm hom him hdm hj
  have hiO := ForcingReflexiveDiagram.at_body hZ true Reln w mode z a f T A C R S K H P r s own head j Qo Uo O bzero D Do hf hh hco hoo hio hdo hj
  have hz := Derives.conjL (.conjR (.conjR hf))
  have heq := OmegaUniversal.empty_unique own z (ZFContext.arithmetic hZ).base.extensionality (.conjL hh) hz
  have hx := SyntaxVariableImagePoint.code_subst_index true w own head z heq (.conjL (.conjR hh))
  have hm := ForcingMemberGuardOpening.from_instance hZ Reln w mode z a f T A C R S K H P r s i V head Qm Um M hf hni hx hV hcm hom him
  exact from_bodies hZ test w z T C P V Rest M O Dm Do (.conjL hf) hz hRest hiM hiO hm

/-- Both guards share the SAME internally generated bound head and table.
The result retains actual code origins and internally generated common G. -/
def commonData {m} (test : Formula 1) (w z f T A C K H P V j Qm Qo Rest M O bzero D Dm Do : Fin m) : Formula m :=
  (ForcingReflexiveImages.diagonalData w z f T A C K H j Qm bzero D Dm).conj
    ((ForcingReflexiveImages.diagonalData w z f T A C K H j Qo bzero D Do).conj
      (result test w z T C P V Rest M O Dm Do))

theorem commonData_rename {m l} (test : Formula 1) (w z f T A C K H P V j Qm Qo Rest M O bzero D Dm Do : Fin m) (ρ : Fin m → Fin l) :
    (commonData test w z f T A C K H P V j Qm Qo Rest M O bzero D Dm Do).rename ρ =
      commonData test (ρ w) (ρ z) (ρ f) (ρ T) (ρ A) (ρ C) (ρ K) (ρ H) (ρ P) (ρ V) (ρ j) (ρ Qm) (ρ Qo) (ρ Rest) (ρ M) (ρ O) (ρ bzero) (ρ D) (ρ Dm) (ρ Do) := by
  simp only [commonData, Formula.rename, ForcingReflexiveImages.diagonalData_rename, result_rename]

def commonBody {m} (test : Formula 1) (w z f T A C K H P V j Qm Qo Rest M O : Fin m) : Formula (m+4) :=
  commonData test (old 4 w) (old 4 z) (old 4 f) (old 4 T) (old 4 A) (old 4 C) (old 4 K) (old 4 H) (old 4 P) (old 4 V) (old 4 j) (old 4 Qm) (old 4 Qo) (old 4 Rest) (old 4 M) (old 4 O)
    (slot 4 0) (slot 4 1) (slot 4 2) (slot 4 3)

def common {m} (test : Formula 1) (w z f T A C K H P V j Qm Qo Rest M O : Fin m) : Formula m :=
  existsMany 4 (commonBody test w z f T A C K H P V j Qm Qo Rest M O)

theorem common_rename {m l} (test : Formula 1) (w z f T A C K H P V j Qm Qo Rest M O : Fin m) (ρ : Fin m → Fin l) :
    (common test w z f T A C K H P V j Qm Qo Rest M O).rename ρ =
      common test (ρ w) (ρ z) (ρ f) (ρ T) (ρ A) (ρ C) (ρ K) (ρ H) (ρ P) (ρ V) (ρ j) (ρ Qm) (ρ Qo) (ρ Rest) (ρ M) (ρ O) := by
  simp only [common, existsMany_rename, commonBody, commonData_rename, lift_old, lift_slot]

private theorem at_order_body {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1) (Reln : Source.Formula (k+2))
    (w mode z a f T A C R S K H P r s own head i V j Qm Qo Um Uo M O Rest bzero D Do : Fin m)
    (hf : Derives Γ (ForcingMemberGuardOpening.frame w mode z a f T A C R S K H P r s))
    (hh : Derives Γ (SyntaxMixedImageHead.head w A f own head))
    (hcm : Derives Γ (ForcingGuardCode.compiled false Reln w A f head Qm))
    (hco : Derives Γ (ForcingGuardCode.compiled true Reln w A f head Qo))
    (hom : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w K H A f C T Qm Um))
    (hoo : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w K H A f C T Qo Uo))
    (him : Derives Γ (SyntaxTopFormulaSyntax.instantiated w z T C P Um M))
    (hio : Derives Γ (SyntaxTopFormulaSyntax.instantiated w z T C P Uo O))
    (hni : Derives Γ (SyntaxNumeralSyntax.numeral k i))
    (hV : Derives Γ (StructuralListFieldSyntax.field w S i V))
    (hnj : Derives Γ (SyntaxNumeralSyntax.numeral (k+1) j))
    (hj : Derives Γ (StructuralListFieldSyntax.field w S j P))
    (hRest : Derives Γ (formulaCode w Rest z T))
    (hdo : Derives Γ (ForcingReflexiveImages.diagonalData w z f T A C K H j Qo bzero D Do)) :
    Derives Γ (common test w z f T A C K H P V j Qm Qo Rest M O) := by
  have hl := Derives.conjL (.conjR (.conjR (.conjR (.conjR hf))))
  have hK := Derives.conjL (SyntaxCodedMixedBinderTyping.output_lists w R S a f z T A C K H hl)
  have hD := ForcingReflexiveImages.target_type w f C T H j bzero D (.conjL (.conjR hdo))
  have hQm := ForcingGuardCode.compiled_type false Reln w A f head Qm hcm
  have he := SyntaxMixedFormulaOutputInduction.actual_exists hZ w K D A f C T Qm (.conjL hf) (.conjI hQm (.conjI hK hD))
  let X := SyntaxMixedFormulaJudgmentSyntax.substituted w.castSucc K.castSucc D.castSucc A.castSucc f.castSucc C.castSucc T.castSucc Qm.castSucc (Fin.last m)
  let Δ := Context.add X (Context.image Formula.raise Γ)
  apply Derives.exE (p := X) he
  have hX : Derives Δ X := .hyp (Or.inl rfl)
  have hdo1 : Derives Δ (ForcingReflexiveImages.diagonalData w.castSucc z.castSucc f.castSucc T.castSucc A.castSucc C.castSucc K.castSucc H.castSucc j.castSucc Qo.castSucc bzero.castSucc D.castSucc Do.castSucc) :=
    of_eq (ForcingReflexiveImages.diagonalData_rename w z f T A C K H j Qo bzero D Do Fin.castSucc) (under hdo X)
  have hdm1 : Derives Δ (ForcingReflexiveImages.diagonalData w.castSucc z.castSucc f.castSucc T.castSucc A.castSucc C.castSucc K.castSucc H.castSucc j.castSucc Qm.castSucc bzero.castSucc D.castSucc (Fin.last m)) :=
    .conjI (.conjL hdo1) (.conjI (.conjL (.conjR hdo1)) hX)
  have hp := at_diagonal (ZFContext.under hZ X) test Reln
    w.castSucc mode.castSucc z.castSucc a.castSucc f.castSucc T.castSucc A.castSucc C.castSucc R.castSucc S.castSucc K.castSucc H.castSucc P.castSucc r.castSucc s.castSucc own.castSucc head.castSucc i.castSucc V.castSucc j.castSucc Qm.castSucc Qo.castSucc Um.castSucc Uo.castSucc M.castSucc O.castSucc Rest.castSucc bzero.castSucc D.castSucc (Fin.last m) Do.castSucc
    (by simpa only [Formula.raise, ForcingMemberGuardOpening.frame_rename] using (under hf X))
    (by simpa only [Formula.raise, SyntaxMixedImageHead.head_rename] using (under hh X))
    (by simpa only [Formula.raise, ForcingGuardCode.compiled_rename] using (under hcm X))
    (by simpa only [Formula.raise, ForcingGuardCode.compiled_rename] using (under hco X))
    (by simpa only [Formula.raise, SyntaxMixedFormulaJudgmentSyntax.substituted_rename] using (under hom X))
    (by simpa only [Formula.raise, SyntaxMixedFormulaJudgmentSyntax.substituted_rename] using (under hoo X))
    (by simpa only [Formula.raise, SyntaxTopFormulaSyntax.instantiated_rename] using (under him X))
    (by simpa only [Formula.raise, SyntaxTopFormulaSyntax.instantiated_rename] using (under hio X))
    (by simpa only [Formula.raise, SyntaxNumeralSyntax.numeral_rename] using (under hni X))
    (by simpa only [Formula.raise, StructuralListFieldSyntax.field_rename] using (under hV X))
    (by simpa only [Formula.raise, SyntaxNumeralSyntax.numeral_rename] using (under hnj X))
    (by simpa only [Formula.raise, StructuralListFieldSyntax.field_rename] using (under hj X))
    (by simpa only [Formula.raise, formulaCode_rename] using (under hRest X))
    hdm1 hdo1
  have hout : Derives Δ (common test w.castSucc z.castSucc f.castSucc T.castSucc A.castSucc C.castSucc K.castSucc H.castSucc P.castSucc V.castSucc j.castSucc Qm.castSucc Qo.castSucc Rest.castSucc M.castSucc O.castSucc) := by
    apply HornBinderRules.intro_many 4 _ (Fin.cases (bzero.castSucc) (Fin.cases (D.castSucc) (Fin.cases (Fin.last m) (Fin.cases (Do.castSucc) (fun e => Fin.elim0 e)))))
    have hd : Derives Δ (commonData test w.castSucc z.castSucc f.castSucc T.castSucc A.castSucc C.castSucc K.castSucc H.castSucc P.castSucc V.castSucc j.castSucc Qm.castSucc Qo.castSucc Rest.castSucc M.castSucc O.castSucc bzero.castSucc D.castSucc (Fin.last m) Do.castSucc) := .conjI hdm1 (.conjI hdo1 hp)
    exact of_eq (by simp only [commonBody, commonData_rename, assign_old, assign_slot]; rfl) hd
  exact of_eq (common_rename test w z f T A C K H P V j Qm Qo Rest M O Fin.castSucc).symm hout

/-- Full ACTUAL original source consumer. Both guard bodies, the common
replacement table, guarded reflexivity row, common background and BOTH original
internal proofs are generated. Only original compiler/opening/native-instance
judgments, selected parameter fields and Rest typing are supplied. -/
theorem from_instances {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1) (Reln : Source.Formula (k+2))
    (w mode z a f T A C R S K H P r s own head i V j Qm Qo Um Uo M O Rest : Fin m)
    (hf : Derives Γ (ForcingMemberGuardOpening.frame w mode z a f T A C R S K H P r s))
    (hh : Derives Γ (SyntaxMixedImageHead.head w A f own head))
    (hcm : Derives Γ (ForcingGuardCode.compiled false Reln w A f head Qm))
    (hco : Derives Γ (ForcingGuardCode.compiled true Reln w A f head Qo))
    (hom : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w K H A f C T Qm Um))
    (hoo : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w K H A f C T Qo Uo))
    (him : Derives Γ (SyntaxTopFormulaSyntax.instantiated w z T C P Um M))
    (hio : Derives Γ (SyntaxTopFormulaSyntax.instantiated w z T C P Uo O))
    (hni : Derives Γ (SyntaxNumeralSyntax.numeral k i))
    (hV : Derives Γ (StructuralListFieldSyntax.field w S i V))
    (hnj : Derives Γ (SyntaxNumeralSyntax.numeral (k+1) j))
    (hj : Derives Γ (StructuralListFieldSyntax.field w S j P))
    (hRest : Derives Γ (formulaCode w Rest z T)) :
    Derives Γ (common test w z f T A C K H P V j Qm Qo Rest M O) := by
  have he := ForcingReflexiveImages.from_compiled hZ true Reln w mode z a f T A C R S K H P r s j head Qo hf hco
  let Q := ForcingReflexiveImages.diagonalBody w z f T A C K H j Qo
  let Δ := Context.add Q (raisedContext 3 Γ)
  apply HornBinderRules.eliminate_many 3 Q _ he
  have hQ : Derives Δ Q := .hyp (Or.inl rfl)
  have hp := at_order_body (HornBinderRules.zf_body 3 hZ Q) test Reln
    (old 3 w) (old 3 mode) (old 3 z) (old 3 a) (old 3 f) (old 3 T) (old 3 A) (old 3 C) (old 3 R) (old 3 S) (old 3 K) (old 3 H) (old 3 P) (old 3 r) (old 3 s) (old 3 own) (old 3 head) (old 3 i) (old 3 V) (old 3 j) (old 3 Qm) (old 3 Qo) (old 3 Um) (old 3 Uo) (old 3 M) (old 3 O) (old 3 Rest) (slot 3 0) (slot 3 1) (slot 3 2)
    (by simpa only [ForcingMemberGuardOpening.frame_rename] using (HornBinderRules.under_body 3 hf Q))
    (by simpa only [SyntaxMixedImageHead.head_rename] using (HornBinderRules.under_body 3 hh Q))
    (by simpa only [ForcingGuardCode.compiled_rename] using (HornBinderRules.under_body 3 hcm Q))
    (by simpa only [ForcingGuardCode.compiled_rename] using (HornBinderRules.under_body 3 hco Q))
    (by simpa only [SyntaxMixedFormulaJudgmentSyntax.substituted_rename] using (HornBinderRules.under_body 3 hom Q))
    (by simpa only [SyntaxMixedFormulaJudgmentSyntax.substituted_rename] using (HornBinderRules.under_body 3 hoo Q))
    (by simpa only [SyntaxTopFormulaSyntax.instantiated_rename] using (HornBinderRules.under_body 3 him Q))
    (by simpa only [SyntaxTopFormulaSyntax.instantiated_rename] using (HornBinderRules.under_body 3 hio Q))
    (by simpa only [SyntaxNumeralSyntax.numeral_rename] using (HornBinderRules.under_body 3 hni Q))
    (by simpa only [StructuralListFieldSyntax.field_rename] using (HornBinderRules.under_body 3 hV Q))
    (by simpa only [SyntaxNumeralSyntax.numeral_rename] using (HornBinderRules.under_body 3 hnj Q))
    (by simpa only [StructuralListFieldSyntax.field_rename] using (HornBinderRules.under_body 3 hj Q))
    (by simpa only [formulaCode_rename] using (HornBinderRules.under_body 3 hRest Q))
    hQ
  exact of_eq (common_rename test w z f T A C K H P V j Qm Qo Rest M O (old 3)).symm hp

def input {k m} (Reln : Source.Formula (k+2)) (w mode z a f T A C R S K H P r s own head i V j Qm Qo Um Uo M O Rest : Fin m) : Formula m :=
  (ForcingMemberGuardOpening.frame w mode z a f T A C R S K H P r s).conj ((SyntaxMixedImageHead.head w A f own head).conj ((ForcingGuardCode.compiled false Reln w A f head Qm).conj ((ForcingGuardCode.compiled true Reln w A f head Qo).conj ((SyntaxMixedFormulaJudgmentSyntax.substituted w K H A f C T Qm Um).conj ((SyntaxMixedFormulaJudgmentSyntax.substituted w K H A f C T Qo Uo).conj ((SyntaxTopFormulaSyntax.instantiated w z T C P Um M).conj ((SyntaxTopFormulaSyntax.instantiated w z T C P Uo O).conj ((SyntaxNumeralSyntax.numeral k i).conj ((StructuralListFieldSyntax.field w S i V).conj ((SyntaxNumeralSyntax.numeral (k+1) j).conj ((StructuralListFieldSyntax.field w S j P).conj (formulaCode w Rest z T))))))))))))

def sentence {k m} (test : Formula 1) (Reln : Source.Formula (k+2)) (w mode z a f T A C R S K H P r s own head i V j Qm Qo Um Uo M O Rest : Fin m) : Source.Sentence :=
  ((input Reln w mode z a f T A C R S K H P r s own head i V j Qm Qo Um Uo M O Rest).imp (common test w z f T A C K H P V j Qm Qo Rest M O)).close

theorem kernel_certificate {k m} (test : Formula 1) (Reln : Source.Formula (k+2)) (w mode z a f T A C R S K H P r s own head i V j Qm Qo Um Uo M O Rest : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (sentence test Reln w mode z a f T A C R S K H P r s own head i V j Qm Qo Um Uo M O Rest)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  let E := input Reln w mode z a f T A C R S K H P r s own head i V j Qm Qo Um Uo M O Rest
  let Γ := Context.add E (Source.SetLanguage.ZF.at m)
  have h : Derives Γ E := .hyp (Or.inl rfl)
  apply from_instances (ZFContext.add (ZFContext.source_ZF m) E) test Reln w mode z a f T A C R S K H P r s own head i V j Qm Qo Um Uo M O Rest
    (.conjL h)
    (.conjL (.conjR h))
    (.conjL (.conjR (.conjR h)))
    (.conjL (.conjR (.conjR (.conjR h))))
    (.conjL (.conjR (.conjR (.conjR (.conjR h)))))
    (.conjL (.conjR (.conjR (.conjR (.conjR (.conjR h))))))
    (.conjL (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR h)))))))
    (.conjL (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR h))))))))
    (.conjL (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR h)))))))))
    (.conjL (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR h))))))))))
    (.conjL (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR h)))))))))))
    (.conjL (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR h))))))))))))
    (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR h))))))))))))

end PPAC.Migration.ForcingRelationGuardProof
