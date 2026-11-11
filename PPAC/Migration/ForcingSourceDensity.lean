import PPAC.Migration.ForcingDensityGuards
import PPAC.Migration.ForcingSourceDensityConstant

/-! The conjunction branch of the original force_of_dense. The two child
hypotheses quantify over actual density compiler and mixed substitution
outputs, and their conclusions are combined with the original conjunction
constructor in the same conditional Root context. -/
namespace PPAC.Migration.ForcingSourceDensity
open Internal Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)
open FormulaCodeSyntax (formulaCode formulaCode_rename)
open SyntaxLogicalSyntax (binaryCode binaryCode_rename)
open SyntaxMixedFormulaJudgmentSyntax (substituted substituted_rename)
open InternalProofBackground (implication implication_rename)
open NativeProofQuotation (eliminate_objects)
set_option maxRecDepth 16384
set_option maxHeartbeats 1600000
attribute [local irreducible] NaturalRecursionSyntax.matrix

private abbrev test : Formula 1 := OriginalAxiomCodeTest.test false

private def point {k m} (Reln : Formula (k+2)) (w z a A B f b j R S G N D H Y : Fin m) : Formula m :=
  ((ForcingDensityCode.compiled Reln w a A B f j N D).conj
    ((substituted w R S a f z b D H).conj ((substituted w R S a f z b N Y).conj
      (implication test w z b G H)))).imp (implication test w z b G Y)

private theorem point_rename {k m l} (Reln : Formula (k+2)) (w z a A B f b j R S G N D H Y : Fin m)
    (r : Fin m → Fin l) :
    (point Reln w z a A B f b j R S G N D H Y).rename r =
      point Reln (r w) (r z) (r a) (r A) (r B) (r f) (r b) (r j) (r R) (r S) (r G) (r N) (r D) (r H) (r Y) := by
  simp only [point, Formula.rename, ForcingDensityCode.compiled_rename, substituted_rename, implication_rename]

private def body {k m} (Reln : Formula (k+2)) (w z a A B f b j R S G N : Fin m) : Formula (m+3) :=
  point Reln (old 3 w) (old 3 z) (old 3 a) (old 3 A) (old 3 B) (old 3 f) (old 3 b) (old 3 j)
    (old 3 R) (old 3 S) (old 3 G) (old 3 N) (slot 3 0) (slot 3 1) (slot 3 2)

/-- At a fixed actual compiled forcing code, quantify over all density
compilations and both corresponding query outputs. -/
def transfer {k m} (Reln : Formula (k+2)) (w z a A B f b j R S G N : Fin m) : Formula m :=
  OriginalUniversalBlock.allMany 3 (body Reln w z a A B f b j R S G N)

theorem transfer_rename {k m l} (Reln : Formula (k+2)) (w z a A B f b j R S G N : Fin m)
    (r : Fin m → Fin l) :
    (transfer Reln w z a A B f b j R S G N).rename r =
      transfer Reln (r w) (r z) (r a) (r A) (r B) (r f) (r b) (r j) (r R) (r S) (r G) (r N) := by
  simp only [transfer, OriginalUniversalBlock.allMany_rename, body, point_rename, lift_old, lift_slot]

theorem apply_transfer {k m} {Γ : Context m} (Reln : Formula (k+2))
    (w z a A B f b j R S G N D H Y : Fin m)
    (hi : Derives Γ (transfer Reln w z a A B f b j R S G N))
    (hD : Derives Γ (ForcingDensityCode.compiled Reln w a A B f j N D))
    (hH : Derives Γ (substituted w R S a f z b D H))
    (hY : Derives Γ (substituted w R S a f z b N Y))
    (hp : Derives Γ (implication test w z b G H)) :
    Derives Γ (implication test w z b G Y) := by
  let outputs : Fin 3 → Fin m := Fin.cases D (SyntaxAtomSyntax.two H Y)
  have h : Derives Γ (point Reln w z a A B f b j R S G N D H Y) :=
    of_eq (by simp only [body, point_rename, assign_old, assign_slot]; rfl)
      (OriginalUniversalBlock.at_many 3 _ outputs hi)
  exact .impE h (.conjI hD (.conjI hH (.conjI hY hp)))

private theorem intro_transfer {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (Reln : Formula (k+2)) (w z a A B f b j R S G N : Fin m)
    (use : ∀ {l} {Δ : Context l} (r : Fin m → Fin l) (D H Y : Fin l), ZFContext.Evidence Δ →
      (∀ {F : Formula m}, Derives Γ F → Derives Δ (F.rename r)) →
      Derives Δ (ForcingDensityCode.compiled Reln (r w) (r a) (r A) (r B) (r f) (r j) (r N) D) →
      Derives Δ (substituted (r w) (r R) (r S) (r a) (r f) (r z) (r b) D H) →
      Derives Δ (substituted (r w) (r R) (r S) (r a) (r f) (r z) (r b) (r N) Y) →
      Derives Δ (implication test (r w) (r z) (r b) (r G) H) →
      Derives Δ (implication test (r w) (r z) (r b) (r G) Y)) :
    Derives Γ (transfer Reln w z a A B f b j R S G N) := by
  apply OriginalUniversalBlock.intro_many 3
  apply Derives.impI
  let r : Fin m → Fin (m+3) := old 3
  let D : Fin (m+3) := slot 3 0
  let H : Fin (m+3) := slot 3 1
  let Y : Fin (m+3) := slot 3 2
  let E := (ForcingDensityCode.compiled Reln (r w) (r a) (r A) (r B) (r f) (r j) (r N) D).conj
    ((substituted (r w) (r R) (r S) (r a) (r f) (r z) (r b) D H).conj
      ((substituted (r w) (r R) (r S) (r a) (r f) (r z) (r b) (r N) Y).conj
        (implication test (r w) (r z) (r b) (r G) H)))
  have hE : Derives (Context.add E (raisedContext 3 Γ)) E := .hyp (Or.inl rfl)
  exact use r D H Y (HornBinderRules.zf_body 3 hZ E) (fun h => HornBinderRules.under_body 3 h E)
    (.conjL hE) (.conjL (.conjR hE)) (.conjL (.conjR (.conjR hE))) (.conjR (.conjR (.conjR hE)))

private theorem child_at_queries {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (Reln : Formula (k+2)) (right : Bool) (w z a A B f b j R S G N X Y D H U V : Fin m)
    (d : Fin 7 → Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hA : Derives Γ (successor A a)) (hB : Derives Γ (successor B A))
    (hN : Derives Γ (formulaCode w N a f)) (hG : Derives Γ (formulaCode w G z b))
    (hPair : Derives Γ (binaryCode 0 w X Y N))
    (hData : Derives Γ (ForcingDensityCode.data Reln w a A B f j N D d))
    (hH : Derives Γ (substituted w R S a f z b D H))
    (hp : Derives Γ (implication test w z b G H))
    (hi : Derives Γ (transfer Reln w z a A B f b j R S G (if right then Y else X)))
    (hF : Derives Γ (substituted w R S a f z b (if right then Y else X) (if right then V else U))) :
    Derives Γ (implication test w z b G (if right then V else U)) := by
  let C := if right then Y else X
  let P := if right then V else U
  refine ForcingDensityGuards.with_conjunct_density_proof hZ Reln right w z a A B f b j R S N X Y D H G d
    hw hz hA hB hN hG hPair hData hH hp (implication test w z b G P) ?_
  intro l Δ r D' H' c hZ1 lift hData' hH' hp'
  have hD' : Derives Δ (ForcingDensityCode.compiled Reln (r w) (r a) (r A) (r B) (r f) (r j) (r C) D') := by
    apply HornBinderRules.intro_many 7 (ForcingDensityCode.body Reln _ _ _ _ _ _ _ _) c
    exact of_eq (by simp only [ForcingDensityCode.body, ForcingDensityCode.data_rename, assign_old, assign_slot, C]) hData'
  exact of_eq (implication_rename test w z b G P r).symm
    (apply_transfer Reln (r w) (r z) (r a) (r A) (r B) (r f) (r b) (r j) (r R) (r S) (r G) (r C) D' H' (r P)
      (of_eq (transfer_rename _ _ _ _ _ _ _ _ _ _ _ _ _ r) (lift hi)) hD' hH'
      (of_eq (substituted_rename _ _ _ _ _ _ _ _ _ _) (lift hF)) hp')

private theorem conjunction_at_record {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (Reln : Formula (k+2)) (w z a A B f b j R S G N X Y D H Z : Fin m)
    (d : Fin 7 → Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hA : Derives Γ (successor A a)) (hB : Derives Γ (successor B A))
    (hG : Derives Γ (formulaCode w G z b))
    (hPair : Derives Γ (binaryCode 0 w X Y N))
    (hData : Derives Γ (ForcingDensityCode.data Reln w a A B f j N D d))
    (hH : Derives Γ (substituted w R S a f z b D H))
    (hZQ : Derives Γ (substituted w R S a f z b N Z))
    (hp : Derives Γ (implication test w z b G H))
    (hiX : Derives Γ (transfer Reln w z a A B f b j R S G X))
    (hiY : Derives Γ (transfer Reln w z a A B f b j R S G Y)) :
    Derives Γ (implication test w z b G Z) := by
  have hN := Derives.conjL (SyntaxMixedFormulaOutput.input_of_substituted hZ w R S a f z b N Z hw hZQ)
  have hXY := ForcingFormulaDiagram.binary_output hZ 0 w R S a f z b N X Y Z hw hPair hZQ
  refine eliminate_objects hZ 2 (fun r v => ForcingFormulaDiagram.binaryData 0
    (r w) (r R) (r S) (r a) (r f) (r z) (r b) (r X) (r Y) (r Z) (v 0) (v 1))
    hXY (implication test w z b G Z) ?_
  intro l Δ r v hZ1 lift h
  have hw1 := of_eq (omega_rename _ _) (lift hw)
  have hz1 := of_eq (empty_rename _ _) (lift hz)
  have hG1 := of_eq (formulaCode_rename _ _ _ _ _) (lift hG)
  have hX := Derives.conjL (.conjR h)
  have hY := Derives.conjR (.conjR h)
  have child (right : Bool)
      (hi : Derives Γ (transfer Reln w z a A B f b j R S G (if right then Y else X)))
      (hq : Derives Δ (substituted (r w) (r R) (r S) (r a) (r f) (r z) (r b)
        (if right then r Y else r X) (if right then v 1 else v 0))) :
      Derives Δ (implication test (r w) (r z) (r b) (r G) (if right then v 1 else v 0)) := by
    have hi1 : Derives Δ (transfer Reln (r w) (r z) (r a) (r A) (r B) (r f) (r b)
        (r j) (r R) (r S) (r G) (if right then r Y else r X)) := by
      cases right <;> exact of_eq (transfer_rename _ _ _ _ _ _ _ _ _ _ _ _ _ r) (lift hi)
    exact child_at_queries hZ1 Reln right (r w) (r z) (r a) (r A) (r B) (r f) (r b) (r j) (r R) (r S)
      (r G) (r N) (r X) (r Y) (r D) (r H) (v 0) (v 1) (r ∘ d) hw1 hz1
      (of_eq (successor_rename _ _ _) (lift hA)) (of_eq (successor_rename _ _ _) (lift hB))
      (of_eq (formulaCode_rename _ _ _ _ _) (lift hN)) hG1 (of_eq (binaryCode_rename _ _ _ _ _ _) (lift hPair))
      (of_eq (ForcingDensityCode.data_rename _ _ _ _ _ _ _ _ _ _ r) (lift hData))
      (of_eq (substituted_rename _ _ _ _ _ _ _ _ _ _) (lift hH))
      (of_eq (implication_rename _ _ _ _ _ _ _) (lift hp)) hi1 hq
  exact of_eq (implication_rename test w z b G Z r).symm
    (ForcingProofContext.join hZ1 test (r w) (r z) (r b) (r G) (v 0) (v 1) (r Z) hw1 hz1 hG1
      (SyntaxMixedFormulaJudgment.target_type _ _ _ _ _ _ _ _ _ hX)
      (SyntaxMixedFormulaJudgment.target_type _ _ _ _ _ _ _ _ _ hY) (.conjL h)
      (child false hiX hX) (child true hiY hY))


private theorem conjunction_from_compiled {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (Reln : Formula (k+2)) (w z a A B f b j R S G N X Y D H Z : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hA : Derives Γ (successor A a)) (hB : Derives Γ (successor B A))
    (hG : Derives Γ (formulaCode w G z b))
    (hPair : Derives Γ (binaryCode 0 w X Y N))
    (hD : Derives Γ (ForcingDensityCode.compiled Reln w a A B f j N D))
    (hH : Derives Γ (substituted w R S a f z b D H))
    (hZQ : Derives Γ (substituted w R S a f z b N Z))
    (hp : Derives Γ (implication test w z b G H))
    (hiX : Derives Γ (transfer Reln w z a A B f b j R S G X))
    (hiY : Derives Γ (transfer Reln w z a A B f b j R S G Y)) :
    Derives Γ (implication test w z b G Z) := by
  refine eliminate_objects hZ 7 (fun r d => ForcingDensityCode.data Reln
    (r w) (r a) (r A) (r B) (r f) (r j) (r N) (r D) d) hD (implication test w z b G Z) ?_
  intro l Δ r d hZ1 lift hData
  exact of_eq (implication_rename test w z b G Z r).symm
    (conjunction_at_record hZ1 Reln (r w) (r z) (r a) (r A) (r B) (r f) (r b) (r j)
      (r R) (r S) (r G) (r N) (r X) (r Y) (r D) (r H) (r Z) d
      (of_eq (omega_rename _ _) (lift hw)) (of_eq (empty_rename _ _) (lift hz))
      (of_eq (successor_rename _ _ _) (lift hA)) (of_eq (successor_rename _ _ _) (lift hB))
      (of_eq (formulaCode_rename _ _ _ _ _) (lift hG)) (of_eq (binaryCode_rename _ _ _ _ _ _) (lift hPair))
      hData (of_eq (substituted_rename _ _ _ _ _ _ _ _ _ _) (lift hH))
      (of_eq (substituted_rename _ _ _ _ _ _ _ _ _ _) (lift hZQ))
      (of_eq (implication_rename _ _ _ _ _ _ _) (lift hp))
      (of_eq (transfer_rename _ _ _ _ _ _ _ _ _ _ _ _ _ r) (lift hiX))
      (of_eq (transfer_rename _ _ _ _ _ _ _ _ _ _ _ _ _ r) (lift hiY)))

/-- The object-language induction step for the original conjunction branch.
The two premises are universally quantified object induction hypotheses. -/
theorem conjunction {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (Reln : Formula (k+2)) (w z a A B f b j R S G N X Y : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hA : Derives Γ (successor A a)) (hB : Derives Γ (successor B A))
    (hG : Derives Γ (formulaCode w G z b))
    (hPair : Derives Γ (binaryCode 0 w X Y N))
    (hiX : Derives Γ (transfer Reln w z a A B f b j R S G X))
    (hiY : Derives Γ (transfer Reln w z a A B f b j R S G Y)) :
    Derives Γ (transfer Reln w z a A B f b j R S G N) := by
  refine intro_transfer hZ Reln w z a A B f b j R S G N ?_
  intro l Δ r D H Z hZ1 lift hD hH hZQ hp
  exact conjunction_from_compiled hZ1 Reln (r w) (r z) (r a) (r A) (r B)
    (r f) (r b) (r j) (r R) (r S) (r G) (r N) (r X) (r Y) D H Z
    (of_eq (omega_rename _ _) (lift hw)) (of_eq (empty_rename _ _) (lift hz))
    (of_eq (successor_rename _ _ _) (lift hA)) (of_eq (successor_rename _ _ _) (lift hB))
    (of_eq (formulaCode_rename _ _ _ _ _) (lift hG)) (of_eq (binaryCode_rename _ _ _ _ _ _) (lift hPair))
    hD hH hZQ hp
    (of_eq (transfer_rename _ _ _ _ _ _ _ _ _ _ _ _ _ r) (lift hiX))
    (of_eq (transfer_rename _ _ _ _ _ _ _ _ _ _ _ _ _ r) (lift hiY))

/-- Density transfer on every genuine forcing compiler output of the same
source formula code. The typing premise is also an object formula. -/
def atSource {k m} (Reln : Formula (k+2)) (Dom : Formula (k+1))
    (w z a A B f b j R S G n : Fin m) : Formula m :=
  (formulaCode w n a z).imp (.all
    ((ForcingCodeRecursion.compiled Reln Dom w.castSucc z.castSucc f.castSucc j.castSucc
      a.castSucc n.castSucc (Fin.last m)).imp
      (transfer Reln w.castSucc z.castSucc a.castSucc A.castSucc B.castSucc f.castSucc
        b.castSucc j.castSucc R.castSucc S.castSucc G.castSucc (Fin.last m))))

theorem atSource_rename {k m l} (Reln : Formula (k+2)) (Dom : Formula (k+1))
    (w z a A B f b j R S G n : Fin m) (r : Fin m → Fin l) :
    (atSource Reln Dom w z a A B f b j R S G n).rename r =
      atSource Reln Dom (r w) (r z) (r a) (r A) (r B) (r f) (r b) (r j) (r R) (r S) (r G) (r n) := by
  simp only [atSource, Formula.rename, formulaCode_rename, ForcingCodeRecursion.compiled_rename, transfer_rename,
    Formula.liftRen, Fin.lastCases_castSucc, Fin.lastCases_last]

def below {k m} (Reln : Formula (k+2)) (Dom : Formula (k+1))
    (w z a A B f b j R S G n : Fin m) : Formula m := .all
  ((Formula.mem (Fin.last m) w.castSucc).imp ((Formula.mem (Fin.last m) n.castSucc).imp
    (atSource Reln Dom w.castSucc z.castSucc a.castSucc A.castSucc B.castSucc f.castSucc b.castSucc
      j.castSucc R.castSucc S.castSucc G.castSucc (Fin.last m))))

theorem below_rename {k m l} (Reln : Formula (k+2)) (Dom : Formula (k+1))
    (w z a A B f b j R S G n : Fin m) (r : Fin m → Fin l) :
    (below Reln Dom w z a A B f b j R S G n).rename r =
      below Reln Dom (r w) (r z) (r a) (r A) (r B) (r f) (r b) (r j) (r R) (r S) (r G) (r n) := by
  simp only [below, Formula.rename, atSource_rename, Formula.liftRen, Fin.lastCases_castSucc, Fin.lastCases_last]

private theorem below_at {k m} {Γ : Context m} (Reln : Formula (k+2)) (Dom : Formula (k+1))
    (w z a A B f b j R S G n x X : Fin m)
    (hi : Derives Γ (below Reln Dom w z a A B f b j R S G n))
    (hx : Derives Γ (.mem x n)) (ht : Derives Γ (formulaCode w x a z))
    (hX : Derives Γ (ForcingCodeRecursion.compiled Reln Dom w z f j a x X)) :
    Derives Γ (transfer Reln w z a A B f b j R S G X) := by
  have hStep : Derives Γ ((Formula.mem x w).imp ((Formula.mem x n).imp (atSource Reln Dom w z a A B f b j R S G x))) :=
    of_eq (by simp only [Formula.instantiate, Formula.rename, atSource_rename, Fin.lastCases_castSucc,
      Fin.lastCases_last, id_eq]) (Derives.allE x hi)
  have h := Derives.impE (.impE (.impE hStep (.conjL (FormulaCodeProperties.guards w x a z ht))) hx) ht
  have hiX : Derives Γ ((ForcingCodeRecursion.compiled Reln Dom w z f j a x X).imp
      (transfer Reln w z a A B f b j R S G X)) :=
    of_eq (by simp only [Formula.instantiate, Formula.rename, ForcingCodeRecursion.compiled_rename, transfer_rename,
      Fin.lastCases_castSucc, Fin.lastCases_last, id_eq]) (Derives.allE X h)
  exact .impE hiX hX

/-- Use the two actual lower source codes in the original conjunction compiler
step and consume the object induction hypothesis at each of them. -/
theorem conjunction_step {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (Reln : Formula (k+2)) (Dom : Formula (k+1)) (w z a A B C f b j R S G h n Q : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hA : Derives Γ (successor A a)) (hB : Derives Γ (successor B A))
    (hG : Derives Γ (formulaCode w G z b)) (hn : Derives Γ (OrdinalSyntax.ordinal n))
    (hh : Derives Γ (ForcingCodeRecursion.graph Reln Dom w z f j h n))
    (hi : Derives Γ (below Reln Dom w z a A B f b j R S G n))
    (hc : Derives Γ (ForcingCodeStep.binary 0 Reln w z f j a A B C h n Q)) :
    Derives Γ (transfer Reln w z a A B f b j R S G Q) := by
  refine eliminate_objects hZ 4 (fun r v => ForcingCodeStep.binaryData 0 Reln (r w) (r z) (r f) (r j)
    (r a) (r A) (r B) (r C) (r h) (r n) (r Q) (v 0) (v 1) (v 2) (v 3)) hc
    (transfer Reln w z a A B f b j R S G Q) ?_
  intro l Δ r v hZ1 lift hd
  have hx := Derives.conjL (.conjR (.conjL hd))
  have hy := Derives.conjL (.conjR (.conjR (.conjL hd)))
  have hLower := of_eq (below_rename Reln Dom _ _ _ _ _ _ _ _ _ _ _ _ r) (lift hi)
  have hn1 := of_eq (OrdinalSyntax.ordinal_rename n r) (lift hn)
  have hGraph := of_eq (ForcingCodeRecursion.graph_rename Reln Dom w z f j h n r) (lift hh)
  have hLeft := ForcingCodeRecursion.read_to_compiled hZ1 Reln Dom (r w) (r z) (r f) (r j) (r h) (r n) (r a)
    (v 0) (v 2) hn1 hx hGraph (.conjL (.conjR hd))
  have hRight := ForcingCodeRecursion.read_to_compiled hZ1 Reln Dom (r w) (r z) (r f) (r j) (r h) (r n) (r a)
    (v 1) (v 3) hn1 hy hGraph (.conjL (.conjR (.conjR hd)))
  have left := below_at Reln Dom (r w) (r z) (r a) (r A) (r B) (r f) (r b) (r j) (r R) (r S) (r G) (r n)
    (v 0) (v 2) hLower hx (.conjL (.conjR (.conjR (.conjR (.conjL hd))))) hLeft
  have right := below_at Reln Dom (r w) (r z) (r a) (r A) (r B) (r f) (r b) (r j) (r R) (r S) (r G) (r n)
    (v 1) (v 3) hLower hy (.conjR (.conjR (.conjR (.conjR (.conjL hd))))) hRight
  exact of_eq (transfer_rename Reln w z a A B f b j R S G Q r).symm
    (conjunction hZ1 Reln (r w) (r z) (r a) (r A) (r B) (r f) (r b) (r j) (r R) (r S) (r G) (r Q)
      (v 2) (v 3) (of_eq (omega_rename _ _) (lift hw)) (of_eq (empty_rename _ _) (lift hz))
      (of_eq (successor_rename _ _ _) (lift hA)) (of_eq (successor_rename _ _ _) (lift hB))
      (of_eq (formulaCode_rename _ _ _ _ _) (lift hG)) (.conjL (.conjR (.conjR (.conjR hd)))) left right)


private def conjunctionInput {k m} (Reln : Formula (k+2)) (Dom : Formula (k+1))
    (w z a A B C f b j R S G h n Q : Fin m) : Formula m :=
  (omega w).conj ((empty z).conj ((successor A a).conj ((successor B A).conj ((formulaCode w G z b).conj
    ((OrdinalSyntax.ordinal n).conj ((ForcingCodeRecursion.graph Reln Dom w z f j h n).conj
      ((below Reln Dom w z a A B f b j R S G n).conj (ForcingCodeStep.binary 0 Reln w z f j a A B C h n Q))))))))

def conjunctionSentence {k m} (Reln : Formula (k+2)) (Dom : Formula (k+1))
    (w z a A B C f b j R S G h n Q : Fin m) : Source.Sentence :=
  ((conjunctionInput Reln Dom w z a A B C f b j R S G h n Q).imp
    (transfer Reln w z a A B f b j R S G Q)).close

theorem conjunction_kernel_certificate {k m} (Reln : Formula (k+2)) (Dom : Formula (k+1))
    (w z a A B C f b j R S G h n Q : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
      (Translation.sentence (conjunctionSentence Reln Dom w z a A B C f b j R S G h n Q)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  let E := conjunctionInput Reln Dom w z a A B C f b j R S G h n Q
  have hE : Derives (Context.add E (Source.SetLanguage.ZF.at m)) E := .hyp (Or.inl rfl)
  have e1 := Derives.conjR hE
  have e2 := Derives.conjR e1
  have e3 := Derives.conjR e2
  have e4 := Derives.conjR e3
  have e5 := Derives.conjR e4
  have e6 := Derives.conjR e5
  have e7 := Derives.conjR e6
  exact conjunction_step (ZFContext.add (ZFContext.source_ZF m) E) Reln Dom w z a A B C f b j R S G h n Q
    (.conjL hE) (.conjL e1) (.conjL e2) (.conjL e3) (.conjL e4) (.conjL e5) (.conjL e6) (.conjL e7) (.conjR e7)

section Constants

open SyntaxNumeralSyntax (numeral numeral_rename)
open ForcingReflexiveImages (replacement replacement_rename)
open StructuralListFieldSyntax (field field_rename)

theorem truth_step {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (Reln : Formula (k+2)) (Dom : Formula (k+1)) (w z a A B C f b j R S G n N : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hA : Derives Γ (successor A a)) (hB : Derives Γ (successor B A)) (hC : Derives Γ (successor C B))
    (hn : Derives Γ (formulaCode w n a z)) (hG : Derives Γ (formulaCode w G z b))
    (hc : Derives Γ (SyntaxNodeSyntax.constructor 0 1 w Fin.elim0 n))
    (hN : Derives Γ (ForcingCodeRecursion.compiled Reln Dom w z f j a n N)) :
    Derives Γ (transfer Reln w z a A B f b j R S G N) := by
  refine intro_transfer hZ Reln w z a A B f b j R S G N ?_
  intro l Δ r _ _ Y hZ1 lift _ _ hY _
  have hc1 : Derives Δ (SyntaxNodeSyntax.constructor 0 1 (r w) Fin.elim0 (r n)) :=
    of_eq (by simp only [SyntaxNodeSyntax.constructor_rename, SyntaxAtomSyntax.zero_map]) (lift hc)
  exact ForcingSourceDensityConstant.truth_from_compiler hZ1 Reln Dom (r w) (r z) (r a) (r A) (r B) (r C)
    (r f) (r j) (r n) (r N) (r b) (r R) (r S) Y (r G)
    (of_eq (omega_rename _ _) (lift hw)) (of_eq (empty_rename _ _) (lift hz))
    (of_eq (formulaCode_rename _ _ _ _ _) (lift hn))
    (of_eq (successor_rename _ _ _) (lift hA)) (of_eq (successor_rename _ _ _) (lift hB))
    (of_eq (successor_rename _ _ _) (lift hC)) hc1
    (of_eq (ForcingCodeRecursion.compiled_rename Reln Dom _ _ _ _ _ _ _ r) (lift hN))
    hY (of_eq (formulaCode_rename _ _ _ _ _) (lift hG))

/-- The original falsum induction case, with the original compiler and
the actual runtime at which the reflexive witness is selected. -/
theorem falsum_step {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (Reln : Formula (k+2)) (Dom : Formula (k+1))
    (w z a A B C f b j R S Base carrierIndex carrier Extra A1 A2 A3 Cr Bd Refl Pre n N : Fin m)
    (raw : Fin 16 → Fin m) (Gb : Fin 5 → Fin m) (H layout : Fin 6 → Fin m)
    (U F P : Fin 3 → Fin m) (I : Fin 5 → Fin m) (Ds : Fin 3 → Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hA : Derives Γ (successor A a)) (hB : Derives Γ (successor B A)) (hC : Derives Γ (successor C B))
    (ht : Derives Γ (SyntaxTermSyntax.term w z b (P 1)))
    (hG : Derives Γ (formulaCode w (layout 3) z b))
    (hIndex : Derives Γ (numeral k carrierIndex))
    (hf : Derives Γ (numeral (k+2) f)) (hj : Derives Γ (numeral (k+1) j))
    (hUpdate : Derives Γ (replacement w f z b Base j (P 1) S))
    (hV : Derives Γ (field w Base carrierIndex carrier))
    (hA1 : Derives Γ (numeral 1 A1)) (hA2 : Derives Γ (numeral 2 A2))
    (hRow : Derives Γ (ForcingPreorderLeaves.data test Reln w z A1 A2 A3 f b Cr Bd Base Refl Pre raw Gb H U F P I Ds))
    (hTarget : Derives Γ (ForcingPreorderInstances.targetData test w z f b Cr Bd Base
      (raw 0) (raw 1) (raw 2) P Pre Refl (U 0)))
    (hExtra : Derives Γ (formulaCode w Extra z b))
    (hLayout : Derives Γ (ForcingProofContext.layoutData w z b Extra Pre H layout))
    (hn : Derives Γ (formulaCode w n a z))
    (hc : Derives Γ (SyntaxNodeSyntax.constructor 0 0 w Fin.elim0 n))
    (hN : Derives Γ (ForcingCodeRecursion.compiled Reln Dom w z f j a n N)) :
    Derives Γ (transfer Reln w z a A B f b j R S (layout 3) N) := by
  have he := ForcingCodeUnary.nullary hZ false Reln Dom w z f j a A B C n N hw hn hA hB hC hc hN
  let Ctor := SyntaxNodeSyntax.constructor 0 0 w.castSucc Fin.elim0 (Fin.last m)
  have eval (q : Fin m) : Ctor.instantiate q = SyntaxNodeSyntax.constructor 0 0 w Fin.elim0 q := by
    simp only [Ctor, Formula.instantiate, SyntaxNodeSyntax.constructor_rename, SyntaxAtomSyntax.zero_map,
      Fin.lastCases_castSucc, Fin.lastCases_last, id_eq]
  have hN0 := of_eq (eval N) (.eqSubst Ctor (eq_symm he) (of_eq (eval n).symm hc))
  refine intro_transfer hZ Reln w z a A B f b j R S (layout 3) N ?_
  intro l Δ r D E Y hZ1 lift hD hE hY hp
  have hN1 : Derives Δ (SyntaxNodeSyntax.constructor 0 0 (r w) Fin.elim0 (r N)) :=
    of_eq (by simp only [SyntaxNodeSyntax.constructor_rename, SyntaxAtomSyntax.zero_map]) (lift hN0)
  exact ForcingDensityGuards.falsum_from_compiled_query hZ1 Reln (r w) (r z) (r a) (r A) (r B) (r f)
    (r b) (r j) (r R) (r S) (r Base) (r carrierIndex) (r carrier) (r Extra) (r A1) (r A2) (r A3)
    (r Cr) (r Bd) (r Refl) (r Pre) D E (r N) Y (r ∘ raw) (r ∘ Gb) (r ∘ H) (r ∘ layout)
    (r ∘ U) (r ∘ F) (r ∘ P) (r ∘ I) (r ∘ Ds)
    (of_eq (omega_rename _ _) (lift hw)) (of_eq (empty_rename _ _) (lift hz))
    (of_eq (successor_rename _ _ _) (lift hA)) (of_eq (SyntaxTermSyntax.term_rename _ _ _ _ _) (lift ht))
    (of_eq (formulaCode_rename _ _ _ _ _) (lift hG))
    (of_eq (numeral_rename _ _ _) (lift hIndex)) (of_eq (numeral_rename _ _ _) (lift hf))
    (of_eq (numeral_rename _ _ _) (lift hj))
    (of_eq (replacement_rename _ _ _ _ _ _ _ _ _) (lift hUpdate)) (of_eq (field_rename _ _ _ _ _) (lift hV))
    (of_eq (numeral_rename _ _ _) (lift hA1)) (of_eq (numeral_rename _ _ _) (lift hA2))
    (of_eq (ForcingPreorderLeaves.data_rename test Reln _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ r) (lift hRow))
    (of_eq (ForcingPreorderInstances.targetData_rename test _ _ _ _ _ _ _ _ _ _ _ _ _ _ r) (lift hTarget))
    (of_eq (formulaCode_rename _ _ _ _ _) (lift hExtra))
    (of_eq (ForcingProofContext.layoutData_rename _ _ _ _ _ _ _ _) (lift hLayout)) hN1 (.conjI hD hE) hp hY

end Constants

end PPAC.Migration.ForcingSourceDensity
