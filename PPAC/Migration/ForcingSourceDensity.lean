import PPAC.Migration.ForcingDensityGuards
import PPAC.Migration.ForcingSourceDensityConstant
import PPAC.Migration.ForcingAtomicDenseTemplate
import PPAC.Migration.ForcingSourceMonoInduction

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
private theorem falsum_step_from_reflexive_query {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
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
    (hRun : Derives Γ (substituted w Bd Base z f z b (raw 1) Refl))
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
  exact ForcingDensityGuards.falsum_from_reflexive_query hZ1 Reln (r w) (r z) (r a) (r A) (r B) (r f)
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
    (of_eq (substituted_rename _ _ _ _ _ _ _ _ _ _) (lift hRun))
    (of_eq (formulaCode_rename _ _ _ _ _) (lift hExtra))
    (of_eq (ForcingProofContext.layoutData_rename _ _ _ _ _ _ _ _) (lift hLayout)) hN1 (.conjI hD hE) hp hY

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
    Derives Γ (transfer Reln w z a A B f b j R S (layout 3) N) :=
  falsum_step_from_reflexive_query hZ Reln Dom w z a A B C f b j R S Base carrierIndex carrier Extra A1 A2 A3 Cr Bd Refl Pre n N
    raw Gb H layout U F P I Ds hw hz hA hB hC ht hG hIndex hf hj hUpdate hV hA1 hA2 hRow
    (.conjL (.conjR (.conjR (.conjR hTarget)))) hExtra hLayout hn hc hN


/-- Consume the existing global runtime. The actual current-condition update
is already retained there; read the reflexive query and the carrier field
from its original preorder and substitution records. -/
theorem falsum_step_from_runtime {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (Reln : Formula (k+2)) (Dom : Formula (k+1))
    (w z a f j b Big R S T SOld SNew A1 A2 A3 K Extra A B C n N : Fin m)
    (raw : Fin 16 → Fin m) (images : Fin 10 → Fin m) (Cr Refl Pre U0 : Fin 2 → Fin m)
    (P : Fin 2 → Fin 3 → Fin m) (rows : Fin 48 → Fin m) (layout : Fin 6 → Fin m)
    (hr : Derives Γ (ForcingRawModalBody.globalModalInput test Reln w z a f j b Big R S T SOld SNew
      A1 A2 A3 K Extra raw images Cr Refl Pre U0 P rows layout))
    (hA : Derives Γ (successor A a)) (hB : Derives Γ (successor B A)) (hC : Derives Γ (successor C B))
    (hn : Derives Γ (formulaCode w n a z))
    (hc : Derives Γ (SyntaxNodeSyntax.constructor 0 0 w Fin.elim0 n))
    (hN : Derives Γ (ForcingCodeRecursion.compiled Reln Dom w z f j a n N)) :
    Derives Γ (transfer Reln w z a A B f b j T SNew (layout 3) N) := by
  let row : Fin 24 → Fin m := fun i => rows (i.castAdd 24)
  let Gb := ForcingMemberRows.backgroundFields row
  let H := ForcingMemberRows.leafFields row
  let U := ForcingMemberRows.nativeFields (U0 0) row
  let F := ForcingMemberRows.proofFields row
  let I := ForcingMemberRows.tailFields row
  let Ds := ForcingMemberRows.prefixFields row
  have hGlobal := Derives.conjL hr
  have hRows := Derives.conjL (.conjL hGlobal)
  have hBasis := Derives.conjL hRows
  have hRow : Derives Γ (ForcingPreorderLeaves.data test Reln w z A1 A2 A3 f b (Cr 0) R S
      (Refl 0) (Pre 0) raw Gb H U F (P 0) I Ds) :=
    .conjL (.conjR hRows)
  have hFresh := Derives.conjL (.conjL (.conjR hGlobal))
  have hz := Derives.conjL hFresh
  have hImages := Derives.conjL (.conjR (.conjR hFresh))
  have hw := Derives.conjL (.conjL hImages)
  have hBase := Derives.conjR (.conjR (.conjR (.conjL hImages)))
  have hOldPre := Derives.conjR (.conjR (.conjR (.conjR (.conjR (.conjR hFresh)))))
  have hCore := Derives.conjL (.conjL (.conjR hRow))
  have hAnd : Derives Γ (binaryCode 0 w (Refl 0) (U0 0) (Pre 0)) := .conjL (.conjR hCore)
  have hRun := ForcingPreorderInstances.reflexive_query hZ Reln w z A1 A2 A3 f b R S (Pre 0) (Refl 0) (U0 0)
    raw hw (.conjL hRow) hOldPre hAnd
  have hf : Derives Γ (numeral (k+2) f) := .conjL (.conjR (.conjR (.conjR (.conjR hBasis))))
  have hK : Derives Γ (numeral k K) := .conjL (.conjR (.conjR (.conjR hBasis)))
  have hAux := Derives.conjR hr
  have hj : Derives Γ (numeral (k+1) j) := .conjL (.conjR hAux)
  have hUpdate : Derives Γ (replacement w f z b S j (P 0 1) SNew) := .conjR (.conjR (.conjR hAux))
  have hExtra : Derives Γ (formulaCode w Extra z b) := .conjL (.conjR (.conjR hGlobal))
  have hLayout : Derives Γ (ForcingProofContext.layoutData w z b Extra (Pre 0) H layout) :=
    .conjR (.conjR (.conjR hGlobal))
  have hG := Derives.conjR (.conjL (.conjR (.conjR (.conjR hLayout))))
  have ht := ForcingRelationWeakening.row_term test Reln w z A1 A2 A3 f b (Cr 0) R S (Refl 0) (Pre 0)
    (U0 0) raw (P 0) row hRow 1
  have hKf : Derives Γ (.mem K f) := SyntaxNumeralMembers.index_member hZ (k+2) (Fin.last k).castSucc f K hf hK
  have hKw := StructuralListTraceOrder.member_member hZ w K f hw (.conjL hBase) hKf
  refine eliminate_objects hZ 1 (fun r v => (Formula.mem (v 0) (r w)).conj
    (field (r w) (r S) (r K) (v 0)))
    (StructuralListFieldValues.exists_value hZ w S K hw hKw) (transfer Reln w z a A B f b j T SNew (layout 3) N) ?_
  intro l Δ r v hZ1 lift hField
  have hc1 : Derives Δ (SyntaxNodeSyntax.constructor 0 0 (r w) Fin.elim0 (r n)) :=
    of_eq (by simp only [SyntaxNodeSyntax.constructor_rename, SyntaxAtomSyntax.zero_map]) (lift hc)
  exact of_eq (transfer_rename Reln w z a A B f b j T SNew (layout 3) N r).symm
    (falsum_step_from_reflexive_query hZ1 Reln Dom (r w) (r z) (r a) (r A) (r B) (r C) (r f) (r b)
      (r j) (r T) (r SNew) (r S) (r K) (v 0) (r Extra) (r A1) (r A2) (r A3)
      (r (Cr 0)) (r R) (r (Refl 0)) (r (Pre 0)) (r n) (r N)
      (r ∘ raw) (r ∘ Gb) (r ∘ H) (r ∘ layout) (r ∘ U) (r ∘ F) (r ∘ P 0) (r ∘ I) (r ∘ Ds)
      (of_eq (omega_rename _ _) (lift hw)) (of_eq (empty_rename _ _) (lift hz))
      (of_eq (successor_rename _ _ _) (lift hA)) (of_eq (successor_rename _ _ _) (lift hB))
      (of_eq (successor_rename _ _ _) (lift hC)) (of_eq (SyntaxTermSyntax.term_rename _ _ _ _ _) (lift ht))
      (of_eq (formulaCode_rename _ _ _ _ _) (lift hG)) (of_eq (numeral_rename _ _ _) (lift hK))
      (of_eq (numeral_rename _ _ _) (lift hf)) (of_eq (numeral_rename _ _ _) (lift hj))
      (of_eq (replacement_rename _ _ _ _ _ _ _ _ _) (lift hUpdate)) (.conjR hField)
      (of_eq (numeral_rename _ _ _) (lift (.conjL (.conjR hBasis))))
      (of_eq (numeral_rename _ _ _) (lift (.conjL (.conjR (.conjR hBasis)))))
      (of_eq (ForcingPreorderLeaves.data_rename test Reln _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ r) (lift hRow))
      (of_eq (substituted_rename _ _ _ _ _ _ _ _ _ _) (lift hRun))
      (of_eq (formulaCode_rename _ _ _ _ _) (lift hExtra))
      (of_eq (ForcingProofContext.layoutData_rename _ _ _ _ _ _ _ _) (lift hLayout))
      (of_eq (formulaCode_rename _ _ _ _ _) (lift hn)) hc1
      (of_eq (ForcingCodeRecursion.compiled_rename Reln Dom _ _ _ _ _ _ _ r) (lift hN)))


private def falsumRuntimeInput {k m} (Reln : Formula (k+2)) (Dom : Formula (k+1))
    (w z a f j b Big R S T SOld SNew A1 A2 A3 K Extra A B C n N : Fin m)
    (raw : Fin 16 → Fin m) (images : Fin 10 → Fin m) (Cr Refl Pre U0 : Fin 2 → Fin m)
    (P : Fin 2 → Fin 3 → Fin m) (rows : Fin 48 → Fin m) (layout : Fin 6 → Fin m) : Formula m :=
  (ForcingRawModalBody.globalModalInput test Reln w z a f j b Big R S T SOld SNew A1 A2 A3 K Extra
    raw images Cr Refl Pre U0 P rows layout).conj
    ((successor A a).conj ((successor B A).conj ((successor C B).conj ((formulaCode w n a z).conj
      ((SyntaxNodeSyntax.constructor 0 0 w Fin.elim0 n).conj (ForcingCodeRecursion.compiled Reln Dom w z f j a n N))))))

def falsumSentence {k m} (Reln : Formula (k+2)) (Dom : Formula (k+1))
    (w z a f j b Big R S T SOld SNew A1 A2 A3 K Extra A B C n N : Fin m)
    (raw : Fin 16 → Fin m) (images : Fin 10 → Fin m) (Cr Refl Pre U0 : Fin 2 → Fin m)
    (P : Fin 2 → Fin 3 → Fin m) (rows : Fin 48 → Fin m) (layout : Fin 6 → Fin m) : Source.Sentence :=
  ((falsumRuntimeInput Reln Dom w z a f j b Big R S T SOld SNew A1 A2 A3 K Extra A B C n N
    raw images Cr Refl Pre U0 P rows layout).imp
      (transfer Reln w z a A B f b j T SNew (layout 3) N)).close

theorem falsum_kernel_certificate {k m} (Reln : Formula (k+2)) (Dom : Formula (k+1))
    (w z a f j b Big R S T SOld SNew A1 A2 A3 K Extra A B C n N : Fin m)
    (raw : Fin 16 → Fin m) (images : Fin 10 → Fin m) (Cr Refl Pre U0 : Fin 2 → Fin m)
    (P : Fin 2 → Fin 3 → Fin m) (rows : Fin 48 → Fin m) (layout : Fin 6 → Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
      (Translation.sentence (falsumSentence Reln Dom w z a f j b Big R S T SOld SNew A1 A2 A3 K Extra A B C n N
        raw images Cr Refl Pre U0 P rows layout)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  let E := falsumRuntimeInput Reln Dom w z a f j b Big R S T SOld SNew A1 A2 A3 K Extra A B C n N
    raw images Cr Refl Pre U0 P rows layout
  have h : Derives (Context.add E (Source.SetLanguage.ZF.at m)) E := .hyp (Or.inl rfl)
  have h1 := Derives.conjR h
  have h2 := Derives.conjR h1
  have h3 := Derives.conjR h2
  have h4 := Derives.conjR h3
  have h5 := Derives.conjR h4
  exact falsum_step_from_runtime (ZFContext.add (ZFContext.source_ZF m) E) Reln Dom w z a f j b Big R S T SOld SNew
    A1 A2 A3 K Extra A B C n N raw images Cr Refl Pre U0 P rows layout
    (.conjL h) (.conjL h1) (.conjL h2) (.conjL h3) (.conjL h4) (.conjL h5) (.conjR h5)

end Constants

section Atoms

/-- The member and equality constructors satisfy the original source density
induction predicate for every actual compiler output and density query. -/
theorem atomic_step_from_runtime {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (equality : Bool) (Reln : Formula (k+2)) (Dom : Formula (k+1))
    (w z a f j b Big R S T SOld SNew A1 A2 A3 K Extra A B C n symbol x y : Fin m)
    (raw : Fin 16 → Fin m) (images : Fin 10 → Fin m) (Cr Refl Pre U0 : Fin 2 → Fin m)
    (P : Fin 2 → Fin 3 → Fin m) (rows : Fin 48 → Fin m) (layout : Fin 6 → Fin m)
    (hr : Derives Γ (ForcingRawModalBody.globalModalInput test Reln w z a f j b Big R S T SOld SNew
      A1 A2 A3 K Extra raw images Cr Refl Pre U0 P rows layout))
    (hA : Derives Γ (successor A a)) (hB : Derives Γ (successor B A)) (hC : Derives Γ (successor C B))
    (hCase : Derives Γ (ForcingSourceMono.atomAt equality w a z symbol x y n)) :
    Derives Γ (atSource Reln Dom w z a A B f b j T SNew (layout 3) n) := by
  have hGlobal := Derives.conjL hr
  have hFresh := Derives.conjL (.conjL (.conjR hGlobal))
  have hw : Derives Γ (omega w) := .conjL (.conjL (.conjL (.conjR (.conjR hFresh))))
  unfold atSource
  apply Derives.impI
  apply Derives.allI
  apply Derives.impI
  let H := formulaCode w n a z
  let r : Fin m → Fin (m+1) := Fin.castSucc
  let F := Fin.last m
  let E := ForcingCodeRecursion.compiled Reln Dom (r w) (r z) (r f) (r j) (r a) (r n) F
  let Δ := Context.add E (Context.image Formula.raise (Context.add H Γ))
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have hH : Derives (Context.add H Γ) H := .hyp (Or.inl rfl)
  have lift {J : Formula m} (h : Derives Γ J) : Derives Δ (J.rename r) := under (add h H) E
  have hZ1 := ZFContext.under (ZFContext.add hZ H) E
  have hw1 := of_eq (omega_rename w r) (lift hw)
  have hN := FormulaCodeProperties.guards (r w) (r n) (r a) (r z)
    (of_eq (formulaCode_rename w n a z r) (under hH E))
  have hCase1 := of_eq (ForcingSourceMono.atomAt_rename equality w a z symbol x y n r) (lift hCase)
  have hAtomic : Derives Δ (SyntaxAtomSyntax.atomic (r w) (r a) (r z) (r n)) := by
    cases equality
    · exact .disjR (.disjL (SyntaxAtomLogic.intro_member _ _ _ _ _ _ _ hCase1))
    · exact .disjR (.disjR (SyntaxAtomLogic.intro_equality _ _ _ _ _ _ hCase1))
  have hCode := ForcingCodeUnary.atomic hZ1 Reln Dom (r w) (r z) (r f) (r j) (r a) (r A) (r B) (r C) (r n) F
    hw1 (.conjL hN) (of_eq (successor_rename A a r) (lift hA)) (of_eq (successor_rename B A r) (lift hB))
    (of_eq (successor_rename C B r) (lift hC)) hAtomic hE
  have hAtom : Derives Δ (ForcingAtomicCode.compiled equality Reln (r w) (r a) (r x) (r y) F) := by
    cases equality
    · exact ForcingAtomCode.member_output hZ1 Reln (r w) (r a) (r z) (r n) (r symbol) (r x) (r y) F hw1 hCase1 hCode
    · exact ForcingAtomCode.equal_output hZ1 Reln (r w) (r a) (r z) (r n) (r x) (r y) F hw1 hCase1 hCode
  have hx : Derives Δ (SyntaxTermSyntax.term (r w) (r a) (r z) (r x)) := by
    cases equality
    · exact .conjL (.conjR (.conjL hCase1))
    · exact .conjL (.conjL hCase1)
  have hy : Derives Δ (SyntaxTermSyntax.term (r w) (r a) (r z) (r y)) := by
    cases equality
    · exact .conjR (.conjR (.conjL hCase1))
    · exact .conjR (.conjL hCase1)
  refine intro_transfer hZ1 Reln (r w) (r z) (r a) (r A) (r B) (r f) (r b) (r j) (r T) (r SNew) (r (layout 3)) F ?_
  intro l Ξ s D E' Y hZ2 move hD hE' hY hProof
  let p := s ∘ r
  have carry {J : Formula m} (h : Derives Γ J) : Derives Ξ (J.rename p) :=
    of_eq (SourceAlgebra.rename_comp J r s) (move (lift h))
  exact ForcingAtomicDenseTemplate.transfer_from_new_query hZ2 equality Reln
    (p w) (p z) (p a) (p f) (p j) (p b) (p Big) (p R) (p S) (p T) (p SOld) (p SNew)
    (p A1) (p A2) (p A3) (p K) (p Extra) (p x) (p y) (s F) Y (p A) (p B) D E'
    (p ∘ raw) (p ∘ images) (p ∘ Cr) (p ∘ Refl) (p ∘ Pre) (p ∘ U0)
    (fun i j => p (P i j)) (p ∘ rows) (p ∘ layout)
    (of_eq (ForcingRawModalBody.globalModalInput_rename test Reln w z a f j b Big R S T SOld SNew
      A1 A2 A3 K Extra raw images Cr Refl Pre U0 P rows layout p) (carry hr))
    (of_eq (successor_rename A a p) (carry hA)) (of_eq (successor_rename B A p) (carry hB))
    (of_eq (SyntaxTermSyntax.term_rename (r w) (r a) (r z) (r x) s) (move hx))
    (of_eq (SyntaxTermSyntax.term_rename (r w) (r a) (r z) (r y) s) (move hy))
    (of_eq (ForcingAtomicCode.compiled_rename equality Reln (r w) (r a) (r x) (r y) F s) (move hAtom))
    hY hD hE' hProof

private def atomicRuntimeInput {k m} (equality : Bool) (Reln : Formula (k+2))
    (w z a f j b Big R S T SOld SNew A1 A2 A3 K Extra A B C n symbol x y : Fin m)
    (raw : Fin 16 → Fin m) (images : Fin 10 → Fin m) (Cr Refl Pre U0 : Fin 2 → Fin m)
    (P : Fin 2 → Fin 3 → Fin m) (rows : Fin 48 → Fin m) (layout : Fin 6 → Fin m) : Formula m :=
  (ForcingRawModalBody.globalModalInput test Reln w z a f j b Big R S T SOld SNew A1 A2 A3 K Extra
    raw images Cr Refl Pre U0 P rows layout).conj
    ((successor A a).conj ((successor B A).conj ((successor C B).conj
      (ForcingSourceMono.atomAt equality w a z symbol x y n))))

def atomicSentence {k m} (equality : Bool) (Reln : Formula (k+2)) (Dom : Formula (k+1))
    (w z a f j b Big R S T SOld SNew A1 A2 A3 K Extra A B C n symbol x y : Fin m)
    (raw : Fin 16 → Fin m) (images : Fin 10 → Fin m) (Cr Refl Pre U0 : Fin 2 → Fin m)
    (P : Fin 2 → Fin 3 → Fin m) (rows : Fin 48 → Fin m) (layout : Fin 6 → Fin m) : Source.Sentence :=
  ((atomicRuntimeInput equality Reln w z a f j b Big R S T SOld SNew A1 A2 A3 K Extra A B C n symbol x y
    raw images Cr Refl Pre U0 P rows layout).imp
      (atSource Reln Dom w z a A B f b j T SNew (layout 3) n)).close

theorem atomic_kernel_certificate {k m} (equality : Bool) (Reln : Formula (k+2)) (Dom : Formula (k+1))
    (w z a f j b Big R S T SOld SNew A1 A2 A3 K Extra A B C n symbol x y : Fin m)
    (raw : Fin 16 → Fin m) (images : Fin 10 → Fin m) (Cr Refl Pre U0 : Fin 2 → Fin m)
    (P : Fin 2 → Fin 3 → Fin m) (rows : Fin 48 → Fin m) (layout : Fin 6 → Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
      (Translation.sentence (atomicSentence equality Reln Dom w z a f j b Big R S T SOld SNew A1 A2 A3 K Extra A B C n symbol x y
        raw images Cr Refl Pre U0 P rows layout)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  let E := atomicRuntimeInput equality Reln w z a f j b Big R S T SOld SNew A1 A2 A3 K Extra A B C n symbol x y
    raw images Cr Refl Pre U0 P rows layout
  have h : Derives (Context.add E (Source.SetLanguage.ZF.at m)) E := .hyp (Or.inl rfl)
  have h1 := Derives.conjR h
  have h2 := Derives.conjR h1
  have h3 := Derives.conjR h2
  exact atomic_step_from_runtime (ZFContext.add (ZFContext.source_ZF m) E) equality Reln Dom w z a f j b Big R S T SOld SNew
    A1 A2 A3 K Extra A B C n symbol x y raw images Cr Refl Pre U0 P rows layout
    (.conjL h) (.conjL h1) (.conjL h2) (.conjL h3) (.conjR h3)

end Atoms


private structure WitnessRuntimeArgs (m : Nat) where
  w : Fin m
  z : Fin m
  a : Fin m
  f : Fin m
  j : Fin m
  b : Fin m
  B : Fin m
  R : Fin m
  S : Fin m
  T : Fin m
  Old : Fin m
  New : Fin m
  A1 : Fin m
  A2 : Fin m
  A3 : Fin m
  K : Fin m
  C : Fin m
  Extra : Fin m
  q : Fin m
  r : Fin m
  raw : Fin 16 → Fin m

private def WitnessRuntimeArgs.map {m l} (p : WitnessRuntimeArgs m) (ρ : Fin m → Fin l) : WitnessRuntimeArgs l :=
  ⟨ρ p.w, ρ p.z, ρ p.a, ρ p.f, ρ p.j, ρ p.b, ρ p.B, ρ p.R, ρ p.S, ρ p.T, ρ p.Old, ρ p.New,
    ρ p.A1, ρ p.A2, ρ p.A3, ρ p.K, ρ p.C, ρ p.Extra, ρ p.q, ρ p.r, ρ ∘ p.raw⟩

private def WitnessRuntimeArgs.terms {m} (p : WitnessRuntimeArgs m) : Fin 3 → Fin m :=
  Fin.cases p.r (SyntaxAtomSyntax.two p.r p.q)

private theorem WitnessRuntimeArgs.terms_map {m l} (p : WitnessRuntimeArgs m) (ρ : Fin m → Fin l) :
    ρ ∘ p.terms = (p.map ρ).terms := by
  funext i
  exact Fin.cases rfl (fun j => Fin.cases rfl (fun k => Fin.cases rfl (fun e => e.elim0) k) j) i

private structure WitnessRuntimeInput {k m} (Γ : Context m) (Reln : Formula (k+2))
    (p : WitnessRuntimeArgs m) : Prop where
  omega : Derives Γ (omega p.w)
  zero : Derives Γ (SyntaxNumeralSyntax.numeral 0 p.z)
  one : Derives Γ (SyntaxNumeralSyntax.numeral 1 p.A1)
  two : Derives Γ (SyntaxNumeralSyntax.numeral 2 p.A2)
  three : Derives Γ (SyntaxNumeralSyntax.numeral 3 p.A3)
  free : Derives Γ (SyntaxNumeralSyntax.numeral (k+2) p.f)
  carrier : Derives Γ (SyntaxNumeralSyntax.numeral k p.K)
  condition : Derives Γ (SyntaxNumeralSyntax.numeral (k+1) p.j)
  boundSuccessor : Derives Γ (successor p.C p.z)
  freshSuccessor : Derives Γ (successor p.B p.b)
  emptyBound : Derives Γ (SyntaxMixedImageCodeSyntax.termList p.w p.z p.z p.b p.R)
  freeBase : Derives Γ (SyntaxMixedImageCodeSyntax.termList p.w p.f p.z p.b p.S)
  names : Derives Γ (SyntaxMixedImageCodeSyntax.termList p.w p.a p.z p.b p.T)
  older : Derives Γ (ForcingReflexiveImages.replacement p.w p.f p.z p.b p.S p.j p.q p.Old)
  newer : Derives Γ (ForcingReflexiveImages.replacement p.w p.f p.z p.b p.S p.j p.r p.New)
  extra : Derives Γ (formulaCode p.w p.Extra p.z p.b)
  terms : ∀ i, Derives Γ (SyntaxTermSyntax.term p.w p.z p.b (p.terms i))
  raw : Derives Γ (ForcingPreorderCode.rawData Reln p.w p.z p.A1 p.A2 p.A3 p.f p.raw)

private theorem WitnessRuntimeInput.map {k m l} {Γ : Context m} {Δ : Context l}
    {Reln : Formula (k+2)} {p : WitnessRuntimeArgs m} (h : WitnessRuntimeInput Γ Reln p)
    (ρ : Fin m → Fin l) (lift : ∀ {F}, Derives Γ F → Derives Δ (F.rename ρ)) :
    WitnessRuntimeInput Δ Reln (p.map ρ) := by
  constructor
  · exact of_eq (omega_rename _ _) (lift h.omega)
  · exact of_eq (SyntaxNumeralSyntax.numeral_rename _ _ _) (lift h.zero)
  · exact of_eq (SyntaxNumeralSyntax.numeral_rename _ _ _) (lift h.one)
  · exact of_eq (SyntaxNumeralSyntax.numeral_rename _ _ _) (lift h.two)
  · exact of_eq (SyntaxNumeralSyntax.numeral_rename _ _ _) (lift h.three)
  · exact of_eq (SyntaxNumeralSyntax.numeral_rename _ _ _) (lift h.free)
  · exact of_eq (SyntaxNumeralSyntax.numeral_rename _ _ _) (lift h.carrier)
  · exact of_eq (SyntaxNumeralSyntax.numeral_rename _ _ _) (lift h.condition)
  · exact of_eq (successor_rename _ _ _) (lift h.boundSuccessor)
  · exact of_eq (successor_rename _ _ _) (lift h.freshSuccessor)
  · exact of_eq (SyntaxMixedImageCodeSyntax.termList_rename _ _ _ _ _ _) (lift h.emptyBound)
  · exact of_eq (SyntaxMixedImageCodeSyntax.termList_rename _ _ _ _ _ _) (lift h.freeBase)
  · exact of_eq (SyntaxMixedImageCodeSyntax.termList_rename _ _ _ _ _ _) (lift h.names)
  · exact of_eq (ForcingReflexiveImages.replacement_rename _ _ _ _ _ _ _ _ _) (lift h.older)
  · exact of_eq (ForcingReflexiveImages.replacement_rename _ _ _ _ _ _ _ _ _) (lift h.newer)
  · exact of_eq (formulaCode_rename _ _ _ _ _) (lift h.extra)
  · intro i
    have e := congrFun (WitnessRuntimeArgs.terms_map p ρ) i
    exact of_eq (SyntaxTermSyntax.term_rename _ _ _ _ ρ |>.trans (congrArg (SyntaxTermSyntax.term (ρ p.w) (ρ p.z) (ρ p.b)) e))
      (lift (h.terms i))
  · exact of_eq (ForcingPreorderCode.rawData_rename Reln _ _ _ _ _ _ _ _) (lift h.raw)

private def witnessFreshTerms {m} (u : Fin 6 → Fin m) : Fin 3 → Fin m :=
  Fin.cases (u 0) (SyntaxAtomSyntax.two (u 1) (u 2))

private def witnessRowTerms {m} (p : WitnessRuntimeArgs m) (u : Fin 6 → Fin m) : Fin 2 → Fin 3 → Fin m :=
  Fin.cases p.terms (fun _ => witnessFreshTerms u)

private def witnessScopes {m} (p : WitnessRuntimeArgs m) : Fin 2 → Fin m := fun _ => p.C

private def witnessRefl {m} (t : Fin 3 → Fin m) (u : Fin 6 → Fin m) : Fin 2 → Fin m :=
  SyntaxAtomSyntax.two (t 1) (u 4)
private def witnessPre {m} (t : Fin 3 → Fin m) (u : Fin 6 → Fin m) : Fin 2 → Fin m :=
  SyntaxAtomSyntax.two (t 0) (u 3)
private def witnessTail {m} (t : Fin 3 → Fin m) (u : Fin 6 → Fin m) : Fin 2 → Fin m :=
  SyntaxAtomSyntax.two (t 2) (u 5)

private theorem witnessRowTerms_map {m l} (p : WitnessRuntimeArgs m) (u : Fin 6 → Fin m) (ρ : Fin m → Fin l) :
    (fun s j => ρ (witnessRowTerms p u s j)) = witnessRowTerms (p.map ρ) (ρ ∘ u) := by
  funext s j
  refine Fin.cases ?_ (fun _ => ?_) s
  · exact congrFun (WitnessRuntimeArgs.terms_map p ρ) j
  · exact Fin.cases rfl (fun i => Fin.cases rfl (fun k => Fin.cases rfl (fun e => e.elim0) k) i) j

private def WitnessRuntimeArgs.runtime {k m} (p : WitnessRuntimeArgs m) (Reln : Formula (k+2))
    (t : Fin 3 → Fin m) (u : Fin 6 → Fin m) (images : Fin 10 → Fin m) (rows : Fin 48 → Fin m)
    (layout : Fin 6 → Fin m) : Formula m :=
  ForcingRawModalBody.globalModalInput test Reln p.w p.z p.a p.f p.j p.b p.B p.R p.S p.T p.Old p.New
    p.A1 p.A2 p.A3 p.K p.Extra p.raw images (witnessScopes p) (witnessRefl t u) (witnessPre t u)
    (witnessTail t u) (witnessRowTerms p u) rows layout

private def WitnessRuntimeArgs.assembled {k m} (p : WitnessRuntimeArgs m) (Reln : Formula (k+2))
    (t : Fin 3 → Fin m) (u : Fin 6 → Fin m) (images : Fin 10 → Fin m) (rows : Fin 48 → Fin m)
    (layout : Fin 6 → Fin m) : Formula m :=
  (p.runtime Reln t u images rows layout).conj
    (substituted p.w p.R p.S p.z p.f p.z p.b (p.raw 0) (t 0))

private theorem at_witness_rows {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    {Reln : Formula (k+2)} {p : WitnessRuntimeArgs m} (h : WitnessRuntimeInput Γ Reln p)
    (t : Fin 3 → Fin m) (u : Fin 6 → Fin m) (images : Fin 10 → Fin m) (rows : Fin 48 → Fin m)
    (hOld : Derives Γ (ForcingPreorderInstances.targetData test p.w p.z p.f p.b p.C p.R p.S
      (p.raw 0) (p.raw 1) (p.raw 2) p.terms (t 0) (t 1) (t 2)))
    (hFresh : Derives Γ (ForcingFreshPreorder.data test Reln p.w p.z p.A1 p.A2 p.A3 p.f p.b p.C p.B p.R p.S
      p.r p.q (t 0) p.raw images u))
    (hRows : Derives Γ (ForcingMemberRows.data test Reln p.w p.z p.A1 p.A2 p.A3 p.f p.b p.B p.R p.S p.K
      p.raw images (witnessScopes p) (witnessRefl t u) (witnessPre t u) (witnessTail t u) (witnessRowTerms p u) rows))
    (out : Formula m)
    (use : ∀ {l} {Δ : Context l} (ρ : Fin m → Fin l) (layout : Fin 6 → Fin l), ZFContext.Evidence Δ →
      (∀ {F}, Derives Γ F → Derives Δ (F.rename ρ)) →
      Derives Δ ((p.map ρ).assembled Reln (ρ ∘ t) (ρ ∘ u) (ρ ∘ images) (ρ ∘ rows) layout) →
      Derives Δ (out.rename ρ)) : Derives Γ out := by
  let row : Fin 24 → Fin m := fun i => rows (i.castAdd 24)
  let H := ForcingMemberRows.leafFields row
  let V := ForcingMemberRows.prefixFields row
  have hOldRow := Derives.conjL (.conjR hRows)
  have hQuery := Derives.conjR (.conjR (.conjR (.conjR hOldRow)))
  have hType (i : Fin 5) : Derives Γ (formulaCode p.w (H i.castSucc) p.z p.b) :=
    SyntaxMixedFormulaJudgment.target_type p.w (V 2) p.S p.A3 p.f p.z p.b _ _
      (ForcingPreorderLeaves.leaf_at p.w (V 2) p.S p.A3 p.f p.z p.b p.raw H
        (ForcingMemberRows.tailFields row) i.castSucc hQuery)
  have hLayout := ForcingProofContext.layout_from_typed hZ p.w p.z p.b p.Extra (t 0) H h.omega h.extra
    (.conjL hOld) hType
  refine eliminate_objects hZ 6 (fun ρ layout => ForcingProofContext.layoutData (ρ p.w) (ρ p.z) (ρ p.b)
    (ρ p.Extra) (ρ (t 0)) (ρ ∘ H) layout) hLayout out ?_
  intro l Δ ρ layout hZ1 lift hLayout1
  let p1 := p.map ρ
  have h1 := h.map ρ lift
  have hRows1 : Derives Δ (ForcingMemberRows.data test Reln p1.w p1.z p1.A1 p1.A2 p1.A3 p1.f p1.b p1.B
      p1.R p1.S p1.K p1.raw (ρ ∘ images) (witnessScopes p1) (witnessRefl (ρ ∘ t) (ρ ∘ u))
      (witnessPre (ρ ∘ t) (ρ ∘ u)) (witnessTail (ρ ∘ t) (ρ ∘ u)) (witnessRowTerms p1 (ρ ∘ u)) (ρ ∘ rows)) :=
    of_eq (by simp only [ForcingMemberRows.data_rename, witnessRowTerms_map, witnessScopes, witnessRefl,
    witnessPre, witnessTail, SyntaxAtomSyntax.two_map, p1, WitnessRuntimeArgs.map, Function.comp_apply]; rfl)
    (lift hRows)
  have hFresh1 := of_eq (ForcingFreshPreorder.data_rename test Reln _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ρ) (lift hFresh)
  have eH : ρ ∘ H = ForcingMemberRows.leafFields (fun i : Fin 24 => ρ (rows (i.castAdd 24))) := by
    funext ⟨i, hi⟩
    have e : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by omega
    rcases e with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  rw [eH] at hLayout1
  have hRuntime : Derives Δ (p1.runtime Reln (ρ ∘ t) (ρ ∘ u) (ρ ∘ images) (ρ ∘ rows) layout) :=
    .conjI (.conjI (.conjI hRows1 h1.three) (.conjI hFresh1 (.conjI h1.extra hLayout1)))
      (.conjI h1.names (.conjI h1.condition (.conjI h1.older h1.newer)))
  exact use ρ layout hZ1 lift (.conjI hRuntime
    (of_eq (substituted_rename _ _ _ _ _ _ _ _ _ _) (lift (.conjL (.conjR hOld)))))


private theorem witness_proof_output {m} {Γ : Context m}
    (w z b G A B : Fin m) (e : Derives Γ (.equal A B))
    (h : Derives Γ (implication test w z b G A)) :
    Derives Γ (implication test w z b G B) := by
  let P := implication test w.castSucc z.castSucc b.castSucc G.castSucc (Fin.last m)
  exact of_eq (by simp only [P, Formula.instantiate, implication_rename,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
    (.eqSubst P e (of_eq (by simp only [P, Formula.instantiate, implication_rename,
      Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) h))

private theorem witness_layout_from_proofs {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z b J Extra Pre : Fin m) (H layout : Fin 6 → Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hJ : Derives Γ (formulaCode w J z b)) (hExtra : Derives Γ (formulaCode w Extra z b))
    (hPre : Derives Γ (formulaCode w Pre z b))
    (hR : Derives Γ (formulaCode w (H 1) z b)) (hQ : Derives Γ (formulaCode w (H 2) z b))
    (hOrder : Derives Γ (formulaCode w (H 4) z b))
    (hLayout : Derives Γ (ForcingProofContext.layoutData w z b Extra Pre H layout))
    (pExtra : Derives Γ (implication test w z b J Extra))
    (pPre : Derives Γ (implication test w z b J Pre))
    (pR : Derives Γ (implication test w z b J (H 1)))
    (pQ : Derives Γ (implication test w z b J (H 2)))
    (pOrder : Derives Γ (implication test w z b J (H 4))) :
    Derives Γ (implication test w z b J (layout 3)) := by
  have h0 := Derives.conjL hLayout
  have h1 := Derives.conjL (.conjR hLayout)
  have h2 := Derives.conjL (.conjR (.conjR hLayout))
  have h3 := Derives.conjL (.conjR (.conjR (.conjR hLayout)))
  have p0 := ForcingProofContext.join hZ test w z b J (H 2) (H 4) (layout 0)
    hw hz hJ hQ hOrder (.conjL h0) pQ pOrder
  have p1 := ForcingProofContext.join hZ test w z b J (H 1) (layout 0) (layout 1)
    hw hz hJ hR (.conjR h0) (.conjL h1) pR p0
  have p2 := ForcingProofContext.join hZ test w z b J Pre (layout 1) (layout 2)
    hw hz hJ hPre (.conjR h1) (.conjL h2) pPre p1
  exact ForcingProofContext.join hZ test w z b J Extra (layout 2) (layout 3)
    hw hz hJ hExtra (.conjR h2) (.conjL h3) pExtra p2

/-- Generate the actual preorder runs and proof context required by the
original monotonicity certificate at the density witness. Replay that
certificate on the actual child compilation at q and r. The order leaf
and member leaves of this runtime are identified with the original guards.
Rebuild its background inside the opened density context and use it to
transfer the positive child to r. -/
theorem with_witness_monotonicity {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (Reln : Formula (k+2)) (Dom : Formula (k+1))
    (w z a f j b B R S T Old New A1 A2 A3 K C Extra q r n Child AtQ AtR OrderA OrderHead OrderCode OrderOut : Fin m)
    (raw : Fin 16 → Fin m) (Local PriorPre : Fin m) (memberQ memberR : Fin 4 → Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hA1 : Derives Γ (SyntaxNumeralSyntax.numeral 1 A1))
    (hA2 : Derives Γ (SyntaxNumeralSyntax.numeral 2 A2))
    (hA3 : Derives Γ (SyntaxNumeralSyntax.numeral 3 A3))
    (hf : Derives Γ (SyntaxNumeralSyntax.numeral (k+2) f))
    (hK : Derives Γ (SyntaxNumeralSyntax.numeral k K))
    (hj : Derives Γ (SyntaxNumeralSyntax.numeral (k+1) j))
    (hC : Derives Γ (successor C z)) (hB : Derives Γ (successor B b))
    (hR : Derives Γ (SyntaxMixedImageCodeSyntax.termList w z z b R))
    (hS : Derives Γ (SyntaxMixedImageCodeSyntax.termList w f z b S))
    (hT : Derives Γ (SyntaxMixedImageCodeSyntax.termList w a z b T))
    (hOld : Derives Γ (ForcingReflexiveImages.replacement w f z b S j q Old))
    (hNew : Derives Γ (ForcingReflexiveImages.replacement w f z b S j r New))
    (hExtra : Derives Γ (formulaCode w Extra z b))
    (hq : Derives Γ (SyntaxTermSyntax.term w z b q))
    (hr : Derives Γ (SyntaxTermSyntax.term w z b r))
    (hRaw : Derives Γ (ForcingPreorderCode.rawData Reln w z A1 A2 A3 f raw))
    (hSource : Derives Γ (formulaCode w n a z))
    (hChild : Derives Γ (ForcingCodeRecursion.compiled Reln Dom w z f j a n Child))
    (hAtQ : Derives Γ (substituted w T Old a f z b Child AtQ))
    (hAtR : Derives Γ (substituted w T New a f z b Child AtR))
    (hPositive : Derives Γ (implication test w z b Extra AtQ))
    (hOrder : Derives Γ (ForcingGuardOpening.result true (ForcingExistGuardsCode.reverseOrder Reln)
      w z f b q New OrderA OrderHead OrderCode OrderOut))
    (hLocal : Derives Γ (formulaCode w Local z b))
    (hPriorPre : Derives Γ (substituted w R S z f z b (raw 0) PriorPre))
    (hMemberQ : Derives Γ (ForcingGuardOpening.result false Reln
      w z f b q S (memberQ 0) (memberQ 1) (memberQ 2) (memberQ 3)))
    (hMemberR : Derives Γ (ForcingGuardOpening.result false Reln
      w z f b r S (memberR 0) (memberR 1) (memberR 2) (memberR 3)))
    (pExtra : Derives Γ (implication test w z b Local Extra))
    (pPre : Derives Γ (implication test w z b Local PriorPre))
    (pMemberQ : Derives Γ (implication test w z b Local (memberQ 3)))
    (pMemberR : Derives Γ (implication test w z b Local (memberR 3)))
    (pOrder : Derives Γ (implication test w z b Local OrderOut))
    (out : Formula m)
    (use : ∀ {l} {Δ : Context l} (ρ : Fin m → Fin l)
      (Refl Pre U0 : Fin 2 → Fin l) (P : Fin 2 → Fin 3 → Fin l)
      (images : Fin 10 → Fin l) (rows : Fin 48 → Fin l) (layout : Fin 6 → Fin l),
      ZFContext.Evidence Δ →
      (∀ {F}, Derives Γ F → Derives Δ (F.rename ρ)) →
      P 0 1 = ρ r → P 0 2 = ρ q →
      Derives Δ (ForcingRawModalBody.globalModalInput test Reln (ρ w) (ρ z) (ρ a) (ρ f) (ρ j)
        (ρ b) (ρ B) (ρ R) (ρ S) (ρ T) (ρ Old) (ρ New) (ρ A1) (ρ A2) (ρ A3)
        (ρ K) (ρ Extra) (ρ ∘ raw) images (fun _ => ρ C) Refl Pre U0 P rows layout) →
      Derives Δ (substituted (ρ w) (ρ R) (ρ S) (ρ z) (ρ f) (ρ z) (ρ b) (ρ (raw 0)) (Pre 0)) →
      Derives Δ (implication test (ρ w) (ρ z) (ρ b) (layout 3) (ρ AtR)) →
      Derives Δ (.equal (ForcingMemberRows.leafFields (fun i => rows (i.castAdd 24)) 4) (ρ OrderOut)) →
      Derives Δ (implication test (ρ w) (ρ z) (ρ b) (ρ Local) (layout 3)) →
      Derives Δ (implication test (ρ w) (ρ z) (ρ b) (ρ Local) (ρ AtR)) →
      Derives Δ (out.rename ρ)) : Derives Γ out := by
  let p : WitnessRuntimeArgs m := ⟨w,z,a,f,j,b,B,R,S,T,Old,New,A1,A2,A3,K,C,Extra,q,r,raw⟩
  have hTerms (i : Fin 3) : Derives Γ (SyntaxTermSyntax.term w z b (p.terms i)) :=
    Fin.cases hr (fun j => Fin.cases hr (fun k => Fin.cases hq (fun e => e.elim0) k) j) i
  have h : WitnessRuntimeInput Γ Reln p := ⟨hw,hz,hA1,hA2,hA3,hf,hK,hj,hC,hB,hR,hS,hT,hOld,hNew,hExtra,hTerms,hRaw⟩
  have hTarget := ForcingPreorderInstances.open_target hZ test Reln w z A1 A2 A3 f b C R S p.terms raw
    hw hz hC hTerms hR hS hRaw
  refine eliminate_objects hZ 3 (fun ρ t => let p1 := p.map ρ
    ForcingPreorderInstances.targetData test p1.w p1.z p1.f p1.b p1.C p1.R p1.S
      (p1.raw 0) (p1.raw 1) (p1.raw 2) p1.terms (t 0) (t 1) (t 2)) ?_ out ?_
  · dsimp only []
    rw [← WitnessRuntimeArgs.terms_map p (old 3)]
    exact hTarget
  intro l Δ ρ t hZ1 lift hTarget1
  let p1 := p.map ρ
  have h1 := h.map ρ lift
  have hImages := ForcingWeakenedImages.produce hZ1 p1.w p1.z p1.f p1.z p1.b p1.B p1.R p1.S
    (.conjI h1.omega (.conjI h1.freshSuccessor (.conjI h1.emptyBound h1.freeBase)))
  refine eliminate_objects hZ1 10 (fun σ images => let p2 := p1.map σ
    ForcingWeakenedImages.data p2.w p2.z p2.f p2.z p2.b p2.B p2.R p2.S images)
    hImages (out.rename ρ) ?_
  intro l2 Ξ σ images hZ2 move hImages2
  let p2 := p1.map σ
  have h2 := h1.map σ move
  have hTarget2 : Derives Ξ (ForcingPreorderInstances.targetData test p2.w p2.z p2.f p2.b p2.C p2.R p2.S
      (p2.raw 0) (p2.raw 1) (p2.raw 2) p2.terms (σ (t 0)) (σ (t 1)) (σ (t 2))) :=
    of_eq (by
      dsimp only []
      rw [ForcingPreorderInstances.targetData_rename]
      change _ = ForcingPreorderInstances.targetData test _ _ _ _ _ _ _ _ _ _ ((p1.map _).terms) _ _ _
      rw [← WitnessRuntimeArgs.terms_map]
      rfl) (move hTarget1)
  have hFresh := ForcingFreshPreorder.produce hZ2 test Reln p2.w p2.z p2.A1 p2.A2 p2.A3 p2.f p2.b p2.C p2.B
    p2.R p2.S p2.r p2.q (σ (t 0)) p2.raw images
    (.conjI h2.zero (.conjI h2.boundSuccessor (.conjI hImages2 (.conjI h2.raw
      (.conjI (h2.terms 1) (.conjI (h2.terms 2) (.conjL (.conjR hTarget2))))))))
  refine eliminate_objects hZ2 6 (fun τ u => let p3 := p2.map τ
    ForcingFreshPreorder.data test Reln p3.w p3.z p3.A1 p3.A2 p3.A3 p3.f p3.b p3.C p3.B p3.R p3.S
      p3.r p3.q (τ (σ (t 0))) p3.raw (τ ∘ images) u) hFresh ((out.rename ρ).rename σ) ?_
  intro l3 Ω τ u hZ3 move3 hFresh3
  let p3 := p2.map τ
  let t3 := τ ∘ σ ∘ t
  let images3 := τ ∘ images
  let P := witnessRowTerms p3 u
  let C3 := witnessScopes p3
  let Refl := witnessRefl t3 u
  let Pre := witnessPre t3 u
  let U0 := witnessTail t3 u
  have h3 := h2.map τ move3
  have hImages3 := of_eq (ForcingWeakenedImages.data_rename _ _ _ _ _ _ _ _ _ τ) (move3 hImages2)
  have hTarget3 : Derives Ω (ForcingPreorderInstances.targetData test p3.w p3.z p3.f p3.b p3.C p3.R p3.S
      (p3.raw 0) (p3.raw 1) (p3.raw 2) p3.terms (t3 0) (t3 1) (t3 2)) :=
    of_eq (by
      rw [ForcingPreorderInstances.targetData_rename]
      change _ = ForcingPreorderInstances.targetData test _ _ _ _ _ _ _ _ _ _ ((p2.map _).terms) _ _ _
      rw [← WitnessRuntimeArgs.terms_map]
      rfl) (move3 hTarget2)
  have hTail := Derives.conjR (.conjR (.conjR hFresh3))
  have hShiftQ := Derives.conjL hTail
  have hShiftP := Derives.conjL (.conjR hTail)
  have hNewTarget := Derives.conjL (.conjR (.conjR hTail))
  have hRow0 := ForcingPreorderLeafTarget.at_target hZ3 test Reln p3.w p3.z p3.A1 p3.A2 p3.A3 p3.f p3.b
    (C3 0) p3.R p3.S (Refl 0) (Pre 0) (U0 0) p3.raw (P 0)
    h3.omega h3.zero h3.one h3.two h3.three h3.raw hTarget3
  have hRow1 := ForcingPreorderLeafTarget.at_target hZ3 test Reln p3.w p3.z p3.A1 p3.A2 p3.A3 p3.f p3.B
    (C3 1) (images3 8) (images3 9) (Refl 1) (Pre 1) (U0 1) p3.raw (P 1)
    h3.omega h3.zero h3.one h3.two h3.three h3.raw hNewTarget
  have hRowsInput : Derives Ω (ForcingMemberRows.input test Reln p3.w p3.z p3.A1 p3.A2 p3.A3 p3.f p3.b
      p3.B p3.R p3.S p3.K p3.raw images3 C3 Refl Pre U0 P) :=
    .conjI h3.zero (.conjI h3.one (.conjI h3.two (.conjI h3.carrier (.conjI h3.free
      (.conjI hImages3 (.conjI hRow0 (.conjI hRow1 (.conjI hShiftQ hShiftP))))))))
  have hRows := ForcingMemberRows.produce hZ3 test Reln p3.w p3.z p3.A1 p3.A2 p3.A3 p3.f p3.b
    p3.B p3.R p3.S p3.K p3.raw images3 C3 Refl Pre U0 P hRowsInput
  let e := τ ∘ σ ∘ ρ
  have carry {F : Formula m} (hp : Derives Γ F) : Derives Ω (F.rename e) :=
    of_eq (by simp only [SourceAlgebra.rename_comp]; rfl) (move3 (move (lift hp)))
  apply of_eq (by simp only [SourceAlgebra.rename_comp]; rfl)
  refine eliminate_objects hZ3 48 (fun i rows => let p4 := p3.map i
    ForcingMemberRows.data test Reln p4.w p4.z p4.A1 p4.A2 p4.A3 p4.f p4.b p4.B p4.R p4.S p4.K
      p4.raw (i ∘ images3) (witnessScopes p4) (witnessRefl (i ∘ t3) (i ∘ u))
      (witnessPre (i ∘ t3) (i ∘ u)) (witnessTail (i ∘ t3) (i ∘ u)) (witnessRowTerms p4 (i ∘ u)) rows)
    ?_ (out.rename e) ?_
  · refine of_eq ?_ hRows
    dsimp only []
    simp only [ForcingMemberRows.produced, ForcingMemberRows.body, witnessRowTerms_map,
      witnessScopes, witnessRefl, witnessPre, witnessTail, SyntaxAtomSyntax.two_map,
      WitnessRuntimeArgs.map, Function.comp_apply, P, C3, Refl, Pre, U0]
    rfl
  intro l4 Λ i rows hZ4 move4 hRows4
  let p4 := p3.map i
  have h4 := h3.map i move4
  have hTarget4 : Derives Λ (ForcingPreorderInstances.targetData test p4.w p4.z p4.f p4.b p4.C p4.R p4.S
      (p4.raw 0) (p4.raw 1) (p4.raw 2) p4.terms (i (t3 0)) (i (t3 1)) (i (t3 2))) :=
    of_eq (by
      rw [ForcingPreorderInstances.targetData_rename]
      change _ = ForcingPreorderInstances.targetData test _ _ _ _ _ _ _ _ _ _ ((p3.map _).terms) _ _ _
      rw [← WitnessRuntimeArgs.terms_map]
      rfl) (move4 hTarget3)
  have hFresh4 := of_eq (ForcingFreshPreorder.data_rename test Reln _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ i) (move4 hFresh3)
  apply of_eq (SourceAlgebra.rename_comp out e i).symm
  refine at_witness_rows hZ4 h4 (i ∘ t3) (i ∘ u) (i ∘ images3) rows hTarget4 hFresh4 hRows4 (out.rename (i ∘ e)) ?_
  intro l5 Ψ v layout hZ5 move5 hResult
  let ρ' := v ∘ i ∘ e
  let p5 := p4.map v
  let lift' : ∀ {F : Formula m}, Derives Γ F → Derives Ψ (F.rename ρ') :=
    fun hp => of_eq (by simp only [ρ', SourceAlgebra.rename_comp]; rfl) (move5 (move4 (carry hp)))
  let Refl5 := witnessRefl (v ∘ i ∘ t3) (v ∘ i ∘ u)
  let Pre5 := witnessPre (v ∘ i ∘ t3) (v ∘ i ∘ u)
  let U5 := witnessTail (v ∘ i ∘ t3) (v ∘ i ∘ u)
  let P5 := witnessRowTerms p5 (v ∘ i ∘ u)
  let images5 := v ∘ i ∘ images3
  let rows5 := v ∘ rows
  have hRuntime := Derives.conjL hResult
  have hMono := ForcingSourceMonoInduction.at_code hZ5 Reln Dom (ρ' w) (ρ' z) (ρ' a) (ρ' f) (ρ' j)
    (ρ' b) (ρ' B) (ρ' R) (ρ' S) (ρ' T) (ρ' Old) (ρ' New) (ρ' A1) (ρ' A2) (ρ' A3)
    (ρ' K) (ρ' Extra) (ρ' n) (ρ' ∘ raw) images5 (fun _ => ρ' C) Refl5 Pre5 U5 P5 rows5 layout
    hRuntime (of_eq (formulaCode_rename w n a z ρ') (lift' hSource))
  have hTransfer := ForcingSourceMono.apply_atSource test Reln Dom (ρ' w) (ρ' z) (ρ' f) (ρ' j) (ρ' a)
    (ρ' b) (layout 3) (fun _ => ρ' T) (SyntaxAtomSyntax.two (ρ' Old) (ρ' New)) (ρ' n) (ρ' Child) hMono
    (of_eq (ForcingCodeRecursion.compiled_rename Reln Dom _ _ _ _ _ _ _ ρ') (lift' hChild))
  let row : Fin 24 → Fin l5 := fun k => rows5 (k.castAdd 24)
  have hGlobal := Derives.conjL hRuntime
  have hRows := Derives.conjL (.conjL hGlobal)
  have hRow := Derives.conjL (.conjR hRows)
  have h5 := h.map ρ' lift'
  have hLayout := Derives.conjR (.conjR (.conjR hGlobal))
  have hMiddle := Derives.conjR (.conjL (.conjR (.conjR hLayout)))
  have hG := Derives.conjL (.conjR (.conjR (.conjR hLayout)))
  have hProj := ForcingRelationGuardProof.project hZ5 test false (ρ' w) (ρ' z) (ρ' b)
    (ρ' Extra) (layout 2) (layout 3) h5.omega h5.zero h5.extra hMiddle (.conjR hG) (.conjL hG)
  have qQuery := of_eq (substituted_rename _ _ _ _ _ _ _ _ _ ρ') (lift' hAtQ)
  have rQuery := of_eq (substituted_rename _ _ _ _ _ _ _ _ _ ρ') (lift' hAtR)
  have hQType := SyntaxMixedFormulaJudgment.target_type (ρ' w) (ρ' T) (ρ' Old)
    (ρ' a) (ρ' f) (ρ' z) (ρ' b) (ρ' Child) (ρ' AtQ) qQuery
  have hProofQ := ForcingRelationGuardProof.chain hZ5 test (ρ' w) (ρ' z) (ρ' b) (layout 3)
    (ρ' Extra) (ρ' AtQ) h5.omega h5.zero (.conjR hG) h5.extra hQType hProj
    (of_eq (implication_rename test _ _ _ _ _ ρ') (lift' hPositive))
  have hProofR := ForcingConjunctionMono.apply_transfer test (ρ' w) (ρ' z) (ρ' a) (ρ' f) (ρ' b) (layout 3)
    (fun _ => ρ' T) (SyntaxAtomSyntax.two (ρ' Old) (ρ' New)) (ρ' Child) (ρ' AtQ) (ρ' AtR)
    hTransfer qQuery rQuery hProofQ
  have hOrderEq := ForcingDensityGuards.witness_order_from_row hZ5 Reln (ρ' w) (ρ' z) (ρ' A1) (ρ' A2)
    (ρ' A3) (ρ' f) (ρ' b) (ρ' C) (ρ' R) (ρ' S) (Refl5 0) (Pre5 0) (ρ' New) (ρ' OrderA) (ρ' OrderHead)
    (ρ' OrderCode) (ρ' OrderOut) (ρ' j) (ρ' ∘ raw) (ForcingMemberRows.backgroundFields row)
    (ForcingMemberRows.leafFields row) (ForcingMemberRows.nativeFields (U5 0) row)
    (ForcingMemberRows.proofFields row) (P5 0) (ForcingMemberRows.tailFields row)
    (ForcingMemberRows.prefixFields row) h5.omega h5.zero h5.one h5.two h5.three h5.free h5.condition
    h5.terms h5.emptyBound h5.freeBase hRow h5.newer
    (of_eq (ForcingGuardOpening.result_rename true (ForcingExistGuardsCode.reverseOrder Reln)
      _ _ _ _ _ _ _ _ _ _ ρ') (lift' hOrder))
  let H := ForcingMemberRows.leafFields row
  let D := ForcingMemberRows.prefixFields row
  let N := ForcingMemberRows.tailFields row
  have member_eq (j : Fin 3) (fields : Fin 4 → Fin l5)
      (hGuard : Derives Ψ (ForcingGuardOpening.result false Reln (ρ' w) (ρ' z) (ρ' f) (ρ' b)
        (P5 0 j) (ρ' S) (fields 0) (fields 1) (fields 2) (fields 3))) :
      Derives Ψ (.equal (H (ForcingPreorderMember.memberPosition j)) (fields 3)) :=
    ForcingDensityGuards.witness_member_from_row hZ5 Reln j (ρ' w) (ρ' z) (ρ' A1) (ρ' A2)
      (ρ' A3) (ρ' f) (ρ' b) (ρ' C) (ρ' R) (ρ' S) (Refl5 0) (Pre5 0)
      (fields 0) (fields 1) (fields 2) (fields 3) (ρ' K)
      (ρ' ∘ raw) (ForcingMemberRows.backgroundFields row) H (ForcingMemberRows.nativeFields (U5 0) row)
      (ForcingMemberRows.proofFields row) (P5 0) N D h5.omega h5.zero h5.one h5.two
      h5.free h5.carrier h5.freeBase hRow hGuard
  have eQ := member_eq 2 (ρ' ∘ memberQ)
    (of_eq (ForcingGuardOpening.result_rename false Reln _ _ _ _ _ _ _ _ _ _ ρ') (lift' hMemberQ))
  have eR := member_eq 1 (ρ' ∘ memberR)
    (of_eq (ForcingGuardOpening.result_rename false Reln _ _ _ _ _ _ _ _ _ _ ρ') (lift' hMemberR))
  have hQueries := Derives.conjR (.conjR (.conjR (.conjR hRow)))
  have hLeafType (j : Fin 6) : Derives Ψ (formulaCode (ρ' w) (H j) (ρ' z) (ρ' b)) :=
    SyntaxMixedFormulaJudgment.target_type (ρ' w) (D 2) (ρ' S) (ρ' A3) (ρ' f)
      (ρ' z) (ρ' b) _ _ (ForcingPreorderLeaves.leaf_at (ρ' w) (D 2) (ρ' S) (ρ' A3)
        (ρ' f) (ρ' z) (ρ' b) (ρ' ∘ raw) H N j hQueries)
  have hPreQuery := Derives.conjR hResult
  have hPreType := SyntaxMixedFormulaJudgment.target_type (ρ' w) (ρ' R) (ρ' S)
    (ρ' z) (ρ' f) (ρ' z) (ρ' b) (ρ' (raw 0)) (Pre5 0) hPreQuery
  have ePre := SyntaxMixedFormulaOutputInduction.unique hZ5 (ρ' w) (ρ' R) (ρ' S)
    (ρ' z) (ρ' f) (ρ' z) (ρ' b) (ρ' (raw 0)) (ρ' PriorPre) (Pre5 0) h5.omega
    (of_eq (substituted_rename _ _ _ _ _ _ _ _ _ ρ') (lift' hPriorPre)) hPreQuery
  have local_output (A : Fin m) (B : Fin l5) (hEq : Derives Ψ (.equal (ρ' A) B))
      (hp : Derives Γ (implication test w z b Local A)) :
      Derives Ψ (implication test (ρ' w) (ρ' z) (ρ' b) (ρ' Local) B) :=
    witness_proof_output (ρ' w) (ρ' z) (ρ' b) (ρ' Local) (ρ' A) B hEq
      (of_eq (implication_rename test _ _ _ _ _ ρ') (lift' hp))
  have hLocalType := of_eq (formulaCode_rename _ _ _ _ ρ') (lift' hLocal)
  have hLocalGlobal := witness_layout_from_proofs hZ5 (ρ' w) (ρ' z) (ρ' b) (ρ' Local)
    (ρ' Extra) (Pre5 0) H layout h5.omega h5.zero hLocalType h5.extra hPreType
    (hLeafType 1) (hLeafType 2) (hLeafType 4) hLayout
    (of_eq (implication_rename test _ _ _ _ _ ρ') (lift' pExtra))
    (local_output PriorPre (Pre5 0) ePre pPre)
    (local_output (memberR 3) (H 1) (eq_symm eR) pMemberR)
    (local_output (memberQ 3) (H 2) (eq_symm eQ) pMemberQ)
    (local_output OrderOut (H 4) (eq_symm hOrderEq) pOrder)
  have hRType := SyntaxMixedFormulaJudgment.target_type (ρ' w) (ρ' T) (ρ' New)
    (ρ' a) (ρ' f) (ρ' z) (ρ' b) (ρ' Child) (ρ' AtR) rQuery
  have hLocalR := ForcingRelationGuardProof.chain hZ5 test (ρ' w) (ρ' z) (ρ' b)
    (ρ' Local) (layout 3) (ρ' AtR) h5.omega h5.zero hLocalType (.conjR hG)
    hRType hLocalGlobal hProofR
  exact of_eq (SourceAlgebra.rename_comp out (i ∘ e) v).symm
    (use ρ' Refl5 Pre5 U5 P5 images5 rows5 layout hZ5 lift' rfl rfl hRuntime hPreQuery
      hProofR hOrderEq hLocalGlobal hLocalR)

end PPAC.Migration.ForcingSourceDensity
