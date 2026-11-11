import PPAC.Migration.ForcingDensityGuards
import PPAC.Migration.ForcingSourceDensityConstant
import PPAC.Migration.ForcingAtomicDenseTemplate
import PPAC.Migration.ForcingSourceMonoInduction

/-! The original force_of_dense clauses on actual internal compiler and
substitution outputs. The proof code is generated in the same conditional
Root context as the corresponding forcing query. -/
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

-- Assemble the witness preorder once for the negative and existential source clauses.
private theorem with_witness_preorder {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (Reln : Formula (k+2))
    (w z a f j b B R S T Old New A1 A2 A3 K C Extra q r OrderA OrderHead OrderCode OrderOut Selected Sel : Fin m)
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
    (hSelected : Derives Γ (ForcingReflexiveImages.replacement w f z b S j Sel Selected))
    (hExtra : Derives Γ (formulaCode w Extra z b))
    (hq : Derives Γ (SyntaxTermSyntax.term w z b q))
    (hr : Derives Γ (SyntaxTermSyntax.term w z b r))
    (hRaw : Derives Γ (ForcingPreorderCode.rawData Reln w z A1 A2 A3 f raw))
    (hOrder : Derives Γ (ForcingGuardOpening.result true (ForcingExistGuardsCode.reverseOrder Reln)
      w z f b q New OrderA OrderHead OrderCode OrderOut))
    (hLocal : Derives Γ (formulaCode w Local z b))
    (hPriorPre : Derives Γ (substituted w R S z f z b (raw 0) PriorPre))
    (hMemberQ : Derives Γ (ForcingGuardOpening.result false Reln
      w z f b q Selected (memberQ 0) (memberQ 1) (memberQ 2) (memberQ 3)))
    (hMemberR : Derives Γ (ForcingGuardOpening.result false Reln
      w z f b r Selected (memberR 0) (memberR 1) (memberR 2) (memberR 3)))
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
      Derives Δ (.equal (ForcingMemberRows.leafFields (fun i => rows (i.castAdd 24)) 4) (ρ OrderOut)) →
      Derives Δ (implication test (ρ w) (ρ z) (ρ b) (ρ Local) (layout 3)) →
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
  let row : Fin 24 → Fin l5 := fun k => rows5 (k.castAdd 24)
  have hGlobal := Derives.conjL hRuntime
  have hRows := Derives.conjL (.conjL hGlobal)
  have hRow := Derives.conjL (.conjR hRows)
  have h5 := h.map ρ' lift'
  have hLayout := Derives.conjR (.conjR (.conjR hGlobal))
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
  have member_eq (ix : Fin 3) (fields : Fin 4 → Fin l5)
      (hGuard : Derives Ψ (ForcingGuardOpening.result false Reln (ρ' w) (ρ' z) (ρ' f) (ρ' b)
        (P5 0 ix) (ρ' Selected) (fields 0) (fields 1) (fields 2) (fields 3))) :
      Derives Ψ (.equal (H (ForcingPreorderMember.memberPosition ix)) (fields 3)) :=
    ForcingDensityGuards.witness_member_from_updated_row hZ5 Reln ix (ρ' w) (ρ' z) (ρ' A1) (ρ' A2)
      (ρ' A3) (ρ' f) (ρ' b) (ρ' C) (ρ' R) (ρ' S) (ρ' Selected) (Refl5 0) (Pre5 0)
      (fields 0) (fields 1) (fields 2) (fields 3) (ρ' K) (ρ' j) (ρ' Sel)
      (ρ' ∘ raw) (ForcingMemberRows.backgroundFields row) H (ForcingMemberRows.nativeFields (U5 0) row)
      (ForcingMemberRows.proofFields row) (P5 0) N D h5.omega h5.zero h5.one h5.two
      h5.free h5.carrier h5.freeBase hRow h5.condition
      (of_eq (ForcingReflexiveImages.replacement_rename _ _ _ _ _ _ _ _ ρ') (lift' hSelected)) hGuard
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
  exact of_eq (SourceAlgebra.rename_comp out (i ∘ e) v).symm
    (use ρ' Refl5 Pre5 U5 P5 images5 rows5 layout hZ5 lift' rfl rfl hRuntime hPreQuery
      hOrderEq hLocalGlobal)

/-- Generate the actual preorder runs and proof context required by the
original monotonicity certificate at the density witness. Replay that
certificate on the actual child compilation at q and r. The order leaf
and member leaves of this runtime are identified with the original guards.
Rebuild its background inside the opened density context and use it to
transfer the positive child to r. -/
theorem with_witness_monotonicity {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (Reln : Formula (k+2)) (Dom : Formula (k+1))
    (w z a f j b B R S T Old New A1 A2 A3 K C Extra q r n Child AtQ AtR OrderA OrderHead OrderCode OrderOut Selected Sel : Fin m)
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
    (hSelected : Derives Γ (ForcingReflexiveImages.replacement w f z b S j Sel Selected))
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
      w z f b q Selected (memberQ 0) (memberQ 1) (memberQ 2) (memberQ 3)))
    (hMemberR : Derives Γ (ForcingGuardOpening.result false Reln
      w z f b r Selected (memberR 0) (memberR 1) (memberR 2) (memberR 3)))
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
  refine with_witness_preorder hZ Reln w z a f j b B R S T Old New A1 A2 A3 K C Extra q r
    OrderA OrderHead OrderCode OrderOut Selected Sel raw Local PriorPre memberQ memberR hw hz hA1 hA2 hA3
    hf hK hj hC hB hR hS hT hOld hNew hSelected hExtra hq hr hRaw hOrder hLocal hPriorPre hMemberQ hMemberR
    pExtra pPre pMemberQ pMemberR pOrder out ?_
  intro l5 Ψ ρ' Refl5 Pre5 U5 P5 images5 rows5 layout hZ5 lift' eR eQ hRuntime hPreQuery hOrderEq hLocalGlobal
  have hMono := ForcingSourceMonoInduction.at_code hZ5 Reln Dom (ρ' w) (ρ' z) (ρ' a) (ρ' f) (ρ' j)
    (ρ' b) (ρ' B) (ρ' R) (ρ' S) (ρ' T) (ρ' Old) (ρ' New) (ρ' A1) (ρ' A2) (ρ' A3)
    (ρ' K) (ρ' Extra) (ρ' n) (ρ' ∘ raw) images5 (fun _ => ρ' C) Refl5 Pre5 U5 P5 rows5 layout
    hRuntime (of_eq (formulaCode_rename w n a z ρ') (lift' hSource))
  have hTransfer := ForcingSourceMono.apply_atSource test Reln Dom (ρ' w) (ρ' z) (ρ' f) (ρ' j) (ρ' a)
    (ρ' b) (layout 3) (fun _ => ρ' T) (SyntaxAtomSyntax.two (ρ' Old) (ρ' New)) (ρ' n) (ρ' Child) hMono
    (of_eq (ForcingCodeRecursion.compiled_rename Reln Dom _ _ _ _ _ _ _ ρ') (lift' hChild))
  have hGlobal := Derives.conjL hRuntime
  have hLayout := Derives.conjR (.conjR (.conjR hGlobal))
  have hw5 := of_eq (omega_rename _ ρ') (lift' hw)
  have hz5 := of_eq (empty_rename _ ρ') (lift' hz)
  have hExtra5 := of_eq (formulaCode_rename _ _ _ _ ρ') (lift' hExtra)
  have hLocalType := of_eq (formulaCode_rename _ _ _ _ ρ') (lift' hLocal)
  have hMiddle := Derives.conjR (.conjL (.conjR (.conjR hLayout)))
  have hG := Derives.conjL (.conjR (.conjR (.conjR hLayout)))
  have hProj := ForcingRelationGuardProof.project hZ5 test false (ρ' w) (ρ' z) (ρ' b)
    (ρ' Extra) (layout 2) (layout 3) hw5 hz5 hExtra5 hMiddle (.conjR hG) (.conjL hG)
  have qQuery := of_eq (substituted_rename _ _ _ _ _ _ _ _ _ ρ') (lift' hAtQ)
  have rQuery := of_eq (substituted_rename _ _ _ _ _ _ _ _ _ ρ') (lift' hAtR)
  have hQType := SyntaxMixedFormulaJudgment.target_type (ρ' w) (ρ' T) (ρ' Old)
    (ρ' a) (ρ' f) (ρ' z) (ρ' b) (ρ' Child) (ρ' AtQ) qQuery
  have hProofQ := ForcingRelationGuardProof.chain hZ5 test (ρ' w) (ρ' z) (ρ' b) (layout 3)
    (ρ' Extra) (ρ' AtQ) hw5 hz5 (.conjR hG) hExtra5 hQType hProj
    (of_eq (implication_rename test _ _ _ _ _ ρ') (lift' hPositive))
  have hProofR := ForcingConjunctionMono.apply_transfer test (ρ' w) (ρ' z) (ρ' a) (ρ' f) (ρ' b) (layout 3)
    (fun _ => ρ' T) (SyntaxAtomSyntax.two (ρ' Old) (ρ' New)) (ρ' Child) (ρ' AtQ) (ρ' AtR)
    hTransfer qQuery rQuery hProofQ
  have hRType := SyntaxMixedFormulaJudgment.target_type (ρ' w) (ρ' T) (ρ' New)
    (ρ' a) (ρ' f) (ρ' z) (ρ' b) (ρ' Child) (ρ' AtR) rQuery
  have hLocalR := ForcingRelationGuardProof.chain hZ5 test (ρ' w) (ρ' z) (ρ' b)
    (ρ' Local) (layout 3) (ρ' AtR) hw5 hz5 hLocalType (.conjR hG)
    hRType hLocalGlobal hProofR
  exact use ρ' Refl5 Pre5 U5 P5 images5 rows5 layout hZ5 lift' eR eQ hRuntime hPreQuery
    hProofR hOrderEq hLocalGlobal hLocalR

set_option maxHeartbeats 600000 in
/-- Use the actual witness table to raise the two original outer proofs, then
consume the local guard proofs in the original monotonicity replay. The
inherited preorder is queried on the unchanged witness free column. -/
private theorem with_raised_witness_monotonicity {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (Reln : Formula (k+2)) (Dom : Formula (k+1))
    (w z a f j b d A L S R T Old New A1 A2 A3 K C H Extra Local
      q r n Child Yq AtQ AtR OldPre OrderA OrderHead OrderCode OrderOut Selected Sel : Fin m)
    (raw : Fin 16 → Fin m) (v : Fin 10 → Fin m) (memberQ memberR : Fin 4 → Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hA1 : Derives Γ (SyntaxNumeralSyntax.numeral 1 A1))
    (hA2 : Derives Γ (SyntaxNumeralSyntax.numeral 2 A2))
    (hA3 : Derives Γ (SyntaxNumeralSyntax.numeral 3 A3))
    (hf : Derives Γ (SyntaxNumeralSyntax.numeral (k+2) f))
    (hK : Derives Γ (SyntaxNumeralSyntax.numeral k K))
    (hj : Derives Γ (SyntaxNumeralSyntax.numeral (k+1) j))
    (hC : Derives Γ (successor C z))
    (hImages : Derives Γ (ForcingWeakenedImages.data w A f z b d L S v))
    (hT : Derives Γ (SyntaxMixedImageCodeSyntax.termList w a z d T))
    (hOld : Derives Γ (ForcingReflexiveImages.replacement w f z d (v 9) j q Old))
    (hNew : Derives Γ (ForcingReflexiveImages.replacement w f z d (v 9) j r New))
    (hSelected : Derives Γ (ForcingReflexiveImages.replacement w f z d (v 9) j Sel Selected))
    (hq : Derives Γ (SyntaxTermSyntax.term w z d q)) (hr : Derives Γ (SyntaxTermSyntax.term w z d r))
    (hRaw : Derives Γ (ForcingPreorderCode.rawData Reln w z A1 A2 A3 f raw))
    (hSource : Derives Γ (formulaCode w n a z))
    (hChild : Derives Γ (ForcingCodeRecursion.compiled Reln Dom w z f j a n Child))
    (hAtQ : Derives Γ (substituted w T Old a f z d Child AtQ))
    (hAtR : Derives Γ (substituted w T New a f z d Child AtR))
    (hLocal : Derives Γ (formulaCode w Local z d))
    (hOldPre : Derives Γ (substituted w R S z f z b (raw 0) OldPre))
    (hWeakExtra : Derives Γ (SyntaxWeakenFreeSyntax.weakened w z b d H Extra))
    (hWeakAtQ : Derives Γ (SyntaxWeakenFreeSyntax.weakened w z b d Yq AtQ))
    (hOrder : Derives Γ (ForcingGuardOpening.result true (ForcingExistGuardsCode.reverseOrder Reln)
      w z f d q New OrderA OrderHead OrderCode OrderOut))
    (hMemberQ : Derives Γ (ForcingGuardOpening.result false Reln
      w z f d q Selected (memberQ 0) (memberQ 1) (memberQ 2) (memberQ 3)))
    (hMemberR : Derives Γ (ForcingGuardOpening.result false Reln
      w z f d r Selected (memberR 0) (memberR 1) (memberR 2) (memberR 3)))
    (pOldPre : Derives Γ (implication test w z b H OldPre))
    (pOldPositive : Derives Γ (implication test w z b H Yq))
    (pExtra : Derives Γ (implication test w z d Local Extra))
    (pMemberQ : Derives Γ (implication test w z d Local (memberQ 3)))
    (pMemberR : Derives Γ (implication test w z d Local (memberR 3)))
    (pOrder : Derives Γ (implication test w z d Local OrderOut))
    (out : Formula m)
    (use : ∀ {l} {Δ : Context l} (ρ : Fin m → Fin l) (R' B : Fin l)
      (Refl Pre U0 : Fin 2 → Fin l) (P : Fin 2 → Fin 3 → Fin l)
      (images : Fin 10 → Fin l) (rows : Fin 48 → Fin l) (layout : Fin 6 → Fin l),
      ZFContext.Evidence Δ → (∀ {F}, Derives Γ F → Derives Δ (F.rename ρ)) →
      P 0 1 = ρ r → P 0 2 = ρ q →
      Derives Δ (ForcingRawModalBody.globalModalInput test Reln (ρ w) (ρ z) (ρ a) (ρ f) (ρ j)
        (ρ d) B R' (ρ (v 9)) (ρ T) (ρ Old) (ρ New) (ρ A1) (ρ A2) (ρ A3)
        (ρ K) (ρ Extra) (ρ ∘ raw) images (fun _ => ρ C) Refl Pre U0 P rows layout) →
      Derives Δ (substituted (ρ w) R' (ρ (v 9)) (ρ z) (ρ f) (ρ z) (ρ d) (ρ (raw 0)) (Pre 0)) →
      Derives Δ (implication test (ρ w) (ρ z) (ρ d) (ρ Local) (layout 3)) →
      Derives Δ (implication test (ρ w) (ρ z) (ρ d) (ρ Local) (ρ AtR)) →
      Derives Δ (out.rename ρ)) : Derives Γ out := by
  have hExtra := SyntaxWeakenFreeOutput.target_type w z b d H Extra hWeakExtra
  have hd := Derives.conjR (.conjR (FormulaCodeProperties.guards w Extra z d hExtra))
  refine ForcingDensityInstantiation.with_raised_witness_proofs hZ w z A f b d L S R (raw 0)
    OldPre H Extra Yq AtQ v hw hz hImages hOldPre hWeakExtra hWeakAtQ pOldPre pOldPositive out ?_
  intro l Δ s R' PriorPre hZ1 move hR hS hPre pPriorPre pPositive
  have hw1 := of_eq (omega_rename w s) (move hw)
  refine InternalProofTemplates.eliminate_successor hZ1 (s w) (s d) hw1 (move hd) (out.rename s) ?_
  intro l2 Ξ t B hZ2 move2 hB
  let e := t ∘ s
  have carry {F : Formula m} (h : Derives Γ F) : Derives Ξ (F.rename e) :=
    of_eq (SourceAlgebra.rename_comp F s t) (move2 (move h))
  have hw2 := of_eq (omega_rename w e) (carry hw)
  have hz2 := of_eq (empty_rename z e) (carry hz)
  have hLocal2 := of_eq (formulaCode_rename w Local z d e) (carry hLocal)
  have hExtra2 := of_eq (formulaCode_rename w Extra z d e) (carry hExtra)
  have hPre2 := of_eq (substituted_rename _ _ _ _ _ _ _ _ _ t) (move2 hPre)
  have hPreT := SyntaxMixedFormulaJudgment.target_type (e w) (t R') (e (v 9)) (e z) (e f)
    (e z) (e d) (e (raw 0)) (t PriorPre) hPre2
  have pExtra2 := of_eq (implication_rename test _ _ _ _ _ e) (carry pExtra)
  have pPre2 := ForcingRelationGuardProof.chain hZ2 test (e w) (e z) (e d) (e Local) (e Extra) (t PriorPre)
    hw2 hz2 hLocal2 hExtra2 hPreT pExtra2
    (of_eq (implication_rename test _ _ _ _ _ t) (move2 pPriorPre))
  apply of_eq (SourceAlgebra.rename_comp out s t).symm
  refine with_witness_monotonicity hZ2 Reln Dom (e w) (e z) (e a) (e f) (e j) (e d) B
    (t R') (e (v 9)) (e T) (e Old) (e New) (e A1) (e A2) (e A3) (e K) (e C)
    (e Extra) (e q) (e r) (e n) (e Child) (e AtQ) (e AtR)
    (e OrderA) (e OrderHead) (e OrderCode) (e OrderOut) (e Selected) (e Sel)
    (e ∘ raw) (e Local) (t PriorPre) (e ∘ memberQ) (e ∘ memberR)
    hw2 hz2 (of_eq (SyntaxNumeralSyntax.numeral_rename _ _ e) (carry hA1))
    (of_eq (SyntaxNumeralSyntax.numeral_rename _ _ e) (carry hA2))
    (of_eq (SyntaxNumeralSyntax.numeral_rename _ _ e) (carry hA3))
    (of_eq (SyntaxNumeralSyntax.numeral_rename _ _ e) (carry hf))
    (of_eq (SyntaxNumeralSyntax.numeral_rename _ _ e) (carry hK))
    (of_eq (SyntaxNumeralSyntax.numeral_rename _ _ e) (carry hj))
    (of_eq (successor_rename _ _ e) (carry hC)) hB
    (of_eq (SyntaxMixedImageCodeSyntax.termList_rename _ _ _ _ _ t) (move2 hR))
    (of_eq (SyntaxMixedImageCodeSyntax.termList_rename _ _ _ _ _ t) (move2 hS))
    (of_eq (SyntaxMixedImageCodeSyntax.termList_rename _ _ _ _ _ e) (carry hT))
    (of_eq (ForcingReflexiveImages.replacement_rename _ _ _ _ _ _ _ _ e) (carry hOld))
    (of_eq (ForcingReflexiveImages.replacement_rename _ _ _ _ _ _ _ _ e) (carry hNew))
    (of_eq (ForcingReflexiveImages.replacement_rename _ _ _ _ _ _ _ _ e) (carry hSelected))
    hExtra2 (of_eq (SyntaxTermSyntax.term_rename _ _ _ _ e) (carry hq))
    (of_eq (SyntaxTermSyntax.term_rename _ _ _ _ e) (carry hr))
    (of_eq (ForcingPreorderCode.rawData_rename Reln _ _ _ _ _ _ _ e) (carry hRaw))
    (of_eq (formulaCode_rename _ _ _ _ e) (carry hSource))
    (of_eq (ForcingCodeRecursion.compiled_rename Reln Dom _ _ _ _ _ _ _ e) (carry hChild))
    (of_eq (substituted_rename _ _ _ _ _ _ _ _ _ e) (carry hAtQ))
    (of_eq (substituted_rename _ _ _ _ _ _ _ _ _ e) (carry hAtR))
    (of_eq (implication_rename test _ _ _ _ _ t) (move2 pPositive))
    (of_eq (ForcingGuardOpening.result_rename true (ForcingExistGuardsCode.reverseOrder Reln)
      _ _ _ _ _ _ _ _ _ _ e) (carry hOrder))
    hLocal2 hPre2
    (of_eq (ForcingGuardOpening.result_rename false Reln _ _ _ _ _ _ _ _ _ _ e) (carry hMemberQ))
    (of_eq (ForcingGuardOpening.result_rename false Reln _ _ _ _ _ _ _ _ _ _ e) (carry hMemberR))
    pExtra2 pPre2 (of_eq (implication_rename test _ _ _ _ _ e) (carry pMemberQ))
    (of_eq (implication_rename test _ _ _ _ _ e) (carry pMemberR))
    (of_eq (implication_rename test _ _ _ _ _ e) (carry pOrder)) (out.rename e) ?_
  intro l3 Θ u Refl Pre U0 P images rows layout hZ3 move3 er eq hRuntime hPre3 _ _ pGlobal pAtR
  let ρ := u ∘ e
  have lift {F : Formula m} (h : Derives Γ F) : Derives Θ (F.rename ρ) :=
    of_eq (SourceAlgebra.rename_comp F e u) (move3 (carry h))
  exact of_eq (SourceAlgebra.rename_comp out e u).symm
    (use ρ (u (t R')) (u B) Refl Pre U0 P images rows layout hZ3 lift er eq
      hRuntime hPre3 pGlobal pAtR)

set_option maxHeartbeats 1000000 in
/-- The original negative density witness supplies the actual q/r queries,
the local guards and the negative proof. Raise the two outer proofs and replay
original monotonicity there. The actual negative proof is instantiated at
that same witness, and the original existential elimination returns falsum
under the original outer background. -/
theorem with_negative_density_transfer {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (Reln : Formula (k+2)) (Dom : Formula (k+1))
    (w z a A B f j n N C b c d t L S D E G W H body Parent Yq Bot
      A1 A2 A3 K R Base Sel OldPre : Fin m)
    (images : Fin 10 → Fin m) (negOpen : Fin 9 → Fin m) (negData : Fin 5 → Fin m)
    (negNodes negOut : Fin 4 → Fin m) (raw : Fin 16 → Fin m)
    (hB : Derives Γ (successor B A))
    (hNeg : Derives Γ (ForcingRawModalBody.negativeRecord Reln w z a f A b c d t L S j C N body Parent
      images negOpen negData negNodes))
    (hNegQueries : Derives Γ (ForcingRawModalBody.data w (negOpen 7) (images 9) A f z d
      (negData 3) (negData 4) (negNodes 1) (negNodes 2) (negOpen 8) negOut))
    (hOperand : Derives Γ (ForcingFormulaDiagram.binaryData 2 w (negOpen 7) (images 9) A f z d
      (negData 2) (negNodes 0) (negOut 3) Yq Bot))
    (hCompiled : Derives Γ (ForcingDensityCode.compiled Reln w a A B f j N D))
    (hQuery : Derives Γ (substituted w L S a f z b D E))
    (hWeakG : Derives Γ (SyntaxWeakenFreeSyntax.weakened w z b d G W))
    (hProof : Derives Γ (implication test w z b G E))
    (hH : Derives Γ (formulaCode w H z d)) (hW : Derives Γ (formulaCode w W z d))
    (hToW : Derives Γ (implication test w z d H W))
    (hM : Derives Γ (implication test w z d H (negOut 1)))
    (hO : Derives Γ (implication test w z d H (negOut 2)))
    (hA1 : Derives Γ (SyntaxNumeralSyntax.numeral 1 A1))
    (hA2 : Derives Γ (SyntaxNumeralSyntax.numeral 2 A2))
    (hA3 : Derives Γ (SyntaxNumeralSyntax.numeral 3 A3))
    (hf : Derives Γ (SyntaxNumeralSyntax.numeral (k+2) f))
    (hK : Derives Γ (SyntaxNumeralSyntax.numeral k K))
    (hj : Derives Γ (SyntaxNumeralSyntax.numeral (k+1) j))
    (hRaw : Derives Γ (ForcingPreorderCode.rawData Reln w z A1 A2 A3 f raw))
    (hSource : Derives Γ (formulaCode w n a z))
    (hChild : Derives Γ (ForcingCodeRecursion.compiled Reln Dom w z f j a n C))
    (hOldPre : Derives Γ (substituted w R Base z f z d (raw 0) OldPre))
    (hSel : Derives Γ (SyntaxTermSyntax.term w z d Sel))
    (hBaseUpdate : Derives Γ (ForcingReflexiveImages.replacement w f z d Base j Sel (images 9)))
    (pOldPre : Derives Γ (implication test w z d H OldPre))
    (pOldPositive : Derives Γ (implication test w z d H Yq))
    : Derives Γ (implication test w z d H (negNodes 0)) := by
  let out := implication test w z d H (negNodes 0)
  refine ForcingDensityInstantiation.with_negative_witness_queries hZ Reln w z a A B f j N C b c d t
    L S D E G W H body Parent Yq Bot images negOpen negData negNodes negOut hB hNeg hNegQueries
    hOperand hCompiled hQuery hWeakG hProof hH hW hToW hM hO out ?_
  intro l Δ s B' T Q K' Fq Fr AtQ AtR Tail Bound OrderHead OrderCode MemberQ Extra Local
    density shell v u x hZ1 move hTail hOpen _ hQ hTable _ _ hFq hFr hWeakQ
    hAtQ hAtR hNegR hWeakExtra _ hMQ hMR hOrder hLocal pExtra pMQ pMR pOrder pNeg
  let membersQ : Fin 4 → Fin l :=
    Fin.cases (s A) (Fin.cases (s (negData 1)) (SyntaxAtomSyntax.two (s (negData 3)) MemberQ))
  let membersR : Fin 4 → Fin l :=
    Fin.cases (s B) (Fin.cases (density 1) (SyntaxAtomSyntax.two (density 4) (x 1)))
  have hInput := Derives.conjL hOpen
  have hw := Derives.conjL hInput
  have hz := Derives.conjL (.conjR hInput)
  have hc := Derives.conjL (.conjR (.conjR (.conjR hInput)))
  have hr := Derives.conjL (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR hInput))))))
  have hOldPre1 := of_eq (substituted_rename _ _ _ _ _ _ _ _ _ s) (move hOldPre)
  have hBase := Derives.conjR (.conjR (SyntaxMixedFormulaOutput.input_of_substituted hZ1
    (s w) (s R) (s Base) (s z) (s f) (s z) (s d) (s (raw 0)) (s OldPre) hw hOldPre1))
  refine ForcingWeakenedOverwrite.with_base_of_update hZ1 (s w) (s A) (s f) (s z) (s d) B'
    Bound (s Base) (s j) (s Sel) (s (images 9)) v (.conjL (.conjR hOpen)) hBase
    (of_eq (SyntaxTermSyntax.term_rename _ _ _ _ s) (move hSel))
    (of_eq (ForcingReflexiveImages.replacement_rename _ _ _ _ _ _ _ _ s) (move hBaseUpdate))
    (out.rename s) ?_
  intro l1 Δ1 e baseV sel hZbase advance hBaseImages hSel1 hUpdate1
  let baseMap := e ∘ s
  have carryBase {F : Formula m} (h : Derives Γ F) : Derives Δ1 (F.rename baseMap) :=
    of_eq (SourceAlgebra.rename_comp F s e) (advance (move h))
  have hw1 := of_eq (omega_rename _ e) (advance hw)
  have hz1 := of_eq (empty_rename _ e) (advance hz)
  have hQ1 := of_eq (SyntaxTermSyntax.term_rename _ _ _ _ e) (advance hQ)
  have hr1 := of_eq (SyntaxTermSyntax.term_rename _ _ _ _ e) (advance hr)
  have hFree := Derives.conjR (SyntaxMixedImageCodePairs.term_lists (baseMap w) (baseV 6) (baseV 7)
    (baseMap A) (baseMap f) (baseMap z) (e B') (baseV 8) (baseV 9) (.conjR (.conjR (.conjR (.conjR hBaseImages)))))
  have hQdirect := ForcingReflexiveImages.replacement_after_replacement hZbase (baseMap w) (baseMap f) (baseMap z)
    (e B') (baseV 9) (baseMap j) sel (e (v 9)) (e Q) (e Fq) hw1 hFree hQ1 hUpdate1
    (of_eq (ForcingReflexiveImages.replacement_rename _ _ _ _ _ _ _ _ e) (advance hFq))
  have hRdirect := ForcingReflexiveImages.replacement_after_replacement hZbase (baseMap w) (baseMap f) (baseMap z)
    (e B') (baseV 9) (baseMap j) sel (e (v 9)) (e T) (e Fr) hw1 hFree hr1 hUpdate1
    (of_eq (ForcingReflexiveImages.replacement_rename _ _ _ _ _ _ _ _ e) (advance hFr))
  apply of_eq (SourceAlgebra.rename_comp out s e).symm
  refine with_raised_witness_monotonicity hZbase Reln Dom (baseMap w) (baseMap z) (baseMap a) (baseMap f) (baseMap j) (baseMap d) (e B')
    (baseMap A) (e Bound) (baseMap Base) (baseMap R) (e K') (e Fq) (e Fr) (baseMap A1) (baseMap A2) (baseMap A3) (baseMap K) (baseMap c)
    (baseMap H) (e Extra) (e Local) (e Q) (e T) (baseMap n) (baseMap C) (baseMap Yq) (e AtQ) (e AtR) (baseMap OldPre)
    (baseMap A) (e OrderHead) (e OrderCode) (e (x 2)) (e (v 9)) sel
    (baseMap ∘ raw) baseV (e ∘ membersQ) (e ∘ membersR) hw1 hz1
    (of_eq (SyntaxNumeralSyntax.numeral_rename _ _ baseMap) (carryBase hA1))
    (of_eq (SyntaxNumeralSyntax.numeral_rename _ _ baseMap) (carryBase hA2))
    (of_eq (SyntaxNumeralSyntax.numeral_rename _ _ baseMap) (carryBase hA3))
    (of_eq (SyntaxNumeralSyntax.numeral_rename _ _ baseMap) (carryBase hf))
    (of_eq (SyntaxNumeralSyntax.numeral_rename _ _ baseMap) (carryBase hK))
    (of_eq (SyntaxNumeralSyntax.numeral_rename _ _ baseMap) (carryBase hj))
    (of_eq (successor_rename _ _ e) (advance hc)) hBaseImages
    (of_eq (SyntaxMixedImageCodeSyntax.termList_rename _ _ _ _ _ e) (advance hTable))
    hQdirect hRdirect hUpdate1 hQ1 hr1
    (of_eq (ForcingPreorderCode.rawData_rename Reln _ _ _ _ _ _ _ baseMap) (carryBase hRaw))
    (of_eq (formulaCode_rename _ _ _ _ baseMap) (carryBase hSource))
    (of_eq (ForcingCodeRecursion.compiled_rename Reln Dom _ _ _ _ _ _ _ baseMap) (carryBase hChild))
    (of_eq (substituted_rename _ _ _ _ _ _ _ _ _ e) (advance hAtQ))
    (of_eq (substituted_rename _ _ _ _ _ _ _ _ _ e) (advance hAtR))
    (of_eq (formulaCode_rename _ _ _ _ e) (advance (.conjR hLocal)))
    (of_eq (substituted_rename _ _ _ _ _ _ _ _ _ baseMap) (carryBase hOldPre))
    (of_eq (SyntaxWeakenFreeSyntax.weakened_rename _ _ _ _ _ _ e) (advance hWeakExtra))
    (of_eq (SyntaxWeakenFreeSyntax.weakened_rename _ _ _ _ _ _ e) (advance hWeakQ))
    (of_eq (ForcingGuardOpening.result_rename true (ForcingExistGuardsCode.reverseOrder Reln)
      _ _ _ _ _ _ _ _ _ _ e) (advance hOrder))
    (of_eq (ForcingGuardOpening.result_rename false Reln _ _ _ _ _ _ _ _ _ _ e) (advance hMQ))
    (of_eq (ForcingGuardOpening.result_rename false Reln _ _ _ _ _ _ _ _ _ _ e) (advance hMR))
    (of_eq (implication_rename test _ _ _ _ _ baseMap) (carryBase pOldPre))
    (of_eq (implication_rename test _ _ _ _ _ baseMap) (carryBase pOldPositive))
    (of_eq (implication_rename test _ _ _ _ _ e) (advance pExtra))
    (of_eq (implication_rename test _ _ _ _ _ e) (advance pMQ))
    (of_eq (implication_rename test _ _ _ _ _ e) (advance pMR))
    (of_eq (implication_rename test _ _ _ _ _ e) (advance pOrder)) (out.rename baseMap) ?_
  intro l2 Ξ δ R' B'' Refl Pre U0 P nextImages rows layout hZ2 finish er eq hRuntime hPre
    pGlobal pAtR
  let t := δ ∘ e
  let ρ := δ ∘ baseMap
  have move2 {F : Formula l} (h : Derives Δ F) : Derives Ξ (F.rename t) :=
    of_eq (SourceAlgebra.rename_comp F e δ) (finish (advance h))
  have carry {F : Formula m} (h : Derives Γ F) : Derives Ξ (F.rename ρ) :=
    of_eq (SourceAlgebra.rename_comp F baseMap δ) (finish (carryBase h))
  let WitnessBase := δ (baseV 9)
  let row : Fin 24 → Fin l2 := fun i => rows (i.castAdd 24)
  have hGlobal := Derives.conjL hRuntime
  have hRows := Derives.conjL (.conjL hGlobal)
  have hRow := Derives.conjL (.conjR hRows)
  have hLayout := Derives.conjR (.conjR (.conjR hGlobal))
  have hExtra := Derives.conjL (.conjR (.conjR hGlobal))
  have hw2 := of_eq (omega_rename _ t) (move2 hw)
  have hz2 := of_eq (empty_rename _ t) (move2 hz)
  have hPreInput := SyntaxMixedFormulaOutput.input_of_substituted hZ2 (ρ w) R' WitnessBase
    (ρ z) (ρ f) (ρ z) (t B') (ρ (raw 0)) (Pre 0) hw2 hPre
  have hBase := Derives.conjR (.conjR hPreInput)
  have hTerm : Derives Ξ (SyntaxTermSyntax.term (ρ w) (ρ z) (t B') (P 0 1)) := by
    rw [er]
    exact of_eq (SyntaxTermSyntax.term_rename _ _ _ _ t) (move2 hr)
  have hUpdate : Derives Ξ (ForcingReflexiveImages.replacement (ρ w) (ρ f) (ρ z) (t B')
      WitnessBase (ρ j) (P 0 1) (t Fr)) := by
    rw [er]
    exact of_eq (ForcingReflexiveImages.replacement_rename _ _ _ _ _ _ _ _ δ) (finish hRdirect)
  have hLocal2 := of_eq (by simp only [FormulaCodeConstructSyntax.typedAt_rename, SyntaxAtomSyntax.two_map]; rfl)
    (move2 hLocal)
  have hAtR2 := of_eq (substituted_rename _ _ _ _ _ _ _ _ _ t) (move2 hAtR)
  have hNegR2 := of_eq (substituted_rename _ _ _ _ _ _ _ _ _ t) (move2 hNegR)
  have pNeg2 := of_eq (implication_rename test _ _ _ _ _ t) (move2 pNeg)
  have hOuter := Derives.conjL (.conjL hNeg)
  have hScope := Derives.conjL (.conjR (.conjR hOuter))
  have hCompiler := Derives.conjL (.conjR hNeg)
  have hShell := Derives.conjL (.conjR (.conjR hNeg))
  have pBot := ForcingDensityGuards.negative_reflexive_contradiction hZ2 Reln
    (ρ w) (ρ z) (ρ a) (ρ A) (ρ f) (t B') (ρ j) (t K') (t Fr) WitnessBase (ρ K) (t Extra)
    (ρ A1) (ρ A2) (ρ A3) (ρ c) R' (Refl 0) (Pre 0) (ρ C) (ρ N) (t AtR) (t (x 3)) (t Local)
    (ρ ∘ raw) (ForcingMemberRows.backgroundFields row) (ForcingMemberRows.leafFields row) layout
    (ForcingMemberRows.nativeFields (U0 0) row) (ForcingMemberRows.proofFields row) (P 0)
    (ForcingMemberRows.tailFields row) (ForcingMemberRows.prefixFields row) (ρ ∘ negData) (ρ ∘ negNodes)
    hw2 hz2 (of_eq (successor_rename _ _ ρ) (carry hScope)) hTerm
    (of_eq (SyntaxNumeralSyntax.numeral_rename _ _ ρ) (carry hK))
    (of_eq (SyntaxNumeralSyntax.numeral_rename _ _ ρ) (carry hf))
    (of_eq (SyntaxNumeralSyntax.numeral_rename _ _ ρ) (carry hj)) hBase hUpdate
    (of_eq (SyntaxNumeralSyntax.numeral_rename _ _ ρ) (carry hA1))
    (of_eq (SyntaxNumeralSyntax.numeral_rename _ _ ρ) (carry hA2)) hRow hPre hExtra hLayout
    (of_eq (ForcingNegCode.data_rename Reln _ _ _ _ _ _ _ negData ρ) (carry hCompiler))
    (of_eq (ForcingNegCode.shellData_rename _ _ _ _ _ _ _ _ negNodes ρ) (carry hShell))
    hAtR2 hNegR2 (.conjR hLocal2) pGlobal pAtR pNeg2
  have hOpen2 := of_eq (ForcingFreshParentOpening.quantifiedData_rename false _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ t)
    (move2 hOpen)
  have hWeak2 := of_eq (SyntaxWeakenFreeSyntax.weakened_rename _ _ _ _ _ _ t) (move2 hWeakExtra)
  have pTail2 := of_eq (implication_rename test _ _ _ _ _ t) (move2 hTail)
  have hOpenedBody := Derives.conjR (.conjR (.conjR (.conjR
    (.conjR (.conjR (.conjR (.conjR hOpen2)))))))
  have hBotCtor : Derives Ξ (SyntaxNodeSyntax.constructor 0 0 (ρ w) Fin.elim0 (ρ (negNodes 0))) :=
    of_eq (by simp only [SyntaxNodeSyntax.constructor_rename, SyntaxAtomSyntax.zero_map])
      (carry (.conjL (.conjL hShell)))
  have pOuterBot := ForcingDensityGuards.negative_witness_discharge hZ2 (ρ w) (ρ z) (ρ d) (ρ c)
    (t B') (ρ H) (t Extra) (t (u 8)) (t (u 4)) (t Tail) (t Local) (ρ (negNodes 0))
    hw2 hz2 (of_eq (formulaCode_rename _ _ _ _ ρ) (carry hH)) hWeak2
    (.conjR (.conjR (.conjR hOpenedBody))) (.conjL (.conjR hOpenedBody))
    (.conjL hLocal2) hBotCtor pTail2 pBot
  exact of_eq (SourceAlgebra.rename_comp out baseMap δ).symm
    (of_eq (implication_rename test _ _ _ _ _ ρ).symm pOuterBot)

private theorem second_witness_guards {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (Reln : Formula (k+2)) (Dom : Formula (k+1)) (leaf : Fin 3)
    (first : ForcingRelationRawTerms.reversed id (ForcingRelationSource.leftIndex leaf) = 0)
    (w z a A B C f j Child Parent Br c Fresh Pfx Selected Tail A1 A2 A3 K R Base Refl Pre U0 Selection : Fin m)
    (raw : Fin 16 → Fin m) (P : Fin 3 → Fin m) (row : Fin 24 → Fin m)
    (cv : Fin 8 → Fin m) (sv : Fin 7 → Fin m) (v : Fin 10 → Fin m)
    (u : Fin 9 → Fin m) (x : Fin 4 → Fin m)
    (ha : Derives Γ (.mem a w)) (hA : Derives Γ (successor A a))
    (h1 : Derives Γ (SyntaxNumeralSyntax.numeral 1 A1))
    (h2 : Derives Γ (SyntaxNumeralSyntax.numeral 2 A2))
    (h3 : Derives Γ (SyntaxNumeralSyntax.numeral 3 A3))
    (hF : Derives Γ (SyntaxNumeralSyntax.numeral (k+2) f))
    (hK : Derives Γ (SyntaxNumeralSyntax.numeral k K))
    (hj : Derives Γ (SyntaxNumeralSyntax.numeral (k+1) j))
    (hR : Derives Γ (SyntaxMixedImageCodeSyntax.termList w z z Fresh R))
    (hBase : Derives Γ (SyntaxMixedImageCodeSyntax.termList w f z Fresh Base))
    (hRow : Derives Γ (ForcingMemberRows.rowData test Reln w z A1 A2 A3 f Fresh c R Base Refl Pre U0 raw P row))
    (hSelected : Derives Γ (ForcingReflexiveImages.replacement w f z Fresh Base j Selection (v 9)))
    (hRField : Derives Γ (StructuralListFieldSyntax.field w (v 8) z
      (P (ForcingRelationRawTerms.reversed id (ForcingRelationSource.rightIndex leaf)))))
    (hCompiler : Derives Γ (ForcingExistCode.data Reln Dom w a A B C f j Child Parent cv))
    (hOpen : Derives Γ (ForcingFreshParentOpening.quantifiedData false w z A f B Br c Fresh (P 0)
      Pfx Selected (sv 4) (sv 3) Tail v u))
    (hFields : Derives Γ (ForcingRawModalBody.nestedData 0 w (u 7) (v 9) B f z Fresh
      (cv 4) (cv 5) (sv 1) (sv 2) (u 8) x)) :
    Derives Γ ((Formula.equal (ForcingMemberRows.leafFields row 0) (x 1)).conj
      (Formula.equal (ForcingMemberRows.leafFields row (ForcingPreorderLeaves.relationPosition leaf)) (x 2))) := by
  let upper := P (ForcingRelationRawTerms.reversed id (ForcingRelationSource.rightIndex leaf))
  let H := ForcingMemberRows.leafFields row
  let G := ForcingMemberRows.backgroundFields row
  let U := ForcingMemberRows.nativeFields U0 row
  let F := ForcingMemberRows.proofFields row
  let N := ForcingMemberRows.tailFields row
  let V := ForcingMemberRows.prefixFields row
  have hInput := Derives.conjL hOpen
  have hw := Derives.conjL hInput
  have hz := Derives.conjL (.conjR hInput)
  have hB := Derives.conjL (.conjR (.conjR hInput))
  have hs := Derives.conjL (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR hInput))))))
  have hCons := Derives.conjL (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR hOpen)))))))
  have hLift := Derives.conjL (.conjR (.conjR (.conjR hOpen)))
  have hLists := SyntaxCodedMixedBinderTyping.input_lists w (v 8) (v 9) A f z Fresh B c (u 2) (u 3) hLift
  have hNames := Derives.conjL hLists
  have hFree := Derives.conjR hLists
  have hzA := SyntaxIndexLiftOrder.zero_member hZ w a A z hw ha hA hz
  have hzB := SyntaxIndexLiftOrder.zero_member hZ w A B z hw (.conjL hNames) hB hz
  have hsField := StructuralListFieldCons.zero_value hZ w (P 0) (v 8) (u 7) z hw
    (SyntaxTerms.range hZ w z Fresh (P 0) hw hs) (.conjL (.conjL (.conjR (.conjR hNames)))) hCons hz
  have hHead := Derives.conjL hCompiler
  have eZero := OmegaUniversal.empty_unique (cv 0) z (ZFContext.arithmetic hZ).base.extensionality (.conjL hHead) hz
  have hVar := SyntaxVariableImagePoint.code_subst_index true w (cv 0) (cv 1) z eZero (.conjL (.conjR hHead))
  have hMember := ForcingGuardOpening.from_lifted_at hZ false Reln w z B f z Fresh (u 7) (v 9)
    (cv 1) (P 0) (cv 4) (x 1) hw hz hVar hzB hsField
    (.conjL (.conjR (.conjR (.conjR hCompiler)))) (.conjL (.conjR (.conjL hFields)))
  have eMember := ForcingDensityGuards.witness_member_from_updated_row hZ Reln 0 w z A1 A2 A3 f Fresh c R Base
    (v 9) Refl Pre B (cv 1) (cv 4) (x 1) K j Selection raw G H U F P N V
    hw hz h1 h2 hF hK hBase hRow hj hSelected hMember
  apply Derives.conjI eMember
  let out := Formula.equal (H (ForcingPreorderLeaves.relationPosition leaf)) (x 2)
  have hNew := ForcingReflexiveImages.exists_replacement hZ w f z Fresh (v 9) j (P 0) hw hFree hs
  refine eliminate_objects hZ 1 (fun r y => ForcingReflexiveImages.replacement (r w) (r f) (r z)
    (r Fresh) (r (v 9)) (r j) (r (P 0)) (y 0)) hNew out ?_
  intro l Δ r y hZ1 lift hReplace
  have hw1 := of_eq (omega_rename _ r) (lift hw)
  have hz1 := of_eq (empty_rename _ r) (lift hz)
  have hs1 := of_eq (SyntaxTermSyntax.term_rename _ _ _ _ r) (lift hs)
  have hBase1 := of_eq (SyntaxMixedImageCodeSyntax.termList_rename _ _ _ _ _ r) (lift hBase)
  have hDirect := ForcingReflexiveImages.replacement_after_replacement hZ1 (r w) (r f) (r z)
    (r Fresh) (r Base) (r j) (r Selection) (r (v 9)) (r (P 0)) (y 0) hw1 hBase1 hs1
    (of_eq (ForcingReflexiveImages.replacement_rename _ _ _ _ _ _ _ _ r) (lift hSelected)) hReplace
  refine ForcingExistOrderOpening.with_prefixed_guard hZ1 Reln (r w) (r z) (r A) (r B) (r f) (r j) (r Fresh)
    (r (u 7)) (r (v 9)) (r (v 8)) (r (P 0)) (r upper) (y 0) (r (cv 5)) (r (x 2))
    hw1 hz1 hs1 (of_eq (SyntaxMixedImageCodeSyntax.termList_rename _ _ _ _ _ r) (lift hNames))
    (of_eq (StructuralListSyntax.consCode_rename _ _ _ _ r) (lift hCons)) (lift hzA)
    (of_eq (StructuralListFieldSyntax.field_rename _ _ _ _ r) (lift hRField)) hReplace
    (of_eq (ForcingExistGuardsCode.compiled_rename Reln _ _ _ _ _ _ r)
      (lift (.conjL (.conjR (.conjR (.conjR (.conjR hCompiler)))))))
    (of_eq (substituted_rename _ _ _ _ _ _ _ _ _ r) (lift (.conjL (.conjR (.conjR hFields))))) (out.rename r) ?_
  intro l1 Ξ σ head order hZ2 move hOrder
  let e := σ ∘ r
  have carry {J : Formula m} (p : Derives Γ J) : Derives Ξ (J.rename e) :=
    of_eq (SourceAlgebra.rename_comp J r σ) (move (lift p))
  apply of_eq (SourceAlgebra.rename_comp out r σ).symm
  refine ForcingDensityGuards.order_from_row hZ2 Reln leaf (e w) (e z) (e A1) (e A2) (e A3) (e f) (e Fresh)
    (e c) (e R) (e Base) (e Refl) (e Pre) (σ (y 0)) (e A) head order (e (x 2)) (e j)
    (e ∘ raw) (e ∘ G) (e ∘ H) (e ∘ U) (e ∘ F) (e ∘ P) (e ∘ N) (e ∘ V)
    (of_eq (omega_rename _ e) (carry hw)) (of_eq (empty_rename _ e) (carry hz))
    (of_eq (SyntaxNumeralSyntax.numeral_rename _ _ e) (carry h1))
    (of_eq (SyntaxNumeralSyntax.numeral_rename _ _ e) (carry h2))
    (of_eq (SyntaxNumeralSyntax.numeral_rename _ _ e) (carry h3))
    (of_eq (SyntaxNumeralSyntax.numeral_rename _ _ e) (carry hF))
    (of_eq (SyntaxNumeralSyntax.numeral_rename _ _ e) (carry hj))
    (fun i => of_eq (SyntaxTermSyntax.term_rename _ _ _ _ e) (carry (ForcingRelationWeakening.row_term test Reln
      w z A1 A2 A3 f Fresh c R Base Refl Pre U0 raw P row hRow i)))
    (of_eq (SyntaxMixedImageCodeSyntax.termList_rename _ _ _ _ _ e) (carry hR))
    (of_eq (SyntaxMixedImageCodeSyntax.termList_rename _ _ _ _ _ e) (carry hBase))
    (of_eq (ForcingPreorderLeaves.data_rename test Reln _ _ _ _ _ _ _ _ _ _ _ _ raw G H U F P N V e) (carry hRow))
    ?_ hOrder
  rw [first]
  exact of_eq (ForcingReflexiveImages.replacement_rename _ _ _ _ _ _ _ _ σ) (move hDirect)

-- Open the actual second body under the weakening of the first local
-- assumptions. Both body conjunctions are the literal compiler outputs.
private theorem with_second_local_proofs {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z b B Local Global Raised Body M I O Name Id Shift : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) (hB : Derives Γ (successor B b))
    (hLocal : Derives Γ (formulaCode w Local z b))
    (hBody : Derives Γ (formulaCode w Body z B)) (hM : Derives Γ (formulaCode w M z B))
    (hI : Derives Γ (formulaCode w I z B)) (hO : Derives Γ (formulaCode w O z B))
    (hName : Derives Γ (formulaCode w Name z B))
    (hOuter : Derives Γ (binaryCode 0 w M I Body)) (hInner : Derives Γ (binaryCode 0 w O Name I))
    (hId : Derives Γ (SyntaxIdentityMapSyntax.identityCode w z Id))
    (hShift : Derives Γ (SyntaxFreeShiftSyntax.shiftCode w b B Shift))
    (hWeakGlobal : Derives Γ (SyntaxWeakenFreeSyntax.weakened w z b B Global Raised))
    (pGlobal : Derives Γ (implication test w z b Local Global))
    (out : Formula m)
    (use : ∀ {l} {Δ : Context l} (r : Fin m → Fin l) (Weak LocalS : Fin l), ZFContext.Evidence Δ →
      (∀ {F : Formula m}, Derives Γ F → Derives Δ (F.rename r)) →
      Derives Δ (SyntaxWeakenFreeSyntax.weakened (r w) (r z) (r b) (r B) (r Local) Weak) →
      Derives Δ (FormulaCodeConstructSyntax.typedAt 2 5 (r w)
        (SyntaxAtomSyntax.two Weak (r Body)) LocalS (r z) (r B)) →
      Derives Δ (implication test (r w) (r z) (r B) LocalS (r Raised)) →
      Derives Δ (implication test (r w) (r z) (r B) LocalS (r M)) →
      Derives Δ (implication test (r w) (r z) (r B) LocalS (r O)) →
      Derives Δ (implication test (r w) (r z) (r B) LocalS (r Name)) →
      Derives Δ (out.rename r)) : Derives Γ out := by
  have hWeak := SyntaxWeakenFreeOutput.exists_at_codes hZ w z b B Local Id Shift hw hLocal hId hShift
  refine eliminate_objects hZ 1 (fun r x => SyntaxWeakenFreeSyntax.weakened
    (r w) (r z) (r b) (r B) (r Local) (x 0)) hWeak out ?_
  intro l Δ r x hZ1 lift hWeak1
  have hw1 := of_eq (omega_rename _ r) (lift hw)
  have hWeakT := SyntaxWeakenFreeOutput.target_type (r w) (r z) (r b) (r B) (r Local) (x 0) hWeak1
  have hAnd := ForcingProofContext.and_exists hZ1 (r w) (r z) (r B) (x 0) (r Body)
    hw1 hWeakT (of_eq (formulaCode_rename _ _ _ _ r) (lift hBody))
  refine eliminate_objects hZ1 1 (fun s x' => (Formula.mem (x' 0) (s (r w))).conj
    (FormulaCodeConstructSyntax.typedAt 2 5 (s (r w)) (SyntaxAtomSyntax.two (s (x 0)) (s (r Body)))
      (x' 0) (s (r z)) (s (r B)))) hAnd (out.rename r) ?_
  intro l1 Ξ s y hZ2 move hLocal2
  let e := s ∘ r
  have carry {F : Formula m} (p : Derives Γ F) : Derives Ξ (F.rename e) :=
    of_eq (SourceAlgebra.rename_comp F r s) (move (lift p))
  let Weak := s (x 0)
  let LocalS := y 0
  have hw2 := of_eq (omega_rename _ e) (carry hw)
  have hz2 := of_eq (empty_rename _ e) (carry hz)
  have hWT := of_eq (formulaCode_rename _ _ _ _ s) (move hWeakT)
  have hBT := of_eq (formulaCode_rename _ _ _ _ e) (carry hBody)
  have hMT := of_eq (formulaCode_rename _ _ _ _ e) (carry hM)
  have hIT := of_eq (formulaCode_rename _ _ _ _ e) (carry hI)
  have hOT := of_eq (formulaCode_rename _ _ _ _ e) (carry hO)
  have hNT := of_eq (formulaCode_rename _ _ _ _ e) (carry hName)
  have hLT := Derives.conjR (.conjR hLocal2)
  have hLC := Derives.conjL (.conjR hLocal2)
  have hOuter2 := of_eq (binaryCode_rename _ _ _ _ _ e) (carry hOuter)
  have hInner2 := of_eq (binaryCode_rename _ _ _ _ _ e) (carry hInner)
  have hWeak2 := of_eq (SyntaxWeakenFreeSyntax.weakened_rename _ _ _ _ _ _ s) (move hWeak1)
  have hWeakGlobal2 := of_eq (SyntaxWeakenFreeSyntax.weakened_rename _ _ _ _ _ _ e) (carry hWeakGlobal)
  have pWeakGlobal := ForcingOldParentInstance.raise_implication hZ2 test (e w) (e z) (e b) (e B)
    (e Local) (e Global) Weak (e Raised) (e Id) (e Shift) hw2 hz2
    (of_eq (successor_rename _ _ e) (carry hB))
    (of_eq (SyntaxIdentityMapSyntax.identityCode_rename _ _ _ e) (carry hId))
    (of_eq (SyntaxFreeShiftSyntax.shiftCode_rename _ _ _ _ e) (carry hShift)) hWeak2 hWeakGlobal2
    (of_eq (implication_rename test _ _ _ _ _ e) (carry pGlobal))
  have pWeak := ForcingRelationGuardProof.project hZ2 test false (e w) (e z) (e B)
    Weak (e Body) LocalS hw2 hz2 hWT hBT hLT hLC
  have pBody := ForcingRelationGuardProof.project hZ2 test true (e w) (e z) (e B)
    Weak (e Body) LocalS hw2 hz2 hWT hBT hLT hLC
  have pWide := ForcingRelationGuardProof.chain hZ2 test (e w) (e z) (e B)
    LocalS Weak (e Raised) hw2 hz2 hLT hWT
    (SyntaxWeakenFreeOutput.target_type (e w) (e z) (e b) (e B) (e Global) (e Raised) hWeakGlobal2) pWeak pWeakGlobal
  have pM := ForcingRelationGuardProof.chain hZ2 test (e w) (e z) (e B) LocalS (e Body) (e M)
    hw2 hz2 hLT hBT hMT pBody (ForcingRelationGuardProof.project hZ2 test false (e w) (e z) (e B)
      (e M) (e I) (e Body) hw2 hz2 hMT hIT hBT hOuter2)
  have pI := ForcingRelationGuardProof.chain hZ2 test (e w) (e z) (e B) LocalS (e Body) (e I)
    hw2 hz2 hLT hBT hIT pBody (ForcingRelationGuardProof.project hZ2 test true (e w) (e z) (e B)
      (e M) (e I) (e Body) hw2 hz2 hMT hIT hBT hOuter2)
  have pO := ForcingRelationGuardProof.chain hZ2 test (e w) (e z) (e B) LocalS (e I) (e O)
    hw2 hz2 hLT hIT hOT pI (ForcingRelationGuardProof.project hZ2 test false (e w) (e z) (e B)
      (e O) (e Name) (e I) hw2 hz2 hOT hNT hIT hInner2)
  have pN := ForcingRelationGuardProof.chain hZ2 test (e w) (e z) (e B) LocalS (e I) (e Name)
    hw2 hz2 hLT hIT hNT pI (ForcingRelationGuardProof.project hZ2 test true (e w) (e z) (e B)
      (e O) (e Name) (e I) hw2 hz2 hOT hNT hIT hInner2)
  exact of_eq (SourceAlgebra.rename_comp out r s).symm
    (use e Weak LocalS hZ2 carry hWeak2 (.conjR hLocal2) pWide pM pO pN)

-- Apply the original transitivity proof to the actual second witness
-- guards. The original name existential is projected from the same body.
private theorem with_second_witness_transitivity {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (Reln : Formula (k+2)) (w z A1 A2 A3 f b B R S K Extra Local Body M I O Name : Fin m)
    (raw : Fin 16 → Fin m) (images : Fin 10 → Fin m) (C Refl Pre U0 : Fin 2 → Fin m)
    (P : Fin 2 → Fin 3 → Fin m) (rows : Fin 48 → Fin m) (layout : Fin 6 → Fin m)
    (hRuntime : Derives Γ (ForcingGlobalWeakening.input test Reln w z A1 A2 A3 f b B R S K Extra
      raw images C Refl Pre U0 P rows layout))
    (hLocal : Derives Γ (formulaCode w Local z b))
    (hBody : Derives Γ (formulaCode w Body z B)) (hM : Derives Γ (formulaCode w M z B))
    (hI : Derives Γ (formulaCode w I z B)) (hO : Derives Γ (formulaCode w O z B))
    (hName : Derives Γ (formulaCode w Name z B))
    (hOuter : Derives Γ (binaryCode 0 w M I Body)) (hInner : Derives Γ (binaryCode 0 w O Name I))
    (hGuards : Derives Γ (let row : Fin 24 → Fin m := fun i => rows (i.addNat 24)
      (Formula.equal (ForcingMemberRows.leafFields row 0) M).conj
        (Formula.equal (ForcingMemberRows.leafFields row 3) O)))
    (hTrans : Derives Γ (let row : Fin 24 → Fin m := fun i => rows (i.addNat 24)
      implication test w z B (ForcingMemberRows.backgroundFields row 0) (ForcingMemberRows.leafFields row 5)))
    (pGlobal : Derives Γ (implication test w z b Local (layout 3)))
    (out : Formula m)
    (use : ∀ {l} {Δ : Context l} (r : Fin m → Fin l) (Weak LocalS : Fin l), ZFContext.Evidence Δ →
      (∀ {F : Formula m}, Derives Γ F → Derives Δ (F.rename r)) →
      Derives Δ (SyntaxWeakenFreeSyntax.weakened (r w) (r z) (r b) (r B) (r Local) Weak) →
      Derives Δ (FormulaCodeConstructSyntax.typedAt 2 5 (r w)
        (SyntaxAtomSyntax.two Weak (r Body)) LocalS (r z) (r B)) →
      Derives Δ (implication test (r w) (r z) (r B) LocalS (r M)) →
      Derives Δ (implication test (r w) (r z) (r B) LocalS (r Name)) →
      Derives Δ (implication test (r w) (r z) (r B) LocalS
        (r (ForcingMemberRows.leafFields (fun i => rows (i.addNat 24)) 5))) →
      Derives Δ (out.rename r)) : Derives Γ out := by
  let row : Fin 24 → Fin m := fun i => rows (i.addNat 24)
  let H := ForcingMemberRows.leafFields row
  let G := ForcingMemberRows.backgroundFields row
  let F := ForcingMemberRows.proofFields row
  let U := ForcingMemberRows.nativeFields (U0 1) row
  let N := ForcingMemberRows.tailFields row
  let V := ForcingMemberRows.prefixFields row
  have hRows := Derives.conjL (.conjL hRuntime)
  have hLeaves := Derives.conjL (.conjR (.conjR hRows))
  have hRow := Derives.conjL (.conjL (.conjR hLeaves))
  have hFresh := Derives.conjL (.conjR hRuntime)
  have hImages := Derives.conjL (.conjR (.conjR (.conjL hFresh)))
  have hMaps := Derives.conjL (.conjR hImages)
  have hw := Derives.conjL (.conjL hImages)
  have hz := Derives.conjL (.conjL hFresh)
  have hB := Derives.conjL (.conjR (.conjL hImages))
  have hTypes (i : Fin 6) : Derives Γ (formulaCode w (H i) z B) :=
    SyntaxMixedFormulaJudgment.target_type w (V 2) (images 9) A3 f z B _ _
      (ForcingPreorderLeaves.leaf_at w (V 2) (images 9) A3 f z B raw H N i
        (.conjR (.conjR (.conjR (.conjR hLeaves)))))
  have hLayout := ForcingGlobalWeakening.produce hZ test Reln w z A1 A2 A3 f b B R S K Extra
    raw images C Refl Pre U0 P rows layout hRuntime
  refine eliminate_objects hZ 7 (fun r y => ForcingGlobalWeakening.data test Reln (r w) (r z)
    (r A1) (r A2) (r A3) (r f) (r b) (r B) (r R) (r S) (r K) (r Extra) (r ∘ raw) (r ∘ images)
    (r ∘ C) (r ∘ Refl) (r ∘ Pre) (r ∘ U0) (fun i => r ∘ P i) (r ∘ rows) (r ∘ layout) y) hLayout out ?_
  intro l Δ r y hZ1 lift hData
  let next : Fin 6 → Fin l := fun i => y i.succ
  have hLayout1 := Derives.conjL (.conjR (.conjR hData))
  have hWeakGlobal := Derives.conjR (.conjR (.conjR hData))
  have hExtra1 := SyntaxWeakenFreeOutput.target_type (r w) (r z) (r b) (r B) (r Extra) (y 0)
    (.conjL (.conjR hData))
  have hw1 := of_eq (omega_rename _ r) (lift hw)
  have hz1 := of_eq (empty_rename _ r) (lift hz)
  have hRow1 := of_eq (ForcingTransitiveGuardProof.row_rename _ _ _ _ _ _ G H U F (P 1) N r) (lift hRow)
  have pRow := Derives.conjR (ForcingProofContext.canonical_projections hZ1 test (r w) (r z) (r B)
    (r (C 1)) (r (Refl 1)) (r (Pre 1)) (y 0) (r ∘ G) (r ∘ H) (r ∘ U) (r ∘ F) (r ∘ P 1)
    (r ∘ N) next hw1 hz1 hExtra1 hRow1 hLayout1)
  refine with_second_local_proofs hZ1 (r w) (r z) (r b) (r B) (r Local) (r (layout 3)) (next 3)
    (r Body) (r M) (r I) (r O) (r Name) (r (images 0)) (r (images 1)) hw1 hz1
    (of_eq (successor_rename _ _ r) (lift hB))
    (of_eq (formulaCode_rename _ _ _ _ r) (lift hLocal))
    (of_eq (formulaCode_rename _ _ _ _ r) (lift hBody))
    (of_eq (formulaCode_rename _ _ _ _ r) (lift hM))
    (of_eq (formulaCode_rename _ _ _ _ r) (lift hI))
    (of_eq (formulaCode_rename _ _ _ _ r) (lift hO))
    (of_eq (formulaCode_rename _ _ _ _ r) (lift hName))
    (of_eq (binaryCode_rename _ _ _ _ _ r) (lift hOuter))
    (of_eq (binaryCode_rename _ _ _ _ _ r) (lift hInner))
    (of_eq (SyntaxIdentityMapSyntax.identityCode_rename _ _ _ r) (lift (.conjL hMaps)))
    (of_eq (SyntaxFreeShiftSyntax.shiftCode_rename _ _ _ _ r) (lift (.conjL (.conjR hMaps)))) hWeakGlobal
    (of_eq (implication_rename test _ _ _ _ _ r) (lift pGlobal)) (out.rename r) ?_
  intro l1 Ξ s Weak LocalS hZ2 move hWeak hLocal2 pWide pMember pOrder pName
  let e := s ∘ r
  have carry {F : Formula m} (p : Derives Γ F) : Derives Ξ (F.rename e) :=
    of_eq (SourceAlgebra.rename_comp F r s) (move (lift p))
  have hw2 := of_eq (omega_rename _ e) (carry hw)
  have hz2 := of_eq (empty_rename _ e) (carry hz)
  have hLT := Derives.conjR hLocal2
  have hTypes2 (i : Fin 6) := of_eq (formulaCode_rename _ _ _ _ e) (carry (hTypes i))
  have hLayout2 := of_eq (ForcingProofContext.layoutData_rename _ _ _ _ _ (r ∘ H) next s) (move hLayout1)
  have hGlobalT := Derives.conjR (.conjL (.conjR (.conjR (.conjR hLayout2))))
  have hLast := Derives.conjR (.conjR (.conjR (.conjR hLayout2)))
  have hPair := Derives.conjL hLast
  have hWide := Derives.conjR hLast
  have hEq := carry hGuards
  have pM := witness_proof_output (e w) (e z) (e B) LocalS (e M) (e (H 0)) (eq_symm (.conjL hEq)) pMember
  have pO := witness_proof_output (e w) (e z) (e B) LocalS (e O) (e (H 3)) (eq_symm (.conjR hEq)) pOrder
  have pPair := ForcingProofContext.join hZ2 test (e w) (e z) (e B) LocalS (e (H 0)) (e (H 3))
    (s (next 4)) hw2 hz2 hLT (hTypes2 0) (hTypes2 3) (.conjL hPair) pM pO
  have pLocal := ForcingProofContext.join hZ2 test (e w) (e z) (e B) LocalS (s (next 3)) (s (next 4))
    (s (next 5)) hw2 hz2 hLT hGlobalT (.conjR hPair) (.conjL hWide) pWide pPair
  have hBackground := of_eq (formulaCode_rename _ _ _ _ e) (carry (.conjL hRow))
  have pBackground := ForcingRelationGuardProof.chain hZ2 test (e w) (e z) (e B) LocalS
    (s (next 5)) (e (G 0)) hw2 hz2 hLT (.conjR hWide) hBackground pLocal
    (of_eq (implication_rename test _ _ _ _ _ s) (move pRow))
  have pTrans := ForcingRelationGuardProof.chain hZ2 test (e w) (e z) (e B) LocalS (e (G 0)) (e (H 5))
    hw2 hz2 hLT hBackground (hTypes2 5) pBackground
    (of_eq (implication_rename test _ _ _ _ _ e) (carry hTrans))
  exact of_eq (SourceAlgebra.rename_comp out r s).symm
    (use e Weak LocalS hZ2 carry hWeak hLocal2 pMember pName pTrans)

private def secondWitnessData {m} (w z b B Local Body M Name Order Weak LocalS : Fin m) : Formula m :=
  (SyntaxWeakenFreeSyntax.weakened w z b B Local Weak).conj
    ((FormulaCodeConstructSyntax.typedAt 2 5 w (SyntaxAtomSyntax.two Weak Body) LocalS z B).conj
      ((implication test w z B LocalS M).conj
        ((implication test w z B LocalS Name).conj (implication test w z B LocalS Order))))

private theorem secondWitnessData_rename {m l} (w z b B Local Body M Name Order Weak LocalS : Fin m)
    (r : Fin m → Fin l) :
    (secondWitnessData w z b B Local Body M Name Order Weak LocalS).rename r =
      secondWitnessData (r w) (r z) (r b) (r B) (r Local) (r Body) (r M) (r Name) (r Order) (r Weak) (r LocalS) := by
  simp only [secondWitnessData, Formula.rename, SyntaxWeakenFreeSyntax.weakened_rename,
    FormulaCodeConstructSyntax.typedAt_rename, SyntaxAtomSyntax.two_map, implication_rename]

private def secondWitnessProofs {m} (w z b B Local Body M Name Order : Fin m) : Formula m :=
  existsMany 2 (secondWitnessData (old 2 w) (old 2 z) (old 2 b) (old 2 B) (old 2 Local) (old 2 Body)
    (old 2 M) (old 2 Name) (old 2 Order) (slot 2 0) (slot 2 1))

private theorem secondWitnessProofs_rename {m l} (w z b B Local Body M Name Order : Fin m) (r : Fin m → Fin l) :
    (secondWitnessProofs w z b B Local Body M Name Order).rename r =
      secondWitnessProofs (r w) (r z) (r b) (r B) (r Local) (r Body) (r M) (r Name) (r Order) := by
  simp only [secondWitnessProofs, existsMany_rename, secondWitnessData_rename, lift_old, lift_slot]


-- Retain the weakening and top-instance executions of the actual name field.
-- The old body is identified by its existential constructor in both traces.
private theorem name_through_fresh_opening {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z A B f b c d t Prefix Selected Tail Body Parent M O E I Base j p : Fin m)
    (s : Fin 9 → Fin m) (v : Fin 16 → Fin m)
    (images : Fin 10 → Fin m) (u : Fin 9 → Fin m) (fields : Fin 4 → Fin m)
    (hScope : Derives Γ (ForcingExistTailOpening.scopeData w Prefix Selected A f z b Parent Base j p s v))
    (hOpen : Derives Γ (ForcingFreshParentOpening.quantifiedData false w z A f B b c d t Prefix Selected Tail Body Parent images u))
    (hFields : Derives Γ (ForcingRawModalBody.nestedData 0 w (u 7) (images 9) B f z d M O E I (u 8) fields))
    (hOuter : Derives Γ (binaryCode 0 w M I Body))
    (hInner : Derives Γ (binaryCode 0 w O E I)) :
    Derives Γ (.ex ((SyntaxWeakenFreeSyntax.weakened w.castSucc c.castSucc b.castSucc d.castSucc (v 8).castSucc (Fin.last m)).conj
      (SyntaxTopFormulaSyntax.instantiated w.castSucc z.castSucc d.castSucc c.castSucc t.castSucc (Fin.last m) (fields 3).castSucc))) := by
  have hInput := Derives.conjL hOpen
  have hw := Derives.conjL hInput
  have hNext := Derives.conjL (.conjR (.conjR (.conjR (.conjR hInput))))
  have hLift := Derives.conjR (.conjR (.conjR (.conjR hOpen)))
  have hAtWeak := Derives.conjL (.conjR hLift)
  have hEnd := Derives.conjR (.conjR (.conjR (.conjR (.conjR hLift))))
  have hInverse := Derives.conjL (.conjR hEnd)
  have hOps := Derives.conjR (.conjR (.conjR (.conjR hInverse)))
  have hData := Derives.conjL hScope
  have eqOld := SyntaxLogicalFields.single_fields hZ 10 w (u 4) (v 0) Parent hw (.conjL hEnd) (.conjL (.conjL hData))
  let oldWeak := SyntaxWeakenFreeSyntax.weakened w.castSucc c.castSucc b.castSucc d.castSucc (Fin.last m) (u 5).castSucc
  have hWeak : Derives Γ (SyntaxWeakenFreeSyntax.weakened w c b d (v 0) (u 5)) :=
    of_eq (by simp only [oldWeak, Formula.instantiate, SyntaxWeakenFreeSyntax.weakened_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
      (.eqSubst oldWeak eqOld (of_eq (by simp only [oldWeak, Formula.instantiate, SyntaxWeakenFreeSyntax.weakened_rename,
        Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjL hOps)))
  have hInst := Derives.conjR hOps
  have hTy := SyntaxWeakenFreeOutput.source_type hZ w c b d (v 0) (u 5) hw hWeak
  have hNat := Derives.conjR (FormulaCodeProperties.guards w (v 0) c b hTy)
  have hWeakFields := ForcingRawModalBody.nested_from_query hZ 0 w (u 2) (u 3) B f c d M O E I Body (u 5)
    hw hOuter hInner hAtWeak
  let out : Formula m := .ex ((SyntaxWeakenFreeSyntax.weakened w.castSucc c.castSucc b.castSucc d.castSucc (v 8).castSucc (Fin.last m)).conj
    (SyntaxTopFormulaSyntax.instantiated w.castSucc z.castSucc d.castSucc c.castSucc t.castSucc (Fin.last m) (fields 3).castSucc))
  refine eliminate_objects hZ 4 (fun r x =>
    ForcingRawModalBody.nestedData 0 (r w) (r (u 2)) (r (u 3)) (r B) (r f) (r c) (r d)
      (r M) (r O) (r E) (r I) (r (u 5)) x) hWeakFields out ?_
  intro l Δ r x hZ1 lift hW
  have hw1 := of_eq (omega_rename _ r) (lift hw)
  have hNext1 := of_eq (successor_rename _ _ r) (lift hNext)
  have hcn : Derives Δ (.mem (r c) (r w)) := lift (.conjL hNat)
  have hbn : Derives Δ (.mem (r b) (r w)) := lift (.conjR hNat)
  have hWeak1 := of_eq (SyntaxWeakenFreeSyntax.weakened_rename _ _ _ _ _ _ r) (lift hWeak)
  have hInst1 := of_eq (SyntaxTopFormulaSyntax.instantiated_rename _ _ _ _ _ _ _ r) (lift hInst)
  have hF := of_eq (ForcingRawModalBody.nestedData_rename _ _ _ _ _ _ _ _ _ _ _ _ _ fields r) (lift hFields)
  have oldOuter := of_eq (binaryCode_rename _ _ _ _ _ r) (lift (.conjL (.conjL (.conjR hData))))
  have oldInner := of_eq (binaryCode_rename _ _ _ _ _ r) (lift (.conjL (.conjL (.conjR (.conjR hData)))))
  have weakRest := Derives.conjR (.impE (.conjL (SyntaxWeakenFreeLogicalInternal.binary_iff hZ1 0
    (r w) (r c) (r b) (r d) (r (v 0)) (r (u 5)) (r (v 5)) (r (v 6)) (x 1) (x 0)
    hw1 hcn hbn hNext1 oldOuter (.conjL (.conjL hW)))) hWeak1)
  have weakName := Derives.conjR (.impE (.conjL (SyntaxWeakenFreeLogicalInternal.binary_iff hZ1 0
    (r w) (r c) (r b) (r d) (r (v 6)) (x 0) (r (v 7)) (r (v 8)) (x 2) (x 3)
    hw1 hcn hbn hNext1 oldInner (.conjL (.conjR hW)))) weakRest)
  have hTop := SyntaxTopFormulaTyping.instantiate_input hZ1 (r w) (r z) (r d) (r c) (r t) (r (u 5)) (r (u 8)) hw1 hInst1
  have instRest := Derives.conjR (.impE (.conjL (SyntaxTopFormulaLogicalEndpoints.instantiate_binary_iff hZ1 0
    (r w) (r z) (r d) (r c) (r t) (r (u 5)) (r (u 8)) (x 1) (x 0) (r (fields 1)) (r (fields 0))
    hw1 hTop (.conjL (.conjL hW)) (.conjL (.conjL hF)))) hInst1)
  have hTopRest := SyntaxTopFormulaTyping.instantiate_input hZ1 (r w) (r z) (r d) (r c) (r t)
    (x 0) (r (fields 0)) hw1 instRest
  have instName := Derives.conjR (.impE (.conjL (SyntaxTopFormulaLogicalEndpoints.instantiate_binary_iff hZ1 0
    (r w) (r z) (r d) (r c) (r t) (x 0) (r (fields 0)) (x 2) (x 3) (r (fields 2)) (r (fields 3))
    hw1 hTopRest (.conjL (.conjR hW)) (.conjL (.conjR hF)))) instRest)
  have result : Derives Δ (.ex ((SyntaxWeakenFreeSyntax.weakened (r w).castSucc (r c).castSucc (r b).castSucc
      (r d).castSucc (r (v 8)).castSucc (Fin.last l)).conj
    (SyntaxTopFormulaSyntax.instantiated (r w).castSucc (r z).castSucc (r d).castSucc (r c).castSucc
      (r t).castSucc (Fin.last l) (r (fields 3)).castSucc))) := by
    apply Derives.exI (x 3)
    exact of_eq (by simp only [Formula.instantiate, Formula.rename, SyntaxWeakenFreeSyntax.weakened_rename,
      SyntaxTopFormulaSyntax.instantiated_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI weakName instName)
  exact of_eq (by simp only [out, Formula.rename, SyntaxWeakenFreeSyntax.weakened_rename,
    SyntaxTopFormulaSyntax.instantiated_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]) result

private def nameExecution {m} (w z b c d t Name Open : Fin m) (weak : Fin m) : Formula m :=
  (SyntaxWeakenFreeSyntax.weakened w c b d Name weak).conj
    (SyntaxTopFormulaSyntax.instantiated w z d c t weak Open)

private theorem equal_fresh_name_codes {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z b c d t N N' Open Open' : Fin m) (hw : Derives Γ (omega w))
    (eq : Derives Γ (.equal N N'))
    (hN : Derives Γ (.ex (nameExecution w.castSucc z.castSucc b.castSucc c.castSucc d.castSucc
      t.castSucc N.castSucc Open.castSucc (Fin.last m))))
    (hN' : Derives Γ (.ex (nameExecution w.castSucc z.castSucc b.castSucc c.castSucc d.castSucc
      t.castSucc N'.castSucc Open'.castSucc (Fin.last m)))) :
    Derives Γ (.equal Open Open') := by
  let out : Formula m := .equal Open Open'
  refine eliminate_objects hZ 1 (fun r v => nameExecution (r w) (r z) (r b) (r c) (r d) (r t) (r N) (r Open) (v 0))
    hN out ?_
  intro l Δ r v hZ1 lift hL
  have hR : Derives Δ (.ex (nameExecution (r w).castSucc (r z).castSucc (r b).castSucc (r c).castSucc
      (r d).castSucc (r t).castSucc (r N').castSucc (r Open').castSucc (Fin.last l))) :=
    of_eq (by simp only [nameExecution, Formula.rename, SyntaxWeakenFreeSyntax.weakened_rename,
      SyntaxTopFormulaSyntax.instantiated_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]) (lift hN')
  refine eliminate_objects hZ1 1 (fun e u => nameExecution (e (r w)) (e (r z)) (e (r b)) (e (r c)) (e (r d))
    (e (r t)) (e (r N')) (e (r Open')) (u 0)) hR (out.rename r) ?_
  intro l' Ξ e u hZ2 move hR
  let g := e ∘ r
  let X := e (v 0)
  let Y := u 0
  have carry {F : Formula m} (hF : Derives Γ F) : Derives Ξ (F.rename g) :=
    of_eq (SourceAlgebra.rename_comp F r e) (move (lift hF))
  have hw2 := of_eq (omega_rename _ g) (carry hw)
  have eq2 : Derives Ξ (.equal (g N) (g N')) := carry eq
  have weakL := of_eq (SyntaxWeakenFreeSyntax.weakened_rename _ _ _ _ _ _ e) (move (.conjL hL))
  have instL := of_eq (SyntaxTopFormulaSyntax.instantiated_rename _ _ _ _ _ _ _ e) (move (.conjR hL))
  let P := SyntaxWeakenFreeSyntax.weakened (g w).castSucc (g c).castSucc (g b).castSucc (g d).castSucc
    (Fin.last l') X.castSucc
  have weakL' : Derives Ξ (SyntaxWeakenFreeSyntax.weakened (g w) (g c) (g b) (g d) (g N') X) :=
    of_eq (by simp only [P, Formula.instantiate, SyntaxWeakenFreeSyntax.weakened_rename,
      Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
      (.eqSubst P eq2 (of_eq (by simp only [P, Formula.instantiate, SyntaxWeakenFreeSyntax.weakened_rename,
        Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]; rfl) weakL))
  have weakEq := SyntaxWeakenFreeUnique.unique hZ2 (g w) (g c) (g b) (g d) (g N') X Y hw2 weakL' (.conjL hR)
  let Q := SyntaxTopFormulaSyntax.instantiated (g w).castSucc (g z).castSucc (g d).castSucc (g c).castSucc
    (g t).castSucc (Fin.last l') (g Open).castSucc
  have instL' : Derives Ξ (SyntaxTopFormulaSyntax.instantiated (g w) (g z) (g d) (g c) (g t) Y (g Open)) :=
    of_eq (by simp only [Q, Formula.instantiate, SyntaxTopFormulaSyntax.instantiated_rename,
      Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
      (.eqSubst Q weakEq (of_eq (by simp only [Q, Formula.instantiate, SyntaxTopFormulaSyntax.instantiated_rename,
        Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]; rfl) instL))
  exact SyntaxTopFormulaUnique.instantiate_unique hZ2 (g w) (g z) (g d) (g c) (g t) Y (g Open) (g Open')
    hw2 instL' (.conjR hR)



private theorem existential_child_source {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w a A B C f j N Nc : Fin m) (hw : Derives Γ (omega w))
    (h : Derives Γ (ForcingExistChildCode.compiled w a A B C f j N Nc)) :
    Derives Γ ((successor C B).conj (formulaCode w N A f)) := by
  refine eliminate_objects hZ 12 (fun r x =>
    ForcingExistChildCode.data (r w) (r a) (r A) (r B) (r C) (r f) (r j) (r N) (r Nc) x) h _ ?_
  intro l Δ r x hZ1 lift hData
  have tail := Derives.conjR (.conjR (.conjR (.conjR hData)))
  have shift := Derives.conjL (.conjR (.conjR (.conjR hData)))
  have hQuery := Derives.conjL (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR tail))))))
  have result : Derives Δ ((successor (r C) (r B)).conj (formulaCode (r w) (r N) (r A) (r f))) :=
    .conjI (.conjL shift) (SyntaxMixedFormulaJudgmentTyping.source_type hZ1 (r w) (x 10) (x 11)
    (r A) (r f) (r C) (r f) (r N) (r Nc) (of_eq (omega_rename _ r) (lift hw)) hQuery)
  exact of_eq (by simp only [Formula.rename, successor_rename, formulaCode_rename]) result

private def targetWitnessData {m}
    (w z A B f j oldScope b d c Prefix Selected Tail Body OldTail M O Name Inner Base q s : Fin m)
    (x : Fin 25 → Fin m) : Formula m :=
  let v : Fin 10 → Fin m := fun i => x ((i.castAdd 13).natAdd 2)
  let u : Fin 9 → Fin m := fun i => x (((i.castAdd 4).natAdd 10).natAdd 2)
  let fields : Fin 4 → Fin m := fun i => x (((i.natAdd 9).natAdd 10).natAdd 2)
  (SyntaxWeakenFreeSyntax.weakened w z oldScope b OldTail (x 0)).conj
    ((substituted w Prefix Selected A f z b Tail (x 0)).conj
      ((ForcingReflexiveImages.replacement w f z d Base j (x 1) (v 9)).conj
        ((StructuralListFieldSyntax.field w (v 8) z q).conj
          ((ForcingFreshParentOpening.quantifiedData false w z A f B b c d s Prefix Selected Tail Body (x 0) v u).conj
            (ForcingRawModalBody.nestedData 0 w (u 7) (v 9) B f z d M O Name Inner (u 8) fields)))))

private theorem targetWitnessData_rename {m l}
    (w z A B f j oldScope b d c Prefix Selected Tail Body OldTail M O Name Inner Base q s : Fin m)
    (x : Fin 25 → Fin m) (r : Fin m → Fin l) :
    (targetWitnessData w z A B f j oldScope b d c Prefix Selected Tail Body OldTail M O Name Inner Base q s x).rename r =
      targetWitnessData (r w) (r z) (r A) (r B) (r f) (r j) (r oldScope) (r b) (r d) (r c) (r Prefix) (r Selected)
        (r Tail) (r Body) (r OldTail) (r M) (r O) (r Name) (r Inner) (r Base) (r q) (r s) (r ∘ x) := by
  simp only [targetWitnessData, Formula.rename, SyntaxWeakenFreeSyntax.weakened_rename,
    substituted_rename, ForcingReflexiveImages.replacement_rename, StructuralListFieldSyntax.field_rename,
    ForcingFreshParentOpening.quantifiedData_rename, ForcingRawModalBody.nestedData_rename, Function.comp_apply]

private def targetWitnessResult {m}
    (w z A B f j oldScope b d c Prefix Selected Tail Body OldTail M O Name Inner Base q s MemberLeaf OrderLeaf NameLeaf : Fin m) : Formula m :=
  existsMany 25 ((targetWitnessData (old 25 w) (old 25 z) (old 25 A) (old 25 B) (old 25 f) (old 25 j)
    (old 25 oldScope) (old 25 b) (old 25 d) (old 25 c) (old 25 Prefix) (old 25 Selected) (old 25 Tail) (old 25 Body) (old 25 OldTail)
    (old 25 M) (old 25 O) (old 25 Name) (old 25 Inner) (old 25 Base) (old 25 q) (old 25 s) (slot 25)).conj
      ((Formula.equal (old 25 MemberLeaf) (slot 25 22)).conj
        ((Formula.equal (old 25 OrderLeaf) (slot 25 23)).conj
          (.equal (old 25 NameLeaf) (slot 25 24)))))

private theorem targetWitnessResult_rename {m l}
    (w z A B f j oldScope b d c Prefix Selected Tail Body OldTail M O Name Inner Base q s MemberLeaf OrderLeaf NameLeaf : Fin m) (r : Fin m → Fin l) :
    (targetWitnessResult w z A B f j oldScope b d c Prefix Selected Tail Body OldTail M O Name Inner Base q s MemberLeaf OrderLeaf NameLeaf).rename r =
      targetWitnessResult (r w) (r z) (r A) (r B) (r f) (r j) (r oldScope) (r b) (r d) (r c) (r Prefix) (r Selected)
        (r Tail) (r Body) (r OldTail) (r M) (r O) (r Name) (r Inner) (r Base) (r q) (r s)
        (r MemberLeaf) (r OrderLeaf) (r NameLeaf) := by
  simp only [targetWitnessResult, existsMany_rename, Formula.rename, targetWitnessData_rename, Function.comp_def, lift_old, lift_slot]

-- Open the original q-tail at the same s as the source witness. The old
-- selected free condition and the q prefix are weakened independently.
private theorem open_target_existential {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z a A B f j oldScope b d c R Base Prefix Name Selected OldTail Tail Body M O E I p q q' s MemberLeaf OrderLeaf NameLeaf : Fin m)
    (images : Fin 10 → Fin m)
    (hNext : Derives Γ (ForcingWeakenedImages.data w z f z b d R Base images))
    (hOldTail : Derives Γ (ForcingDensityInstantiation.weakenedTailResult w z A f oldScope b Prefix Selected Tail OldTail))
    (hName : Derives Γ (SyntaxMixedImageCodeSyntax.termList w a z b Name))
    (hPrefix : Derives Γ (StructuralListSyntax.consCode w q Name Prefix))
    (hOld : Derives Γ (ForcingReflexiveImages.replacement w f z b Base j p Selected))
    (hp : Derives Γ (SyntaxTermSyntax.term w z b p)) (hq : Derives Γ (SyntaxTermSyntax.term w z b q))
    (hRenameQ : Derives Γ (SyntaxRenameTermSyntax.renamed w (images 2) (images 3) z b z d q q'))
    (hSCode : Derives Γ (SyntaxVariableSyntax.code false w z s))
    (hSTerm : Derives Γ (SyntaxTermSyntax.term w z d s))
    (hz : Derives Γ (empty z))
    (hA : Derives Γ (successor A a)) (hB : Derives Γ (successor B A))
    (hc : Derives Γ (successor c z))
    (hBinder : Derives Γ (SyntaxLogicalSyntax.singleCode 10 w Body Tail))
    (hOuter : Derives Γ (binaryCode 0 w M I Body))
    (hInner : Derives Γ (binaryCode 0 w O E I))
    (matchFields : ∀ {l} {Δ : Context l} (r : Fin m → Fin l) (v : Fin 25 → Fin l),
      ZFContext.Evidence Δ → (∀ {F : Formula m}, Derives Γ F → Derives Δ (F.rename r)) →
      Derives Δ (targetWitnessData (r w) (r z) (r A) (r B) (r f) (r j) (r oldScope) (r b) (r d) (r c)
        (r Prefix) (r Selected) (r Tail) (r Body) (r OldTail) (r M) (r O) (r E) (r I) (r (images 9)) (r q') (r s) v) →
      Derives Δ ((Formula.equal (r MemberLeaf) (v 22)).conj ((Formula.equal (r OrderLeaf) (v 23)).conj (.equal (r NameLeaf) (v 24))))) :
    Derives Γ (targetWitnessResult w z A B f j oldScope b d c Prefix Selected Tail Body OldTail M O E I (images 9) q' s MemberLeaf OrderLeaf NameLeaf) := by
  let out := targetWitnessResult w z A B f j oldScope b d c Prefix Selected Tail Body OldTail M O E I (images 9) q' s MemberLeaf OrderLeaf NameLeaf
  have hMaps := Derives.conjL (.conjR hNext)
  have hw := Derives.conjL (.conjL hNext)
  have hScope := Derives.conjL (.conjR (.conjL hNext))
  have hIndex : Derives Γ (SyntaxIndexMapSyntax.maps w (images 2) (images 3) z b z d) :=
    .conjI (.conjR (.conjL (.conjR (.conjR hMaps)))) (.conjR (.conjR (.conjR (.conjR hMaps))))
  have hRename := SyntaxRenameTermExistence.for_term hZ w (images 2) (images 3) z b z d p hw hIndex hp
  refine eliminate_objects hZ 1 (fun r x => (Formula.mem (x 0) (r w)).conj
    (SyntaxRenameTermSyntax.renamed (r w) (r (images 2)) (r (images 3)) (r z) (r b) (r z) (r d) (r p) (x 0)))
    hRename out ?_
  intro l Δ r ps hZ1 lift hRenameP
  refine eliminate_objects hZ1 1 (fun t x => (SyntaxWeakenFreeSyntax.weakened (t (r w)) (t (r z))
    (t (r oldScope)) (t (r b)) (t (r OldTail)) (x 0)).conj
      (substituted (t (r w)) (t (r Prefix)) (t (r Selected)) (t (r A)) (t (r f))
        (t (r z)) (t (r b)) (t (r Tail)) (x 0)))
    (of_eq (ForcingDensityInstantiation.weakenedTailResult_rename _ _ _ _ _ _ _ _ _ _ r) (lift hOldTail))
    (out.rename r) ?_
  intro l1 Ξ t target hZ2 move hTarget
  let e := t ∘ r
  have carry {F : Formula m} (p0 : Derives Γ F) : Derives Ξ (F.rename e) :=
    of_eq (SourceAlgebra.rename_comp F r t) (move (lift p0))
  have hw2 := of_eq (omega_rename _ e) (carry hw)
  have hz2 := of_eq (empty_rename _ e) (carry hz)
  have hPrefixType := Derives.conjL (.conjR (SyntaxMixedFormulaOutput.input_of_substituted hZ2
    (e w) (e Prefix) (e Selected) (e A) (e f) (e z) (e b) (e Tail) (target 0) hw2 (.conjR hTarget)))
  have hName2 := of_eq (SyntaxMixedImageCodeSyntax.termList_rename _ _ _ _ _ e) (carry hName)
  have hA2 := of_eq (successor_rename _ _ e) (carry hA)
  have hzA := SyntaxIndexLiftOrder.zero_member hZ2 (e w) (e a) (e A) (e z) hw2 (.conjL hName2) hA2 hz2
  apply of_eq (SourceAlgebra.rename_comp out r t).symm
  refine ForcingWeakenedOverwrite.with_selected_existential_images hZ2 (e w) (e z) (e a) (e A) (e f) (e b) (e d)
    (e R) (e Base) (e Prefix) (e Name) (e Selected) (e j) (e p) (t (ps 0)) (e q) (e q') (e ∘ images)
    (of_eq (ForcingWeakenedImages.data_rename _ _ _ _ _ _ _ _ images e) (carry hNext))
    hPrefixType hName2 hz2 hzA (of_eq (SyntaxTermSyntax.term_rename _ _ _ _ e) (carry hq))
    (of_eq (StructuralListSyntax.consCode_rename _ _ _ _ e) (carry hPrefix))
    (of_eq (SyntaxRenameTermSyntax.renamed_rename _ _ _ _ _ _ _ _ _ e) (carry hRenameQ))
    (of_eq (SyntaxRenameTermSyntax.renamed_rename _ _ _ _ _ _ _ _ _ t) (move (.conjR hRenameP)))
    (of_eq (ForcingReflexiveImages.replacement_rename _ _ _ _ _ _ _ _ e) (carry hOld)) (out.rename e) ?_
  intro l2 Ω u v hZ3 extend hImages hReplace hField
  let g := u ∘ e
  have move3 {F : Formula m} (p0 : Derives Γ F) : Derives Ω (F.rename g) :=
    of_eq (SourceAlgebra.rename_comp F e u) (extend (carry p0))
  apply of_eq (SourceAlgebra.rename_comp out e u).symm
  refine ForcingDensityInstantiation.with_fresh_existential_body_at_images hZ3
    (g w) (g z) (g A) (g B) (g f) (g b) (g c) (g d) (g s) (g Prefix) (g Selected)
    (g Tail) (g Body) (u (target 0)) (g M) (g O) (g E) (g I) v
    (of_eq (omega_rename _ g) (move3 hw)) (of_eq (empty_rename _ g) (move3 hz))
    (of_eq (successor_rename _ _ g) (move3 hB)) (of_eq (successor_rename _ _ g) (move3 hc))
    (of_eq (successor_rename _ _ g) (move3 hScope))
    (of_eq (SyntaxVariableSyntax.code_rename _ _ _ _ g) (move3 hSCode))
    (of_eq (SyntaxTermSyntax.term_rename _ _ _ _ g) (move3 hSTerm))
    (of_eq (SyntaxLogicalSyntax.singleCode_rename _ _ _ _ g) (move3 hBinder))
    (of_eq (binaryCode_rename _ _ _ _ _ g) (move3 hOuter))
    (of_eq (binaryCode_rename _ _ _ _ _ g) (move3 hInner))
    (of_eq (substituted_rename _ _ _ _ _ _ _ _ _ u) (extend (.conjR hTarget))) hImages (out.rename g) ?_
  intro l3 Θ h opened fields hZ4 last hOpened hFields
  let k := h ∘ g
  have carry4 {F : Formula l1} (p0 : Derives Ξ F) : Derives Θ (F.rename (h ∘ u)) :=
    of_eq (SourceAlgebra.rename_comp F u h) (last (extend p0))
  apply of_eq (SourceAlgebra.rename_comp out g h).symm
  apply of_eq (targetWitnessResult_rename _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ k).symm
  let values : Fin 25 → Fin l3 :=
    Fin.addCases (motive := fun _ => Fin l3) (SyntaxAtomSyntax.two (h (u (target 0))) (h (u (t (ps 0)))))
      (Fin.addCases (motive := fun _ => Fin l3) (h ∘ v) (Fin.addCases (motive := fun _ => Fin l3) opened fields))
  have hPayload := Derives.conjI
    (of_eq (SyntaxWeakenFreeSyntax.weakened_rename _ _ _ _ _ _ (h ∘ u)) (carry4 (.conjL hTarget)))
    (.conjI (of_eq (substituted_rename _ _ _ _ _ _ _ _ _ (h ∘ u)) (carry4 (.conjR hTarget)))
      (.conjI (of_eq (ForcingReflexiveImages.replacement_rename _ _ _ _ _ _ _ _ h) (last hReplace))
        (.conjI (of_eq (StructuralListFieldSyntax.field_rename _ _ _ _ h) (last hField))
          (.conjI hOpened hFields))))
  have hData : Derives Θ (targetWitnessData (k w) (k z) (k A) (k B) (k f) (k j) (k oldScope) (k b)
      (k d) (k c) (k Prefix) (k Selected) (k Tail) (k Body) (k OldTail) (k M) (k O) (k E) (k I)
      (k (images 9)) (k q') (k s) values) := of_eq (by
    simp only [targetWitnessData, values, Fin.addCases_left, Fin.addCases_right, Function.comp_def]
    rfl) hPayload
  have lift4 {F : Formula m} (p0 : Derives Γ F) : Derives Θ (F.rename k) :=
    of_eq (SourceAlgebra.rename_comp F g h) (last (move3 p0))
  have hEq := matchFields k values hZ4 lift4 hData
  apply HornBinderRules.intro_many 25 _ values
  have hAssign : assign 25 values ∘ slot 25 = values := funext (assign_slot 25 values)
  exact of_eq (by simp only [Formula.rename, targetWitnessData_rename, assign_old, assign_slot, hAssign])
    (.conjI hData hEq)

/-- Replay the two successive witness queries in the original existential
density clause. The first witness is the reflexive condition of the second
query and both queries use the same inherited preorder and free table. -/
theorem with_existential_witnesses {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (Reln : Formula (k+2)) (Dom : Formula (k+1))
    (w z a A B C f j N Child b c d t L S D E G W H body Parent A1 A2 A3 K R Base Sel OldPre : Fin m)
    (images : Fin 10 → Fin m) (opened : Fin 9 → Fin m) (cv : Fin 8 → Fin m)
    (sv : Fin 7 → Fin m) (outputs : Fin 4 → Fin m) (raw : Fin 16 → Fin m)
    (hB : Derives Γ (successor B A))
    (hExist : Derives Γ (ForcingRawModalBody.existentialRecord Reln Dom w z a f A B C b c d t L S
      j Child N body Parent images opened cv sv))
    (hQueries : Derives Γ (ForcingRawModalBody.data w (opened 7) (images 9) A f z d
      (cv 2) (cv 3) (sv 4) (sv 5) (opened 8) outputs))
    (hCompiled : Derives Γ (ForcingDensityCode.compiled Reln w a A B f j N D))
    (hQuery : Derives Γ (substituted w L S a f z b D E))
    (hWeakG : Derives Γ (SyntaxWeakenFreeSyntax.weakened w z b d G W))
    (hProof : Derives Γ (implication test w z b G E))
    (hH : Derives Γ (formulaCode w H z d)) (hW : Derives Γ (formulaCode w W z d))
    (hToW : Derives Γ (implication test w z d H W))
    (pQ : Derives Γ (implication test w z d H (outputs 1)))
    (pOrder : Derives Γ (implication test w z d H (outputs 2)))
    (hA1 : Derives Γ (SyntaxNumeralSyntax.numeral 1 A1))
    (hA2 : Derives Γ (SyntaxNumeralSyntax.numeral 2 A2))
    (hA3 : Derives Γ (SyntaxNumeralSyntax.numeral 3 A3))
    (hf : Derives Γ (SyntaxNumeralSyntax.numeral (k+2) f))
    (hK : Derives Γ (SyntaxNumeralSyntax.numeral k K))
    (hj : Derives Γ (SyntaxNumeralSyntax.numeral (k+1) j))
    (hRaw : Derives Γ (ForcingPreorderCode.rawData Reln w z A1 A2 A3 f raw))
    (hOldPre : Derives Γ (substituted w R Base z f z d (raw 0) OldPre))
    (hSel : Derives Γ (SyntaxTermSyntax.term w z d Sel))
    (hBaseUpdate : Derives Γ (ForcingReflexiveImages.replacement w f z d Base j Sel (images 9)))
    (pOldPre : Derives Γ (implication test w z d H OldPre))
    (out : Formula m)
    (use : ∀ {l} {Δ : Context l} (ρ : Fin m → Fin l)
      (Br Fresh Rr Sr Nr Sq Name Extra Local OrderR TailR Bound Pfx TailS : Fin l)
      (ds : Fin 5 → Fin l) (v : Fin 10 → Fin l) (u : Fin 9 → Fin l)
      (Refl Pre U0 : Fin 2 → Fin l) (P : Fin 2 → Fin 3 → Fin l)
      (nextImages : Fin 10 → Fin l) (rows : Fin 48 → Fin l) (layout : Fin 6 → Fin l)
      (secondImages : Fin 10 → Fin l) (secondOpen : Fin 9 → Fin l) (secondFields : Fin 4 → Fin l),
      ZFContext.Evidence Δ → (∀ {F : Formula m}, Derives Γ F → Derives Δ (F.rename ρ)) →
      Derives Δ (ForcingFreshParentOpening.quantifiedData false (ρ w) (ρ z) (ρ A) (ρ f) (ρ B)
        (ρ d) (ρ c) Br (P 0 1) Bound (ρ (images 9)) (ds 2) (ds 1) TailR v u) →
      Derives Δ (SyntaxWeakenFreeSyntax.weakened (ρ w) (ρ z) (ρ d) Br (ρ H) Extra) →
      Derives Δ (FormulaCodeConstructSyntax.typedAt 2 5 (ρ w)
        (SyntaxAtomSyntax.two Extra (u 8)) Local (ρ z) Br) →
      Derives Δ (implication test (ρ w) (ρ z) (ρ d) (ρ H) TailR) →
      Derives Δ (ForcingRawModalBody.globalModalInput test Reln (ρ w) (ρ z) (ρ a) (ρ f) (ρ j)
        Br Fresh Rr Sr Name Sq Nr (ρ A1) (ρ A2) (ρ A3) (ρ K) Extra (ρ ∘ raw)
        nextImages (fun _ => ρ c) Refl Pre U0 P rows layout) →
      Derives Δ (.equal (ForcingMemberRows.leafFields (fun i => rows (i.castAdd 24)) 4) OrderR) →
      Derives Δ (implication test (ρ w) (ρ z) Br Local (layout 3)) →
      Derives Δ (StructuralListSyntax.consCode (ρ w) (P 0 1) Name Pfx) →
      Derives Δ (StructuralListSyntax.consCode (ρ w) (P 0 2) Name (v 8)) →
      Derives Δ (ForcingDensityInstantiation.weakenedTailResult (ρ w) (ρ z) (ρ A) (ρ f)
        (ρ d) Br (v 8) (v 9) (ρ (sv 4)) (ρ (outputs 3))) →
      Derives Δ (ForcingExistTailOpening.scopeResult (ρ w) Pfx Nr (ρ A) (ρ f) (ρ z) Br TailS
        Sr (ρ j) (P 0 1) (ForcingExistTailOpening.shellCodes (ρ (cv 4)) (ρ (cv 5))
          (ρ (cv 6)) (ρ (cv 7)) (ρ ∘ sv))) →
      Derives Δ (ForcingReflexiveImages.replacement (ρ w) (ρ f) (ρ z) Fresh (nextImages 9)
        (ρ j) (P 1 1) (secondImages 9)) →
      Derives Δ (StructuralListFieldSyntax.field (ρ w) (secondImages 8) (ρ z) (P 1 1)) →
      Derives Δ (ForcingFreshParentOpening.quantifiedData false (ρ w) (ρ z) (ρ A) (ρ f) (ρ B)
        Br (ρ c) Fresh (P 1 0) Pfx Nr (ρ (sv 4)) (ρ (sv 3)) TailS secondImages secondOpen) →
      Derives Δ (ForcingRawModalBody.nestedData 0 (ρ w) (secondOpen 7) (secondImages 9) (ρ B) (ρ f)
        (ρ z) Fresh (ρ (cv 4)) (ρ (cv 5)) (ρ (sv 1)) (ρ (sv 2)) (secondOpen 8) secondFields) →
      Derives Δ (let row : Fin 24 → Fin l := fun i => rows (i.addNat 24)
        (Formula.equal (ForcingMemberRows.leafFields row 0) (secondFields 1)).conj
          (Formula.equal (ForcingMemberRows.leafFields row 3) (secondFields 2))) →
      Derives Δ (let freshRow : Fin 24 → Fin l := fun i => rows (i.addNat 24)
        let background := ForcingMemberRows.backgroundFields freshRow 0
        let guards := ForcingMemberRows.leafFields freshRow
        (implication test (ρ w) (ρ z) Fresh background (guards 0)).conj
          (implication test (ρ w) (ρ z) Fresh background (guards 5))) →
      Derives Δ (implication test (ρ w) (ρ z) Br Local TailS) →
      Derives Δ (secondWitnessProofs (ρ w) (ρ z) Br Fresh Local (secondOpen 8) (secondFields 1)
        (secondFields 3) (ForcingMemberRows.leafFields (fun i => rows (i.addNat 24)) 5)) →
      Derives Δ (targetWitnessResult (ρ w) (ρ z) (ρ A) (ρ B) (ρ f) (ρ j) (ρ d) Br Fresh (ρ c)
        (v 8) (v 9) (ρ (sv 4)) (ρ (sv 3)) (ρ (outputs 3)) (ρ (cv 4)) (ρ (cv 5))
        (ρ (sv 1)) (ρ (sv 2)) (nextImages 9) (P 1 2) (P 1 0)
        (ForcingMemberRows.leafFields (fun i => rows (i.addNat 24)) 0)
        (ForcingMemberRows.leafFields (fun i => rows (i.addNat 24)) 5) (secondFields 3)) →
      Derives Δ (out.rename ρ)) : Derives Γ out := by
  refine ForcingDensityInstantiation.with_existential_density_witness hZ Reln Dom w z a A B C f j N Child
    b c d t L S D E G W H body Parent images opened cv sv outputs hB hExist hQueries hCompiled hQuery
    hWeakG hProof hH hW hToW pQ pOrder out ?_
  intro l Δ s Br r q Name Fr TailR Bound OrderHead OrderCode MemberQ Extra Local density ds v u x
    hZ1 move pTailR hOpen hq hName hQPrefix hQTail hFr hAtR hWeakExtra hMQ hMR hOrder hLocal pExtra pMQ pMR pRleQ pAtR
  let membersQ : Fin 4 → Fin l :=
    Fin.cases (s A) (Fin.cases (s (cv 1)) (SyntaxAtomSyntax.two (s (cv 2)) MemberQ))
  let membersR : Fin 4 → Fin l :=
    Fin.cases (s B) (Fin.cases (density 1) (SyntaxAtomSyntax.two (density 4) (x 1)))
  have hInput := Derives.conjL hOpen
  have hw := Derives.conjL hInput
  have hz := Derives.conjL (.conjR hInput)
  have hc := Derives.conjL (.conjR (.conjR (.conjR hInput)))
  have hr := Derives.conjL (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR hInput))))))
  have hOldPre1 := of_eq (substituted_rename _ _ _ _ _ _ _ _ _ s) (move hOldPre)
  have hBase := Derives.conjR (.conjR (SyntaxMixedFormulaOutput.input_of_substituted hZ1
    (s w) (s R) (s Base) (s z) (s f) (s z) (s d) (s (raw 0)) (s OldPre) hw hOldPre1))
  refine ForcingWeakenedOverwrite.with_base_of_update hZ1 (s w) (s A) (s f) (s z) (s d) Br
    Bound (s Base) (s j) (s Sel) (s (images 9)) v (.conjL (.conjR hOpen)) hBase
    (of_eq (SyntaxTermSyntax.term_rename _ _ _ _ s) (move hSel))
    (of_eq (ForcingReflexiveImages.replacement_rename _ _ _ _ _ _ _ _ s) (move hBaseUpdate)) (out.rename s) ?_
  intro l1 Δ1 e baseV sel hZ2 advance hBaseImages hSel1 hUpdate
  let e0 := e ∘ s
  have move1 {F : Formula m} (h : Derives Γ F) : Derives Δ1 (F.rename e0) :=
    of_eq (SourceAlgebra.rename_comp F s e) (advance (move h))
  have hw1 := of_eq (omega_rename _ e) (advance hw)
  have hz1 := of_eq (empty_rename _ e) (advance hz)
  have hr1 := of_eq (SyntaxTermSyntax.term_rename _ _ _ _ e) (advance hr)
  have hFree := Derives.conjR (SyntaxMixedImageCodePairs.term_lists (e0 w) (baseV 6) (baseV 7)
    (e0 A) (e0 f) (e0 z) (e Br) (baseV 8) (baseV 9) (.conjR (.conjR (.conjR (.conjR hBaseImages)))))
  have hRdirect := ForcingReflexiveImages.replacement_after_replacement hZ2 (e0 w) (e0 f) (e0 z)
    (e Br) (baseV 9) (e0 j) sel (e (v 9)) (e r) (e Fr) hw1 hFree hr1 hUpdate
    (of_eq (ForcingReflexiveImages.replacement_rename _ _ _ _ _ _ _ _ e) (advance hFr))
  apply of_eq (SourceAlgebra.rename_comp out s e).symm
  refine ForcingDensityInstantiation.with_raised_preorder hZ2 (e0 w) (e0 z) (e0 A) (e0 f) (e0 d) (e Br)
    (e Bound) (e0 Base) (e0 R) (e0 (raw 0)) (e0 OldPre) (e0 H) (e Extra) baseV hw1 hz1 hBaseImages
    (of_eq (substituted_rename _ _ _ _ _ _ _ _ _ e0) (move1 hOldPre))
    (of_eq (SyntaxWeakenFreeSyntax.weakened_rename _ _ _ _ _ _ e) (advance hWeakExtra))
    (of_eq (implication_rename test _ _ _ _ _ e0) (move1 pOldPre)) (out.rename e0) ?_
  intro l2 Δ2 g Rr PriorPre hZ3 extend hR hS hPre pPre
  let e1 := g ∘ e
  let e2 := g ∘ e0
  have move2 {F : Formula l} (h : Derives Δ F) : Derives Δ2 (F.rename e1) :=
    of_eq (SourceAlgebra.rename_comp F e g) (extend (advance h))
  have move3 {F : Formula m} (h : Derives Γ F) : Derives Δ2 (F.rename e2) :=
    of_eq (SourceAlgebra.rename_comp F e0 g) (extend (move1 h))
  have hw2 := of_eq (omega_rename _ g) (extend hw1)
  have hz2 := of_eq (empty_rename _ g) (extend hz1)
  have hq2 := of_eq (SyntaxTermSyntax.term_rename _ _ _ _ e1) (move2 hq)
  have hWeak2 := of_eq (SyntaxWeakenFreeSyntax.weakened_rename _ _ _ _ _ _ e1) (move2 hWeakExtra)
  have hExtra2 := SyntaxWeakenFreeOutput.target_type (e2 w) (e2 z) (e2 d) (e1 Br) (e2 H) (e1 Extra) hWeak2
  have hRange := Derives.conjR (.conjR (FormulaCodeProperties.guards _ _ _ _ hExtra2))
  have hQdirect := ForcingReflexiveImages.exists_replacement hZ3 (e2 w) (e2 f) (e2 z) (e1 Br) (g (baseV 9))
    (e2 j) (e1 q) hw2 hS hq2
  apply of_eq (SourceAlgebra.rename_comp out e0 g).symm
  refine eliminate_objects hZ3 1 (fun h y => ForcingReflexiveImages.replacement (h (e2 w)) (h (e2 f))
    (h (e2 z)) (h (e1 Br)) (h (g (baseV 9))) (h (e2 j)) (h (e1 q)) (y 0)) hQdirect (out.rename e2) ?_
  intro l3 Δ3 h y hZ4 step hQdirect3
  refine InternalProofTemplates.eliminate_successor hZ4 (h (e2 w)) (h (e1 Br))
    (of_eq (omega_rename _ h) (step hw2)) (step hRange) ((out.rename e2).rename h) ?_
  intro l4 Δ4 i Fresh hZ5 step2 hFresh
  let n := i ∘ h
  let σ := n ∘ e1
  let τ := n ∘ e2
  have carry4 {F : Formula l2} (p : Derives Δ2 F) : Derives Δ4 (F.rename n) :=
    of_eq (SourceAlgebra.rename_comp F h i) (step2 (step p))
  have carry5 {F : Formula l} (p : Derives Δ F) : Derives Δ4 (F.rename σ) :=
    of_eq (SourceAlgebra.rename_comp F e1 n) (carry4 (move2 p))
  have carry6 {F : Formula m} (p : Derives Γ F) : Derives Δ4 (F.rename τ) :=
    of_eq (SourceAlgebra.rename_comp F e2 n) (carry4 (move3 p))
  have hw4 := of_eq (omega_rename _ n) (carry4 hw2)
  have hz4 := of_eq (empty_rename _ n) (carry4 hz2)
  have hExtra4 := of_eq (formulaCode_rename _ _ _ _ n) (carry4 hExtra2)
  have hLocal4 := of_eq (formulaCode_rename _ _ _ _ σ) (carry5 (.conjR hLocal))
  have hPre4 := of_eq (substituted_rename _ _ _ _ _ _ _ _ _ n) (carry4 hPre)
  have hPreT := SyntaxMixedFormulaJudgment.target_type (τ w) (n Rr) (n (g (baseV 9))) (τ z) (τ f)
    (τ z) (σ Br) (τ (raw 0)) (n PriorPre) hPre4
  have pExtra4 := of_eq (implication_rename test _ _ _ _ _ σ) (carry5 pExtra)
  have pPre4 := ForcingRelationGuardProof.chain hZ5 test (τ w) (τ z) (σ Br) (σ Local) (σ Extra) (n PriorPre)
    hw4 hz4 hLocal4 hExtra4 hPreT pExtra4 (of_eq (implication_rename test _ _ _ _ _ n) (carry4 pPre))
  have hRdirect4 := of_eq (ForcingReflexiveImages.replacement_rename _ _ _ _ _ _ _ _ (n ∘ g))
    (of_eq (SourceAlgebra.rename_comp _ g n) (carry4 (extend hRdirect)))
  apply of_eq (SourceAlgebra.rename_comp _ h i).symm
  apply of_eq (SourceAlgebra.rename_comp out e2 n).symm
  have hSelection4 := of_eq (ForcingReflexiveImages.replacement_rename _ _ _ _ _ _ _ _ (n ∘ g))
    (of_eq (SourceAlgebra.rename_comp _ g n) (carry4 (extend hUpdate)))
  have hSelectionTerm4 := of_eq (SyntaxTermSyntax.term_rename _ _ _ _ (n ∘ g))
    (of_eq (SourceAlgebra.rename_comp _ g n) (carry4 (extend hSel1)))
  refine with_witness_preorder hZ5 Reln (τ w) (τ z) (τ a) (τ f) (τ j) (σ Br) Fresh
    (n Rr) (n (g (baseV 9))) (σ Name) (i (y 0)) (σ Fr) (τ A1) (τ A2) (τ A3) (τ K) (τ c)
    (σ Extra) (σ q) (σ r) (τ A) (σ OrderHead) (σ OrderCode) (σ (x 2)) (σ (v 9)) (n (g sel))
    (τ ∘ raw) (σ Local) (n PriorPre) (σ ∘ membersQ) (σ ∘ membersR) hw4 hz4
    (of_eq (SyntaxNumeralSyntax.numeral_rename _ _ τ) (carry6 hA1))
    (of_eq (SyntaxNumeralSyntax.numeral_rename _ _ τ) (carry6 hA2))
    (of_eq (SyntaxNumeralSyntax.numeral_rename _ _ τ) (carry6 hA3))
    (of_eq (SyntaxNumeralSyntax.numeral_rename _ _ τ) (carry6 hf))
    (of_eq (SyntaxNumeralSyntax.numeral_rename _ _ τ) (carry6 hK))
    (of_eq (SyntaxNumeralSyntax.numeral_rename _ _ τ) (carry6 hj))
    (of_eq (successor_rename _ _ σ) (carry5 hc)) hFresh
    (of_eq (SyntaxMixedImageCodeSyntax.termList_rename _ _ _ _ _ n) (carry4 hR))
    (of_eq (SyntaxMixedImageCodeSyntax.termList_rename _ _ _ _ _ n) (carry4 hS))
    (of_eq (SyntaxMixedImageCodeSyntax.termList_rename _ _ _ _ _ σ) (carry5 hName))
    (of_eq (ForcingReflexiveImages.replacement_rename _ _ _ _ _ _ _ _ i) (step2 hQdirect3)) hRdirect4
    hSelection4
    hExtra4 (of_eq (SyntaxTermSyntax.term_rename _ _ _ _ n) (carry4 hq2))
    (of_eq (SyntaxTermSyntax.term_rename _ _ _ _ σ) (carry5 hr))
    (of_eq (ForcingPreorderCode.rawData_rename Reln _ _ _ _ _ _ _ τ) (carry6 hRaw))
    (of_eq (ForcingGuardOpening.result_rename true (ForcingExistGuardsCode.reverseOrder Reln)
      _ _ _ _ _ _ _ _ _ _ σ) (carry5 hOrder)) hLocal4 hPre4
    (of_eq (ForcingGuardOpening.result_rename false Reln _ _ _ _ _ _ _ _ _ _ σ) (carry5 hMQ))
    (of_eq (ForcingGuardOpening.result_rename false Reln _ _ _ _ _ _ _ _ _ _ σ) (carry5 hMR)) pExtra4 pPre4
    (of_eq (implication_rename test _ _ _ _ _ σ) (carry5 pMQ))
    (of_eq (implication_rename test _ _ _ _ _ σ) (carry5 pMR))
    (of_eq (implication_rename test _ _ _ _ _ σ) (carry5 pRleQ)) (out.rename τ) ?_
  intro l5 Δ5 δ Refl Pre U0 P nextImages rows layout hZ6 finish er eq hRuntime hPre5 hOrderEq pGlobal
  let r1 := δ ∘ σ
  let r2 := δ ∘ τ
  have lift5 {F : Formula l} (p : Derives Δ F) : Derives Δ5 (F.rename r1) :=
    of_eq (SourceAlgebra.rename_comp F σ δ) (finish (carry5 p))
  have lift6 {F : Formula m} (p : Derives Γ F) : Derives Δ5 (F.rename r2) :=
    of_eq (SourceAlgebra.rename_comp F τ δ) (finish (carry6 p))
  let row : Fin 24 → Fin l5 := fun k => rows (k.castAdd 24)
  have hGlobal := Derives.conjL hRuntime
  have hRows := Derives.conjL (.conjL hGlobal)
  have hRow := Derives.conjL (.conjR hRows)
  have hLayout := Derives.conjR (.conjR (.conjR hGlobal))
  have hw5 := of_eq (omega_rename _ r1) (lift5 hw)
  have hz5 := of_eq (empty_rename _ r1) (lift5 hz)
  let freshRow : Fin 24 → Fin l5 := fun k => rows (k.addNat 24)
  have hFreshRow := Derives.conjL (.conjR (.conjR hRows))
  have hOrderProof := ForcingTransitiveGuardProof.at_background hZ6 test (r2 w) (r2 z) (δ Fresh)
    (r2 c) (Refl 1) (Pre 1) (ForcingMemberRows.backgroundFields freshRow) (ForcingMemberRows.leafFields freshRow)
    (ForcingMemberRows.nativeFields (U0 1) freshRow) (ForcingMemberRows.proofFields freshRow) (P 1)
    (ForcingMemberRows.tailFields freshRow) hw5 hz5 (.conjL (.conjL (.conjR hFreshRow)))
  have hTerm : Derives Δ5 (SyntaxTermSyntax.term (r2 w) (r2 z) (r1 Br) (P 0 1)) := by
    rw [er]
    exact of_eq (SyntaxTermSyntax.term_rename _ _ _ _ r1) (lift5 hr)
  have hUpdate5 : Derives Δ5 (ForcingReflexiveImages.replacement (r2 w) (r2 f) (r2 z) (r1 Br)
      (δ (n (g (baseV 9)))) (r2 j) (P 0 1) (r1 Fr)) := by
    rw [er]
    exact of_eq (ForcingReflexiveImages.replacement_rename _ _ _ _ _ _ _ _ δ) (finish hRdirect4)
  have hParent := Derives.conjL hExist
  have hA := Derives.conjL (.conjR (.conjR (.conjL hParent)))
  have hCompiler := Derives.conjL (.conjR hExist)
  have hShell := Derives.conjL (.conjR (.conjR hExist))
  apply of_eq (SourceAlgebra.rename_comp out τ δ).symm
  refine ForcingDensityGuards.with_existential_at_reflexive hZ6 Reln Dom
    (r2 w) (r2 z) (r2 a) (r2 A) (r2 B) (r2 C) (r2 f) (r1 Br) (r2 j) (r1 Name) (r1 Fr)
    (δ (n (g (baseV 9)))) (r2 K) (r1 Extra) (r2 A1) (r2 A2) (r2 A3) (r2 c) (δ (n Rr))
    (Refl 0) (Pre 0) (r2 Child) (r2 N) (r1 (x 3)) (r1 Local) (r2 ∘ raw)
    (ForcingMemberRows.backgroundFields row) (ForcingMemberRows.leafFields row) layout
    (ForcingMemberRows.nativeFields (U0 0) row) (ForcingMemberRows.proofFields row) (P 0)
    (ForcingMemberRows.tailFields row) (ForcingMemberRows.prefixFields row) (r2 ∘ cv) (r2 ∘ sv)
    hw5 hz5 (of_eq (successor_rename _ _ r2) (lift6 hA)) hTerm
    (of_eq (SyntaxNumeralSyntax.numeral_rename _ _ r2) (lift6 hK))
    (of_eq (SyntaxNumeralSyntax.numeral_rename _ _ r2) (lift6 hf))
    (of_eq (SyntaxNumeralSyntax.numeral_rename _ _ r2) (lift6 hj))
    (of_eq (SyntaxMixedImageCodeSyntax.termList_rename _ _ _ _ _ δ)
      (finish (of_eq (SyntaxMixedImageCodeSyntax.termList_rename _ _ _ _ _ n) (carry4 hS)))) hUpdate5
    (of_eq (SyntaxNumeralSyntax.numeral_rename _ _ r2) (lift6 hA1))
    (of_eq (SyntaxNumeralSyntax.numeral_rename _ _ r2) (lift6 hA2)) hRow hPre5
    (.conjL (.conjR (.conjR hGlobal))) hLayout
    (of_eq (ForcingExistCode.data_rename Reln Dom _ _ _ _ _ _ _ _ _ cv r2) (lift6 hCompiler))
    (of_eq (ForcingExistCode.shellData_rename _ _ _ _ _ _ _ _ _ _ _ _ _ sv r2) (lift6 hShell))
    (of_eq (substituted_rename _ _ _ _ _ _ _ _ _ r1) (lift5 hAtR))
    (of_eq (formulaCode_rename _ _ _ _ r1) (lift5 (.conjR hLocal))) pGlobal
    (of_eq (implication_rename test _ _ _ _ _ r1) (lift5 pAtR)) (out.rename r2) ?_
  intro l6 Δ6 η Pfx TailS hZ7 transport hPfx hTail hPrepared pTailS
  let sMap := η ∘ r2
  let fresh := η (δ Fresh)
  have lift7 {F : Formula m} (p : Derives Γ F) : Derives Δ6 (F.rename sMap) :=
    of_eq (SourceAlgebra.rename_comp F r2 η) (transport (lift6 p))
  have hFreshData := Derives.conjL (.conjR hGlobal)
  have hsCode := Derives.conjL (.conjR hFreshData)
  have hsTerm := Derives.conjL (.conjR (.conjR hFreshData))
  have hsScope := of_eq (successor_rename _ _ (η ∘ δ))
    (of_eq (SourceAlgebra.rename_comp _ δ η) (transport (finish hFresh)))
  apply of_eq (SourceAlgebra.rename_comp out r2 η).symm
  have hw7 := of_eq (omega_rename _ η) (transport hw5)
  have hz7 := of_eq (empty_rename _ η) (transport hz5)
  have hPfxType := Derives.conjL (.conjR (SyntaxMixedFormulaOutput.input_of_substituted hZ7
    (sMap w) Pfx (η (r1 Fr)) (sMap A) (sMap f) (sMap z) (η (r1 Br)) (sMap (sv 4)) TailS hw7 hTail))
  have hName7 := of_eq (SyntaxMixedImageCodeSyntax.termList_rename _ _ _ _ _ (η ∘ r1))
    (of_eq (SourceAlgebra.rename_comp _ r1 η) (transport (lift5 hName)))
  have hzA := SyntaxIndexLiftOrder.zero_member hZ7 (sMap w) (sMap a) (sMap A) (sMap z)
    hw7 (.conjL hName7) (of_eq (successor_rename _ _ sMap) (lift7 hA)) hz7
  have hNext := Derives.conjL (.conjR (.conjR (.conjL hFreshData)))
  have hRShift := Derives.conjL (.conjR (.conjR (.conjR hFreshData)))
  refine ForcingWeakenedOverwrite.with_selected_existential_images hZ7
    (sMap w) (sMap z) (sMap a) (sMap A) (sMap f) (η (r1 Br)) fresh
    (η (δ (n Rr))) (η (δ (n (g (baseV 9))))) Pfx (η (r1 Name)) (η (r1 Fr)) (sMap j)
    (η (P 0 1)) (η (P 1 1)) (η (P 0 1)) (η (P 1 1)) (η ∘ nextImages)
    (of_eq (ForcingWeakenedImages.data_rename _ _ _ _ _ _ _ _ nextImages η) (transport hNext))
    hPfxType hName7 hz7 hzA (of_eq (SyntaxTermSyntax.term_rename _ _ _ _ η) (transport hTerm)) hPfx
    (of_eq (SyntaxRenameTermSyntax.renamed_rename _ _ _ _ _ _ _ _ _ η) (transport hRShift))
    (of_eq (SyntaxRenameTermSyntax.renamed_rename _ _ _ _ _ _ _ _ _ η) (transport hRShift))
    (of_eq (ForcingReflexiveImages.replacement_rename _ _ _ _ _ _ _ _ η) (transport hUpdate5))
    (out.rename sMap) ?_
  intro l7 Δ7 toAligned aligned hZ8 align hAligned hSelectedR hRField
  let openMap := toAligned ∘ sMap
  have lift8 {F : Formula m} (p : Derives Γ F) : Derives Δ7 (F.rename openMap) :=
    of_eq (SourceAlgebra.rename_comp F sMap toAligned) (align (lift7 p))
  have hInnerShell := of_eq (ForcingExistCode.shellData_rename _ _ _ _ _ _ _ _ _ _ _ _ _ sv openMap) (lift8 hShell)
  have hBody := Derives.conjR (.conjR hInnerShell)
  apply of_eq (SourceAlgebra.rename_comp out sMap toAligned).symm
  refine ForcingDensityInstantiation.with_fresh_existential_body_at_images hZ8
    (openMap w) (openMap z) (openMap A) (openMap B) (openMap f) (toAligned (η (r1 Br))) (openMap c) (toAligned fresh) (toAligned (η (P 1 0)))
    (toAligned Pfx) (toAligned (η (r1 Fr))) (openMap (sv 4)) (openMap (sv 3)) (toAligned TailS) (openMap (cv 4)) (openMap (cv 5))
    (openMap (sv 1)) (openMap (sv 2)) aligned
    (of_eq (omega_rename _ toAligned) (align hw7)) (of_eq (empty_rename _ toAligned) (align hz7))
    (of_eq (successor_rename _ _ openMap) (lift8 hB))
    (of_eq (successor_rename _ _ (toAligned ∘ η ∘ r1))
      (of_eq (by simp only [SourceAlgebra.rename_comp]; rfl) (align (transport (lift5 hc)))))
    (of_eq (successor_rename _ _ toAligned) (align hsScope))
    (of_eq (SyntaxVariableSyntax.code_rename _ _ _ _ (toAligned ∘ η))
      (of_eq (SourceAlgebra.rename_comp _ η toAligned) (align (transport hsCode))))
    (of_eq (SyntaxTermSyntax.term_rename _ _ _ _ (toAligned ∘ η))
      (of_eq (SourceAlgebra.rename_comp _ η toAligned) (align (transport hsTerm))))
    (.conjL (.conjL (.conjR (.conjR hBody)))) (.conjL (.conjL (.conjR hBody))) (.conjL (.conjL hBody))
    (of_eq (substituted_rename _ _ _ _ _ _ _ _ _ toAligned) (align hTail)) hAligned (out.rename openMap) ?_
  intro l8 Δ8 ν secondOpen secondFields hZ9 last hSecondOpen hSecondFields
  let secondImages := ν ∘ aligned
  let secondLift := ν ∘ toAligned
  let secondMap := secondLift ∘ η
  let ρ := secondMap ∘ r2
  let ε := secondMap ∘ r1
  have carrySecond {F : Formula l6} (p : Derives Δ6 F) : Derives Δ8 (F.rename secondLift) :=
    of_eq (SourceAlgebra.rename_comp F toAligned ν) (last (align p))
  have carryRuntime {F : Formula l5} (p : Derives Δ5 F) : Derives Δ8 (F.rename secondMap) :=
    of_eq (SourceAlgebra.rename_comp F η secondLift) (carrySecond (transport p))
  have lift9 {F : Formula m} (p : Derives Γ F) : Derives Δ8 (F.rename ρ) :=
    of_eq (SourceAlgebra.rename_comp F r2 secondMap) (carryRuntime (lift6 p))
  have open1 {F : Formula l} (p : Derives Δ F) : Derives Δ8 (F.rename ε) :=
    of_eq (SourceAlgebra.rename_comp F r1 secondMap) (carryRuntime (lift5 p))
  have hOpen8 := of_eq (ForcingFreshParentOpening.quantifiedData_rename false _ _ _ _ _ _ _ _ _ _ _ _ _ _
    v u ε) (open1 hOpen)
  have er8 : (secondMap ∘ P 0) 1 = ε r := congrArg secondMap er
  rw [← er8] at hOpen8
  have hQPrefix9 := of_eq (StructuralListSyntax.consCode_rename _ _ _ _ ε) (open1 hQPrefix)
  have eq9 : (secondMap ∘ P 0) 2 = ε q := congrArg secondMap eq
  rw [← eq9] at hQPrefix9
  have hRuntime9 := of_eq (ForcingRawModalBody.globalModalInput_rename test Reln (r2 w) (r2 z) (r2 a) (r2 f) (r2 j)
    (r1 Br) (δ Fresh) (δ (n Rr)) (δ (n (g (baseV 9)))) (r1 Name) (δ (i (y 0))) (r1 Fr)
    (r2 A1) (r2 A2) (r2 A3) (r2 K) (r1 Extra) (r2 ∘ raw) nextImages (fun _ => r2 c) Refl Pre U0 P rows layout secondMap)
    (carryRuntime hRuntime)
  have hSelected9 := of_eq (ForcingReflexiveImages.replacement_rename _ _ _ _ _ _ _ _ ν) (last hSelectedR)
  have hRField9 := of_eq (StructuralListFieldSyntax.field_rename _ _ _ _ ν) (last hRField)
  have hNext9 := of_eq (ForcingWeakenedImages.data_rename _ _ _ _ _ _ _ _ nextImages secondMap) (carryRuntime hNext)
  have hLists := SyntaxMixedImageCodePairs.term_lists (ρ w) (secondMap (nextImages 6)) (secondMap (nextImages 7))
    (ρ z) (ρ f) (ρ z) (secondMap (δ Fresh)) (secondMap (nextImages 8)) (secondMap (nextImages 9))
    (.conjR (.conjR (.conjR (.conjR hNext9))))
  have hRows9 := Derives.conjL (.conjL (.conjL hRuntime9))
  have hGuards := second_witness_guards hZ9 Reln Dom 0 rfl (ρ w) (ρ z) (ρ a) (ρ A) (ρ B) (ρ C) (ρ f) (ρ j)
    (ρ Child) (ρ N) (ε Br) (ρ c) (secondMap (δ Fresh)) (secondLift Pfx) (ε Fr) (secondLift TailS)
    (ρ A1) (ρ A2) (ρ A3) (ρ K) (secondMap (nextImages 8)) (secondMap (nextImages 9))
    (secondMap (Refl 1)) (secondMap (Pre 1)) (secondMap (U0 1)) (secondMap (P 1 1)) (ρ ∘ raw) (secondMap ∘ P 1)
    (secondMap ∘ freshRow) (ρ ∘ cv) (ρ ∘ sv) secondImages secondOpen secondFields
    (open1 (.conjL hName)) (of_eq (successor_rename _ _ ρ) (lift9 hA))
    (of_eq (SyntaxNumeralSyntax.numeral_rename _ _ ρ) (lift9 hA1))
    (of_eq (SyntaxNumeralSyntax.numeral_rename _ _ ρ) (lift9 hA2))
    (of_eq (SyntaxNumeralSyntax.numeral_rename _ _ ρ) (lift9 hA3))
    (of_eq (SyntaxNumeralSyntax.numeral_rename _ _ ρ) (lift9 hf))
    (of_eq (SyntaxNumeralSyntax.numeral_rename _ _ ρ) (lift9 hK))
    (of_eq (SyntaxNumeralSyntax.numeral_rename _ _ ρ) (lift9 hj))
    (.conjL hLists) (.conjR hLists) (.conjL (.conjR (.conjR hRows9))) hSelected9 hRField9
    (of_eq (ForcingExistCode.data_rename Reln Dom _ _ _ _ _ _ _ _ _ cv ρ) (lift9 hCompiler))
    hSecondOpen hSecondFields
  let openedRow := secondMap ∘ freshRow
  let fresh := secondMap (δ Fresh)
  let H5 := ForcingMemberRows.leafFields openedRow 5
  let localProofsFormula := secondWitnessProofs (ρ w) (ρ z) (ε Br) fresh (ε Local)
    (secondOpen 8) (secondFields 1) (secondFields 3) H5
  have hOrder9 : Derives Δ8 (implication test (ρ w) (ρ z) fresh
      (ForcingMemberRows.backgroundFields openedRow 0) H5) :=
    of_eq (by simp only [implication_rename]; rfl) (carryRuntime (.conjR hOrderProof))
  have pGlobal9 := of_eq (implication_rename test _ _ _ _ _ secondMap) (carryRuntime pGlobal)
  have hLocal9 := of_eq (formulaCode_rename _ _ _ _ ε) (open1 (.conjR hLocal))
  have hSecondBody := Derives.conjL (.conjR (.conjR (.conjR (.conjR
    (.conjR (.conjR (.conjR (.conjR hSecondOpen))))))))
  have hSecondOuter := Derives.conjL hSecondFields
  have hSecondInner := Derives.conjR hSecondFields
  have queryType (X Y : Fin l8) (h : Derives Δ8 (substituted (ρ w) (secondOpen 7)
      (secondImages 9) (ρ B) (ρ f) (ρ z) fresh X Y)) : Derives Δ8 (formulaCode (ρ w) Y (ρ z) fresh) :=
    SyntaxMixedFormulaJudgment.target_type (ρ w) (secondOpen 7) (secondImages 9) (ρ B) (ρ f) (ρ z) fresh X Y h
  have hProofs : Derives Δ8 localProofsFormula := by
    refine with_second_witness_transitivity hZ9 Reln (ρ w) (ρ z) (ρ A1) (ρ A2) (ρ A3) (ρ f) (ε Br) fresh
      (secondMap (δ (n Rr))) (secondMap (δ (n (g (baseV 9))))) (ρ K) (ε Extra) (ε Local)
      (secondOpen 8) (secondFields 1) (secondFields 0) (secondFields 2) (secondFields 3)
      (ρ ∘ raw) (secondMap ∘ nextImages) (fun _ => ρ c) (secondMap ∘ Refl) (secondMap ∘ Pre) (secondMap ∘ U0)
      (fun t => secondMap ∘ P t) (secondMap ∘ rows) (secondMap ∘ layout) (.conjL hRuntime9)
      hLocal9 (queryType (ρ (sv 3)) (secondOpen 8) hSecondBody)
      (queryType (ρ (cv 4)) (secondFields 1) (.conjL (.conjR hSecondOuter)))
      (queryType (ρ (sv 2)) (secondFields 0) (.conjR (.conjR hSecondOuter)))
      (queryType (ρ (cv 5)) (secondFields 2) (.conjL (.conjR hSecondInner)))
      (queryType (ρ (sv 1)) (secondFields 3) (.conjR (.conjR hSecondInner)))
      (.conjL hSecondOuter) (.conjL hSecondInner) hGuards hOrder9 pGlobal9 localProofsFormula ?_
    intro l9 Δ9 r Weak LocalS hZ10 move hWeak hLocalS pMember pName pTrans
    apply of_eq (secondWitnessProofs_rename _ _ _ _ _ _ _ _ _ r).symm
    apply HornBinderRules.intro_many 2 _ (SyntaxAtomSyntax.two Weak LocalS)
    exact of_eq (by simp only [secondWitnessData_rename, assign_old, assign_slot]; rfl)
      (.conjI hWeak (.conjI hLocalS (.conjI pMember (.conjI pName pTrans))))
  have hQTail9 := of_eq (ForcingDensityInstantiation.weakenedTailResult_rename _ _ _ _ _ _ _ _ _ _ ε) (open1 hQTail)
  have hQTerm9 : Derives Δ8 (SyntaxTermSyntax.term (ρ w) (ρ z) (ε Br) ((secondMap ∘ P 0) 2)) := by
    rw [eq9]
    exact of_eq (SyntaxTermSyntax.term_rename _ _ _ _ ε) (open1 hq)
  have hQShift := Derives.conjL (.conjR (.conjR (.conjR (.conjR hFreshData))))
  have hSelected9Q := of_eq (ForcingReflexiveImages.replacement_rename _ _ _ _ _ _ _ _ (secondMap ∘ δ))
    (of_eq (SourceAlgebra.rename_comp _ δ secondMap) (carryRuntime (finish hSelection4)))
  have hSelectedTerm9 := of_eq (SyntaxTermSyntax.term_rename _ _ _ _ (secondMap ∘ δ))
    (of_eq (SourceAlgebra.rename_comp _ δ secondMap) (carryRuntime (finish hSelectionTerm4)))
  have hShell9 := of_eq (ForcingExistCode.shellData_rename _ _ _ _ _ _ _ _ _ _ _ _ _ sv ρ) (lift9 hShell)
  have hBody9 := Derives.conjR (.conjR hShell9)
  have hTargetQ := open_target_existential hZ9 (ρ w) (ρ z) (ρ a) (ρ A) (ρ B) (ρ f) (ρ j) (ρ d) (ε Br)
    fresh (ρ c) (secondMap (δ (n Rr))) (secondMap (δ (n (g (baseV 9)))))
    (ε (v 8)) (ε Name) (ε (v 9)) (ρ (outputs 3)) (ρ (sv 4)) (ρ (sv 3)) (ρ (cv 4)) (ρ (cv 5))
    (ρ (sv 1)) (ρ (sv 2)) (secondMap (δ (n (g sel)))) (secondMap (P 0 2)) (secondMap (P 1 2))
    (secondMap (P 1 0)) (ForcingMemberRows.leafFields openedRow 0) H5 (secondFields 3)
    (secondMap ∘ nextImages) hNext9 hQTail9
    (of_eq (SyntaxMixedImageCodeSyntax.termList_rename _ _ _ _ _ ε) (open1 hName)) hQPrefix9
    hSelected9Q hSelectedTerm9 hQTerm9
    (of_eq (SyntaxRenameTermSyntax.renamed_rename _ _ _ _ _ _ _ _ _ secondMap) (carryRuntime hQShift))
    (of_eq (SyntaxVariableSyntax.code_rename _ _ _ _ secondMap) (carryRuntime hsCode))
    (of_eq (SyntaxTermSyntax.term_rename _ _ _ _ secondMap) (carryRuntime hsTerm))
    (of_eq (empty_rename _ secondMap) (carryRuntime hz5))
    (of_eq (successor_rename _ _ ρ) (lift9 hA)) (of_eq (successor_rename _ _ ρ) (lift9 hB))
    (of_eq (successor_rename _ _ ε) (open1 hc))
    (.conjL (.conjL (.conjR (.conjR hBody9)))) (.conjL (.conjL (.conjR hBody9))) (.conjL (.conjL hBody9)) (by
      intro lQ ΔQ qmap data hZQ qmove hData
      let e := qmap ∘ ρ
      let eRow := qmap ∘ secondMap
      let qv : Fin 10 → Fin lQ := fun i => data ((i.castAdd 13).natAdd 2)
      let qo : Fin 9 → Fin lQ := fun i => data (((i.castAdd 4).natAdd 10).natAdd 2)
      let qf : Fin 4 → Fin lQ := fun i => data (((i.natAdd 9).natAdd 10).natAdd 2)
      have liftQ {F : Formula m} (p : Derives Γ F) : Derives ΔQ (F.rename e) :=
        of_eq (SourceAlgebra.rename_comp F ρ qmap) (qmove (lift9 p))
      have hRowQ := of_eq (ForcingMemberRows.rowData_rename test Reln _ _ _ _ _ _ _ _ _ _ _ _ _
        (ρ ∘ raw) (secondMap ∘ P 1) openedRow qmap)
        (qmove (.conjL (.conjR (.conjR hRows9))))
      have hGuardsQ := second_witness_guards hZQ Reln Dom 2 rfl (e w) (e z) (e a) (e A) (e B) (e C) (e f) (e j)
        (e Child) (e N) (qmap (ε Br)) (e c) (qmap fresh) (qmap (ε (v 8))) (qmap (ε (v 9))) (data 0)
        (e A1) (e A2) (e A3) (e K) (eRow (nextImages 8)) (eRow (nextImages 9))
        (eRow (Refl 1)) (eRow (Pre 1)) (eRow (U0 1)) (data 1) (e ∘ raw) (eRow ∘ P 1)
        (qmap ∘ openedRow) (e ∘ cv) (e ∘ sv) qv qo qf (qmove (open1 (.conjL hName)))
        (of_eq (successor_rename _ _ e) (liftQ hA))
        (of_eq (SyntaxNumeralSyntax.numeral_rename _ _ e) (liftQ hA1))
        (of_eq (SyntaxNumeralSyntax.numeral_rename _ _ e) (liftQ hA2))
        (of_eq (SyntaxNumeralSyntax.numeral_rename _ _ e) (liftQ hA3))
        (of_eq (SyntaxNumeralSyntax.numeral_rename _ _ e) (liftQ hf))
        (of_eq (SyntaxNumeralSyntax.numeral_rename _ _ e) (liftQ hK))
        (of_eq (SyntaxNumeralSyntax.numeral_rename _ _ e) (liftQ hj))
        (of_eq (SyntaxMixedImageCodeSyntax.termList_rename _ _ _ _ _ qmap) (qmove (.conjL hLists)))
        (of_eq (SyntaxMixedImageCodeSyntax.termList_rename _ _ _ _ _ qmap) (qmove (.conjR hLists)))
        hRowQ (.conjL (.conjR (.conjR hData))) (.conjL (.conjR (.conjR (.conjR hData))))
        (of_eq (ForcingExistCode.data_rename Reln Dom _ _ _ _ _ _ _ _ _ cv e) (liftQ hCompiler))
        (.conjL (.conjR (.conjR (.conjR (.conjR hData))))) (.conjR (.conjR (.conjR (.conjR (.conjR hData)))))
      refine .conjI (.conjL hGuardsQ) (.conjI (.conjR hGuardsQ) ?_)
      let base := secondMap (δ (n (g (baseV 9))))
      let sourcePrefix := secondLift Pfx
      let sourceTail := secondLift TailS
      let sourceBound := ε Fr
      let targetPrefix := ε (v 8)
      let targetBound := ε (v 9)
      let br := ε Br
      let rr := secondMap (P 0 1)
      let qq := secondMap (P 0 2)
      let selected := secondMap (δ (n (g sel)))
      let codes := ForcingExistTailOpening.shellCodes (e (cv 4)) (e (cv 5)) (e (cv 6)) (e (cv 7)) (e ∘ sv)
      have hwQ : Derives ΔQ (omega (e w)) :=
        of_eq (omega_rename _ qmap) (qmove (.conjL (.conjL hSecondOpen)))
      have hzQ : Derives ΔQ (empty (e z)) :=
        of_eq (empty_rename _ qmap) (qmove (.conjL (.conjR (.conjL hSecondOpen))))
      have hShellQ := of_eq (ForcingExistCode.shellData_rename _ _ _ _ _ _ _ _ _ _ _ _ _ sv e) (liftQ hShell)
      have hTargetOld := ForcingExistTailOpening.prepare_shell hZQ (e w) (e a) (e A) (e B) (e C) (e f)
        (e (cv 2)) (e (cv 3)) (e (cv 4)) (e (cv 5)) (e (cv 6)) (e (cv 7)) (e N)
        (qmap targetPrefix) (qmap targetBound) (e z) (qmap br) (data 0) (qmap base) (e j) (qmap selected)
        (e ∘ sv) hwQ hzQ (of_eq (ForcingReflexiveImages.replacement_rename _ _ _ _ _ _ _ _ qmap) (qmove hSelected9Q))
        hShellQ (.conjL (.conjR hData))
      have hSourceOld := of_eq (ForcingExistTailOpening.scopeResult_rename _ _ _ _ _ _ _ _ _ _ _
        (ForcingExistTailOpening.shellCodes (sMap (cv 4)) (sMap (cv 5)) (sMap (cv 6)) (sMap (cv 7)) (sMap ∘ sv))
        (qmap ∘ secondLift))
        (of_eq (SourceAlgebra.rename_comp _ secondLift qmap) (qmove (carrySecond hPrepared)))
      let outQ := Formula.equal (qmap (secondFields 3)) (qf 3)
      refine eliminate_objects hZQ 16 (fun α a =>
        ForcingExistTailOpening.scopeData (α (e w)) (α (qmap sourcePrefix)) (α (qmap sourceBound))
          (α (e A)) (α (e f)) (α (e z)) (α (qmap br)) (α (qmap sourceTail)) (α (qmap base))
          (α (e j)) (α (qmap rr)) (α ∘ codes) a) hSourceOld outQ ?_
      intro lR ΔR α ar hZR pushR hSource
      have hTargetR := of_eq (ForcingExistTailOpening.scopeResult_rename _ _ _ _ _ _ _ _ _ _ _ codes α) (pushR hTargetOld)
      refine eliminate_objects hZR 16 (fun β b =>
        ForcingExistTailOpening.scopeData (β (α (e w))) (β (α (qmap targetPrefix))) (β (α (qmap targetBound)))
          (β (α (e A))) (β (α (e f))) (β (α (e z))) (β (α (qmap br))) (β (α (data 0))) (β (α (qmap base)))
          (β (α (e j))) (β (α (qmap selected))) (β ∘ α ∘ codes) b) hTargetR (outQ.rename α) ?_
      intro lB ΔB β bt hZB pushB hTarget
      let moveB := β ∘ α
      let g := moveB ∘ e
      let up := moveB ∘ qmap
      have carry {F : Formula lQ} (hp : Derives ΔQ F) : Derives ΔB (F.rename moveB) :=
        of_eq (SourceAlgebra.rename_comp F α β) (pushB (pushR hp))
      have main {F : Formula m} (hp : Derives Γ F) : Derives ΔB (F.rename g) :=
        of_eq (SourceAlgebra.rename_comp F e moveB) (carry (liftQ hp))
      have fromSecond {F : Formula l8} (hp : Derives Δ8 F) : Derives ΔB (F.rename up) :=
        of_eq (SourceAlgebra.rename_comp F qmap moveB) (carry (qmove hp))
      have hwB := of_eq (omega_rename _ moveB) (carry hwQ)
      have hzB := of_eq (empty_rename _ moveB) (carry hzQ)
      have hComp := of_eq (ForcingExistCode.data_rename Reln Dom _ _ _ _ _ _ _ _ _ cv g) (main hCompiler)
      have hHead := Derives.conjL hComp
      have eZero := OmegaUniversal.empty_unique (g (cv 0)) (g z) (ZFContext.arithmetic hZB).base.extensionality (.conjL hHead) hzB
      have hX := SyntaxVariableImagePoint.code_subst_index true (g w) (g (cv 0)) (g (cv 1)) (g z) eZero (.conjL (.conjR hHead))
      have hRight := Derives.conjR (.conjR (.conjR (.conjR (.conjR hComp))))
      have hChild := Derives.conjL (.conjR hRight)
      have hChildSource := existential_child_source hZB (g w) (g a) (g A) (g B) (g C) (g f) (g j)
        (g Child) (g (cv 7)) hwB hChild
      have hSourceB := of_eq (ForcingExistTailOpening.scopeData_rename _ _ _ _ _ _ _ _ _ _ _ (α ∘ codes) ar β) (pushB hSource)
      have hRterm := of_eq (SyntaxTermSyntax.term_rename _ _ _ _ (up ∘ secondMap))
        (of_eq (SourceAlgebra.rename_comp _ secondMap up) (fromSecond (carryRuntime hTerm)))
      have hQterm := of_eq (SyntaxTermSyntax.term_rename _ _ _ _ up) (fromSecond hQTerm9)
      have hRp := of_eq (StructuralListSyntax.consCode_rename _ _ _ _ (up ∘ secondLift))
        (of_eq (SourceAlgebra.rename_comp _ secondLift up) (fromSecond (carrySecond hPfx)))
      have hQp := of_eq (StructuralListSyntax.consCode_rename _ _ _ _ up) (fromSecond hQPrefix9)
      have hNameB := of_eq (SyntaxMixedImageCodeSyntax.termList_rename _ _ _ _ _ (up ∘ ε))
        (of_eq (SourceAlgebra.rename_comp _ ε up) (fromSecond (open1 hName)))
      have hOldEq := ForcingExistTailComparison.name_from_opened_tails hZB Dom (g w) (g z) (g a) (g A) (g B) (g C)
        (g f) (up br) (up (ε Name)) (up sourcePrefix) (up rr) (up targetPrefix) (up qq) (up base)
        (g K) (g j) (up rr) (up selected) (g (cv 1)) (g Child)
        (up sourceBound) (up sourceTail) (up targetBound) (moveB (data 0))
        (moveB ∘ codes) (β ∘ ar) bt hwB hzB
        (of_eq (successor_rename _ _ g) (main hA)) (of_eq (successor_rename _ _ g) (main hB))
        (.conjL hChildSource) hNameB hRterm hQterm hRp hQp (.conjR hChildSource) hSourceB hTarget
        (of_eq (SyntaxNumeralSyntax.numeral_rename _ _ g) (main hK))
        (of_eq (SyntaxNumeralSyntax.numeral_rename _ _ g) (main hj))
        (of_eq (SyntaxNumeralSyntax.numeral_rename _ _ g) (main hf))
        hX (.conjL hRight) hChild
      have hShellB := of_eq (ForcingExistCode.shellData_rename _ _ _ _ _ _ _ _ _ _ _ _ _ sv g) (main hShell)
      have hBodyB := Derives.conjR (.conjR hShellB)
      have outer := Derives.conjL (.conjL (.conjR hBodyB))
      have inner := Derives.conjL (.conjL hBodyB)
      have hSourceExec := name_through_fresh_opening hZB (g w) (g z) (g A) (g B) (g f) (up br) (g c) (up fresh)
        (up (secondMap (P 1 0))) (up sourcePrefix) (up sourceBound) (g (sv 4)) (g (sv 3)) (up sourceTail)
        (g (cv 4)) (g (cv 5)) (g (sv 1)) (g (sv 2)) (up base) (g j) (up rr)
        (moveB ∘ codes) (β ∘ ar) (up ∘ secondImages) (up ∘ secondOpen) (up ∘ secondFields) hSourceB
        (of_eq (ForcingFreshParentOpening.quantifiedData_rename false _ _ _ _ _ _ _ _ _ _ _ _ _ _ secondImages secondOpen up)
          (fromSecond hSecondOpen))
        (of_eq (ForcingRawModalBody.nestedData_rename _ _ _ _ _ _ _ _ _ _ _ _ _ secondFields up) (fromSecond hSecondFields))
        outer inner
      have hTargetData := Derives.conjR (.conjR (.conjR (.conjR hData)))
      have hTargetExec := name_through_fresh_opening hZB (g w) (g z) (g A) (g B) (g f) (up br) (g c) (up fresh)
        (up (secondMap (P 1 0))) (up targetPrefix) (up targetBound) (g (sv 4)) (g (sv 3)) (moveB (data 0))
        (g (cv 4)) (g (cv 5)) (g (sv 1)) (g (sv 2)) (up base) (g j) (up selected)
        (moveB ∘ codes) bt (moveB ∘ qv) (moveB ∘ qo) (moveB ∘ qf) hTarget
        (of_eq (ForcingFreshParentOpening.quantifiedData_rename false _ _ _ _ _ _ _ _ _ _ _ _ _ _ qv qo moveB)
          (carry (.conjL hTargetData)))
        (of_eq (ForcingRawModalBody.nestedData_rename _ _ _ _ _ _ _ _ _ _ _ _ _ qf moveB) (carry (.conjR hTargetData)))
        outer inner
      exact equal_fresh_name_codes hZB (g w) (g z) (up br) (g c) (up fresh) (up (secondMap (P 1 0)))
        (β (ar 8)) (bt 8) (up (secondFields 3)) (moveB (qf 3)) hwB hOldEq hSourceExec hTargetExec)
  apply of_eq (SourceAlgebra.rename_comp out openMap ν).symm
  exact use ρ (ε Br) (secondMap (δ Fresh)) (secondMap (δ (n Rr))) (secondMap (δ (n (g (baseV 9))))) (ε Fr) (secondMap (δ (i (y 0))))
    (ε Name) (ε Extra) (ε Local) (ε (x 2)) (ε TailR) (ε Bound) (secondLift Pfx) (secondLift TailS)
    (ε ∘ ds) (ε ∘ v) (ε ∘ u) (secondMap ∘ Refl) (secondMap ∘ Pre) (secondMap ∘ U0) (fun t => secondMap ∘ P t)
    (secondMap ∘ nextImages) (secondMap ∘ rows) (secondMap ∘ layout) secondImages secondOpen secondFields hZ9 lift9 hOpen8
    (of_eq (SyntaxWeakenFreeSyntax.weakened_rename _ _ _ _ _ _ ε) (open1 hWeakExtra))
    (of_eq (by simp only [FormulaCodeConstructSyntax.typedAt_rename, SyntaxAtomSyntax.two_map]; rfl)
      (open1 hLocal))
    (of_eq (implication_rename test _ _ _ _ _ ε) (open1 pTailR))
    hRuntime9
    (of_eq (by rfl) (carryRuntime hOrderEq))
    pGlobal9
    (of_eq (StructuralListSyntax.consCode_rename _ _ _ _ secondLift) (carrySecond hPfx))
    hQPrefix9 hQTail9
    (of_eq (ForcingExistTailOpening.scopeResult_rename _ _ _ _ _ _ _ _ _ _ _
      (ForcingExistTailOpening.shellCodes (sMap (cv 4)) (sMap (cv 5)) (sMap (cv 6)) (sMap (cv 7)) (sMap ∘ sv)) secondLift)
      (carrySecond hPrepared))
    hSelected9 hRField9 hSecondOpen hSecondFields hGuards
    (of_eq (by simp only [Formula.rename, implication_rename]; rfl) (carryRuntime hOrderProof))
    (of_eq (implication_rename test _ _ _ _ _ secondLift) (carrySecond pTailS)) hProofs hTargetQ


-- Eliminate the actual old existential once its opened body proves the
-- actual weakening of the result.
private theorem discharge_opened_witness {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z a f alpha b A B t R S n x Parent G Extra Local Result Raised : Fin m)
    (v : Fin 10 → Fin m) (u : Fin 9 → Fin m)
    (h : Derives Γ (ForcingFreshParentOpening.quantifiedData false w z a f alpha b A B t R S n x Parent v u))
    (hG : Derives Γ (formulaCode w G z b))
    (hExtra : Derives Γ (SyntaxWeakenFreeSyntax.weakened w z b B G Extra))
    (hLocal : Derives Γ (binaryCode 0 w Extra (u 8) Local))
    (hRaised : Derives Γ (SyntaxWeakenFreeSyntax.weakened w z b B Result Raised))
    (pParent : Derives Γ (implication test w z b G Parent))
    (pResult : Derives Γ (implication test w z B Local Raised)) :
    Derives Γ (implication test w z b G Result) := by
  have hi := Derives.conjL h
  have hw := Derives.conjL hi
  have hz := Derives.conjL (.conjR hi)
  have hA := Derives.conjL (.conjR (.conjR (.conjR hi)))
  have hQ := Derives.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR h))))))))
  have ha := Derives.conjR (.conjR hQ)
  have habs := ForcingFreshBackground.derive hZ w z b A B Result Raised
    (.conjI hw (.conjI hz (.conjI hA hRaised)))
  exact ForcingDensityGuards.witness_discharge hZ w z b A B G Extra (u 8) (u 4) Parent Local Result Raised hw hz hG
    hExtra ha (.conjL hQ) hLocal (SyntaxWeakenFreeOutput.source_type hZ w z b B Result Raised hw hRaised)
    (SyntaxTopFormulaTyping.abstract_target_type w z b A B Raised Result habs)
    (SyntaxWeakenFreeOutput.target_type w z b B Result Raised hRaised) habs pParent pResult

-- Rebuild the literal pair of target conjunctions and introduce the
-- existential with the same condition as the actual source witness.
private theorem introduce_target_witness {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z A B f br c Fresh s Prefix Selected Tail Body Parent M O Name Inner LocalS : Fin m)
    (v : Fin 10 → Fin m) (u : Fin 9 → Fin m) (fields : Fin 4 → Fin m)
    (hOpen : Derives Γ (ForcingFreshParentOpening.quantifiedData false w z A f B br c Fresh s Prefix Selected Tail Body Parent v u))
    (hFields : Derives Γ (ForcingRawModalBody.nestedData 0 w (u 7) (v 9) B f z Fresh M O Name Inner (u 8) fields))
    (hExists : Derives Γ (SyntaxLogicalSyntax.singleCode 10 w (u 5) (u 6)))
    (hLocalS : Derives Γ (formulaCode w LocalS z Fresh))
    (pMember : Derives Γ (implication test w z Fresh LocalS (fields 1)))
    (pOrder : Derives Γ (implication test w z Fresh LocalS (fields 2)))
    (pName : Derives Γ (implication test w z Fresh LocalS (fields 3))) :
    Derives Γ (implication test w z Fresh LocalS (u 6)) := by
  have hi := Derives.conjL hOpen
  have hw := Derives.conjL hi
  have hz := Derives.conjL (.conjR hi)
  have outer := Derives.conjL hFields
  have inner := Derives.conjR hFields
  have typed (Raw Output : Fin m) (p : Derives Γ (substituted w (u 7) (v 9) B f z Fresh Raw Output)) :
      Derives Γ (formulaCode w Output z Fresh) :=
    SyntaxMixedFormulaJudgment.target_type w (u 7) (v 9) B f z Fresh Raw Output p
  have pRest := ForcingProofContext.join hZ test w z Fresh LocalS (fields 2) (fields 3) (fields 0) hw hz hLocalS
    (typed O (fields 2) (.conjL (.conjR inner))) (typed Name (fields 3) (.conjR (.conjR inner))) (.conjL inner) pOrder pName
  have pBody := ForcingProofContext.join hZ test w z Fresh LocalS (fields 1) (fields 0) (u 8) hw hz hLocalS
    (typed M (fields 1) (.conjL (.conjR outer))) (typed Inner (fields 0) (.conjR (.conjR outer))) (.conjL outer) pMember pRest
  have hQ := Derives.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR hOpen))))))))
  have hInverse := Derives.conjL (.conjR hQ)
  have hInstance := Derives.conjR (.conjR (.conjR (.conjR (.conjR hInverse))))
  exact ForcingDensityGuards.introduce_from_instance hZ w z Fresh c s LocalS (u 8) (u 5) (u 6)
    hw hz hLocalS hInstance hExists pBody


/-- At the actual outer condition, derive the original target existential
by reusing the second source witness and eliminating both source existentials. -/
theorem existential_at_condition {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (Reln : Formula (k+2)) (Dom : Formula (k+1))
    (w z a A B C f j N Child b c d t L S D E G W H body Parent A1 A2 A3 K R Base Sel OldPre : Fin m)
    (images : Fin 10 → Fin m) (opened : Fin 9 → Fin m) (cv : Fin 8 → Fin m)
    (sv : Fin 7 → Fin m) (outputs : Fin 4 → Fin m) (raw : Fin 16 → Fin m)
    (hB : Derives Γ (successor B A))
    (hExist : Derives Γ (ForcingRawModalBody.existentialRecord Reln Dom w z a f A B C b c d t L S
      j Child N body Parent images opened cv sv))
    (hQueries : Derives Γ (ForcingRawModalBody.data w (opened 7) (images 9) A f z d
      (cv 2) (cv 3) (sv 4) (sv 5) (opened 8) outputs))
    (hCompiled : Derives Γ (ForcingDensityCode.compiled Reln w a A B f j N D))
    (hQuery : Derives Γ (substituted w L S a f z b D E))
    (hWeakG : Derives Γ (SyntaxWeakenFreeSyntax.weakened w z b d G W))
    (hProof : Derives Γ (implication test w z b G E))
    (hH : Derives Γ (formulaCode w H z d)) (hW : Derives Γ (formulaCode w W z d))
    (hToW : Derives Γ (implication test w z d H W))
    (pQ : Derives Γ (implication test w z d H (outputs 1)))
    (pOrder : Derives Γ (implication test w z d H (outputs 2)))
    (hA1 : Derives Γ (SyntaxNumeralSyntax.numeral 1 A1))
    (hA2 : Derives Γ (SyntaxNumeralSyntax.numeral 2 A2))
    (hA3 : Derives Γ (SyntaxNumeralSyntax.numeral 3 A3))
    (hf : Derives Γ (SyntaxNumeralSyntax.numeral (k+2) f))
    (hK : Derives Γ (SyntaxNumeralSyntax.numeral k K))
    (hj : Derives Γ (SyntaxNumeralSyntax.numeral (k+1) j))
    (hRaw : Derives Γ (ForcingPreorderCode.rawData Reln w z A1 A2 A3 f raw))
    (hOldPre : Derives Γ (substituted w R Base z f z d (raw 0) OldPre))
    (hSel : Derives Γ (SyntaxTermSyntax.term w z d Sel))
    (hBaseUpdate : Derives Γ (ForcingReflexiveImages.replacement w f z d Base j Sel (images 9)))
    (pOldPre : Derives Γ (implication test w z d H OldPre)) :
    Derives Γ (implication test w z d H (outputs 3)) := by
  let out := implication test w z d H (outputs 3)
  refine with_existential_witnesses hZ Reln Dom w z a A B C f j N Child b c d t L S D E G W H body Parent
    A1 A2 A3 K R Base Sel OldPre images opened cv sv outputs raw hB hExist hQueries hCompiled hQuery
    hWeakG hProof hH hW hToW pQ pOrder hA1 hA2 hA3 hf hK hj hRaw hOldPre hSel hBaseUpdate pOldPre out ?_
  intro l Δ ρ Br Fresh Rr Sr Nr Sq Name Extra Local OrderR TailR Bound Pfx TailS ds v u Refl Pre U0 P
    nextImages rows layout secondImages secondOpen secondFields hZ1 lift hFirst hExtra hLocal pTailR
    _ _ _ _ _ _ _ _ _ hSecond _ hSourceGuard _ pTailS hProofs hTarget
  let row : Fin 24 → Fin l := fun i => rows (i.addNat 24)
  let member := ForcingMemberRows.leafFields row 0
  let order := ForcingMemberRows.leafFields row 5
  let goal := implication test (ρ w) (ρ z) (ρ d) (ρ H) (ρ (outputs 3))
  apply of_eq (implication_rename _ _ _ _ _ _ ρ).symm
  refine eliminate_objects hZ1 2 (fun r x => secondWitnessData (r (ρ w)) (r (ρ z)) (r Br) (r Fresh)
    (r Local) (r (secondOpen 8)) (r (secondFields 1)) (r (secondFields 3)) (r order) (x 0) (x 1))
    hProofs goal ?_
  intro l1 Ξ r x hZ2 move hSecondProofs
  have hTarget1 := of_eq (targetWitnessResult_rename _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ r) (move hTarget)
  refine eliminate_objects hZ2 25 (fun e y =>
    (targetWitnessData (e (r (ρ w))) (e (r (ρ z))) (e (r (ρ A))) (e (r (ρ B))) (e (r (ρ f))) (e (r (ρ j)))
      (e (r (ρ d))) (e (r Br)) (e (r Fresh)) (e (r (ρ c))) (e (r (v 8))) (e (r (v 9)))
      (e (r (ρ (sv 4)))) (e (r (ρ (sv 3)))) (e (r (ρ (outputs 3)))) (e (r (ρ (cv 4)))) (e (r (ρ (cv 5))))
      (e (r (ρ (sv 1)))) (e (r (ρ (sv 2)))) (e (r (nextImages 9))) (e (r (P 1 2))) (e (r (P 1 0))) y).conj
      ((Formula.equal (e (r member)) (y 22)).conj
        ((Formula.equal (e (r order)) (y 23)).conj (.equal (e (r (secondFields 3))) (y 24)))))
    hTarget1 (goal.rename r) ?_
  intro l2 Θ e y hZ3 extend hTarget2
  let k := e ∘ r
  let g := k ∘ ρ
  have carry {F : Formula l} (p : Derives Δ F) : Derives Θ (F.rename k) :=
    of_eq (SourceAlgebra.rename_comp F r e) (extend (move p))
  have original {F : Formula m} (p : Derives Γ F) : Derives Θ (F.rename g) :=
    of_eq (SourceAlgebra.rename_comp F ρ k) (carry (lift p))
  let qv : Fin 10 → Fin l2 := fun i => y ((i.castAdd 13).natAdd 2)
  let qo : Fin 9 → Fin l2 := fun i => y (((i.castAdd 4).natAdd 10).natAdd 2)
  let qf : Fin 4 → Fin l2 := fun i => y (((i.natAdd 9).natAdd 10).natAdd 2)
  let localS := e (x 1)
  have hQData := Derives.conjL hTarget2
  have hQWeak := Derives.conjL hQData
  have hQ := Derives.conjR (.conjR (.conjR (.conjR hQData)))
  have hQOpen := Derives.conjL hQ
  have hQFields := Derives.conjR hQ
  have eqs := Derives.conjR hTarget2
  have hProof := of_eq (secondWitnessData_rename _ _ _ _ _ _ _ _ _ _ _ e) (extend hSecondProofs)
  have localST := Derives.conjR (.conjL (.conjR hProof))
  have sourceMemberEq : Derives Θ (.equal (k member) (k (secondFields 1))) := carry (.conjL hSourceGuard)
  have eMember := eq_trans (eq_symm sourceMemberEq) (.conjL eqs)
  have pM := witness_proof_output (g w) (g z) (k Fresh) localS (k (secondFields 1)) (qf 1)
    eMember (.conjL (.conjR (.conjR hProof)))
  have pO := witness_proof_output (g w) (g z) (k Fresh) localS (k order) (qf 2)
    (.conjL (.conjR eqs)) (.conjR (.conjR (.conjR (.conjR hProof))))
  have pN := witness_proof_output (g w) (g z) (k Fresh) localS (k (secondFields 3)) (qf 3)
    (.conjR (.conjR eqs)) (.conjL (.conjR (.conjR (.conjR hProof))))
  have raisedQ := ForcingFreshParentOpening.weakened_quantified hZ3 false (g w) (g z) (g A) (g f) (g B)
    (k Br) (g c) (k Fresh) (k (P 1 0)) (k (v 8)) (k (v 9)) (g (sv 4)) (g (sv 3)) (y 0) qv qo hQOpen
  have pQFresh := introduce_target_witness hZ3 (g w) (g z) (g A) (g B) (g f)
    (k Br) (g c) (k Fresh) (k (P 1 0)) (k (v 8)) (k (v 9)) (g (sv 4)) (g (sv 3)) (y 0)
    (g (cv 4)) (g (cv 5)) (g (sv 1)) (g (sv 2)) localS qv qo qf
    hQOpen hQFields (.conjR raisedQ) localST pM pO pN
  have hLocal1 := of_eq (by simp only [FormulaCodeConstructSyntax.typedAt_rename, SyntaxAtomSyntax.two_map]; rfl)
    (carry hLocal)
  have pQBr := discharge_opened_witness hZ3 (g w) (g z) (g A) (g f) (g B)
    (k Br) (g c) (k Fresh) (k (P 1 0)) (k Pfx) (k Nr) (g (sv 4)) (g (sv 3)) (k TailS)
    (k Local) (e (x 0)) localS (y 0) (qo 6) (k ∘ secondImages) (k ∘ secondOpen)
    (of_eq (ForcingFreshParentOpening.quantifiedData_rename false _ _ _ _ _ _ _ _ _ _ _ _ _ _
      secondImages secondOpen k) (carry hSecond))
    (.conjR hLocal1) (.conjL hProof) (.conjL (.conjL (.conjR hProof))) (.conjL raisedQ)
    (of_eq (implication_rename _ _ _ _ _ _ k) (carry pTailS)) pQFresh
  have pQOuter := discharge_opened_witness hZ3 (g w) (g z) (g A) (g f) (g B)
    (g d) (g c) (k Br) (k (P 0 1)) (k Bound) (g (images 9)) (k (ds 2)) (k (ds 1)) (k TailR)
    (g H) (k Extra) (k Local) (g (outputs 3)) (y 0) (k ∘ v) (k ∘ u)
    (of_eq (ForcingFreshParentOpening.quantifiedData_rename false _ _ _ _ _ _ _ _ _ _ _ _ _ _ v u k) (carry hFirst))
    (of_eq (formulaCode_rename _ _ _ _ g) (original hH))
    (of_eq (SyntaxWeakenFreeSyntax.weakened_rename _ _ _ _ _ _ k) (carry hExtra)) (.conjL hLocal1) hQWeak
    (of_eq (implication_rename _ _ _ _ _ _ k) (carry pTailR)) pQBr
  exact of_eq (by simp only [goal, implication_rename]; rfl) pQOuter


private theorem curry_into {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z b G A C D Y : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hG : Derives Γ (formulaCode w G z b)) (hA : Derives Γ (formulaCode w A z b))
    (hD : Derives Γ (formulaCode w D z b))
    (hC : Derives Γ (binaryCode 0 w G A C)) (hY : Derives Γ (binaryCode 2 w A D Y))
    (hp : Derives Γ (implication test w z b C D)) : Derives Γ (implication test w z b G Y) := by
  have hResult := InternalProofCurry.from_implication hZ test w z b G A C D hw hz hG hA hD hC hp
  refine eliminate_objects hZ 1 (fun r x =>
    (binaryCode 2 (r w) (r A) (r D) (x 0)).conj (implication test (r w) (r z) (r b) (r G) (x 0)))
    hResult (implication test w z b G Y) ?_
  intro l Δ r x hZ1 lift h
  have he := SyntaxConstructors.unique hZ1 2 7 (r w) (SyntaxAtomSyntax.two (r A) (r D)) (x 0) (r Y)
    (of_eq (omega_rename _ _) (lift hw)) (.conjL h)
    (of_eq (binaryCode_rename _ _ _ _ _ _) (lift hY))
  exact of_eq (implication_rename test _ _ _ _ _ r).symm
    (witness_proof_output (r w) (r z) (r b) (r G) (x 0) (r Y) he (.conjR h))

private theorem with_outer_guard_context {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z d W M O : Fin m) (hw : Derives Γ (omega w))
    (hW : Derives Γ (formulaCode w W z d)) (hM : Derives Γ (formulaCode w M z d))
    (hO : Derives Γ (formulaCode w O z d)) (out : Formula m)
    (use : ∀ {l} {Δ : Context l} (r : Fin m → Fin l) (H0 H1 : Fin l), ZFContext.Evidence Δ →
      (∀ {P : Formula m}, Derives Γ P → Derives Δ (P.rename r)) →
      Derives Δ (FormulaCodeConstructSyntax.typedAt 2 5 (r w) (SyntaxAtomSyntax.two (r W) (r M)) H0 (r z) (r d)) →
      Derives Δ (FormulaCodeConstructSyntax.typedAt 2 5 (r w) (SyntaxAtomSyntax.two H0 (r O)) H1 (r z) (r d)) →
      Derives Δ (out.rename r)) : Derives Γ out := by
  refine eliminate_objects hZ 1 (fun r x => (Formula.mem (x 0) (r w)).conj
    (FormulaCodeConstructSyntax.typedAt 2 5 (r w) (SyntaxAtomSyntax.two (r W) (r M)) (x 0) (r z) (r d)))
    (ForcingProofContext.and_exists hZ w z d W M hw hW hM) out ?_
  intro l Δ r x hZ1 lift hx
  have hw1 := of_eq (omega_rename _ _) (lift hw)
  have hO1 := of_eq (formulaCode_rename _ _ _ _ _) (lift hO)
  refine eliminate_objects hZ1 1 (fun s y => (Formula.mem (y 0) (s (r w))).conj
    (FormulaCodeConstructSyntax.typedAt 2 5 (s (r w)) (SyntaxAtomSyntax.two (s (x 0)) (s (r O)))
      (y 0) (s (r z)) (s (r d))))
    (ForcingProofContext.and_exists hZ1 (r w) (r z) (r d) (x 0) (r O) hw1 (.conjR (.conjR hx)) hO1)
    (out.rename r) ?_
  intro l1 Δ1 s y hZ2 move hy
  let R := s ∘ r
  have carry {P : Formula m} (h : Derives Γ P) : Derives Δ1 (P.rename R) :=
    of_eq (SourceAlgebra.rename_comp P r s) (move (lift h))
  have hw2 := of_eq (omega_rename _ _) (carry hw)
  have hx2 := of_eq (by simp only [FormulaCodeConstructSyntax.typedAt_rename]; rfl)
    (move (.conjR hx))
  exact of_eq (SourceAlgebra.rename_comp out r s).symm
    (use R (s (x 0)) (y 0) hZ2 carry hx2 (.conjR hy))

private theorem with_outer_density_context {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z d W M O Y : Fin m) (hw : Derives Γ (omega w))
    (hW : Derives Γ (formulaCode w W z d)) (hM : Derives Γ (formulaCode w M z d))
    (hO : Derives Γ (formulaCode w O z d)) (hYOriginal : Derives Γ (formulaCode w Y z d)) (out : Formula m)
    (use : ∀ {l} {Δ : Context l} (r : Fin m → Fin l) (H0 H1 H : Fin l), ZFContext.Evidence Δ →
      (∀ {P : Formula m}, Derives Γ P → Derives Δ (P.rename r)) →
      Derives Δ (FormulaCodeConstructSyntax.typedAt 2 5 (r w) (SyntaxAtomSyntax.two (r W) (r M)) H0 (r z) (r d)) →
      Derives Δ (FormulaCodeConstructSyntax.typedAt 2 5 (r w) (SyntaxAtomSyntax.two H0 (r O)) H1 (r z) (r d)) →
      Derives Δ (FormulaCodeConstructSyntax.typedAt 2 5 (r w) (SyntaxAtomSyntax.two H1 (r Y)) H (r z) (r d)) →
      Derives Δ (out.rename r)) : Derives Γ out := by
  refine with_outer_guard_context hZ w z d W M O hw hW hM hO out ?_
  intro l Δ1 R H0 H1 hZ2 carry hX hY
  have hw2 := of_eq (omega_rename _ R) (carry hw)
  have hY2 := of_eq (formulaCode_rename _ _ _ _ R) (carry hYOriginal)
  refine eliminate_objects hZ2 1 (fun t u => (Formula.mem (u 0) (t (R w))).conj
    (FormulaCodeConstructSyntax.typedAt 2 5 (t (R w)) (SyntaxAtomSyntax.two (t H1) (t (R Y)))
      (u 0) (t (R z)) (t (R d))))
    (ForcingProofContext.and_exists hZ2 (R w) (R z) (R d) H1 (R Y) hw2 (.conjR hY) hY2)
    (out.rename R) ?_
  intro l2 Δ2 t u hZ3 move2 hu
  let T := t ∘ R
  have carry2 {P : Formula m} (h : Derives Γ P) : Derives Δ2 (P.rename T) :=
    of_eq (SourceAlgebra.rename_comp P R t) (move2 (carry h))
  exact of_eq (SourceAlgebra.rename_comp out R t).symm
    (use T (t H0) (t H1) (u 0) hZ3 carry2
      (of_eq (by simp only [FormulaCodeConstructSyntax.typedAt_rename]; rfl) (move2 hX))
      (of_eq (by simp only [FormulaCodeConstructSyntax.typedAt_rename]; rfl) (move2 hY)) (.conjR hu))


private theorem close_guarded_universal {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z a f A b c d t L S N Body Parent G W M O Tail Inner H0 H1 : Fin m)
    (images : Fin 10 → Fin m) (opened : Fin 9 → Fin m)
    (hOpening : Derives Γ (ForcingFreshParentOpening.data w z a f A b c d t L S N Body Parent images opened))
    (hWeak : Derives Γ (SyntaxWeakenFreeSyntax.weakened w z b d G W))
    (hM : Derives Γ (formulaCode w M z d)) (hO : Derives Γ (formulaCode w O z d))
    (hTail : Derives Γ (formulaCode w Tail z d)) (hInner : Derives Γ (formulaCode w Inner z d))
    (hAnd0 : Derives Γ (FormulaCodeConstructSyntax.typedAt 2 5 w (SyntaxAtomSyntax.two W M) H0 z d))
    (hAnd1 : Derives Γ (FormulaCodeConstructSyntax.typedAt 2 5 w (SyntaxAtomSyntax.two H0 O) H1 z d))
    (hOuterCode : Derives Γ (binaryCode 2 w M Inner (opened 8)))
    (hInnerCode : Derives Γ (binaryCode 2 w O Tail Inner))
    (pTail : Derives Γ (implication test w z d H1 Tail)) :
    Derives Γ (implication test w z b G Parent) := by
  have hi := Derives.conjL hOpening
  have hw := Derives.conjL hi
  have hz := Derives.conjL (.conjR hi)
  have hc := Derives.conjL (.conjR (.conjR (.conjR hi)))
  have hG := SyntaxWeakenFreeOutput.source_type hZ w z b d G W hw hWeak
  have hW := SyntaxWeakenFreeOutput.target_type w z b d G W hWeak
  have hWAbs := ForcingFreshBackground.derive hZ w z b c d G W (.conjI hw (.conjI hz (.conjI hc hWeak)))
  have hRest := Derives.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR hOpening)))))))
  have hAllCode := Derives.conjL (.conjR hRest)
  have hAbs := Derives.conjR (.conjR (.conjR hRest))
  have hBody := SyntaxTopFormulaTyping.abstract_source_type hZ w z b c d (opened 8) (opened 4) hw hAbs
  have hBound := SyntaxTopFormulaTyping.abstract_target_type w z b c d (opened 8) (opened 4) hAbs
  have pInner := curry_into hZ w z d H0 O H1 Tail Inner hw hz (.conjR hAnd0) hO hTail
    (.conjL hAnd1) hInnerCode pTail
  have pBody := curry_into hZ w z d W M H0 Inner (opened 8) hw hz hW hM hInner
    (.conjL hAnd0) hOuterCode pInner
  have pAll := ForcingProofUniversal.generalize_body hZ test w z b c d G W M Inner (opened 8) (opened 4)
    hw hz hG hWAbs (.conjI hOuterCode (.conjI hBody (.conjI pBody (.conjI hAbs hBound))))
  refine eliminate_objects hZ 1 (fun r x =>
    (SyntaxLogicalSyntax.singleCode 9 (r w) (r (opened 4)) (x 0)).conj
      (implication test (r w) (r z) (r b) (r G) (x 0))) pAll (implication test w z b G Parent) ?_
  intro l Δ r x hZ1 lift hX
  have eq := SyntaxLogicalFields.single_unique hZ1 9 (r w) (r (opened 4)) (x 0) (r Parent)
    (of_eq (omega_rename _ r) (lift hw)) (.conjL hX)
    (of_eq (SyntaxLogicalSyntax.singleCode_rename _ _ _ _ r) (lift hAllCode))
  exact of_eq (implication_rename test _ _ _ _ _ r).symm
    (witness_proof_output (r w) (r z) (r b) (r G) (x 0) (r Parent) eq (.conjR hX))



-- Consume the original outer member and order guards and close its universal.
private theorem existential_from_opened {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (Reln : Formula (k+2)) (Dom : Formula (k+1))
    (w z a A B C f j N Child b c d t L S D E G W body Parent A1 A2 A3 K R Base Sel OldPre : Fin m)
    (images : Fin 10 → Fin m) (opened : Fin 9 → Fin m) (cv : Fin 8 → Fin m)
    (sv : Fin 7 → Fin m) (outputs : Fin 4 → Fin m) (raw : Fin 16 → Fin m)
    (hB : Derives Γ (successor B A))
    (hExist : Derives Γ (ForcingRawModalBody.existentialRecord Reln Dom w z a f A B C b c d t L S
      j Child N body Parent images opened cv sv))
    (hQueries : Derives Γ (ForcingRawModalBody.data w (opened 7) (images 9) A f z d
      (cv 2) (cv 3) (sv 4) (sv 5) (opened 8) outputs))
    (hCompiled : Derives Γ (ForcingDensityCode.compiled Reln w a A B f j N D))
    (hQuery : Derives Γ (substituted w L S a f z b D E))
    (hWeakG : Derives Γ (SyntaxWeakenFreeSyntax.weakened w z b d G W))
    (hProof : Derives Γ (implication test w z b G E))
    (hA1 : Derives Γ (SyntaxNumeralSyntax.numeral 1 A1))
    (hA2 : Derives Γ (SyntaxNumeralSyntax.numeral 2 A2))
    (hA3 : Derives Γ (SyntaxNumeralSyntax.numeral 3 A3))
    (hf : Derives Γ (SyntaxNumeralSyntax.numeral (k+2) f))
    (hK : Derives Γ (SyntaxNumeralSyntax.numeral k K))
    (hj : Derives Γ (SyntaxNumeralSyntax.numeral (k+1) j))
    (hRaw : Derives Γ (ForcingPreorderCode.rawData Reln w z A1 A2 A3 f raw))
    (hOldPre : Derives Γ (substituted w R Base z f z d (raw 0) OldPre))
    (hSel : Derives Γ (SyntaxTermSyntax.term w z d Sel))
    (hBaseUpdate : Derives Γ (ForcingReflexiveImages.replacement w f z d Base j Sel (images 9)))
    (pOldPre : Derives Γ (implication test w z d W OldPre)) :
    Derives Γ (implication test w z b G Parent) := by
  have hOpening := Derives.conjL hExist
  have hi := Derives.conjL hOpening
  have hw := Derives.conjL hi
  have hz := Derives.conjL (.conjR hi)
  have hW := SyntaxWeakenFreeOutput.target_type w z b d G W hWeakG
  have hPre := SyntaxMixedFormulaJudgment.target_type w R Base z f z d (raw 0) OldPre hOldPre
  have typed (X Y : Fin m) (p : Derives Γ (substituted w (opened 7) (images 9) A f z d X Y)) :
      Derives Γ (formulaCode w Y z d) :=
    SyntaxMixedFormulaJudgment.target_type w (opened 7) (images 9) A f z d X Y p
  have outer := Derives.conjL hQueries
  have inner := Derives.conjR hQueries
  have hM := typed (cv 2) (outputs 1) (.conjL (.conjR outer))
  have hO := typed (cv 3) (outputs 2) (.conjL (.conjR inner))
  have hTail := typed (sv 4) (outputs 3) (.conjR (.conjR inner))
  have hInner := typed (sv 5) (outputs 0) (.conjR (.conjR outer))
  let out := implication test w z b G Parent
  refine with_outer_guard_context hZ w z d W (outputs 1) (outputs 2) hw hW hM hO out ?_
  intro l Δ r H0 H hZ1 lift hAnd0 hAnd
  have hw1 := of_eq (omega_rename _ r) (lift hw)
  have hz1 := of_eq (empty_rename _ r) (lift hz)
  have type1 {Y : Fin m} (h : Derives Γ (formulaCode w Y z d)) :
      Derives Δ (formulaCode (r w) (r Y) (r z) (r d)) := of_eq (formulaCode_rename _ _ _ _ r) (lift h)
  have hH0 := Derives.conjR hAnd0
  have hH := Derives.conjR hAnd
  have pH0 := ForcingRelationGuardProof.project hZ1 test false (r w) (r z) (r d)
    H0 (r (outputs 2)) H hw1 hz1 hH0 (type1 hO) hH (.conjL hAnd)
  have pO := ForcingRelationGuardProof.project hZ1 test true (r w) (r z) (r d)
    H0 (r (outputs 2)) H hw1 hz1 hH0 (type1 hO) hH (.conjL hAnd)
  have p0W := ForcingRelationGuardProof.project hZ1 test false (r w) (r z) (r d)
    (r W) (r (outputs 1)) H0 hw1 hz1 (type1 hW) (type1 hM) hH0 (.conjL hAnd0)
  have p0M := ForcingRelationGuardProof.project hZ1 test true (r w) (r z) (r d)
    (r W) (r (outputs 1)) H0 hw1 hz1 (type1 hW) (type1 hM) hH0 (.conjL hAnd0)
  have pW := ForcingRelationGuardProof.chain hZ1 test (r w) (r z) (r d) H H0 (r W)
    hw1 hz1 hH hH0 (type1 hW) pH0 p0W
  have pM := ForcingRelationGuardProof.chain hZ1 test (r w) (r z) (r d) H H0 (r (outputs 1))
    hw1 hz1 hH hH0 (type1 hM) pH0 p0M
  have pPre := ForcingRelationGuardProof.chain hZ1 test (r w) (r z) (r d) H (r W) (r OldPre)
    hw1 hz1 hH (type1 hW) (type1 hPre) pW (of_eq (implication_rename _ _ _ _ _ _ r) (lift pOldPre))
  have hWeak := of_eq (SyntaxWeakenFreeSyntax.weakened_rename _ _ _ _ _ _ r) (lift hWeakG)
  have hExist1 := of_eq (ForcingRawModalBody.existentialRecord_rename Reln Dom
    w z a f A B C b c d t L S j Child N body Parent images opened cv sv r) (lift hExist)
  have pTail := existential_at_condition hZ1 Reln Dom (r w) (r z) (r a) (r A) (r B) (r C) (r f) (r j)
    (r N) (r Child) (r b) (r c) (r d) (r t) (r L) (r S) (r D) (r E) (r G) (r W) H (r body) (r Parent)
    (r A1) (r A2) (r A3) (r K) (r R) (r Base) (r Sel) (r OldPre) (r ∘ images) (r ∘ opened)
    (r ∘ cv) (r ∘ sv) (r ∘ outputs) (r ∘ raw) (of_eq (successor_rename _ _ r) (lift hB))
    hExist1 (of_eq (ForcingRawModalBody.data_rename _ _ _ _ _ _ _ _ _ _ _ _ outputs r) (lift hQueries))
    (of_eq (ForcingDensityCode.compiled_rename Reln w a A B f j N D r) (lift hCompiled))
    (of_eq (substituted_rename _ _ _ _ _ _ _ _ _ r) (lift hQuery)) hWeak
    (of_eq (implication_rename _ _ _ _ _ _ r) (lift hProof)) hH (type1 hW) pW pM pO
    (of_eq (SyntaxNumeralSyntax.numeral_rename _ _ r) (lift hA1)) (of_eq (SyntaxNumeralSyntax.numeral_rename _ _ r) (lift hA2))
    (of_eq (SyntaxNumeralSyntax.numeral_rename _ _ r) (lift hA3)) (of_eq (SyntaxNumeralSyntax.numeral_rename _ _ r) (lift hf))
    (of_eq (SyntaxNumeralSyntax.numeral_rename _ _ r) (lift hK)) (of_eq (SyntaxNumeralSyntax.numeral_rename _ _ r) (lift hj))
    (of_eq (ForcingPreorderCode.rawData_rename Reln w z A1 A2 A3 f raw r) (lift hRaw))
    (of_eq (substituted_rename _ _ _ _ _ _ _ _ _ r) (lift hOldPre))
    (of_eq (SyntaxTermSyntax.term_rename _ _ _ _ r) (lift hSel))
    (of_eq (ForcingReflexiveImages.replacement_rename _ _ _ _ _ _ _ _ r) (lift hBaseUpdate)) pPre
  exact of_eq (implication_rename _ _ _ _ _ _ r).symm
    (close_guarded_universal hZ1 (r w) (r z) (r a) (r f) (r A) (r b) (r c) (r d) (r t)
      (r L) (r S) (r N) (r body) (r Parent) (r G) (r W) (r (outputs 1)) (r (outputs 2))
      (r (outputs 3)) (r (outputs 0)) H0 H (r ∘ images) (r ∘ opened) (.conjL hExist1) hWeak
      (type1 hM) (type1 hO) (type1 hTail) (type1 hInner) hAnd0 hAnd
      (of_eq (binaryCode_rename _ _ _ _ _ r) (lift (.conjL outer)))
      (of_eq (binaryCode_rename _ _ _ _ _ r) (lift (.conjL inner))) pTail)


set_option maxHeartbeats 1000000 in
/-- Consume the actual negative compiler and its outer opening. Build the
three local conjunctions and discharge them in reverse order. The outer
universal is the original compiled forcing formula at p. -/
theorem negative_step_from_opened {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (Reln : Formula (k+2)) (Dom : Formula (k+1))
    (w z a A B f j n N C b c d t L S D E G W body Parent Yq Bot
      A1 A2 A3 K R Base Sel OldPre : Fin m)
    (images : Fin 10 → Fin m) (negOpen : Fin 9 → Fin m) (negData : Fin 5 → Fin m)
    (negNodes negOut : Fin 4 → Fin m) (raw : Fin 16 → Fin m)
    (hB : Derives Γ (successor B A))
    (hNeg : Derives Γ (ForcingRawModalBody.negativeRecord Reln w z a f A b c d t L S j C N body Parent
      images negOpen negData negNodes))
    (hNegQueries : Derives Γ (ForcingRawModalBody.data w (negOpen 7) (images 9) A f z d
      (negData 3) (negData 4) (negNodes 1) (negNodes 2) (negOpen 8) negOut))
    (hOperand : Derives Γ (ForcingFormulaDiagram.binaryData 2 w (negOpen 7) (images 9) A f z d
      (negData 2) (negNodes 0) (negOut 3) Yq Bot))
    (hCompiled : Derives Γ (ForcingDensityCode.compiled Reln w a A B f j N D))
    (hQuery : Derives Γ (substituted w L S a f z b D E))
    (hWeakG : Derives Γ (SyntaxWeakenFreeSyntax.weakened w z b d G W))
    (hProof : Derives Γ (implication test w z b G E))
    (hA1 : Derives Γ (SyntaxNumeralSyntax.numeral 1 A1))
    (hA2 : Derives Γ (SyntaxNumeralSyntax.numeral 2 A2))
    (hA3 : Derives Γ (SyntaxNumeralSyntax.numeral 3 A3))
    (hf : Derives Γ (SyntaxNumeralSyntax.numeral (k+2) f))
    (hK : Derives Γ (SyntaxNumeralSyntax.numeral k K))
    (hj : Derives Γ (SyntaxNumeralSyntax.numeral (k+1) j))
    (hRaw : Derives Γ (ForcingPreorderCode.rawData Reln w z A1 A2 A3 f raw))
    (hSource : Derives Γ (formulaCode w n a z))
    (hChild : Derives Γ (ForcingCodeRecursion.compiled Reln Dom w z f j a n C))
    (hOldPre : Derives Γ (substituted w R Base z f z d (raw 0) OldPre))
    (hSel : Derives Γ (SyntaxTermSyntax.term w z d Sel))
    (hBaseUpdate : Derives Γ (ForcingReflexiveImages.replacement w f z d Base j Sel (images 9)))
    (pOldPre : Derives Γ (implication test w z d W OldPre)) :
    Derives Γ (implication test w z b G Parent) := by
  have hOpening := Derives.conjL hNeg
  have hInput := Derives.conjL hOpening
  have hw := Derives.conjL hInput
  have hz := Derives.conjL (.conjR hInput)
  have hW := SyntaxWeakenFreeOutput.target_type w z b d G W hWeakG
  have hPre := SyntaxMixedFormulaJudgment.target_type w R Base z f z d (raw 0) OldPre hOldPre
  have query_type (X Y : Fin m) (h : Derives Γ (substituted w (negOpen 7) (images 9) A f z d X Y)) :
      Derives Γ (formulaCode w Y z d) :=
    SyntaxMixedFormulaJudgment.target_type w (negOpen 7) (images 9) A f z d X Y h
  have hLeft := Derives.conjL hNegQueries
  have hRight := Derives.conjR hNegQueries
  have hM := query_type (negData 3) (negOut 1) (.conjL (.conjR hLeft))
  have hO := query_type (negData 4) (negOut 2) (.conjL (.conjR hRight))
  have hY := query_type (negData 2) Yq (.conjL (.conjR hOperand))
  have hBot := query_type (negNodes 0) Bot (.conjR (.conjR hOperand))
  have hInner := query_type (negNodes 2) (negOut 0) (.conjR (.conjR hLeft))
  have hTail := query_type (negNodes 1) (negOut 3) (.conjR (.conjR hRight))
  have hRawBot : Derives Γ (SyntaxNodeSyntax.constructor 0 0 w Fin.elim0 (negNodes 0)) :=
    .conjL (.conjL (.conjL (.conjR (.conjR hNeg))))
  have hBotEq := SyntaxMixedFormulaNullary.unique hZ false w (negOpen 7) (images 9) A f z d (negNodes 0) Bot
    hw hRawBot (.conjR (.conjR hOperand))
  let out := implication test w z b G Parent
  refine with_outer_density_context hZ w z d W (negOut 1) (negOut 2) Yq hw hW hM hO hY out ?_
  intro l Δ r H0 H1 H hZ1 lift hAnd0 hAnd1 hAnd
  have hw1 := of_eq (omega_rename _ _) (lift hw)
  have hz1 := of_eq (empty_rename _ _) (lift hz)
  have typed {Y : Fin m} (h : Derives Γ (formulaCode w Y z d)) :
      Derives Δ (formulaCode (r w) (r Y) (r z) (r d)) :=
    of_eq (formulaCode_rename _ _ _ _ r) (lift h)
  have hH0 := Derives.conjR hAnd0
  have hH1 := Derives.conjR hAnd1
  have hH := Derives.conjR hAnd
  have pH1 := ForcingRelationGuardProof.project hZ1 test false (r w) (r z) (r d) H1 (r Yq) H
    hw1 hz1 hH1 (typed hY) hH (.conjL hAnd)
  have pY := ForcingRelationGuardProof.project hZ1 test true (r w) (r z) (r d) H1 (r Yq) H
    hw1 hz1 hH1 (typed hY) hH (.conjL hAnd)
  have p1H0 := ForcingRelationGuardProof.project hZ1 test false (r w) (r z) (r d) H0 (r (negOut 2)) H1
    hw1 hz1 hH0 (typed hO) hH1 (.conjL hAnd1)
  have p1O := ForcingRelationGuardProof.project hZ1 test true (r w) (r z) (r d) H0 (r (negOut 2)) H1
    hw1 hz1 hH0 (typed hO) hH1 (.conjL hAnd1)
  have pH0 := ForcingRelationGuardProof.chain hZ1 test (r w) (r z) (r d) H H1 H0
    hw1 hz1 hH hH1 hH0 pH1 p1H0
  have pO := ForcingRelationGuardProof.chain hZ1 test (r w) (r z) (r d) H H1 (r (negOut 2))
    hw1 hz1 hH hH1 (typed hO) pH1 p1O
  have p0W := ForcingRelationGuardProof.project hZ1 test false (r w) (r z) (r d)
    (r W) (r (negOut 1)) H0 hw1 hz1 (typed hW) (typed hM) hH0 (.conjL hAnd0)
  have p0M := ForcingRelationGuardProof.project hZ1 test true (r w) (r z) (r d)
    (r W) (r (negOut 1)) H0 hw1 hz1 (typed hW) (typed hM) hH0 (.conjL hAnd0)
  have pW := ForcingRelationGuardProof.chain hZ1 test (r w) (r z) (r d) H H0 (r W)
    hw1 hz1 hH hH0 (typed hW) pH0 p0W
  have pM := ForcingRelationGuardProof.chain hZ1 test (r w) (r z) (r d) H H0 (r (negOut 1))
    hw1 hz1 hH hH0 (typed hM) pH0 p0M
  have pPre := ForcingRelationGuardProof.chain hZ1 test (r w) (r z) (r d) H (r W) (r OldPre)
    hw1 hz1 hH (typed hW) (typed hPre) pW
    (of_eq (implication_rename test _ _ _ _ _ r) (lift pOldPre))
  have pOuterBot := with_negative_density_transfer hZ1 Reln Dom (r w) (r z) (r a) (r A) (r B) (r f)
    (r j) (r n) (r N) (r C) (r b) (r c) (r d) (r t) (r L) (r S) (r D) (r E) (r G) (r W)
    H (r body) (r Parent) (r Yq) (r Bot) (r A1) (r A2) (r A3) (r K) (r R) (r Base) (r Sel) (r OldPre)
    (r ∘ images) (r ∘ negOpen) (r ∘ negData) (r ∘ negNodes) (r ∘ negOut) (r ∘ raw)
    (of_eq (successor_rename _ _ _) (lift hB))
    (of_eq (ForcingRawModalBody.negativeRecord_rename Reln w z a f A b c d t L S j C N body Parent
      images negOpen negData negNodes r) (lift hNeg))
    (of_eq (ForcingRawModalBody.data_rename _ _ _ _ _ _ _ _ _ _ _ _ negOut r) (lift hNegQueries))
    (of_eq (ForcingFormulaDiagram.binaryData_rename 2 _ _ _ _ _ _ _ _ _ _ _ _ r) (lift hOperand))
    (of_eq (ForcingDensityCode.compiled_rename Reln _ _ _ _ _ _ _ _ r) (lift hCompiled))
    (of_eq (substituted_rename _ _ _ _ _ _ _ _ _ r) (lift hQuery))
    (of_eq (SyntaxWeakenFreeSyntax.weakened_rename _ _ _ _ _ _ r) (lift hWeakG))
    (of_eq (implication_rename test _ _ _ _ _ r) (lift hProof))
    hH (typed hW) pW pM pO
    (of_eq (SyntaxNumeralSyntax.numeral_rename _ _ _) (lift hA1))
    (of_eq (SyntaxNumeralSyntax.numeral_rename _ _ _) (lift hA2))
    (of_eq (SyntaxNumeralSyntax.numeral_rename _ _ _) (lift hA3))
    (of_eq (SyntaxNumeralSyntax.numeral_rename _ _ _) (lift hf))
    (of_eq (SyntaxNumeralSyntax.numeral_rename _ _ _) (lift hK))
    (of_eq (SyntaxNumeralSyntax.numeral_rename _ _ _) (lift hj))
    (of_eq (ForcingPreorderCode.rawData_rename Reln _ _ _ _ _ _ raw r) (lift hRaw))
    (of_eq (formulaCode_rename _ _ _ _ r) (lift hSource))
    (of_eq (ForcingCodeRecursion.compiled_rename Reln Dom _ _ _ _ _ _ _ r) (lift hChild))
    (of_eq (substituted_rename _ _ _ _ _ _ _ _ _ r) (lift hOldPre))
    (of_eq (SyntaxTermSyntax.term_rename _ _ _ _ r) (lift hSel))
    (of_eq (ForcingReflexiveImages.replacement_rename _ _ _ _ _ _ _ _ r) (lift hBaseUpdate))
    pPre pY
  have pBot := witness_proof_output (r w) (r z) (r d) H (r (negNodes 0)) (r Bot)
    (eq_symm (lift hBotEq)) pOuterBot
  have pTail := curry_into hZ1 (r w) (r z) (r d) H1 (r Yq) H (r Bot) (r (negOut 3))
    hw1 hz1 hH1 (typed hY) (typed hBot) (.conjL hAnd)
    (of_eq (binaryCode_rename _ _ _ _ _ r) (lift (.conjL hOperand))) pBot
  exact of_eq (implication_rename _ _ _ _ _ _ r).symm
    (close_guarded_universal hZ1 (r w) (r z) (r a) (r f) (r A) (r b) (r c) (r d) (r t)
      (r L) (r S) (r N) (r body) (r Parent) (r G) (r W) (r (negOut 1)) (r (negOut 2)) (r (negOut 3))
      (r (negOut 0)) H0 H1 (r ∘ images) (r ∘ negOpen)
      (of_eq (ForcingFreshParentOpening.data_rename _ _ _ _ _ _ _ _ _ _ _ _ _ _ images negOpen r) (lift hOpening))
      (of_eq (SyntaxWeakenFreeSyntax.weakened_rename _ _ _ _ _ _ r) (lift hWeakG))
      (typed hM) (typed hO) (typed hTail) (typed hInner) hAnd0 hAnd1
      (of_eq (binaryCode_rename _ _ _ _ _ r) (lift (.conjL hLeft)))
      (of_eq (binaryCode_rename _ _ _ _ _ r) (lift (.conjL hRight))) pTail)


set_option maxHeartbeats 1000000 in
/-- Read the negative shell from the actual compiler and open its three
implications in the fresh parent table. All of the intermediate codes are
bound by the original object-language query relations. -/
theorem negative_step_from_parent_opening {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (Reln : Formula (k+2)) (Dom : Formula (k+1))
    (w z a A B f j n N C b c d t L S D E G W body Parent
      A1 A2 A3 K R Base Sel OldPre : Fin m)
    (images : Fin 10 → Fin m) (negOpen : Fin 9 → Fin m) (raw : Fin 16 → Fin m)
    (hB : Derives Γ (successor B A))
    (hOpening : Derives Γ (ForcingFreshParentOpening.data w z a f A b c d t L S N body Parent
      images negOpen))
    (hNegCode : Derives Γ (ForcingNegCode.compiled Reln w a A f j C N))
    (hCompiled : Derives Γ (ForcingDensityCode.compiled Reln w a A B f j N D))
    (hQuery : Derives Γ (substituted w L S a f z b D E))
    (hWeakG : Derives Γ (SyntaxWeakenFreeSyntax.weakened w z b d G W))
    (hProof : Derives Γ (implication test w z b G E))
    (hA1 : Derives Γ (SyntaxNumeralSyntax.numeral 1 A1))
    (hA2 : Derives Γ (SyntaxNumeralSyntax.numeral 2 A2))
    (hA3 : Derives Γ (SyntaxNumeralSyntax.numeral 3 A3))
    (hf : Derives Γ (SyntaxNumeralSyntax.numeral (k+2) f))
    (hK : Derives Γ (SyntaxNumeralSyntax.numeral k K))
    (hj : Derives Γ (SyntaxNumeralSyntax.numeral (k+1) j))
    (hRaw : Derives Γ (ForcingPreorderCode.rawData Reln w z A1 A2 A3 f raw))
    (hSource : Derives Γ (formulaCode w n a z))
    (hChild : Derives Γ (ForcingCodeRecursion.compiled Reln Dom w z f j a n C))
    (hOldPre : Derives Γ (substituted w R Base z f z d (raw 0) OldPre))
    (hSel : Derives Γ (SyntaxTermSyntax.term w z d Sel))
    (hBaseUpdate : Derives Γ (ForcingReflexiveImages.replacement w f z d Base j Sel (images 9)))
    (pOldPre : Derives Γ (implication test w z d W OldPre)) :
    Derives Γ (implication test w z b G Parent) := by
  let out := implication test w z b G Parent
  have hNegative := ForcingRawModalBody.from_negative hZ Reln w z a f A b c d t L S j C N body
    Parent images negOpen hOpening hNegCode
  refine eliminate_objects hZ 5 (fun r cv => ForcingRawModalBody.negativeAt Reln
    (r w) (r z) (r a) (r f) (r A) (r b) (r c) (r d) (r t) (r L) (r S) (r j) (r C) (r N) (r body)
    (r Parent) (r ∘ images) (r ∘ negOpen) cv) hNegative out ?_
  intro l Δ r cv hZ1 lift hAt
  refine eliminate_objects hZ1 4 (fun s sv => let e := s ∘ r
    ForcingRawModalBody.negativeRecord Reln (e w) (e z) (e a) (e f) (e A) (e b) (e c) (e d)
      (e t) (e L) (e S) (e j) (e C) (e N) (e body) (e Parent) (e ∘ images) (e ∘ negOpen) (s ∘ cv) sv)
    hAt (out.rename r) ?_
  intro l1 Δ1 s sv hZ2 move hRecord
  let e := s ∘ r
  have carry {F : Formula m} (h : Derives Γ F) : Derives Δ1 (F.rename e) :=
    of_eq (SourceAlgebra.rename_comp F r s) (move (lift h))
  have hGuarded := Derives.conjR (.conjR (.conjR hRecord))
  have hShell := Derives.conjL (.conjR (.conjR hRecord))
  have hTailCode : Derives Δ1 (binaryCode 2 (e w) (s (cv 2)) (sv 0) (sv 1)) :=
    .conjL (.conjL (.conjR hShell))
  apply of_eq (SourceAlgebra.rename_comp out r s).symm
  refine eliminate_objects hZ2 4 (fun u q => let i := u ∘ e
    ForcingRawModalBody.guardData Reln (i w) (i (negOpen 7)) (i (images 9)) (i A) (i f) (i z)
      (i d) (i t) (u (s (cv 1))) (u (s (cv 3))) (u (s (cv 4))) (u (sv 1)) (u (sv 2))
      (i (negOpen 8)) q) hGuarded (out.rename e) ?_
  intro l2 Δ2 u q hZ3 move2 hGuard
  let i := u ∘ e
  have carry2 {F : Formula m} (h : Derives Γ F) : Derives Δ2 (F.rename i) :=
    of_eq (SourceAlgebra.rename_comp F e u) (move2 (carry h))
  have hw := of_eq (omega_rename _ _) (carry2 (.conjL (.conjL hOpening)))
  have hQueries := Derives.conjL hGuard
  have hTailQuery := Derives.conjR (.conjR (.conjR hQueries))
  have hOperands := ForcingFormulaDiagram.binary_output hZ3 2 (i w) (i (negOpen 7)) (i (images 9))
    (i A) (i f) (i z) (i d) (u (sv 1)) (u (s (cv 2))) (u (sv 0)) (q 3) hw
    (of_eq (binaryCode_rename _ _ _ _ _ u) (move2 hTailCode)) hTailQuery
  apply of_eq (SourceAlgebra.rename_comp out e u).symm
  refine eliminate_objects hZ3 2 (fun v x => let ρ := v ∘ i
    ForcingFormulaDiagram.binaryData 2 (ρ w) (ρ (negOpen 7)) (ρ (images 9)) (ρ A) (ρ f) (ρ z) (ρ d)
      (v (u (s (cv 2)))) (v (u (sv 0))) (v (q 3)) (x 0) (x 1)) hOperands (out.rename i) ?_
  intro l3 Δ3 v x hZ4 move3 hOperand
  let ρ := v ∘ i
  have carry3 {F : Formula m} (h : Derives Γ F) : Derives Δ3 (F.rename ρ) :=
    of_eq (SourceAlgebra.rename_comp F i v) (move3 (carry2 h))
  have hRecord3 := of_eq
    (ForcingRawModalBody.negativeRecord_rename Reln (e w) (e z) (e a) (e f) (e A) (e b) (e c)
      (e d) (e t) (e L) (e S) (e j) (e C) (e N) (e body) (e Parent) (e ∘ images) (e ∘ negOpen)
      (s ∘ cv) sv (v ∘ u))
    (of_eq (SourceAlgebra.rename_comp _ u v) (move3 (move2 hRecord)))
  have hQueries3 := of_eq (ForcingRawModalBody.data_rename _ _ _ _ _ _ _ _ _ _ _ _ q v) (move3 hQueries)
  apply of_eq (SourceAlgebra.rename_comp out i v).symm
  apply of_eq (implication_rename test _ _ _ _ _ ρ).symm
  exact negative_step_from_opened hZ4 Reln Dom
    (ρ w) (ρ z) (ρ a) (ρ A) (ρ B) (ρ f) (ρ j) (ρ n) (ρ N) (ρ C) (ρ b) (ρ c) (ρ d)
    (ρ t) (ρ L) (ρ S) (ρ D) (ρ E) (ρ G) (ρ W) (ρ body) (ρ Parent) (x 0) (x 1)
    (ρ A1) (ρ A2) (ρ A3) (ρ K) (ρ R) (ρ Base) (ρ Sel) (ρ OldPre)
    (ρ ∘ images) (ρ ∘ negOpen) (v ∘ u ∘ s ∘ cv) (v ∘ u ∘ sv) (v ∘ q) (ρ ∘ raw)
    (of_eq (successor_rename _ _ _) (carry3 hB)) hRecord3 hQueries3 hOperand
    (of_eq (ForcingDensityCode.compiled_rename Reln _ _ _ _ _ _ _ _ ρ) (carry3 hCompiled))
    (of_eq (substituted_rename _ _ _ _ _ _ _ _ _ ρ) (carry3 hQuery))
    (of_eq (SyntaxWeakenFreeSyntax.weakened_rename _ _ _ _ _ _ ρ) (carry3 hWeakG))
    (of_eq (implication_rename test _ _ _ _ _ ρ) (carry3 hProof))
    (of_eq (SyntaxNumeralSyntax.numeral_rename _ _ _) (carry3 hA1))
    (of_eq (SyntaxNumeralSyntax.numeral_rename _ _ _) (carry3 hA2))
    (of_eq (SyntaxNumeralSyntax.numeral_rename _ _ _) (carry3 hA3))
    (of_eq (SyntaxNumeralSyntax.numeral_rename _ _ _) (carry3 hf))
    (of_eq (SyntaxNumeralSyntax.numeral_rename _ _ _) (carry3 hK))
    (of_eq (SyntaxNumeralSyntax.numeral_rename _ _ _) (carry3 hj))
    (of_eq (ForcingPreorderCode.rawData_rename Reln _ _ _ _ _ _ raw ρ) (carry3 hRaw))
    (of_eq (formulaCode_rename _ _ _ _ ρ) (carry3 hSource))
    (of_eq (ForcingCodeRecursion.compiled_rename Reln Dom _ _ _ _ _ _ _ ρ) (carry3 hChild))
    (of_eq (substituted_rename _ _ _ _ _ _ _ _ _ ρ) (carry3 hOldPre))
    (of_eq (SyntaxTermSyntax.term_rename _ _ _ _ ρ) (carry3 hSel))
    (of_eq (ForcingReflexiveImages.replacement_rename _ _ _ _ _ _ _ _ ρ) (carry3 hBaseUpdate))
    (of_eq (implication_rename test _ _ _ _ _ ρ) (carry3 pOldPre))




private theorem with_raised_density_background {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z a f j b d L S G R Base Sel RawPre Pre : Fin m) (images : Fin 10 → Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hImages : Derives Γ (ForcingWeakenedImages.data w a f z b d L S images))
    (hG : Derives Γ (formulaCode w G z b))
    (hPre : Derives Γ (substituted w R Base z f z b RawPre Pre))
    (hSel : Derives Γ (SyntaxTermSyntax.term w z b Sel))
    (hUpdate : Derives Γ (ForcingReflexiveImages.replacement w f z b Base j Sel S))
    (pPre : Derives Γ (implication test w z b G Pre)) (out : Formula m)
    (use : ∀ {l} {Δ : Context l} (ρ : Fin m → Fin l) (Bound Base' Sel' Pre' Weak : Fin l),
      ZFContext.Evidence Δ → (∀ {F : Formula m}, Derives Γ F → Derives Δ (F.rename ρ)) →
      Derives Δ (SyntaxWeakenFreeSyntax.weakened (ρ w) (ρ z) (ρ b) (ρ d) (ρ G) Weak) →
      Derives Δ (substituted (ρ w) Bound Base' (ρ z) (ρ f) (ρ z) (ρ d) (ρ RawPre) Pre') →
      Derives Δ (SyntaxTermSyntax.term (ρ w) (ρ z) (ρ d) Sel') →
      Derives Δ (ForcingReflexiveImages.replacement (ρ w) (ρ f) (ρ z) (ρ d) Base' (ρ j) Sel' (ρ (images 9))) →
      Derives Δ (implication test (ρ w) (ρ z) (ρ d) Weak Pre') →
      Derives Δ (out.rename ρ)) : Derives Γ out := by
  have hBase := Derives.conjR (.conjR (SyntaxMixedFormulaOutput.input_of_substituted hZ
    w R Base z f z b RawPre Pre hw hPre))
  have hSucc := Derives.conjL (.conjR (.conjL hImages))
  have hWeak := SyntaxWeakenFreeOutput.exists_output hZ w z b d G hw (.conjI hG hSucc)
  refine ForcingWeakenedOverwrite.with_base_of_update hZ w a f z b d L Base j Sel S
    images hImages hBase hSel hUpdate out ?_
  intro l Δ r base sel hZ1 lift hBaseImages hSel1 hUpdate1
  refine eliminate_objects hZ1 1 (fun s x =>
    SyntaxWeakenFreeSyntax.weakened (s (r w)) (s (r z)) (s (r b)) (s (r d)) (s (r G)) (x 0))
    (of_eq (SyntaxWeakenFreeSyntax.existsOutput_rename _ _ _ _ _ r) (lift hWeak)) (out.rename r) ?_
  intro l1 Δ1 s x hZ2 move hWeakG
  let e := s ∘ r
  have carry {F : Formula m} (h : Derives Γ F) : Derives Δ1 (F.rename e) :=
    of_eq (SourceAlgebra.rename_comp F r s) (move (lift h))
  apply of_eq (SourceAlgebra.rename_comp out r s).symm
  refine ForcingDensityInstantiation.with_raised_preorder hZ2 (e w) (e z) (e a) (e f) (e b) (e d)
    (e L) (e Base) (e R) (e RawPre) (e Pre) (e G) (x 0) (s ∘ base)
    (of_eq (omega_rename _ _) (carry hw)) (of_eq (empty_rename _ _) (carry hz))
    (of_eq (ForcingWeakenedImages.data_rename _ _ _ _ _ _ _ _ base s) (move hBaseImages))
    (of_eq (substituted_rename _ _ _ _ _ _ _ _ _ e) (carry hPre)) hWeakG
    (of_eq (implication_rename test _ _ _ _ _ e) (carry pPre)) (out.rename e) ?_
  intro l2 Δ2 u Bnd Pre1 hZ3 move2 _ _ hPre1 pPre1
  let ρ := u ∘ e
  have lift3 {F : Formula m} (h : Derives Γ F) : Derives Δ2 (F.rename ρ) :=
    of_eq (SourceAlgebra.rename_comp F e u) (move2 (carry h))
  have hUpdate2 := of_eq (ForcingReflexiveImages.replacement_rename _ _ _ _ _ _ _ _ (u ∘ s))
    (of_eq (SourceAlgebra.rename_comp _ s u) (move2 (move hUpdate1)))
  have hSel2 := of_eq (SyntaxTermSyntax.term_rename _ _ _ _ (u ∘ s))
    (of_eq (SourceAlgebra.rename_comp _ s u) (move2 (move hSel1)))
  exact of_eq (SourceAlgebra.rename_comp out e u).symm
    (use ρ Bnd (u (s (base 9))) (u (s sel)) Pre1 (u (x 0)) hZ3 lift3
      (of_eq (SyntaxWeakenFreeSyntax.weakened_rename _ _ _ _ _ _ u) (move2 hWeakG)) hPre1 hSel2 hUpdate2 pPre1)


private theorem negative_from_runtime_opening {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (Reln : Formula (k+2)) (Dom : Formula (k+1))
    (w z a A B f j n N C b c d t L S D E G body Parent
      A1 A2 A3 K R Base Sel Pre : Fin m)
    (images : Fin 10 → Fin m) (negOpen : Fin 9 → Fin m) (raw : Fin 16 → Fin m)
    (hB : Derives Γ (successor B A))
    (hOpening : Derives Γ (ForcingFreshParentOpening.data w z a f A b c d t L S N body Parent images negOpen))
    (hNegCode : Derives Γ (ForcingNegCode.compiled Reln w a A f j C N))
    (hCompiled : Derives Γ (ForcingDensityCode.compiled Reln w a A B f j N D))
    (hQuery : Derives Γ (substituted w L S a f z b D E))
    (hG : Derives Γ (formulaCode w G z b))
    (hProof : Derives Γ (implication test w z b G E))
    (hA1 : Derives Γ (SyntaxNumeralSyntax.numeral 1 A1))
    (hA2 : Derives Γ (SyntaxNumeralSyntax.numeral 2 A2))
    (hA3 : Derives Γ (SyntaxNumeralSyntax.numeral 3 A3))
    (hf : Derives Γ (SyntaxNumeralSyntax.numeral (k+2) f))
    (hK : Derives Γ (SyntaxNumeralSyntax.numeral k K))
    (hj : Derives Γ (SyntaxNumeralSyntax.numeral (k+1) j))
    (hRaw : Derives Γ (ForcingPreorderCode.rawData Reln w z A1 A2 A3 f raw))
    (hSource : Derives Γ (formulaCode w n a z))
    (hChild : Derives Γ (ForcingCodeRecursion.compiled Reln Dom w z f j a n C))
    (hPre : Derives Γ (substituted w R Base z f z b (raw 0) Pre))
    (hSel : Derives Γ (SyntaxTermSyntax.term w z b Sel))
    (hUpdate : Derives Γ (ForcingReflexiveImages.replacement w f z b Base j Sel S))
    (pPre : Derives Γ (implication test w z b G Pre)) : Derives Γ (implication test w z b G Parent) := by
  let out := implication test w z b G Parent
  have hInput := Derives.conjL hOpening
  have hw := Derives.conjL hInput
  have hz := Derives.conjL (.conjR hInput)
  have hImages := Derives.conjL (.conjR hOpening)
  refine with_raised_density_background hZ w z a f j b d L S G R Base Sel (raw 0) Pre images
    hw hz hImages hG hPre hSel hUpdate pPre out ?_
  intro l Δ ρ Bnd Base1 Sel1 Pre1 Weak hZ3 lift3 hWeakG hPre1 hSel2 hUpdate2 pPre1
  apply of_eq (implication_rename test _ _ _ _ _ ρ).symm
  exact negative_step_from_parent_opening hZ3 Reln Dom (ρ w) (ρ z) (ρ a) (ρ A) (ρ B) (ρ f) (ρ j)
    (ρ n) (ρ N) (ρ C) (ρ b) (ρ c) (ρ d) (ρ t) (ρ L) (ρ S) (ρ D) (ρ E) (ρ G) Weak
    (ρ body) (ρ Parent) (ρ A1) (ρ A2) (ρ A3) (ρ K) Bnd Base1 Sel1 Pre1
    (ρ ∘ images) (ρ ∘ negOpen) (ρ ∘ raw)
    (of_eq (successor_rename _ _ ρ) (lift3 hB))
    (of_eq (ForcingFreshParentOpening.data_rename _ _ _ _ _ _ _ _ _ _ _ _ _ _ images negOpen ρ) (lift3 hOpening))
    (of_eq (ForcingNegCode.compiled_rename Reln _ _ _ _ _ _ _ ρ) (lift3 hNegCode))
    (of_eq (ForcingDensityCode.compiled_rename Reln _ _ _ _ _ _ _ _ ρ) (lift3 hCompiled))
    (of_eq (substituted_rename _ _ _ _ _ _ _ _ _ ρ) (lift3 hQuery))
    hWeakG
    (of_eq (implication_rename test _ _ _ _ _ ρ) (lift3 hProof))
    (of_eq (SyntaxNumeralSyntax.numeral_rename _ _ _) (lift3 hA1))
    (of_eq (SyntaxNumeralSyntax.numeral_rename _ _ _) (lift3 hA2))
    (of_eq (SyntaxNumeralSyntax.numeral_rename _ _ _) (lift3 hA3))
    (of_eq (SyntaxNumeralSyntax.numeral_rename _ _ _) (lift3 hf))
    (of_eq (SyntaxNumeralSyntax.numeral_rename _ _ _) (lift3 hK))
    (of_eq (SyntaxNumeralSyntax.numeral_rename _ _ _) (lift3 hj))
    (of_eq (ForcingPreorderCode.rawData_rename Reln _ _ _ _ _ _ raw ρ) (lift3 hRaw))
    (of_eq (formulaCode_rename _ _ _ _ ρ) (lift3 hSource))
    (of_eq (ForcingCodeRecursion.compiled_rename Reln Dom _ _ _ _ _ _ _ ρ) (lift3 hChild))
    hPre1 hSel2 hUpdate2 pPre1



set_option maxHeartbeats 2600000 in
/-- The negative clause of the original density induction. The complete
source compiler record and the common preorder runtime suffice for every
actual density and parent query in the transfer predicate. -/
theorem negative_step_from_runtime {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (Reln : Formula (k+2)) (Dom : Formula (k+1))
    (w z a f j b Big R S T SOld SNew A1 A2 A3 K Extra A B C h n N : Fin m)
    (raw : Fin 16 → Fin m) (images : Fin 10 → Fin m) (Cr Refl Pre U0 : Fin 2 → Fin m)
    (P : Fin 2 → Fin 3 → Fin m) (rows : Fin 48 → Fin m) (layout : Fin 6 → Fin m)
    (hr : Derives Γ (ForcingRawModalBody.globalModalInput test Reln w z a f j b Big R S T SOld SNew
      A1 A2 A3 K Extra raw images Cr Refl Pre U0 P rows layout))
    (hA : Derives Γ (successor A a)) (hB : Derives Γ (successor B A))
    (hn : Derives Γ (OrdinalSyntax.ordinal n))
    (hh : Derives Γ (ForcingCodeRecursion.graph Reln Dom w z f j h n))
    (hNeg : Derives Γ (ForcingCodeStep.negative Reln Dom w z f j a A B C h n N)) :
    Derives Γ (transfer Reln w z a A B f b j T SNew (layout 3) N) := by
  let row : Fin 24 → Fin m := fun i => rows (i.castAdd 24)
  let H := ForcingMemberRows.leafFields row
  let G := layout 3
  let out := transfer Reln w z a A B f b j T SNew G N
  have hGlobal := Derives.conjL hr
  have hRows := Derives.conjL (.conjL hGlobal)
  have hBasis := Derives.conjL hRows
  have hRow := Derives.conjL (.conjR hRows)
  have hFresh := Derives.conjL (.conjR hGlobal)
  have hFreshInput := Derives.conjL hFresh
  have hz := Derives.conjL hFreshInput
  have hc := Derives.conjL (.conjR hFreshInput)
  have hImages := Derives.conjL (.conjR (.conjR hFreshInput))
  have hw := Derives.conjL (.conjL hImages)
  have hBig := Derives.conjL (.conjR (.conjL hImages))
  have hRaw := Derives.conjL (.conjR (.conjR (.conjR hFreshInput)))
  have hVar := Derives.conjL (.conjR hFresh)
  have hTerm := Derives.conjL (.conjR (.conjR hFresh))
  have hPre := Derives.conjR (.conjR (.conjR (.conjR (.conjR (.conjR hFreshInput)))))
  have hAux := Derives.conjR hr
  have hj := Derives.conjL (.conjR hAux)
  have hUpdate := Derives.conjR (.conjR (.conjR hAux))
  have hSel := ForcingRelationWeakening.row_term test Reln w z A1 A2 A3 f b (Cr 0) R S (Refl 0)
    (Pre 0) (U0 0) raw (P 0) row hRow 1
  have hOne := Derives.conjL (.conjR hBasis)
  have hTwo := Derives.conjL (.conjR (.conjR hBasis))
  have hK := Derives.conjL (.conjR (.conjR (.conjR hBasis)))
  have hf := Derives.conjL (.conjR (.conjR (.conjR (.conjR hBasis))))
  have hThree := Derives.conjR (.conjL hGlobal)
  have hExtra := Derives.conjL (.conjR (.conjR hGlobal))
  have hLayout : Derives Γ (ForcingProofContext.layoutData w z b Extra (Pre 0) H layout) :=
    .conjR (.conjR (.conjR hGlobal))
  have hG := Derives.conjR (.conjL (.conjR (.conjR (.conjR hLayout))))
  have pPre := Derives.conjL (ForcingAtomicMono.layout_proofs hZ w z b Extra (Pre 0) H layout hw hz hExtra hLayout)
  refine eliminate_objects hZ 2 (fun r v =>
    (FormulaCodeRecursiveSyntax.singleFields 4 false (r w) (r a) (r z) (v 0) (r n)).conj
      ((ForcingCodeStep.read (r w) (r h) (v 0) (r a) (r f) (v 1)).conj
        (ForcingNegCode.compiled Reln (r w) (r a) (r A) (r f) (r j) (v 1) (r N)))) hNeg out ?_
  intro l Δ r v hZ1 lift hRecord
  have hChild := ForcingCodeRecursion.read_to_compiled hZ1 Reln Dom (r w) (r z) (r f) (r j) (r h) (r n)
    (r a) (v 0) (v 1) (of_eq (OrdinalSyntax.ordinal_rename _ r) (lift hn)) (.conjL (.conjR (.conjL hRecord)))
    (of_eq (ForcingCodeRecursion.graph_rename Reln Dom _ _ _ _ _ _ r) (lift hh)) (.conjL (.conjR hRecord))
  have hChildType := Derives.conjR (.conjR (.conjL hRecord))
  have hNegCode := Derives.conjR (.conjR hRecord)
  apply of_eq (transfer_rename Reln _ _ _ _ _ _ _ _ _ _ _ _ r).symm
  refine intro_transfer hZ1 Reln (r w) (r z) (r a) (r A) (r B) (r f) (r b) (r j) (r T) (r SNew) (r G) (r N) ?_
  intro l1 Δ1 s D E Parent hZ2 move hCompiled hQuery hParent pD
  let e := s ∘ r
  have carry {F : Formula m} (d : Derives Γ F) : Derives Δ1 (F.rename e) :=
    of_eq (SourceAlgebra.rename_comp F r s) (move (lift d))
  have hNeg2 := of_eq (ForcingNegCode.compiled_rename Reln _ _ _ _ _ _ _ s) (move hNegCode)
  let goal := implication test (e w) (e z) (e b) (e G) Parent
  refine eliminate_objects hZ2 1 (fun u x =>
    (SyntaxLogicalSyntax.singleCode 9 (u (e w)) (x 0) (u (e N))).conj
      (formulaCode (u (e w)) (x 0) (u (e A)) (u (e f))))
    (ForcingNegCode.body_output Reln (e w) (e a) (e A) (e f) (e j) (s (v 1)) (e N) hNeg2) goal ?_
  intro l2 Δ2 u x hZ3 move2 hBody
  let i := u ∘ e
  have carry2 {F : Formula m} (d : Derives Γ F) : Derives Δ2 (F.rename i) :=
    of_eq (SourceAlgebra.rename_comp F e u) (move2 (carry d))
  have hOpen := ForcingFreshParentOpening.produce hZ3 (i w) (i z) (i a) (i f) (i A) (i b) (i (Cr 1))
    (i Big) (i (P 1 0)) (i T) (i SNew) (i N) (x 0) (u Parent)
    (.conjI (of_eq (omega_rename _ _) (carry2 hw))
      (.conjI (of_eq (empty_rename _ _) (carry2 hz))
        (.conjI (of_eq (successor_rename _ _ i) (carry2 hA))
          (.conjI (of_eq (successor_rename _ _ i) (carry2 hc))
            (.conjI (of_eq (successor_rename _ _ i) (carry2 hBig))
              (.conjI (of_eq (SyntaxVariableSyntax.code_rename _ _ _ _ i) (carry2 hVar))
                (.conjI (of_eq (SyntaxTermSyntax.term_rename _ _ _ _ i) (carry2 hTerm))
                  (.conjI (.conjL hBody) (of_eq (substituted_rename _ _ _ _ _ _ _ _ _ u) (move2 hParent))))))))))
  refine eliminate_objects hZ3 10 (fun σ vv =>
    ForcingFreshParentOpening.atImages (σ (i w)) (σ (i z)) (σ (i a)) (σ (i f)) (σ (i A)) (σ (i b))
      (σ (i (Cr 1))) (σ (i Big)) (σ (i (P 1 0))) (σ (i T)) (σ (i SNew)) (σ (i N)) (σ (x 0))
      (σ (u Parent)) vv) hOpen (goal.rename u) ?_
  intro l3 Δ3 σ vv hZ4 move3 hAt
  let η := σ ∘ i
  have carry3 {F : Formula m} (d : Derives Γ F) : Derives Δ3 (F.rename η) :=
    of_eq (SourceAlgebra.rename_comp F i σ) (move3 (carry2 d))
  refine eliminate_objects hZ4 9 (fun τ uu => let ρ := τ ∘ η
    ForcingFreshParentOpening.data (ρ w) (ρ z) (ρ a) (ρ f) (ρ A) (ρ b) (ρ (Cr 1)) (ρ Big)
      (ρ (P 1 0)) (ρ T) (ρ SNew) (ρ N) (τ (σ (x 0))) (τ (σ (u Parent))) (τ ∘ vv) uu)
    hAt ((goal.rename u).rename σ) ?_
  intro l4 Δ4 τ uu hZ5 move4 hOpening
  let ρ := τ ∘ η
  let μ := τ ∘ σ ∘ u
  let χ := μ ∘ s
  have carry4 {F : Formula m} (d : Derives Γ F) : Derives Δ4 (F.rename ρ) :=
    of_eq (SourceAlgebra.rename_comp F η τ) (move4 (carry3 d))
  have latest {F : Formula l1} (d : Derives Δ1 F) : Derives Δ4 (F.rename μ) :=
    of_eq (by simp only [μ, SourceAlgebra.rename_comp]; rfl) (move4 (move3 (move2 d)))
  have earlier {F : Formula l} (d : Derives Δ F) : Derives Δ4 (F.rename χ) :=
    of_eq (SourceAlgebra.rename_comp F s μ) (latest (move d))
  apply of_eq (by simp only [SourceAlgebra.rename_comp]; rfl)
  apply of_eq (implication_rename test _ _ _ _ _ μ).symm
  exact negative_from_runtime_opening hZ5 Reln Dom (ρ w) (ρ z) (ρ a) (ρ A) (ρ B) (ρ f) (ρ j)
    (χ (v 0)) (ρ N) (χ (v 1)) (ρ b) (ρ (Cr 1)) (ρ Big) (ρ (P 1 0)) (ρ T) (ρ SNew)
    (μ D) (μ E) (ρ G) (τ (σ (x 0))) (μ Parent) (ρ A1) (ρ A2) (ρ A3) (ρ K) (ρ R) (ρ S) (ρ (P 0 1)) (ρ (Pre 0))
    (τ ∘ vv) uu (ρ ∘ raw) (of_eq (successor_rename _ _ ρ) (carry4 hB)) hOpening
    (of_eq (ForcingNegCode.compiled_rename Reln _ _ _ _ _ _ _ χ) (earlier hNegCode))
    (of_eq (ForcingDensityCode.compiled_rename Reln _ _ _ _ _ _ _ _ μ) (latest hCompiled))
    (of_eq (substituted_rename _ _ _ _ _ _ _ _ _ μ) (latest hQuery))
    (of_eq (formulaCode_rename _ _ _ _ ρ) (carry4 hG))
    (of_eq (implication_rename test _ _ _ _ _ μ) (latest pD))
    (of_eq (SyntaxNumeralSyntax.numeral_rename _ _ _) (carry4 hOne))
    (of_eq (SyntaxNumeralSyntax.numeral_rename _ _ _) (carry4 hTwo))
    (of_eq (SyntaxNumeralSyntax.numeral_rename _ _ _) (carry4 hThree))
    (of_eq (SyntaxNumeralSyntax.numeral_rename _ _ _) (carry4 hf))
    (of_eq (SyntaxNumeralSyntax.numeral_rename _ _ _) (carry4 hK))
    (of_eq (SyntaxNumeralSyntax.numeral_rename _ _ _) (carry4 hj))
    (of_eq (ForcingPreorderCode.rawData_rename Reln _ _ _ _ _ _ raw ρ) (carry4 hRaw))
    (of_eq (formulaCode_rename _ _ _ _ χ) (earlier hChildType))
    (of_eq (ForcingCodeRecursion.compiled_rename Reln Dom _ _ _ _ _ _ _ χ) (earlier hChild))
    (of_eq (substituted_rename _ _ _ _ _ _ _ _ _ ρ) (carry4 hPre))
    (of_eq (SyntaxTermSyntax.term_rename _ _ _ _ ρ) (carry4 hSel))
    (of_eq (ForcingReflexiveImages.replacement_rename _ _ _ _ _ _ _ _ ρ) (carry4 hUpdate))
    (of_eq (implication_rename test _ _ _ _ _ ρ) (carry4 pPre))



private def negativeInput {k m} (Reln : Formula (k+2)) (Dom : Formula (k+1))
    (w z a f j b Big R S T SOld SNew A1 A2 A3 K Extra A B C h n N : Fin m)
    (raw : Fin 16 → Fin m) (images : Fin 10 → Fin m) (Cr Refl Pre U0 : Fin 2 → Fin m)
    (P : Fin 2 → Fin 3 → Fin m) (rows : Fin 48 → Fin m) (layout : Fin 6 → Fin m) : Formula m :=
  (ForcingRawModalBody.globalModalInput test Reln w z a f j b Big R S T SOld SNew
    A1 A2 A3 K Extra raw images Cr Refl Pre U0 P rows layout).conj
    ((successor A a).conj ((successor B A).conj ((OrdinalSyntax.ordinal n).conj
      ((ForcingCodeRecursion.graph Reln Dom w z f j h n).conj
        (ForcingCodeStep.negative Reln Dom w z f j a A B C h n N)))))

def negativeSentence {k m} (Reln : Formula (k+2)) (Dom : Formula (k+1))
    (w z a f j b Big R S T SOld SNew A1 A2 A3 K Extra A B C h n N : Fin m)
    (raw : Fin 16 → Fin m) (images : Fin 10 → Fin m) (Cr Refl Pre U0 : Fin 2 → Fin m)
    (P : Fin 2 → Fin 3 → Fin m) (rows : Fin 48 → Fin m) (layout : Fin 6 → Fin m) : Source.Sentence :=
  ((negativeInput Reln Dom w z a f j b Big R S T SOld SNew A1 A2 A3 K Extra A B C h n N
    raw images Cr Refl Pre U0 P rows layout).imp (transfer Reln w z a A B f b j T SNew (layout 3) N)).close

theorem negative_kernel_certificate {k m} (Reln : Formula (k+2)) (Dom : Formula (k+1))
    (w z a f j b Big R S T SOld SNew A1 A2 A3 K Extra A B C h n N : Fin m)
    (raw : Fin 16 → Fin m) (images : Fin 10 → Fin m) (Cr Refl Pre U0 : Fin 2 → Fin m)
    (P : Fin 2 → Fin 3 → Fin m) (rows : Fin 48 → Fin m) (layout : Fin 6 → Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
      (Translation.sentence (negativeSentence Reln Dom w z a f j b Big R S T SOld SNew A1 A2 A3 K Extra
        A B C h n N raw images Cr Refl Pre U0 P rows layout)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  let F := negativeInput Reln Dom w z a f j b Big R S T SOld SNew A1 A2 A3 K Extra A B C h n N
    raw images Cr Refl Pre U0 P rows layout
  let Γ := Context.add F (Source.SetLanguage.ZF.at m)
  have hF : Derives Γ F := .hyp (Or.inl rfl)
  have hRest := Derives.conjR hF
  exact negative_step_from_runtime (ZFContext.add (ZFContext.source_ZF m) F) Reln Dom
    w z a f j b Big R S T SOld SNew A1 A2 A3 K Extra A B C h n N raw images Cr Refl Pre U0 P rows layout
    (.conjL hF) (.conjL hRest) (.conjL (.conjR hRest)) (.conjL (.conjR (.conjR hRest)))
    (.conjL (.conjR (.conjR (.conjR hRest)))) (.conjR (.conjR (.conjR (.conjR hRest))))



private theorem existential_from_runtime_record {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (Reln : Formula (k+2)) (Dom : Formula (k+1))
    (w z a A B C f j N Child b c d t L S D E G Parent A1 A2 A3 K R Base Sel Pre : Fin m)
    (images : Fin 10 → Fin m) (opened : Fin 9 → Fin m) (cv : Fin 8 → Fin m)
    (sv : Fin 7 → Fin m) (raw : Fin 16 → Fin m)
    (hB : Derives Γ (successor B A))
    (hExist : Derives Γ (ForcingRawModalBody.existentialRecord Reln Dom w z a f A B C b c d t L S
      j Child N (sv 6) Parent images opened cv sv))
    (hCompiled : Derives Γ (ForcingDensityCode.compiled Reln w a A B f j N D))
    (hQuery : Derives Γ (substituted w L S a f z b D E))
    (hG : Derives Γ (formulaCode w G z b))
    (hProof : Derives Γ (implication test w z b G E))
    (hA1 : Derives Γ (SyntaxNumeralSyntax.numeral 1 A1)) (hA2 : Derives Γ (SyntaxNumeralSyntax.numeral 2 A2)) (hA3 : Derives Γ (SyntaxNumeralSyntax.numeral 3 A3))
    (hf : Derives Γ (SyntaxNumeralSyntax.numeral (k+2) f)) (hK : Derives Γ (SyntaxNumeralSyntax.numeral k K)) (hj : Derives Γ (SyntaxNumeralSyntax.numeral (k+1) j))
    (hRaw : Derives Γ (ForcingPreorderCode.rawData Reln w z A1 A2 A3 f raw))
    (hPre : Derives Γ (substituted w R Base z f z b (raw 0) Pre))
    (hSel : Derives Γ (SyntaxTermSyntax.term w z b Sel))
    (hUpdate : Derives Γ (ForcingReflexiveImages.replacement w f z b Base j Sel S))
    (pPre : Derives Γ (implication test w z b G Pre)) :
    Derives Γ (implication test w z b G Parent) := by
  let out := implication test w z b G Parent
  have hOpen := Derives.conjL hExist
  have hw := Derives.conjL (.conjL hOpen)
  have hz := Derives.conjL (.conjR (.conjL hOpen))
  have hImages := Derives.conjL (.conjR hOpen)
  have hShell := Derives.conjL (.conjR (.conjR hExist))
  have spine := Derives.conjR (.conjR (.conjR (.conjR (.conjR hShell))))
  have hBody := Derives.conjL (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR hOpen))))))))
  have hOutputs := ForcingRawModalBody.from_query hZ w (opened 7) (images 9) A f z d
    (cv 2) (cv 3) (sv 4) (sv 5) (sv 6) (opened 8) hw
    (.conjL (.conjL (.conjR spine))) (.conjL (.conjL spine)) hBody
  refine eliminate_objects hZ 4 (fun r x => ForcingRawModalBody.data
    (r w) (r (opened 7)) (r (images 9)) (r A) (r f) (r z) (r d)
    (r (cv 2)) (r (cv 3)) (r (sv 4)) (r (sv 5)) (r (opened 8)) x) hOutputs out ?_
  intro l Δ r x hZ1 lift hOutputs1
  refine with_raised_density_background hZ1 (r w) (r z) (r a) (r f) (r j) (r b) (r d) (r L) (r S) (r G)
    (r R) (r Base) (r Sel) (r (raw 0)) (r Pre) (r ∘ images)
    (of_eq (omega_rename _ r) (lift hw)) (of_eq (empty_rename _ r) (lift hz))
    (of_eq (ForcingWeakenedImages.data_rename _ _ _ _ _ _ _ _ images r) (lift hImages))
    (of_eq (formulaCode_rename _ _ _ _ r) (lift hG))
    (of_eq (substituted_rename _ _ _ _ _ _ _ _ _ r) (lift hPre))
    (of_eq (SyntaxTermSyntax.term_rename _ _ _ _ r) (lift hSel))
    (of_eq (ForcingReflexiveImages.replacement_rename _ _ _ _ _ _ _ _ r) (lift hUpdate))
    (of_eq (implication_rename _ _ _ _ _ _ r) (lift pPre)) (out.rename r) ?_
  intro l1 Ξ e Bound Base' Sel' Pre' Weak hZ2 move hWeak hPre' hSel' hUpdate' pPre'
  let ρ := e ∘ r
  have carry {F : Formula m} (p : Derives Γ F) : Derives Ξ (F.rename ρ) :=
    of_eq (SourceAlgebra.rename_comp F r e) (move (lift p))
  apply of_eq (SourceAlgebra.rename_comp out r e).symm
  apply of_eq (implication_rename _ _ _ _ _ _ ρ).symm
  exact existential_from_opened hZ2 Reln Dom (ρ w) (ρ z) (ρ a) (ρ A) (ρ B) (ρ C) (ρ f) (ρ j)
    (ρ N) (ρ Child) (ρ b) (ρ c) (ρ d) (ρ t) (ρ L) (ρ S) (ρ D) (ρ E) (ρ G) Weak (ρ (sv 6)) (ρ Parent)
    (ρ A1) (ρ A2) (ρ A3) (ρ K) Bound Base' Sel' Pre' (ρ ∘ images) (ρ ∘ opened) (ρ ∘ cv) (ρ ∘ sv) (e ∘ x) (ρ ∘ raw)
    (of_eq (successor_rename _ _ ρ) (carry hB))
    (of_eq (ForcingRawModalBody.existentialRecord_rename Reln Dom w z a f A B C b c d t L S j Child N (sv 6) Parent
      images opened cv sv ρ) (carry hExist))
    (of_eq (ForcingRawModalBody.data_rename _ _ _ _ _ _ _ _ _ _ _ _ x e) (move hOutputs1))
    (of_eq (ForcingDensityCode.compiled_rename Reln w a A B f j N D ρ) (carry hCompiled))
    (of_eq (substituted_rename _ _ _ _ _ _ _ _ _ ρ) (carry hQuery)) hWeak
    (of_eq (implication_rename _ _ _ _ _ _ ρ) (carry hProof))
    (of_eq (SyntaxNumeralSyntax.numeral_rename _ _ ρ) (carry hA1)) (of_eq (SyntaxNumeralSyntax.numeral_rename _ _ ρ) (carry hA2))
    (of_eq (SyntaxNumeralSyntax.numeral_rename _ _ ρ) (carry hA3)) (of_eq (SyntaxNumeralSyntax.numeral_rename _ _ ρ) (carry hf))
    (of_eq (SyntaxNumeralSyntax.numeral_rename _ _ ρ) (carry hK)) (of_eq (SyntaxNumeralSyntax.numeral_rename _ _ ρ) (carry hj))
    (of_eq (ForcingPreorderCode.rawData_rename Reln w z A1 A2 A3 f raw ρ) (carry hRaw))
    hPre' hSel' hUpdate' pPre'


set_option maxHeartbeats 3000000 in
/-- The original existential density step at every actual compiler and
forcing output of the common runtime. Both witnesses are eliminated internally. -/
theorem existential_step_from_runtime {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (Reln : Formula (k+2)) (Dom : Formula (k+1))
    (w z a f j b Big R S T SOld SNew A1 A2 A3 K Extra A B C h n N : Fin m)
    (raw : Fin 16 → Fin m) (images : Fin 10 → Fin m) (Cr Refl Pre U0 : Fin 2 → Fin m)
    (P : Fin 2 → Fin 3 → Fin m) (rows : Fin 48 → Fin m) (layout : Fin 6 → Fin m)
    (hr : Derives Γ (ForcingRawModalBody.globalModalInput test Reln w z a f j b Big R S T SOld SNew
      A1 A2 A3 K Extra raw images Cr Refl Pre U0 P rows layout))
    (hA : Derives Γ (successor A a)) (hB : Derives Γ (successor B A))
    (hEx : Derives Γ (ForcingCodeStep.existential Reln Dom w z f j a A B C h n N)) :
    Derives Γ (transfer Reln w z a A B f b j T SNew (layout 3) N) := by
  let row : Fin 24 → Fin m := fun i => rows (i.castAdd 24)
  let H := ForcingMemberRows.leafFields row
  let G := layout 3
  let out := transfer Reln w z a A B f b j T SNew G N
  have hGlobal := Derives.conjL hr
  have hRows := Derives.conjL (.conjL hGlobal)
  have hBasis := Derives.conjL hRows
  have hRow := Derives.conjL (.conjR hRows)
  have hFresh := Derives.conjL (.conjR hGlobal)
  have hFreshInput := Derives.conjL hFresh
  have hz := Derives.conjL hFreshInput
  have hc := Derives.conjL (.conjR hFreshInput)
  have hImages := Derives.conjL (.conjR (.conjR hFreshInput))
  have hw := Derives.conjL (.conjL hImages)
  have hBig := Derives.conjL (.conjR (.conjL hImages))
  have hRaw := Derives.conjL (.conjR (.conjR (.conjR hFreshInput)))
  have hVar := Derives.conjL (.conjR hFresh)
  have hTerm := Derives.conjL (.conjR (.conjR hFresh))
  have hPre := Derives.conjR (.conjR (.conjR (.conjR (.conjR (.conjR hFreshInput)))))
  have hAux := Derives.conjR hr
  have hj := Derives.conjL (.conjR hAux)
  have hUpdate := Derives.conjR (.conjR (.conjR hAux))
  have hSel := ForcingRelationWeakening.row_term test Reln w z A1 A2 A3 f b (Cr 0) R S (Refl 0)
    (Pre 0) (U0 0) raw (P 0) row hRow 1
  have hOne := Derives.conjL (.conjR hBasis)
  have hTwo := Derives.conjL (.conjR (.conjR hBasis))
  have hK := Derives.conjL (.conjR (.conjR (.conjR hBasis)))
  have hf := Derives.conjL (.conjR (.conjR (.conjR (.conjR hBasis))))
  have hThree := Derives.conjR (.conjL hGlobal)
  have hExtra := Derives.conjL (.conjR (.conjR hGlobal))
  have hLayout : Derives Γ (ForcingProofContext.layoutData w z b Extra (Pre 0) H layout) :=
    .conjR (.conjR (.conjR hGlobal))
  have hG := Derives.conjR (.conjL (.conjR (.conjR (.conjR hLayout))))
  have pPre := Derives.conjL (ForcingAtomicMono.layout_proofs hZ w z b Extra (Pre 0) H layout hw hz hExtra hLayout)
  refine eliminate_objects hZ 2 (fun r v =>
    (FormulaCodeRecursiveSyntax.singleFields 10 true (r w) (r a) (r z) (v 0) (r n)).conj
      ((ForcingCodeStep.read (r w) (r h) (v 0) (r A) (r f) (v 1)).conj
        (ForcingExistCode.compiled Reln Dom (r w) (r a) (r A) (r B) (r C) (r f) (r j) (v 1) (r N)))) hEx out ?_
  intro l Δ r v hZ1 lift hRecord
  have hEx1 := Derives.conjR (.conjR hRecord)
  apply of_eq (transfer_rename Reln _ _ _ _ _ _ _ _ _ _ _ _ r).symm
  refine intro_transfer hZ1 Reln (r w) (r z) (r a) (r A) (r B) (r f) (r b) (r j) (r T) (r SNew) (r G) (r N) ?_
  intro l1 Δ1 s D E Parent hZ2 move hCompiled hQuery hParent pD
  let e := s ∘ r
  let child := s (v 1)
  let goal := implication test (e w) (e z) (e b) (e G) Parent
  have carry {F : Formula m} (p : Derives Γ F) : Derives Δ1 (F.rename e) :=
    of_eq (SourceAlgebra.rename_comp F r s) (move (lift p))
  have hEx2 := of_eq (ForcingExistCode.compiled_rename Reln Dom _ _ _ _ _ _ _ _ _ s) (move hEx1)
  refine eliminate_objects hZ2 8 (fun q cv =>
    ForcingExistCode.data Reln Dom (q (e w)) (q (e a)) (q (e A)) (q (e B)) (q (e C))
      (q (e f)) (q (e j)) (q child) (q (e N)) cv) (.conjR hEx2) goal ?_
  intro l2 Δ2 q cv hZ3 push hCV
  refine eliminate_objects hZ3 7 (fun u sv =>
    ForcingExistCode.shellData (u (q (e w))) (u (q (e a))) (u (q (e A))) (u (q (e B))) (u (q (e C)))
      (u (q (e f))) (u (cv 2)) (u (cv 3)) (u (cv 4)) (u (cv 5)) (u (cv 6)) (u (cv 7)) (u (q (e N))) sv)
    (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR hCV))))))) (goal.rename q) ?_
  intro l3 Δ3 u sv hZ4 raise hShell
  let dmap := u ∘ q
  let g := dmap ∘ e
  have fromD {F : Formula l1} (p : Derives Δ1 F) : Derives Δ3 (F.rename dmap) :=
    of_eq (SourceAlgebra.rename_comp F q u) (raise (push p))
  have bring {F : Formula m} (p : Derives Γ F) : Derives Δ3 (F.rename g) :=
    of_eq (SourceAlgebra.rename_comp F e dmap) (fromD (carry p))
  have hCtor := Derives.conjL (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR hShell)))))))
  have hFresh := ForcingFreshParentOpening.produce hZ4 (g w) (g z) (g a) (g f) (g A) (g b) (g (Cr 1))
    (g Big) (g (P 1 0)) (g T) (g SNew) (g N) (sv 6) (dmap Parent)
    (.conjI (of_eq (omega_rename _ g) (bring hw)) (.conjI (of_eq (empty_rename _ g) (bring hz))
      (.conjI (of_eq (successor_rename _ _ g) (bring hA)) (.conjI (of_eq (successor_rename _ _ g) (bring hc))
        (.conjI (of_eq (successor_rename _ _ g) (bring hBig))
          (.conjI (of_eq (SyntaxVariableSyntax.code_rename _ _ _ _ g) (bring hVar))
            (.conjI (of_eq (SyntaxTermSyntax.term_rename _ _ _ _ g) (bring hTerm))
              (.conjI hCtor (of_eq (substituted_rename _ _ _ _ _ _ _ _ _ dmap) (fromD hParent))))))))))
  apply of_eq (SourceAlgebra.rename_comp goal q u).symm
  refine eliminate_objects hZ4 10 (fun σ vv =>
    ForcingFreshParentOpening.atImages (σ (g w)) (σ (g z)) (σ (g a)) (σ (g f)) (σ (g A)) (σ (g b))
      (σ (g (Cr 1))) (σ (g Big)) (σ (g (P 1 0))) (σ (g T)) (σ (g SNew)) (σ (g N)) (σ (sv 6)) (σ (dmap Parent)) vv)
    hFresh (goal.rename dmap) ?_
  intro l4 Δ4 σ vv hZ5 extend hAt
  let g1 := σ ∘ g
  refine eliminate_objects hZ5 9 (fun τ uu =>
    let ρ := τ ∘ g1
    ForcingFreshParentOpening.data (ρ w) (ρ z) (ρ a) (ρ f) (ρ A) (ρ b) (ρ (Cr 1)) (ρ Big)
      (ρ (P 1 0)) (ρ T) (ρ SNew) (ρ N) (τ (σ (sv 6))) (τ (σ (dmap Parent))) (τ ∘ vv) uu)
    hAt ((goal.rename dmap).rename σ) ?_
  intro l5 Δ5 τ uu hZ6 finish hOpen
  let last := τ ∘ σ
  let ρ := last ∘ g
  let toD := last ∘ dmap
  let cv1 := last ∘ u ∘ cv
  let sv1 := last ∘ sv
  have fromShell {F : Formula l3} (p : Derives Δ3 F) : Derives Δ5 (F.rename last) :=
    of_eq (SourceAlgebra.rename_comp F σ τ) (finish (extend p))
  have final {F : Formula m} (p : Derives Γ F) : Derives Δ5 (F.rename ρ) :=
    of_eq (SourceAlgebra.rename_comp F g last) (fromShell (bring p))
  have finalD {F : Formula l1} (p : Derives Δ1 F) : Derives Δ5 (F.rename toD) :=
    of_eq (SourceAlgebra.rename_comp F dmap last) (fromShell (fromD p))
  have hCV1 := of_eq (ForcingExistCode.data_rename Reln Dom _ _ _ _ _ _ _ _ _ cv (last ∘ u))
    (of_eq (SourceAlgebra.rename_comp _ u last) (fromShell (raise hCV)))
  have hShell1 := of_eq (ForcingExistCode.shellData_rename _ _ _ _ _ _ _ _ _ _ _ _ _ sv last) (fromShell hShell)
  have hExist := ForcingRawModalBody.existential_at_records hZ6 Reln Dom
    (ρ w) (ρ z) (ρ a) (ρ f) (ρ A) (ρ B) (ρ C) (ρ b) (ρ (Cr 1)) (ρ Big) (ρ (P 1 0)) (ρ T) (ρ SNew)
    (ρ j) (toD child) (ρ N) (sv1 6) (toD Parent) (τ ∘ vv) uu cv1 sv1 hOpen hCV1 hShell1
  apply of_eq (by simp only [SourceAlgebra.rename_comp]; rfl)
  apply of_eq (implication_rename _ _ _ _ _ _ toD).symm
  exact existential_from_runtime_record hZ6 Reln Dom (ρ w) (ρ z) (ρ a) (ρ A) (ρ B) (ρ C) (ρ f) (ρ j)
    (ρ N) (toD child) (ρ b) (ρ (Cr 1)) (ρ Big) (ρ (P 1 0)) (ρ T) (ρ SNew) (toD D) (toD E) (ρ G)
    (toD Parent) (ρ A1) (ρ A2) (ρ A3) (ρ K) (ρ R) (ρ S) (ρ (P 0 1)) (ρ (Pre 0)) (τ ∘ vv) uu cv1 sv1 (ρ ∘ raw)
    (of_eq (successor_rename _ _ ρ) (final hB)) hExist
    (of_eq (ForcingDensityCode.compiled_rename Reln _ _ _ _ _ _ _ _ toD) (finalD hCompiled))
    (of_eq (substituted_rename _ _ _ _ _ _ _ _ _ toD) (finalD hQuery))
    (of_eq (formulaCode_rename _ _ _ _ ρ) (final hG))
    (of_eq (implication_rename _ _ _ _ _ _ toD) (finalD pD))
    (of_eq (SyntaxNumeralSyntax.numeral_rename _ _ ρ) (final hOne)) (of_eq (SyntaxNumeralSyntax.numeral_rename _ _ ρ) (final hTwo))
    (of_eq (SyntaxNumeralSyntax.numeral_rename _ _ ρ) (final hThree)) (of_eq (SyntaxNumeralSyntax.numeral_rename _ _ ρ) (final hf))
    (of_eq (SyntaxNumeralSyntax.numeral_rename _ _ ρ) (final hK)) (of_eq (SyntaxNumeralSyntax.numeral_rename _ _ ρ) (final hj))
    (of_eq (ForcingPreorderCode.rawData_rename Reln w z A1 A2 A3 f raw ρ) (final hRaw))
    (of_eq (substituted_rename _ _ _ _ _ _ _ _ _ ρ) (final hPre))
    (of_eq (SyntaxTermSyntax.term_rename _ _ _ _ ρ) (final hSel))
    (of_eq (ForcingReflexiveImages.replacement_rename _ _ _ _ _ _ _ _ ρ) (final hUpdate))
    (of_eq (implication_rename _ _ _ _ _ _ ρ) (final pPre))


private def existentialInput {k m} (Reln : Formula (k+2)) (Dom : Formula (k+1))
    (w z a f j b Big R S T SOld SNew A1 A2 A3 K Extra A B C h n N : Fin m)
    (raw : Fin 16 → Fin m) (images : Fin 10 → Fin m) (Cr Refl Pre U0 : Fin 2 → Fin m)
    (P : Fin 2 → Fin 3 → Fin m) (rows : Fin 48 → Fin m) (layout : Fin 6 → Fin m) : Formula m :=
  (ForcingRawModalBody.globalModalInput test Reln w z a f j b Big R S T SOld SNew
    A1 A2 A3 K Extra raw images Cr Refl Pre U0 P rows layout).conj
    ((successor A a).conj ((successor B A).conj
      (ForcingCodeStep.existential Reln Dom w z f j a A B C h n N)))

def existentialSentence {k m} (Reln : Formula (k+2)) (Dom : Formula (k+1))
    (w z a f j b Big R S T SOld SNew A1 A2 A3 K Extra A B C h n N : Fin m)
    (raw : Fin 16 → Fin m) (images : Fin 10 → Fin m) (Cr Refl Pre U0 : Fin 2 → Fin m)
    (P : Fin 2 → Fin 3 → Fin m) (rows : Fin 48 → Fin m) (layout : Fin 6 → Fin m) : Source.Sentence :=
  ((existentialInput Reln Dom w z a f j b Big R S T SOld SNew A1 A2 A3 K Extra A B C h n N
    raw images Cr Refl Pre U0 P rows layout).imp (transfer Reln w z a A B f b j T SNew (layout 3) N)).close

theorem existential_kernel_certificate {k m} (Reln : Formula (k+2)) (Dom : Formula (k+1))
    (w z a f j b Big R S T SOld SNew A1 A2 A3 K Extra A B C h n N : Fin m)
    (raw : Fin 16 → Fin m) (images : Fin 10 → Fin m) (Cr Refl Pre U0 : Fin 2 → Fin m)
    (P : Fin 2 → Fin 3 → Fin m) (rows : Fin 48 → Fin m) (layout : Fin 6 → Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
      (Translation.sentence (existentialSentence Reln Dom w z a f j b Big R S T SOld SNew A1 A2 A3 K Extra
        A B C h n N raw images Cr Refl Pre U0 P rows layout)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  let F := existentialInput Reln Dom w z a f j b Big R S T SOld SNew A1 A2 A3 K Extra A B C h n N
    raw images Cr Refl Pre U0 P rows layout
  let Γ := Context.add F (Source.SetLanguage.ZF.at m)
  have hF : Derives Γ F := .hyp (Or.inl rfl)
  have hRest := Derives.conjR hF
  exact existential_step_from_runtime (ZFContext.add (ZFContext.source_ZF m) F) Reln Dom
    w z a f j b Big R S T SOld SNew A1 A2 A3 K Extra A B C h n N raw images Cr Refl Pre U0 P rows layout
    (.conjL hF) (.conjL hRest) (.conjL (.conjR hRest)) (.conjR (.conjR hRest))


end PPAC.Migration.ForcingSourceDensity
