import PPAC.Migration.ForcingProofContext
import PPAC.Migration.ForcingCodeBinary

/-! The conjunction branch of pinned ForcingQuotient.force_mono.
Both actual mixed parent queries produce their own child outputs internally.
The child induction hypotheses are OBJECT universal formulas, not host
callbacks or assumed proofs of the parent. Original projection, chain and
conditional conjunction generate original Root proofs under the SAME G.
This branch does not assert the full formula induction or final Con. -/
namespace PPAC.Migration.ForcingConjunctionMono
open Internal Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)
open FormulaCodeSyntax (formulaCode formulaCode_rename)
open SyntaxMixedFormulaJudgmentSyntax (substituted substituted_rename)
open InternalProofBackground (implication implication_rename)
set_option maxRecDepth 32768
attribute [local irreducible] NaturalRecursionSyntax.matrix

private def point {m} (test : Formula 1) (w z a f b G : Fin m)
    (R S : Fin 2 → Fin m) (n P Q : Fin m) : Formula m :=
  ((substituted w (R 0) (S 0) a f z b n P).conj
    (substituted w (R 1) (S 1) a f z b n Q)).imp
      ((implication test w z b G P).imp (implication test w z b G Q))
private theorem point_rename {m l} (test : Formula 1) (w z a f b G : Fin m)
    (R S : Fin 2 → Fin m) (n P Q : Fin m) (ρ : Fin m → Fin l) :
    (point test w z a f b G R S n P Q).rename ρ =
      point test (ρ w) (ρ z) (ρ a) (ρ f) (ρ b) (ρ G)
        (fun i => ρ (R i)) (fun i => ρ (S i)) (ρ n) (ρ P) (ρ Q) := by
  simp only [point, Formula.rename, substituted_rename, implication_rename]
private def body {m} (test : Formula 1) (w z a f b G : Fin m)
    (R S : Fin 2 → Fin m) (n : Fin m) : Formula (m+2) :=
  point test (old 2 w) (old 2 z) (old 2 a) (old 2 f) (old 2 b) (old 2 G)
    (fun i => old 2 (R i)) (fun i => old 2 (S i)) (old 2 n) (slot 2 0) (slot 2 1)

/-- Conditional Root-proof transport for every two internal query outputs.
The original induction supplies this formula for each child. It retains
arbitrary G so the parent projections can feed those SAME child hypotheses. -/
def transfer {m} (test : Formula 1) (w z a f b G : Fin m)
    (R S : Fin 2 → Fin m) (n : Fin m) : Formula m :=
  OriginalUniversalBlock.allMany 2 (body test w z a f b G R S n)
theorem transfer_rename {m l} (test : Formula 1) (w z a f b G : Fin m)
    (R S : Fin 2 → Fin m) (n : Fin m) (ρ : Fin m → Fin l) :
    (transfer test w z a f b G R S n).rename ρ =
      transfer test (ρ w) (ρ z) (ρ a) (ρ f) (ρ b) (ρ G)
        (fun i => ρ (R i)) (fun i => ρ (S i)) (ρ n) := by
  simp only [transfer, OriginalUniversalBlock.allMany_rename, body, point_rename, lift_old, lift_slot]

theorem apply_transfer {m} {Γ : Context m} (test : Formula 1) (w z a f b G : Fin m)
    (R S : Fin 2 → Fin m) (n P Q : Fin m)
    (hi : Derives Γ (transfer test w z a f b G R S n))
    (hP : Derives Γ (substituted w (R 0) (S 0) a f z b n P))
    (hQ : Derives Γ (substituted w (R 1) (S 1) a f z b n Q))
    (hp : Derives Γ (implication test w z b G P)) :
    Derives Γ (implication test w z b G Q) := by
  have h : Derives Γ (point test w z a f b G R S n P Q) := of_eq
    (by simp only [body, point_rename, assign_old, assign_slot]; rfl)
    (OriginalUniversalBlock.at_many 2 _ (SyntaxAtomSyntax.two P Q) hi)
  exact .impE (.impE h (.conjI hP hQ)) hp

private theorem at_outputs {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1)
    (w z a f b G : Fin m) (R S : Fin 2 → Fin m) (x y P Q X Y U V : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hg : Derives Γ (formulaCode w G z b))
    (htP : Derives Γ (formulaCode w P z b))
    (h0 : Derives Γ (ForcingFormulaDiagram.binaryData 0 w (R 0) (S 0) a f z b x y P X Y))
    (h1 : Derives Γ (ForcingFormulaDiagram.binaryData 0 w (R 1) (S 1) a f z b x y Q U V))
    (hx : Derives Γ (transfer test w z a f b G R S x))
    (hy : Derives Γ (transfer test w z a f b G R S y))
    (hp : Derives Γ (implication test w z b G P)) :
    Derives Γ (implication test w z b G Q) := by
  have htX := SyntaxMixedFormulaJudgment.target_type w (R 0) (S 0) a f z b x X (.conjL (.conjR h0))
  have htY := SyntaxMixedFormulaJudgment.target_type w (R 0) (S 0) a f z b y Y (.conjR (.conjR h0))
  have htU := SyntaxMixedFormulaJudgment.target_type w (R 1) (S 1) a f z b x U (.conjL (.conjR h1))
  have htV := SyntaxMixedFormulaJudgment.target_type w (R 1) (S 1) a f z b y V (.conjR (.conjR h1))
  have px := ForcingRelationGuardProof.project hZ test false w z b X Y P hw hz htX htY htP (.conjL h0)
  have py := ForcingRelationGuardProof.project hZ test true w z b X Y P hw hz htX htY htP (.conjL h0)
  have gx := ForcingRelationGuardProof.chain hZ test w z b G P X hw hz hg htP htX hp px
  have gy := ForcingRelationGuardProof.chain hZ test w z b G P Y hw hz hg htP htY hp py
  have gu := apply_transfer test w z a f b G R S x X U hx (.conjL (.conjR h0)) (.conjL (.conjR h1)) gx
  have gv := apply_transfer test w z a f b G R S y Y V hy (.conjR (.conjR h0)) (.conjR (.conjR h1)) gy
  exact ForcingProofContext.join hZ test w z b G U V Q hw hz hg htU htV (.conjL h1) gu gv

private theorem after_left {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1)
    (w z a f b G : Fin m) (R S : Fin 2 → Fin m) (n x y P Q X Y : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hg : Derives Γ (formulaCode w G z b)) (htP : Derives Γ (formulaCode w P z b))
    (hc : Derives Γ (SyntaxLogicalSyntax.binaryCode 0 w x y n))
    (h0 : Derives Γ (ForcingFormulaDiagram.binaryData 0 w (R 0) (S 0) a f z b x y P X Y))
    (hQ : Derives Γ (substituted w (R 1) (S 1) a f z b n Q))
    (hx : Derives Γ (transfer test w z a f b G R S x))
    (hy : Derives Γ (transfer test w z a f b G R S y))
    (hp : Derives Γ (implication test w z b G P)) :
    Derives Γ (implication test w z b G Q) := by
  let E := ForcingFormulaDiagram.binaryBody 0 w (R 1) (S 1) a f z b x y Q
  let Δ := Context.add E (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 E _ (ForcingFormulaDiagram.binary_output hZ 0 w (R 1) (S 1) a f z b n x y Q hw hc hQ)
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  exact of_eq (implication_rename test w z b G Q (old 2)).symm
    (at_outputs (HornBinderRules.zf_body 2 hZ E) test
      (old 2 w) (old 2 z) (old 2 a) (old 2 f) (old 2 b) (old 2 G)
      (fun i => old 2 (R i)) (fun i => old 2 (S i))
      (old 2 x) (old 2 y) (old 2 P) (old 2 Q) (old 2 X) (old 2 Y) (slot 2 0) (slot 2 1)
      (of_eq (omega_rename w (old 2)) (HornBinderRules.under_body 2 hw E))
      (of_eq (empty_rename z (old 2)) (HornBinderRules.under_body 2 hz E))
      (of_eq (formulaCode_rename w G z b (old 2)) (HornBinderRules.under_body 2 hg E))
      (of_eq (formulaCode_rename w P z b (old 2)) (HornBinderRules.under_body 2 htP E))
      (of_eq (ForcingFormulaDiagram.binaryData_rename 0 w (R 0) (S 0) a f z b x y P X Y (old 2)) (HornBinderRules.under_body 2 h0 E)) hE
      (of_eq (transfer_rename test w z a f b G R S x (old 2)) (HornBinderRules.under_body 2 hx E))
      (of_eq (transfer_rename test w z a f b G R S y (old 2)) (HornBinderRules.under_body 2 hy E))
      (of_eq (implication_rename test w z b G P (old 2)) (HornBinderRules.under_body 2 hp E)))

/-- Consume BOTH actual whole-parent queries. Their FOUR child outputs are
generated/eliminated by the existing mixed-query rule, never supplied. -/
theorem derive {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1)
    (w z a f b G : Fin m) (R S : Fin 2 → Fin m) (n x y P Q : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hg : Derives Γ (formulaCode w G z b))
    (hc : Derives Γ (SyntaxLogicalSyntax.binaryCode 0 w x y n))
    (hP : Derives Γ (substituted w (R 0) (S 0) a f z b n P))
    (hQ : Derives Γ (substituted w (R 1) (S 1) a f z b n Q))
    (hx : Derives Γ (transfer test w z a f b G R S x))
    (hy : Derives Γ (transfer test w z a f b G R S y))
    (hp : Derives Γ (implication test w z b G P)) :
    Derives Γ (implication test w z b G Q) := by
  let E := ForcingFormulaDiagram.binaryBody 0 w (R 0) (S 0) a f z b x y P
  let Δ := Context.add E (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 E _ (ForcingFormulaDiagram.binary_output hZ 0 w (R 0) (S 0) a f z b n x y P hw hc hP)
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  exact of_eq (implication_rename test w z b G Q (old 2)).symm
    (after_left (HornBinderRules.zf_body 2 hZ E) test
      (old 2 w) (old 2 z) (old 2 a) (old 2 f) (old 2 b) (old 2 G)
      (fun i => old 2 (R i)) (fun i => old 2 (S i))
      (old 2 n) (old 2 x) (old 2 y) (old 2 P) (old 2 Q) (slot 2 0) (slot 2 1)
      (of_eq (omega_rename w (old 2)) (HornBinderRules.under_body 2 hw E))
      (of_eq (empty_rename z (old 2)) (HornBinderRules.under_body 2 hz E))
      (of_eq (formulaCode_rename w G z b (old 2)) (HornBinderRules.under_body 2 hg E))
      (of_eq (formulaCode_rename w P z b (old 2)) (HornBinderRules.under_body 2
        (SyntaxMixedFormulaJudgment.target_type w (R 0) (S 0) a f z b n P hP) E))
      (of_eq (SyntaxLogicalSyntax.binaryCode_rename 0 w x y n (old 2)) (HornBinderRules.under_body 2 hc E)) hE
      (of_eq (substituted_rename w (R 1) (S 1) a f z b n Q (old 2)) (HornBinderRules.under_body 2 hQ E))
      (of_eq (transfer_rename test w z a f b G R S x (old 2)) (HornBinderRules.under_body 2 hx E))
      (of_eq (transfer_rename test w z a f b G R S y (old 2)) (HornBinderRules.under_body 2 hy E))
      (of_eq (implication_rename test w z b G P (old 2)) (HornBinderRules.under_body 2 hp E)))

theorem conjunction {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1)
    (w z a f b G : Fin m) (R S : Fin 2 → Fin m) (n x y : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hg : Derives Γ (formulaCode w G z b))
    (hc : Derives Γ (SyntaxLogicalSyntax.binaryCode 0 w x y n))
    (hx : Derives Γ (transfer test w z a f b G R S x))
    (hy : Derives Γ (transfer test w z a f b G R S y)) :
    Derives Γ (transfer test w z a f b G R S n) := by
  apply OriginalUniversalBlock.intro_many 2
  apply Derives.impI
  apply Derives.impI
  let B := (substituted (old 2 w) (old 2 (R 0)) (old 2 (S 0)) (old 2 a) (old 2 f) (old 2 z) (old 2 b) (old 2 n) (slot 2 0)).conj
    (substituted (old 2 w) (old 2 (R 1)) (old 2 (S 1)) (old 2 a) (old 2 f) (old 2 z) (old 2 b) (old 2 n) (slot 2 1))
  let E := implication test (old 2 w) (old 2 z) (old 2 b) (old 2 G) (slot 2 0)
  let Δ := Context.add E (Context.add B (raisedContext 2 Γ))
  have hB : Derives Δ B := .hyp (Or.inr (Or.inl rfl))
  exact derive (ZFContext.add (HornBinderRules.zf_body 2 hZ B) E) test
    (old 2 w) (old 2 z) (old 2 a) (old 2 f) (old 2 b) (old 2 G)
    (fun i => old 2 (R i)) (fun i => old 2 (S i))
    (old 2 n) (old 2 x) (old 2 y) (slot 2 0) (slot 2 1)
    (.weaken (fun _ h => Or.inr h) (of_eq (omega_rename w (old 2)) (HornBinderRules.under_body 2 hw B)))
    (.weaken (fun _ h => Or.inr h) (of_eq (empty_rename z (old 2)) (HornBinderRules.under_body 2 hz B)))
    (.weaken (fun _ h => Or.inr h) (of_eq (formulaCode_rename w G z b (old 2)) (HornBinderRules.under_body 2 hg B)))
    (.weaken (fun _ h => Or.inr h) (of_eq (SyntaxLogicalSyntax.binaryCode_rename 0 w x y n (old 2)) (HornBinderRules.under_body 2 hc B)))
    (.conjL hB) (.conjR hB)
    (.weaken (fun _ h => Or.inr h) (of_eq (transfer_rename test w z a f b G R S x (old 2)) (HornBinderRules.under_body 2 hx B)))
    (.weaken (fun _ h => Or.inr h) (of_eq (transfer_rename test w z a f b G R S y (old 2)) (HornBinderRules.under_body 2 hy B)))
    (.hyp (Or.inl rfl))

/-- Actual source-compiler consumer for the original conjunction case.
The whole parent and both children are independently compiled original
records. The parent AND constructor is obtained from that real computation,
not an expected logical-output premise. -/
theorem source_step {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1)
    (Reln : Source.Formula (k+2)) (Dom : Source.Formula (k+1))
    (w z f j a A B C n c x y cx cy b G : Fin m) (R S : Fin 2 → Fin m)
    (hz : Derives Γ (empty z)) (hg : Derives Γ (formulaCode w G z b))
    (hi : Derives Γ (ForcingCodeBinary.input 0 Reln Dom w z f j a A B C n c x y cx cy))
    (hx : Derives Γ (transfer test w z a f b G R S cx))
    (hy : Derives Γ (transfer test w z a f b G R S cy)) :
    Derives Γ (transfer test w z a f b G R S c) := by
  have hc := ForcingCodeBinary.binary hZ 0 Reln Dom w z f j a A B C n c x y cx cy
    (.conjL hi) (.conjL (.conjR hi)) (.conjL (.conjR (.conjR hi)))
    (.conjL (.conjR (.conjR (.conjR hi)))) (.conjL (.conjR (.conjR (.conjR (.conjR hi)))))
    (.conjL (.conjR (.conjR (.conjR (.conjR (.conjR hi))))))
    (.conjL (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR hi)))))))
    (.conjL (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR hi))))))))
    (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR hi))))))))
  exact conjunction hZ test w z a f b G R S c cx cy (.conjL hi) hz hg (.conjL hc) hx hy

def sentence {k m} (target : Bool) (Reln : Source.Formula (k+2)) (Dom : Source.Formula (k+1))
    (w z f j a A B C n c x y cx cy b G : Fin m) (R S : Fin 2 → Fin m) : Source.Sentence :=
  ((empty z).imp ((formulaCode w G z b).imp
    ((ForcingCodeBinary.input 0 Reln Dom w z f j a A B C n c x y cx cy).imp
      ((transfer (OriginalAxiomCodeTest.test target) w z a f b G R S cx).imp
        ((transfer (OriginalAxiomCodeTest.test target) w z a f b G R S cy).imp
          (transfer (OriginalAxiomCodeTest.test target) w z a f b G R S c)))))).close

theorem kernel_certificate {k m} (target : Bool) (Reln : Source.Formula (k+2)) (Dom : Source.Formula (k+1))
    (w z f j a A B C n c x y cx cy b G : Fin m) (R S : Fin 2 → Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
      (Translation.sentence (sentence target Reln Dom w z f j a A B C n c x y cx cy b G R S)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  exact source_step (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.add
    (ZFContext.add (ZFContext.source_ZF m) _) _) _) _) _) (OriginalAxiomCodeTest.test target)
    Reln Dom w z f j a A B C n c x y cx cy b G R S
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    (.hyp (Or.inr (Or.inr (Or.inl rfl))))
    (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

end PPAC.Migration.ForcingConjunctionMono
