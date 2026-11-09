import PPAC.Migration.InternalProofQuantifier
import PPAC.Migration.ForcingNegCode

/-! Actual full negative compilation -> real opened forall -> original rule20
instance proof under a common background. No bare forall replacement is used:
the input is the original complete negative compiler including both guards
and condition rebinding. Their remaining commutation/forcing MP is unproved. -/
namespace PPAC.Migration.ForcingNegProof
open Internal Source SourceAlgebra SourceLogic OmegaSyntax
open SyntaxRenameQuerySyntax (of_eq)
open FormulaCodeSyntax (formulaCode formulaCode_rename)
open InternalProofConjunction (proved proved_rename)
set_option maxRecDepth 16384
attribute [local irreducible] NaturalRecursionSyntax.matrix

/-- The real typed raw body, same actual pointwise opening/lift and generated
G→instance proof. All bodies, environments and outputs are object witnesses. -/
def result {m} (test : Formula 1) (w z a A f T Q V term G : Fin m) : Formula m := .ex
  ((SyntaxLogicalSyntax.singleCode 9 w.castSucc (Fin.last m) Q.castSucc).conj
    ((formulaCode w.castSucc (Fin.last m) A.castSucc f.castSucc).conj
      (InternalProofQuantifier.guardedOpenedInstance test w.castSucc z.castSucc a.castSucc f.castSucc T.castSucc (Fin.last m) V.castSucc term.castSucc G.castSucc)))

theorem result_rename {m l} (test : Formula 1) (w z a A f T Q V term G : Fin m) (r : Fin m → Fin l) :
    (result test w z a A f T Q V term G).rename r = result test (r w) (r z) (r a) (r A) (r f) (r T) (r Q) (r V) (r term) (r G) := by
  simp only [result, Formula.rename, SyntaxLogicalSyntax.singleCode_rename, formulaCode_rename,
    InternalProofQuantifier.guardedOpenedInstance_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

/-- Consume the ACTUAL complete raw negative compilation and ACTUAL opening.
The parent proof is G→opened-negative, so G is not assumed true or proved.
Generate all native instance/proof witnesses inside the original object theory. -/
theorem derive {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1) (R : Source.Formula (k+2))
    (w z a A f j N Q T V term G I : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hc : Derives Γ (ForcingNegCode.compiled R w a A f j N Q))
    (ho : Derives Γ (ForcingPointwiseCode.opened w z a f T Q V))
    (ht : Derives Γ (SyntaxTermSyntax.term w z T term)) (hG : Derives Γ (formulaCode w G z T))
    (hI : Derives Γ (SyntaxNodeSyntax.constructor 2 7 w (SyntaxAtomSyntax.two G V) I))
    (hp : Derives Γ (proved test w z T I)) : Derives Γ (result test w z a A f T Q V term G) := by
  let E := (SyntaxLogicalSyntax.singleCode 9 w.castSucc (Fin.last m) Q.castSucc).conj
    (formulaCode w.castSucc (Fin.last m) A.castSucc f.castSucc)
  let Δ := Context.add E (Context.image Formula.raise Γ)
  apply Derives.exE (p := E) (ForcingNegCode.body_output R w a A f j N Q hc)
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have hproof := InternalProofQuantifier.guarded_opened_instance (ZFContext.under hZ E) test
    w.castSucc z.castSucc a.castSucc f.castSucc T.castSucc Q.castSucc (Fin.last m) V.castSucc term.castSucc G.castSucc I.castSucc
    (of_eq (omega_rename w Fin.castSucc) (under hw E)) (of_eq (empty_rename z Fin.castSucc) (under hz E)) (.conjL hE)
    (of_eq (ForcingPointwiseCode.opened_rename w z a f T Q V Fin.castSucc) (under ho E))
    (of_eq (SyntaxTermSyntax.term_rename w z T term Fin.castSucc) (under ht E))
    (of_eq (formulaCode_rename w G z T Fin.castSucc) (under hG E))
    (of_eq (by simp only [Formula.raise, SyntaxNodeSyntax.constructor_rename, SyntaxAtomSyntax.two_map]) (under hI E))
    (of_eq (proved_rename test w z T I Fin.castSucc) (under hp E))
  have hout : Derives Δ (result test w.castSucc z.castSucc a.castSucc A.castSucc f.castSucc T.castSucc Q.castSucc V.castSucc term.castSucc G.castSucc) := by
    apply Derives.exI (Fin.last m)
    exact of_eq (by simp only [Formula.instantiate, Formula.rename, SyntaxLogicalSyntax.singleCode_rename, formulaCode_rename,
      InternalProofQuantifier.guardedOpenedInstance_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
      (.conjI (.conjL hE) (.conjI (.conjR hE) hproof))
  exact of_eq (result_rename test w z a A f T Q V term G Fin.castSucc).symm hout

def input {k m} (test : Formula 1) (R : Source.Formula (k+2)) (w z a A f j N Q T V term G I : Fin m) : Formula m :=
  (omega w).conj ((empty z).conj ((ForcingNegCode.compiled R w a A f j N Q).conj
    ((ForcingPointwiseCode.opened w z a f T Q V).conj ((SyntaxTermSyntax.term w z T term).conj
      ((formulaCode w G z T).conj ((SyntaxNodeSyntax.constructor 2 7 w (SyntaxAtomSyntax.two G V) I).conj (proved test w z T I)))))))

def sentence {k m} (target : Bool) (R : Source.Formula (k+2)) (w z a A f j N Q T V term G I : Fin m) : Source.Sentence :=
  ((input (OriginalAxiomCodeTest.test target) R w z a A f j N Q T V term G I).imp
    (result (OriginalAxiomCodeTest.test target) w z a A f T Q V term G)).close

theorem kernel_certificate {k m} (target : Bool) (R : Source.Formula (k+2)) (w z a A f j N Q T V term G I : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (sentence target R w z a A f j N Q T V term G I)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  let E := input (OriginalAxiomCodeTest.test target) R w z a A f j N Q T V term G I
  let Γ := Context.add E (Source.SetLanguage.ZF.at m)
  have h : Derives Γ E := .hyp (Or.inl rfl)
  exact derive (ZFContext.add (ZFContext.source_ZF m) E) (OriginalAxiomCodeTest.test target) R w z a A f j N Q T V term G I
    (.conjL h)
    (.conjL (.conjR h))
    (.conjL (.conjR (.conjR h)))
    (.conjL (.conjR (.conjR (.conjR h))))
    (.conjL (.conjR (.conjR (.conjR (.conjR h)))))
    (.conjL (.conjR (.conjR (.conjR (.conjR (.conjR h))))))
    (.conjL (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR h)))))))
    (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR h)))))))

end PPAC.Migration.ForcingNegProof
