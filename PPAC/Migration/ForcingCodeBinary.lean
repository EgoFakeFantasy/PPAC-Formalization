import PPAC.Migration.ForcingCodeUnique
import PPAC.Migration.Internal.StructuralListTraceOrder
import PPAC.Migration.InternalProofTemplates

/-! The actual four binary computation laws of the pinned forcing compiler.
Consume genuine independently specified parent and child compilations, not a
supplied local binary answer or history. Reuse existing branch selectors,
original internal recursion, bounded reads and independent output uniqueness.
This is a code computation law, not forcing MP or semantic soundness. -/
namespace PPAC.Migration.ForcingCodeBinary
open Internal Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)
set_option maxRecDepth 16384
attribute [local irreducible] NaturalRecursionSyntax.matrix

private theorem read_subst {m} {Γ : Context m} (w g x a f Q y : Fin m)
    (he : Derives Γ (.equal x y)) (hr : Derives Γ (ForcingCodeStep.read w g x a f Q)) : Derives Γ (ForcingCodeStep.read w g y a f Q) := by
  let P := ForcingCodeStep.read w.castSucc g.castSucc (Fin.last m) a.castSucc f.castSucc Q.castSucc
  exact of_eq (by simp only [P, Formula.instantiate, ForcingCodeStep.read_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
    (.eqSubst P he (of_eq (by simp only [P, Formula.instantiate, ForcingCodeStep.read_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hr))

private theorem at_data {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Fin 4)
    (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j a A B C g n Q x y N M u v U V : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (.mem n w))
    (hc : Derives Γ (SyntaxLogicalSyntax.binaryCode kind w x y n))
    (hg : Derives Γ (ForcingCodeRecursion.graph R H w z f j g n))
    (hN : Derives Γ (ForcingCodeRecursion.compiled R H w z f j a x N))
    (hM : Derives Γ (ForcingCodeRecursion.compiled R H w z f j a y M))
    (hd : Derives Γ (ForcingCodeStep.binaryData kind R w z f j a A B C g n Q u v U V)) :
    Derives Γ (ForcingLogicalCode.binary kind R w a A f j N M Q) := by
  have he := SyntaxLogicalFields.binary_fields hZ kind w u v x y n hw (.conjL (.conjL hd)) hc
  have hb := SyntaxLogicalFields.binary_bounds hZ kind w x y n hw hc
  have ho := NaturalOrderBasic.ordinal hZ w n hw hn
  have hrU := read_subst w g u a f U x (.conjL he) (.conjL (.conjR hd))
  have hrV := read_subst w g v a f V y (.conjR he) (.conjL (.conjR (.conjR hd)))
  have hU := ForcingCodeRecursion.read_to_compiled hZ R H w z f j g n a x U ho (.conjL hb) hg hrU
  have hV := ForcingCodeRecursion.read_to_compiled hZ R H w z f j g n a y V ho (.conjR hb) hg hrV
  have eU := ForcingCodeUnique.unique hZ R H w z f j a x U N hw
    (StructuralListTraceOrder.member_member hZ w x n hw hn (.conjL hb)) hU hN
  have eV := ForcingCodeUnique.unique hZ R H w z f j a y V M hw
    (StructuralListTraceOrder.member_member hZ w y n hw hn (.conjR hb)) hV hM
  let P := ForcingLogicalCode.binary kind R w.castSucc a.castSucc A.castSucc f.castSucc j.castSucc (Fin.last m) V.castSucc Q.castSucc
  have h0 : Derives Γ (ForcingLogicalCode.binary kind R w a A f j N V Q) :=
    of_eq (by simp only [P, Formula.instantiate, ForcingLogicalCode.binary_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
      (.eqSubst P eU (of_eq (by simp only [P, Formula.instantiate, ForcingLogicalCode.binary_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjR (.conjR (.conjR hd)))))
  let S := ForcingLogicalCode.binary kind R w.castSucc a.castSucc A.castSucc f.castSucc j.castSucc N.castSucc (Fin.last m) Q.castSucc
  exact of_eq (by simp only [S, Formula.instantiate, ForcingLogicalCode.binary_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
    (.eqSubst S eV (of_eq (by simp only [S, Formula.instantiate, ForcingLogicalCode.binary_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) h0))

private theorem at_case {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Fin 4)
    (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j a A B C g n Q x y N M : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (.mem n w))
    (hc : Derives Γ (SyntaxLogicalSyntax.binaryCode kind w x y n))
    (hg : Derives Γ (ForcingCodeRecursion.graph R H w z f j g n))
    (hN : Derives Γ (ForcingCodeRecursion.compiled R H w z f j a x N))
    (hM : Derives Γ (ForcingCodeRecursion.compiled R H w z f j a y M))
    (hd : Derives Γ (ForcingCodeStep.binary kind R w z f j a A B C g n Q)) :
    Derives Γ (ForcingLogicalCode.binary kind R w a A f j N M Q) := by
  let E := ForcingCodeStep.binaryData kind R (old 4 w) (old 4 z) (old 4 f) (old 4 j) (old 4 a) (old 4 A) (old 4 B) (old 4 C)
    (old 4 g) (old 4 n) (old 4 Q) (slot 4 0) (slot 4 1) (slot 4 2) (slot 4 3)
  let Δ := Context.add E (raisedContext 4 Γ)
  apply HornBinderRules.eliminate_many 4 E _ hd
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  exact of_eq (ForcingLogicalCode.binary_rename kind R w a A f j N M Q (old 4)).symm
    (at_data (HornBinderRules.zf_body 4 hZ E) kind R H (old 4 w) (old 4 z) (old 4 f) (old 4 j) (old 4 a) (old 4 A) (old 4 B) (old 4 C)
      (old 4 g) (old 4 n) (old 4 Q) (old 4 x) (old 4 y) (old 4 N) (old 4 M) (slot 4 0) (slot 4 1) (slot 4 2) (slot 4 3)
      (of_eq (omega_rename w (old 4)) (HornBinderRules.under_body 4 hw E)) (HornBinderRules.under_body 4 hn E)
      (of_eq (SyntaxLogicalSyntax.binaryCode_rename kind w x y n (old 4)) (HornBinderRules.under_body 4 hc E))
      (of_eq (ForcingCodeRecursion.graph_rename R H w z f j g n (old 4)) (HornBinderRules.under_body 4 hg E))
      (of_eq (ForcingCodeRecursion.compiled_rename R H w z f j a x N (old 4)) (HornBinderRules.under_body 4 hN E))
      (of_eq (ForcingCodeRecursion.compiled_rename R H w z f j a y M (old 4)) (HornBinderRules.under_body 4 hM E)) hE)

private theorem at_graph {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Fin 4)
    (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j a A B C g n Q x y N M : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (.mem n w))
    (hA : Derives Γ (successor A a)) (hB : Derives Γ (successor B A)) (hC : Derives Γ (successor C B))
    (hc : Derives Γ (SyntaxLogicalSyntax.binaryCode kind w x y n))
    (hg : Derives Γ (ForcingCodeRecursion.graph R H w z f j g n))
    (hQ : Derives Γ (ForcingCodeRecursion.compiled R H w z f j a n Q))
    (hN : Derives Γ (ForcingCodeRecursion.compiled R H w z f j a x N))
    (hM : Derives Γ (ForcingCodeRecursion.compiled R H w z f j a y M)) :
    Derives Γ (ForcingLogicalCode.binary kind R w a A f j N M Q) := by
  have hs := ForcingCodeUnique.compiled_step hZ R H w z f j n g a A B C Q hw (NaturalOrderBasic.ordinal hZ w n hw hn) hA hB hC hg hQ
  exact at_case hZ kind R H w z f j a A B C g n Q x y N M hw hn hc hg hN hM
    (ForcingCodeStepUnique.select_binary hZ kind R H w z f j a A B C g n Q x y hw hc (.conjR hs))

/-- The parent output is the exact source-selected binary forcing expression
on ANY independently compiled child outputs. No history or local answer premise. -/
theorem binary {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Fin 4)
    (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j a A B C n Q x y N M : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (.mem n w))
    (hA : Derives Γ (successor A a)) (hB : Derives Γ (successor B A)) (hC : Derives Γ (successor C B))
    (hc : Derives Γ (SyntaxLogicalSyntax.binaryCode kind w x y n))
    (hQ : Derives Γ (ForcingCodeRecursion.compiled R H w z f j a n Q))
    (hN : Derives Γ (ForcingCodeRecursion.compiled R H w z f j a x N))
    (hM : Derives Γ (ForcingCodeRecursion.compiled R H w z f j a y M)) :
    Derives Γ (ForcingLogicalCode.binary kind R w a A f j N M Q) := by
  let E := ForcingCodeRecursion.graph R H w.castSucc z.castSucc f.castSucc j.castSucc (Fin.last m) n.castSucc
  let Δ := Context.add E (Context.image Formula.raise Γ)
  apply Derives.exE (p := E) (ForcingCodeRecursion.exists_graph hZ R H w z f j n (NaturalOrderBasic.ordinal hZ w n hw hn))
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  exact of_eq (ForcingLogicalCode.binary_rename kind R w a A f j N M Q Fin.castSucc).symm
    (at_graph (ZFContext.under hZ E) kind R H w.castSucc z.castSucc f.castSucc j.castSucc a.castSucc A.castSucc B.castSucc C.castSucc
      (Fin.last m) n.castSucc Q.castSucc x.castSucc y.castSucc N.castSucc M.castSucc
      (of_eq (omega_rename w Fin.castSucc) (under hw E)) (under hn E)
      (of_eq (successor_rename A a Fin.castSucc) (under hA E)) (of_eq (successor_rename B A Fin.castSucc) (under hB E))
      (of_eq (successor_rename C B Fin.castSucc) (under hC E))
      (of_eq (SyntaxLogicalSyntax.binaryCode_rename kind w x y n Fin.castSucc) (under hc E)) hE
      (of_eq (ForcingCodeRecursion.compiled_rename R H w z f j a n Q Fin.castSucc) (under hQ E))
      (of_eq (ForcingCodeRecursion.compiled_rename R H w z f j a x N Fin.castSucc) (under hN E))
      (of_eq (ForcingCodeRecursion.compiled_rename R H w z f j a y M Fin.castSucc) (under hM E)))

def input {k m} (kind : Fin 4) (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j a A B C n Q x y N M : Fin m) : Formula m :=
  (omega w).conj ((Formula.mem n w).conj ((successor A a).conj ((successor B A).conj ((successor C B).conj
    ((SyntaxLogicalSyntax.binaryCode kind w x y n).conj ((ForcingCodeRecursion.compiled R H w z f j a n Q).conj
      ((ForcingCodeRecursion.compiled R H w z f j a x N).conj (ForcingCodeRecursion.compiled R H w z f j a y M))))))))
private theorem from_input {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Fin 4)
    (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j a A B C n Q x y N M : Fin m)
    (hI : Derives Γ (input kind R H w z f j a A B C n Q x y N M)) :
    Derives Γ (ForcingLogicalCode.binary kind R w a A f j N M Q) := by
  exact binary hZ kind R H w z f j a A B C n Q x y N M
    (.conjL hI) (.conjL (.conjR hI)) (.conjL (.conjR (.conjR hI))) (.conjL (.conjR (.conjR (.conjR hI))))
    (.conjL (.conjR (.conjR (.conjR (.conjR hI))))) (.conjL (.conjR (.conjR (.conjR (.conjR (.conjR hI))))))
    (.conjL (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR hI)))))))
    (.conjL (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR hI))))))))
    (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR hI))))))))

def sentence {k m} (kind : Fin 4) (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j a A B C n Q x y N M : Fin m) : Source.Sentence :=
  ((input kind R H w z f j a A B C n Q x y N M).imp (ForcingLogicalCode.binary kind R w a A f j N M Q)).close

theorem kernel_certificate {k m} (kind : Fin 4) (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j a A B C n Q x y N M : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (sentence kind R H w z f j a A B C n Q x y N M)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  let E := input kind R H w z f j a A B C n Q x y N M
  let Γ := Context.add E (Source.SetLanguage.ZF.at m)
  have hE : Derives Γ E := .hyp (Or.inl rfl)
  exact from_input (ZFContext.add (ZFContext.source_ZF m) E) kind R H w z f j a A B C n Q x y N M hE

/-- An actual closed-source conjunction compilation now feeds the accepted
original proof constructors in BOTH directions, with no local AND oracle. -/
theorem conjunction_iff {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1)
    (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j A B C n Q x y N M : Fin m)
    (hz : Derives Γ (empty z)) (hI : Derives Γ (input 0 R H w z f j z A B C n Q x y N M)) :
    Derives Γ ((InternalProofConjunction.proved test w z f Q).iff
      ((InternalProofConjunction.proved test w z f N).conj (InternalProofConjunction.proved test w z f M))) :=
  InternalProofTemplates.compiled_iff hZ test R w z A f j N M Q (.conjL hI) hz
    (from_input hZ 0 R H w z f j z A B C n Q x y N M hI)

def conjunctionSentence {k m} (target : Bool) (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j A B C n Q x y N M : Fin m) : Source.Sentence :=
  ((empty z).imp ((input 0 R H w z f j z A B C n Q x y N M).imp
    ((InternalProofConjunction.proved (OriginalAxiomCodeTest.test target) w z f Q).iff
      ((InternalProofConjunction.proved (OriginalAxiomCodeTest.test target) w z f N).conj
        (InternalProofConjunction.proved (OriginalAxiomCodeTest.test target) w z f M))))).close

theorem conjunction_kernel_certificate {k m} (target : Bool) (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j A B C n Q x y N M : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (conjunctionSentence target R H w z f j A B C n Q x y N M)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  exact conjunction_iff (ZFContext.add (ZFContext.add (ZFContext.source_ZF m) _) _) (OriginalAxiomCodeTest.test target)
    R H w z f j A B C n Q x y N M (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

end PPAC.Migration.ForcingCodeBinary
