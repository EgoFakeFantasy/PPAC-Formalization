import PPAC.Migration.ProjectCompilerQuotation
import PPAC.Migration.Internal.SyntaxUnaryIterationLaws

/-! The ORIGINAL whole forall closure, compared with original native quotation.
The existing internal iteration is unchanged. Count and syntax index an
external proof scheme; the candidate count/code values remain object variables.
Uniform nonstandard-body/count forcing and final Con are not asserted here. -/
namespace PPAC.Migration.SchemaClosureQuotation
open Internal Source SourceAlgebra SourceLogic OmegaSyntax
open SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket (Tree)
attribute [local irreducible] NaturalRecursionSyntax.matrix
attribute [local implicit_reducible] YesMetaZFC.SetTheory.signature

def wrapped : Nat → Tree → Tree
  | 0, input => input
  | n+1, input => .node 9 [wrapped n input]

theorem construct {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (count : Nat) (input : Tree) (w a n y : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (SyntaxNumeralSyntax.numeral count n))
    (ha : Derives Γ (OriginalTreeQuotationSyntax.tree input w a))
    (hy : Derives Γ (OriginalTreeQuotationSyntax.tree (wrapped count input) w y)) :
    Derives Γ (SyntaxUnaryIterationSyntax.forallClosure w a n y) := by
  induction count generalizing m with
  | zero =>
    have he := OriginalTreeQuotationUnique.tree_unique hZ input w a y hw ha hy
    have hv := SyntaxUnaryIterationLaws.zero_value hZ 9 w a n hw (OriginalTreeQuotationProperties.tree_range hZ input w a hw ha) hn
    exact SyntaxUnaryIterationSyntax.output_subst 9 w a n a y he hv
  | succ count ih =>
    let N := (SyntaxNumeralSyntax.numeral count (Fin.last m)).conj (successor n.castSucc (Fin.last m))
    let Ξ := Context.add N (Context.image Formula.raise Γ)
    apply SyntaxNumeralSyntax.eliminate_succ count n _ hn
    have hN : Derives Ξ N := .hyp (Or.inl rfl)
    have hZ1 := ZFContext.under hZ N
    have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw N)
    let X := (Source.Formula.mem (Fin.last (m+1)) w.castSucc.castSucc).conj
      (OriginalTreeQuotationSyntax.tree (wrapped count input) w.castSucc.castSucc (Fin.last (m+1)))
    let Δ := Context.add X (Context.image Formula.raise Ξ)
    apply Derives.exE (p := X) (OriginalTreeQuotationExistence.tree_exists hZ1 (wrapped count input) w.castSucc hw1)
    have hX : Derives Δ X := .hyp (Or.inl rfl)
    have hZ2 := ZFContext.under hZ1 X
    have hw2 := of_eq (omega_rename w.castSucc Fin.castSucc) (under hw1 X)
    have hn2 := of_eq (SyntaxNumeralSyntax.numeral_rename count (Fin.last m) Fin.castSucc) (under (.conjL hN) X)
    have hs2 := of_eq (successor_rename n.castSucc (Fin.last m) Fin.castSucc) (under (.conjR hN) X)
    have ha2 : Derives Δ (OriginalTreeQuotationSyntax.tree input w.castSucc.castSucc a.castSucc.castSucc) :=
      of_eq (by simp only [Formula.raise,OriginalTreeQuotationSyntax.tree_rename]) (under (under ha N) X)
    have hy2 : Derives Δ (OriginalTreeQuotationSyntax.tree (.node 9 [wrapped count input]) w.castSucc.castSucc y.castSucc.castSucc) :=
      of_eq (by simp only [Formula.raise,OriginalTreeQuotationSyntax.tree_rename,wrapped]) (under (under hy N) X)
    have hi := ih hZ2 w.castSucc.castSucc a.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) hw2 hn2 ha2 (.conjR hX)
    have hc := OriginalQuotationNodeFields.tree_to_constructor hZ2 9 [wrapped count input] w.castSucc.castSucc y.castSucc.castSucc
      (fun _ => Fin.last (m+1)) hw2 (.conjI (.conjR hX) (.eqRefl w.castSucc.castSucc)) hy2
    have hv := SyntaxUnaryIterationLaws.successor_backward hZ2 9 w.castSucc.castSucc a.castSucc.castSucc
      (Fin.last m).castSucc n.castSucc.castSucc (Fin.last (m+1)) y.castSucc.castSucc hw2
        (OriginalTreeQuotationProperties.tree_range hZ2 input w.castSucc.castSucc a.castSucc.castSucc hw2 ha2)
        (SyntaxNumerals.range hZ2 count w.castSucc.castSucc (Fin.last m).castSucc hw2 hn2) hs2 hi hc
    exact of_eq (by simp only [Formula.raise,SyntaxUnaryIterationSyntax.forallClosure_rename]; rfl) hv

theorem tree_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (count : Nat) (input : Tree) (w a n y : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (SyntaxNumeralSyntax.numeral count n))
    (ha : Derives Γ (OriginalTreeQuotationSyntax.tree input w a)) :
    Derives Γ ((SyntaxUnaryIterationSyntax.forallClosure w a n y).iff
      (OriginalTreeQuotationSyntax.tree (wrapped count input) w y)) := by
  have he := OriginalTreeQuotationExistence.tree_exists hZ (wrapped count input) w hw
  apply Derives.conjI
  · apply Derives.impI
    let E := SyntaxUnaryIterationSyntax.forallClosure w a n y
    let Ξ := Context.add E Γ
    let P := (Source.Formula.mem (Fin.last m) w.castSucc).conj
      (OriginalTreeQuotationSyntax.tree (wrapped count input) w.castSucc (Fin.last m))
    let Δ := Context.add P (Context.image Formula.raise Ξ)
    apply Derives.exE (p := P) (add he E)
    have hP : Derives Δ P := .hyp (Or.inl rfl)
    have hZ1 := ZFContext.under (ZFContext.add hZ E) P
    have hw1 := of_eq (omega_rename w Fin.castSucc) (under (add hw E) P)
    have hn1 := of_eq (SyntaxNumeralSyntax.numeral_rename count n Fin.castSucc) (under (add hn E) P)
    have ha1 := of_eq (OriginalTreeQuotationSyntax.tree_rename input w a Fin.castSucc) (under (add ha E) P)
    have hC := construct hZ1 count input w.castSucc a.castSucc n.castSucc (Fin.last m) hw1 hn1 ha1 (.conjR hP)
    have hE : Derives Ξ E := .hyp (Or.inl rfl)
    have hE1 := of_eq (SyntaxUnaryIterationSyntax.forallClosure_rename w a n y Fin.castSucc) (under hE P)
    have hEq := SyntaxUnaryIterationCore.unique hZ1 9 w.castSucc a.castSucc n.castSucc (Fin.last m) y.castSucc hw1
      (SyntaxNumerals.range hZ1 count w.castSucc n.castSucc hw1 hn1) hC hE1
    have ho := OriginalQuotationValue.tree_output_subst (wrapped count input) w.castSucc (Fin.last m) y.castSucc hEq (.conjR hP)
    exact of_eq (OriginalTreeQuotationSyntax.tree_rename (wrapped count input) w y Fin.castSucc).symm ho
  · apply Derives.impI
    exact construct (ZFContext.add hZ _) count input w a n y (add hw _) (add hn _) (add ha _) (.hyp (Or.inl rfl))

private theorem wrapped_unary (n : Nat) (input : Tree) : wrapped n (.node 9 [input]) = wrapped (n+1) input := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg (fun t => Tree.node 9 [t]) ih

open YesMetaZFC.SetTheory.Definitional.Project (fo_formula fo_sentence)

/-- Exact ORIGINAL Project.Sentence.forallClosure, not a replacement closure. -/
theorem original_closure_tree {depth : Nat} (input : YesMetaZFC.SetTheory.Definitional.Project.Formula 1 depth) (hc : input.FreeClosed) :
    wrapped depth (PureSyntaxQuotation.formulaTree (fo_formula input hc)) =
      PureSyntaxQuotation.formulaTree (fo_sentence (YesMetaZFC.SetTheory.Definitional.Project.Sentence.forallClosure input hc)) := by
  induction depth with
  | zero => rfl
  | succ depth ih =>
    let p : YesMetaZFC.SetTheory.Definitional.Project.Formula 1 depth := .forallE input
    have hp : p.FreeClosed := by simpa only [p,YesMetaZFC.SetTheory.Definitional.Formula.FreeClosed] using hc
    have hi := ih p hp
    have hL : PureSyntaxQuotation.formulaTree (fo_formula p hp) = .node 9 [PureSyntaxQuotation.formulaTree (fo_formula input hc)] := by
      simp -implicitDefEqProofs only [p,fo_formula,PureSyntaxQuotation.formulaTree]
    have hR : PureSyntaxQuotation.formulaTree (fo_sentence (YesMetaZFC.SetTheory.Definitional.Project.Sentence.forallClosure p hp)) =
        PureSyntaxQuotation.formulaTree (fo_sentence (YesMetaZFC.SetTheory.Definitional.Project.Sentence.forallClosure input hc)) := by rfl
    rw [hL,hR] at hi
    exact (wrapped_unary depth (PureSyntaxQuotation.formulaTree (fo_formula input hc))).symm.trans hi

theorem native_formula_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) {depth : Nat}
    (input : YesMetaZFC.SetTheory.Definitional.Project.Formula 1 depth) (hc : input.FreeClosed) (w a n y : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (SyntaxNumeralSyntax.numeral depth n))
    (ha : Derives Γ (PureQuotationSyntax.formula (fo_formula input hc) w a)) :
    Derives Γ ((SyntaxUnaryIterationSyntax.forallClosure w a n y).iff
      (PureQuotationSyntax.formula (fo_sentence (YesMetaZFC.SetTheory.Definitional.Project.Sentence.forallClosure input hc)) w y)) := by
  have hh := tree_iff hZ depth (PureSyntaxQuotation.formulaTree (fo_formula input hc)) w a n y hw hn ha
  exact of_eq (congrArg (fun t => (SyntaxUnaryIterationSyntax.forallClosure w a n y).iff (OriginalTreeQuotationSyntax.tree t w y))
    (original_closure_tree input hc)) hh

private theorem separationCore_closed {k : Nat} (schema : YesMetaZFC.SetTheory.Definitional.Project.UnarySchema k) :
    (YesMetaZFC.SetTheory.Axioms.Schema.separationCore schema).FreeClosed :=
  (YesMetaZFC.SetTheory.Definitional.Formula.freeClosed_forallClosure _).mp
    (YesMetaZFC.SetTheory.Axioms.Schema.separation schema).freeClosed

private theorem collectionCore_closed {k : Nat} (schema : YesMetaZFC.SetTheory.Definitional.Project.BinarySchema k) :
    (YesMetaZFC.SetTheory.Axioms.Schema.collectionCore schema).FreeClosed :=
  (YesMetaZFC.SetTheory.Definitional.Formula.freeClosed_forallClosure _).mp
    (YesMetaZFC.SetTheory.Axioms.Schema.collection schema).freeClosed

theorem separation_iff {m k} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (schema : YesMetaZFC.SetTheory.Definitional.Project.UnarySchema k) (w a n y : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (SyntaxNumeralSyntax.numeral k n))
    (ha : Derives Γ (PureQuotationSyntax.formula (fo_formula (YesMetaZFC.SetTheory.Axioms.Schema.separationCore schema) (separationCore_closed schema)) w a)) :
    Derives Γ ((SyntaxUnaryIterationSyntax.forallClosure w a n y).iff
      (PureQuotationSyntax.formula (NativeAxiomCertificateData.sentence (.separation schema)) w y)) :=
  of_eq (by rfl) (native_formula_iff hZ (YesMetaZFC.SetTheory.Axioms.Schema.separationCore schema) (separationCore_closed schema) w a n y hw hn ha)

theorem collection_iff {m k} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (schema : YesMetaZFC.SetTheory.Definitional.Project.BinarySchema k) (w a n y : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (SyntaxNumeralSyntax.numeral k n))
    (ha : Derives Γ (PureQuotationSyntax.formula (fo_formula (YesMetaZFC.SetTheory.Axioms.Schema.collectionCore schema) (collectionCore_closed schema)) w a)) :
    Derives Γ ((SyntaxUnaryIterationSyntax.forallClosure w a n y).iff
      (PureQuotationSyntax.formula (NativeAxiomCertificateData.sentence (.collection schema)) w y)) :=
  of_eq (by rfl) (native_formula_iff hZ (YesMetaZFC.SetTheory.Axioms.Schema.collectionCore schema) (collectionCore_closed schema) w a n y hw hn ha)

def sentence {m} {depth : Nat} (input : YesMetaZFC.SetTheory.Definitional.Project.Formula 1 depth) (hc : input.FreeClosed)
    (w a n y : Fin m) : Source.Sentence :=
  ((omega w).imp ((SyntaxNumeralSyntax.numeral depth n).imp
    ((PureQuotationSyntax.formula (fo_formula input hc) w a).imp
      ((SyntaxUnaryIterationSyntax.forallClosure w a n y).iff
        (PureQuotationSyntax.formula (fo_sentence (YesMetaZFC.SetTheory.Definitional.Project.Sentence.forallClosure input hc)) w y))))).close

theorem source_certificate {m} {depth : Nat} (input : YesMetaZFC.SetTheory.Definitional.Project.Formula 1 depth) (hc : input.FreeClosed)
    (w a n y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (sentence input hc w a n y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ := Context.add (PureQuotationSyntax.formula (fo_formula input hc) w a)
    (Context.add (SyntaxNumeralSyntax.numeral depth n) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.source_ZF m) _) _) _
  exact native_formula_iff hZ input hc w a n y (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem kernel_certificate {m} {depth : Nat} (input : YesMetaZFC.SetTheory.Definitional.Project.Formula 1 depth) (hc : input.FreeClosed)
    (w a n y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (sentence input hc w a n y)) :=
  ZFReplay.replay (TheoryTransport.sentence (source_certificate input hc w a n y))

def separationSentence {m k} (schema : YesMetaZFC.SetTheory.Definitional.Project.UnarySchema k) (w a n y : Fin m) : Source.Sentence :=
  ((omega w).imp ((SyntaxNumeralSyntax.numeral k n).imp
    ((PureQuotationSyntax.formula (fo_formula (YesMetaZFC.SetTheory.Axioms.Schema.separationCore schema) (separationCore_closed schema)) w a).imp
      ((SyntaxUnaryIterationSyntax.forallClosure w a n y).iff
        (PureQuotationSyntax.formula (NativeAxiomCertificateData.sentence (.separation schema)) w y))))).close

def collectionSentence {m k} (schema : YesMetaZFC.SetTheory.Definitional.Project.BinarySchema k) (w a n y : Fin m) : Source.Sentence :=
  ((omega w).imp ((SyntaxNumeralSyntax.numeral k n).imp
    ((PureQuotationSyntax.formula (fo_formula (YesMetaZFC.SetTheory.Axioms.Schema.collectionCore schema) (collectionCore_closed schema)) w a).imp
      ((SyntaxUnaryIterationSyntax.forallClosure w a n y).iff
        (PureQuotationSyntax.formula (NativeAxiomCertificateData.sentence (.collection schema)) w y))))).close

theorem separation_kernel_certificate {m k} (schema : YesMetaZFC.SetTheory.Definitional.Project.UnarySchema k) (w a n y : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (separationSentence schema w a n y)) :=
  kernel_certificate (YesMetaZFC.SetTheory.Axioms.Schema.separationCore schema) (separationCore_closed schema) w a n y

theorem collection_kernel_certificate {m k} (schema : YesMetaZFC.SetTheory.Definitional.Project.BinarySchema k) (w a n y : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (collectionSentence schema w a n y)) :=
  kernel_certificate (YesMetaZFC.SetTheory.Axioms.Schema.collectionCore schema) (collectionCore_closed schema) w a n y

end PPAC.Migration.SchemaClosureQuotation
