import PPAC.Migration.OriginalAxiomCodeTest
import PPAC.Migration.Internal.PureQuotationFormulaTyping
import PPAC.Migration.Internal.ProofTheoryNode

/-! Closed conclusion typing for the ACTUAL original ZF/U axiom test.
Pinned dependencies: the original native axiom certificate table and
ObjectProofNode.theoryShape. Consumer: the theory branch of internal proof
induction. Schema bodies/counts and accepted rows are arbitrary internal codes;
no quotation of a standard schema body is assumed. This is typing, not the
still outstanding uniform forcing soundness or internal Con theorem. -/
namespace PPAC.Migration.OriginalAxiomTyping
open Internal Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open OriginalAxiomCodeTest
open SyntaxRenameQuerySyntax (of_eq)

private theorem quotation_closed {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (input : PureSyntaxQuotation.Fm [] []) (w f : Fin m)
    (hw : Derives Γ (omega w)) (hf : Derives Γ (PureQuotationSyntax.formula input w f)) :
    Derives Γ (closedCode w f) := by
  let B := (Formula.mem (Fin.last m) w.castSucc).conj (empty (Fin.last m))
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) (SyntaxNumerals.exists_numeral hZ 0 w hw)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw B)
  have hf1 := of_eq (PureQuotationSyntax.formula_rename input w f Fin.castSucc) (under hf B)
  have ht := PureQuotationFormulaTyping.formula_type (ZFContext.under hZ B) input
    w.castSucc (Fin.last m) (Fin.last m) f.castSucc hw1 (.conjR hB) (.conjR hB) hf1
  have ho : Derives Δ (closedCode w.castSucc f.castSucc) := by
    apply Derives.exI (Fin.last m)
    exact of_eq (by simp only [Formula.instantiate, Formula.rename, empty_rename,
      FormulaCodeSyntax.formulaCode_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
      (.conjI (.conjR hB) ht)
  exact of_eq (closedCode_rename w f Fin.castSucc).symm ho

theorem table_typed {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (target : Bool) (w c f : Fin m) (hw : Derives Γ (omega w))
    (h : Derives Γ (table target w c f)) : Derives Γ (closedCode w f) := by
  apply Derives.disjE h
  · apply ProofTreeRootSyntax.disjoin_elim _ _ (.hyp (Or.inl rfl))
    intro q hq
    obtain ⟨kind, _, rfl⟩ := List.mem_map.mp hq
    apply Derives.impI
    exact quotation_closed (ZFContext.add (ZFContext.add hZ _) _)
      (NativeAxiomCertificateData.fixedFormula kind) w f (add (add hw _) _)
      (.conjR (.hyp (Or.inl rfl)))
  · apply Derives.disjE (.hyp (Or.inl rfl))
    · exact schemaBranch_typed (ZFContext.add (ZFContext.add hZ _) _) false w c f
        (add (add hw _) _) (.hyp (Or.inl rfl))
    · exact schemaBranch_typed (ZFContext.add (ZFContext.add hZ _) _) true w c f
        (add (add hw _) _) (.hyp (Or.inl rfl))

/-- Consume the exact axiom query in the original six-rule theory node. -/
theorem query_typed {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (target : Bool) (w c f : Fin m) (hw : Derives Γ (omega w))
    (h : Derives Γ (OriginalAxiomExprQuery.rowQuery (test target) 2 0 w (SetLanguage.args2 c f))) :
    Derives Γ (closedCode w f) := by
  let B := (SyntaxNodeSyntax.constructor 2 0 w.castSucc
    (SetLanguage.args2 c.castSucc f.castSucc) (Fin.last m)).conj
      (AxiomTestSyntax.holds (test target) (Fin.last m))
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) h
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw B)
  have hrow := Derives.impE (.conjL (test_iff_row (ZFContext.under hZ B) target
    w.castSucc (Fin.last m) hw1)) (.conjR hB)
  have ht := Derives.impE (.conjL (row_at (ZFContext.under hZ B) target w.castSucc
    (Fin.last m) c.castSucc f.castSucc hw1 (.conjL hB))) hrow
  exact of_eq (closedCode_rename w f Fin.castSucc).symm
    (table_typed (ZFContext.under hZ B) target w.castSucc c.castSucc f.castSucc hw1 ht)

theorem theory_matrix_typed {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (target : Bool) (w z row : Fin m) (env : Fin 3 → Fin m) (hw : Derives Γ (omega w))
    (h : Derives Γ (ProofTheoryNodeSyntax.normalizedMatrix (test target) w z row env)) :
    Derives Γ (closedCode w (env 1)) :=
  query_typed hZ target w (env 2) (env 1) hw (.conjR (.conjR (.conjR h)))

theorem actual_theory_matrix_typed {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (target : Bool) (w z row : Fin m) (env : Fin 3 → Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (h : Derives Γ (ProofTheoryNodeSyntax.boundedMatrix (test target) w row env)) :
    Derives Γ (closedCode w (env 1)) :=
  theory_matrix_typed hZ target w z row env hw
    (.impE (.conjL (ProofTheoryNode.matrix_iff (test target) hZ w z row env hw hz)) h)

def sentence {m} (target : Bool) (w z row : Fin m) (env : Fin 3 → Fin m) : Source.Sentence :=
  ((omega w).imp ((empty z).imp
    ((ProofTheoryNodeSyntax.boundedMatrix (test target) w row env).imp
      (closedCode w (env 1))))).close

theorem kernel_certificate {m} (target : Bool) (w z row : Fin m) (env : Fin 3 → Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
      (Translation.sentence (sentence target w z row env)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  exact actual_theory_matrix_typed
    (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.source_ZF m) _) _) _)
    target w z row env (.hyp (Or.inr (Or.inr (Or.inl rfl))))
      (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

end PPAC.Migration.OriginalAxiomTyping
