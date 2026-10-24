import PPAC.Migration.Internal.FixedAxiomTableSyntax

/-! Object derivations for the fixed part of the axiom test; schemas remain separate. -/
namespace PPAC.Migration.Internal.FixedAxiomTableFacts
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax FixedAxiomTableSyntax
open SyntaxRenameQuerySyntax (of_eq)
open NativeAxiomCertificateData (fixedFormula fixedTag)
attribute [local irreducible] FixedAxiomPacketSyntax.leaf PureQuotationSyntax.formula

theorem intro_table {m} {Γ : Context m} (target : Bool) (kind : Fin 10) (hk : kind ∈ kinds target)
    (w c f : Fin m) (hc : Derives Γ (FixedAxiomPacketSyntax.leaf (fixedTag kind) w c))
    (hf : Derives Γ (PureQuotationSyntax.formula (fixedFormula kind) w f)) : Derives Γ (table target w c f) :=
  ProofTreeRootSyntax.disjoin_intro _ _ (List.mem_map.mpr ⟨kind,hk,rfl⟩) (.conjI hc hf)

theorem table_at {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (target : Bool) (kind : Fin 10)
    (hk : kind ∈ kinds target) (w c f : Fin m) (hw : Derives Γ (omega w))
    (hc : Derives Γ (FixedAxiomPacketSyntax.leaf (fixedTag kind) w c)) :
    Derives Γ ((table target w c f).iff (PureQuotationSyntax.formula (fixedFormula kind) w f)) := by
  apply Derives.conjI
  · apply Derives.impI
    let E := table target w c f
    let Δ := Context.add E Γ
    have hE : Derives Δ E := .hyp (Or.inl rfl)
    apply ProofTreeRootSyntax.disjoin_elim _ _ hE
    intro q hq
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hq
    apply Derives.impI
    have hB : Derives (Context.add (branch j w c f) Δ) (branch j w c f) := .hyp (Or.inl rfl)
    by_cases he : j = kind
    · subst j
      exact .conjR hB
    · have ht : fixedTag j ≠ fixedTag kind := fun h => he (NativeAxiomCertificateData.fixedTag_injective h)
      exact .botE (FixedAxiomPacketUnique.disjoint (ZFContext.add (ZFContext.add hZ E) _) _ _ ht w c
        (add (add hw E) _) (.conjL hB) (add (add hc E) _))
  · apply Derives.impI
    exact intro_table target kind hk w c f (add hc _) (.hyp (Or.inl rfl))

theorem table_inputs {m} {Γ : Context m} (target : Bool) (w c f d g : Fin m)
    (hc : Derives Γ (.equal c d)) (hf : Derives Γ (.equal f g)) (ht : Derives Γ (table target w c f)) :
    Derives Γ (table target w d g) := by
  let P := table target w.castSucc (Fin.last m) f.castSucc
  let Q := table target w.castSucc d.castSucc (Fin.last m)
  have hP0 : P.instantiate c = table target w c f := by simp only [P, Formula.instantiate, table_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have hP1 : P.instantiate d = table target w d f := by simp only [P, Formula.instantiate, table_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have hQ0 : Q.instantiate f = table target w d f := by simp only [Q, Formula.instantiate, table_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have hQ1 : Q.instantiate g = table target w d g := by simp only [Q, Formula.instantiate, table_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact of_eq hQ1 (Derives.eqSubst Q hf (of_eq hQ0.symm (of_eq hP1 (Derives.eqSubst P hc (of_eq hP0.symm ht)))))

def rowBody {m} (target : Bool) (w row : Fin m) : Formula (m+2) :=
  (SyntaxNodeSyntax.constructor 2 0 (old 2 w) (SetLanguage.args2 (slot 2 0) (slot 2 1)) (old 2 row)).conj
    (table target (old 2 w) (slot 2 0) (slot 2 1))

theorem rowTest_eq {m} (target : Bool) (w row : Fin m) :
    rowTest target w row = existsMany 2 (rowBody target w row) := rfl

theorem intro_row {m} {Γ : Context m} (target : Bool) (w row c f : Fin m)
    (hr : Derives Γ (SyntaxNodeSyntax.constructor 2 0 w (SetLanguage.args2 c f) row))
    (ht : Derives Γ (table target w c f)) : Derives Γ (rowTest target w row) := by
  rw [rowTest_eq]
  apply HornBinderRules.intro_many 2 (rowBody target w row) (SetLanguage.args2 c f)
  exact of_eq (by simp only [rowBody, Formula.rename, SyntaxNodeSyntax.constructor_rename, table_rename,
    ProofTreeEntryFacts.args2_map, assign_old, assign_slot]; rfl) (.conjI hr ht)

theorem row_at {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (target : Bool) (w row c f : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (SyntaxNodeSyntax.constructor 2 0 w (SetLanguage.args2 c f) row)) :
    Derives Γ ((rowTest target w row).iff (table target w c f)) := by
  apply Derives.conjI
  · apply Derives.impI
    let E := rowTest target w row
    let B := rowBody target w row
    let Δ := Context.add B (raisedContext 2 (Context.add E Γ))
    have hE : Derives (Context.add E Γ) E := .hyp (Or.inl rfl)
    apply HornBinderRules.eliminate_many 2 B _ hE
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have hZ2 := HornBinderRules.zf_body 2 (ZFContext.add hZ E) B
    have hw2 := of_eq (omega_rename w (old 2)) (HornBinderRules.under_body 2 (add hw E) B)
    have hr2 : Derives Δ (SyntaxNodeSyntax.constructor 2 0 (old 2 w) (SetLanguage.args2 (old 2 c) (old 2 f)) (old 2 row)) := of_eq (by simp only [SyntaxNodeSyntax.constructor_rename, ProofTreeEntryFacts.args2_map]) (HornBinderRules.under_body 2 (add hr E) B)
    have e0 := ProofTreeConstructorFacts.field_equal hZ2 2 0 (old 2 w) (old 2 row)
      (SetLanguage.args2 (slot 2 0) (slot 2 1)) (SetLanguage.args2 (old 2 c) (old 2 f)) 0 hw2 (.conjL hB) hr2
    have e1 := ProofTreeConstructorFacts.field_equal hZ2 2 0 (old 2 w) (old 2 row)
      (SetLanguage.args2 (slot 2 0) (slot 2 1)) (SetLanguage.args2 (old 2 c) (old 2 f)) 1 hw2 (.conjL hB) hr2
    exact of_eq (table_rename target w c f (old 2)).symm
      (table_inputs target (old 2 w) (slot 2 0) (slot 2 1) (old 2 c) (old 2 f) e0 e1 (.conjR hB))
  · apply Derives.impI
    exact intro_row target w row c f (add hr _) (.hyp (Or.inl rfl))

theorem row_omega_subst {m} {Γ : Context m} (target : Bool) (w v row : Fin m)
    (he : Derives Γ (.equal w v)) (hr : Derives Γ (rowTest target w row)) : Derives Γ (rowTest target v row) := by
  let P := rowTest target (Fin.last m) row.castSucc
  have h0 : P.instantiate w = rowTest target w row := by simp only [P, Formula.instantiate, rowTest_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have h1 : P.instantiate v = rowTest target v row := by simp only [P, Formula.instantiate, rowTest_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact of_eq h1 (Derives.eqSubst P he (of_eq h0.symm hr))

theorem test_iff_row {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (target : Bool) (w row : Fin m)
    (hw : Derives Γ (omega w)) : Derives Γ ((AxiomTestSyntax.holds (test target) row).iff (rowTest target w row)) := by
  apply Derives.conjI
  · apply Derives.impI
    let E := AxiomTestSyntax.holds (test target) row
    let B := (omega (Fin.last m)).conj (rowTest target (Fin.last m) row.castSucc)
    let Δ := Context.add B (Context.image Formula.raise (Context.add E Γ))
    have hE : Derives (Context.add E Γ) E := .hyp (Or.inl rfl)
    apply Derives.exE (p := B) (of_eq (test_at target row) hE)
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have hw1 := of_eq (omega_rename w Fin.castSucc) (under (add hw E) B)
    have he := OmegaAlgebra.unique (Fin.last m) w.castSucc (ZFContext.arithmetic (ZFContext.under (ZFContext.add hZ E) B)).base.extensionality (.conjL hB) hw1
    exact of_eq (by simp only [Formula.raise, rowTest_rename]) (row_omega_subst target (Fin.last m) w.castSucc row.castSucc he (.conjR hB))
  · apply Derives.impI
    apply of_eq (test_at target row).symm
    apply Derives.exI w
    exact of_eq (by simp only [Formula.instantiate, Formula.rename, omega_rename, rowTest_rename,
      Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI (add hw _) (.hyp (Or.inl rfl)))

theorem at_packet_row {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (target : Bool) (kind : Fin 10)
    (hk : kind ∈ kinds target) (w row c f : Fin m) (hw : Derives Γ (omega w))
    (hr : Derives Γ (SyntaxNodeSyntax.constructor 2 0 w (SetLanguage.args2 c f) row))
    (hc : Derives Γ (FixedAxiomPacketSyntax.leaf (fixedTag kind) w c)) :
    Derives Γ ((AxiomTestSyntax.holds (test target) row).iff (PureQuotationSyntax.formula (fixedFormula kind) w f)) := by
  have h0 := test_iff_row hZ target w row hw
  have h1 := row_at hZ target w row c f hw hr
  have h2 := table_at hZ target kind hk w c f hw hc
  apply Derives.conjI
  · apply Derives.impI
    exact .impE (add (.conjL h2) _) (.impE (add (.conjL h1) _) (.impE (add (.conjL h0) _) (.hyp (Or.inl rfl))))
  · apply Derives.impI
    exact .impE (add (.conjR h0) _) (.impE (add (.conjR h1) _) (.impE (add (.conjR h2) _) (.hyp (Or.inl rfl))))

theorem reject_choice_row {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (target : Bool)
    (w row c f : Fin m) (hw : Derives Γ (omega w))
    (hr : Derives Γ (SyntaxNodeSyntax.constructor 2 0 w (SetLanguage.args2 c f) row))
    (hc : Derives Γ (FixedAxiomPacketSyntax.leaf 7 w c)) :
    Derives Γ (AxiomTestSyntax.holds (test target) row).neg := by
  have h0 := test_iff_row hZ target w row hw
  have h1 := row_at hZ target w row c f hw hr
  apply Derives.impI
  let E := AxiomTestSyntax.holds (test target) row
  let Δ := Context.add E Γ
  have ht : Derives Δ (table target w c f) := .impE (add (.conjL h1) E)
    (.impE (add (.conjL h0) E) (.hyp (Or.inl rfl)))
  apply ProofTreeRootSyntax.disjoin_elim _ _ ht
  intro q hq
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hq
  apply Derives.impI
  have hB : Derives (Context.add (branch j w c f) Δ) (branch j w c f) := .hyp (Or.inl rfl)
  exact FixedAxiomPacketUnique.disjoint (ZFContext.add (ZFContext.add hZ E) _) _ _
    (NativeAxiomCertificateData.fixedTag_ne_choice j) w c (add (add hw E) _) (.conjL hB) (add (add hc E) _)

end PPAC.Migration.Internal.FixedAxiomTableFacts
