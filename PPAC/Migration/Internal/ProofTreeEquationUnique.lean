import PPAC.Migration.Internal.ProofTreeEquationReverseStep

/-! 原ZF Foundation消去反向IH；原节点是六分支下降方程的唯一内部解。 -/
namespace PPAC.Migration.Internal.ProofTreeEquationUnique
open Source SourceAlgebra SourceLogic OmegaSyntax ProofTreeInductionSyntax ProofTreeEquationSyntax
open SyntaxRenameQuerySyntax (of_eq)
open ReplacementPredicates (paramsUp)

def inductionMatrix (test : Formula 1) (P : Formula 2) : Formula 2 := reverseCorrect test P (0 : Fin 1).castSucc (Fin.last 1)

theorem matrix_pred {m} (test : Formula 1) (P : Formula 2) (ρ : Fin 1 → Fin m) (x : Fin m) :
    MinimalPredicates.pred (inductionMatrix test P) ρ x = reverseCorrect test P (ρ 0) x := by
  simp only [inductionMatrix, MinimalPredicates.pred, reverseCorrect_rename, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem progressive {m} {Γ : Context m} (test : Formula 1) (P : Formula 2) (hZ : ZFContext.Evidence Γ)
    (w : Fin m) (hw : Derives Γ (omega w)) (he : Derives Γ (equation test P w)) :
    Derives Γ (SetInductionSyntax.progressive (inductionMatrix test P) (fun _ : Fin 1 => w)) := by
  simp only [SetInductionSyntax.progressive, SetInductionSyntax.below, matrix_pred, paramsUp]
  apply Derives.allI
  apply Derives.impI
  let I := reverseIH test P w.castSucc (Fin.last m)
  let Δ := Context.add I (Context.image Formula.raise Γ)
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw I)
  have he1 := of_eq (equation_rename test P w Fin.castSucc) (under he I)
  exact ProofTreeEquationReverseStep.from_induction test P (ZFContext.under hZ I) w.castSucc (Fin.last m) hw1 he1 (.hyp (Or.inl rfl))

theorem all_reverse {m} {Γ : Context m} (test : Formula 1) (P : Formula 2) (hZ : ZFContext.Evidence Γ)
    (w : Fin m) (hw : Derives Γ (omega w)) (he : Derives Γ (equation test P w)) :
    Derives Γ (.all (reverseCorrect test P w.castSucc (Fin.last m))) := by
  have hh := SetInduction.all_holds (inductionMatrix test P) (fun _ : Fin 1 => w)
    (ZFContext.separation hZ (inductionMatrix test P).neg) (ZFContext.arithmetic hZ).base.foundation
    (ZFContext.closed hZ ObjectTransitiveCover.source_cover) (progressive test P hZ w hw he)
  exact of_eq (by simp only [SetInductionSyntax.holds, matrix_pred, paramsUp]) hh

theorem reverse_at {m} {Γ : Context m} (test : Formula 1) (P : Formula 2) (hZ : ZFContext.Evidence Γ)
    (w code : Fin m) (hw : Derives Γ (omega w)) (he : Derives Γ (equation test P w)) :
    Derives Γ (reverseCorrect test P w code) := of_eq
  (by simp only [Formula.instantiate, reverseCorrect_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
  (Derives.allE code (all_reverse test P hZ w hw he))

theorem point_iff {m} {Γ : Context m} (test : Formula 1) (P : Formula 2) (hZ : ZFContext.Evidence Γ)
    (w code : Fin m) (hw : Derives Γ (omega w)) (he : Derives Γ (equation test P w)) :
    Derives Γ ((ProofTreeEntrySyntax.node test w code).iff (property P w code)) :=
  .conjI (ProofTreeInduction.at_node test P hZ w code hw (closure_from_equation test P w he)) (reverse_at test P hZ w code hw he)

theorem all_iff {m} {Γ : Context m} (test : Formula 1) (P : Formula 2) (hZ : ZFContext.Evidence Γ)
    (w : Fin m) (hw : Derives Γ (omega w)) (he : Derives Γ (equation test P w)) :
    Derives Γ (.all ((ProofTreeEntrySyntax.node test w.castSucc (Fin.last m)).iff (property P w.castSucc (Fin.last m)))) := by
  apply Derives.allI
  have hw1 := of_eq (omega_rename w Fin.castSucc) (Derives.rename Fin.castSucc hw)
  have he1 := of_eq (equation_rename test P w Fin.castSucc) (Derives.rename Fin.castSucc he)
  exact point_iff test P (ZFContext.rename hZ Fin.castSucc) w.castSucc (Fin.last m) hw1 he1

theorem root_iff {m} {Γ : Context m} (test : Formula 1) (P : Formula 2) (hZ : ZFContext.Evidence Γ)
    (w code conclusion : Fin m) (hw : Derives Γ (omega w)) (he : Derives Γ (equation test P w)) :
    Derives Γ ((ProofTreeEntrySyntax.root test w code conclusion).iff
      ((property P w code).conj (ProofTreeRootSyntax.closedPayload w code conclusion))) :=
  RawCodeFieldAtConstructor.iff_trans (ProofTreeRootBackward.root_iff test hZ w code conclusion hw)
    (FormulaCodeCongruence.conj_congr (point_iff test P hZ w code hw he) (SyntaxTypeLocalTransfer.iff_refl _))

theorem two_solutions {m} {Γ : Context m} (test : Formula 1) (P Q : Formula 2) (hZ : ZFContext.Evidence Γ)
    (w code : Fin m) (hw : Derives Γ (omega w)) (hp : Derives Γ (equation test P w)) (hq : Derives Γ (equation test Q w)) :
    Derives Γ ((property P w code).iff (property Q w code)) := by
  have hP := point_iff test P hZ w code hw hp
  exact RawCodeFieldAtConstructor.iff_trans (.conjI (.conjR hP) (.conjL hP)) (point_iff test Q hZ w code hw hq)

theorem node_natural {m} {Γ : Context m} (test : Formula 1) (hZ : ZFContext.Evidence Γ) (w code : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (ProofTreeEntrySyntax.node test w code)) : Derives Γ (.mem code w) := by
  let B := (SyntaxNodeSyntax.constructor 1 0 w.castSucc (fun _ => code.castSucc) (Fin.last m)).conj
    (ProofTreeTraceSyntax.condition test w.castSucc (Fin.last m))
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) hn
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  exact ProjectionNodeFields.constructor_field_natural (ZFContext.under hZ B) 1 0 w.castSucc (Fin.last m) (fun _ => code.castSucc) 0
    (of_eq (omega_rename w Fin.castSucc) (under hw B)) (.conjL hB)

theorem property_natural {m} {Γ : Context m} (test : Formula 1) (P : Formula 2) (hZ : ZFContext.Evidence Γ)
    (w code : Fin m) (hw : Derives Γ (omega w)) (he : Derives Γ (equation test P w))
    (hp : Derives Γ (property P w code)) : Derives Γ (.mem code w) :=
  node_natural test hZ w code hw (.impE (reverse_at test P hZ w code hw he) hp)

end PPAC.Migration.Internal.ProofTreeEquationUnique
