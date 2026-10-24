import PPAC.Migration.Internal.ProofTreeInductionStep

/-! 原ZF Foundation／Separation证明全部内部证明码的条件结构归纳；不存在外部Nat归纳替代。 -/
namespace PPAC.Migration.Internal.ProofTreeInduction
open Source SourceAlgebra SourceLogic OmegaSyntax ProofTreeInductionSyntax
open SyntaxRenameQuerySyntax (of_eq)
open ReplacementPredicates (paramsUp)

def inductionMatrix (test : Formula 1) (P : Formula 2) : Formula 2 := correct test P (0 : Fin 1).castSucc (Fin.last 1)

theorem matrix_pred {m} (test : Formula 1) (P : Formula 2) (ρ : Fin 1 → Fin m) (x : Fin m) :
    MinimalPredicates.pred (inductionMatrix test P) ρ x = correct test P (ρ 0) x := by
  simp only [inductionMatrix, MinimalPredicates.pred, correct_rename, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem progressive {m} {Γ : Context m} (test : Formula 1) (P : Formula 2) (hZ : ZFContext.Evidence Γ)
    (w : Fin m) (hw : Derives Γ (omega w)) (hc : Derives Γ (closure test P w)) :
    Derives Γ (SetInductionSyntax.progressive (inductionMatrix test P) (fun _ : Fin 1 => w)) := by
  simp only [SetInductionSyntax.progressive, SetInductionSyntax.below, matrix_pred, paramsUp]
  apply Derives.allI
  apply Derives.impI
  let I := allIH test P w.castSucc (Fin.last m)
  let Δ := Context.add I (Context.image Formula.raise Γ)
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw I)
  have hc1 := of_eq (closure_rename test P w Fin.castSucc) (under hc I)
  exact ProofTreeInductionStep.from_induction test P (ZFContext.under hZ I) w.castSucc (Fin.last m) hw1 hc1 (.hyp (Or.inl rfl))

theorem all_correct {m} {Γ : Context m} (test : Formula 1) (P : Formula 2) (hZ : ZFContext.Evidence Γ)
    (w : Fin m) (hw : Derives Γ (omega w)) (hc : Derives Γ (closure test P w)) :
    Derives Γ (.all (correct test P w.castSucc (Fin.last m))) := by
  have hh := SetInduction.all_holds (inductionMatrix test P) (fun _ : Fin 1 => w)
    (ZFContext.separation hZ (inductionMatrix test P).neg) (ZFContext.arithmetic hZ).base.foundation
    (ZFContext.closed hZ ObjectTransitiveCover.source_cover) (progressive test P hZ w hw hc)
  exact of_eq (by simp only [SetInductionSyntax.holds, matrix_pred, paramsUp]) hh

theorem at_node {m} {Γ : Context m} (test : Formula 1) (P : Formula 2) (hZ : ZFContext.Evidence Γ)
    (w code : Fin m) (hw : Derives Γ (omega w)) (hc : Derives Γ (closure test P w)) :
    Derives Γ (correct test P w code) := of_eq
  (by simp only [Formula.instantiate, correct_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
  (Derives.allE code (all_correct test P hZ w hw hc))

theorem at_root {m} {Γ : Context m} (test : Formula 1) (P : Formula 2) (hZ : ZFContext.Evidence Γ)
    (w code conclusion : Fin m) (hw : Derives Γ (omega w)) (hc : Derives Γ (closure test P w))
    (hr : Derives Γ (ProofTreeEntrySyntax.root test w code conclusion)) : Derives Γ (property P w code) := by
  have hn := Derives.conjL (Derives.impE (.conjL (ProofTreeRootBackward.root_iff test hZ w code conclusion hw)) hr)
  exact .impE (at_node test P hZ w code hw hc) hn

theorem reject_node {m} {Γ : Context m} (test : Formula 1) (P : Formula 2) (hZ : ZFContext.Evidence Γ)
    (w code : Fin m) (hw : Derives Γ (omega w)) (hc : Derives Γ (closure test P w))
    (hp : Derives Γ (property P w code).neg) : Derives Γ (ProofTreeEntrySyntax.node test w code).neg := by
  apply Derives.impI
  exact .impE (add hp _) (.impE (add (at_node test P hZ w code hw hc) _) (.hyp (Or.inl rfl)))

theorem reject_root {m} {Γ : Context m} (test : Formula 1) (P : Formula 2) (hZ : ZFContext.Evidence Γ)
    (w code conclusion : Fin m) (hw : Derives Γ (omega w)) (hc : Derives Γ (closure test P w))
    (hp : Derives Γ (property P w code).neg) : Derives Γ (ProofTreeEntrySyntax.root test w code conclusion).neg := by
  apply Derives.impI
  exact .impE (add hp _) (at_root test P (ZFContext.add hZ _) w code conclusion (add hw _) (add hc _) (.hyp (Or.inl rfl)))

end PPAC.Migration.Internal.ProofTreeInduction
