import PPAC.Migration.Internal.ProofTreeBranchHead

/-! 实际根标签1使原局部rowCheck条件在对象理论中成立。 -/
namespace PPAC.Migration.Internal.ProofTreeRootLocal
open Source SourceAlgebra SourceLogic OmegaSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem node_one {m} {Γ : Context m} (test : Formula 1) (hZ : ZFContext.Evidence Γ) (k : Nat)
    (w tag r : Fin m) (xs : Fin k → Fin m) (hw : Derives Γ (omega w))
    (ht : Derives Γ (SyntaxNumeralSyntax.numeral 1 tag)) (hr : Derives Γ (SyntaxNodeSyntax.node k w tag xs r)) :
    Derives Γ (ProofTreeRowLocalSyntax.localCondition test w r) := by
  let B := SyntaxNodeSyntax.nodeBody k w tag xs r
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply SyntaxNodeSyntax.eliminate_node k w tag xs r _ hr
  have hZ1 := ZFContext.under hZ B
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw B)
  have ht1 := of_eq (SyntaxNumeralSyntax.numeral_rename 1 tag Fin.castSucc) (under ht B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hp := SyntaxForests.range hZ1 k w.castSucc (fun i => (xs i).castSucc) (Fin.last m) hw1 (.conjL (.conjR hB))
  have hs := PairingProjection.selected_code true true w.castSucc tag.castSucc (Fin.last m) r.castSucc (.conjL hB) hp (.conjR (.conjR hB))
  have hst : Derives Δ (PairingProjectionSyntax.step true true w.castSucc r.castSucc tag.castSucc) := .disjL (by simpa only [ite_true] using hs)
  have hg : Derives Δ ((empty tag.castSucc).imp (ProofTreeRowLocalSyntax.atZero test w.castSucc r.castSucc)) := by
    apply Derives.impI
    exact .botE (.impE (add (ProofTreeZeroGuard.one_nonempty tag.castSucc ht1) _) (.hyp (Or.inl rfl)))
  have ho : Derives Δ (ProofTreeRowLocalSyntax.localCondition test w.castSucc r.castSucc) := by
    apply Derives.exI tag.castSucc
    simpa only [ProofTreeRowLocalSyntax.localCondition, Formula.instantiate, Formula.rename, PairingProjectionSyntax.step_rename,
      empty_rename, ProofTreeRowLocalSyntax.atZero_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using
      Derives.conjI hst hg
  exact of_eq (ProofTreeRowLocalSyntax.localCondition_rename test w r Fin.castSucc).symm ho

theorem constructor_one {m} {Γ : Context m} (test : Formula 1) (hZ : ZFContext.Evidence Γ) (k : Nat)
    (w r : Fin m) (xs : Fin k → Fin m) (hw : Derives Γ (omega w))
    (hr : Derives Γ (SyntaxNodeSyntax.constructor k 1 w xs r)) : Derives Γ (ProofTreeRowLocalSyntax.localCondition test w r) := by
  let B := SyntaxNodeSyntax.constructorBody k 1 w xs r
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply SyntaxNodeSyntax.eliminate_constructor k 1 w xs r _ hr
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have ho := node_one test (ZFContext.under hZ B) k w.castSucc (Fin.last m) r.castSucc (fun i => (xs i).castSucc)
    (of_eq (omega_rename w Fin.castSucc) (under hw B)) (.conjL hB) (.conjR hB)
  exact of_eq (ProofTreeRowLocalSyntax.localCondition_rename test w r Fin.castSucc).symm ho

end PPAC.Migration.Internal.ProofTreeRootLocal
