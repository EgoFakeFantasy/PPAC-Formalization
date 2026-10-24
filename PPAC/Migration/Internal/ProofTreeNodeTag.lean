import PPAC.Migration.Internal.ProofTreeNodeFieldLocal

/-! 实际tag0投影在对象EX中取得，并把原条件局部检查精确化为载荷局部表。 -/
namespace PPAC.Migration.Internal.ProofTreeNodeTag
open Source SourceAlgebra SourceLogic OmegaSyntax
open SyntaxRenameQuerySyntax (of_eq)

def zeroTag {m} (w row : Fin m) : Formula m := .ex
  ((empty (Fin.last m)).conj (PairingProjectionSyntax.step true true w.castSucc row.castSucc (Fin.last m)))

theorem zeroTag_rename {m l} (w row : Fin m) (ρ : Fin m → Fin l) :
    (zeroTag w row).rename ρ = zeroTag (ρ w) (ρ row) := by
  simp only [zeroTag, Formula.rename, empty_rename, PairingProjectionSyntax.step_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem node_empty_tag {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (k : Nat)
    (w tag row : Fin m) (xs : Fin k → Fin m) (hw : Derives Γ (omega w))
    (ht : Derives Γ (empty tag)) (hr : Derives Γ (SyntaxNodeSyntax.node k w tag xs row)) : Derives Γ (zeroTag w row) := by
  let B := SyntaxNodeSyntax.nodeBody k w tag xs row
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply SyntaxNodeSyntax.eliminate_node k w tag xs row _ hr
  have hZ1 := ZFContext.under hZ B
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw B)
  have ht1 := of_eq (empty_rename tag Fin.castSucc) (under ht B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hp := SyntaxForests.range hZ1 k w.castSucc (fun i => (xs i).castSucc) (Fin.last m) hw1 (.conjL (.conjR hB))
  have hs := PairingProjection.selected_code true true w.castSucc tag.castSucc (Fin.last m) row.castSucc (.conjL hB) hp (.conjR (.conjR hB))
  have hst : Derives Δ (PairingProjectionSyntax.step true true w.castSucc row.castSucc tag.castSucc) := .disjL (by simpa only [ite_true] using hs)
  have ho : Derives Δ (zeroTag w.castSucc row.castSucc) := by
    apply Derives.exI tag.castSucc
    simpa only [zeroTag, Formula.instantiate, Formula.rename, empty_rename, PairingProjectionSyntax.step_rename,
      Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using Derives.conjI ht1 hst
  exact of_eq (zeroTag_rename w row Fin.castSucc).symm ho

theorem constructor_zero_tag {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (k : Nat)
    (w row : Fin m) (xs : Fin k → Fin m) (hw : Derives Γ (omega w))
    (hr : Derives Γ (SyntaxNodeSyntax.constructor k 0 w xs row)) : Derives Γ (zeroTag w row) := by
  let B := SyntaxNodeSyntax.constructorBody k 0 w xs row
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply SyntaxNodeSyntax.eliminate_constructor k 0 w xs row _ hr
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have ho := node_empty_tag (ZFContext.under hZ B) k w.castSucc (Fin.last m) row.castSucc (fun i => (xs i).castSucc)
    (of_eq (omega_rename w Fin.castSucc) (under hw B)) (.conjL hB) (.conjR hB)
  exact of_eq (zeroTag_rename w row Fin.castSucc).symm ho

theorem local_at_zero {m} {Γ : Context m} (test : Formula 1) (hZ : ZFContext.Evidence Γ) (w row z : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hs : Derives Γ (PairingProjectionSyntax.step true true w row z)) :
    Derives Γ ((ProofTreeRowLocalSyntax.localCondition test w row).iff (ProofTreeRowLocalSyntax.atZero test w row)) := by
  apply Derives.conjI
  · apply Derives.impI
    let E := ProofTreeRowLocalSyntax.localCondition test w row
    let B := (PairingProjectionSyntax.step true true w.castSucc row.castSucc (Fin.last m)).conj
      ((empty (Fin.last m)).imp (ProofTreeRowLocalSyntax.atZero test w.castSucc row.castSucc))
    let Δ := Context.add B (Context.image Formula.raise (Context.add E Γ))
    apply Derives.exE (p := B) (.hyp (Or.inl rfl))
    have lift {P : Formula m} (h : Derives Γ P) : Derives Δ P.raise := under (add h E) B
    have hw1 := of_eq (omega_rename w Fin.castSucc) (lift hw)
    have hz1 := of_eq (empty_rename z Fin.castSucc) (lift hz)
    have hs1 := of_eq (PairingProjectionSyntax.step_rename true true w row z Fin.castSucc) (lift hs)
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have he := PairingProjection.functional_point (ZFContext.under (ZFContext.add hZ E) B) true true w.castSucc row.castSucc (Fin.last m) z.castSucc hw1 (.conjL hB) hs1
    have ht := NaturalMultiplicationLaws.empty_subst z.castSucc (Fin.last m) (eq_symm he) hz1
    exact of_eq (ProofTreeRowLocalSyntax.atZero_rename test w row Fin.castSucc).symm (.impE (.conjR hB) ht)
  · apply Derives.impI
    let E := ProofTreeRowLocalSyntax.atZero test w row
    have hg : Derives (Context.add E Γ) ((empty z).imp E) := by
      apply Derives.impI
      exact .hyp (Or.inr (Or.inl rfl))
    apply Derives.exI z
    simpa only [ProofTreeRowLocalSyntax.localCondition, Formula.instantiate, Formula.rename,
      PairingProjectionSyntax.step_rename, empty_rename, ProofTreeRowLocalSyntax.atZero_rename,
      Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using Derives.conjI (add hs E) hg

theorem local_iff {m} {Γ : Context m} (test : Formula 1) (hZ : ZFContext.Evidence Γ) (w row code : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (SyntaxNodeSyntax.constructor 1 0 w (fun _ => code) row)) :
    Derives Γ ((ProofTreeRowLocalSyntax.localCondition test w row).iff (ProofAllNodeSyntax.table test w code)) := by
  let B := (empty (Fin.last m)).conj (PairingProjectionSyntax.step true true w.castSucc row.castSucc (Fin.last m))
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) (constructor_zero_tag hZ 1 w row (fun _ => code) hw hr)
  have hZ1 := ZFContext.under hZ B
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw B)
  have hr1 := of_eq (SyntaxNodeSyntax.constructor_rename 1 0 w (fun _ => code) row Fin.castSucc) (under hr B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have ho := RawCodeFieldAtConstructor.iff_trans (local_at_zero test hZ1 w.castSucc row.castSucc (Fin.last m) hw1 (.conjL hB) (.conjR hB))
    (ProofTreeNodeFieldLocal.atZero_iff test hZ1 w.castSucc row.castSucc code.castSucc hw1 hr1)
  exact of_eq (by simp only [Formula.raise, Formula.iff, Formula.rename, ProofTreeRowLocalSyntax.localCondition_rename, ProofAllTableRenaming.table_rename]) ho

end PPAC.Migration.Internal.ProofTreeNodeTag
