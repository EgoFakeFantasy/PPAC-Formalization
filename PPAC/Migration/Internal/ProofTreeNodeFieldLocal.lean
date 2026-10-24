import PPAC.Migration.Internal.ProofTreeRootBackward

/-! 实际node0的field0局部测试对应准确六类局部表；全部见证对象消去。 -/
namespace PPAC.Migration.Internal.ProofTreeNodeFieldLocal
open Source SourceAlgebra SourceLogic OmegaSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem table_subst {m} {Γ : Context m} (test : Formula 1) (w x y : Fin m)
    (he : Derives Γ (.equal x y)) (hx : Derives Γ (ProofAllNodeSyntax.table test w x)) :
    Derives Γ (ProofAllNodeSyntax.table test w y) := by
  let P := ProofAllNodeSyntax.table test w.castSucc (Fin.last m)
  have h0 : P.instantiate x = ProofAllNodeSyntax.table test w x := by
    simp only [P, Formula.instantiate, ProofAllTableRenaming.table_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have h1 : P.instantiate y = ProofAllNodeSyntax.table test w y := by
    simp only [P, Formula.instantiate, ProofAllTableRenaming.table_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact of_eq h1 (Derives.eqSubst P he (of_eq h0.symm hx))

theorem fieldCheck_iff {m} {Γ : Context m} (test : Formula 1) (hZ : ZFContext.Evidence Γ) (w row code z : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (SyntaxNodeSyntax.constructor 1 0 w (fun _ => code) row))
    (hz : Derives Γ (empty z)) :
    Derives Γ ((ProofTreeRowLocalSyntax.fieldCheck test w row z).iff (ProofAllNodeSyntax.table test w code)) := by
  apply Derives.conjI
  · apply Derives.impI
    let E := ProofTreeRowLocalSyntax.fieldCheck test w row z
    let B := (RawCodeFieldSyntax.field w.castSucc row.castSucc z.castSucc (Fin.last m)).conj (ProofAllNodeSyntax.table test w.castSucc (Fin.last m))
    let Δ := Context.add B (Context.image Formula.raise (Context.add E Γ))
    apply Derives.exE (p := B) (.hyp (Or.inl rfl))
    have lift {P : Formula m} (h : Derives Γ P) : Derives Δ P.raise := under (add h E) B
    have hw1 := of_eq (omega_rename w Fin.castSucc) (lift hw)
    have hr1 := of_eq (SyntaxNodeSyntax.constructor_rename 1 0 w (fun _ => code) row Fin.castSucc) (lift hr)
    have hz1 := of_eq (empty_rename z Fin.castSucc) (lift hz)
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have he := Derives.impE (.conjL (RawCodeFieldAtConstructor.constructor_at (ZFContext.under (ZFContext.add hZ E) B) 1 0 w.castSucc (fun _ => code.castSucc) row.castSucc 0 z.castSucc (Fin.last m) hw1 hr1 hz1)) (.conjL hB)
    exact of_eq (ProofAllTableRenaming.table_rename test w code Fin.castSucc).symm (table_subst test w.castSucc (Fin.last m) code.castSucc he (.conjR hB))
  · apply Derives.impI
    let E := ProofAllNodeSyntax.table test w code
    have hf := Derives.impE (.conjR (RawCodeFieldAtConstructor.constructor_at (ZFContext.add hZ E) 1 0 w (fun _ => code) row 0 z code (add hw E) (add hr E) (add hz E))) (.eqRefl code)
    apply Derives.exI code
    simpa only [ProofTreeRowLocalSyntax.fieldCheck, Formula.instantiate, Formula.rename, RawCodeFieldSyntax.field_rename,
      ProofAllTableRenaming.table_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using
      Derives.conjI hf (Derives.hyp (Γ := Context.add E Γ) (Or.inl rfl))

theorem atZero_iff {m} {Γ : Context m} (test : Formula 1) (hZ : ZFContext.Evidence Γ) (w row code : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (SyntaxNodeSyntax.constructor 1 0 w (fun _ => code) row)) :
    Derives Γ ((ProofTreeRowLocalSyntax.atZero test w row).iff (ProofAllNodeSyntax.table test w code)) := by
  apply Derives.conjI
  · apply Derives.impI
    let E := ProofTreeRowLocalSyntax.atZero test w row
    let B := (empty (Fin.last m)).conj (ProofTreeRowLocalSyntax.fieldCheck test w.castSucc row.castSucc (Fin.last m))
    let Δ := Context.add B (Context.image Formula.raise (Context.add E Γ))
    apply Derives.exE (p := B) (.hyp (Or.inl rfl))
    have hw1 := of_eq (omega_rename w Fin.castSucc) (under (add hw E) B)
    have hr1 := of_eq (SyntaxNodeSyntax.constructor_rename 1 0 w (fun _ => code) row Fin.castSucc) (under (add hr E) B)
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have ho := Derives.impE (.conjL (fieldCheck_iff test (ZFContext.under (ZFContext.add hZ E) B) w.castSucc row.castSucc code.castSucc (Fin.last m) hw1 hr1 (.conjL hB))) (.conjR hB)
    exact of_eq (ProofAllTableRenaming.table_rename test w code Fin.castSucc).symm ho
  · apply Derives.impI
    let E := ProofAllNodeSyntax.table test w code
    let B := (Formula.mem (Fin.last m) w.castSucc).conj (empty (Fin.last m))
    let Δ := Context.add B (Context.image Formula.raise (Context.add E Γ))
    apply Derives.exE (p := B) (SyntaxNumerals.exists_numeral (ZFContext.add hZ E) 0 w (add hw E))
    have hw1 := of_eq (omega_rename w Fin.castSucc) (under (add hw E) B)
    have hr1 := of_eq (SyntaxNodeSyntax.constructor_rename 1 0 w (fun _ => code) row Fin.castSucc) (under (add hr E) B)
    have ht1 := of_eq (ProofAllTableRenaming.table_rename test w code Fin.castSucc) (under (Derives.hyp (Γ := Context.add E Γ) (Or.inl rfl)) B)
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have hf := Derives.impE (.conjR (fieldCheck_iff test (ZFContext.under (ZFContext.add hZ E) B) w.castSucc row.castSucc code.castSucc (Fin.last m) hw1 hr1 (.conjR hB))) ht1
    have ho : Derives Δ (ProofTreeRowLocalSyntax.atZero test w.castSucc row.castSucc) := by
      apply Derives.exI (Fin.last m)
      simpa only [ProofTreeRowLocalSyntax.atZero, Formula.instantiate, Formula.rename, empty_rename,
        ProofTreeRowLocalSyntax.fieldCheck_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using Derives.conjI (.conjR hB) hf
    exact of_eq (ProofTreeRowLocalSyntax.atZero_rename test w row Fin.castSucc).symm ho

end PPAC.Migration.Internal.ProofTreeNodeFieldLocal
