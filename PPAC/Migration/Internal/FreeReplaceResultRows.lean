import PPAC.Migration.Internal.FreeReplaceResultSyntax

/-! 原mode3五字段行码的实际构造、深度自然性及闭轨迹执行判据。 -/
namespace PPAC.Migration.Internal.FreeReplaceResultRows
open Source SourceAlgebra SourceLogic OmegaSyntax FreeReplaceResultSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem exists_root {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w d p x y : Fin m)
    (hw : Derives Γ (omega w)) (hd : Derives Γ (.mem d w)) (hp : Derives Γ (.mem p w))
    (hx : Derives Γ (.mem x w)) (hy : Derives Γ (.mem y w)) : Derives Γ (existsRoot w d p x y) := by
  have he := SyntaxNumerals.exists_numeral hZ 3 w hw
  let M := (Formula.mem (Fin.last m) w.castSucc).conj (SyntaxNumeralSyntax.numeral 3 (Fin.last m))
  let Δ := Context.add M (Context.image Formula.raise Γ)
  apply Derives.exE (p := M) he
  have hZ1 := ZFContext.under hZ M
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw M)
  have hM : Derives Δ M := .hyp (Or.inl rfl)
  have hn : ∀ i, Derives Δ (.mem (HornRowFields.five (Fin.last m) d.castSucc p.castSucc x.castSucc y.castSucc i) w.castSucc) :=
    fun i => Fin.cases (.conjL hM) (fun a => Fin.cases (under hd M) (fun b => Fin.cases (under hp M) (fun c => Fin.cases (under hx M) (fun _ => under hy M) c) b) a) i
  have hc := SyntaxConstructors.exists_constructor hZ1 5 1 w.castSucc _ hw1 (SyntaxForestSyntax.intro_inputs 5 _ _ hn)
  let C := (Formula.mem (Fin.last (m+1)) w.castSucc.castSucc).conj
    (SyntaxNodeSyntax.constructor 5 1 w.castSucc.castSucc (HornRowFields.five (Fin.last m).castSucc d.castSucc.castSucc p.castSucc.castSucc x.castSucc.castSucc y.castSucc.castSucc) (Fin.last (m+1)))
  let Ξ := Context.add C (Context.image Formula.raise Δ)
  apply Derives.exE (p := C) hc
  have hM1 : Derives Ξ ((Formula.mem (Fin.last m).castSucc w.castSucc.castSucc).conj (SyntaxNumeralSyntax.numeral 3 (Fin.last m).castSucc)) := of_eq
    (by simp only [M, Formula.raise, Formula.rename, SyntaxNumeralSyntax.numeral_rename]) (under hM C)
  have hC : Derives Ξ C := .hyp (Or.inl rfl)
  have hr := intro_root _ _ _ _ _ _ _ (.conjR hM1) (.conjR hC)
  have ho : Derives Ξ (existsRoot w.castSucc.castSucc d.castSucc.castSucc p.castSucc.castSucc x.castSucc.castSucc y.castSucc.castSucc) := by
    apply Derives.exI (Fin.last (m+1))
    exact of_eq (by simp only [Formula.instantiate, Formula.rename, root_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI (.conjL hC) hr)
  simpa only [Formula.raise, existsRoot_rename] using ho

theorem depth_natural {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w d p x y r : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (root w d p x y r)) : Derives Γ (.mem d w) := by
  let B := (SyntaxNumeralSyntax.numeral 3 (Fin.last m)).conj
    (SyntaxNodeSyntax.constructor 5 1 w.castSucc (HornRowFields.five (Fin.last m) d.castSucc p.castSucc x.castSucc y.castSucc) r.castSucc)
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) hr
  have hZ1 := ZFContext.under hZ B
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hn := SyntaxNodeInjective.constructor_range hZ1 5 1 _ _ _ hw1 (.conjR hB)
  exact StructuralListTraceOrder.member_member hZ1 w.castSucc d.castSucc r.castSucc hw1 hn (SyntaxConstructors.child_member hZ1 5 1 _ _ _ 1 hw1 (.conjR hB))

theorem trace_iff_execution {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w d p x idx y r : Fin m)
    (hw : Derives Γ (omega w)) (hv : Derives Γ (SyntaxVariableSyntax.code false w idx x))
    (hr : Derives Γ (root w d p x y r)) :
    Derives Γ ((HornLookupConditionSyntax.condition w r).iff (LookupTableExecutionSyntax.executed w p idx y)) := by
  let B := (SyntaxNumeralSyntax.numeral 3 (Fin.last m)).conj
    (SyntaxNodeSyntax.constructor 5 1 w.castSucc (HornRowFields.five (Fin.last m) d.castSucc p.castSucc x.castSucc y.castSucc) r.castSucc)
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) hr
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw B)
  have hv1 : Derives Δ (SyntaxVariableSyntax.code false w.castSucc idx.castSucc x.castSucc) := of_eq (SyntaxVariableSyntax.code_rename false w idx x Fin.castSucc) (under hv B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have ho := OriginalFreeReplace.trace_iff_execution (ZFContext.under hZ B) w.castSucc r.castSucc idx.castSucc _ hw1 (.conjR hB) (.conjL hB) hv1
  have h2 : HornRowFields.five (Fin.last m) d.castSucc p.castSucc x.castSucc y.castSucc (2 : Fin 5) = p.castSucc := rfl
  have h4 : HornRowFields.five (Fin.last m) d.castSucc p.castSucc x.castSucc y.castSucc (4 : Fin 5) = y.castSucc := rfl
  rw [h2, h4] at ho
  simpa only [Formula.raise, Formula.iff, Formula.rename, HornLookupConditionSyntax.condition_rename, LookupTableExecutionSyntax.executed_rename] using ho

end PPAC.Migration.Internal.FreeReplaceResultRows
