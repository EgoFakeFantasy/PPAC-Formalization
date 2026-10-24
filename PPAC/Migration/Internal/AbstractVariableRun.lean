import PPAC.Migration.Internal.OriginalTransformRowSyntax
import PPAC.Migration.Internal.OriginalTermTraceSyntax
import PPAC.Migration.Internal.AbstractVariableNumeric

/-! 原mode1整条变量运行的数值双条件；实际原五字段行在对象EX内构造并消去。 -/
namespace PPAC.Migration.Internal.AbstractVariableRun
open Source SourceAlgebra SourceLogic OmegaSyntax AbstractVariableValueSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem trace_iff_value {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (bound : Bool) (w r idx : Fin m)
    (xs : Fin 5 → Fin m) (hw : Derives Γ (omega w)) (hc : Derives Γ (SyntaxNodeSyntax.constructor 5 1 w xs r))
    (hm : Derives Γ (SyntaxNumeralSyntax.numeral 1 (xs 0))) (hv : Derives Γ (SyntaxVariableSyntax.code bound w idx (xs 3))) :
    Derives Γ ((HornLookupConditionSyntax.condition w r).iff (valueSpec bound w (xs 1) idx (xs 3) (xs 4))) := by
  cases bound with
  | false => exact AbstractVariableNumeric.free_iff hZ w r idx xs hw hc hm hv
  | true => exact AbstractVariableNumeric.bound_iff hZ w r idx xs hw hc hm hv

theorem output_natural {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (bound : Bool) (w d i x y : Fin m)
    (hw : Derives Γ (omega w)) (hx : Derives Γ (.mem x w)) (hv : Derives Γ (valueSpec bound w d i x y)) : Derives Γ (.mem y w) := by
  cases bound with
  | true =>
    apply Derives.disjE hv
    · exact mem_subst (eq_symm (.conjR (Derives.hyp (Or.inl rfl)))) (add hx _)
    · let E := boundShifted w d i y
      let B := (successor (Fin.last m) i.castSucc).conj ((Formula.mem d.castSucc (Fin.last m)).conj
        (SyntaxVariableSyntax.code true w.castSucc (Fin.last m) y.castSucc))
      let Δ := Context.add B (Context.image Formula.raise (Context.add E Γ))
      apply Derives.exE (p := B) (.hyp (Or.inl rfl))
      have hw1 := of_eq (omega_rename w Fin.castSucc) (under (add hw E) B)
      have hB : Derives Δ B := .hyp (Or.inl rfl)
      exact HornVariableValue.code_natural (ZFContext.under (ZFContext.add hZ E) B) true _ _ _ hw1 (.conjR (.conjR hB))
  | false =>
    apply Derives.disjE hv
    · exact HornVariableValue.code_natural (ZFContext.add hZ _) true w d y (add hw _) (.conjR (.hyp (Or.inl rfl)))
    · let E := freeTail w i y
      let B := (successor i.castSucc (Fin.last m)).conj (SyntaxVariableSyntax.code false w.castSucc (Fin.last m) y.castSucc)
      let Δ := Context.add B (Context.image Formula.raise (Context.add E Γ))
      apply Derives.exE (p := B) (.hyp (Or.inl rfl))
      have hw1 := of_eq (omega_rename w Fin.castSucc) (under (add hw E) B)
      have hB : Derives Δ B := .hyp (Or.inl rfl)
      exact HornVariableValue.code_natural (ZFContext.under (ZFContext.add hZ E) B) false _ _ _ hw1 (.conjR hB)

theorem run_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (bound : Bool) (w mode depth P x idx y : Fin m)
    (hw : Derives Γ (omega w)) (hm : Derives Γ (SyntaxNumeralSyntax.numeral 1 mode))
    (hd : Derives Γ (OriginalTermTraceSyntax.metadata w depth P)) (hv : Derives Γ (SyntaxVariableSyntax.code bound w idx x)) :
    Derives Γ ((OriginalTransformRowSyntax.run 1 w mode depth P x y).iff (valueSpec bound w depth idx x y)) := by
  apply Derives.conjI
  · apply Derives.impI
    let E := OriginalTransformRowSyntax.run 1 w mode depth P x y
    let B := (OriginalTransformRowSyntax.row 1 w.castSucc mode.castSucc depth.castSucc P.castSucc x.castSucc y.castSucc (Fin.last m)).conj
      (HornLookupConditionSyntax.condition w.castSucc (Fin.last m))
    let Δ := Context.add B (Context.image Formula.raise (Context.add E Γ))
    apply Derives.exE (p := B) (.hyp (Or.inl rfl))
    have hw1 := of_eq (omega_rename w Fin.castSucc) (under (add hw E) B)
    have hm1 := of_eq (SyntaxNumeralSyntax.numeral_rename 1 mode Fin.castSucc) (under (add hm E) B)
    have hv1 := of_eq (SyntaxVariableSyntax.code_rename bound w idx x Fin.castSucc) (under (add hv E) B)
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have he := trace_iff_value (ZFContext.under (ZFContext.add hZ E) B) bound w.castSucc (Fin.last m) idx.castSucc
      (HornRowFields.five mode.castSucc depth.castSucc P.castSucc x.castSucc y.castSucc) hw1 (.conjL hB) hm1 hv1
    have ho := Derives.impE (.conjL he) (.conjR hB)
    exact of_eq (valueSpec_rename bound w depth idx x y Fin.castSucc).symm ho
  · apply Derives.impI
    let E := valueSpec bound w depth idx x y
    have hE : Derives (Context.add E Γ) E := .hyp (Or.inl rfl)
    have hx := HornVariableValue.code_natural hZ bound w idx x hw hv
    have hy := output_natural (ZFContext.add hZ E) bound w depth idx x y (add hw E) (add hx E) hE
    have hmode := SyntaxNumerals.range (ZFContext.add hZ E) 1 w mode (add hw E) (add hm E)
    have hinputs := SyntaxForestSyntax.intro_inputs 5 w (HornRowFields.five mode depth P x y)
      (Fin.cases hmode (Fin.cases (add (.conjL hd) E) (Fin.cases (add (.conjR hd) E) (Fin.cases (add hx E) (Fin.cases hy (fun z => Fin.elim0 z))))))
    let B := (Formula.mem (Fin.last m) w.castSucc).conj
      (OriginalTransformRowSyntax.row 1 w.castSucc mode.castSucc depth.castSucc P.castSucc x.castSucc y.castSucc (Fin.last m))
    let Δ := Context.add B (Context.image Formula.raise (Context.add E Γ))
    apply Derives.exE (p := B) (SyntaxConstructors.exists_constructor (ZFContext.add hZ E) 5 1 w (HornRowFields.five mode depth P x y) (add hw E) hinputs)
    have hw1 := of_eq (omega_rename w Fin.castSucc) (under (add hw E) B)
    have hm1 := of_eq (SyntaxNumeralSyntax.numeral_rename 1 mode Fin.castSucc) (under (add hm E) B)
    have hv1 := of_eq (SyntaxVariableSyntax.code_rename bound w idx x Fin.castSucc) (under (add hv E) B)
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have hvalue := of_eq (valueSpec_rename bound w depth idx x y Fin.castSucc) (under hE B)
    have he := trace_iff_value (ZFContext.under (ZFContext.add hZ E) B) bound w.castSucc (Fin.last m) idx.castSucc
      (HornRowFields.five mode.castSucc depth.castSucc P.castSucc x.castSucc y.castSucc) hw1 (.conjR hB) hm1 hv1
    have ht := Derives.impE (.conjR he) hvalue
    have ho := OriginalTransformRowSyntax.intro_run 1 _ _ _ _ _ _ _ (.conjR hB) ht
    exact of_eq (OriginalTransformRowSyntax.run_rename 1 w mode depth P x y Fin.castSucc).symm ho

end PPAC.Migration.Internal.AbstractVariableRun
