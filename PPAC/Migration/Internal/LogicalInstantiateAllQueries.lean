import PPAC.Migration.Internal.LogicalInstantiateSyntax

/-! 原逻辑20／23／25的查询完整双条件；实际Num2与bound1后继见证均对象构造并消去。 -/
namespace PPAC.Migration.Internal.LogicalInstantiateAllQueries
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax LogicalInstantiateSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem at_bound4_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z A : Fin m) (env : Fin 4 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 4 w env)) (hz : Derives Γ (empty z))
    (hA : Derives Γ (successor A z)) : Derives Γ ((bundle4 w env).iff (atBound4 w z A env)) := by
  have hF := LogicalInstantiateQueries.formula_iff hZ (0 : Fin 4) 1 w z A env hw hn hz hA
  have hT0 := LogicalInstantiateQueries.term_iff hZ (0 : Fin 4) 2 w z env hw hn hz
  apply Derives.conjI
  · apply Derives.impI
    let E := bundle4 w env
    have hE : Derives (Context.add E Γ) E := .hyp (Or.inl rfl)
    have hf := Derives.impE (add (Derives.conjL hF) E) (Derives.conjL hE)
    have ht0 := Derives.impE (add (Derives.conjL hT0) E) (Derives.conjL (Derives.conjR hE))
    have hX0 := LogicalInstantiateQueries.typed_transform_iff (ZFContext.add hZ E) (0 : Fin 4) 2 1 3 w z A env (add hw E) (add hn E) (add hz E) (add hA E) ht0 hf
    exact .conjI hf (.conjI ht0 ((.impE (Derives.conjL hX0) (Derives.conjR (Derives.conjR hE)))))
  · apply Derives.impI
    let E := atBound4 w z A env
    have hE : Derives (Context.add E Γ) E := .hyp (Or.inl rfl)
    have hf := (Derives.conjL hE)
    have ht0 := (Derives.conjL (Derives.conjR hE))
    have hX0 := LogicalInstantiateQueries.typed_transform_iff (ZFContext.add hZ E) (0 : Fin 4) 2 1 3 w z A env (add hw E) (add hn E) (add hz E) (add hA E) ht0 hf
    exact .conjI (.impE (add (Derives.conjR hF) E) hf) (.conjI (.impE (add (Derives.conjR hT0) E) ht0) ((.impE (Derives.conjR hX0) (Derives.conjR (Derives.conjR hE)))))

theorem bundle4_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z : Fin m) (env : Fin 4 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 4 w env)) (hz : Derives Γ (empty z)) :
    Derives Γ ((bundle4 w env).iff (specification4 w z env)) := by
  apply Derives.conjI
  · apply Derives.impI
    let E := bundle4 w env
    let B := successor (Fin.last m) z.castSucc
    let Δ := Context.add B (Context.image Formula.raise (Context.add E Γ))
    apply Derives.exE (p := B) (InsertExistence.exists_insert z z (ZFContext.arithmetic (ZFContext.add hZ E)).base.pairing (ZFContext.arithmetic (ZFContext.add hZ E)).base.union)
    have lift {p : Formula m} (h : Derives Γ p) : Derives Δ p.raise := under (add h E) B
    have hw1 := of_eq (omega_rename w Fin.castSucc) (lift hw)
    have hn1 := of_eq (environmentNat_rename 4 w env Fin.castSucc) (lift hn)
    have hz1 := of_eq (empty_rename z Fin.castSucc) (lift hz)
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have hE : Derives Δ (bundle4 w.castSucc (fun i => (env i).castSucc)) := of_eq (bundle4_rename w env Fin.castSucc) (under (Derives.hyp (Γ := Context.add E Γ) (Or.inl rfl)) B)
    have hs := Derives.impE (Derives.conjL (at_bound4_iff (ZFContext.under (ZFContext.add hZ E) B) _ _ _ _ hw1 hn1 hz1 hB)) hE
    exact of_eq (specification4_rename w z env Fin.castSucc).symm (intro_specification4 _ _ _ _ hB hs)
  · apply Derives.impI
    let E := specification4 w z env
    let B := (successor (Fin.last m) z.castSucc).conj (atBound4 w.castSucc z.castSucc (Fin.last m) (fun i => (env i).castSucc))
    let Δ := Context.add B (Context.image Formula.raise (Context.add E Γ))
    apply Derives.exE (p := B) (.hyp (Or.inl rfl))
    have lift {p : Formula m} (h : Derives Γ p) : Derives Δ p.raise := under (add h E) B
    have hw1 := of_eq (omega_rename w Fin.castSucc) (lift hw)
    have hn1 := of_eq (environmentNat_rename 4 w env Fin.castSucc) (lift hn)
    have hz1 := of_eq (empty_rename z Fin.castSucc) (lift hz)
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have ho := Derives.impE (Derives.conjR (at_bound4_iff (ZFContext.under (ZFContext.add hZ E) B) _ _ _ _ hw1 hn1 hz1 (Derives.conjL hB))) (Derives.conjR hB)
    exact of_eq (bundle4_rename w env Fin.castSucc).symm ho

theorem at_bound6_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z A : Fin m) (env : Fin 6 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 6 w env)) (hz : Derives Γ (empty z))
    (hA : Derives Γ (successor A z)) : Derives Γ ((bundle6 w env).iff (atBound6 w z A env)) := by
  have hF := LogicalInstantiateQueries.formula_iff hZ (0 : Fin 6) 3 w z A env hw hn hz hA
  have hT0 := LogicalInstantiateQueries.term_iff hZ (0 : Fin 6) 1 w z env hw hn hz
  have hT1 := LogicalInstantiateQueries.term_iff hZ (0 : Fin 6) 2 w z env hw hn hz
  apply Derives.conjI
  · apply Derives.impI
    let E := bundle6 w env
    have hE : Derives (Context.add E Γ) E := .hyp (Or.inl rfl)
    have hf := Derives.impE (add (Derives.conjL hF) E) (Derives.conjL (Derives.conjR (Derives.conjR hE)))
    have ht0 := Derives.impE (add (Derives.conjL hT0) E) (Derives.conjL hE)
    have ht1 := Derives.impE (add (Derives.conjL hT1) E) (Derives.conjL (Derives.conjR hE))
    have hX0 := LogicalInstantiateQueries.typed_transform_iff (ZFContext.add hZ E) (0 : Fin 6) 1 3 4 w z A env (add hw E) (add hn E) (add hz E) (add hA E) ht0 hf
    have hX1 := LogicalInstantiateQueries.typed_transform_iff (ZFContext.add hZ E) (0 : Fin 6) 2 3 5 w z A env (add hw E) (add hn E) (add hz E) (add hA E) ht1 hf
    exact .conjI ht0 (.conjI ht1 (.conjI hf (.conjI (.impE (Derives.conjL hX0) (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR hE))))) ((.impE (Derives.conjL hX1) (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hE)))))))))
  · apply Derives.impI
    let E := atBound6 w z A env
    have hE : Derives (Context.add E Γ) E := .hyp (Or.inl rfl)
    have hf := (Derives.conjL (Derives.conjR (Derives.conjR hE)))
    have ht0 := (Derives.conjL hE)
    have ht1 := (Derives.conjL (Derives.conjR hE))
    have hX0 := LogicalInstantiateQueries.typed_transform_iff (ZFContext.add hZ E) (0 : Fin 6) 1 3 4 w z A env (add hw E) (add hn E) (add hz E) (add hA E) ht0 hf
    have hX1 := LogicalInstantiateQueries.typed_transform_iff (ZFContext.add hZ E) (0 : Fin 6) 2 3 5 w z A env (add hw E) (add hn E) (add hz E) (add hA E) ht1 hf
    exact .conjI (.impE (add (Derives.conjR hT0) E) ht0) (.conjI (.impE (add (Derives.conjR hT1) E) ht1) (.conjI (.impE (add (Derives.conjR hF) E) hf) (.conjI (.impE (Derives.conjR hX0) (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR hE))))) ((.impE (Derives.conjR hX1) (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hE)))))))))

theorem bundle6_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z : Fin m) (env : Fin 6 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 6 w env)) (hz : Derives Γ (empty z)) :
    Derives Γ ((bundle6 w env).iff (specification6 w z env)) := by
  apply Derives.conjI
  · apply Derives.impI
    let E := bundle6 w env
    let B := successor (Fin.last m) z.castSucc
    let Δ := Context.add B (Context.image Formula.raise (Context.add E Γ))
    apply Derives.exE (p := B) (InsertExistence.exists_insert z z (ZFContext.arithmetic (ZFContext.add hZ E)).base.pairing (ZFContext.arithmetic (ZFContext.add hZ E)).base.union)
    have lift {p : Formula m} (h : Derives Γ p) : Derives Δ p.raise := under (add h E) B
    have hw1 := of_eq (omega_rename w Fin.castSucc) (lift hw)
    have hn1 := of_eq (environmentNat_rename 6 w env Fin.castSucc) (lift hn)
    have hz1 := of_eq (empty_rename z Fin.castSucc) (lift hz)
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have hE : Derives Δ (bundle6 w.castSucc (fun i => (env i).castSucc)) := of_eq (bundle6_rename w env Fin.castSucc) (under (Derives.hyp (Γ := Context.add E Γ) (Or.inl rfl)) B)
    have hs := Derives.impE (Derives.conjL (at_bound6_iff (ZFContext.under (ZFContext.add hZ E) B) _ _ _ _ hw1 hn1 hz1 hB)) hE
    exact of_eq (specification6_rename w z env Fin.castSucc).symm (intro_specification6 _ _ _ _ hB hs)
  · apply Derives.impI
    let E := specification6 w z env
    let B := (successor (Fin.last m) z.castSucc).conj (atBound6 w.castSucc z.castSucc (Fin.last m) (fun i => (env i).castSucc))
    let Δ := Context.add B (Context.image Formula.raise (Context.add E Γ))
    apply Derives.exE (p := B) (.hyp (Or.inl rfl))
    have lift {p : Formula m} (h : Derives Γ p) : Derives Δ p.raise := under (add h E) B
    have hw1 := of_eq (omega_rename w Fin.castSucc) (lift hw)
    have hn1 := of_eq (environmentNat_rename 6 w env Fin.castSucc) (lift hn)
    have hz1 := of_eq (empty_rename z Fin.castSucc) (lift hz)
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have ho := Derives.impE (Derives.conjR (at_bound6_iff (ZFContext.under (ZFContext.add hZ E) B) _ _ _ _ hw1 hn1 hz1 (Derives.conjL hB))) (Derives.conjR hB)
    exact of_eq (bundle6_rename w env Fin.castSucc).symm ho

end PPAC.Migration.Internal.LogicalInstantiateAllQueries
