import PPAC.Migration.Internal.LogicalAbstractSyntax

/-! 原21／24全部查询双条件；两个后继与真实Num1、码表均在对象层构造／消去。 -/
namespace PPAC.Migration.Internal.LogicalAbstractAllQueries
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax LogicalAbstractSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem at_successor21_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z A B : Fin m) (env : Fin 5 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 5 w env)) (hz : Derives Γ (empty z))
    (hA : Derives Γ (successor A z)) (hs : Derives Γ (successor B (env 0))) : Derives Γ ((bundle21 w env).iff (atSuccessor21 w z A B env)) := by
  have hF0 := LogicalAbstractQueries.formula_iff hZ (0 : Fin 5) 1 w z B env hw hn hz hs
  have hF1 := LogicalAbstractQueries.formula_iff hZ (0 : Fin 5) 2 w z B env hw hn hz hs
  apply Derives.conjI
  · apply Derives.impI
    let E := bundle21 w env
    have hE : Derives (Context.add E Γ) E := .hyp (Or.inl rfl)
    have hf0 := Derives.impE (add (Derives.conjL hF0) E) (Derives.conjL hE)
    have hf1 := Derives.impE (add (Derives.conjL hF1) E) (Derives.conjL (Derives.conjR hE))
    have hX0 := LogicalAbstractQueries.typed_transform_iff (ZFContext.add hZ E) (0 : Fin 5) 1 3 w z A B env (add hw E) (add hn E) (add hz E) (add hA E) (add hs E) hf0
    have hX1 := LogicalAbstractQueries.typed_transform_iff (ZFContext.add hZ E) (0 : Fin 5) 2 4 w z A B env (add hw E) (add hn E) (add hz E) (add hA E) (add hs E) hf1
    exact (.conjI hf0 (.conjI hf1 (.conjI (.impE (Derives.conjL hX0) (Derives.conjL (Derives.conjR (Derives.conjR hE)))) (.impE (Derives.conjL hX1) (Derives.conjR (Derives.conjR (Derives.conjR hE)))))))
  · apply Derives.impI
    let E := atSuccessor21 w z A B env
    have hE : Derives (Context.add E Γ) E := .hyp (Or.inl rfl)
    have hf0 := (Derives.conjL hE)
    have hf1 := (Derives.conjL (Derives.conjR hE))
    have hX0 := LogicalAbstractQueries.typed_transform_iff (ZFContext.add hZ E) (0 : Fin 5) 1 3 w z A B env (add hw E) (add hn E) (add hz E) (add hA E) (add hs E) hf0
    have hX1 := LogicalAbstractQueries.typed_transform_iff (ZFContext.add hZ E) (0 : Fin 5) 2 4 w z A B env (add hw E) (add hn E) (add hz E) (add hA E) (add hs E) hf1
    exact (.conjI (.impE (add (Derives.conjR hF0) E) hf0) (.conjI (.impE (add (Derives.conjR hF1) E) hf1) (.conjI (.impE (Derives.conjR hX0) (Derives.conjL (Derives.conjR (Derives.conjR hE)))) (.impE (Derives.conjR hX1) (Derives.conjR (Derives.conjR (Derives.conjR hE)))))))

theorem at_one_bundle21_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z A : Fin m) (env : Fin 5 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 5 w env)) (hz : Derives Γ (empty z))
    (hA : Derives Γ (successor A z)) :
    Derives Γ ((bundle21 w env).iff (atOneSpecification21 w z A env)) := by
  apply Derives.conjI
  · apply Derives.impI
    let E := bundle21 w env
    let B := successor (Fin.last m) (env 0).castSucc
    let Δ := Context.add B (Context.image Formula.raise (Context.add E Γ))
    have he := InsertExistence.exists_insert (env 0) (env 0) (ZFContext.arithmetic (ZFContext.add hZ E)).base.pairing
      (ZFContext.arithmetic (ZFContext.add hZ E)).base.union
    apply Derives.exE (p := B) he
    have lift {P : Formula m} (h : Derives Γ P) : Derives Δ P.raise := under (add h E) B
    have hw1 := of_eq (omega_rename w Fin.castSucc) (lift hw)
    have hn1 := of_eq (environmentNat_rename 5 w env Fin.castSucc) (lift hn)
    have hz1 := of_eq (empty_rename z Fin.castSucc) (lift hz)
    have hA1 := of_eq (successor_rename A z Fin.castSucc) (lift hA)
    have hs : Derives Δ B := .hyp (Or.inl rfl)
    have hE : Derives Δ (bundle21 w.castSucc (fun j => (env j).castSucc)) :=
      of_eq (bundle21_rename w env Fin.castSucc) (under (Derives.hyp (Γ := Context.add E Γ) (Or.inl rfl)) B)
    have ha := Derives.impE (.conjL (at_successor21_iff (ZFContext.under (ZFContext.add hZ E) B) _ _ _ _ _ hw1 hn1 hz1 hA1 hs)) hE
    have ho := intro_atOneSpecification21 _ _ _ _ _ hs ha
    exact of_eq (atOneSpecification21_rename w z A env Fin.castSucc).symm ho
  · apply Derives.impI
    let E := atOneSpecification21 w z A env
    let B := (successor (Fin.last m) (env 0).castSucc).conj (atSuccessor21 w.castSucc z.castSucc A.castSucc (Fin.last m) (fun j => (env j).castSucc))
    let Δ := Context.add B (Context.image Formula.raise (Context.add E Γ))
    apply Derives.exE (p := B) (.hyp (Or.inl rfl))
    have lift {P : Formula m} (h : Derives Γ P) : Derives Δ P.raise := under (add h E) B
    have hw1 := of_eq (omega_rename w Fin.castSucc) (lift hw)
    have hn1 := of_eq (environmentNat_rename 5 w env Fin.castSucc) (lift hn)
    have hz1 := of_eq (empty_rename z Fin.castSucc) (lift hz)
    have hA1 := of_eq (successor_rename A z Fin.castSucc) (lift hA)
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have ho := Derives.impE (.conjR (at_successor21_iff (ZFContext.under (ZFContext.add hZ E) B) _ _ _ _ _ hw1 hn1 hz1 hA1 (.conjL hB))) (.conjR hB)
    exact of_eq (bundle21_rename w env Fin.castSucc).symm ho

theorem bundle21_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z : Fin m) (env : Fin 5 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 5 w env)) (hz : Derives Γ (empty z)) :
    Derives Γ ((bundle21 w env).iff (specification21 w z env)) := by
  apply Derives.conjI
  · apply Derives.impI
    let E := bundle21 w env
    let B := successor (Fin.last m) z.castSucc
    let Δ := Context.add B (Context.image Formula.raise (Context.add E Γ))
    have he := InsertExistence.exists_insert z z (ZFContext.arithmetic (ZFContext.add hZ E)).base.pairing
      (ZFContext.arithmetic (ZFContext.add hZ E)).base.union
    apply Derives.exE (p := B) he
    have lift {P : Formula m} (h : Derives Γ P) : Derives Δ P.raise := under (add h E) B
    have hw1 := of_eq (omega_rename w Fin.castSucc) (lift hw)
    have hn1 := of_eq (environmentNat_rename 5 w env Fin.castSucc) (lift hn)
    have hz1 := of_eq (empty_rename z Fin.castSucc) (lift hz)
    have hs : Derives Δ B := .hyp (Or.inl rfl)
    have hE : Derives Δ (bundle21 w.castSucc (fun j => (env j).castSucc)) :=
      of_eq (bundle21_rename w env Fin.castSucc) (under (Derives.hyp (Γ := Context.add E Γ) (Or.inl rfl)) B)
    have ha := Derives.impE (.conjL (at_one_bundle21_iff (ZFContext.under (ZFContext.add hZ E) B) _ _ _ _ hw1 hn1 hz1 hs)) hE
    have ho := intro_specification21 _ _ _ _ hs ha
    exact of_eq (specification21_rename w z env Fin.castSucc).symm ho
  · apply Derives.impI
    let E := specification21 w z env
    let B := (successor (Fin.last m) z.castSucc).conj (atOneSpecification21 w.castSucc z.castSucc (Fin.last m) (fun j => (env j).castSucc))
    let Δ := Context.add B (Context.image Formula.raise (Context.add E Γ))
    apply Derives.exE (p := B) (.hyp (Or.inl rfl))
    have lift {P : Formula m} (h : Derives Γ P) : Derives Δ P.raise := under (add h E) B
    have hw1 := of_eq (omega_rename w Fin.castSucc) (lift hw)
    have hn1 := of_eq (environmentNat_rename 5 w env Fin.castSucc) (lift hn)
    have hz1 := of_eq (empty_rename z Fin.castSucc) (lift hz)
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have ho := Derives.impE (.conjR (at_one_bundle21_iff (ZFContext.under (ZFContext.add hZ E) B) _ _ _ _ hw1 hn1 hz1 (.conjL hB))) (.conjR hB)
    exact of_eq (bundle21_rename w env Fin.castSucc).symm ho


theorem at_successor24_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z A B : Fin m) (env : Fin 4 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 4 w env)) (hz : Derives Γ (empty z))
    (hA : Derives Γ (successor A z)) (hs : Derives Γ (successor B (env 0))) : Derives Γ ((bundle24 w env).iff (atSuccessor24 w z A B env)) := by
  have hF0 := LogicalAbstractQueries.formula_iff hZ (0 : Fin 4) 1 w z B env hw hn hz hs
  have hF1 := LogicalStaticQueries.query_iff hZ false (0 : Fin 4) 2 w z env hw hn hz
  apply Derives.conjI
  · apply Derives.impI
    let E := bundle24 w env
    have hE : Derives (Context.add E Γ) E := .hyp (Or.inl rfl)
    have hf0 := Derives.impE (add (Derives.conjL hF0) E) (Derives.conjL hE)
    have hf1 := Derives.impE (add (Derives.conjL hF1) E) (Derives.conjL (Derives.conjR hE))
    have hX0 := LogicalAbstractQueries.typed_transform_iff (ZFContext.add hZ E) (0 : Fin 4) 1 3 w z A B env (add hw E) (add hn E) (add hz E) (add hA E) (add hs E) hf0
    exact (.conjI hf0 (.conjI hf1 (.impE (Derives.conjL hX0) (Derives.conjR (Derives.conjR hE)))))
  · apply Derives.impI
    let E := atSuccessor24 w z A B env
    have hE : Derives (Context.add E Γ) E := .hyp (Or.inl rfl)
    have hf0 := (Derives.conjL hE)
    have hf1 := (Derives.conjL (Derives.conjR hE))
    have hX0 := LogicalAbstractQueries.typed_transform_iff (ZFContext.add hZ E) (0 : Fin 4) 1 3 w z A B env (add hw E) (add hn E) (add hz E) (add hA E) (add hs E) hf0
    exact (.conjI (.impE (add (Derives.conjR hF0) E) hf0) (.conjI (.impE (add (Derives.conjR hF1) E) hf1) (.impE (Derives.conjR hX0) (Derives.conjR (Derives.conjR hE)))))

theorem at_one_bundle24_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z A : Fin m) (env : Fin 4 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 4 w env)) (hz : Derives Γ (empty z))
    (hA : Derives Γ (successor A z)) :
    Derives Γ ((bundle24 w env).iff (atOneSpecification24 w z A env)) := by
  apply Derives.conjI
  · apply Derives.impI
    let E := bundle24 w env
    let B := successor (Fin.last m) (env 0).castSucc
    let Δ := Context.add B (Context.image Formula.raise (Context.add E Γ))
    have he := InsertExistence.exists_insert (env 0) (env 0) (ZFContext.arithmetic (ZFContext.add hZ E)).base.pairing
      (ZFContext.arithmetic (ZFContext.add hZ E)).base.union
    apply Derives.exE (p := B) he
    have lift {P : Formula m} (h : Derives Γ P) : Derives Δ P.raise := under (add h E) B
    have hw1 := of_eq (omega_rename w Fin.castSucc) (lift hw)
    have hn1 := of_eq (environmentNat_rename 4 w env Fin.castSucc) (lift hn)
    have hz1 := of_eq (empty_rename z Fin.castSucc) (lift hz)
    have hA1 := of_eq (successor_rename A z Fin.castSucc) (lift hA)
    have hs : Derives Δ B := .hyp (Or.inl rfl)
    have hE : Derives Δ (bundle24 w.castSucc (fun j => (env j).castSucc)) :=
      of_eq (bundle24_rename w env Fin.castSucc) (under (Derives.hyp (Γ := Context.add E Γ) (Or.inl rfl)) B)
    have ha := Derives.impE (.conjL (at_successor24_iff (ZFContext.under (ZFContext.add hZ E) B) _ _ _ _ _ hw1 hn1 hz1 hA1 hs)) hE
    have ho := intro_atOneSpecification24 _ _ _ _ _ hs ha
    exact of_eq (atOneSpecification24_rename w z A env Fin.castSucc).symm ho
  · apply Derives.impI
    let E := atOneSpecification24 w z A env
    let B := (successor (Fin.last m) (env 0).castSucc).conj (atSuccessor24 w.castSucc z.castSucc A.castSucc (Fin.last m) (fun j => (env j).castSucc))
    let Δ := Context.add B (Context.image Formula.raise (Context.add E Γ))
    apply Derives.exE (p := B) (.hyp (Or.inl rfl))
    have lift {P : Formula m} (h : Derives Γ P) : Derives Δ P.raise := under (add h E) B
    have hw1 := of_eq (omega_rename w Fin.castSucc) (lift hw)
    have hn1 := of_eq (environmentNat_rename 4 w env Fin.castSucc) (lift hn)
    have hz1 := of_eq (empty_rename z Fin.castSucc) (lift hz)
    have hA1 := of_eq (successor_rename A z Fin.castSucc) (lift hA)
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have ho := Derives.impE (.conjR (at_successor24_iff (ZFContext.under (ZFContext.add hZ E) B) _ _ _ _ _ hw1 hn1 hz1 hA1 (.conjL hB))) (.conjR hB)
    exact of_eq (bundle24_rename w env Fin.castSucc).symm ho

theorem bundle24_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z : Fin m) (env : Fin 4 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 4 w env)) (hz : Derives Γ (empty z)) :
    Derives Γ ((bundle24 w env).iff (specification24 w z env)) := by
  apply Derives.conjI
  · apply Derives.impI
    let E := bundle24 w env
    let B := successor (Fin.last m) z.castSucc
    let Δ := Context.add B (Context.image Formula.raise (Context.add E Γ))
    have he := InsertExistence.exists_insert z z (ZFContext.arithmetic (ZFContext.add hZ E)).base.pairing
      (ZFContext.arithmetic (ZFContext.add hZ E)).base.union
    apply Derives.exE (p := B) he
    have lift {P : Formula m} (h : Derives Γ P) : Derives Δ P.raise := under (add h E) B
    have hw1 := of_eq (omega_rename w Fin.castSucc) (lift hw)
    have hn1 := of_eq (environmentNat_rename 4 w env Fin.castSucc) (lift hn)
    have hz1 := of_eq (empty_rename z Fin.castSucc) (lift hz)
    have hs : Derives Δ B := .hyp (Or.inl rfl)
    have hE : Derives Δ (bundle24 w.castSucc (fun j => (env j).castSucc)) :=
      of_eq (bundle24_rename w env Fin.castSucc) (under (Derives.hyp (Γ := Context.add E Γ) (Or.inl rfl)) B)
    have ha := Derives.impE (.conjL (at_one_bundle24_iff (ZFContext.under (ZFContext.add hZ E) B) _ _ _ _ hw1 hn1 hz1 hs)) hE
    have ho := intro_specification24 _ _ _ _ hs ha
    exact of_eq (specification24_rename w z env Fin.castSucc).symm ho
  · apply Derives.impI
    let E := specification24 w z env
    let B := (successor (Fin.last m) z.castSucc).conj (atOneSpecification24 w.castSucc z.castSucc (Fin.last m) (fun j => (env j).castSucc))
    let Δ := Context.add B (Context.image Formula.raise (Context.add E Γ))
    apply Derives.exE (p := B) (.hyp (Or.inl rfl))
    have lift {P : Formula m} (h : Derives Γ P) : Derives Δ P.raise := under (add h E) B
    have hw1 := of_eq (omega_rename w Fin.castSucc) (lift hw)
    have hn1 := of_eq (environmentNat_rename 4 w env Fin.castSucc) (lift hn)
    have hz1 := of_eq (empty_rename z Fin.castSucc) (lift hz)
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have ho := Derives.impE (.conjR (at_one_bundle24_iff (ZFContext.under (ZFContext.add hZ E) B) _ _ _ _ hw1 hn1 hz1 (.conjL hB))) (.conjR hB)
    exact of_eq (bundle24_rename w env Fin.castSucc).symm ho


end PPAC.Migration.Internal.LogicalAbstractAllQueries
