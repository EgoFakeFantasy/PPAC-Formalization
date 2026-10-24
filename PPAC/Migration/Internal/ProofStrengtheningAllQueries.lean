import PPAC.Migration.Internal.ProofStrengtheningQueries

/-! 全部四查询按原顺序；后继自由界由对象Pairing/Union取得，最终消去。 -/
namespace PPAC.Migration.Internal.ProofStrengtheningAllQueries
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax ProofStrengtheningSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem at_successor_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z B : Fin m) (env : Fin 4 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 4 w env)) (hz : Derives Γ (empty z))
    (hs : Derives Γ (successor B (env 0))) : Derives Γ ((bundle w env).iff (atSuccessor w z B env)) := by
  have hF := ProofStrengtheningQueries.formula_iff hZ w z env hw hn hz
  have hP := ProofStrengtheningQueries.free_iff_at_successor hZ w z B env hw hn hz hs
  have hQ := ProofStrengtheningQueries.predecessorFormula_iff hZ w env hw hn
  apply Derives.conjI
  · apply Derives.impI
    let E := bundle w env
    have hE : Derives (Context.add E Γ) E := .hyp (Or.inl rfl)
    have hf := Derives.conjL hE
    have hT := ProofStrengtheningQueries.guarded_transform_iff (ZFContext.add hZ E) w z B env
      (add hw E) (add hn E) (add hz E) (add hs E) hf
    exact .conjI (.impE (add (.conjL hF) E) hf)
      (.conjI (.impE (add (.conjL hP) E) (.conjL (.conjR hE)))
        (.conjI (.impE (add (.conjL hQ) E) (.conjL (.conjR (.conjR hE))))
          (.impE (.conjL hT) (.conjR (.conjR (.conjR hE))))))
  · apply Derives.impI
    let E := atSuccessor w z B env
    have hE : Derives (Context.add E Γ) E := .hyp (Or.inl rfl)
    have hf := Derives.impE (add (.conjR hF) E) (.conjL hE)
    have hT := ProofStrengtheningQueries.guarded_transform_iff (ZFContext.add hZ E) w z B env
      (add hw E) (add hn E) (add hz E) (add hs E) hf
    exact .conjI hf (.conjI (.impE (add (.conjR hP) E) (.conjL (.conjR hE)))
      (.conjI (.impE (add (.conjR hQ) E) (.conjL (.conjR (.conjR hE))))
        (.impE (.conjR hT) (.conjR (.conjR (.conjR hE))))))

theorem bundle_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z : Fin m) (env : Fin 4 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 4 w env)) (hz : Derives Γ (empty z)) :
    Derives Γ ((bundle w env).iff (specification w z env)) := by
  apply Derives.conjI
  · apply Derives.impI
    let E := bundle w env
    let B := successor (Fin.last m) (env 0).castSucc
    let Δ := Context.add B (Context.image Formula.raise (Context.add E Γ))
    have he := InsertExistence.exists_insert (env 0) (env 0) (ZFContext.arithmetic (ZFContext.add hZ E)).base.pairing
      (ZFContext.arithmetic (ZFContext.add hZ E)).base.union
    apply Derives.exE (p := B) he
    have lift {P : Formula m} (h : Derives Γ P) : Derives Δ P.raise := under (add h E) B
    have hw1 := of_eq (omega_rename w Fin.castSucc) (lift hw)
    have hn1 := of_eq (environmentNat_rename 4 w env Fin.castSucc) (lift hn)
    have hz1 := of_eq (empty_rename z Fin.castSucc) (lift hz)
    have hs : Derives Δ B := .hyp (Or.inl rfl)
    have hE : Derives Δ (bundle w.castSucc (fun j => (env j).castSucc)) :=
      of_eq (bundle_rename w env Fin.castSucc) (under (Derives.hyp (Γ := Context.add E Γ) (Or.inl rfl)) B)
    have ha := Derives.impE (.conjL (at_successor_iff (ZFContext.under (ZFContext.add hZ E) B) _ _ _ _ hw1 hn1 hz1 hs)) hE
    have ho := intro_specification _ _ _ _ hs ha
    exact of_eq (specification_rename w z env Fin.castSucc).symm ho
  · apply Derives.impI
    let E := specification w z env
    let B := (successor (Fin.last m) (env 0).castSucc).conj (atSuccessor w.castSucc z.castSucc (Fin.last m) (fun j => (env j).castSucc))
    let Δ := Context.add B (Context.image Formula.raise (Context.add E Γ))
    apply Derives.exE (p := B) (.hyp (Or.inl rfl))
    have lift {P : Formula m} (h : Derives Γ P) : Derives Δ P.raise := under (add h E) B
    have hw1 := of_eq (omega_rename w Fin.castSucc) (lift hw)
    have hn1 := of_eq (environmentNat_rename 4 w env Fin.castSucc) (lift hn)
    have hz1 := of_eq (empty_rename z Fin.castSucc) (lift hz)
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have ho := Derives.impE (.conjR (at_successor_iff (ZFContext.under (ZFContext.add hZ E) B) _ _ _ _ hw1 hn1 hz1 (.conjL hB))) (.conjR hB)
    exact of_eq (bundle_rename w env Fin.castSucc).symm ho

end PPAC.Migration.Internal.ProofStrengtheningAllQueries
