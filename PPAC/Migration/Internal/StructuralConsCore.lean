import PPAC.Migration.Internal.StructuralConsAt

/-! 消去隐藏的零/单位见证，构造原Cons，并保持全部内部自然输入。 -/
namespace PPAC.Migration.Internal.StructuralConsCore
open Source SourceAlgebra SourceLogic OmegaSyntax StructuralListSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem specialize {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z e h t n : Fin m)
    (hz : Derives Γ (empty z)) (he : Derives Γ (successor e z)) (hn : Derives Γ (consCode w h t n)) : Derives Γ (consAt w e h t n) := by
  let C := consUnits w h t n
  let Δ := Context.add C (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply eliminate_cons w h t n _ hn
  have hZ2 : ZFContext.Evidence Δ := ZFContext.under_two hZ C
  have hz2 : Derives Δ (empty z.castSucc.castSucc) := by simpa only [Formula.raise, empty_rename] using OrderedPairElimination.under_two hz C
  have he2 : Derives Δ (successor e.castSucc.castSucc z.castSucc.castSucc) := by simpa only [Formula.raise, successor_rename] using OrderedPairElimination.under_two he C
  have hC : Derives Δ C := .hyp (Or.inl rfl)
  have hef := StructuralListUnits.unique hZ2 _ _ _ _ (.conjL hC) (.conjL (.conjR hC)) hz2 he2
  have hout := consAt_tag_subst _ _ _ _ _ _ hef (.conjR (.conjR hC))
  simpa only [Formula.raise, consAt_rename] using hout

theorem tag_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z e h t n : Fin m)
    (hz : Derives Γ (empty z)) (he : Derives Γ (successor e z)) : Derives Γ ((consCode w h t n).iff (consAt w e h t n)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact specialize (ZFContext.add hZ _) _ _ _ _ _ _ (add hz _) (add he _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact intro_cons _ _ _ _ _ _ (add hz _) (add he _) (.hyp (Or.inl rfl))

theorem range {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w h t n : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (consCode w h t n)) : Derives Γ (.mem n w) := by
  let C := consUnits w h t n
  let Δ := Context.add C (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply eliminate_cons w h t n _ hn
  have hZ2 : ZFContext.Evidence Δ := ZFContext.under_two hZ C
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using OrderedPairElimination.under_two hw C
  have hC : Derives Δ C := .hyp (Or.inl rfl)
  exact StructuralConsAt.range hZ2 _ _ _ _ _ hw2 (.conjR (.conjR hC))

theorem positive {m} {Γ : Context m} (w h t n : Fin m) (hn : Derives Γ (consCode w h t n)) : Derives Γ (empty n).neg := by
  let C := consUnits w h t n
  let Δ := Context.add C (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply eliminate_cons w h t n _ hn
  have hC : Derives Δ C := .hyp (Or.inl rfl)
  have hout := StructuralConsAt.positive _ _ _ _ _ (.conjR (.conjR hC))
  simpa only [Formula.raise, Formula.neg, Formula.rename, empty_rename] using hout

theorem components {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w h t n : Fin m)
    (hw : Derives Γ (omega w)) (hh : Derives Γ (.mem h w)) (ht : Derives Γ (.mem t w)) (hn : Derives Γ (consCode w h t n)) :
    Derives Γ ((Formula.mem h n).conj (.mem t n)) := by
  let C := consUnits w h t n
  let Δ := Context.add C (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply eliminate_cons w h t n _ hn
  have hZ2 : ZFContext.Evidence Δ := ZFContext.under_two hZ C
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using OrderedPairElimination.under_two hw C
  have hC : Derives Δ C := .hyp (Or.inl rfl)
  have heW := StructuralListUnits.member hZ2 _ _ _ hw2 (.conjL hC) (.conjL (.conjR hC))
  exact StructuralConsAt.components hZ2 _ _ _ _ _ hw2 heW (OrderedPairElimination.under_two hh C) (OrderedPairElimination.under_two ht C) (.conjR (.conjR hC))

theorem intro_existsCons {m} {Γ : Context m} (w h t n : Fin m) (hn : Derives Γ (.mem n w))
    (hc : Derives Γ (consCode w h t n)) : Derives Γ (existsCons w h t) := by
  apply Derives.exI n
  simp only [Formula.instantiate, Formula.rename, consCode_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact .conjI hn hc

theorem exists_with_units {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z e h t : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) (he : Derives Γ (successor e z)) (hh : Derives Γ (.mem h w)) (ht : Derives Γ (.mem t w)) :
    Derives Γ (existsCons w h t) := by
  have heW := StructuralListUnits.member hZ w z e hw hz he
  have hq := GodelPairCore.exists_code hZ w h t hw hh ht
  let Q := (Formula.mem (Fin.last m) w.castSucc).conj (GodelPairSyntax.code w.castSucc h.castSucc t.castSucc (Fin.last m))
  let Ξ := Context.add Q (Context.image Formula.raise Γ)
  change Derives Γ (.ex Q) at hq
  apply Derives.exE (p := Q) hq
  have hZ1 : ZFContext.Evidence Ξ := ZFContext.under hZ Q
  have hw1 : Derives Ξ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw Q
  have hQ : Derives Ξ Q := .hyp (Or.inl rfl)
  have hn := StructuralNodeExistence.exists_raw hZ1 w.castSucc e.castSucc (Fin.last m) hw1 (under heW Q) (.conjL hQ)
  let N := (Formula.mem (Fin.last (m+1)) w.castSucc.castSucc).conj (StructuralNodeSyntax.raw w.castSucc.castSucc e.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)))
  let Δ := Context.add N (Context.image Formula.raise Ξ)
  change Derives Ξ (.ex N) at hn
  apply Derives.exE (p := N) hn
  have hQ2 : Derives Δ ((Formula.mem (Fin.last m).castSucc w.castSucc.castSucc).conj
      (GodelPairSyntax.code w.castSucc.castSucc h.castSucc.castSucc t.castSucc.castSucc (Fin.last m).castSucc)) := by
    simpa only [Q, Formula.raise, Formula.rename, GodelPairSyntax.code_rename] using under hQ N
  have hz2 : Derives Δ (empty z.castSucc.castSucc) := by simpa only [Formula.raise, empty_rename] using under (under hz Q) N
  have he2 : Derives Δ (successor e.castSucc.castSucc z.castSucc.castSucc) := by simpa only [Formula.raise, successor_rename] using under (under he Q) N
  have hN : Derives Δ N := .hyp (Or.inl rfl)
  have hc := intro_cons _ _ _ _ _ _ hz2 he2 (intro_consAt _ _ _ _ _ _ (.conjR hQ2) (.conjR hN))
  have hout := intro_existsCons _ _ _ _ (.conjL hN) hc
  simpa only [Formula.raise, existsCons_rename] using hout

theorem exists_cons {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w h t : Fin m)
    (hw : Derives Γ (omega w)) (hh : Derives Γ (.mem h w)) (ht : Derives Γ (.mem t w)) : Derives Γ (existsCons w h t) := by
  let U := unitWitness m
  let Δ := Context.add U (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply StructuralListUnits.with_units w _ hw
  have hZ2 : ZFContext.Evidence Δ := ZFContext.under_two hZ U
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using OrderedPairElimination.under_two hw U
  have hU : Derives Δ U := .hyp (Or.inl rfl)
  have hout := exists_with_units hZ2 _ _ _ _ _ hw2 (.conjL hU) (.conjR hU) (OrderedPairElimination.under_two hh U) (OrderedPairElimination.under_two ht U)
  simpa only [Formula.raise, existsCons_rename] using hout
end PPAC.Migration.Internal.StructuralConsCore
