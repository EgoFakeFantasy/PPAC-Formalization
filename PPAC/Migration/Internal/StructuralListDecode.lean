import PPAC.Migration.Internal.StructuralListTraceInvert

/-! 纯对象有效列表的Nil/Cons双向递归式、有效尾反射和零码排除。 -/
namespace PPAC.Migration.Internal.StructuralListDecode
open Source SourceAlgebra SourceLogic OmegaSyntax StructuralListSyntax StructuralListTraceSyntax StructuralListDecodeSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem from_tail {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (tailCase w n)) : Derives Γ (valid w n) := by
  let T := (valid w.castSucc (Fin.last m)).conj (step w.castSucc (Fin.last m) n.castSucc)
  let Ξ := Context.add T (Context.image Formula.raise Γ)
  change Derives Γ (.ex T) at hn
  apply Derives.exE (p := T) hn
  have hT : Derives Ξ T := .hyp (Or.inl rfl)
  let H := (Formula.mem (Fin.last (m+1)) w.castSucc.castSucc).conj (consCode w.castSucc.castSucc (Fin.last (m+1)) (Fin.last m).castSucc n.castSucc.castSucc)
  let Δ := Context.add H (Context.image Formula.raise Ξ)
  have hh : Derives Ξ (.ex H) := .conjR hT
  apply Derives.exE (p := H) hh
  have hZ2 : ZFContext.Evidence Δ := ZFContext.under (ZFContext.under hZ T) H
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using under (under hw T) H
  have hv2 : Derives Δ (valid w.castSucc.castSucc (Fin.last m).castSucc) := by simpa only [Formula.raise, valid_rename] using under (Derives.conjL hT) H
  have hH : Derives Δ H := .hyp (Or.inl rfl)
  have hout := StructuralListValidity.cons_valid hZ2 _ _ _ _ hw2 (.conjL hH) hv2 (.conjR hH)
  simpa only [Formula.raise, valid_rename] using hout

theorem fold {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (decomposition w n)) : Derives Γ (valid w n) := by
  apply Derives.disjE hn
  · exact StructuralListTraceBase.valid_nil (ZFContext.add hZ _) _ _ (add hw _) (.hyp (Or.inl rfl))
  · exact from_tail (ZFContext.add hZ _) _ _ (add hw _) (.hyp (Or.inl rfl))

theorem recursive_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n : Fin m)
    (hw : Derives Γ (omega w)) : Derives Γ ((valid w n).iff (decomposition w n)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact StructuralListTraceInvert.valid_decomposition (ZFContext.add hZ _) _ _ (add hw _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact fold (ZFContext.add hZ _) _ _ (add hw _) (.hyp (Or.inl rfl))

theorem nil_positive {m} {Γ : Context m} (w n : Fin m) (hn : Derives Γ (nilCode w n)) : Derives Γ (empty n).neg := by
  let N := nilWitness w n
  let Δ := Context.add N (Context.image Formula.raise Γ)
  apply eliminate_nil w n _ hn
  have hN : Derives Δ N := .hyp (Or.inl rfl)
  have hout := StructuralNodeProperties.positive _ _ _ _ (.conjR hN)
  simpa only [Formula.raise, Formula.neg, Formula.rename, empty_rename] using hout

theorem step_positive {m} {Γ : Context m} (w a b : Fin m) (hs : Derives Γ (step w a b)) : Derives Γ (empty b).neg := by
  let H := (Formula.mem (Fin.last m) w.castSucc).conj (consCode w.castSucc (Fin.last m) a.castSucc b.castSucc)
  let Δ := Context.add H (Context.image Formula.raise Γ)
  change Derives Γ (.ex H) at hs
  apply Derives.exE (p := H) hs
  have hH : Derives Δ H := .hyp (Or.inl rfl)
  have hout := StructuralConsCore.positive _ _ _ _ (.conjR hH)
  simpa only [Formula.raise, Formula.neg, Formula.rename, empty_rename] using hout

theorem positive {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (valid w n)) : Derives Γ (empty n).neg := by
  have hd := StructuralListTraceInvert.valid_decomposition hZ w n hw hn
  apply Derives.disjE hd
  · exact nil_positive _ _ (.hyp (Or.inl rfl))
  · let P := tailCase w n
    let Γp := Context.add P Γ
    let T := (valid w.castSucc (Fin.last m)).conj (step w.castSucc (Fin.last m) n.castSucc)
    let Δ := Context.add T (Context.image Formula.raise Γp)
    have ht : Derives Γp (.ex T) := .hyp (Or.inl rfl)
    apply Derives.exE (p := T) ht
    have hT : Derives Δ T := .hyp (Or.inl rfl)
    have hout := step_positive _ _ _ (.conjR hT)
    simpa only [Formula.raise, Formula.neg, Formula.rename, empty_rename] using hout

theorem zero_rejected {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) : Derives Γ (valid w z).neg := by
  apply Derives.impI
  exact .impE (positive (ZFContext.add hZ _) w z (add hw _) (.hyp (Or.inl rfl))) (add hz _)

theorem tail_valid {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w h t n : Fin m)
    (hw : Derives Γ (omega w)) (hh : Derives Γ (.mem h w)) (ht : Derives Γ (.mem t w))
    (hc : Derives Γ (consCode w h t n)) (hn : Derives Γ (valid w n)) : Derives Γ (valid w t) := by
  have hd := StructuralListTraceInvert.valid_decomposition hZ w n hw hn
  apply Derives.disjE hd
  · exact .botE (StructuralConsUnique.disjoint (ZFContext.add hZ _) _ _ _ _ (add hw _) (.hyp (Or.inl rfl)) (add hc _))
  · let P := tailCase w n
    let Γp := Context.add P Γ
    let T := (valid w.castSucc (Fin.last m)).conj (step w.castSucc (Fin.last m) n.castSucc)
    let Ξ := Context.add T (Context.image Formula.raise Γp)
    have htEx : Derives Γp (.ex T) := .hyp (Or.inl rfl)
    apply Derives.exE (p := T) htEx
    have hT : Derives Ξ T := .hyp (Or.inl rfl)
    have haW := StructuralListValidity.range _ _ (.conjL hT)
    let H := (Formula.mem (Fin.last (m+1)) w.castSucc.castSucc).conj (consCode w.castSucc.castSucc (Fin.last (m+1)) (Fin.last m).castSucc n.castSucc.castSucc)
    let Δ := Context.add H (Context.image Formula.raise Ξ)
    have hhEx : Derives Ξ (.ex H) := .conjR hT
    apply Derives.exE (p := H) hhEx
    have hZ2 : ZFContext.Evidence Δ := ZFContext.under (ZFContext.under (ZFContext.add hZ P) T) H
    have lift {q : Formula m} (hq : Derives Γ q) : Derives Δ q.raise.raise := under (under (add hq P) T) H
    have hw2 : Derives Δ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using lift hw
    have hc2 : Derives Δ (consCode w.castSucc.castSucc h.castSucc.castSucc t.castSucc.castSucc n.castSucc.castSucc) := by simpa only [Formula.raise, consCode_rename] using lift hc
    have ha2 : Derives Δ (valid w.castSucc.castSucc (Fin.last m).castSucc) := by simpa only [Formula.raise, valid_rename] using under (Derives.conjL hT) H
    have hH : Derives Δ H := .hyp (Or.inl rfl)
    have heq := StructuralConsUnique.injective hZ2 _ _ _ _ _ _ hw2 (.conjL hH) (under haW H) (lift hh) (lift ht) (.conjR hH) hc2
    have hout := output_subst _ _ _ (.conjR heq) ha2
    simpa only [Formula.raise, valid_rename] using hout

theorem cons_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w h t n : Fin m)
    (hw : Derives Γ (omega w)) (hh : Derives Γ (.mem h w)) (ht : Derives Γ (.mem t w))
    (hc : Derives Γ (consCode w h t n)) : Derives Γ ((valid w n).iff (valid w t)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact tail_valid (ZFContext.add hZ _) _ _ _ _ (add hw _) (add hh _) (add ht _) (add hc _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact StructuralListValidity.cons_valid (ZFContext.add hZ _) _ _ _ _ (add hw _) (add hh _) (.hyp (Or.inl rfl)) (add hc _)
end PPAC.Migration.Internal.StructuralListDecode
