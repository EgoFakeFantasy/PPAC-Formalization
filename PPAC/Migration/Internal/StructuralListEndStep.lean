import PPAC.Migration.Internal.StructuralListEndRules

/-! 原Cons严格尾码界上的内部成员归纳步，目标保持全部实际长度及求值候选。 -/
namespace PPAC.Migration.Internal.StructuralListEndStep
open Source SourceAlgebra SourceLogic OmegaSyntax StructuralListSyntax StructuralListLengthSyntax StructuralListProjectionSyntax StructuralListEndSyntax
open StructuralListTraceSyntax (valid)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem code_step {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n l y : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (earlier w n))
    (hl : Derives Γ (hasLength w n l)) (hy : Derives Γ (iteration false w n l y)) : Derives Γ (nilCode w y) := by
  have hv := StructuralListLengthBasic.valid_of_length w n l hl
  have hd := StructuralListTraceInvert.valid_decomposition hZ w n hw hv
  apply Derives.disjE hd
  · let N := nilCode w n
    exact StructuralListEndRules.from_nil (ZFContext.add hZ N) w n l y (add hw N) (.hyp (Or.inl rfl)) (add hl N) (add hy N)
  · let P := StructuralListDecodeSyntax.tailCase w n
    let Γp := Context.add P Γ
    let T := (valid w.castSucc (Fin.last m)).conj (StructuralListTraceSyntax.step w.castSucc (Fin.last m) n.castSucc)
    let Ξ := Context.add T (Context.image Formula.raise Γp)
    have htEx : Derives Γp (.ex T) := .hyp (Or.inl rfl)
    apply Derives.exE (p := T) htEx
    have hZ1 : ZFContext.Evidence Ξ := ZFContext.under (ZFContext.add hZ P) T
    have lift1 {q : Formula m} (hq : Derives Γ q) : Derives Ξ q.raise := under (add hq P) T
    have hT : Derives Ξ T := .hyp (Or.inl rfl)
    have htW := StructuralListValidity.range _ _ (.conjL hT)
    let H := (Formula.mem (Fin.last (m+1)) w.castSucc.castSucc).conj (consCode w.castSucc.castSucc (Fin.last (m+1)) (Fin.last m).castSucc n.castSucc.castSucc)
    let Δ := Context.add H (Context.image Formula.raise Ξ)
    have hhEx : Derives Ξ (.ex H) := .conjR hT
    apply Derives.exE (p := H) hhEx
    have hZ2 : ZFContext.Evidence Δ := ZFContext.under hZ1 H
    have lift {q : Formula m} (hq : Derives Γ q) : Derives Δ q.raise.raise := under (lift1 hq) H
    have hw2 : Derives Δ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using lift hw
    have hi2 : Derives Δ (earlier w.castSucc.castSucc n.castSucc.castSucc) := by simpa only [Formula.raise, earlier_rename] using lift hi
    have hl2 : Derives Δ (hasLength w.castSucc.castSucc n.castSucc.castSucc l.castSucc.castSucc) := by simpa only [Formula.raise, hasLength_rename] using lift hl
    have hy2 : Derives Δ (iteration false w.castSucc.castSucc n.castSucc.castSucc l.castSucc.castSucc y.castSucc.castSucc) := by
      simpa only [Formula.raise, iteration_rename] using lift hy
    have hH : Derives Δ H := .hyp (Or.inl rfl)
    have htW2 : Derives Δ (.mem (Fin.last m).castSucc w.castSucc.castSucc) := under htW H
    have hb := StructuralConsCore.components hZ2 _ _ _ _ hw2 (.conjL hH) htW2 (.conjR hH)
    have htail := earlier_at _ _ _ hi2 htW2 (.conjR hb)
    have hout := StructuralListEndRules.from_cons hZ2 _ _ _ _ _ _ hw2 (.conjL hH) htW2 (.conjR hH) hl2 hy2 htail
    simpa only [Formula.raise, nilCode_rename] using hout
end PPAC.Migration.Internal.StructuralListEndStep
