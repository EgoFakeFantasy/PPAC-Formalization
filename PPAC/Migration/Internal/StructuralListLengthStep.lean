import PPAC.Migration.Internal.StructuralListLengthRules

/-! 严格较小尾码上的长度唯一性给出当前码长度唯一性，全部比较都在对象层。 -/
namespace PPAC.Migration.Internal.StructuralListLengthStep
open Source SourceAlgebra SourceLogic OmegaSyntax StructuralListSyntax StructuralListTraceSyntax StructuralListLengthSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

def earlier {m} (w n : Fin m) : Formula m := .all
  ((Formula.mem (Fin.last m) w.castSucc).imp ((Formula.mem (Fin.last m) n.castSucc).imp (property w.castSucc (Fin.last m))))
theorem earlier_rename {m k} (w n : Fin m) (r : Fin m → Fin k) : (earlier w n).rename r = earlier (r w) (r n) := by
  simp only [earlier, Formula.rename, property_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]
theorem earlier_at {m} {Γ : Context m} (w n t : Fin m) (hi : Derives Γ (earlier w n))
    (ht : Derives Γ (.mem t w)) (hn : Derives Γ (.mem t n)) : Derives Γ (property w t) := by
  have h : Derives Γ ((Formula.mem t w).imp ((Formula.mem t n).imp (property w t))) := by
    simpa only [earlier, Formula.instantiate, Formula.rename, property_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using Derives.allE t hi
  exact .impE (.impE h ht) hn

theorem unique_from_predecessors {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w t l k : Fin m)
    (hprop : Derives Γ (property w t)) (hl : Derives Γ (predecessorLength w t l)) (hk : Derives Γ (predecessorLength w t k)) : Derives Γ (.equal l k) := by
  let P := ((Formula.mem (Fin.last m) w.castSucc).conj (successor l.castSucc (Fin.last m))).conj (hasLength w.castSucc t.castSucc (Fin.last m))
  let Ξ := Context.add P (Context.image Formula.raise Γ)
  change Derives Γ (.ex P) at hl
  apply Derives.exE (p := P) hl
  have hk1 : Derives Ξ (predecessorLength w.castSucc t.castSucc k.castSucc) := by simpa only [Formula.raise, predecessorLength_rename] using under hk P
  let Q := ((Formula.mem (Fin.last (m+1)) w.castSucc.castSucc).conj (successor k.castSucc.castSucc (Fin.last (m+1)))).conj
    (hasLength w.castSucc.castSucc t.castSucc.castSucc (Fin.last (m+1)))
  let Δ := Context.add Q (Context.image Formula.raise Ξ)
  change Derives Ξ (.ex Q) at hk1
  apply Derives.exE (p := Q) hk1
  have hZ2 : ZFContext.Evidence Δ := ZFContext.under (ZFContext.under hZ P) Q
  have hp2 : Derives Δ (property w.castSucc.castSucc t.castSucc.castSucc) := by simpa only [Formula.raise, property_rename] using under (under hprop P) Q
  have hP : Derives Ξ P := .hyp (Or.inl rfl)
  have hP2 : Derives Δ (((Formula.mem (Fin.last m).castSucc w.castSucc.castSucc).conj (successor l.castSucc.castSucc (Fin.last m).castSucc)).conj
      (hasLength w.castSucc.castSucc t.castSucc.castSucc (Fin.last m).castSucc)) := by
    simpa only [P, Formula.raise, Formula.rename, successor_rename, hasLength_rename] using under hP Q
  have hQ : Derives Δ Q := .hyp (Or.inl rfl)
  have heq := property_at _ _ _ _ hp2 (.conjR hP2) (.conjR hQ)
  have hls := GodelUnpairArithmetic.successor_base_subst _ _ _ heq (.conjR (.conjL hP2))
  exact OmegaUniversal.successor_unique _ _ _ (ZFContext.arithmetic hZ2).base.extensionality hls (.conjR (.conjL hQ))

theorem unique_step {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n l k : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (earlier w n))
    (hl : Derives Γ (hasLength w n l)) (hk : Derives Γ (hasLength w n k)) : Derives Γ (.equal l k) := by
  have hv := StructuralListLengthBasic.valid_of_length w n l hl
  have hd := StructuralListTraceInvert.valid_decomposition hZ w n hw hv
  apply Derives.disjE hd
  · let N := nilCode w n
    let Δ := Context.add N Γ
    have hZ1 : ZFContext.Evidence Δ := ZFContext.add hZ N
    have hn : Derives Δ N := .hyp (Or.inl rfl)
    have hle := StructuralListLengthRules.nil_empty hZ1 _ _ _ (add hw N) hn (add hl N)
    have hke := StructuralListLengthRules.nil_empty hZ1 _ _ _ (add hw N) hn (add hk N)
    exact OmegaUniversal.empty_unique l k (ZFContext.arithmetic hZ1).base.extensionality hle hke
  · let P := StructuralListDecodeSyntax.tailCase w n
    let Γp := Context.add P Γ
    let T := (valid w.castSucc (Fin.last m)).conj (step w.castSucc (Fin.last m) n.castSucc)
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
    have hk2 : Derives Δ (hasLength w.castSucc.castSucc n.castSucc.castSucc k.castSucc.castSucc) := by simpa only [Formula.raise, hasLength_rename] using lift hk
    have hH : Derives Δ H := .hyp (Or.inl rfl)
    have htW2 : Derives Δ (.mem (Fin.last m).castSucc w.castSucc.castSucc) := under htW H
    have hb := StructuralConsCore.components hZ2 _ _ _ _ hw2 (.conjL hH) htW2 (.conjR hH)
    have htailProp := earlier_at _ _ _ hi2 htW2 (.conjR hb)
    have hpL := StructuralListLengthRules.cons_predecessor hZ2 _ _ _ _ _ hw2 (.conjL hH) htW2 (.conjR hH) hl2
    have hpK := StructuralListLengthRules.cons_predecessor hZ2 _ _ _ _ _ hw2 (.conjL hH) htW2 (.conjR hH) hk2
    exact unique_from_predecessors hZ2 _ _ _ _ htailProp hpL hpK
end PPAC.Migration.Internal.StructuralListLengthStep
