import PPAC.Migration.Internal.StructuralListCodeSyntax

/-! 指定实际后继长度的Cons反演，尾保持原前驱长度而非仅有效性。 -/
namespace PPAC.Migration.Internal.StructuralListCodeLength
open Source SourceAlgebra SourceLogic OmegaSyntax StructuralListSyntax StructuralListLengthSyntax StructuralListCodeSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem predecessor_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w s r p : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (.mem r w)) (hs : Derives Γ (successor s r))
    (hp : Derives Γ (successor s p)) : Derives Γ (.equal r p) := by
  have ht := OmegaStructureAlgebra.element_transitive_at w r
    (OmegaStructureInduction.elements_transitive w (ZFContext.separation hZ OmegaStructureSyntax.transitiveMatrix) hw) hr
  exact OmegaStructureAlgebra.successor_injective s r p ht (NaturalOrderBasic.nonself hZ r) hs hp

theorem tail_length {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w h t n r s : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (.mem r w)) (hh : Derives Γ (.mem h w)) (ht : Derives Γ (.mem t w))
    (hc : Derives Γ (consCode w h t n)) (hl : Derives Γ (hasLength w n s))
    (hs : Derives Γ (successor s r)) : Derives Γ (hasLength w t r) := by
  have hp := StructuralListLengthRules.cons_predecessor hZ w h t n s hw hh ht hc hl
  let P := ((Formula.mem (Fin.last m) w.castSucc).conj (successor s.castSucc (Fin.last m))).conj (hasLength w.castSucc t.castSucc (Fin.last m))
  let Δ := Context.add P (Context.image Formula.raise Γ)
  change Derives Γ (.ex P) at hp
  apply Derives.exE (p := P) hp
  have hZ1 : ZFContext.Evidence Δ := ZFContext.under hZ P
  have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw P
  have hs1 : Derives Δ (successor s.castSucc r.castSucc) := by simpa only [Formula.raise, successor_rename] using under hs P
  have hP : Derives Δ P := .hyp (Or.inl rfl)
  have heq := predecessor_unique hZ1 _ _ _ _ hw1 (under hr P) hs1 (.conjR (.conjL hP))
  have hout := StructuralListLengthConstruct.length_subst _ _ _ _ (eq_symm heq) (.conjR hP)
  simpa only [Formula.raise, hasLength_rename] using hout

theorem nil_successor_absurd {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n r s : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (nilCode w n)) (hl : Derives Γ (hasLength w n s))
    (hs : Derives Γ (successor s r)) : Derives Γ .bot := by
  have he := StructuralListLengthRules.nil_empty hZ w n s hw hn hl
  exact .impE (empty_at s r he) (InsertLogic.new_member s r r hs)

theorem successor_view {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n r s : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (.mem r w)) (hs : Derives Γ (successor s r))
    (hl : Derives Γ (hasLength w n s)) : Derives Γ (consView w n r) := by
  have hv := StructuralListLengthBasic.valid_of_length w n s hl
  have hd := StructuralListTraceInvert.valid_decomposition hZ w n hw hv
  apply Derives.disjE hd
  · exact .botE (nil_successor_absurd (ZFContext.add hZ _) _ _ _ _ (add hw _) (.hyp (Or.inl rfl)) (add hl _) (add hs _))
  · let P := StructuralListDecodeSyntax.tailCase w n
    let Γp := Context.add P Γ
    let T := (StructuralListTraceSyntax.valid w.castSucc (Fin.last m)).conj (StructuralListTraceSyntax.step w.castSucc (Fin.last m) n.castSucc)
    let Ξ := Context.add T (Context.image Formula.raise Γp)
    have htEx : Derives Γp (.ex T) := .hyp (Or.inl rfl)
    apply Derives.exE (p := T) htEx
    have hZ1 : ZFContext.Evidence Ξ := ZFContext.under (ZFContext.add hZ P) T
    have hT : Derives Ξ T := .hyp (Or.inl rfl)
    have htW := StructuralListValidity.range _ _ (.conjL hT)
    let H := (Formula.mem (Fin.last (m+1)) w.castSucc.castSucc).conj (consCode w.castSucc.castSucc (Fin.last (m+1)) (Fin.last m).castSucc n.castSucc.castSucc)
    let Δ := Context.add H (Context.image Formula.raise Ξ)
    have hhEx : Derives Ξ (.ex H) := .conjR hT
    apply Derives.exE (p := H) hhEx
    have hZ2 : ZFContext.Evidence Δ := ZFContext.under hZ1 H
    have lift {q : Formula m} (hq : Derives Γ q) : Derives Δ q.raise.raise := under (under (add hq P) T) H
    have hw2 : Derives Δ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using lift hw
    have hs2 : Derives Δ (successor s.castSucc.castSucc r.castSucc.castSucc) := by simpa only [Formula.raise, successor_rename] using lift hs
    have hl2 : Derives Δ (hasLength w.castSucc.castSucc n.castSucc.castSucc s.castSucc.castSucc) := by simpa only [Formula.raise, hasLength_rename] using lift hl
    have hH : Derives Δ H := .hyp (Or.inl rfl)
    have htail := tail_length hZ2 _ _ _ _ _ _ hw2 (lift hr) (.conjL hH) (under htW H) (.conjR hH) hl2 hs2
    have hout := intro_view _ _ _ _ _ (.conjL hH) htail (.conjR hH)
    simpa only [Formula.raise, consView_rename] using hout
end PPAC.Migration.Internal.StructuralListCodeLength
