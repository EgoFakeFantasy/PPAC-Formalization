import PPAC.Migration.Internal.StructuralNodeDecodeSyntax

/-! 每个正内部自然码实际分解为唯一自然标签与载荷；零码由后继非空排除。 -/
namespace PPAC.Migration.Internal.StructuralNodeDecodeExistence
open Source SourceAlgebra SourceLogic OmegaSyntax StructuralNodeDecodeSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem preimage_exists {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (.mem n w)) (hpos : Derives Γ (empty n).neg) : Derives Γ (preimage w n) := by
  have hd := OmegaStructureAlgebra.decomposition_at w n
    (OmegaStructureInduction.decomposition w (ZFContext.separation hZ OmegaStructureSyntax.splitMatrix) hw) hn
  have hq := OmegaStructureAlgebra.nonzero_predecessor w n hd hpos
  let Q := (Formula.mem (Fin.last m) w.castSucc).conj (successor n.castSucc (Fin.last m))
  let Ξ := Context.add Q (Context.image Formula.raise Γ)
  change Derives Γ (.ex Q) at hq
  apply Derives.exE (p := Q) hq
  suffices hout : Derives Ξ (preimage w.castSucc n.castSucc) by
    simpa only [Formula.raise, preimage_rename] using hout
  have hZ1 : ZFContext.Evidence Ξ := ZFContext.under hZ Q
  have hw1 : Derives Ξ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw Q
  have hQ : Derives Ξ Q := .hyp (Or.inl rfl)
  have hi := GodelUnpairExistence.preimage_exists hZ1 w.castSucc (Fin.last m) hw1 (.conjL hQ)
  let W := GodelUnpairSyntax.witness w.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc (Fin.last (m+2))
  let Δ := Context.add W (Context.image Formula.raise (Context.image Formula.raise Ξ))
  apply GodelUnpairSyntax.eliminate_preimage w.castSucc (Fin.last m) _ hi
  have hW : Derives Δ W := .hyp (Or.inl rfl)
  have hQ3 : Derives Δ ((Formula.mem (Fin.last m).castSucc.castSucc w.castSucc.castSucc.castSucc).conj
      (successor n.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc)) := by
    simpa only [Q, Formula.raise, Formula.rename, successor_rename] using OrderedPairElimination.under_two hQ W
  have hraw := StructuralNodeSyntax.intro_raw _ _ _ _ _ (.conjR hW) (.conjR hQ3)
  have hout := intro_preimage _ _ _ _ (.conjL (.conjL hW)) (.conjR (.conjL hW)) hraw
  simpa only [Formula.raise, preimage_rename] using hout

theorem preimage_positive {m} {Γ : Context m} (w n : Fin m) (hn : Derives Γ (preimage w n)) : Derives Γ (empty n).neg := by
  let W := witness w.castSucc.castSucc n.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
  let Δ := Context.add W (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply eliminate_preimage w n _ hn
  have hW : Derives Δ W := .hyp (Or.inl rfl)
  have hout := StructuralNodeProperties.positive _ _ _ _ (.conjR hW)
  simpa only [Formula.raise, Formula.neg, Formula.rename, empty_rename] using hout

theorem positive_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (.mem n w)) : Derives Γ ((empty n).neg.iff (preimage w n)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact preimage_exists (ZFContext.add hZ _) _ _ (add hw _) (add hn _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact preimage_positive _ _ (.hyp (Or.inl rfl))
end PPAC.Migration.Internal.StructuralNodeDecodeExistence
