import PPAC.Migration.Internal.StructuralListEncodeGraph

/-! 任意原完整ω值序列及内部自然长度都有实际原列表码，解码字段图就是该序列。 -/
namespace PPAC.Migration.Internal.StructuralListEncodeExistence
open Source SourceAlgebra SourceLogic OmegaSyntax SequenceSyntax StructuralListSuffixSyntax StructuralListEncodeSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem exists_encoding {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w f l : Fin m)
    (hw : Derives Γ (omega w)) (hf : Derives Γ (sequence f l w)) (hl : Derives Γ (.mem l w)) : Derives Γ (existsEncoding w f l) := by
  have hz : Derives Γ (zeroIn w) := .conjL (.conjL hw)
  let Z := (Formula.mem (Fin.last m) w.castSucc).conj (empty (Fin.last m))
  let Ξ := Context.add Z (Context.image Formula.raise Γ)
  change Derives Γ (.ex Z) at hz
  apply Derives.exE (p := Z) hz
  have hZ1 : ZFContext.Evidence Ξ := ZFContext.under hZ Z
  have hw1 : Derives Ξ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw Z
  have hf1 : Derives Ξ (sequence f.castSucc l.castSucc w.castSucc) := by simpa only [Formula.raise, sequence_rename] using under hf Z
  have hZv : Derives Ξ Z := .hyp (Or.inl rfl)
  have hn := StructuralListSuffixInduction.full_suffix hZ1 w.castSucc f.castSucc l.castSucc (Fin.last m) hw1 hf1 (under hl Z) (.conjR hZv)
  let N := coded w.castSucc.castSucc f.castSucc.castSucc (Fin.last m).castSucc l.castSucc.castSucc (Fin.last (m+1))
  let Δ := Context.add N (Context.image Formula.raise Ξ)
  change Derives Ξ (.ex N) at hn
  apply Derives.exE (p := N) hn
  have hZ2 : ZFContext.Evidence Δ := ZFContext.under hZ1 N
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw1 N
  have hf2 : Derives Δ (sequence f.castSucc.castSucc l.castSucc.castSucc w.castSucc.castSucc) := by simpa only [Formula.raise, sequence_rename] using under hf1 N
  have hz2 : Derives Δ (empty (Fin.last m).castSucc) := by simpa only [Z, Formula.raise, empty_rename] using under (.conjR hZv) N
  have hN : Derives Δ N := .hyp (Or.inl rfl)
  have hfields := StructuralListEncodeGraph.fields_from_zero hZ2 _ _ _ _ _ hw2 hf2 (under (under hl Z) N) hz2 (.conjR hN)
  have hout := intro_encoding _ _ _ _ (.conjL (.conjL hN)) (.conjR (.conjL hN)) hfields
  simpa only [Formula.raise, existsEncoding_rename] using hout
end PPAC.Migration.Internal.StructuralListEncodeExistence
