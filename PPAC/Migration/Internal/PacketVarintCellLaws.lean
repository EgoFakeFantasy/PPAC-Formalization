import PPAC.Migration.Internal.PacketVarintConstruct

/-! Canonical terminal and continuation cells are disjoint; both give actual byte bounds at 128 and 256. -/
namespace PPAC.Migration.Internal.PacketVarintCellLaws
open Source SourceAlgebra SourceLogic OmegaSyntax PacketVarintCellSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem continuation_nonzero {m} {Γ : Context m} (w B h u v : Fin m) (hc : Derives Γ (continuation w B h u v)) : Derives Γ (empty u).neg := by
  let R := (empty u.castSucc).neg.conj ((PacketAffineSyntax.affine w.castSucc B.castSucc (Fin.last m) u.castSucc v.castSucc).conj
    (NaturalAdditionSyntax.sum w.castSucc (Fin.last m) B.castSucc h.castSucc))
  let Δ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) hc
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  simpa only [Formula.raise,Formula.neg,Formula.rename,empty_rename] using Derives.conjL hR

theorem terminal_continuation_disjoint {m} {Γ : Context m} (w B x h u v : Fin m)
    (ht : Derives Γ (terminal w B x h u v)) (hc : Derives Γ (continuation w B h u v)) : Derives Γ .bot :=
  .impE (continuation_nonzero w B h u v hc) (.conjL (.conjR ht))

theorem zero_forces_terminal {m} {Γ : Context m} (w B x h u v : Fin m) (hu : Derives Γ (empty u))
    (hc : Derives Γ (cell w B x h u v)) : Derives Γ (terminal w B x h u v) := by
  apply Derives.disjE (.conjR (.conjR (.conjR hc)))
  · exact .hyp (Or.inl rfl)
  · exact .botE (.impE (continuation_nonzero w B h u v (.hyp (Or.inl rfl))) (add hu _))

theorem nonempty_previous_forces_continuation {m} {Γ : Context m} (w B x h u v : Fin m)
    (hx : Derives Γ (StructuralListSyntax.nilCode w x).neg) (hc : Derives Γ (cell w B x h u v)) : Derives Γ (continuation w B h u v) := by
  apply Derives.disjE (.conjR (.conjR (.conjR hc)))
  · exact .botE (.impE (add hx _) (.conjL (.hyp (Or.inl rfl))))
  · exact .hyp (Or.inl rfl)

theorem continuation_byte_bound {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B C h u v : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B))
    (hC : Derives Γ (SyntaxNumeralSyntax.numeral 256 C)) (hc : Derives Γ (continuation w B h u v)) : Derives Γ (.mem h C) := by
  let R := (empty u.castSucc).neg.conj ((PacketAffineSyntax.affine w.castSucc B.castSucc (Fin.last m) u.castSucc v.castSucc).conj
    (NaturalAdditionSyntax.sum w.castSucc (Fin.last m) B.castSucc h.castSucc))
  let Δ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) hc
  have hZ1 := ZFContext.under hZ R
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw R)
  have hB1 := of_eq (SyntaxNumeralSyntax.numeral_rename 128 B Fin.castSucc) (under hB R)
  have hC1 := of_eq (SyntaxNumeralSyntax.numeral_rename 256 C Fin.castSucc) (under hC R)
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  exact PacketTokenByteBounds.shifted_digit_byte hZ1 w.castSucc B.castSucc C.castSucc (Fin.last m) h.castSucc hw1 hB1 hC1
    (PacketAffineCore.digit_guard _ _ _ _ _ (.conjL (.conjR hR))) (.conjR (.conjR hR))

theorem cell_byte_bound {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B C x h u v : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B))
    (hC : Derives Γ (SyntaxNumeralSyntax.numeral 256 C)) (hc : Derives Γ (cell w B x h u v)) : Derives Γ (.mem h C) := by
  apply Derives.disjE (.conjR (.conjR (.conjR hc)))
  · exact PacketTokenByteBounds.small_digit_byte (ZFContext.add hZ _) w B C h (add hw _) (add hB _) (add hC _) (.conjL (.conjR (.conjR (.hyp (Or.inl rfl)))))
  · exact continuation_byte_bound (ZFContext.add hZ _) w B C h u v (add hw _) (add hB _) (add hC _) (.hyp (Or.inl rfl))

end PPAC.Migration.Internal.PacketVarintCellLaws
