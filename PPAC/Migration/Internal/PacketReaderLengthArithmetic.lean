import PPAC.Migration.Internal.PacketReaderTailLength

/-! Original unbounded addition transfers one consumed length unit to the internal step index. -/
namespace PPAC.Migration.Internal.PacketReaderLengthArithmetic
open Source SourceAlgebra SourceLogic OmegaSyntax NaturalAdditionSyntax ZFArithmetic
open SyntaxRenameQuerySyntax (of_eq)

theorem zero_sum {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w i a N : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (empty i)) (ha : Derives Γ (.mem a w))
    (he : Derives Γ (.equal a N)) : Derives Γ (sum w i a N) := by
  have hiN := OmegaStructureAlgebra.zero_member w i (ZFContext.arithmetic hZ).base.extensionality hw hi
  have hN := mem_subst he ha
  have hs := add_zero hZ w N i hw hN hi
  have hc := add_commute hZ w N i N hw hN hiN hs
  exact NaturalAdditionTransport.index_subst w i N a N (eq_symm he) hc

theorem transfer {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w i j a b N : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (.mem i w)) (hb : Derives Γ (.mem b w))
    (hj : Derives Γ (successor j i)) (ha : Derives Γ (successor a b)) (hs : Derives Γ (sum w i a N)) :
    Derives Γ (sum w j b N) := by
  let R := (Formula.mem (Fin.last m) w.castSucc).conj (sum w.castSucc i.castSucc b.castSucc (Fin.last m))
  let Δ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) (add_exists hZ w i b hw hi hb)
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hZ1 := ZFContext.under hZ R
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw R)
  have hi1 : Derives Δ (.mem i.castSucc w.castSucc) := under hi R
  have hb1 : Derives Δ (.mem b.castSucc w.castSucc) := under hb R
  have hj1 := of_eq (successor_rename j i Fin.castSucc) (under hj R)
  have ha1 := of_eq (successor_rename a b Fin.castSucc) (under ha R)
  have hs1 := of_eq (sum_rename w i a N Fin.castSucc) (under hs R)
  have hN := add_succ_forward hZ1 _ _ _ _ _ _ hw1 hi1 hb1 ha1 (.conjR hR) hs1
  have hout := NaturalAdditionShift.shift_at (ZFContext.arithmetic hZ1) _ _ _ _ _ _ (ZFContext.recAdd hZ1)
    (ZFContext.separation hZ1 NaturalAdditionShift.matrix) hw1 hi1 hj1 hb1 (.conjR hR) hN
  simpa only [Formula.raise,sum_rename] using hout

theorem index_bound {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w i a N : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (.mem i w)) (ha : Derives Γ (.mem a w))
    (hs : Derives Γ (sum w i a N)) : Derives Γ (NaturalAdditionBounds.below i N) :=
  NaturalDifference.below_of_exists hZ w i N hw hi (NaturalDifferenceSyntax.intro_difference w i N a ha hs)

end PPAC.Migration.Internal.PacketReaderLengthArithmetic
