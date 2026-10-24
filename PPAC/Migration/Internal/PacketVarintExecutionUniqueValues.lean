import PPAC.Migration.Internal.PacketVarintExecutionDomain

/-! Original division, sum and Cons uniqueness align two complete actual continuation branches. -/
namespace PPAC.Migration.Internal.PacketVarintExecutionUniqueValues
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax PacketVarintSyntax PacketVarintExecutionSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem values {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B n s t d q h x e r k y : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B)) (hi : Derives Γ (earlier w n))
    (ha : Derives Γ (PacketAffineSyntax.affine w B d q n)) (hb : Derives Γ (PacketAffineSyntax.affine w B e r n))
    (hq : Derives Γ (empty q).neg) (hs : Derives Γ (NaturalAdditionSyntax.sum w d B h)) (ht : Derives Γ (NaturalAdditionSyntax.sum w e B k))
    (hx : Derives Γ (canonical w q x)) (hy : Derives Γ (canonical w r y))
    (hc : Derives Γ (StructuralListSyntax.consCode w h x s)) (hd : Derives Γ (StructuralListSyntax.consCode w k y t)) : Derives Γ (.equal s t) := by
  have hpair := PacketDivisionUnique.unique hZ w B d q e r n hw ha hb
  have hyq := PacketVarintExecutionHelpers.canonical_input w r y q (eq_symm (.conjR hpair)) hy
  have hP := PacketVarintExecutionHelpers.below_property hZ w B n d q hw hB hi ha hq
  have hxy := unique_at w q x y hP hx hyq
  have hsum := PacketVarintExecutionHelpers.sum_left w e B k d (eq_symm (.conjL hpair)) ht
  have hhk := ZFArithmetic.add_unique hZ w d B h k hw (PacketAffineCore.radix_guard _ _ _ _ _ ha) hs hsum
  have hhead := PacketVarintCanonicalPieces.cons_head w k y t h (eq_symm hhk) hd
  have haligned := PacketVarintExecutionHelpers.cons_tail w h y t x (eq_symm hxy) hhead
  have hh := ZFArithmetic.add_range hZ w d B h hw (PacketAffineCore.digit_natural hZ w B d q n hw ha) hs
  exact StructuralConsUnique.unique hZ w h x s t hw hh (PacketVarintExecutionHelpers.list_natural w q x hx) hc haligned

theorem large_not_small {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B n s : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (.mem n B)) (hc : Derives Γ (PacketVarintCanonicalRecursionSyntax.largeCase true w B n s)) : Derives Γ .bot := by
  let R := PacketVarintCanonicalRecursionSyntax.largeBody true w B n s
  let Δ := Context.add R (raisedContext 4 Γ)
  apply HornBinderRules.eliminate_many 4 R _ hc
  have hZ4 := HornBinderRules.zf_body 4 hZ R
  have hw4 := of_eq (omega_rename w (old 4)) (HornBinderRules.under_body 4 hw R)
  have hn4 : Derives Δ (.mem (old 4 n) (old 4 B)) := HornBinderRules.under_body 4 hn R
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  exact .impE (.conjL (.conjR hR)) (.impE (.conjR (PacketDivisionDescentCore.terminal_iff hZ4 (old 4 w) (old 4 B) (slot 4 0) (slot 4 1) (old 4 n) hw4 (.conjL hR))) hn4)

theorem small_values {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n s t e f : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (.mem n w)) (he : Derives Γ (StructuralListSyntax.nilCode w e))
    (hf : Derives Γ (StructuralListSyntax.nilCode w f)) (hs : Derives Γ (StructuralListSyntax.consCode w n e s))
    (ht : Derives Γ (StructuralListSyntax.consCode w n f t)) : Derives Γ (.equal s t) := by
  have hef := StructuralNil.unique hZ w e f hw he hf
  have haligned := PacketVarintExecutionHelpers.cons_tail w n f t e (eq_symm hef) ht
  exact StructuralConsUnique.unique hZ w n e s t hw hn (StructuralNil.range hZ w e hw he) hs haligned

end PPAC.Migration.Internal.PacketVarintExecutionUniqueValues
