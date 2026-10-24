import PPAC.Migration.Internal.PacketTokenUniqueSyntax

/-! Inverse decomposition, shift sums, recursive token outputs and final affine outputs are compared in the object kernel. -/
namespace PPAC.Migration.Internal.PacketTokenUniqueValues
open Source SourceAlgebra SourceLogic OmegaSyntax PacketAffineSyntax PacketAffineCore PacketTokenAcceptedSyntax
open PacketTokenUniqueSyntax

theorem unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B C n t a b d q u y e p v z : Fin m)
    (hw : Derives Γ (omega w)) (h0 : Derives Γ (affine w B d q n)) (h2 : Derives Γ (affine w B e p n))
    (hy : Derives Γ (NaturalAdditionSyntax.sum w d B y)) (hz : Derives Γ (NaturalAdditionSyntax.sum w e B z))
    (hu : Derives Γ (accepted w q t u)) (hv : Derives Γ (accepted w p t v))
    (h1 : Derives Γ (affine w C y u a)) (h3 : Derives Γ (affine w C z v b)) (hi : Derives Γ (property w q)) :
    Derives Γ (.equal a b) := by
  have hpair := PacketDivisionUnique.unique hZ w B d q e p n hw h0 h2
  have hvq := PacketTokenValueTransport.accepted_input w p t v q (eq_symm (.conjR hpair)) hv
  have huv := property_at w q t u v hi hu hvq
  have hzd := PacketTokenValueTransport.sum_first w e B z d (eq_symm (.conjL hpair)) hz
  have hyz := ZFArithmetic.add_unique hZ w d B y z hw (radix_guard _ _ _ _ _ h0) hy hzd
  have h1z := PacketAffineTransport.digit w C y u a z hyz h1
  have h1v := PacketAffineTransport.tail w C z u a v huv h1z
  exact PacketAffineCore.unique hZ w C z v a b hw h1v h3

end PPAC.Migration.Internal.PacketTokenUniqueValues
