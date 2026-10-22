import PPAC.Migration.Internal.SyntaxMixedImageBinderFiber

/-! 全内部binder关系在任意实际规范见证上的精确新零、旧bound和旧free字段律。 -/
namespace PPAC.Migration.Internal.SyntaxMixedImageBinderFields
open Source SourceAlgebra SourceLogic OmegaSyntax GraphSyntax SyntaxRenameQuerySyntax SyntaxMixedImageBinderSyntax

theorem zero_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r s a b c d A C k h R S z n q : Fin m)
    (hw : Derives Γ (omega w)) (hR : Derives Γ (SyntaxFreeShiftSyntax.shiftMap w c C R))
    (hS : Derives Γ (SyntaxIdentityMapSyntax.identityMap w d S)) (hHead : Derives Γ (SyntaxMixedImageHead.head w C d z n))
    (hl : Derives Γ (lifted w r s a b c d A C k h)) : Derives Γ ((edge k z q).iff (Formula.equal q n)) := by
  have ha := SyntaxMixedImageBinderOutput.at_witnesses hZ w r s a b c d A C k h R S z n hw hR hS hHead hl
  exact SyntaxMixedImageLiftFields.zero_iff hZ w R S r s a b c d A C n k h z q ha hw (.conjL hHead)

theorem bound_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r s a b c d A C k h R S z n i j t q : Fin m)
    (hw : Derives Γ (omega w)) (hR : Derives Γ (SyntaxFreeShiftSyntax.shiftMap w c C R))
    (hS : Derives Γ (SyntaxIdentityMapSyntax.identityMap w d S)) (hHead : Derives Γ (SyntaxMixedImageHead.head w C d z n))
    (hl : Derives Γ (lifted w r s a b c d A C k h)) (hj : Derives Γ (.mem j a)) (hi : Derives Γ (successor i j)) (ht : Derives Γ (edge r j t)) : Derives Γ ((edge k i q).iff (SyntaxRenameTermSyntax.renamed w R S c d C d t q)) := by
  have ha := SyntaxMixedImageBinderOutput.at_witnesses hZ w r s a b c d A C k h R S z n hw hR hS hHead hl
  exact SyntaxMixedImageLiftFields.bound_iff hZ w R S r s a b c d A C n k h i j t q ha hw hj hi ht

theorem free_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r s a b c d A C k h R S z n j t q : Fin m)
    (hw : Derives Γ (omega w)) (hR : Derives Γ (SyntaxFreeShiftSyntax.shiftMap w c C R))
    (hS : Derives Γ (SyntaxIdentityMapSyntax.identityMap w d S)) (hHead : Derives Γ (SyntaxMixedImageHead.head w C d z n))
    (hl : Derives Γ (lifted w r s a b c d A C k h)) (ht : Derives Γ (edge s j t)) : Derives Γ ((edge h j q).iff (SyntaxRenameTermSyntax.renamed w R S c d C d t q)) := by
  have ha := SyntaxMixedImageBinderOutput.at_witnesses hZ w r s a b c d A C k h R S z n hw hR hS hHead hl
  exact SyntaxMixedImageLiftFields.free_iff hZ w R S r s a b c d A C n k h j t q ha ht

end PPAC.Migration.Internal.SyntaxMixedImageBinderFields
