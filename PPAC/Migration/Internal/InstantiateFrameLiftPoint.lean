import PPAC.Migration.Internal.InstantiateOperationFrameRoot
import PPAC.Migration.Internal.InstantiateBinderVariable
import PPAC.Migration.Internal.SyntaxCodedMixedBinderFields

/-! mode2实际提升两码表的三类逐点兼容；point分支使用闭参数真实重命名保持。 -/
namespace PPAC.Migration.Internal.InstantiateFrameLiftPoint
open Source SourceAlgebra SourceLogic OmegaSyntax InstantiateOperationFrameSyntax InstantiateVariableValueSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem fresh {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w depth P D R S a b c e A C K H U V z n i X q : Fin m)
    (hw : Derives Γ (omega w)) (hd : Derives Γ (.mem depth w)) (hD : Derives Γ (successor D depth))
    (hl : Derives Γ (SyntaxCodedMixedBinderSyntax.lifted w R S a b c e A C K H))
    (hU : Derives Γ (SyntaxFreeShiftSyntax.shiftMap w c C U)) (hV : Derives Γ (SyntaxIdentityMapSyntax.identityMap w e V))
    (hHead : Derives Γ (SyntaxMixedImageHead.head w C e z n))
    (hi : Derives Γ (.mem i A)) (hiz : Derives Γ (empty i)) (hX : Derives Γ (SyntaxVariableSyntax.code true w i X)) :
    Derives Γ ((boundValue w D P i X q).iff (StructuralListFieldSyntax.field w K i q)) := by
  have hDn := OmegaStructureAlgebra.successor_member w D depth (ZFContext.arithmetic hZ).base.extensionality hw hd hD
  have hiD := SyntaxIndexLiftOrder.zero_member hZ w depth D i hw hd hD hiz
  have hezi := OmegaUniversal.empty_unique z i (ZFContext.arithmetic hZ).base.extensionality (.conjL hHead) hiz
  have hni := AbstractVariableIndex.code_index_subst true w z i n hezi (.conjL (.conjR hHead))
  have hn := InstantiateVariableSpecialization.below_iff hZ w D P i X q hw hDn hiD
  have hx := AbstractBinderRename.code_iff_equal hZ true w i X q hw hX
  have hc := AbstractBinderRename.code_iff_equal hZ true w i n q hw hni
  have hv := SyntaxTypeLocalTransfer.iff_trans hn (SyntaxTypeLocalTransfer.iff_trans (.conjI (.conjR hx) (.conjL hx)) hc)
  have hh : Derives Γ (SyntaxMixedImageHead.head w C e i n) := .conjI hiz (.conjI hni (.conjR (.conjR hHead)))
  have hf := AbstractTopVariablePoint.remove_scope hi (SyntaxCodedMixedBinderFields.zero_iff hZ w R S a b c e A C K H U V i n q hw hl hU hV hh)
  exact SyntaxTypeLocalTransfer.iff_trans hv (.conjI (.conjR hf) (.conjL hf))

theorem bound_at {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w mode depth P D R S a b c e A C K H U V z n i j x X t q : Fin m)
    (hw : Derives Γ (omega w)) (hF : Derives Γ (frame w mode depth P a b c e R S))
    (hD : Derives Γ (successor D depth))
    (hl : Derives Γ (SyntaxCodedMixedBinderSyntax.lifted w R S a b c e A C K H))
    (hU : Derives Γ (SyntaxFreeShiftSyntax.shiftMap w c C U)) (hV : Derives Γ (SyntaxIdentityMapSyntax.identityMap w e V))
    (hHead : Derives Γ (SyntaxMixedImageHead.head w C e z n))
    (hi : Derives Γ (.mem i A)) (hj : Derives Γ (.mem j a)) (hij : Derives Γ (successor i j))
    (hx : Derives Γ (SyntaxVariableSyntax.code true w j x)) (hX : Derives Γ (SyntaxVariableSyntax.code true w i X))
    (ht : Derives Γ (StructuralListFieldSyntax.field w R j t)) :
    Derives Γ ((boundValue w D P i X q).iff (StructuralListFieldSyntax.field w K i q)) := by
  have hTyped := SyntaxMixedImageCodeFields.field_type w a c e R j t (.conjL (term_lists w mode depth P a b c e R S hF)) hj ht
  have hOld := Derives.impE (.conjR (compatible_at true w depth P a b R S j x t (variables true w mode depth P a b c e R S hF) hj hx)) ht
  have hv := InstantiateBinderVariable.bound_iff hZ w depth P a j D i U V c e C x X t q hw (.conjL (metadata w mode depth P a b c e R S hF)) (source_successor w mode depth P a b c e R S hF) hj hD hij hU hV hTyped hx hX (parameter_closed w mode depth P a b c e R S hF) hOld
  have hf := AbstractTopVariablePoint.remove_scope hi (SyntaxCodedMixedBinderFields.bound_iff hZ w R S a b c e A C K H U V z n i j t q hw hl hU hV hHead hj hij ht)
  exact SyntaxTypeLocalTransfer.iff_trans hv (.conjI (.conjR hf) (.conjL hf))

theorem free_at {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w mode depth P D R S a b c e A C K H U V z n i X t q : Fin m)
    (hw : Derives Γ (omega w)) (hF : Derives Γ (frame w mode depth P a b c e R S))
    (_hD : Derives Γ (successor D depth))
    (hl : Derives Γ (SyntaxCodedMixedBinderSyntax.lifted w R S a b c e A C K H))
    (hU : Derives Γ (SyntaxFreeShiftSyntax.shiftMap w c C U)) (hV : Derives Γ (SyntaxIdentityMapSyntax.identityMap w e V))
    (hHead : Derives Γ (SyntaxMixedImageHead.head w C e z n))
    (hi : Derives Γ (.mem i b)) (hX : Derives Γ (SyntaxVariableSyntax.code false w i X))
    (ht : Derives Γ (StructuralListFieldSyntax.field w S i t)) :
    Derives Γ ((Formula.equal q X).iff (StructuralListFieldSyntax.field w H i q)) := by
  have hTyped := SyntaxMixedImageCodeFields.field_type w b c e S i t (.conjR (term_lists w mode depth P a b c e R S hF)) hi ht
  have hOld := Derives.impE (.conjR (compatible_at false w depth P a b R S i X t (variables false w mode depth P a b c e R S hF) hi hX)) ht
  have hv := InstantiateBinderVariable.free_iff hZ w i U V c e C X t q hw hU hV hTyped hX hOld
  have hf := AbstractTopVariablePoint.remove_scope hi (SyntaxCodedMixedBinderFields.free_iff hZ w R S a b c e A C K H U V z n i t q hw hl hU hV hHead hi ht)
  exact SyntaxTypeLocalTransfer.iff_trans hv (.conjI (.conjR hf) (.conjL hf))

end PPAC.Migration.Internal.InstantiateFrameLiftPoint
