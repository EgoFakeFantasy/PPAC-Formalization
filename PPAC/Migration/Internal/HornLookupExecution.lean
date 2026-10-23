import PPAC.Migration.Internal.HornLookupRowSyntax

/-! 实际Cons和索引见证引回独立查找程序；不调用宿主lookup。 -/
namespace PPAC.Migration.Internal.HornLookupExecution
open Source SourceAlgebra SourceLogic OmegaSyntax

theorem zero {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n i y t : Fin m)
    (hw : Derives Γ (omega w)) (hy : Derives Γ (.mem y w)) (ht : Derives Γ (.mem t w))
    (hc : Derives Γ (StructuralListSyntax.consCode w y t n)) (hi : Derives Γ (empty i)) :
    Derives Γ (LookupTableExecutionSyntax.executed w n i y) := by
  have hn := StructuralConsCore.range hZ w y t n hw hc
  have hiw := OmegaStructureAlgebra.zero_member w i (ZFContext.arithmetic hZ).base.extensionality hw hi
  have hh := StructuralListProjectionSyntax.intro_selected true w n y t (.conjI (.conjI hy ht) hc)
  exact .impE (.conjR (LookupTableRecursive.recursive_iff hZ w n i y hw)) (.conjI hn (.conjI (.conjI hiw hy) (.disjL (.conjI hi hh))))

theorem successor {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n i y h t j : Fin m)
    (hw : Derives Γ (omega w)) (hh : Derives Γ (.mem h w)) (ht : Derives Γ (.mem t w))
    (hj : Derives Γ (.mem j w)) (hy : Derives Γ (.mem y w)) (hc : Derives Γ (StructuralListSyntax.consCode w h t n))
    (hs : Derives Γ (OmegaSyntax.successor i j)) (he : Derives Γ (LookupTableExecutionSyntax.executed w t j y)) :
    Derives Γ (LookupTableExecutionSyntax.executed w n i y) := by
  have hn := StructuralConsCore.range hZ w h t n hw hc
  have hi := OmegaStructureAlgebra.successor_member w i j (ZFContext.arithmetic hZ).base.extensionality hw hj hs
  have hp := StructuralListProjectionSyntax.intro_selected false w n t h (.conjI (.conjI ht hh) hc)
  have hStep := LookupTableRecursiveSyntax.intro_successor w n i y t j hp hj hs he
  exact .impE (.conjR (LookupTableRecursive.recursive_iff hZ w n i y hw)) (.conjI hn (.conjI (.conjI hi hy) (.disjR hStep)))

end PPAC.Migration.Internal.HornLookupExecution
