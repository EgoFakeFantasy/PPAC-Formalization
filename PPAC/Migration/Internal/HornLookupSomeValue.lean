import PPAC.Migration.Internal.HornLookupPowerCondition

/-! 原全表轨迹成功图的原自然接口及所有内部输出的单值性。 -/
namespace PPAC.Migration.Internal.HornLookupSomeValue
open Source SourceAlgebra SourceLogic OmegaSyntax HornLookupSomeSyntax

theorem raw_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n i y : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (.mem n w)) (hi : Derives Γ (.mem i w)) :
    Derives Γ ((returned w n i y).iff (StrictLookupSyntax.returned w n i y)) :=
  SyntaxTypeLocalTransfer.iff_trans (HornLookupSome.execution_iff hZ w n i y hw) (LookupTableCorrectnessInduction.execution_iff_at_natural hZ w n i y hw hn hi)

theorem has_output_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n i : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (.mem n w)) (hi : Derives Γ (.mem i w)) :
    Derives Γ ((hasOutput w n i).iff (StrictLookupSyntax.hasOutput w n i)) :=
  SyntaxTypeLocalTransfer.iff_trans (HornLookupSome.has_output_iff hZ w n i hw) (LookupTableOutcome.has_output_iff hZ w n i hw hn hi)

theorem unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n i y z : Fin m)
    (hw : Derives Γ (omega w)) (hy : Derives Γ (returned w n i y)) (hz : Derives Γ (returned w n i z)) :
    Derives Γ (.equal y z) :=
  LookupTableOutcome.unique hZ w n i y z hw (.impE (.conjL (HornLookupSome.execution_iff hZ w n i y hw)) hy)
    (.impE (.conjL (HornLookupSome.execution_iff hZ w n i z hw)) hz)

end PPAC.Migration.Internal.HornLookupSomeValue
