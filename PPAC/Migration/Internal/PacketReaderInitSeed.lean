import PPAC.Migration.Internal.PacketReaderInitSyntax

/-! The actual initial four-field state is constructed from any valid internal input and actual zero/one, with no state-code premise. -/
namespace PPAC.Migration.Internal.PacketReaderInitSeed
open Source SourceAlgebra SourceLogic OmegaSyntax PacketReaderInitSyntax

theorem state {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z o L : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) (ho : Derives Γ (successor o z))
    (hL : Derives Γ (StructuralListTraceSyntax.valid w L)) : Derives Γ (PacketReaderStepSyntax.state w L z o o) :=
  .conjI hL (.conjI (OmegaStructureAlgebra.zero_member w z (ZFContext.arithmetic hZ).base.extensionality hw hz)
    (.conjI (StructuralListUnits.member hZ w z o hw hz ho)
      (StructuralListTraceBase.valid_unit hZ w z o hw hz ho)))

theorem exists_seed {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z o L : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) (ho : Derives Γ (successor o z))
    (hL : Derives Γ (StructuralListTraceSyntax.valid w L)) : Derives Γ (existsSeed w z o L) :=
  PacketReaderStateCode.exists_code hZ w L z o o hw (state hZ w z o L hw hz ho hL)

theorem unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z o L n r : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (seed w z o L n)) (hr : Derives Γ (seed w z o L r)) : Derives Γ (.equal n r) :=
  PacketReaderStateCode.unique hZ w L z o o n r hw hn hr

theorem natural {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z o L n : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (seed w z o L n)) : Derives Γ (.mem n w) :=
  PacketReaderStateCode.range hZ w L z o o n hw hn

theorem input_valid {m} {Γ : Context m} (w z o L n : Fin m) (hn : Derives Γ (seed w z o L n)) :
    Derives Γ (StructuralListTraceSyntax.valid w L) := .conjL (.conjL hn)

theorem carrier {m} {Γ : Context m} (w z o L n : Fin m) (hn : Derives Γ (seed w z o L n)) :
    Derives Γ (PacketReaderStateSyntax.carrier w n) := PacketReaderStateSyntax.intro_carrier w L z o o n hn

end PPAC.Migration.Internal.PacketReaderInitSeed
