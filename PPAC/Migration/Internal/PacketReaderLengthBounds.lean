import PPAC.Migration.Internal.PacketReaderLengthInduction

/-! Every actual internal history index, including its last index, is bounded by the actual initial list length. -/
namespace PPAC.Migration.Internal.PacketReaderLengthBounds
open Source SourceAlgebra SourceLogic OmegaSyntax PacketReaderLengthSyntax PacketReaderHistorySyntax PacketReaderHistoryLaws PacketReaderConsumptionSyntax
open StructuralListLengthSyntax (hasLength hasLength_rename)
open NaturalAdditionBounds (below below_rename)
open SyntaxRenameQuerySyntax (of_eq)

theorem index_from_balance {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o n r l d f N i : Fin m)
    (hw : Derives Γ (omega w)) (hh : Derives Γ (history w B z o n r l d f))
    (hBal : Derives Γ (allBalance w f N)) (hi : Derives Γ (.mem i d)) : Derives Γ (below i N) := by
  have hd := OmegaStructureAlgebra.successor_member w d l (ZFContext.arithmetic hZ).base.extensionality hw (length_at _ _ _ _ _ _ _ _ _ hh) (successor_at _ _ _ _ _ _ _ _ _ hh)
  have hiN := StructuralListTraceOrder.member_member hZ w i d hw hd hi
  have hb := all_at w f N i hBal hiN
  let R := (Formula.mem (Fin.last m) w.castSucc).conj (lengthAt w.castSucc f.castSucc i.castSucc (Fin.last m))
  let Δ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) (PacketReaderLengthAt.exists_at hZ w B z o n r l d f i hw hh hi)
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hZ1 := ZFContext.under hZ R
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw R)
  have hi1 : Derives Δ (.mem i.castSucc w.castSucc) := under hiN R
  have hb1 := of_eq (balance_rename w f N i Fin.castSucc) (under hb R)
  have hs := balance_at _ _ _ _ _ hb1 (.conjR hR)
  simpa only [Formula.raise,below_rename] using PacketReaderLengthArithmetic.index_bound hZ1 _ _ _ _ hw1 hi1 (.conjL hR) hs

theorem index_bound {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o n r l d f L N i : Fin m)
    (hw : Derives Γ (omega w)) (hh : Derives Γ (history w B z o n r l d f))
    (hL : Derives Γ (input w n L)) (hN : Derives Γ (hasLength w L N))
    (hi : Derives Γ (.mem i d)) : Derives Γ (below i N) :=
  index_from_balance hZ w B z o n r l d f N i hw hh (PacketReaderLengthInduction.all_balance hZ w B z o n r l d f L N hw hh hL hN) hi

theorem history_bound {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o n r l d f L N : Fin m)
    (hw : Derives Γ (omega w)) (hh : Derives Γ (history w B z o n r l d f))
    (hL : Derives Γ (input w n L)) (hN : Derives Γ (hasLength w L N)) : Derives Γ (below l N) :=
  index_bound hZ w B z o n r l d f L N l hw hh hL hN (InsertLogic.new_member d l l (successor_at _ _ _ _ _ _ _ _ _ hh))

theorem no_too_long_history {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o n r l d f L N : Fin m)
    (hw : Derives Γ (omega w)) (hh : Derives Γ (history w B z o n r l d f))
    (hL : Derives Γ (input w n L)) (hN : Derives Γ (hasLength w L N)) : Derives Γ ((Formula.mem N l).neg) := by
  apply Derives.impI
  let H := Formula.mem N l
  have hZ1 := ZFContext.add hZ H
  exact NaturalOrderBasic.below_not_reverse hZ1 w l N (add hw H) (add (length_at _ _ _ _ _ _ _ _ _ hh) H)
    (add (history_bound hZ w B z o n r l d f L N hw hh hL hN) H) (.hyp (Or.inl rfl))

end PPAC.Migration.Internal.PacketReaderLengthBounds
