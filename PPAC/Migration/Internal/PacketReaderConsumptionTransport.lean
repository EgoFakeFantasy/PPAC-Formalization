import PPAC.Migration.Internal.PacketReaderConsumptionSyntax

/-! Equality transports only actual original input fields and actual state carriers. -/
namespace PPAC.Migration.Internal.PacketReaderConsumptionTransport
open Source SourceAlgebra SourceLogic PacketReaderConsumptionSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem head_rest {m} {Γ : Context m} (w l h x r : Fin m) (he : Derives Γ (.equal x r))
    (hh : Derives Γ (PacketReaderInputSyntax.headRest w l h x)) : Derives Γ (PacketReaderInputSyntax.headRest w l h r) := by
  let P := PacketReaderInputSyntax.headRest w.castSucc l.castSucc h.castSucc (Fin.last m)
  have h0 : P.instantiate x = PacketReaderInputSyntax.headRest w l h x := by simp only [P,Formula.instantiate,PacketReaderInputSyntax.headRest_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  have h1 : P.instantiate r = PacketReaderInputSyntax.headRest w l h r := by simp only [P,Formula.instantiate,PacketReaderInputSyntax.headRest_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  exact of_eq h1 (Derives.eqSubst P he (of_eq h0.symm hh))

theorem tail_target {m} {Γ : Context m} (w l x r : Fin m) (he : Derives Γ (.equal x r))
    (hh : Derives Γ (tail w l x)) : Derives Γ (tail w l r) := by
  let P := tail w.castSucc l.castSucc (Fin.last m)
  have h0 : P.instantiate x = tail w l x := by simp only [P,Formula.instantiate,tail_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  have h1 : P.instantiate r = tail w l r := by simp only [P,Formula.instantiate,tail_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  exact of_eq h1 (Derives.eqSubst P he (of_eq h0.symm hh))

theorem input_source {m} {Γ : Context m} (w n l N : Fin m) (he : Derives Γ (.equal n N))
    (hh : Derives Γ (input w n l)) : Derives Γ (input w N l) := by
  let P := input w.castSucc (Fin.last m) l.castSucc
  have h0 : P.instantiate n = input w n l := by simp only [P,Formula.instantiate,input_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  have h1 : P.instantiate N = input w N l := by simp only [P,Formula.instantiate,input_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  exact of_eq h1 (Derives.eqSubst P he (of_eq h0.symm hh))

theorem carrier_code {m} {Γ : Context m} (w n N : Fin m) (he : Derives Γ (.equal n N))
    (hh : Derives Γ (PacketReaderStateSyntax.carrier w n)) : Derives Γ (PacketReaderStateSyntax.carrier w N) := by
  let P := PacketReaderStateSyntax.carrier w.castSucc (Fin.last m)
  have h0 : P.instantiate n = PacketReaderStateSyntax.carrier w n := by simp only [P,Formula.instantiate,PacketReaderStateSyntax.carrier_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  have h1 : P.instantiate N = PacketReaderStateSyntax.carrier w N := by simp only [P,Formula.instantiate,PacketReaderStateSyntax.carrier_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  exact of_eq h1 (Derives.eqSubst P he (of_eq h0.symm hh))

end PPAC.Migration.Internal.PacketReaderConsumptionTransport
