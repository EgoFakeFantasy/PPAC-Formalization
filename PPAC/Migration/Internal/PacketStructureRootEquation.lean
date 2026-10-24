import PPAC.Migration.Internal.PacketStructureRootPacket

/-! Unbounded structural outcomes are exactly the normalized specified-root cases, independently of reverse bounded search. -/
namespace PPAC.Migration.Internal.PacketStructureRootEquation
open Source SourceAlgebra SourceLogic OmegaSyntax PacketStructureSyntax PacketStructureDispatchData
open SyntaxRenameQuerySyntax (of_eq)

theorem two_eta {m} (xs : Fin 2 → Fin m) : xs = SyntaxAtomSyntax.two (xs 0) (xs 1) := by
  funext i
  exact Fin.cases rfl (fun j => Fin.cases rfl (fun k => Fin.elim0 k) j) i

theorem three_eta {m} (xs : Fin 3 → Fin m) : xs = SyntaxAtomSyntax.three (xs 0) (xs 1) (xs 2) := by
  funext i
  exact Fin.cases rfl (fun j => Fin.cases rfl (fun k => Fin.cases rfl (fun l => Fin.elim0 l) k) j) i

theorem four_eta {m} (xs : Fin 4 → Fin m) : xs = four (xs 0) (xs 1) (xs 2) (xs 3) := by
  funext i
  exact Fin.cases rfl (fun j => Fin.cases rfl (fun k => Fin.cases rfl (fun l => Fin.cases rfl (fun h => Fin.elim0 h) l) k) j) i

theorem outcomes_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (f : Family) (w V r : Fin m) (xs : Fin (width f) → Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (row (width f) (tag f) w xs r)) :
    Derives Γ ((PacketStructureDispatch.results false f w V r).iff (PacketStructureRootSyntax.criterion f w V xs)) := by
  cases f with
  | tree =>
    have hr0 := of_eq (congrArg (fun ys => row 3 3 w ys r) (three_eta xs)) hr
    exact PacketStructureRootTree.root_iff hZ w V (xs (0 : Fin 3)) (xs (1 : Fin 3)) (xs (2 : Fin 3)) r hw hr0
  | forest =>
    have hr0 := of_eq (congrArg (fun ys => row 4 4 w ys r) (four_eta xs)) hr
    exact SyntaxTypeLocalTransfer.disj_congr
      (PacketStructureRootNil.root_iff hZ w V (xs (0 : Fin 4)) (xs (1 : Fin 4)) (xs (2 : Fin 4)) (xs (3 : Fin 4)) r hw hr0)
      (PacketStructureRootCons.root_iff hZ w V (xs (0 : Fin 4)) (xs (1 : Fin 4)) (xs (2 : Fin 4)) (xs (3 : Fin 4)) r hw hr0)
  | packet =>
    have hr0 := of_eq (congrArg (fun ys => row 2 5 w ys r) (two_eta xs)) hr
    exact PacketStructureRootPacket.root_iff hZ w V (xs (0 : Fin 2)) (xs (1 : Fin 2)) r hw hr0

theorem condition_forward {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (f : Family) (w V r : Fin m) (xs : Fin (width f) → Fin m)
    (hw : Derives Γ (omega w)) (hv : Derives Γ (PacketTraceCore.value w V)) (hr : Derives Γ (row (width f) (tag f) w xs r))
    (hc : Derives Γ (PacketTraceSyntax.condition w r)) : Derives Γ (PacketStructureRootSyntax.criterion f w V xs) :=
  .impE (.conjL (outcomes_iff hZ f w V r xs hw hr)) (PacketStructureDispatch.condition_forward hZ f w V r xs hw hv hr hc)

end PPAC.Migration.Internal.PacketStructureRootEquation
