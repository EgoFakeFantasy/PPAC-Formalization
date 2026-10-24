import PPAC.Migration.Internal.PacketVarintExecutionFiberSyntax

/-! Only omega remains: the independent canonical unique-list fiber has exactly the internal natural-value domain. -/
namespace PPAC.Migration.Internal.PacketVarintExecution
open Source SourceAlgebra SourceLogic OmegaSyntax PacketVarintSyntax PacketVarintExecutionSyntax PacketVarintExecutionFiberSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem natural_to_fiber {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n : Fin m) (hw : Derives Γ (omega w))
    (hn : Derives Γ (.mem n w)) : Derives Γ (fiber w n) := by
  let S := (Formula.mem (Fin.last m) w.castSucc).conj (canonical w.castSucc n.castSucc (Fin.last m))
  let Δ := Context.add S (Context.image Formula.raise Γ)
  apply Derives.exE (p := S) (PacketVarintExecutionLiterals.exists_list hZ w n hw hn)
  have hZ1 := ZFContext.under hZ S
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw S)
  have hS : Derives Δ S := .hyp (Or.inl rfl)
  have hb := PacketVarintExecutionLiterals.byte_input hZ1 w.castSucc n.castSucc (Fin.last m) hw1 (.conjR hS)
  have hu : Derives Δ (uniqueAt w.castSucc n.castSucc (Fin.last m)) := by
    apply Derives.allI
    apply Derives.impI
    let H := canonical w.castSucc.castSucc n.castSucc.castSucc (Fin.last (m+1))
    have hZ2 := ZFContext.under hZ1 H
    have hw2 := of_eq (omega_rename w.castSucc Fin.castSucc) (under hw1 H)
    have hc2 := of_eq (canonical_rename w.castSucc n.castSucc (Fin.last m) Fin.castSucc) (under (.conjR hS) H)
    exact PacketVarintExecutionLiterals.list_unique hZ2 w.castSucc.castSucc n.castSucc.castSucc (Fin.last (m+1)) (Fin.last m).castSucc hw2 (.hyp (Or.inl rfl)) hc2
  simpa only [Formula.raise,fiber_rename] using intro_fiber w.castSucc n.castSucc (Fin.last m) (.conjL hS) (.conjR hS) hb hu

theorem fiber_to_natural {m} {Γ : Context m} (w n : Fin m) (hf : Derives Γ (fiber w n)) : Derives Γ (.mem n w) := by
  let R := fiberBody w n
  let Δ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) hf
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  exact .conjL (PacketVarintDomain.domain w.castSucc n.castSucc (Fin.last m) (.conjR (.conjL hR)))

theorem fiber_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n : Fin m) (hw : Derives Γ (omega w)) : Derives Γ ((fiber w n).iff (.mem n w)) :=
  .conjI (.impI (fiber_to_natural w n (.hyp (Or.inl rfl))))
    (.impI (natural_to_fiber (ZFContext.add hZ _) w n (add hw _) (.hyp (Or.inl rfl))))

theorem exists_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n : Fin m) (hw : Derives Γ (omega w)) : Derives Γ ((existsList w n).iff (.mem n w)) := by
  apply Derives.conjI
  · apply Derives.impI
    let S := (Formula.mem (Fin.last m) w.castSucc).conj (canonical w.castSucc n.castSucc (Fin.last m))
    let Δ := Context.add S (Context.image Formula.raise (Context.add (existsList w n) Γ))
    apply Derives.exE (p := S) (.hyp (Or.inl rfl))
    have hS : Derives Δ S := .hyp (Or.inl rfl)
    exact .conjL (PacketVarintDomain.domain w.castSucc n.castSucc (Fin.last m) (.conjR hS))
  · apply Derives.impI
    exact PacketVarintExecutionLiterals.exists_list (ZFContext.add hZ _) w n (add hw _) (.hyp (Or.inl rfl))

theorem all_law {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w : Fin m) (hw : Derives Γ (omega w)) : Derives Γ (allLaw w) := by
  apply Derives.allI
  have hw1 := of_eq (omega_rename w Fin.castSucc) (Derives.rename Fin.castSucc hw)
  exact fiber_iff (ZFContext.rename hZ Fin.castSucc) w.castSucc (Fin.last m) hw1

end PPAC.Migration.Internal.PacketVarintExecution
