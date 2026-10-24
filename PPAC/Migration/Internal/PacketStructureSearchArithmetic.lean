import PPAC.Migration.Internal.PacketStructureSearchEnvironment

/-! Canonical real premise members inherit actual numeric bounds; the affine radix is internally constructed and eliminated. -/
namespace PPAC.Migration.Internal.PacketStructureSearchArithmetic
open Source SourceAlgebra SourceLogic OmegaSyntax PacketStructureSyntax
open NaturalAdditionBounds (below below_rename)
open SyntaxRenameQuerySyntax (of_eq)

theorem token_input {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w V n t a : Fin m)
    (hw : Derives Γ (omega w)) (hv : Derives Γ (PacketTraceCore.value w V)) (ha : Derives Γ (PacketTokenSyntax.entry w V n t a)) : Derives Γ (below n a) :=
  PacketTokenBounds.input_below hZ w n t a hw (.impE (.conjL (PacketTokenCanonicalEntry.entry_iff 2 w V n t a hv)) ha)

theorem token_tail {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w V n t a : Fin m)
    (hw : Derives Γ (omega w)) (hv : Derives Γ (PacketTraceCore.value w V)) (ha : Derives Γ (PacketTokenSyntax.entry w V n t a)) : Derives Γ (below t a) :=
  PacketTokenBounds.tail_below hZ w n t a hw (.impE (.conjL (PacketTokenCanonicalEntry.entry_iff 2 w V n t a hv)) ha)

theorem tree_tail {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w V n t a : Fin m)
    (hw : Derives Γ (omega w)) (hv : Derives Γ (PacketTraceCore.value w V)) (ha : Derives Γ (treeEntry w V n t a)) : Derives Γ (below t a) :=
  PacketStructureTailBounds.tree_tail hZ w n t a hw (.impE (.conjL (PacketStructureCanonicalCases.entry_iff 3 3 w V (SyntaxAtomSyntax.three n t a) hv)) ha)

theorem forest_tail {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w V n l t a : Fin m)
    (hw : Derives Γ (omega w)) (hv : Derives Γ (PacketTraceCore.value w V)) (ha : Derives Γ (forestEntry w V n l t a)) : Derives Γ (below t a) :=
  PacketStructureTailBounds.forest_tail hZ w n l t a hw (.impE (.conjL (PacketStructureCanonicalCases.entry_iff 4 4 w V (four n l t a) hv)) ha)

theorem affine_tail {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w V d q n : Fin m)
    (hw : Derives Γ (omega w)) (hv : Derives Γ (PacketTraceCore.value w V)) (ha : Derives Γ (PacketTokenSyntax.tagEntry 1 w V d q n)) : Derives Γ (below q n) := by
  let P := PacketAffineLiteralSyntax.frame true w.castSucc (Fin.last m)
  let Δ := Context.add P (Context.image Formula.raise Γ)
  apply Derives.exE (p := P) (SyntaxNumerals.exists_numeral hZ 256 w hw)
  have hZ1 := ZFContext.under hZ P
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw P)
  have hv1 := of_eq (PacketTraceCore.value_rename w V Fin.castSucc) (under hv P)
  have ha1 := of_eq (PacketTokenSyntax.tagEntry_rename 1 w V d q n Fin.castSucc) (under ha P)
  have hP : Derives Δ P := .hyp (Or.inl rfl)
  have hA := PacketTokenEntryArithmetic.affine_of_entry hZ1 true w.castSucc (Fin.last m) V.castSucc d.castSucc q.castSucc n.castSucc hw1 (.conjR hP) hv1 ha1
  exact of_eq (below_rename q n Fin.castSucc).symm
    (PacketDivisionDescentCore.quotient_below hZ1 true w.castSucc (Fin.last m) d.castSucc q.castSucc n.castSucc hw1 (.conjR hP) hA)

end PPAC.Migration.Internal.PacketStructureSearchArithmetic
