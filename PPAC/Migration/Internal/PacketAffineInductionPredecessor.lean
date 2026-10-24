import PPAC.Migration.Internal.PacketAffineInductionEntry

/-! Two internally witnessed predecessors of the same natural successor are aligned before using the IH. -/
namespace PPAC.Migration.Internal.PacketAffineInductionPredecessor
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax PacketAffineInductionSyntax PacketAffineRootSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem sound {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (wide : Bool) (w B V d t s n : Fin m)
    (hw : Derives Γ (omega w)) (ht : Derives Γ (.mem t w)) (hI : Derives Γ (correct wide w B V t))
    (hs : Derives Γ (successor s t)) (hp : Derives Γ (predecessor wide w B V d s n)) :
    Derives Γ (PacketAffineSyntax.affine w B d s n) := by
  let C := predecessorBody wide w B V d s n
  let Δ := Context.add C (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 C _ hp
  have hZ2 := HornBinderRules.zf_body 2 hZ C
  have hw2 := of_eq (omega_rename w (old 2)) (HornBinderRules.under_body 2 hw C)
  have ht2 : Derives Δ (.mem (old 2 t) (old 2 w)) := HornBinderRules.under_body 2 ht C
  have hI2 := of_eq (correct_rename wide w B V t (old 2)) (HornBinderRules.under_body 2 hI C)
  have hs2 := of_eq (successor_rename s t (old 2)) (HornBinderRules.under_body 2 hs C)
  have hC : Derives Δ C := .hyp (Or.inl rfl)
  have he := StructuralListCodeLength.predecessor_unique hZ2 (old 2 w) (old 2 s) (old 2 t) (slot 2 0)
    hw2 ht2 hs2 (.conjL hC)
  have hE := PacketAffineRootTransport.entry_tail wide (old 2 w) (old 2 V) (old 2 d) (slot 2 0) (slot 2 1) (old 2 t)
    (eq_symm he) (.conjR (.conjR hC))
  have hA := PacketAffineInductionEntry.entry_to_affine wide (old 2 w) (old 2 B) (old 2 V) (old 2 t) (old 2 d) (slot 2 1) hI2 hE
  exact of_eq (PacketAffineSyntax.affine_rename w B d s n (old 2)).symm
    (PacketAffineStep.advance hZ2 (old 2 w) (old 2 B) (old 2 d) (old 2 t) (slot 2 1) (old 2 s) (old 2 n)
      hw2 hA hs2 (.conjL (.conjR hC)))

theorem complete {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (wide : Bool) (w B V d t s n : Fin m)
    (hw : Derives Γ (omega w)) (ht : Derives Γ (.mem t w)) (hI : Derives Γ (correct wide w B V t))
    (hs : Derives Γ (successor s t)) (ha : Derives Γ (PacketAffineSyntax.affine w B d s n)) :
    Derives Γ (predecessor wide w B V d s n) := by
  have he := PacketAffineStep.retreat hZ w B d t s n hw ht hs ha
  let C := PacketAffineSyntax.stepBody w B d s n
  let Δ := Context.add C (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 C _ he
  have hZ2 := HornBinderRules.zf_body 2 hZ C
  have hw2 := of_eq (omega_rename w (old 2)) (HornBinderRules.under_body 2 hw C)
  have ht2 : Derives Δ (.mem (old 2 t) (old 2 w)) := HornBinderRules.under_body 2 ht C
  have hI2 := of_eq (correct_rename wide w B V t (old 2)) (HornBinderRules.under_body 2 hI C)
  have hs2 := of_eq (successor_rename s t (old 2)) (HornBinderRules.under_body 2 hs C)
  have hC : Derives Δ C := .hyp (Or.inl rfl)
  have hp := StructuralListCodeLength.predecessor_unique hZ2 (old 2 w) (old 2 s) (old 2 t) (slot 2 0)
    hw2 ht2 hs2 (.conjL hC)
  have hA := PacketAffineTransport.tail (old 2 w) (old 2 B) (old 2 d) (slot 2 0) (slot 2 1) (old 2 t)
    (eq_symm hp) (.conjL (.conjR hC))
  have hE := PacketAffineInductionEntry.affine_to_entry hZ2 wide (old 2 w) (old 2 B) (old 2 V) (old 2 t)
    (old 2 d) (slot 2 1) hw2 hI2 hA
  exact of_eq (predecessor_rename wide w B V d s n (old 2)).symm
    (intro_predecessor wide (old 2 w) (old 2 B) (old 2 V) (old 2 d) (old 2 s) (old 2 n) (old 2 t) (slot 2 1)
      hs2 (.conjR (.conjR hC)) hE)

end PPAC.Migration.Internal.PacketAffineInductionPredecessor
