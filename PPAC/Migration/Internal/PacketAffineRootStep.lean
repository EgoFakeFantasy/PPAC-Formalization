import PPAC.Migration.Internal.PacketAffineRootBase

/-! All five original step witnesses are object-bound; head injectivity aligns digit, tail and output. -/
namespace PPAC.Migration.Internal.PacketAffineRootStep
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax PacketAffineRootSyntax
open SyntaxRenameQuerySyntax (of_eq)

def witnessBody {m} (wide : Bool) (w B V r : Fin m) : Formula (m+5) :=
  (successor (slot 5 3) (slot 5 1)).conj
    ((NaturalAdditionSyntax.sum (old 5 w) (slot 5 2) (old 5 B) (slot 5 4)).conj
      ((PacketHornAffineSyntax.row wide (old 5 w) (slot 5 0) (slot 5 3) (slot 5 4) (old 5 r)).conj
        (PacketHornAffineSyntax.entry wide (old 5 w) (old 5 V) (slot 5 0) (slot 5 1) (slot 5 2))))

theorem actual_witness {m} (wide : Bool) (w B V r : Fin m) :
    PacketAffineApplicationSyntax.stepOutcome wide w B V r = existsMany 5 (witnessBody wide w B V r) := rfl

theorem forward {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (wide : Bool) (w B V d t n r : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (PacketHornAffineSyntax.row wide w d t n r))
    (hs : Derives Γ (PacketAffineApplicationSyntax.stepOutcome wide w B V r)) :
    Derives Γ (predecessor wide w B V d t n) := by
  let C := witnessBody wide w B V r
  let Δ := Context.add C (raisedContext 5 Γ)
  apply HornBinderRules.eliminate_many 5 C _ (of_eq (actual_witness wide w B V r) hs)
  have hZ5 := HornBinderRules.zf_body 5 hZ C
  have hw5 := of_eq (omega_rename w (old 5)) (HornBinderRules.under_body 5 hw C)
  have hr5 := of_eq (PacketHornAffineSyntax.row_rename wide w d t n r (old 5)) (HornBinderRules.under_body 5 hr C)
  have hC : Derives Δ C := .hyp (Or.inl rfl)
  have he (i : Fin 3) := SyntaxNodeInjective.constructor_input_eq hZ5 3 (PacketAffineRuleData.relation wide)
    (PacketAffineRuleData.relation wide) (old 5 w) (SyntaxAtomSyntax.three (slot 5 0) (slot 5 3) (slot 5 4))
    (SyntaxAtomSyntax.three (old 5 d) (old 5 t) (old 5 n)) (old 5 r) i hw5 (.conjL (.conjR (.conjR hC))) hr5
  have hS := NaturalAdditionAlgebraLaws.successor_output_subst (slot 5 3) (old 5 t) (slot 5 1) (he 1) (.conjL hC)
  have hN := NaturalAdditionSyntax.output_subst (old 5 w) (slot 5 2) (old 5 B) (slot 5 4) (old 5 n) (he 2) (.conjL (.conjR hC))
  have hE := PacketAffineRootTransport.entry_digit wide (old 5 w) (old 5 V) (slot 5 0) (slot 5 1) (slot 5 2) (old 5 d)
    (he 0) (.conjR (.conjR (.conjR hC)))
  exact of_eq (predecessor_rename wide w B V d t n (old 5)).symm
    (intro_predecessor wide (old 5 w) (old 5 B) (old 5 V) (old 5 d) (old 5 t) (old 5 n) (slot 5 1) (slot 5 2) hS hN hE)

theorem backward {m} {Γ : Context m} (wide : Bool) (w B V d t n r : Fin m)
    (hr : Derives Γ (PacketHornAffineSyntax.row wide w d t n r)) (hp : Derives Γ (predecessor wide w B V d t n)) :
    Derives Γ (PacketAffineApplicationSyntax.stepOutcome wide w B V r) := by
  let C := predecessorBody wide w B V d t n
  let Δ := Context.add C (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 C _ hp
  have hr2 := of_eq (PacketHornAffineSyntax.row_rename wide w d t n r (old 2)) (HornBinderRules.under_body 2 hr C)
  have hC : Derives Δ C := .hyp (Or.inl rfl)
  have hs := PacketHornAffineSyntax.intro_step wide (old 2 w) (old 2 B) (old 2 V) (old 2 d) (slot 2 0) (slot 2 1)
    (old 2 r) (old 2 t) (old 2 n) (.conjL hC) (.conjL (.conjR hC)) hr2 (.conjR (.conjR hC))
  exact of_eq (PacketAffineApplicationSyntax.stepOutcome_rename wide w B V r (old 2)).symm
    (PacketAffineApplicationSyntax.intro_step wide (old 2 w) (old 2 B) (old 2 V) (old 2 r) (old 2 d) (slot 2 0) (slot 2 1) hs)

theorem step_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (wide : Bool) (w B V d t n r : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (PacketHornAffineSyntax.row wide w d t n r)) :
    Derives Γ ((PacketAffineApplicationSyntax.stepOutcome wide w B V r).iff (predecessor wide w B V d t n)) := by
  apply Derives.conjI
  · exact .impI (forward (ZFContext.add hZ _) wide w B V d t n r (add hw _) (add hr _) (.hyp (Or.inl rfl)))
  · exact .impI (backward wide w B V d t n r (add hr _) (.hyp (Or.inl rfl)))

end PPAC.Migration.Internal.PacketAffineRootStep
