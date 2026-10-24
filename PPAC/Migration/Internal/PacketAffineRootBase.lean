import PPAC.Migration.Internal.PacketAffineRootSyntax

/-! The original base application's existential fields are aligned to the specified root by object injectivity. -/
namespace PPAC.Migration.Internal.PacketAffineRootBase
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax PacketAffineRootSyntax
open SyntaxRenameQuerySyntax (of_eq)

def witnessBody {m} (wide : Bool) (w B r : Fin m) : Formula (m+2) :=
  (empty (slot 2 1)).conj ((PacketHornAffineSyntax.row wide (old 2 w) (slot 2 0) (slot 2 1) (slot 2 0) (old 2 r)).conj
    (.mem (slot 2 0) (old 2 B)))

theorem actual_witness {m} (wide : Bool) (w B r : Fin m) :
    PacketAffineApplicationSyntax.baseOutcome wide w B r = existsMany 2 (witnessBody wide w B r) := rfl

theorem forward {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (wide : Bool) (w B d t n r : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (PacketHornAffineSyntax.row wide w d t n r))
    (hb : Derives Γ (PacketAffineApplicationSyntax.baseOutcome wide w B r)) : Derives Γ (zeroCase B d t n) := by
  let C := witnessBody wide w B r
  let Δ := Context.add C (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 C _ (of_eq (actual_witness wide w B r) hb)
  have hZ2 := HornBinderRules.zf_body 2 hZ C
  have hw2 := of_eq (omega_rename w (old 2)) (HornBinderRules.under_body 2 hw C)
  have hr2 := of_eq (PacketHornAffineSyntax.row_rename wide w d t n r (old 2)) (HornBinderRules.under_body 2 hr C)
  have hC : Derives Δ C := .hyp (Or.inl rfl)
  have he (i : Fin 3) := SyntaxNodeInjective.constructor_input_eq hZ2 3 (PacketAffineRuleData.relation wide)
    (PacketAffineRuleData.relation wide) (old 2 w) (SyntaxAtomSyntax.three (slot 2 0) (slot 2 1) (slot 2 0))
    (SyntaxAtomSyntax.three (old 2 d) (old 2 t) (old 2 n)) (old 2 r) i hw2 (.conjL (.conjR hC)) hr2
  have hz := NaturalMultiplicationLaws.empty_subst (slot 2 1) (old 2 t) (he 1) (.conjL hC)
  have hd := mem_subst (he 0) (.conjR (.conjR hC))
  have hn := eq_trans (eq_symm (he 2)) (he 0)
  exact of_eq (zeroCase_rename B d t n (old 2)).symm (.conjI hz (.conjI hd hn))

theorem backward {m} {Γ : Context m} (wide : Bool) (w B d t n r : Fin m)
    (hr : Derives Γ (PacketHornAffineSyntax.row wide w d t n r)) (hz : Derives Γ (zeroCase B d t n)) :
    Derives Γ (PacketAffineApplicationSyntax.baseOutcome wide w B r) := by
  have hRow := PacketAffineRootTransport.row_output wide w d t n r d (.conjR (.conjR hz)) hr
  exact PacketAffineApplicationSyntax.intro_base wide w B r d
    (PacketHornAffineLocal.intro_base wide w B d r t (.conjL hz) hRow (.conjL (.conjR hz)))

theorem base_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (wide : Bool) (w B d t n r : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (PacketHornAffineSyntax.row wide w d t n r)) :
    Derives Γ ((PacketAffineApplicationSyntax.baseOutcome wide w B r).iff (zeroCase B d t n)) := by
  apply Derives.conjI
  · exact .impI (forward (ZFContext.add hZ _) wide w B d t n r (add hw _) (add hr _) (.hyp (Or.inl rfl)))
  · exact .impI (backward wide w B d t n r (add hr _) (.hyp (Or.inl rfl)))

end PPAC.Migration.Internal.PacketAffineRootBase
