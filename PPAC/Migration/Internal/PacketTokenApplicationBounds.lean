import PPAC.Migration.Internal.PacketTokenEntryArithmetic

/-! Auxiliary digit, quotient and recursive output bounds come from actual canonical affine premises. -/
namespace PPAC.Migration.Internal.PacketTokenApplicationBounds
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax HornExprBounds PacketTokenSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem row_bounds {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (tag : Nat) (w a b c r : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (tagRow tag w a b c r)) :
    Derives Γ (environmentBound 3 r (SyntaxAtomSyntax.three a b c)) :=
  intro_environmentBound r (SyntaxAtomSyntax.three a b c) (fun i => .disjR
    (SyntaxConstructors.child_member hZ 3 tag w (SyntaxAtomSyntax.three a b c) r i hw hr))

theorem largeAt_bounds {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B C V z y r : Fin m) (env : Fin 6 → Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B))
    (hC : Derives Γ (SyntaxNumeralSyntax.numeral 256 C)) (hv : Derives Γ (PacketTraceCore.value w V))
    (hl : Derives Γ (largeAt w B V z y r env)) : Derives Γ (environmentBound 6 r env) := by
  have hr := Derives.conjL hl
  have hrN := SyntaxNodeInjective.constructor_range hZ 3 2 w (SyntaxAtomSyntax.three (env 0) (env 1) (env 2)) r hw hr
  have hf (i : Fin 3) : Derives Γ (NaturalAdditionBounds.below (SyntaxAtomSyntax.three (env 0) (env 1) (env 2) i) r) :=
    .disjR (SyntaxConstructors.child_member hZ 3 2 w (SyntaxAtomSyntax.three (env 0) (env 1) (env 2)) r i hw hr)
  have hA0 := PacketTokenEntryArithmetic.affine_of_entry hZ false w B V (env 3) (env 4) (env 0) hw hB hv (.conjL (.conjR (.conjR hl)))
  have hA1 := PacketTokenEntryArithmetic.affine_of_entry hZ true w C V y (env 5) (env 2) hw hC hv (.conjR (.conjR (.conjR (.conjR hl))))
  have h3 := NaturalOrderBasic.transitive hZ w (env 3) (env 0) r hw hrN
    (PacketTokenEntryArithmetic.digit_below_output hZ w B (env 3) (env 4) (env 0) hw hA0) (hf 0)
  have h4 := NaturalOrderBasic.transitive hZ w (env 4) (env 0) r hw hrN
    (PacketDivisionDescentCore.quotient_below hZ false w B (env 3) (env 4) (env 0) hw hB hA0) (hf 0)
  have h5 := NaturalOrderBasic.transitive hZ w (env 5) (env 2) r hw hrN
    (PacketDivisionDescentCore.quotient_below hZ true w C y (env 5) (env 2) hw hC hA1) (hf 2)
  apply intro_environmentBound r env
  intro i
  exact Fin.cases (hf 0) (fun j => Fin.cases (hf 1) (fun k => Fin.cases (hf 2) (fun l => Fin.cases h3
    (fun s => Fin.cases h4 (fun t => Fin.cases h5 (fun u => Fin.elim0 u) t) s) l) k) j) i

theorem large_bounds {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B C V r : Fin m) (env : Fin 6 → Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B))
    (hC : Derives Γ (SyntaxNumeralSyntax.numeral 256 C)) (hv : Derives Γ (PacketTraceCore.value w V))
    (hl : Derives Γ (large w B V r env)) : Derives Γ (environmentBound 6 r env) := by
  let L := largeBody w B V r env
  let Δ := Context.add L (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 L _ hl
  have hw2 := of_eq (omega_rename w (old 2)) (HornBinderRules.under_body 2 hw L)
  have hB2 := of_eq (SyntaxNumeralSyntax.numeral_rename 128 B (old 2)) (HornBinderRules.under_body 2 hB L)
  have hC2 := of_eq (SyntaxNumeralSyntax.numeral_rename 256 C (old 2)) (HornBinderRules.under_body 2 hC L)
  have hv2 := of_eq (PacketTraceCore.value_rename w V (old 2)) (HornBinderRules.under_body 2 hv L)
  have hL : Derives Δ L := .hyp (Or.inl rfl)
  exact of_eq (environmentBound_rename 6 r env (old 2)).symm
    (largeAt_bounds (HornBinderRules.zf_body 2 hZ L) (old 2 w) (old 2 B) (old 2 C) (old 2 V) (slot 2 0) (slot 2 1)
      (old 2 r) (fun i => old 2 (env i)) hw2 hB2 hC2 hv2 (.conjR (.conjR hL)))

end PPAC.Migration.Internal.PacketTokenApplicationBounds
