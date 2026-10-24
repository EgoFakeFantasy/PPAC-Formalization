import PPAC.Migration.Internal.PacketTokenLocal

/-! Naturality of all six token assignments follows from the actual head and premise rows. -/
namespace PPAC.Migration.Internal.PacketTokenNatural
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax HornBinderSyntax PacketTokenSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem row_environment {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (tag : Nat) (w a b c r : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (tagRow tag w a b c r)) :
    Derives Γ (environmentNat 3 w (SyntaxAtomSyntax.three a b c)) := by
  have hN := SyntaxNodeInjective.constructor_range hZ 3 tag w (SyntaxAtomSyntax.three a b c) r hw hr
  exact HornApplicationRules.intro_nat w (SyntaxAtomSyntax.three a b c) (fun i =>
    StructuralListTraceOrder.member_member hZ w (SyntaxAtomSyntax.three a b c i) r hw hN
      (SyntaxConstructors.child_member hZ 3 tag w (SyntaxAtomSyntax.three a b c) r i hw hr))

theorem entry_environment {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (tag : Nat) (w V a b c : Fin m)
    (hw : Derives Γ (omega w)) (he : Derives Γ (tagEntry tag w V a b c)) :
    Derives Γ (environmentNat 3 w (SyntaxAtomSyntax.three a b c)) := by
  let P := (tagRow tag w.castSucc a.castSucc b.castSucc c.castSucc (Fin.last m)).conj (.mem (Fin.last m) V.castSucc)
  let Δ := Context.add P (Context.image Formula.raise Γ)
  apply Derives.exE (p := P) he
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw P)
  have hP : Derives Δ P := .hyp (Or.inl rfl)
  have hn := row_environment (ZFContext.under hZ P) tag w.castSucc a.castSucc b.castSucc c.castSucc (Fin.last m) hw1 (.conjL hP)
  simpa only [Formula.raise, environmentNat_rename, SyntaxAtomSyntax.three_map] using hn

theorem largeAt_environment {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B V z y r : Fin m) (env : Fin 6 → Fin m)
    (hw : Derives Γ (omega w)) (hl : Derives Γ (largeAt w B V z y r env)) : Derives Γ (environmentNat 6 w env) := by
  have hh := row_environment hZ 2 w (env 0) (env 1) (env 2) r hw (.conjL hl)
  have hp0 := entry_environment hZ 0 w V (env 3) (env 4) (env 0) hw (.conjL (.conjR (.conjR hl)))
  have hp1 := entry_environment hZ 1 w V y (env 5) (env 2) hw (.conjR (.conjR (.conjR (.conjR hl))))
  have h0 := environmentNat_at w (SyntaxAtomSyntax.three (env 0) (env 1) (env 2)) hh 0
  have h1 := environmentNat_at w (SyntaxAtomSyntax.three (env 0) (env 1) (env 2)) hh 1
  have h2 := environmentNat_at w (SyntaxAtomSyntax.three (env 0) (env 1) (env 2)) hh 2
  have h3 := environmentNat_at w (SyntaxAtomSyntax.three (env 3) (env 4) (env 0)) hp0 0
  have h4 := environmentNat_at w (SyntaxAtomSyntax.three (env 3) (env 4) (env 0)) hp0 1
  have h5 := environmentNat_at w (SyntaxAtomSyntax.three y (env 5) (env 2)) hp1 1
  apply HornApplicationRules.intro_nat w env
  intro i
  exact Fin.cases h0 (fun j => Fin.cases h1 (fun k => Fin.cases h2 (fun l => Fin.cases h3
    (fun s => Fin.cases h4 (fun t => Fin.cases h5 (fun u => Fin.elim0 u) t) s) l) k) j) i

theorem large_environment {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B V r : Fin m) (env : Fin 6 → Fin m)
    (hw : Derives Γ (omega w)) (hl : Derives Γ (large w B V r env)) : Derives Γ (environmentNat 6 w env) := by
  let C := largeBody w B V r env
  let Δ := Context.add C (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 C _ hl
  have hw2 := of_eq (omega_rename w (old 2)) (HornBinderRules.under_body 2 hw C)
  have hC : Derives Δ C := .hyp (Or.inl rfl)
  exact of_eq (environmentNat_rename 6 w env (old 2)).symm
    (largeAt_environment (HornBinderRules.zf_body 2 hZ C) (old 2 w) (old 2 B) (old 2 V) (slot 2 0) (slot 2 1)
      (old 2 r) (fun i => old 2 (env i)) hw2 (.conjR (.conjR hC)))

end PPAC.Migration.Internal.PacketTokenNatural
