import PPAC.Migration.Internal.PacketAffineApplicationSyntax

/-! Natural assignment guards are consequences of actual row/entry evidence, not added answer premises. -/
namespace PPAC.Migration.Internal.PacketAffineApplicationNatural
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax HornBinderSyntax PacketHornAffineSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem row_environment {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (wide : Bool) (w d t n r : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (row wide w d t n r)) :
    Derives Γ (environmentNat 3 w (SyntaxAtomSyntax.three d t n)) := by
  have hN := SyntaxNodeInjective.constructor_range hZ 3 (PacketAffineRuleData.relation wide) w (SyntaxAtomSyntax.three d t n) r hw hr
  exact HornApplicationRules.intro_nat w (SyntaxAtomSyntax.three d t n) (fun i =>
    StructuralListTraceOrder.member_member hZ w (SyntaxAtomSyntax.three d t n i) r hw hN
      (SyntaxConstructors.child_member hZ 3 (PacketAffineRuleData.relation wide) w (SyntaxAtomSyntax.three d t n) r i hw hr))

theorem entry_environment {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (wide : Bool) (w V d t n : Fin m)
    (hw : Derives Γ (omega w)) (he : Derives Γ (entry wide w V d t n)) :
    Derives Γ (environmentNat 3 w (SyntaxAtomSyntax.three d t n)) := by
  let P := (row wide w.castSucc d.castSucc t.castSucc n.castSucc (Fin.last m)).conj (.mem (Fin.last m) V.castSucc)
  let Δ := Context.add P (Context.image Formula.raise Γ)
  apply Derives.exE (p := P) he
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw P)
  have hP : Derives Δ P := .hyp (Or.inl rfl)
  have hr := row_environment (ZFContext.under hZ P) wide w.castSucc d.castSucc t.castSucc n.castSucc (Fin.last m) hw1 (.conjL hP)
  simpa only [Formula.raise, environmentNat_rename, SyntaxAtomSyntax.three_map] using hr

theorem base_digit {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (wide : Bool) (w B d r : Fin m)
    (hw : Derives Γ (omega w)) (hb : Derives Γ (base wide w B d r)) : Derives Γ (.mem d w) := by
  let P := (empty (Fin.last m)).conj
    ((row wide w.castSucc d.castSucc (Fin.last m) d.castSucc r.castSucc).conj (.mem d.castSucc B.castSucc))
  let Δ := Context.add P (Context.image Formula.raise Γ)
  apply Derives.exE (p := P) hb
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw P)
  have hP : Derives Δ P := .hyp (Or.inl rfl)
  have hn := row_environment (ZFContext.under hZ P) wide w.castSucc d.castSucc (Fin.last m) d.castSucc r.castSucc hw1 (.conjL (.conjR hP))
  exact environmentNat_at w.castSucc (SyntaxAtomSyntax.three d.castSucc (Fin.last m) d.castSucc) hn 0

theorem step_environment {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (wide : Bool) (w B V d t a r : Fin m)
    (hw : Derives Γ (omega w)) (hs : Derives Γ (step wide w B V d t a r)) :
    Derives Γ (environmentNat 3 w (SyntaxAtomSyntax.three d t a)) := by
  let C := stepBody wide w B V d t a r
  let Δ := Context.add C (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 C _ hs
  have hw2 := of_eq (omega_rename w (old 2)) (HornBinderRules.under_body 2 hw C)
  have hC : Derives Δ C := .hyp (Or.inl rfl)
  have hn := entry_environment (HornBinderRules.zf_body 2 hZ C) wide (old 2 w) (old 2 V) (old 2 d) (old 2 t) (old 2 a)
    hw2 (.conjR (.conjR (.conjR hC)))
  exact of_eq (by simp only [environmentNat_rename, SyntaxAtomSyntax.three_map]) hn

end PPAC.Migration.Internal.PacketAffineApplicationNatural
