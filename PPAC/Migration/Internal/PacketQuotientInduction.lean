import PPAC.Migration.Internal.PacketQuotientInductionSyntax

/-! Original Foundation and Separation discharge every internal quotient IH for each object matrix. -/
namespace PPAC.Migration.Internal.PacketQuotientInduction
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax MinimalPredicates
open PacketQuotientInductionSyntax
open ReplacementPredicates (paramsUp)
open SyntaxRenameQuerySyntax (of_eq)

theorem large_nonempty {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (wide : Bool) (B n : Fin m)
    (hB : Derives Γ (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B))
    (hn : Derives Γ (Formula.mem n B).neg) : Derives Γ (empty n).neg := by
  apply Derives.impI
  exact .impE (add hn _) (SyntaxNumerals.less (ZFContext.add hZ _) 0 (PacketAffineRuleData.radix wide)
    (by cases wide <;> decide) n B (.hyp (Or.inl rfl)) (add hB _))

theorem point {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (wide : Bool)
    (p : Formula (k+1)) (ρ : Fin k → Fin m) (w B n : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B))
    (hb : Derives Γ (base p ρ w B)) (hs : Derives Γ (step p ρ w B)) (hn : Derives Γ (.mem n w))
    (hi : Derives Γ (BoundedInduction.below p ρ w n)) : Derives Γ (pred p ρ n) := by
  apply SourcePropositional.by_cases (Formula.mem n B) (pred p ρ n)
  · exact .impE (.impE (add (base_at p ρ w B n hb) _) (add hn _)) (.hyp (Or.inl rfl))
  · let H := (Formula.mem n B).neg
    let ΓH := Context.add H Γ
    let C := PacketDivisionSyntax.decompositionBody w B n
    let Δ := Context.add C (raisedContext 2 ΓH)
    apply HornBinderRules.eliminate_many 2 C _ (add (PacketDivisionInduction.exists_decomposition hZ wide w B n hw hB hn) H)
    have hZ2 := HornBinderRules.zf_body 2 (ZFContext.add hZ H) C
    have hw2 := of_eq (omega_rename w (old 2)) (HornBinderRules.under_body 2 (add hw H) C)
    have hB2 := of_eq (SyntaxNumeralSyntax.numeral_rename (PacketAffineRuleData.radix wide) B (old 2)) (HornBinderRules.under_body 2 (add hB H) C)
    have hH2 : Derives Δ (Formula.mem (old 2 n) (old 2 B)).neg := HornBinderRules.under_body 2 (Derives.hyp (Γ := ΓH) (Or.inl rfl)) C
    have hN2 : Derives Δ (.mem (old 2 n) (old 2 w)) := HornBinderRules.under_body 2 (add hn H) C
    have hC : Derives Δ C := .hyp (Or.inl rfl)
    have hqn := PacketDivisionDescentCore.quotient_strict hZ2 wide (old 2 w) (old 2 B) (slot 2 0) (slot 2 1) (old 2 n)
      hw2 hB2 hC (large_nonempty hZ2 wide (old 2 B) (old 2 n) hB2 hH2)
    have hI2 : Derives Δ (BoundedInduction.below p (fun i => old 2 (ρ i)) (old 2 w) (old 2 n)) :=
      of_eq (BoundedInduction.below_rename p ρ w n (old 2)) (HornBinderRules.under_body 2 (add hi H) C)
    have hPq := below_at p (fun i => old 2 (ρ i)) (old 2 w) (old 2 n) (slot 2 1) hI2
      (PacketAffineCore.tail_guard _ _ _ _ _ hC) hqn
    have hS2 := of_eq (step_rename p ρ w B (old 2)) (HornBinderRules.under_body 2 (add hs H) C)
    have ho := Derives.impE (.impE (.impE (.impE (step_at p (fun i => old 2 (ρ i)) (old 2 w) (old 2 B)
      (old 2 n) (slot 2 0) (slot 2 1) hS2) hN2) hH2) hC) hPq
    exact of_eq (pred_rename p ρ n (old 2)).symm ho

theorem progressive {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (wide : Bool)
    (p : Formula (k+1)) (ρ : Fin k → Fin m) (w B : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B))
    (hb : Derives Γ (base p ρ w B)) (hs : Derives Γ (step p ρ w B)) : Derives Γ (BoundedInduction.progressive p ρ w) := by
  apply Derives.allI
  apply Derives.impI
  apply Derives.impI
  let N := Formula.mem (Fin.last m) w.castSucc
  let I := BoundedInduction.below p (paramsUp ρ) w.castSucc (Fin.last m)
  let Δ := Context.add I (Context.add N (Context.image Formula.raise Γ))
  have hZ1 := ZFContext.add (ZFContext.add (ZFContext.rename hZ Fin.castSucc) N) I
  have hw1 := of_eq (omega_rename w Fin.castSucc) (Derives.rename Fin.castSucc hw)
  have hB1 := of_eq (SyntaxNumeralSyntax.numeral_rename (PacketAffineRuleData.radix wide) B Fin.castSucc) (Derives.rename Fin.castSucc hB)
  have hb1 := of_eq (base_rename p ρ w B Fin.castSucc) (Derives.rename Fin.castSucc hb)
  have hs1 := of_eq (step_rename p ρ w B Fin.castSucc) (Derives.rename Fin.castSucc hs)
  have hN : Derives Δ N := .hyp (Or.inr (Or.inl rfl))
  have hI : Derives Δ I := .hyp (Or.inl rfl)
  exact point hZ1 wide p (paramsUp ρ) w.castSucc B.castSucc (Fin.last m)
    (add (add hw1 N) I) (add (add hB1 N) I) (add (add hb1 N) I) (add (add hs1 N) I) hN hI

theorem all_holds {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (wide : Bool)
    (p : Formula (k+1)) (ρ : Fin k → Fin m) (w B : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B))
    (hb : Derives Γ (base p ρ w B)) (hs : Derives Γ (step p ρ w B)) : Derives Γ (BoundedInduction.holds p ρ w) :=
  BoundedInduction.induction_on_set p ρ w (ZFContext.separation hZ p.neg) (ZFContext.arithmetic hZ).base.foundation
    (progressive hZ wide p ρ w B hw hB hb hs)

end PPAC.Migration.Internal.PacketQuotientInduction
