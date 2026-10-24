import PPAC.Migration.Internal.PacketTokenMatrix

/-! The actual zero and shifted digit witnesses are existentially discharged in the token matrix. -/
namespace PPAC.Migration.Internal.PacketTokenLocal
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax HornBinderSyntax PacketTokenSyntax PacketTokenRuleData
open SyntaxRenameQuerySyntax (of_eq)

theorem large_forward {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B r V : Fin m) (env : Fin 6 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 6 w env)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B))
    (hm : Derives Γ (HornRuleSyntax.matrix largeRule w r V env)) : Derives Γ (large w B V r env) := by
  let Z := (Formula.mem (Fin.last m) w.castSucc).conj (empty (Fin.last m))
  let Ξ := Context.add Z (Context.image Formula.raise Γ)
  apply Derives.exE (p := Z) (SyntaxNumerals.exists_numeral hZ 0 w hw)
  have hZ1 := ZFContext.under hZ Z
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw Z)
  have hn1 := of_eq (environmentNat_rename 6 w env Fin.castSucc) (under hn Z)
  have hB1 := of_eq (SyntaxNumeralSyntax.numeral_rename 128 B Fin.castSucc) (under hB Z)
  have hm1 := of_eq (HornRuleSyntax.matrix_rename largeRule w r V env Fin.castSucc) (under hm Z)
  have hVZ : Derives Ξ Z := .hyp (Or.inl rfl)
  have he := ZFArithmetic.add_exists hZ1 w.castSucc (env 3).castSucc B.castSucc hw1
    (environmentNat_at w.castSucc (fun i => (env i).castSucc) hn1 3) (SyntaxNumerals.range hZ1 128 w.castSucc B.castSucc hw1 hB1)
  let Y := (Formula.mem (Fin.last (m+1)) w.castSucc.castSucc).conj
    (NaturalAdditionSyntax.sum w.castSucc.castSucc (env 3).castSucc.castSucc B.castSucc.castSucc (Fin.last (m+1)))
  let Δ := Context.add Y (Context.image Formula.raise Ξ)
  apply Derives.exE (p := Y) he
  have hZ2 := ZFContext.under hZ1 Y
  have hw2 := of_eq (omega_rename w.castSucc Fin.castSucc) (under hw1 Y)
  have hn2 := of_eq (environmentNat_rename 6 w.castSucc (fun i => (env i).castSucc) Fin.castSucc) (under hn1 Y)
  have hB2 := of_eq (SyntaxNumeralSyntax.numeral_rename 128 B.castSucc Fin.castSucc) (under hB1 Y)
  have hm2 := of_eq (HornRuleSyntax.matrix_rename largeRule w.castSucc r.castSucc V.castSucc (fun i => (env i).castSucc) Fin.castSucc) (under hm1 Y)
  have hz2 := of_eq (empty_rename (Fin.last m) Fin.castSucc) (under (.conjR hVZ) Y)
  have hY : Derives Δ Y := .hyp (Or.inl rfl)
  have ha := Derives.impE (.conjL (PacketTokenMatrix.large_at hZ2 w.castSucc.castSucc B.castSucc.castSucc
    (Fin.last m).castSucc (Fin.last (m+1)) r.castSucc.castSucc V.castSucc.castSucc (fun i => (env i).castSucc.castSucc)
    hw2 hn2 hB2 hz2 (.conjR hY))) hm2
  have ho := intro_large w.castSucc.castSucc B.castSucc.castSucc V.castSucc.castSucc r.castSucc.castSucc
    (Fin.last m).castSucc (Fin.last (m+1)) (fun i => (env i).castSucc.castSucc) hz2 (.conjR hY) ha
  simpa only [Formula.raise, large_rename] using ho

theorem large_backward {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B r V : Fin m) (env : Fin 6 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 6 w env)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B))
    (hl : Derives Γ (large w B V r env)) : Derives Γ (HornRuleSyntax.matrix largeRule w r V env) := by
  let C := largeBody w B V r env
  let Δ := Context.add C (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 C _ hl
  have hw2 := of_eq (omega_rename w (old 2)) (HornBinderRules.under_body 2 hw C)
  have hn2 := of_eq (environmentNat_rename 6 w env (old 2)) (HornBinderRules.under_body 2 hn C)
  have hB2 := of_eq (SyntaxNumeralSyntax.numeral_rename 128 B (old 2)) (HornBinderRules.under_body 2 hB C)
  have hC : Derives Δ C := .hyp (Or.inl rfl)
  exact of_eq (HornRuleSyntax.matrix_rename largeRule w r V env (old 2)).symm
    (.impE (.conjR (PacketTokenMatrix.large_at (HornBinderRules.zf_body 2 hZ C) (old 2 w) (old 2 B)
      (slot 2 0) (slot 2 1) (old 2 r) (old 2 V) (fun i => old 2 (env i)) hw2 hn2 hB2
      (.conjL hC) (.conjL (.conjR hC)))) (.conjR (.conjR hC)))

theorem large_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B r V : Fin m) (env : Fin 6 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 6 w env)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B)) :
    Derives Γ ((HornRuleSyntax.matrix largeRule w r V env).iff (large w B V r env)) := by
  apply Derives.conjI
  · exact .impI (large_forward (ZFContext.add hZ _) w B r V env (add hw _) (add hn _) (add hB _) (.hyp (Or.inl rfl)))
  · exact .impI (large_backward (ZFContext.add hZ _) w B r V env (add hw _) (add hn _) (add hB _) (.hyp (Or.inl rfl)))

end PPAC.Migration.Internal.PacketTokenLocal
