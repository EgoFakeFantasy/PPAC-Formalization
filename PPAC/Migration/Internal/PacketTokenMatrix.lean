import PPAC.Migration.Internal.PacketTokenExpr

/-! Full original token matrices, all guards and all three ordered large premises. -/
namespace PPAC.Migration.Internal.PacketTokenMatrix
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax PacketTokenSyntax
open PacketTokenRuleData
open YesMetaZFC.Automation
open YesMetaZFC.Automation.ObjectHorn (Expr)

theorem small_at {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B r V : Fin m) (env : Fin 3 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 3 w env)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B)) :
    Derives Γ ((HornRuleSyntax.matrix smallRule w r V env).iff (small w B V (env 0) (env 1) (env 2) r)) := by
  have hh := PacketTokenExpr.variable_row_iff hZ 2 (SyntaxAtomSyntax.three (0 : Fin 3) 1 2) w r env hw hn
  have hg := HornRuleValue.guard_at hZ (.var (0 : Fin 3)) (.literal 128) w (env 0) B env hw hn
    (.conjI (environmentNat_at w env hn 0) (.eqRefl _)) hB
  have hp := PacketTokenExpr.variable_premise_iff hZ 1 (SyntaxAtomSyntax.three (0 : Fin 3) 1 2) w V env hw hn
  apply Derives.conjI
  · apply Derives.impI
    let M := HornRuleSyntax.matrix smallRule w r V env
    have he : Derives (Context.add M Γ) M := .hyp (Or.inl rfl)
    exact .conjI (.impE (add (.conjL hh) M) (.conjL he))
      (.conjI (.impE (add (.conjL hg) M) (.conjL (.conjL (.conjR he))))
        (.impE (add (.conjL hp) M) (.conjL (.conjR (.conjR he)))))
  · apply Derives.impI
    let M := small w B V (env 0) (env 1) (env 2) r
    have he : Derives (Context.add M Γ) M := .hyp (Or.inl rfl)
    exact .conjI (.impE (add (.conjR hh) M) (.conjL he))
      (.conjI (.conjI (.impE (add (.conjR hg) M) (.conjL (.conjR he))) HornRuleSyntax.truth_proved)
        (.conjI (.impE (add (.conjR hp) M) (.conjR (.conjR he))) HornRuleSyntax.truth_proved))

theorem large_at {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z y r V : Fin m) (env : Fin 6 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 6 w env)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B))
    (hz : Derives Γ (empty z)) (hy : Derives Γ (NaturalAdditionSyntax.sum w (env 3) B y)) :
    Derives Γ ((HornRuleSyntax.matrix largeRule w r V env).iff (largeAt w B V z y r env)) := by
  have hv (i : Fin 6) : Derives Γ (graph (.var i) w env (env i)) := .conjI (environmentNat_at w env hn i) (.eqRefl _)
  have hh := PacketTokenExpr.variable_row_iff hZ 2 (SyntaxAtomSyntax.three (0 : Fin 6) 1 2) w r env hw hn
  have hg0 := HornRuleValue.guard_at hZ (.literal (arity := 6) 0) (.var 4) w z (env 4) env hw hn hz (hv 4)
  have hg1 := HornRuleValue.guard_at hZ (.var (3 : Fin 6)) (.literal 128) w (env 3) B env hw hn (hv 3) hB
  have hp0 := PacketTokenExpr.variable_premise_iff hZ 0 (SyntaxAtomSyntax.three (3 : Fin 6) 4 0) w V env hw hn
  have hp1 := PacketTokenExpr.variable_premise_iff hZ 2 (SyntaxAtomSyntax.three (4 : Fin 6) 1 5) w V env hw hn
  have hp2 := PacketTokenExpr.shifted_premise_iff hZ w B y V env hw hn hB hy
  apply Derives.conjI
  · apply Derives.impI
    let M := HornRuleSyntax.matrix largeRule w r V env
    have he : Derives (Context.add M Γ) M := .hyp (Or.inl rfl)
    have hguards := Derives.conjL (.conjR he)
    have hprems := Derives.conjR (.conjR he)
    exact .conjI (.impE (add (.conjL hh) M) (.conjL he))
      (.conjI (.conjI (.impE (add (.conjL hg0) M) (.conjL hguards))
        (.impE (add (.conjL hg1) M) (.conjL (.conjR hguards))))
        (.conjI (.impE (add (.conjL hp0) M) (.conjL hprems))
          (.conjI (.impE (add (.conjL hp1) M) (.conjL (.conjR hprems)))
            (.impE (add (.conjL hp2) M) (.conjL (.conjR (.conjR hprems)))))))
  · apply Derives.impI
    let M := largeAt w B V z y r env
    have he : Derives (Context.add M Γ) M := .hyp (Or.inl rfl)
    have hguards := Derives.conjL (.conjR he)
    have hprems := Derives.conjR (.conjR he)
    exact .conjI (.impE (add (.conjR hh) M) (.conjL he))
      (.conjI (.conjI (.impE (add (.conjR hg0) M) (.conjL hguards))
        (.conjI (.impE (add (.conjR hg1) M) (.conjR hguards)) HornRuleSyntax.truth_proved))
        (.conjI (.impE (add (.conjR hp0) M) (.conjL hprems))
          (.conjI (.impE (add (.conjR hp1) M) (.conjL (.conjR hprems)))
            (.conjI (.impE (add (.conjR hp2) M) (.conjR (.conjR hprems))) HornRuleSyntax.truth_proved))))

end PPAC.Migration.Internal.PacketTokenMatrix
