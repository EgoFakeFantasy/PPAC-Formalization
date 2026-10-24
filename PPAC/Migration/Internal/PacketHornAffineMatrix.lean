import PPAC.Migration.Internal.PacketHornAffineExpr

/-! The actual original affine rule matrices, including their guard and recursive premise. -/
namespace PPAC.Migration.Internal.PacketHornAffineMatrix
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax PacketHornAffineSyntax
open SyntaxRenameQuerySyntax (of_eq)
open PacketAffineRuleData (baseRule stepRule radix)
open YesMetaZFC.Automation

theorem base_at {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (wide : Bool) (w B z r V : Fin m) (env : Fin 1 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 1 w env))
    (hB : Derives Γ (SyntaxNumeralSyntax.numeral (radix wide) B)) (hz : Derives Γ (empty z)) :
    Derives Γ ((HornRuleSyntax.matrix (baseRule wide) w r V env).iff
      ((row wide w (env 0) z (env 0) r).conj (.mem (env 0) B))) := by
  have hh := PacketHornAffineExpr.base_head_iff hZ wide w z r env hw hn hz
  have hg := PacketHornAffineExpr.base_guard_iff hZ wide w B env hw hn hB
  apply Derives.conjI
  · apply Derives.impI
    have he : Derives (Context.add (HornRuleSyntax.matrix (baseRule wide) w r V env) Γ)
      (HornRuleSyntax.matrix (baseRule wide) w r V env) := .hyp (Or.inl rfl)
    exact .conjI (.impE (add (.conjL hh) _) (.conjL he))
      (.impE (add (.conjL hg) _) (.conjL (.conjL (.conjR he))))
  · apply Derives.impI
    have he : Derives (Context.add ((row wide w (env 0) z (env 0) r).conj (.mem (env 0) B)) Γ)
      ((row wide w (env 0) z (env 0) r).conj (.mem (env 0) B)) := .hyp (Or.inl rfl)
    exact .conjI (.impE (add (.conjR hh) _) (.conjL he))
      (.conjI (.conjI (.impE (add (.conjR hg) _) (.conjR he)) HornRuleSyntax.truth_proved) HornRuleSyntax.truth_proved)

theorem step_at {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (wide : Bool) (w B s y r V : Fin m) (env : Fin 3 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 3 w env))
    (hB : Derives Γ (SyntaxNumeralSyntax.numeral (radix wide) B))
    (hs : Derives Γ (successor s (env 1))) (hy : Derives Γ (NaturalAdditionSyntax.sum w (env 2) B y)) :
    Derives Γ ((HornRuleSyntax.matrix (stepRule wide) w r V env).iff
      ((row wide w (env 0) s y r).conj (entry wide w V (env 0) (env 1) (env 2)))) := by
  have hh := PacketHornAffineExpr.step_head_iff hZ wide w B s y r env hw hn hB hs hy
  have hp := PacketHornAffineExpr.step_premise_iff hZ wide w V env hw hn
  apply Derives.conjI
  · apply Derives.impI
    have he : Derives (Context.add (HornRuleSyntax.matrix (stepRule wide) w r V env) Γ)
      (HornRuleSyntax.matrix (stepRule wide) w r V env) := .hyp (Or.inl rfl)
    exact .conjI (.impE (add (.conjL hh) _) (.conjL he))
      (.impE (add (.conjL hp) _) (.conjL (.conjR (.conjR he))))
  · apply Derives.impI
    have he : Derives (Context.add ((row wide w (env 0) s y r).conj (entry wide w V (env 0) (env 1) (env 2))) Γ)
      ((row wide w (env 0) s y r).conj (entry wide w V (env 0) (env 1) (env 2))) := .hyp (Or.inl rfl)
    exact .conjI (.impE (add (.conjR hh) _) (.conjL he))
      (.conjI HornRuleSyntax.truth_proved (.conjI (.impE (add (.conjR hp) _) (.conjR he)) HornRuleSyntax.truth_proved))

end PPAC.Migration.Internal.PacketHornAffineMatrix
