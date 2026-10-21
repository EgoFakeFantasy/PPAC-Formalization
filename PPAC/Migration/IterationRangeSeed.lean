import PPAC.Migration.IterationRangeSyntax

/-! 实际零长度轨迹证明种子属于精确末值集合。 -/
namespace PPAC.Migration.IterationRangeSeed
open Source SourceAlgebra SourceLogic OmegaSyntax IterationValueSyntax IterationRangeSyntax

theorem seed_value {m} {Γ : Context m} (hA : IterationContext.Evidence Γ) (z a : Fin m)
    (hz : Derives Γ (empty z)) : Derives Γ (value z z a a) := by
  have he := IterationBaseExistence.exists_base z a hA.pairing hA.extensionality hz
  let B := FiniteIterationSyntax.witness (Fin.last (m+1)) (Fin.last m).castSucc
    z.castSucc.castSucc z.castSucc.castSucc a.castSucc.castSucc
  let Γb := Context.add B (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply IterationExistence.eliminate_track z z a _ he
  have hB : Derives Γb B := .hyp (Or.inl rfl)
  have hr := intro_value (Fin.last (m+1)) (Fin.last m).castSucc z.castSucc.castSucc z.castSucc.castSucc
    a.castSucc.castSucc a.castSucc.castSucc hB (.conjL (.conjR (.conjR hB)))
  simpa only [Formula.raise, value_rename] using hr

theorem seed_member {m} {Γ : Context m} (hA : IterationContext.Evidence Γ) (c w z a : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) (hc : Derives Γ (IterationValueSyntax.range c w z a)) :
    Derives Γ (.mem a c) := member_from_value c w z a z a hc
      (OmegaStructureAlgebra.zero_member w z hA.extensionality hw hz) (seed_value hA z a hz)
end PPAC.Migration.IterationRangeSeed
