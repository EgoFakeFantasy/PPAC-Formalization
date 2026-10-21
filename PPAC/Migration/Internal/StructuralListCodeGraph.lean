import PPAC.Migration.Internal.StructuralListCodeInduction

/-! 精确完整字段图相同推出原列表码相等；不借用宿主函数外延性。 -/
namespace PPAC.Migration.Internal.StructuralListCodeGraph
open Source SourceAlgebra SourceLogic OmegaSyntax StructuralListCodeSyntax StructuralListFieldSyntax StructuralListFieldGraphSyntax StructuralListEncodeSyntax
open StructuralListLengthSyntax (hasLength)

theorem same_fields_point {m} {Γ : Context m} (w r a b f i y : Fin m)
    (ha : Derives Γ (fields w a r f)) (hb : Derives Γ (fields w b r f)) (hi : Derives Γ (.mem i r)) :
    Derives Γ ((field w a i y).iff (field w b i y)) := by
  have hA := law_at w a r f i y (.conjR (.conjR ha))
  have hB := law_at w b r f i y (.conjR (.conjR hb))
  apply Derives.conjI
  · apply Derives.impI
    exact .conjR (.impE (add (.conjL hB) _) (.impE (add (.conjR hA) _) (.conjI (add hi _) (.hyp (Or.inl rfl)))))
  · apply Derives.impI
    exact .conjR (.impE (add (.conjL hA) _) (.impE (add (.conjR hB) _) (.conjI (add hi _) (.hyp (Or.inl rfl)))))

theorem from_common_fields {m} {Γ : Context m} (w r a b f : Fin m)
    (ha : Derives Γ (fields w a r f)) (hb : Derives Γ (fields w b r f)) : Derives Γ (agree w r a b) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  let M := Formula.mem (Fin.last m).castSucc r.castSucc.castSucc
  let Δ := Context.add M (Context.image Formula.raise (Context.image Formula.raise Γ))
  have lift {p : Formula m} (hp : Derives Γ p) : Derives Δ p.raise.raise := add (Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hp)) M
  have ha2 : Derives Δ (fields w.castSucc.castSucc a.castSucc.castSucc r.castSucc.castSucc f.castSucc.castSucc) := by simpa only [Formula.raise, fields_rename] using lift ha
  have hb2 : Derives Δ (fields w.castSucc.castSucc b.castSucc.castSucc r.castSucc.castSucc f.castSucc.castSucc) := by simpa only [Formula.raise, fields_rename] using lift hb
  exact same_fields_point _ _ _ _ _ _ _ ha2 hb2 (.hyp (Or.inl rfl))

theorem same_fields_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r a b f : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (hasLength w a r)) (hb : Derives Γ (hasLength w b r))
    (hfa : Derives Γ (fields w a r f)) (hfb : Derives Γ (fields w b r f)) : Derives Γ (.equal a b) :=
  StructuralListCodeInduction.unique hZ w r a b hw ha hb (from_common_fields w r a b f hfa hfb)

theorem encoded_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w f r a b : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (encoding w f r a)) (hb : Derives Γ (encoding w f r b)) : Derives Γ (.equal a b) :=
  same_fields_unique hZ w r a b f hw (.conjR (.conjL ha)) (.conjR (.conjL hb)) (.conjR ha) (.conjR hb)
end PPAC.Migration.Internal.StructuralListCodeGraph
