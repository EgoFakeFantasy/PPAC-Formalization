import PPAC.Migration.Internal.StructuralListSuffixArithmetic

/-! 内部零后缀实际由原Nil编码；空域匹配是对象空集消去，不作宿主有限枚举。 -/
namespace PPAC.Migration.Internal.StructuralListSuffixBase
open Source SourceAlgebra SourceLogic OmegaSyntax StructuralListSyntax StructuralListSuffixSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem aligned_empty {m} {Γ : Context m} (w f k r n : Fin m) (hr : Derives Γ (empty r)) : Derives Γ (aligned w f k r n) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  let A := (Formula.mem (Fin.last m).castSucc.castSucc r.castSucc.castSucc.castSucc).conj
    (NaturalAdditionSyntax.sum w.castSucc.castSucc.castSucc k.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc)
  let Δ := Context.add A (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise Γ)))
  have hr3 : Derives Δ (empty r.castSucc.castSucc.castSucc) := by simpa only [Formula.raise, empty_rename] using add (OrdinalRestriction.raise_three hr) A
  have hA : Derives Δ A := .hyp (Or.inl rfl)
  exact .botE (.impE (empty_at _ _ hr3) (.conjL hA))

theorem empty_code {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w f k r : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (empty r)) : Derives Γ (existsCode w f k r) := by
  have hn := StructuralNil.unique_fiber hZ w hw
  let N := (((Formula.mem (Fin.last m) w.castSucc).conj (nilCode w.castSucc (Fin.last m))).conj (.all
    ((nilCode w.castSucc.castSucc (Fin.last (m+1))).imp (.equal (Fin.last (m+1)) (Fin.last m).castSucc))))
  let Δ := Context.add N (Context.image Formula.raise Γ)
  change Derives Γ (.ex N) at hn
  apply Derives.exE (p := N) hn
  have hZ1 : ZFContext.Evidence Δ := ZFContext.under hZ N
  have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw N
  have hr1 : Derives Δ (empty r.castSucc) := by simpa only [Formula.raise, empty_rename] using under hr N
  have hN : Derives Δ N := .hyp (Or.inl rfl)
  have hl := StructuralListLengthConstruct.nil_length hZ1 w.castSucc (Fin.last m) r.castSucc hw1 (.conjR (.conjL hN)) hr1
  have hm := aligned_empty w.castSucc f.castSucc k.castSucc r.castSucc (Fin.last m) hr1
  have hout := intro_code _ _ _ _ _ (.conjL (.conjL hN)) hl hm
  simpa only [Formula.raise, existsCode_rename] using hout

theorem empty_property {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w f l r : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (empty r)) : Derives Γ (property w f l r) := by
  apply Derives.allI
  apply Derives.impI
  apply Derives.impI
  let M := Formula.mem (Fin.last m) w.castSucc
  let S := NaturalAdditionSyntax.sum w.castSucc r.castSucc (Fin.last m) l.castSucc
  let Δ := Context.add S (Context.add M (Context.image Formula.raise Γ))
  have hZ1 : ZFContext.Evidence Δ := ZFContext.add (ZFContext.under hZ M) S
  have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using add (under hw M) S
  have hr1 : Derives Δ (empty r.castSucc) := by simpa only [Formula.raise, empty_rename] using add (under hr M) S
  exact empty_code hZ1 w.castSucc f.castSucc (Fin.last m) r.castSucc hw1 hr1
end PPAC.Migration.Internal.StructuralListSuffixBase
