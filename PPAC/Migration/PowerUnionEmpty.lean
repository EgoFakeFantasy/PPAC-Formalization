import PPAC.Migration.PowerUnionOperation

/-! 空索引下幂集精确像及其并为空；纯对象逻辑推导。 -/
namespace PPAC.Migration.PowerUnionEmpty
open Source SourceAlgebra SourceLogic InsertSyntax PowerUnionSyntax

theorem range_empty {m} {Γ : Context m} (c a h : Fin m)
    (hz : Derives Γ (OmegaSyntax.empty a)) (hr : Derives Γ (PowerValueSyntax.range c a h)) : Derives Γ (OmegaSyntax.empty c) := by
  apply Derives.allI
  have hz' : Derives (Context.image Formula.raise Γ) (OmegaSyntax.empty a.castSucc) := by
    simpa only [Formula.raise, OmegaSyntax.empty_rename] using Derives.rename Fin.castSucc hz
  have hr' : Derives (Context.image Formula.raise Γ) (PowerValueSyntax.range c.castSucc a.castSucc h.castSucc) := by
    simpa only [Formula.raise, PowerValueSyntax.range_rename] using Derives.rename Fin.castSucc hr
  apply Derives.impI
  let M := Formula.mem (Fin.last m) c.castSucc
  let Γw := Context.add M (Context.image Formula.raise Γ)
  have hi := Derives.impE (.conjL (add (PowerValueSyntax.range_at c.castSucc a.castSucc h.castSucc (Fin.last m) hr') M))
    (Derives.hyp (Γ := Γw) (Or.inl rfl))
  let B := (Formula.mem (Fin.last (m+1)) a.castSucc.castSucc).conj
    (PowerValueSyntax.value h.castSucc.castSucc (Fin.last (m+1)) (Fin.last m).castSucc)
  let Ξ := Context.add B (Context.image Formula.raise Γw)
  change Derives Γw (.ex B) at hi
  apply Derives.exE (p := B) hi
  have hzB : Derives Ξ (OmegaSyntax.empty a.castSucc.castSucc) := by
    simpa only [Formula.raise, OmegaSyntax.empty_rename] using under (add hz' M) B
  exact .impE (OmegaSyntax.empty_at a.castSucc.castSucc (Fin.last (m+1)) hzB) (.conjL (.hyp (Or.inl rfl)))

theorem union_empty {m} {Γ : Context m} (y c : Fin m)
    (hz : Derives Γ (OmegaSyntax.empty c)) (hu : Derives Γ (unionOf y c)) : Derives Γ (OmegaSyntax.empty y) := by
  apply Derives.allI
  have hz' : Derives (Context.image Formula.raise Γ) (OmegaSyntax.empty c.castSucc) := by
    simpa only [Formula.raise, OmegaSyntax.empty_rename] using Derives.rename Fin.castSucc hz
  have hu' : Derives (Context.image Formula.raise Γ) (unionOf y.castSucc c.castSucc) := by
    simpa only [Formula.raise, unionOf_rename] using Derives.rename Fin.castSucc hu
  apply Derives.impI
  let M := Formula.mem (Fin.last m) y.castSucc
  let Γz := Context.add M (Context.image Formula.raise Γ)
  have hi := Derives.impE (.conjL (add (union_at y.castSucc c.castSucc (Fin.last m) hu') M))
    (Derives.hyp (Γ := Γz) (Or.inl rfl))
  let B := (Formula.mem (Fin.last (m+1)) c.castSucc.castSucc).conj (.mem (Fin.last m).castSucc (Fin.last (m+1)))
  let Ξ := Context.add B (Context.image Formula.raise Γz)
  change Derives Γz (.ex B) at hi
  apply Derives.exE (p := B) hi
  have hzB : Derives Ξ (OmegaSyntax.empty c.castSucc.castSucc) := by
    simpa only [Formula.raise, OmegaSyntax.empty_rename] using under (add hz' M) B
  exact .impE (OmegaSyntax.empty_at c.castSucc.castSucc (Fin.last (m+1)) hzB) (.conjL (.hyp (Or.inl rfl)))

theorem operation_empty {m} {Γ : Context m} (a h y : Fin m)
    (hz : Derives Γ (OmegaSyntax.empty a)) (hop : Derives Γ (operation a h y)) : Derives Γ (OmegaSyntax.empty y) := by
  let C := (PowerValueSyntax.range (Fin.last m) a.castSucc h.castSucc).conj (unionOf y.castSucc (Fin.last m))
  let Ξ := Context.add C (Context.image Formula.raise Γ)
  change Derives Γ (.ex C) at hop
  apply Derives.exE (p := C) hop
  have hzC : Derives Ξ (OmegaSyntax.empty a.castSucc) := by
    simpa only [Formula.raise, OmegaSyntax.empty_rename] using under hz C
  have hC : Derives Ξ C := .hyp (Or.inl rfl)
  simpa only [Formula.raise, OmegaSyntax.empty_rename] using union_empty y.castSucc (Fin.last m)
    (range_empty (Fin.last m) a.castSucc h.castSucc hzC (.conjL hC)) (.conjR hC)
end PPAC.Migration.PowerUnionEmpty
