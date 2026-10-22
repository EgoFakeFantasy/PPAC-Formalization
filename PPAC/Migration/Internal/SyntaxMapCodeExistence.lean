import PPAC.Migration.Internal.SyntaxMapCode

/-! 每个内部完整有限索引图实际取得唯一原自然列表码；不选择宿主索引函数。 -/
namespace PPAC.Migration.Internal.SyntaxMapCodeExistence
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxIndexMapSyntax SyntaxMapCodeSyntax
open StructuralListEncodeSyntax (encoding encoding_rename)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem exists_code {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r a c : Fin m)
    (hw : Derives Γ (omega w)) (hm : Derives Γ (indexMap w r a c)) : Derives Γ (existsCode w r a c) := by
  have he := StructuralListEncodeExistence.exists_encoding hZ w r a hw (SyntaxMapCode.omega_sequence hZ w r a c hw hm) (.conjL (.conjL hm))
  let K := encoding w.castSucc r.castSucc a.castSucc (Fin.last m)
  let Δ := Context.add K (Context.image Formula.raise Γ)
  change Derives Γ (.ex K) at he
  apply Derives.exE he
  have hm1 : Derives Δ (indexMap w.castSucc r.castSucc a.castSucc c.castSucc) := by simpa only [Formula.raise, indexMap_rename] using under hm K
  have hK : Derives Δ K := .hyp (Or.inl rfl)
  have ho : Derives Δ (existsCode w.castSucc r.castSucc a.castSucc c.castSucc) := by
    apply Derives.exI (Fin.last m)
    simp only [Formula.instantiate, encoded_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
    exact .conjI hK hm1
  simpa only [Formula.raise, existsCode_rename] using ho

theorem actual_code_fiber {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r a c : Fin m)
    (hw : Derives Γ (omega w)) (hm : Derives Γ (indexMap w r a c)) : Derives Γ (codeFiber w r a c) := by
  have he := exists_code hZ w r a c hw hm
  let K := encoded w.castSucc r.castSucc a.castSucc c.castSucc (Fin.last m)
  let Ξ := Context.add K (Context.image Formula.raise Γ)
  change Derives Γ (.ex K) at he
  apply Derives.exE he
  have hZ1 := ZFContext.under hZ K
  have hw1 : Derives Ξ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw K
  have hK : Derives Ξ K := .hyp (Or.inl rfl)
  have hu : Derives Ξ (.all ((encoded w.castSucc.castSucc r.castSucc.castSucc a.castSucc.castSucc c.castSucc.castSucc (Fin.last (m+1))).imp
      (.equal (Fin.last (m+1)) (Fin.last m).castSucc))) := by
    apply Derives.allI
    apply Derives.impI
    let L := encoded w.castSucc.castSucc r.castSucc.castSucc a.castSucc.castSucc c.castSucc.castSucc (Fin.last (m+1))
    let Δ := Context.add L (Context.image Formula.raise Ξ)
    have hw2 : Derives Δ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw1 L
    have hk2 : Derives Δ (encoded w.castSucc.castSucc r.castSucc.castSucc a.castSucc.castSucc c.castSucc.castSucc (Fin.last m).castSucc) := by
      simpa only [K, Formula.raise, encoded_rename] using under hK L
    exact SyntaxMapCode.unique_code (ZFContext.under hZ1 L) _ _ _ _ _ _ hw2 (.hyp (Or.inl rfl)) hk2
  have ho : Derives Ξ (codeFiber w.castSucc r.castSucc a.castSucc c.castSucc) := by
    apply Derives.exI (Fin.last m)
    simp only [Formula.instantiate, Formula.rename, encoded_rename, Formula.liftRen,
      Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
    exact .conjI hK hu
  simpa only [Formula.raise, codeFiber_rename] using ho
end PPAC.Migration.Internal.SyntaxMapCodeExistence
