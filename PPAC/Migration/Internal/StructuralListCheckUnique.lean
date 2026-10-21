import PPAC.Migration.Internal.StructuralListCheckMinimal

/-! 首个终端的实际索引与值唯一；给所有内部自然码取得实际检查唯一纤维。 -/
namespace PPAC.Migration.Internal.StructuralListCheckUnique
open Source SourceAlgebra SourceLogic OmegaSyntax StructuralListProjectionSyntax StructuralListCheckSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem index_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n r s a b : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (checkedAt w n r a)) (hb : Derives Γ (checkedAt w n s b)) :
    Derives Γ (.equal r s) := by
  have hr := Derives.conjL (.conjL (.conjL ha))
  have hs := Derives.conjL (.conjL (.conjL hb))
  let C := (Formula.mem r s).disj (.mem s r)
  have hcmp := NaturalOrderBasic.compare hZ w r s hw hr hs
  apply Derives.disjE hcmp
  · exact .hyp (Or.inl rfl)
  · apply Derives.disjE (.hyp (Or.inl rfl))
    · have hno := before_at w n s r (add (add (.conjR hb) C) (.mem r s)) (.hyp (Or.inl rfl))
      have ho := intro_occurs w n r a (add (add (.conjR (.conjL (.conjL ha))) C) (.mem r s)) (add (add (.conjR (.conjL ha)) C) (.mem r s))
      exact .botE (.impE hno ho)
    · have hno := before_at w n r s (add (add (.conjR ha) C) (.mem s r)) (.hyp (Or.inl rfl))
      have ho := intro_occurs w n s b (add (add (.conjR (.conjL (.conjL hb))) C) (.mem s r)) (add (add (.conjR (.conjL hb)) C) (.mem s r))
      exact .botE (.impE hno ho)

theorem at_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n r s a b : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (checkedAt w n r a)) (hb : Derives Γ (checkedAt w n s b)) :
    Derives Γ (.equal a b) := by
  have he := index_unique hZ w n r s a b hw ha hb
  have hi := StructuralListIterationTransport.index_subst false w n r s a he (.conjR (.conjL (.conjL ha)))
  exact StructuralListIterationTransport.unique hZ false w n s a b hw (.conjL (.conjL (.conjL hb))) hi (.conjR (.conjL (.conjL hb)))

theorem value_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n a b : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (checkValue w n a)) (hb : Derives Γ (checkValue w n b)) :
    Derives Γ (.equal a b) := by
  let R := checkedAt w.castSucc n.castSucc (Fin.last m) a.castSucc
  let Ξ := Context.add R (Context.image Formula.raise Γ)
  change Derives Γ (.ex R) at ha
  apply Derives.exE (p := R) ha
  have hb1 : Derives Ξ (checkValue w.castSucc n.castSucc b.castSucc) := by simpa only [Formula.raise, checkValue_rename] using under hb R
  let S := checkedAt w.castSucc.castSucc n.castSucc.castSucc (Fin.last (m+1)) b.castSucc.castSucc
  let Δ := Context.add S (Context.image Formula.raise Ξ)
  change Derives Ξ (.ex S) at hb1
  apply Derives.exE (p := S) hb1
  have hZ2 : ZFContext.Evidence Δ := ZFContext.under (ZFContext.under hZ R) S
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using under (under hw R) S
  have hR : Derives Ξ R := .hyp (Or.inl rfl)
  have hR2 : Derives Δ (checkedAt w.castSucc.castSucc n.castSucc.castSucc (Fin.last m).castSucc a.castSucc.castSucc) := by
    simpa only [R, Formula.raise, checkedAt_rename] using under hR S
  exact at_unique hZ2 _ _ _ _ _ _ hw2 hR2 (.hyp (Or.inl rfl))

theorem exists_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (.mem n w)) : Derives Γ (checkFiber w n) := by
  have hb := StructuralListCheckMinimal.exists_check hZ w n hw hn
  let B := checkValue w.castSucc n.castSucc (Fin.last m)
  let Ξ := Context.add B (Context.image Formula.raise Γ)
  change Derives Γ (.ex B) at hb
  apply Derives.exE (p := B) hb
  have hZ1 : ZFContext.Evidence Ξ := ZFContext.under hZ B
  have hw1 : Derives Ξ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw B
  have hB : Derives Ξ B := .hyp (Or.inl rfl)
  have hu : Derives Ξ (.all ((checkValue w.castSucc.castSucc n.castSucc.castSucc (Fin.last (m+1))).imp
      (.equal (Fin.last (m+1)) (Fin.last m).castSucc))) := by
    apply Derives.allI
    apply Derives.impI
    let C := checkValue w.castSucc.castSucc n.castSucc.castSucc (Fin.last (m+1))
    let Δ := Context.add C (Context.image Formula.raise Ξ)
    have hw2 : Derives Δ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw1 C
    have hOld : Derives Δ (checkValue w.castSucc.castSucc n.castSucc.castSucc (Fin.last m).castSucc) := by
      simpa only [B, Formula.raise, checkValue_rename] using under hB C
    exact value_unique (ZFContext.under hZ1 C) _ _ _ _ hw2 (.hyp (Or.inl rfl)) hOld
  have hout : Derives Ξ (checkFiber w.castSucc n.castSucc) := by
    apply Derives.exI (Fin.last m)
    simp only [Formula.instantiate, Formula.rename, checkValue_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
    exact .conjI hB hu
  simpa only [Formula.raise, checkFiber_rename] using hout
end PPAC.Migration.Internal.StructuralListCheckUnique
