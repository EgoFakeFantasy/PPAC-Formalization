import PPAC.Migration.Internal.SyntaxFreeSubstPoint

/-! 双向逐点关系的原Replacement总单值合同，覆盖全部内部自然长度。 -/
namespace PPAC.Migration.Internal.SyntaxFreeSubstExistence
open Source SourceAlgebra SourceLogic OmegaSyntax GraphSyntax ReplacementPredicates SyntaxRenameQuerySyntax SyntaxFreeSubstSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem decode_fiber {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (ρ : Fin 2 → Fin m) (a c i : Fin m)
    (hw : Derives Γ (omega (ρ 0))) (hf : Derives Γ (termGraph (ρ 0) (ρ 1) a c)) (hi : Derives Γ (.mem i a)) :
    Derives Γ (fiber decodeMatrix ρ i) := by
  have he : Derives Γ (hasValue decodeMatrix ρ i) :=
    of_eq (by simp only [hasValue, decodeMatrix_rel, paramsUp]) (SyntaxFreeSubstPoint.decoded_exists (ρ 0) (ρ 1) a c i hf hi)
  let Y := rel decodeMatrix (paramsUp ρ) i.castSucc (Fin.last m)
  let Ξ := Context.add Y (Context.image Formula.raise Γ)
  apply Derives.exE (p := Y) he
  have hY : Derives Ξ Y := .hyp (Or.inl rfl)
  have hu : Derives Ξ (unique decodeMatrix (paramsUp ρ) i.castSucc (Fin.last m)) := by
    apply Derives.allI
    apply Derives.impI
    let Z := rel decodeMatrix (paramsUp (paramsUp ρ)) i.castSucc.castSucc (Fin.last (m+1))
    let Δ := Context.add Z (Context.image Formula.raise Ξ)
    have hZ2 := ZFContext.under (ZFContext.under hZ Y) Z
    have hw2 : Derives Δ (omega (ρ 0).castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (under (under hw Y) Z)
    have hf2 : Derives Δ (termGraph (ρ 0).castSucc.castSucc (ρ 1).castSucc.castSucc a.castSucc.castSucc c.castSucc.castSucc) :=
      of_eq (by simp only [Formula.raise, termGraph_rename]) (under (under hf Y) Z)
    have hy2 : Derives Δ (decodedValue (ρ 0).castSucc.castSucc (ρ 1).castSucc.castSucc i.castSucc.castSucc (Fin.last m).castSucc) :=
      of_eq (by simp only [Y, Formula.raise, decodeMatrix_rel, decodedValue_rename, paramsUp]) (under hY Z)
    have hz2 : Derives Δ (decodedValue (ρ 0).castSucc.castSucc (ρ 1).castSucc.castSucc i.castSucc.castSucc (Fin.last (m+1))) :=
      of_eq (by simp only [Z, decodeMatrix_rel, paramsUp]) (Derives.hyp (Or.inl rfl) : Derives Δ Z)
    exact SyntaxFreeSubstPoint.decoded_unique hZ2 _ _ _ _ _ _ hw2 (.conjL (.conjL (.conjR hf2))) hz2 hy2
  have ho : Derives Ξ (fiber decodeMatrix (paramsUp ρ) i.castSucc) := by
    apply Derives.exI (Fin.last m)
    exact of_eq (by simp only [Y, Formula.instantiate, Formula.rename, rel_rename, unique_rename, paramsUp,
      Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI hY hu)
  exact of_eq (by simp only [Formula.raise, fiber_rename]) ho

theorem decode_total {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (ρ : Fin 2 → Fin m) (a c : Fin m)
    (hw : Derives Γ (omega (ρ 0))) (hf : Derives Γ (termGraph (ρ 0) (ρ 1) a c)) :
    Derives Γ (ReplacementPredicates.total decodeMatrix ρ a) := by
  apply Derives.allI
  apply Derives.impI
  let M := Formula.mem (Fin.last m) a.castSucc
  let Δ := Context.add M (Context.image Formula.raise Γ)
  have hw1 : Derives Δ (omega (ρ 0).castSucc) := of_eq (omega_rename _ Fin.castSucc) (under hw M)
  have hf1 : Derives Δ (termGraph (ρ 0).castSucc (ρ 1).castSucc a.castSucc c.castSucc) :=
    of_eq (termGraph_rename _ _ _ _ Fin.castSucc) (under hf M)
  exact decode_fiber (ZFContext.under hZ M) (paramsUp ρ) _ _ _ hw1 hf1 (.hyp (Or.inl rfl))

theorem encode_fiber {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (ρ : Fin 2 → Fin m) (a c i : Fin m)
    (hw : Derives Γ (omega (ρ 0))) (hf : Derives Γ (SyntaxIndexMapSyntax.indexMap (ρ 0) (ρ 1) a c)) (hi : Derives Γ (.mem i a)) :
    Derives Γ (fiber encodeMatrix ρ i) := by
  have he : Derives Γ (hasValue encodeMatrix ρ i) :=
    of_eq (by simp only [hasValue, encodeMatrix_rel, paramsUp]) (SyntaxFreeSubstPoint.encoded_exists hZ (ρ 0) (ρ 1) a c i hw hf hi)
  let Y := rel encodeMatrix (paramsUp ρ) i.castSucc (Fin.last m)
  let Ξ := Context.add Y (Context.image Formula.raise Γ)
  apply Derives.exE (p := Y) he
  have hY : Derives Ξ Y := .hyp (Or.inl rfl)
  have hu : Derives Ξ (unique encodeMatrix (paramsUp ρ) i.castSucc (Fin.last m)) := by
    apply Derives.allI
    apply Derives.impI
    let Z := rel encodeMatrix (paramsUp (paramsUp ρ)) i.castSucc.castSucc (Fin.last (m+1))
    let Δ := Context.add Z (Context.image Formula.raise Ξ)
    have hZ2 := ZFContext.under (ZFContext.under hZ Y) Z
    have hw2 : Derives Δ (omega (ρ 0).castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (under (under hw Y) Z)
    have hf2 : Derives Δ (SyntaxIndexMapSyntax.indexMap (ρ 0).castSucc.castSucc (ρ 1).castSucc.castSucc a.castSucc.castSucc c.castSucc.castSucc) :=
      of_eq (by simp only [Formula.raise, SyntaxIndexMapSyntax.indexMap_rename]) (under (under hf Y) Z)
    have hy2 : Derives Δ (encodedValue (ρ 0).castSucc.castSucc (ρ 1).castSucc.castSucc i.castSucc.castSucc (Fin.last m).castSucc) :=
      of_eq (by simp only [Y, Formula.raise, encodeMatrix_rel, encodedValue_rename, paramsUp]) (under hY Z)
    have hz2 : Derives Δ (encodedValue (ρ 0).castSucc.castSucc (ρ 1).castSucc.castSucc i.castSucc.castSucc (Fin.last (m+1))) :=
      of_eq (by simp only [Z, encodeMatrix_rel, paramsUp]) (Derives.hyp (Or.inl rfl) : Derives Δ Z)
    exact SyntaxFreeSubstPoint.encoded_unique hZ2 _ _ _ _ _ _ hw2 (.conjL (.conjR hf2)) hz2 hy2
  have ho : Derives Ξ (fiber encodeMatrix (paramsUp ρ) i.castSucc) := by
    apply Derives.exI (Fin.last m)
    exact of_eq (by simp only [Y, Formula.instantiate, Formula.rename, rel_rename, unique_rename, paramsUp,
      Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI hY hu)
  exact of_eq (by simp only [Formula.raise, fiber_rename]) ho

theorem encode_total {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (ρ : Fin 2 → Fin m) (a c : Fin m)
    (hw : Derives Γ (omega (ρ 0))) (hf : Derives Γ (SyntaxIndexMapSyntax.indexMap (ρ 0) (ρ 1) a c)) :
    Derives Γ (ReplacementPredicates.total encodeMatrix ρ a) := by
  apply Derives.allI
  apply Derives.impI
  let M := Formula.mem (Fin.last m) a.castSucc
  let Δ := Context.add M (Context.image Formula.raise Γ)
  have hw1 : Derives Δ (omega (ρ 0).castSucc) := of_eq (omega_rename _ Fin.castSucc) (under hw M)
  have hf1 : Derives Δ (SyntaxIndexMapSyntax.indexMap (ρ 0).castSucc (ρ 1).castSucc a.castSucc c.castSucc) :=
    of_eq (SyntaxIndexMapSyntax.indexMap_rename _ _ _ _ Fin.castSucc) (under hf M)
  exact encode_fiber (ZFContext.under hZ M) (paramsUp ρ) _ _ _ hw1 hf1 (.hyp (Or.inl rfl))

theorem decode_outputs {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (ρ : Fin 2 → Fin m) (a c : Fin m)
    (hw : Derives Γ (omega (ρ 0))) (hf : Derives Γ (termGraph (ρ 0) (ρ 1) a c)) :
    Derives Γ (RelationGraph.outputsInto decodeMatrix ρ a c) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  let B := (Formula.mem (Fin.last m).castSucc a.castSucc.castSucc).conj
    (rel decodeMatrix (paramsUp (paramsUp ρ)) (Fin.last m).castSucc (Fin.last (m+1)))
  let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise Γ))
  have hZ2 := SyntaxRenameBinders.zf_under_2 hZ B
  have hw2 : Derives Δ (omega (ρ 0).castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxRenameBinders.under_2 hw B)
  have hf2 : Derives Δ (termGraph (ρ 0).castSucc.castSucc (ρ 1).castSucc.castSucc a.castSucc.castSucc c.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise, termGraph_rename]) (SyntaxRenameBinders.under_2 hf B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  exact SyntaxFreeSubstPoint.decoded_target hZ2 (ρ 0).castSucc.castSucc (ρ 1).castSucc.castSucc a.castSucc.castSucc c.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) hw2 hf2
    (of_eq (by simp only [decodeMatrix_rel, paramsUp]) (.conjR hB))

theorem encode_outputs {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (ρ : Fin 2 → Fin m) (a : Fin m)
    (hw : Derives Γ (omega (ρ 0))) : Derives Γ (RelationGraph.outputsInto encodeMatrix ρ a (ρ 0)) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  let B := (Formula.mem (Fin.last m).castSucc a.castSucc.castSucc).conj
    (rel encodeMatrix (paramsUp (paramsUp ρ)) (Fin.last m).castSucc (Fin.last (m+1)))
  let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise Γ))
  have hw2 : Derives Δ (omega (ρ 0).castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxRenameBinders.under_2 hw B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  exact SyntaxFreeSubstPoint.encoded_natural (SyntaxRenameBinders.zf_under_2 hZ B) (ρ 0).castSucc.castSucc (ρ 1).castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) hw2
    (of_eq (by simp only [encodeMatrix_rel, paramsUp]) (.conjR hB))

end PPAC.Migration.Internal.SyntaxFreeSubstExistence
