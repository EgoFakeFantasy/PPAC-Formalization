import PPAC.Migration.Internal.SyntaxMixedTermExistence

/-! 混合项像仍有唯一输出；仅源码恢复索引，目标bound/free类别不参与唯一性假设。 -/
namespace PPAC.Migration.Internal.SyntaxMixedTermUnique
open Source SourceAlgebra SourceLogic OmegaSyntax GraphSyntax SyntaxRenameQuerySyntax SyntaxMixedTermSyntax
open SyntaxTermImageSyntax (maps maps_rename)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem from_branch {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (bound : Bool)
    (w r s a b c d n q v : Fin m) (hw : Derives Γ (omega w))
    (hb : Derives Γ (branch bound w (SyntaxIndexMapSyntax.selectMap bound r s) (SyntaxTermSyntax.limit bound a b) n q))
    (hv : Derives Γ (substituted w r s a b c d n v)) : Derives Γ (.equal q v) := by
  let B := branchBody bound w (SyntaxIndexMapSyntax.selectMap bound r s) (SyntaxTermSyntax.limit bound a b) n q
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) hb
  have hZ1 := ZFContext.under hZ B
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw B)
  have hv1 : Derives Δ (substituted w.castSucc r.castSucc s.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc v.castSucc) :=
    of_eq (substituted_rename w r s a b c d n v Fin.castSucc) (under hv B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hk := SyntaxMixedTermKnown.at_code hZ1 bound w.castSucc r.castSucc s.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc v.castSucc (Fin.last m)
    hw1 (.conjL hv1) (.conjL (.conjR hB))
  have heV := Derives.conjR (.impE (.conjL hk) hv1)
  have heQ : Derives Δ (edge (SyntaxIndexMapSyntax.selectMap bound r.castSucc s.castSucc) (Fin.last m) q.castSucc) :=
    of_eq (by simp only [SyntaxIndexMapSyntax.selectMap_map]) (.conjR (.conjR hB))
  have hm := SyntaxTermImageSyntax.selected bound _ _ _ _ _ _ _ (.conjL hv1)
  exact GraphProperties.single_valued _ _ _ _ _ (ZFContext.arithmetic hZ1).base.extensionality
    (SyntaxTermImageSyntax.image_function _ _ _ _ _ hm) heQ heV

theorem unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r s a b c d n q v : Fin m)
    (hw : Derives Γ (omega w)) (hq : Derives Γ (substituted w r s a b c d n q))
    (hv : Derives Γ (substituted w r s a b c d n v)) : Derives Γ (.equal q v) := by
  apply Derives.disjE (.conjR hq)
  · exact from_branch (ZFContext.add hZ _) true w r s a b c d n q v (add hw _) (.hyp (Or.inl rfl)) (add hv _)
  · exact from_branch (ZFContext.add hZ _) false w r s a b c d n q v (add hw _) (.hyp (Or.inl rfl)) (add hv _)

theorem unique_output {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r s a b c d n q : Fin m)
    (hw : Derives Γ (omega w)) (hq : Derives Γ (substituted w r s a b c d n q)) :
    Derives Γ (uniqueOutput w r s a b c d n q) := by
  apply Derives.allI
  apply Derives.impI
  let V := substituted w.castSucc r.castSucc s.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc (Fin.last m)
  let Δ := Context.add V (Context.image Formula.raise Γ)
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw V)
  have hq1 : Derives Δ (substituted w.castSucc r.castSucc s.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc q.castSucc) :=
    of_eq (substituted_rename w r s a b c d n q Fin.castSucc) (under hq V)
  exact unique (ZFContext.under hZ V) _ _ _ _ _ _ _ _ _ _ hw1 (.hyp (Or.inl rfl)) hq1

theorem actual_fiber {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r s a b c d n : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (input w r s a b c d n)) : Derives Γ (fiber w r s a b c d n) := by
  let Q := substituted w.castSucc r.castSucc s.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc (Fin.last m)
  let Δ := Context.add Q (Context.image Formula.raise Γ)
  apply Derives.exE (p := Q) (SyntaxMixedTermExistence.exists_output w r s a b c d n hi)
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw Q)
  have hQ : Derives Δ Q := .hyp (Or.inl rfl)
  have hu := unique_output (ZFContext.under hZ Q) _ _ _ _ _ _ _ _ _ hw1 hQ
  have ho : Derives Δ (fiber w.castSucc r.castSucc s.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc) := by
    apply Derives.exI (Fin.last m)
    exact of_eq (by simp only [Q, Formula.instantiate, Formula.rename, substituted_rename, uniqueOutput_rename,
      Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI hQ hu)
  exact of_eq (fiber_rename w r s a b c d n Fin.castSucc).symm ho

theorem exists_iff_input {m} {Γ : Context m} (w r s a b c d n : Fin m) :
    Derives Γ ((existsOutput w r s a b c d n).iff (input w r s a b c d n)) := by
  apply Derives.conjI
  · apply Derives.impI
    let E := existsOutput w r s a b c d n
    let Q := substituted w.castSucc r.castSucc s.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc (Fin.last m)
    let Δ := Context.add Q (Context.image Formula.raise (Context.add E Γ))
    apply Derives.exE (p := Q) (.hyp (Or.inl rfl))
    have ho := SyntaxMixedTermTyping.input_of_substituted w.castSucc r.castSucc s.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc (Fin.last m)
      (Derives.hyp (Or.inl rfl) : Derives Δ Q)
    exact of_eq (input_rename w r s a b c d n Fin.castSucc).symm ho
  · apply Derives.impI
    exact SyntaxMixedTermExistence.exists_output w r s a b c d n (.hyp (Or.inl rfl))

theorem fiber_iff_input {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r s a b c d n : Fin m)
    (hw : Derives Γ (omega w)) : Derives Γ ((fiber w r s a b c d n).iff (input w r s a b c d n)) := by
  apply Derives.conjI
  · apply Derives.impI
    let E := fiber w r s a b c d n
    let Q := (substituted w.castSucc r.castSucc s.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc (Fin.last m)).conj
      (uniqueOutput w.castSucc r.castSucc s.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc (Fin.last m))
    let Δ := Context.add Q (Context.image Formula.raise (Context.add E Γ))
    apply Derives.exE (p := Q) (.hyp (Or.inl rfl))
    have hQ : Derives Δ Q := .hyp (Or.inl rfl)
    have ho := SyntaxMixedTermTyping.input_of_substituted _ _ _ _ _ _ _ _ _ (.conjL hQ)
    exact of_eq (input_rename w r s a b c d n Fin.castSucc).symm ho
  · apply Derives.impI
    exact actual_fiber (ZFContext.add hZ _) w r s a b c d n (add hw _) (.hyp (Or.inl rfl))

end PPAC.Migration.Internal.SyntaxMixedTermUnique
