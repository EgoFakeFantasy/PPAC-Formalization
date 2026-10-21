import PPAC.Migration.Internal.StructuralListFieldPairSyntax

/-! 字段索引对的实际存在唯一和原Replacement精确像，不抽取任何宿主选择函数。 -/
namespace PPAC.Migration.Internal.StructuralListFieldPairs
open Source SourceAlgebra SourceLogic OmegaSyntax PairSyntax StructuralListFieldSyntax StructuralListFieldPairSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n i p q : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (.mem i w))
    (hp : Derives Γ (entry w n i p)) (hq : Derives Γ (entry w n i q)) : Derives Γ (.equal p q) := by
  let Y := (field w.castSucc n.castSucc i.castSucc (Fin.last m)).conj (ordered p.castSucc i.castSucc (Fin.last m))
  let Ξ := Context.add Y (Context.image Formula.raise Γ)
  change Derives Γ (.ex Y) at hp
  apply Derives.exE (p := Y) hp
  have hq1 : Derives Ξ (entry w.castSucc n.castSucc i.castSucc q.castSucc) := by simpa only [Formula.raise, entry_rename] using under hq Y
  let Z := (field w.castSucc.castSucc n.castSucc.castSucc i.castSucc.castSucc (Fin.last (m+1))).conj
    (ordered q.castSucc.castSucc i.castSucc.castSucc (Fin.last (m+1)))
  let Δ := Context.add Z (Context.image Formula.raise Ξ)
  change Derives Ξ (.ex Z) at hq1
  apply Derives.exE (p := Z) hq1
  have hZ2 : ZFContext.Evidence Δ := ZFContext.under (ZFContext.under hZ Y) Z
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using under (under hw Y) Z
  have hY : Derives Ξ Y := .hyp (Or.inl rfl)
  have hY2 : Derives Δ ((field w.castSucc.castSucc n.castSucc.castSucc i.castSucc.castSucc (Fin.last m).castSucc).conj
      (ordered p.castSucc.castSucc i.castSucc.castSucc (Fin.last m).castSucc)) := by
    simpa only [Y, Formula.raise, Formula.rename, field_rename, ordered_rename] using under hY Z
  have hZv : Derives Δ Z := .hyp (Or.inl rfl)
  have heq := StructuralListFieldValues.unique hZ2 _ _ _ _ _ hw2 (under (under hi Y) Z) (.conjL hY2) (.conjL hZv)
  have ho := GraphLogic.ordered_subst_right _ _ _ _ (eq_symm heq) (.conjR hZv)
  exact OrderedPairLogic.unique _ _ _ _ (ZFContext.arithmetic hZ2).base.extensionality (.conjR hY2) ho

theorem exists_entry {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n i : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (.mem i w)) : Derives Γ (existsEntry w n i) := by
  have hy := StructuralListFieldValues.exists_value hZ w n i hw hi
  let Y := (Formula.mem (Fin.last m) w.castSucc).conj (field w.castSucc n.castSucc i.castSucc (Fin.last m))
  let Ξ := Context.add Y (Context.image Formula.raise Γ)
  change Derives Γ (.ex Y) at hy
  apply Derives.exE (p := Y) hy
  have hZ1 : ZFContext.Evidence Ξ := ZFContext.under hZ Y
  have hp := OrderedPairExistence.exists_pair i.castSucc (Fin.last m) (ZFContext.arithmetic hZ1).base.pairing
  let P := ordered (Fin.last (m+1)) i.castSucc.castSucc (Fin.last m).castSucc
  let Δ := Context.add P (Context.image Formula.raise Ξ)
  change Derives Ξ (.ex P) at hp
  apply Derives.exE (p := P) hp
  have hY : Derives Ξ Y := .hyp (Or.inl rfl)
  have hf : Derives Δ (field w.castSucc.castSucc n.castSucc.castSucc i.castSucc.castSucc (Fin.last m).castSucc) := by
    simpa only [Formula.raise, field_rename] using under (.conjR hY) P
  have hP : Derives Δ P := .hyp (Or.inl rfl)
  have he := intro_entry _ _ _ _ _ hf hP
  have hout := intro_existsEntry _ _ _ _ he
  simpa only [Formula.raise, existsEntry_rename] using hout

theorem exists_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n i : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (.mem i w)) : Derives Γ (pairFiber w n i) := by
  have hp := exists_entry hZ w n i hw hi
  let P := entry w.castSucc n.castSucc i.castSucc (Fin.last m)
  let Ξ := Context.add P (Context.image Formula.raise Γ)
  change Derives Γ (.ex P) at hp
  apply Derives.exE (p := P) hp
  have hZ1 : ZFContext.Evidence Ξ := ZFContext.under hZ P
  have hw1 : Derives Ξ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw P
  have hP : Derives Ξ P := .hyp (Or.inl rfl)
  have hu : Derives Ξ (.all ((entry w.castSucc.castSucc n.castSucc.castSucc i.castSucc.castSucc (Fin.last (m+1))).imp
      (.equal (Fin.last (m+1)) (Fin.last m).castSucc))) := by
    apply Derives.allI
    apply Derives.impI
    let Q := entry w.castSucc.castSucc n.castSucc.castSucc i.castSucc.castSucc (Fin.last (m+1))
    let Δ := Context.add Q (Context.image Formula.raise Ξ)
    have hZ2 : ZFContext.Evidence Δ := ZFContext.under hZ1 Q
    have hw2 : Derives Δ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw1 Q
    have hOld : Derives Δ (entry w.castSucc.castSucc n.castSucc.castSucc i.castSucc.castSucc (Fin.last m).castSucc) := by
      simpa only [P, Formula.raise, entry_rename] using under hP Q
    exact unique hZ2 _ _ _ _ _ hw2 (under (under hi P) Q) (.hyp (Or.inl rfl)) hOld
  have hout : Derives Ξ (pairFiber w.castSucc n.castSucc i.castSucc) := by
    apply Derives.exI (Fin.last m)
    simp only [Formula.instantiate, Formula.rename, entry_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
    exact .conjI hP hu
  simpa only [Formula.raise, pairFiber_rename] using hout

theorem total {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (ρ : Fin 2 → Fin m) (l : Fin m)
    (hw : Derives Γ (omega (ρ 0))) (hl : Derives Γ (.mem l (ρ 0))) :
    Derives Γ (ReplacementPredicates.total matrix ρ l) := by
  simp only [ReplacementPredicates.total, matrix_fiber, ReplacementPredicates.paramsUp]
  apply Derives.allI
  apply Derives.impI
  let M := Formula.mem (Fin.last m) l.castSucc
  let Δ := Context.add M (Context.image Formula.raise Γ)
  have hZ1 : ZFContext.Evidence Δ := ZFContext.under hZ M
  have hw1 : Derives Δ (omega (ρ 0).castSucc) := by simpa only [Formula.raise, omega_rename] using under hw M
  have hi := StructuralListTraceOrder.member_member hZ1 (ρ 0).castSucc (Fin.last m) l.castSucc hw1 (under hl M) (.hyp (Or.inl rfl))
  exact exists_unique hZ1 _ _ _ hw1 hi

theorem exists_graph {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n l : Fin m)
    (hw : Derives Γ (omega w)) (hl : Derives Γ (.mem l w)) : Derives Γ (existsGraph w n l) := by
  have hRep : Derives Γ ((Source.SetLanguage.replacement matrix).rename Fin.elim0) :=
    .hyp (hZ _ ⟨_, Source.SetLanguage.IsZFAxiom.replacement matrix, rfl⟩)
  have hi := Derives.impE (IterationValueCollection.replacement_instance matrix (Source.SetLanguage.args2 w n) l hRep)
    (total hZ (Source.SetLanguage.args2 w n) l hw hl)
  simpa only [ReplacementPredicates.imageExists, matrix_graph, ReplacementPredicates.paramsUp,
    PairSyntax.args2_first, PairSyntax.args2_second, existsGraph] using hi
end PPAC.Migration.Internal.StructuralListFieldPairs
