import PPAC.Migration.Internal.RelationGraphSyntax

/-! 任意对象函数关系实际取得原Kuratowski索引对精确像；只用原Replacement及Pairing。 -/
namespace PPAC.Migration.Internal.RelationGraphPairs
open Source SourceAlgebra SourceLogic PairSyntax GraphSyntax ReplacementPredicates RelationGraphSyntax

theorem pair_unique {n m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (P : Formula (n+2)) (ρ : Fin n → Fin m)
    (d x p q : Fin m) (ht : Derives Γ (total P ρ d)) (hx : Derives Γ (.mem x d))
    (hp : Derives Γ (entry P ρ x p)) (hq : Derives Γ (entry P ρ x q)) : Derives Γ (.equal p q) := by
  let Y := (rel P (paramsUp ρ) x.castSucc (Fin.last m)).conj (ordered p.castSucc x.castSucc (Fin.last m))
  let Ξ := Context.add Y (Context.image Formula.raise Γ)
  change Derives Γ (.ex Y) at hp
  apply Derives.exE hp
  have hq1 : Derives Ξ (entry P (paramsUp ρ) x.castSucc q.castSucc) := by
    simpa only [Formula.raise, entry_rename, paramsUp] using under hq Y
  let Z := (rel P (paramsUp (paramsUp ρ)) x.castSucc.castSucc (Fin.last (m+1))).conj
    (ordered q.castSucc.castSucc x.castSucc.castSucc (Fin.last (m+1)))
  let Δ := Context.add Z (Context.image Formula.raise Ξ)
  change Derives Ξ (.ex Z) at hq1
  apply Derives.exE hq1
  have hZ2 := ZFContext.under (ZFContext.under hZ Y) Z
  have ht2 : Derives Δ (total P (paramsUp (paramsUp ρ)) d.castSucc.castSucc) := by
    simpa only [Formula.raise, total_rename, paramsUp] using under (under ht Y) Z
  have hY : Derives Ξ Y := .hyp (Or.inl rfl)
  have hY2 : Derives Δ
      ((rel P (paramsUp (paramsUp ρ)) x.castSucc.castSucc (Fin.last m).castSucc).conj
        (ordered p.castSucc.castSucc x.castSucc.castSucc (Fin.last m).castSucc)) := by
    simpa only [Y, Formula.raise, Formula.rename, rel_rename, ordered_rename, paramsUp] using under hY Z
  have hZp : Derives Δ Z := .hyp (Or.inl rfl)
  have hyz := relation_unique P _ _ _ _ _ ht2 (under (under hx Y) Z) (.conjL hY2) (.conjL hZp)
  have ho := GraphLogic.ordered_subst_right _ _ _ _ (eq_symm hyz) (.conjR hZp)
  exact OrderedPairLogic.unique _ _ _ _ (ZFContext.arithmetic hZ2).base.extensionality (.conjR hY2) ho

theorem exists_entry {n m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (P : Formula (n+2)) (ρ : Fin n → Fin m)
    (d x : Fin m) (ht : Derives Γ (total P ρ d)) (hx : Derives Γ (.mem x d)) :
    Derives Γ (hasValue (entryMatrix P) ρ x) := by
  have he := ReplacementFromCollection.fiber_value P ρ x (.impE (specialize_total P ρ d x ht) hx)
  let Y := rel P (paramsUp ρ) x.castSucc (Fin.last m)
  let Ξ := Context.add Y (Context.image Formula.raise Γ)
  change Derives Γ (.ex Y) at he
  apply Derives.exE he
  have hp := OrderedPairExistence.exists_pair x.castSucc (Fin.last m) (ZFContext.arithmetic (ZFContext.under hZ Y)).base.pairing
  let O := ordered (Fin.last (m+1)) x.castSucc.castSucc (Fin.last m).castSucc
  let Δ := Context.add O (Context.image Formula.raise Ξ)
  change Derives Ξ (.ex O) at hp
  apply Derives.exE hp
  have hY : Derives Ξ Y := .hyp (Or.inl rfl)
  have hY2 : Derives Δ (rel P (paramsUp (paramsUp ρ)) x.castSucc.castSucc (Fin.last m).castSucc) := by
    simpa only [Y, Formula.raise, rel_rename, paramsUp] using under hY O
  have hO : Derives Δ O := .hyp (Or.inl rfl)
  have he2 := intro_entry P _ x.castSucc.castSucc (Fin.last (m+1)) (Fin.last m).castSucc hY2 hO
  have ho : Derives Δ (hasValue (entryMatrix P) (paramsUp (paramsUp ρ)) x.castSucc.castSucc) := by
    apply Derives.exI (Fin.last (m+1))
    simpa only [Formula.instantiate, rel_rename, entryMatrix_rel, entry_rename, paramsUp,
      Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using he2
  simpa only [Formula.raise, hasValue_rename, paramsUp] using ho

theorem entry_fiber {n m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (P : Formula (n+2)) (ρ : Fin n → Fin m)
    (d x : Fin m) (ht : Derives Γ (total P ρ d)) (hx : Derives Γ (.mem x d)) :
    Derives Γ (fiber (entryMatrix P) ρ x) := by
  have he := exists_entry hZ P ρ d x ht hx
  let E := entry P (paramsUp ρ) x.castSucc (Fin.last m)
  let Ξ := Context.add E (Context.image Formula.raise Γ)
  simp only [hasValue, entryMatrix_rel] at he
  apply Derives.exE he
  have hZ1 := ZFContext.under hZ E
  have ht1 : Derives Ξ (total P (paramsUp ρ) d.castSucc) := by simpa only [Formula.raise, total_rename, paramsUp] using under ht E
  have hE : Derives Ξ E := .hyp (Or.inl rfl)
  have hu : Derives Ξ (unique (entryMatrix P) (paramsUp ρ) x.castSucc (Fin.last m)) := by
    apply Derives.allI
    apply Derives.impI
    let Q := rel (entryMatrix P) (paramsUp (paramsUp ρ)) x.castSucc.castSucc (Fin.last (m+1))
    let Δ := Context.add Q (Context.image Formula.raise Ξ)
    have ht2 : Derives Δ (total P (paramsUp (paramsUp ρ)) d.castSucc.castSucc) := by
      simpa only [Formula.raise, total_rename, paramsUp] using under ht1 Q
    have hp : Derives Δ (entry P (paramsUp (paramsUp ρ)) x.castSucc.castSucc (Fin.last m).castSucc) := by
      simpa only [E, Formula.raise, entry_rename, paramsUp] using under hE Q
    have hQ : Derives Δ (entry P (paramsUp (paramsUp ρ)) x.castSucc.castSucc (Fin.last (m+1))) := by
      simpa only [Q, entryMatrix_rel] using (Derives.hyp (Or.inl rfl) : Derives Δ Q)
    exact pair_unique (ZFContext.under hZ1 Q) P _ _ _ _ _ ht2 (under (under hx E) Q) hQ hp
  have ho : Derives Ξ (fiber (entryMatrix P) (paramsUp ρ) x.castSucc) := by
    apply Derives.exI (Fin.last m)
    simp only [Formula.instantiate, Formula.rename, unique_rename, entryMatrix_rel, entry_rename, paramsUp,
      Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
    exact .conjI hE hu
  simpa only [Formula.raise, fiber_rename, paramsUp] using ho

theorem pair_total {n m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (P : Formula (n+2)) (ρ : Fin n → Fin m)
    (d : Fin m) (ht : Derives Γ (total P ρ d)) : Derives Γ (total (entryMatrix P) ρ d) := by
  apply Derives.allI
  apply Derives.impI
  let M := Formula.mem (Fin.last m) d.castSucc
  let Δ := Context.add M (Context.image Formula.raise Γ)
  have ht1 : Derives Δ (total P (paramsUp ρ) d.castSucc) := by simpa only [Formula.raise, total_rename, paramsUp] using under ht M
  exact entry_fiber (ZFContext.under hZ M) P (paramsUp ρ) d.castSucc (Fin.last m) ht1 (.hyp (Or.inl rfl))

theorem exists_pair_graph {n m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (P : Formula (n+2)) (ρ : Fin n → Fin m)
    (d : Fin m) (ht : Derives Γ (total P ρ d)) :
    Derives Γ (.ex (pairGraph P (paramsUp ρ) d.castSucc (Fin.last m))) := by
  have hRep : Derives Γ ((Source.SetLanguage.replacement (entryMatrix P)).rename Fin.elim0) :=
    .hyp (hZ _ ⟨_, Source.SetLanguage.IsZFAxiom.replacement (entryMatrix P), rfl⟩)
  have he := Derives.impE (IterationValueCollection.replacement_instance (entryMatrix P) ρ d hRep) (pair_total hZ P ρ d ht)
  simpa only [imageExists, entryMatrix_graph] using he
end PPAC.Migration.Internal.RelationGraphPairs
