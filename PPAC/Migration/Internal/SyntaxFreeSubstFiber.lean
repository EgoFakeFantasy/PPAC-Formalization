import PPAC.Migration.Internal.SyntaxFreeSubstCodeUnique

/-! 全内部原项列表/索引码的实际唯一纤维及精确接受输入双条件。 -/
namespace PPAC.Migration.Internal.SyntaxFreeSubstFiber
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxRenameQuerySyntax SyntaxFreeSubstSyntax
open SyntaxMapCodeSyntax (mapCode mapCode_rename)
attribute [local irreducible] NaturalRecursionSyntax.matrix

def mapExists {m} (w a c L : Fin m) : Formula m := .ex (codeConversion w.castSucc a.castSucc c.castSucc L.castSucc (Fin.last m))

def mapUnique {m} (w a c L S : Fin m) : Formula m := .all
  ((codeConversion w.castSucc a.castSucc c.castSucc L.castSucc (Fin.last m)).imp (.equal (Fin.last m) S.castSucc))

def mapFiber {m} (w a c L : Fin m) : Formula m := .ex
  ((codeConversion w.castSucc a.castSucc c.castSucc L.castSucc (Fin.last m)).conj (mapUnique w.castSucc a.castSucc c.castSucc L.castSucc (Fin.last m)))

theorem mapExists_rename {m k} (w a c L : Fin m) (ρ : Fin m → Fin k) :
    (mapExists w a c L).rename ρ = mapExists (ρ w) (ρ a) (ρ c) (ρ L) := by
  simp only [mapExists, Formula.rename, codeConversion_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem mapUnique_rename {m k} (w a c L S : Fin m) (ρ : Fin m → Fin k) :
    (mapUnique w a c L S).rename ρ = mapUnique (ρ w) (ρ a) (ρ c) (ρ L) (ρ S) := by
  simp only [mapUnique, Formula.rename, codeConversion_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem mapFiber_rename {m k} (w a c L : Fin m) (ρ : Fin m → Fin k) :
    (mapFiber w a c L).rename ρ = mapFiber (ρ w) (ρ a) (ρ c) (ρ L) := by
  simp only [mapFiber, Formula.rename, codeConversion_rename, mapUnique_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem map_unique_formula {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a c L S : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (codeConversion w a c L S)) : Derives Γ (mapUnique w a c L S) := by
  apply Derives.allI
  apply Derives.impI
  let H := codeConversion w.castSucc a.castSucc c.castSucc L.castSucc (Fin.last m)
  let Δ := Context.add H (Context.image Formula.raise Γ)
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw H)
  have hc1 : Derives Δ (codeConversion w.castSucc a.castSucc c.castSucc L.castSucc S.castSucc) := of_eq (codeConversion_rename w a c L S Fin.castSucc) (under hc H)
  exact SyntaxFreeSubstCodeUnique.map_unique (ZFContext.under hZ H) w.castSucc a.castSucc c.castSucc L.castSucc (Fin.last m) S.castSucc hw1 (.hyp (Or.inl rfl)) hc1

theorem map_actual_fiber {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a c L : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (termList w a c L)) : Derives Γ (mapFiber w a c L) := by
  let H := codeConversion w.castSucc a.castSucc c.castSucc L.castSucc (Fin.last m)
  let Δ := Context.add H (Context.image Formula.raise Γ)
  apply Derives.exE (p := H) (SyntaxFreeSubstCode.from_list hZ w a c L hw hi)
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw H)
  have hH : Derives Δ H := .hyp (Or.inl rfl)
  have hu := map_unique_formula (ZFContext.under hZ H) w.castSucc a.castSucc c.castSucc L.castSucc (Fin.last m) hw1 hH
  have ho : Derives Δ (mapFiber w.castSucc a.castSucc c.castSucc L.castSucc) := by
    apply Derives.exI (Fin.last m)
    exact of_eq (by simp only [H, Formula.instantiate, Formula.rename, codeConversion_rename, mapUnique_rename,
      Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI hH hu)
  exact of_eq (mapFiber_rename w a c L Fin.castSucc).symm ho

theorem map_exists_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a c L : Fin m)
    (hw : Derives Γ (omega w)) : Derives Γ ((mapExists w a c L).iff (termList w a c L)) := by
  apply Derives.conjI
  · apply Derives.impI
    let I := mapExists w a c L
    let H := codeConversion w.castSucc a.castSucc c.castSucc L.castSucc (Fin.last m)
    let Δ := Context.add H (Context.image Formula.raise (Context.add I Γ))
    apply Derives.exE (p := H) (.hyp (Or.inl rfl))
    have hH : Derives Δ H := .hyp (Or.inl rfl)
    have ho := SyntaxFreeSubstCode.list_of_conversion w.castSucc a.castSucc c.castSucc L.castSucc (Fin.last m) hH
    exact of_eq (termList_rename w a c L Fin.castSucc).symm ho
  · apply Derives.impI
    exact SyntaxFreeSubstCode.from_list (ZFContext.add hZ _) w a c L (add hw _) (.hyp (Or.inl rfl))

theorem map_fiber_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a c L : Fin m)
    (hw : Derives Γ (omega w)) : Derives Γ ((mapFiber w a c L).iff (termList w a c L)) := by
  apply Derives.conjI
  · apply Derives.impI
    let I := mapFiber w a c L
    let H := (codeConversion w.castSucc a.castSucc c.castSucc L.castSucc (Fin.last m)).conj (mapUnique w.castSucc a.castSucc c.castSucc L.castSucc (Fin.last m))
    let Δ := Context.add H (Context.image Formula.raise (Context.add I Γ))
    apply Derives.exE (p := H) (.hyp (Or.inl rfl))
    have hH : Derives Δ H := .hyp (Or.inl rfl)
    have ho := SyntaxFreeSubstCode.list_of_conversion w.castSucc a.castSucc c.castSucc L.castSucc (Fin.last m) (.conjL hH)
    exact of_eq (termList_rename w a c L Fin.castSucc).symm ho
  · apply Derives.impI
    exact map_actual_fiber (ZFContext.add hZ _) w a c L (add hw _) (.hyp (Or.inl rfl))

def listExists {m} (w a c S : Fin m) : Formula m := .ex (codeConversion w.castSucc a.castSucc c.castSucc (Fin.last m) S.castSucc)

def listUnique {m} (w a c S L : Fin m) : Formula m := .all
  ((codeConversion w.castSucc a.castSucc c.castSucc (Fin.last m) S.castSucc).imp (.equal (Fin.last m) L.castSucc))

def listFiber {m} (w a c S : Fin m) : Formula m := .ex
  ((codeConversion w.castSucc a.castSucc c.castSucc (Fin.last m) S.castSucc).conj (listUnique w.castSucc a.castSucc c.castSucc S.castSucc (Fin.last m)))

theorem listExists_rename {m k} (w a c S : Fin m) (ρ : Fin m → Fin k) :
    (listExists w a c S).rename ρ = listExists (ρ w) (ρ a) (ρ c) (ρ S) := by
  simp only [listExists, Formula.rename, codeConversion_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem listUnique_rename {m k} (w a c S L : Fin m) (ρ : Fin m → Fin k) :
    (listUnique w a c S L).rename ρ = listUnique (ρ w) (ρ a) (ρ c) (ρ S) (ρ L) := by
  simp only [listUnique, Formula.rename, codeConversion_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem listFiber_rename {m k} (w a c S : Fin m) (ρ : Fin m → Fin k) :
    (listFiber w a c S).rename ρ = listFiber (ρ w) (ρ a) (ρ c) (ρ S) := by
  simp only [listFiber, Formula.rename, codeConversion_rename, listUnique_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem list_unique_formula {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a c S L : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (codeConversion w a c L S)) : Derives Γ (listUnique w a c S L) := by
  apply Derives.allI
  apply Derives.impI
  let H := codeConversion w.castSucc a.castSucc c.castSucc (Fin.last m) S.castSucc
  let Δ := Context.add H (Context.image Formula.raise Γ)
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw H)
  have hc1 : Derives Δ (codeConversion w.castSucc a.castSucc c.castSucc L.castSucc S.castSucc) := of_eq (codeConversion_rename w a c L S Fin.castSucc) (under hc H)
  exact SyntaxFreeSubstCodeUnique.list_unique (ZFContext.under hZ H) w.castSucc a.castSucc c.castSucc (Fin.last m) L.castSucc S.castSucc hw1 (.hyp (Or.inl rfl)) hc1

theorem list_actual_fiber {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a c S : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (mapCode w a c S)) : Derives Γ (listFiber w a c S) := by
  let H := codeConversion w.castSucc a.castSucc c.castSucc (Fin.last m) S.castSucc
  let Δ := Context.add H (Context.image Formula.raise Γ)
  apply Derives.exE (p := H) (SyntaxFreeSubstCode.from_map hZ w a c S hw hi)
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw H)
  have hH : Derives Δ H := .hyp (Or.inl rfl)
  have hu := list_unique_formula (ZFContext.under hZ H) w.castSucc a.castSucc c.castSucc S.castSucc (Fin.last m) hw1 hH
  have ho : Derives Δ (listFiber w.castSucc a.castSucc c.castSucc S.castSucc) := by
    apply Derives.exI (Fin.last m)
    exact of_eq (by simp only [H, Formula.instantiate, Formula.rename, codeConversion_rename, listUnique_rename,
      Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI hH hu)
  exact of_eq (listFiber_rename w a c S Fin.castSucc).symm ho

theorem list_exists_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a c S : Fin m)
    (hw : Derives Γ (omega w)) : Derives Γ ((listExists w a c S).iff (mapCode w a c S)) := by
  apply Derives.conjI
  · apply Derives.impI
    let I := listExists w a c S
    let H := codeConversion w.castSucc a.castSucc c.castSucc (Fin.last m) S.castSucc
    let Δ := Context.add H (Context.image Formula.raise (Context.add I Γ))
    apply Derives.exE (p := H) (.hyp (Or.inl rfl))
    have hH : Derives Δ H := .hyp (Or.inl rfl)
    have ho := SyntaxFreeSubstCode.map_of_conversion w.castSucc a.castSucc c.castSucc (Fin.last m) S.castSucc hH
    exact of_eq (mapCode_rename w a c S Fin.castSucc).symm ho
  · apply Derives.impI
    exact SyntaxFreeSubstCode.from_map (ZFContext.add hZ _) w a c S (add hw _) (.hyp (Or.inl rfl))

theorem list_fiber_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a c S : Fin m)
    (hw : Derives Γ (omega w)) : Derives Γ ((listFiber w a c S).iff (mapCode w a c S)) := by
  apply Derives.conjI
  · apply Derives.impI
    let I := listFiber w a c S
    let H := (codeConversion w.castSucc a.castSucc c.castSucc (Fin.last m) S.castSucc).conj (listUnique w.castSucc a.castSucc c.castSucc S.castSucc (Fin.last m))
    let Δ := Context.add H (Context.image Formula.raise (Context.add I Γ))
    apply Derives.exE (p := H) (.hyp (Or.inl rfl))
    have hH : Derives Δ H := .hyp (Or.inl rfl)
    have ho := SyntaxFreeSubstCode.map_of_conversion w.castSucc a.castSucc c.castSucc (Fin.last m) S.castSucc (.conjL hH)
    exact of_eq (mapCode_rename w a c S Fin.castSucc).symm ho
  · apply Derives.impI
    exact list_actual_fiber (ZFContext.add hZ _) w a c S (add hw _) (.hyp (Or.inl rfl))

end PPAC.Migration.Internal.SyntaxFreeSubstFiber
