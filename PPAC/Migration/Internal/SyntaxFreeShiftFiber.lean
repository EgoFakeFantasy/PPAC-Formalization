import PPAC.Migration.Internal.SyntaxFreeShiftCode

/-! 位移图/码的实际唯一纤维、精确合法输入和 fresh 头槽零边排除。 -/
namespace PPAC.Migration.Internal.SyntaxFreeShiftFiber
open Source SourceAlgebra SourceLogic OmegaSyntax GraphSyntax SyntaxRenameQuerySyntax SyntaxMapCodeSyntax
open SyntaxFreeShiftSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem actual_map_fiber {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b B : Fin m)
    (hw : Derives Γ (omega w)) (hb : Derives Γ (.mem b w)) (hB : Derives Γ (successor B b)) :
    Derives Γ (mapFiber w b B) := by
  let G := shiftMap w.castSucc b.castSucc B.castSucc (Fin.last m)
  let Ξ := Context.add G (Context.image Formula.raise Γ)
  apply Derives.exE (p := G) (SyntaxFreeShiftGraph.exists_map hZ w b B hw hb hB)
  have hG : Derives Ξ G := .hyp (Or.inl rfl)
  have hu : Derives Ξ (.all ((shiftMap w.castSucc.castSucc b.castSucc.castSucc B.castSucc.castSucc (Fin.last (m+1))).imp
      (.equal (Fin.last (m+1)) (Fin.last m).castSucc))) := by
    apply Derives.allI
    apply Derives.impI
    let H := shiftMap w.castSucc.castSucc b.castSucc.castSucc B.castSucc.castSucc (Fin.last (m+1))
    let Δ := Context.add H (Context.image Formula.raise Ξ)
    have hg2 : Derives Δ (shiftMap w.castSucc.castSucc b.castSucc.castSucc B.castSucc.castSucc (Fin.last m).castSucc) :=
      of_eq (by simp only [G, Formula.raise, shiftMap_rename]) (under hG H)
    exact SyntaxFreeShiftGraph.unique_map (ZFContext.under (ZFContext.under hZ G) H) _ _ _ _ _ (.hyp (Or.inl rfl)) hg2
  have ho : Derives Ξ (mapFiber w.castSucc b.castSucc B.castSucc) := by
    apply Derives.exI (Fin.last m)
    exact of_eq (by simp only [G, Formula.instantiate, Formula.rename, shiftMap_rename, Formula.liftRen,
      Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI hG hu)
  exact of_eq (mapFiber_rename w b B Fin.castSucc).symm ho

theorem actual_code_fiber {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b B : Fin m)
    (hw : Derives Γ (omega w)) (hb : Derives Γ (.mem b w)) (hB : Derives Γ (successor B b)) :
    Derives Γ (SyntaxFreeShiftSyntax.codeFiber w b B) := by
  let S := shiftCode w.castSucc b.castSucc B.castSucc (Fin.last m)
  let Ξ := Context.add S (Context.image Formula.raise Γ)
  apply Derives.exE (p := S) (SyntaxFreeShiftCode.exists_code hZ w b B hw hb hB)
  have hS : Derives Ξ S := .hyp (Or.inl rfl)
  have hu : Derives Ξ (.all ((shiftCode w.castSucc.castSucc b.castSucc.castSucc B.castSucc.castSucc (Fin.last (m+1))).imp
      (.equal (Fin.last (m+1)) (Fin.last m).castSucc))) := by
    apply Derives.allI
    apply Derives.impI
    let T := shiftCode w.castSucc.castSucc b.castSucc.castSucc B.castSucc.castSucc (Fin.last (m+1))
    let Δ := Context.add T (Context.image Formula.raise Ξ)
    have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (under (under hw S) T)
    have hs2 : Derives Δ (shiftCode w.castSucc.castSucc b.castSucc.castSucc B.castSucc.castSucc (Fin.last m).castSucc) :=
      of_eq (by simp only [S, Formula.raise, shiftCode_rename]) (under hS T)
    exact SyntaxFreeShiftCode.unique (ZFContext.under (ZFContext.under hZ S) T) _ _ _ _ _ hw2 (.hyp (Or.inl rfl)) hs2
  have ho : Derives Ξ (SyntaxFreeShiftSyntax.codeFiber w.castSucc b.castSucc B.castSucc) := by
    apply Derives.exI (Fin.last m)
    exact of_eq (by simp only [S, Formula.instantiate, Formula.rename, shiftCode_rename, Formula.liftRen,
      Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI hS hu)
  exact of_eq (SyntaxFreeShiftSyntax.codeFiber_rename w b B Fin.castSucc).symm ho

theorem exists_iff_input {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b B : Fin m)
    (hw : Derives Γ (omega w)) :
    Derives Γ ((SyntaxFreeShiftSyntax.existsCode w b B).iff ((Formula.mem b w).conj (successor B b))) := by
  apply Derives.conjI
  · apply Derives.impI
    let E := SyntaxFreeShiftSyntax.existsCode w b B
    let S := shiftCode w.castSucc b.castSucc B.castSucc (Fin.last m)
    let Δ := Context.add S (Context.image Formula.raise (Context.add E Γ))
    apply Derives.exE (p := S) (.hyp (Or.inl rfl))
    have ho := SyntaxFreeShiftCode.input w.castSucc b.castSucc B.castSucc (Fin.last m)
      (Derives.hyp (Or.inl rfl) : Derives Δ S)
    exact of_eq (by simp only [Formula.raise, Formula.rename, successor_rename]) ho
  · apply Derives.impI
    let I := (Formula.mem b w).conj (successor B b)
    have hI : Derives (Context.add I Γ) I := .hyp (Or.inl rfl)
    exact SyntaxFreeShiftCode.exists_code (ZFContext.add hZ I) w b B (add hw I) (.conjL hI) (.conjR hI)

theorem actual_state {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b : Fin m)
    (hw : Derives Γ (omega w)) (hb : Derives Γ (.mem b w)) : Derives Γ (actualState w b) := by
  have he := InsertExistence.exists_insert b b (ZFContext.arithmetic hZ).base.pairing (ZFContext.arithmetic hZ).base.union
  let B := successor (Fin.last m) b.castSucc
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) he
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hf := actual_code_fiber (ZFContext.under hZ B) w.castSucc b.castSucc (Fin.last m) hw1 (under hb B) hB
  have ho : Derives Δ (actualState w.castSucc b.castSucc) := by
    apply Derives.exI (Fin.last m)
    exact of_eq (by simp only [B, Formula.instantiate, Formula.rename, successor_rename,
      SyntaxFreeShiftSyntax.codeFiber_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI hB hf)
  exact of_eq (actualState_rename w b Fin.castSucc).symm ho

theorem map_edges {m} {Γ : Context m} (w b B r i j : Fin m) (hm : Derives Γ (shiftMap w b B r)) :
    Derives Γ ((edge r i j).iff ((Formula.mem i b).conj (successor j i))) :=
  SyntaxFreeShiftGraph.edge_iff b r i j (SyntaxFreeShiftGraph.to_graph w b B r hm)

theorem coded_edges {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b B S r i j : Fin m)
    (hc : Derives Γ (shiftCode w b B S)) (hr : Derives Γ (encoded w r b B S)) :
    Derives Γ ((edge r i j).iff ((Formula.mem i b).conj (successor j i))) :=
  map_edges w b B r i j (SyntaxFreeShiftCode.at_graph hZ w b B S r hc hr)

theorem fresh_absent {m} {Γ : Context m} (w b B r i z : Fin m)
    (hm : Derives Γ (shiftMap w b B r)) (hz : Derives Γ (empty z)) : Derives Γ (edge r i z).neg := by
  apply Derives.impI
  have hs := Derives.conjR (.impE (add (.conjL (map_edges w b B r i z hm)) _) (.hyp (Or.inl rfl)))
  exact .impE (OmegaStructureAlgebra.successor_not_empty z i hs) (add hz _)

theorem empty_source {m} {Γ : Context m} (w b B r i j : Fin m)
    (hm : Derives Γ (shiftMap w b B r)) (hb : Derives Γ (empty b)) : Derives Γ (edge r i j).neg := by
  apply Derives.impI
  have hi := Derives.conjL (.impE (add (.conjL (map_edges w b B r i j hm)) _) (.hyp (Or.inl rfl)))
  exact .impE (add (OmegaSyntax.empty_at b i hb) _) hi

theorem range_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b B C S T : Fin m)
    (hS : Derives Γ (shiftCode w b B S)) (hT : Derives Γ (shiftCode w b C T)) : Derives Γ (.equal B C) :=
  InsertLogic.unique B C b b (ZFContext.arithmetic hZ).base.extensionality
    (.conjR (SyntaxFreeShiftCode.input w b B S hS)) (.conjR (SyntaxFreeShiftCode.input w b C T hT))
theorem empty_graph {m} {Γ : Context m} (w b B r : Fin m)
    (hm : Derives Γ (shiftMap w b B r)) (hb : Derives Γ (empty b)) : Derives Γ (empty r) := by
  apply Derives.allI
  apply Derives.impI
  let M := Formula.mem (Fin.last m) r.castSucc
  let Δ := Context.add M (Context.image Formula.raise Γ)
  have hm1 : Derives Δ (shiftMap w.castSucc b.castSucc B.castSucc r.castSucc) :=
    of_eq (shiftMap_rename w b B r Fin.castSucc) (under hm M)
  have hb1 : Derives Δ (empty b.castSucc) := of_eq (empty_rename b Fin.castSucc) (under hb M)
  have hg := SyntaxFreeShiftGraph.to_graph _ _ _ _ hm1
  have he := Derives.impE (entries_at r.castSucc b.castSucc (Fin.last m) (.conjL (.conjL hg)))
    (Derives.hyp (Or.inl rfl) : Derives Δ M)
  let A := GraphLogic.entryWitnesses b.castSucc (Fin.last m)
  let Θ := Context.add A (Context.image Formula.raise (Context.image Formula.raise Δ))
  apply GraphLogic.entry_elim b.castSucc (Fin.last m) _ he
  have hb3 : Derives Θ (empty b.castSucc.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise, empty_rename]) (OrderedPairElimination.under_two hb1 A)
  have hA : Derives Θ A := .hyp (Or.inl rfl)
  exact .impE (empty_at b.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc hb3) (.conjL hA)

theorem zero_state {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) : Derives Γ (actualState w z) :=
  actual_state hZ w z hw (OmegaStructureAlgebra.zero_member w z (ZFContext.arithmetic hZ).base.extensionality hw hz)
end PPAC.Migration.Internal.SyntaxFreeShiftFiber
