import PPAC.Migration.Internal.SyntaxForestFieldValues

/-! 原forest与真实完整字段图在所有内部索引/值上的精确位置双条件。 -/
namespace PPAC.Migration.Internal.SyntaxForestFields
open Source SourceAlgebra SourceLogic OmegaSyntax GraphSyntax SyntaxNumeralSyntax SyntaxForestSyntax SyntaxPositionSyntax
open StructuralListLengthSyntax (hasLength hasLength_rename)
open StructuralListFieldGraphSyntax (fields fields_rename)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem edge_at {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (k : Nat) (w : Fin m) (xs : Fin k → Fin m)
    (n l g : Fin m) (j : Fin k) (i y : Fin m) (hw : Derives Γ (omega w)) (hf : Derives Γ (forest k w xs n))
    (hl : Derives Γ (hasLength w n l)) (hg : Derives Γ (fields w n l g)) (hi : Derives Γ (numeral j.val i)) :
    Derives Γ ((edge g i y).iff (.equal y (xs j))) := by
  have hn := FormulaCodeFieldArity.forest_length hZ k w xs n l hw hf hl
  have hd := SyntaxNumeralMembers.index_member hZ k j l i hn hi
  have hv := SyntaxForestFieldValues.field_at hZ k w xs n j i y hw hf hi
  have he := StructuralListFieldGraphSyntax.law_at w n l g i y (.conjR (.conjR hg))
  apply Derives.conjI
  · apply Derives.impI
    exact .impE (add (.conjL hv) _) (.conjR (.impE (add (.conjL he) _) (.hyp (Or.inl rfl))))
  · apply Derives.impI
    exact .impE (add (.conjR he) _) (.conjI (add hd _) (.impE (add (.conjR hv) _) (.hyp (Or.inl rfl))))

theorem full_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (k : Nat) (w : Fin m) (xs : Fin k → Fin m)
    (n l g i y : Fin m) (hw : Derives Γ (omega w)) (hf : Derives Γ (forest k w xs n))
    (hl : Derives Γ (hasLength w n l)) (hg : Derives Γ (fields w n l g)) :
    Derives Γ ((edge g i y).iff (positions k xs i y)) := by
  have hn := FormulaCodeFieldArity.forest_length hZ k w xs n l hw hf hl
  have hm := SyntaxNumeralMembers.member_iff hZ k l i hn
  have he := StructuralListFieldGraphSyntax.law_at w n l g i y (.conjR (.conjR hg))
  apply Derives.conjI
  · apply Derives.impI
    let E := edge g i y
    let Δ := Context.add E Γ
    have hE : Derives Δ E := .hyp (Or.inl rfl)
    have hb := Derives.impE (add (.conjL hm) E) (.conjL (.impE (add (.conjL he) E) hE))
    have hh : Derives Δ ((below k i).imp (positions k xs i y)) := by
      apply below_imp k i (positions k xs i y)
      intro j
      apply Derives.impI
      have hi : Derives (Context.add (numeral j.val i) Δ) (numeral j.val i) := .hyp (Or.inl rfl)
      have hv := edge_at (ZFContext.add (ZFContext.add hZ E) _) k w xs n l g j i y
        (add (add hw E) _) (add (add hf E) _) (add (add hl E) _) (add (add hg E) _) hi
      exact intro_position k xs j i y hi (.impE (.conjL hv) (add hE _))
    exact .impE hh hb
  · apply positions_imp k xs i y (edge g i y)
    intro j
    apply Derives.impI
    let P := (numeral j.val i).conj (.equal y (xs j))
    have hP : Derives (Context.add P Γ) P := .hyp (Or.inl rfl)
    have hv := edge_at (ZFContext.add hZ P) k w xs n l g j i y
      (add hw P) (add hf P) (add hl P) (add hg P) (.conjL hP)
    exact .impE (.conjR hv) (.conjR hP)

def graphLaw {m} (k : Nat) (xs : Fin k → Fin m) (g : Fin m) : Formula m := .all (.all
  ((edge g.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))).iff
    (positions k (fun j => (xs j).castSucc.castSucc) (Fin.last m).castSucc (Fin.last (m+1)))))

theorem graphLaw_rename {m n} (k : Nat) (xs : Fin k → Fin m) (g : Fin m) (r : Fin m → Fin n) :
    (graphLaw k xs g).rename r = graphLaw k (fun j => r (xs j)) (r g) := by
  simp only [graphLaw, Formula.iff, Formula.rename, edge_rename, positions_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem all_edges {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (k : Nat) (w : Fin m) (xs : Fin k → Fin m)
    (n l g : Fin m) (hw : Derives Γ (omega w)) (hf : Derives Γ (forest k w xs n))
    (hl : Derives Γ (hasLength w n l)) (hg : Derives Γ (fields w n l g)) : Derives Γ (graphLaw k xs g) := by
  apply Derives.allI
  apply Derives.allI
  let Δ := Context.image Formula.raise (Context.image Formula.raise Γ)
  have hZ2 := ZFContext.rename (ZFContext.rename hZ Fin.castSucc) Fin.castSucc
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := by
    simpa only [omega_rename] using Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hw)
  have hf2 : Derives Δ (forest k w.castSucc.castSucc (fun j => (xs j).castSucc.castSucc) n.castSucc.castSucc) := by
    simpa only [forest_rename] using Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hf)
  have hl2 : Derives Δ (hasLength w.castSucc.castSucc n.castSucc.castSucc l.castSucc.castSucc) := by
    simpa only [hasLength_rename] using Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hl)
  have hg2 : Derives Δ (fields w.castSucc.castSucc n.castSucc.castSucc l.castSucc.castSucc g.castSucc.castSucc) := by
    simpa only [fields_rename] using Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hg)
  exact full_iff hZ2 k w.castSucc.castSucc (fun j => (xs j).castSucc.castSucc)
    n.castSucc.castSucc l.castSucc.castSucc g.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) hw2 hf2 hl2 hg2
theorem law_at {m} {Γ : Context m} (k : Nat) (xs : Fin k → Fin m) (g i y : Fin m)
    (hh : Derives Γ (graphLaw k xs g)) : Derives Γ ((edge g i y).iff (positions k xs i y)) := by
  simpa only [graphLaw, Formula.instantiate, Formula.iff, Formula.rename, edge_rename, positions_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using Derives.allE y (Derives.allE i hh)
end PPAC.Migration.Internal.SyntaxForestFields
