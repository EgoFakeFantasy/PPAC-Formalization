import PPAC.Migration.Internal.LookupTableCorrectnessSyntax

/-! 实际Cons tail的严格表码界驱动执行对应，不以外部表或宿主递归作归纳。 -/
namespace PPAC.Migration.Internal.LookupTableCorrectnessPoint
open Source SourceAlgebra SourceLogic OmegaSyntax LookupTableCorrectnessSyntax
open SyntaxRenameQuerySyntax (of_eq)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem forward_successor {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n i y : Fin m)
    (hw : Derives Γ (omega w)) (he : Derives Γ (earlier w n))
    (hs : Derives Γ (LookupTableRecursiveSyntax.successorCase w n i y)) : Derives Γ (StrictLookupSyntax.returned w n i y) := by
  let B := LookupTableRecursiveSyntax.successorBody w n i y
  let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply SyntaxRenameBinders.eliminate_2 B _ hs
  have hZ2 := SyntaxRenameBinders.zf_under_2 hZ B
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxRenameBinders.under_2 hw B)
  have he2 : Derives Δ (earlier w.castSucc.castSucc n.castSucc.castSucc) := of_eq (by simp only [Formula.raise, earlier_rename]) (SyntaxRenameBinders.under_2 he B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have htW := StructuralListProjection.selected_range false w.castSucc.castSucc n.castSucc.castSucc (Fin.last m).castSucc (.conjL hB)
  have htN := LookupTableProgramFacts.tail_member hZ2 w.castSucc.castSucc n.castSucc.castSucc (Fin.last m).castSucc hw2 (.conjL hB)
  have hChild := earlier_at w.castSucc.castSucc n.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) y.castSucc.castSucc he2 htW htN (.conjL (.conjL (.conjR hB)))
  have hRun := LookupTableProgramFacts.successor_selected hZ2 w.castSucc.castSucc n.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) i.castSucc.castSucc y.castSucc.castSucc hw2 (.conjL (.conjL (.conjR hB))) (.conjR (.conjL (.conjR hB))) (.conjL hB)
  exact of_eq (by simp only [Formula.raise, StrictLookupSyntax.returned_rename])
    (.impE (.conjR hRun) (.impE (.conjL hChild) (.conjR (.conjR hB))))

theorem reverse_successor {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n i y j : Fin m)
    (hw : Derives Γ (omega w)) (he : Derives Γ (earlier w n))
    (hj : Derives Γ (.mem j w)) (hi : Derives Γ (successor i j)) (hy : Derives Γ (StrictLookupSyntax.returned w n i y)) :
    Derives Γ (LookupTableRecursiveSyntax.successorCase w n i y) := by
  have hiW := OmegaStructureAlgebra.successor_member w i j (ZFContext.arithmetic hZ).base.extensionality hw hj hi
  have hx := LookupTableProgramFacts.tail_of_returned hZ w n i y hw hiW hy
  let T := StructuralListProjectionSyntax.selected false w.castSucc n.castSucc (Fin.last m)
  let Δ := Context.add T (Context.image Formula.raise Γ)
  apply Derives.exE (p := T) hx
  have hZ1 := ZFContext.under hZ T
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw T)
  have he1 : Derives Δ (earlier w.castSucc n.castSucc) := of_eq (earlier_rename w n Fin.castSucc) (under he T)
  have hi1 : Derives Δ (successor i.castSucc j.castSucc) := of_eq (successor_rename i j Fin.castSucc) (under hi T)
  have hy1 : Derives Δ (StrictLookupSyntax.returned w.castSucc n.castSucc i.castSucc y.castSucc) := of_eq (StrictLookupSyntax.returned_rename w n i y Fin.castSucc) (under hy T)
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  have htW := StructuralListProjection.selected_range false w.castSucc n.castSucc (Fin.last m) hT
  have htN := LookupTableProgramFacts.tail_member hZ1 w.castSucc n.castSucc (Fin.last m) hw1 hT
  have hChild := earlier_at w.castSucc n.castSucc (Fin.last m) j.castSucc y.castSucc he1 htW htN (under hj T)
  have hRun := LookupTableProgramFacts.successor_selected hZ1 w.castSucc n.castSucc (Fin.last m) j.castSucc i.castSucc y.castSucc hw1 (under hj T) hi1 hT
  have ho := LookupTableRecursiveSyntax.intro_successor w.castSucc n.castSucc i.castSucc y.castSucc (Fin.last m) j.castSucc hT (under hj T) hi1
    (.impE (.conjR hChild) (.impE (.conjL hRun) hy1))
  exact of_eq (LookupTableRecursiveSyntax.successorCase_rename w n i y Fin.castSucc).symm ho

theorem forward {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n i y : Fin m)
    (hw : Derives Γ (omega w)) (he : Derives Γ (earlier w n))
    (hy : Derives Γ (LookupTableExecutionSyntax.executed w n i y)) : Derives Γ (StrictLookupSyntax.returned w n i y) := by
  have hc := Derives.impE (.conjL (LookupTableRecursive.recursive_iff hZ w n i y hw)) hy
  apply Derives.disjE (.conjR (.conjR hc))
  · have hZc := ZFContext.add hZ (LookupTableProgramSyntax.zeroCase w n i y)
    have hC : Derives (Context.add (LookupTableProgramSyntax.zeroCase w n i y) Γ) (LookupTableProgramSyntax.zeroCase w n i y) := .hyp (Or.inl rfl)
    exact .impE (.conjR (StrictLookupRules.zero_selected hZc w n i y (add hw _) (.conjL hC))) (.conjR hC)
  · exact forward_successor (ZFContext.add hZ _) w n i y (add hw _) (add he _) (.hyp (Or.inl rfl))

theorem reverse {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n i y : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (.mem n w)) (hi : Derives Γ (.mem i w))
    (he : Derives Γ (earlier w n)) (hy : Derives Γ (StrictLookupSyntax.returned w n i y)) :
    Derives Γ (LookupTableExecutionSyntax.executed w n i y) := by
  have hStep : Derives Γ (LookupTableRecursiveSyntax.step w n i y) := by
    apply SourcePropositional.by_cases (empty i)
    · have hz : Derives (Context.add (empty i) Γ) (empty i) := .hyp (Or.inl rfl)
      exact .disjL (.conjI hz (.impE (.conjL (StrictLookupRules.zero_selected (ZFContext.add hZ _) w n i y (add hw _) hz)) (add hy _)))
    · let Z := (empty i).neg
      have hd := OmegaStructureAlgebra.decomposition_at w i
        (OmegaStructureInduction.decomposition w (ZFContext.separation (ZFContext.add hZ Z) OmegaStructureSyntax.splitMatrix) (add hw Z)) (add hi Z)
      have hp := OmegaStructureAlgebra.nonzero_predecessor w i hd (Derives.hyp (Γ := Context.add Z Γ) (Or.inl rfl))
      let J := (Formula.mem (Fin.last m) w.castSucc).conj (successor i.castSucc (Fin.last m))
      let Δ := Context.add J (Context.image Formula.raise (Context.add Z Γ))
      apply Derives.exE (p := J) hp
      have lift {p : Formula m} (hh : Derives Γ p) : Derives Δ p.raise := under (add hh Z) J
      have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (lift hw)
      have he1 : Derives Δ (earlier w.castSucc n.castSucc) := of_eq (earlier_rename w n Fin.castSucc) (lift he)
      have hy1 : Derives Δ (StrictLookupSyntax.returned w.castSucc n.castSucc i.castSucc y.castSucc) := of_eq (StrictLookupSyntax.returned_rename w n i y Fin.castSucc) (lift hy)
      have hJ : Derives Δ J := .hyp (Or.inl rfl)
      have ho : Derives Δ (LookupTableRecursiveSyntax.step w.castSucc n.castSucc i.castSucc y.castSucc) := .disjR
        (reverse_successor (ZFContext.under (ZFContext.add hZ Z) J) w.castSucc n.castSucc i.castSucc y.castSucc (Fin.last m) hw1 he1 (.conjL hJ) (.conjR hJ) hy1)
      exact of_eq (LookupTableRecursiveSyntax.step_rename w n i y Fin.castSucc).symm ho
  exact .impE (.conjR (LookupTableRecursive.recursive_iff hZ w n i y hw))
    (.conjI hn (.conjI (.conjI hi (StrictLookupValue.output_natural w n i y hy)) hStep))

theorem property_from_earlier {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (.mem n w)) (he : Derives Γ (earlier w n)) : Derives Γ (property w n) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  let I := Formula.mem (Fin.last m).castSucc w.castSucc.castSucc
  let Δ := Context.add I (Context.image Formula.raise (Context.image Formula.raise Γ))
  have hZ2 := SyntaxRenameBinders.zf_under_2 hZ I
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxRenameBinders.under_2 hw I)
  have hn2 : Derives Δ (.mem n.castSucc.castSucc w.castSucc.castSucc) := SyntaxRenameBinders.under_2 hn I
  have he2 : Derives Δ (earlier w.castSucc.castSucc n.castSucc.castSucc) := of_eq (by simp only [Formula.raise, earlier_rename]) (SyntaxRenameBinders.under_2 he I)
  have hI : Derives Δ I := .hyp (Or.inl rfl)
  apply Derives.conjI
  · apply Derives.impI
    exact forward (ZFContext.add hZ2 _) w.castSucc.castSucc n.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) (add hw2 _) (add he2 _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact reverse (ZFContext.add hZ2 _) w.castSucc.castSucc n.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) (add hw2 _) (add hn2 _) (add hI _) (add he2 _) (.hyp (Or.inl rfl))

end PPAC.Migration.Internal.LookupTableCorrectnessPoint
