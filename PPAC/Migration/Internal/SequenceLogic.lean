import PPAC.Migration.Internal.SequenceSyntax

/-! 实际空序列、精确域求值及追加后的值域保持。 -/
namespace PPAC.Migration.Internal.SequenceLogic
open Source SourceAlgebra SourceLogic GraphSyntax OmegaSyntax SequenceSyntax

theorem no_empty_edge {m} {Γ : Context m} (f i y : Fin m)
    (hf : Derives Γ (empty f)) (he : Derives Γ (edge f i y)) : Derives Γ .bot := by
  let P := (Formula.mem (Fin.last m) f.castSucc).conj (PairSyntax.ordered (Fin.last m) i.castSucc y.castSucc)
  let Ξ := Context.add P (Context.image Formula.raise Γ)
  apply GraphLogic.edge_elim f i y _ he
  have hfP : Derives Ξ (empty f.castSucc) := by
    simpa only [Formula.raise, empty_rename] using under hf P
  have hP : Derives Ξ P := .hyp (Or.inl rfl)
  exact .impE (empty_at f.castSucc (Fin.last m) hfP) (.conjL hP)

theorem empty_sequence {m} {Γ : Context m} (z b : Fin m) (hz : Derives Γ (empty z)) :
    Derives Γ (sequence z z b) := by
  have hfn : Derives Γ (functionOn z z) := by
    apply Derives.conjI
    · apply Derives.allI
      have hz' : Derives (Context.image Formula.raise Γ) (empty z.castSucc) := by
        simpa only [Formula.raise, empty_rename] using Derives.rename Fin.castSucc hz
      apply Derives.impI
      exact .botE (.impE (add (empty_at z.castSucc (Fin.last m) hz') _) (.hyp (Or.inl rfl)))
    · apply Derives.allI
      have hz' : Derives (Context.image Formula.raise Γ) (empty z.castSucc) := by
        simpa only [Formula.raise, empty_rename] using Derives.rename Fin.castSucc hz
      apply Derives.impI
      exact .botE (.impE (add (empty_at z.castSucc (Fin.last m) hz') _) (.hyp (Or.inl rfl)))
  apply Derives.conjI hfn
  apply Derives.allI
  apply Derives.allI
  have hz' : Derives (Context.image Formula.raise (Context.image Formula.raise Γ)) (empty z.castSucc.castSucc) := by
    simpa only [Formula.raise, empty_rename] using Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hz)
  apply Derives.impI
  exact .botE (no_empty_edge z.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) (add hz' _) (.hyp (Or.inl rfl)))

theorem value_at {m} {Γ : Context m} (f n b i : Fin m)
    (hf : Derives Γ (sequence f n b)) (hi : Derives Γ (.mem i n)) : Derives Γ (value f i b) := by
  have hv := Derives.impE (total_at f n i (.conjR (.conjL hf))) hi
  let Y := valueAt f.castSucc i.castSucc (Fin.last m)
  let Ξ := Context.add Y (Context.image Formula.raise Γ)
  change Derives Γ (.ex Y) at hv
  apply Derives.exE (p := Y) hv
  have hbY : Derives Ξ (bounded f.castSucc b.castSucc) := by
    simpa only [Formula.raise, bounded_rename] using under (.conjR hf) Y
  have hY : Derives Ξ Y := .hyp (Or.inl rfl)
  have hm := Derives.impE (bounded_at f.castSucc b.castSucc i.castSucc (Fin.last m) hbY) (.conjL hY)
  have hout : Derives Ξ (value f.castSucc i.castSucc b.castSucc) := by
    apply Derives.exI (Fin.last m)
    simp only [Formula.instantiate, Formula.rename, valueAt_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
    exact .conjI hm hY
  simpa only [Formula.raise, value_rename] using hout

theorem appended_bounded {m} {Γ : Context m} (g f n y b : Fin m)
    (hf : Derives Γ (bounded f b)) (hy : Derives Γ (.mem y b))
    (hl : Derives Γ (GraphInsertSyntax.edgeLaw g f n y)) : Derives Γ (bounded g b) := by
  apply Derives.allI
  apply Derives.allI
  let Δ := Context.image Formula.raise (Context.image Formula.raise Γ)
  have hf' : Derives Δ (bounded f.castSucc.castSucc b.castSucc.castSucc) := by
    simpa only [Formula.raise, bounded_rename] using Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hf)
  have hy' : Derives Δ (.mem y.castSucc.castSucc b.castSucc.castSucc) := Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hy)
  have hl' : Derives Δ (GraphInsertSyntax.edgeLaw g.castSucc.castSucc f.castSucc.castSucc n.castSucc.castSucc y.castSucc.castSucc) := by
    simpa only [Formula.raise, GraphInsertSyntax.edgeLaw_rename] using Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hl)
  apply Derives.impI
  let E := edge g.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
  have hc := Derives.impE (.conjL (law_at g.castSucc.castSucc f.castSucc.castSucc n.castSucc.castSucc y.castSucc.castSucc
    (Fin.last m).castSucc (Fin.last (m+1)) (add hl' E))) (.hyp (Or.inl rfl))
  apply Derives.disjE hc
  · exact .impE (add (add (bounded_at f.castSucc.castSucc b.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) hf') E) _) (.hyp (Or.inl rfl))
  · exact mem_subst (eq_symm (.conjR (.hyp (Or.inl rfl)))) (add (add hy' E) _)

theorem laws_included {m} {Γ : Context m} (g h f n y : Fin m)
    (hg : Derives Γ (GraphInsertSyntax.edgeLaw g f n y)) (hh : Derives Γ (GraphInsertSyntax.edgeLaw h f n y)) :
    Derives Γ (GraphPointwiseSyntax.edgeIncluded g h) := by
  apply Derives.allI
  apply Derives.allI
  let Δ := Context.image Formula.raise (Context.image Formula.raise Γ)
  have hg' : Derives Δ (GraphInsertSyntax.edgeLaw g.castSucc.castSucc f.castSucc.castSucc n.castSucc.castSucc y.castSucc.castSucc) := by
    simpa only [Formula.raise, GraphInsertSyntax.edgeLaw_rename] using Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hg)
  have hh' : Derives Δ (GraphInsertSyntax.edgeLaw h.castSucc.castSucc f.castSucc.castSucc n.castSucc.castSucc y.castSucc.castSucc) := by
    simpa only [Formula.raise, GraphInsertSyntax.edgeLaw_rename] using Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hh)
  apply Derives.impI
  exact .impE (.conjR (law_at h.castSucc.castSucc f.castSucc.castSucc n.castSucc.castSucc y.castSucc.castSucc
    (Fin.last m).castSucc (Fin.last (m+1)) (add hh' _)))
    (.impE (.conjL (law_at g.castSucc.castSucc f.castSucc.castSucc n.castSucc.castSucc y.castSucc.castSucc
      (Fin.last m).castSucc (Fin.last (m+1)) (add hg' _))) (.hyp (Or.inl rfl)))

theorem append_unique {m} {Γ : Context m} (g h k f n y b : Fin m)
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hg : Derives Γ (append g k f n y b)) (hh : Derives Γ (append h k f n y b)) : Derives Γ (.equal g h) :=
  GraphPointwiseEntries.equal_of_edges g h k k he (.conjL (.conjL (.conjL hg))) (.conjL (.conjL (.conjL hh)))
    (.conjI (laws_included g h f n y (.conjL (.conjR hg)) (.conjL (.conjR hh)))
      (laws_included h g f n y (.conjL (.conjR hh)) (.conjL (.conjR hg))))
end PPAC.Migration.Internal.SequenceLogic
