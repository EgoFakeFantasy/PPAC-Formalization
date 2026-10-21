import PPAC.Migration.IterationValueSyntax

/-! 从真实有限轨迹及完整functionOn取得任意内部索引的实际末值。 -/
namespace PPAC.Migration.IterationValueExistence
open Source SourceAlgebra SourceLogic OmegaSyntax GraphSyntax IterationSyntax FiniteIterationSyntax IterationValueSyntax

theorem track_at {m} {Γ : Context m} (hA : IterationContext.Evidence Γ) (n z a w : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) (hn : Derives Γ (.mem n w)) : Derives Γ (existsTrack n z a) := by
  have hi := Derives.allE n (IterationContext.all_exists hA z a w hw hz)
  have hr : Derives Γ ((Formula.mem n w).imp (existsTrack n z a)) := by
    simpa only [Formula.instantiate, Formula.rename, existsTrack_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hi
  exact .impE hr hn

theorem from_track {m} {Γ : Context m} (n z a : Fin m) (hf : Derives Γ (existsTrack n z a)) :
    Derives Γ (valueExists n z a) := by
  let B := witness (Fin.last (m+1)) (Fin.last m).castSucc n.castSucc.castSucc z.castSucc.castSucc a.castSucc.castSucc
  let Γb := Context.add B (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply IterationExistence.eliminate_track n z a _ hf
  have hB : Derives Γb B := .hyp (Or.inl rfl)
  have hn := InsertLogic.new_member (Fin.last m).castSucc n.castSucc.castSucc n.castSucc.castSucc (.conjL hB)
  have he := GraphProperties.output_exists (Fin.last (m+1)) (Fin.last m).castSucc n.castSucc.castSucc (.conjL (.conjR hB)) hn
  let R := edge (Fin.last (m+1)).castSucc n.castSucc.castSucc.castSucc (Fin.last (m+2))
  let Γr := Context.add R (Context.image Formula.raise Γb)
  change Derives Γb (.ex R) at he
  simp only [Formula.raise, IterationValueSyntax.valueExists_rename]
  apply Derives.exE (p := R) he
  have hBR : Derives Γr (witness (Fin.last (m+1)).castSucc (Fin.last m).castSucc.castSucc
      n.castSucc.castSucc.castSucc z.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc) := by
    simpa only [Formula.raise, B, witness_rename] using under hB R
  have hR : Derives Γr R := .hyp (Or.inl rfl)
  have hv := intro_value (Fin.last (m+1)).castSucc (Fin.last m).castSucc.castSucc
    n.castSucc.castSucc.castSucc z.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc (Fin.last (m+2)) hBR hR
  have hr : Derives Γr (valueExists n.castSucc.castSucc.castSucc z.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc) := by
    apply Derives.exI (Fin.last (m+2))
    simpa only [Formula.instantiate, value_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hv
  simpa only [Formula.raise, IterationValueSyntax.valueExists_rename] using hr

theorem exists_at {m} {Γ : Context m} (hA : IterationContext.Evidence Γ) (n z a w : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) (hn : Derives Γ (.mem n w)) : Derives Γ (valueExists n z a) :=
  from_track n z a (track_at hA n z a w hw hz hn)
end PPAC.Migration.IterationValueExistence
