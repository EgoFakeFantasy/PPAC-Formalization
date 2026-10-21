import PPAC.Migration.Internal.SyntaxRenameTermUnique

/-! 任意内部完整索引映射和合法输入项实际取得重命名输出，不要求单射或标准码。 -/
namespace PPAC.Migration.Internal.SyntaxRenameTermExistence
open Source SourceAlgebra SourceLogic OmegaSyntax GraphSyntax SyntaxVariableSyntax SyntaxIndexMapSyntax SyntaxRenameTermSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem at_index {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (bound : Bool) (w r a c n i : Fin m)
    (hw : Derives Γ (omega w)) (hm : Derives Γ (indexMap w r a c)) (hi : Derives Γ (.mem i a))
    (hn : Derives Γ (code bound w i n)) : Derives Γ (existsBranch bound w r a n) := by
  have he := value_exists w r a c i hm hi
  let J := (Formula.mem (Fin.last m) c.castSucc).conj (valueAt r.castSucc i.castSucc (Fin.last m))
  let Ξ := Context.add J (Context.image Formula.raise Γ)
  change Derives Γ (.ex J) at he
  apply Derives.exE he
  have hZ1 := ZFContext.under hZ J
  have hw1 : Derives Ξ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw J
  have hm1 : Derives Ξ (indexMap w.castSucc r.castSucc a.castSucc c.castSucc) := by simpa only [Formula.raise, indexMap_rename] using under hm J
  have hn1 : Derives Ξ (code bound w.castSucc i.castSucc n.castSucc) := by simpa only [Formula.raise, code_rename] using under hn J
  have hJ : Derives Ξ J := .hyp (Or.inl rfl)
  have hjNat := StructuralListTraceOrder.member_member hZ1 w.castSucc (Fin.last m) c.castSucc hw1 (.conjR (.conjL hm1)) (.conjL hJ)
  have hc := SyntaxVariables.exists_code hZ1 bound w.castSucc (Fin.last m) hw1 hjNat
  let Q := (Formula.mem (Fin.last (m+1)) w.castSucc.castSucc).conj
    (code bound w.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)))
  let Δ := Context.add Q (Context.image Formula.raise Ξ)
  change Derives Ξ (.ex Q) at hc
  apply Derives.exE hc
  have hn2 : Derives Δ (code bound w.castSucc.castSucc i.castSucc.castSucc n.castSucc.castSucc) := by
    simpa only [Formula.raise, code_rename] using under hn1 Q
  have hi2 : Derives Δ (.mem i.castSucc.castSucc a.castSucc.castSucc) := under (under hi J) Q
  have hEdge : Derives Δ (edge r.castSucc.castSucc i.castSucc.castSucc (Fin.last m).castSucc) := by
    simpa only [J, Formula.raise, edge_rename] using under (Derives.conjL (.conjR hJ)) Q
  have hQ : Derives Δ Q := .hyp (Or.inl rfl)
  have hb := intro_branch bound w.castSucc.castSucc r.castSucc.castSucc a.castSucc.castSucc n.castSucc.castSucc
    (Fin.last (m+1)) i.castSucc.castSucc (Fin.last m).castSucc hi2 hEdge hn2 (.conjR hQ)
  have ho : Derives Δ (existsBranch bound w.castSucc.castSucc r.castSucc.castSucc a.castSucc.castSucc n.castSucc.castSucc) := by
    apply Derives.exI (Fin.last (m+1))
    simp only [Formula.instantiate, Formula.rename, branch_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
    exact .conjI (.conjL hQ) hb
  simpa only [Formula.raise, existsBranch_rename] using ho

theorem for_branch {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (bound : Bool) (w r a c n : Fin m)
    (hw : Derives Γ (omega w)) (hm : Derives Γ (indexMap w r a c))
    (hn : Derives Γ (SyntaxTermSyntax.branch bound w a n)) : Derives Γ (existsBranch bound w r a n) := by
  let I := SyntaxTermSyntax.branchWitness bound w a n
  let Δ := Context.add I (Context.image Formula.raise Γ)
  apply SyntaxTermSyntax.eliminate_branch bound w a n _ hn
  have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw I
  have hm1 : Derives Δ (indexMap w.castSucc r.castSucc a.castSucc c.castSucc) := by simpa only [Formula.raise, indexMap_rename] using under hm I
  have hI : Derives Δ I := .hyp (Or.inl rfl)
  have ho := at_index (ZFContext.under hZ I) bound w.castSucc r.castSucc a.castSucc c.castSucc n.castSucc (Fin.last m) hw1 hm1 (.conjL hI) (.conjR hI)
  simpa only [Formula.raise, existsBranch_rename] using ho

theorem from_exists_branch {m} {Γ : Context m} (bound : Bool) (w r s a b c d n : Fin m)
    (hm : Derives Γ (maps w r s a b c d))
    (he : Derives Γ (existsBranch bound w (selectMap bound r s) (SyntaxTermSyntax.limit bound a b) n)) :
    Derives Γ (existsRenamed w r s a b c d n) := by
  let Q := (Formula.mem (Fin.last m) w.castSucc).conj
    (branch bound w.castSucc (selectMap bound r s).castSucc (SyntaxTermSyntax.limit bound a b).castSucc n.castSucc (Fin.last m))
  let Δ := Context.add Q (Context.image Formula.raise Γ)
  change Derives Γ (.ex Q) at he
  apply Derives.exE he
  have hm1 : Derives Δ (maps w.castSucc r.castSucc s.castSucc a.castSucc b.castSucc c.castSucc d.castSucc) := by
    simpa only [Formula.raise, maps_rename] using under hm Q
  have hQ : Derives Δ Q := .hyp (Or.inl rfl)
  have hb : Derives Δ (branch bound w.castSucc (selectMap bound r.castSucc s.castSucc)
      (SyntaxTermSyntax.limit bound a.castSucc b.castSucc) n.castSucc (Fin.last m)) := by
    simpa only [selectMap_map, SyntaxTermSyntax.limit_map] using Derives.conjR hQ
  have hr := intro_renamed bound _ _ _ _ _ _ _ _ _ hm1 hb
  have ho : Derives Δ (existsRenamed w.castSucc r.castSucc s.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc) := by
    apply Derives.exI (Fin.last m)
    simp only [Formula.instantiate, Formula.rename, renamed_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
    exact .conjI (.conjL hQ) hr
  simpa only [Formula.raise, existsRenamed_rename] using ho

theorem for_term {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r s a b c d n : Fin m)
    (hw : Derives Γ (omega w)) (hm : Derives Γ (maps w r s a b c d))
    (hn : Derives Γ (SyntaxTermSyntax.term w a b n)) : Derives Γ (existsRenamed w r s a b c d n) := by
  apply Derives.disjE (.conjR hn)
  · have he := for_branch (ZFContext.add hZ _) true w r a c n (add hw _) (add (.conjL hm) _) (.hyp (Or.inl rfl))
    exact from_exists_branch true w r s a b c d n (add hm _) he
  · have he := for_branch (ZFContext.add hZ _) false w s b d n (add hw _) (add (.conjR hm) _) (.hyp (Or.inl rfl))
    exact from_exists_branch false w r s a b c d n (add hm _) he
end PPAC.Migration.Internal.SyntaxRenameTermExistence
