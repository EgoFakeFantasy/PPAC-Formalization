import PPAC.Migration.Internal.PacketReaderHistoryBase

/-! Actual graph inclusion preserves every old reader row; the final added row is constructed separately. -/
namespace PPAC.Migration.Internal.PacketReaderHistoryRowMap
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax GraphSyntax GraphPointwiseSyntax PacketReaderHistorySyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem row_map {m} {Γ : Context m} (w B z o f g i : Fin m)
    (hf : Derives Γ (edgeIncluded f g)) (hr : Derives Γ (row w B z o f i)) : Derives Γ (row w B z o g i) := by
  let R := rowBody w B z o f i
  let Δ := Context.add R (raisedContext 3 Γ)
  apply HornBinderRules.eliminate_many 3 R _ hr
  have hf3 := of_eq (edgeIncluded_rename f g (old 3)) (HornBinderRules.under_body 3 hf R)
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hn := Derives.impE (edgeIncluded_at _ _ _ _ hf3) (.conjL (.conjR hR))
  have hs := Derives.impE (edgeIncluded_at _ _ _ _ hf3) (.conjL (.conjR (.conjR hR)))
  exact of_eq (row_rename w B z o g i (old 3)).symm
    (intro_row _ _ _ _ _ _ _ _ _ (.conjL hR) hn hs (.conjR (.conjR (.conjR hR))))

theorem links_map {m} {Γ : Context m} (w B z o l f g : Fin m) (hl : Derives Γ (links w B z o l f))
    (hf : Derives Γ (edgeIncluded f g)) : Derives Γ (links w B z o l g) := by
  apply Derives.allI
  apply Derives.impI
  let M := Formula.mem (Fin.last m) l.castSucc
  have hl1 := of_eq (links_rename w B z o l f Fin.castSucc) (under hl M)
  have hf1 := of_eq (edgeIncluded_rename f g Fin.castSucc) (under hf M)
  exact row_map _ _ _ _ _ _ _ hf1 (links_at _ _ _ _ _ _ _ hl1 (.hyp (Or.inl rfl)))

theorem index_subst {m} {Γ : Context m} (w B z o f i j : Fin m) (he : Derives Γ (.equal i j))
    (hr : Derives Γ (row w B z o f i)) : Derives Γ (row w B z o f j) := by
  let P := row w.castSucc B.castSucc z.castSucc o.castSucc f.castSucc (Fin.last m)
  have h0 : P.instantiate i = row w B z o f i := by simp only [P,Formula.instantiate,row_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  have h1 : P.instantiate j = row w B z o f j := by simp only [P,Formula.instantiate,row_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  exact of_eq h1 (Derives.eqSubst P he (of_eq h0.symm hr))

theorem append_links {m} {Γ : Context m} (w B z o l d f g : Fin m) (hd : Derives Γ (successor d l))
    (hl : Derives Γ (links w B z o l f)) (hf : Derives Γ (edgeIncluded f g))
    (hnew : Derives Γ (row w B z o g l)) : Derives Γ (links w B z o d g) := by
  have hm := links_map w B z o l f g hl hf
  apply Derives.allI
  apply Derives.impI
  let M := Formula.mem (Fin.last m) d.castSucc
  have hd1 := of_eq (successor_rename d l Fin.castSucc) (under hd M)
  have hm1 := of_eq (links_rename w B z o l g Fin.castSucc) (under hm M)
  have hn1 := of_eq (row_rename w B z o g l Fin.castSucc) (under hnew M)
  apply Derives.disjE (InsertLogic.member_cases _ _ _ _ hd1 (.hyp (Or.inl rfl)))
  · exact links_at _ _ _ _ _ _ _ (add hm1 _) (.hyp (Or.inl rfl))
  · exact index_subst _ _ _ _ _ _ _ (eq_symm (.hyp (Or.inl rfl))) (add hn1 _)

end PPAC.Migration.Internal.PacketReaderHistoryRowMap
