import PPAC.Migration.Internal.PacketBytesTraceSyntax

/-! Both sequence inclusions preserve every old byte step; the new final step is separately constructed. -/
namespace PPAC.Migration.Internal.PacketBytesRowMap
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax GraphSyntax GraphPointwiseSyntax PacketBytesRowSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem row_map {m} {Γ : Context m} (w C f g F G i : Fin m)
    (hf : Derives Γ (edgeIncluded f F)) (hg : Derives Γ (edgeIncluded g G)) (hr : Derives Γ (row w C f g i)) :
    Derives Γ (row w C F G i) := by
  let R := rowBody w C f g i
  let Δ := Context.add R (raisedContext 6 Γ)
  apply HornBinderRules.eliminate_many 6 R _ hr
  have hf6 := of_eq (edgeIncluded_rename f F (old 6)) (HornBinderRules.under_body 6 hf R)
  have hg6 := of_eq (edgeIncluded_rename g G (old 6)) (HornBinderRules.under_body 6 hg R)
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hx := Derives.impE (edgeIncluded_at _ _ _ _ hf6) (.conjL (.conjR hR))
  have hy := Derives.impE (edgeIncluded_at _ _ _ _ hf6) (.conjL (.conjR (.conjR hR)))
  have hu := Derives.impE (edgeIncluded_at _ _ _ _ hg6) (.conjL (.conjR (.conjR (.conjR (.conjR hR)))))
  have hv := Derives.impE (edgeIncluded_at _ _ _ _ hg6) (.conjL (.conjR (.conjR (.conjR (.conjR (.conjR hR))))))
  apply of_eq (row_rename w C F G i (old 6)).symm
  exact intro_row (old 6 w) (old 6 C) (old 6 F) (old 6 G) (old 6 i)
    (slot 6 0) (slot 6 1) (slot 6 2) (slot 6 3) (slot 6 4) (slot 6 5)
    (.conjL hR) hx hy (.conjL (.conjR (.conjR (.conjR hR)))) hu hv
    (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR hR))))))

theorem links_map {m} {Γ : Context m} (w C l f g F G : Fin m) (hl : Derives Γ (links w C l f g))
    (hf : Derives Γ (edgeIncluded f F)) (hg : Derives Γ (edgeIncluded g G)) : Derives Γ (links w C l F G) := by
  apply Derives.allI
  apply Derives.impI
  let M := Formula.mem (Fin.last m) l.castSucc
  have hl1 := of_eq (links_rename w C l f g Fin.castSucc) (under hl M)
  have hf1 := of_eq (edgeIncluded_rename f F Fin.castSucc) (under hf M)
  have hg1 := of_eq (edgeIncluded_rename g G Fin.castSucc) (under hg M)
  exact row_map _ _ _ _ _ _ _ hf1 hg1 (links_at _ _ _ _ _ _ hl1 (.hyp (Or.inl rfl)))

theorem row_index_subst {m} {Γ : Context m} (w C f g i j : Fin m) (he : Derives Γ (.equal i j))
    (hr : Derives Γ (row w C f g i)) : Derives Γ (row w C f g j) := by
  let P := row w.castSucc C.castSucc f.castSucc g.castSucc (Fin.last m)
  have h0 : P.instantiate i = row w C f g i := by simp only [P,Formula.instantiate,row_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  have h1 : P.instantiate j = row w C f g j := by simp only [P,Formula.instantiate,row_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  exact of_eq h1 (Derives.eqSubst P he (of_eq h0.symm hr))

theorem append_links {m} {Γ : Context m} (w C l d f g F G : Fin m) (hd : Derives Γ (successor d l))
    (hl : Derives Γ (links w C l f g)) (hf : Derives Γ (edgeIncluded f F)) (hg : Derives Γ (edgeIncluded g G))
    (hnew : Derives Γ (row w C F G l)) : Derives Γ (links w C d F G) := by
  have hm := links_map w C l f g F G hl hf hg
  apply Derives.allI
  apply Derives.impI
  let M := Formula.mem (Fin.last m) d.castSucc
  have hd1 := of_eq (successor_rename d l Fin.castSucc) (under hd M)
  have hm1 := of_eq (links_rename w C l F G Fin.castSucc) (under hm M)
  have hn1 := of_eq (row_rename w C F G l Fin.castSucc) (under hnew M)
  apply Derives.disjE (InsertLogic.member_cases _ _ _ _ hd1 (.hyp (Or.inl rfl)))
  · exact links_at _ _ _ _ _ _ (add hm1 _) (.hyp (Or.inl rfl))
  · exact row_index_subst _ _ _ _ _ _ (eq_symm (.hyp (Or.inl rfl))) (add hn1 _)

end PPAC.Migration.Internal.PacketBytesRowMap
