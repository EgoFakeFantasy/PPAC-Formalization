import PPAC.Migration.Internal.SyntaxIdentityCode

/-! 任意完整对角索引图恢复原恒等图，并在对象核中证明实际恒等自然码唯一。 -/
namespace PPAC.Migration.Internal.SyntaxIdentityUnique
open Source SourceAlgebra SourceLogic OmegaSyntax GraphSyntax SyntaxRenameQuerySyntax
open SyntaxIdentityMapSyntax SyntaxIndexMapSyntax SyntaxMapCodeSyntax SyntaxRenameTermIdentity
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem diagonal_edge {m} {Γ : Context m} (w a r i : Fin m)
    (hm : Derives Γ (indexMap w r a a)) (hd : Derives Γ (diagonal r))
    (hi : Derives Γ (.mem i a)) : Derives Γ (edge r i i) := by
  have he := Derives.impE (GraphSyntax.total_at r a i (.conjR (.conjL (.conjR hm)))) hi
  let V := valueAt r.castSucc i.castSucc (Fin.last m)
  let Δ := Context.add V (Context.image Formula.raise Γ)
  change Derives Γ (.ex V) at he
  apply Derives.exE he
  have hd1 : Derives Δ (diagonal r.castSucc) := of_eq (diagonal_rename r Fin.castSucc) (under hd V)
  have hV : Derives Δ V := .hyp (Or.inl rfl)
  have hv := Derives.conjL hV
  have hiq := diagonal_at r.castSucc i.castSucc (Fin.last m) hd1 hv
  have ho := GraphPointwiseSyntax.edge_subst_output r.castSucc i.castSucc (Fin.last m) i.castSucc (eq_symm hiq) hv
  exact of_eq (edge_rename r i i Fin.castSucc).symm ho

theorem edge_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a r i j : Fin m)
    (hm : Derives Γ (indexMap w r a a)) (hd : Derives Γ (diagonal r)) :
    Derives Γ ((edge r i j).iff ((Formula.mem i a).conj (.equal i j))) := by
  apply Derives.conjI
  · apply Derives.impI
    have he : Derives (Context.add (edge r i j) Γ) (edge r i j) := .hyp (Or.inl rfl)
    exact .conjI (SyntaxIndexMapSyntax.edge_source (ZFContext.add hZ _) w r a a i j (add hm _) he)
      (diagonal_at r i j (add hd _) he)
  · apply Derives.impI
    have h : Derives (Context.add ((Formula.mem i a).conj (.equal i j)) Γ)
        ((Formula.mem i a).conj (.equal i j)) := .hyp (Or.inl rfl)
    exact GraphPointwiseSyntax.edge_subst_output r i i j (.conjR h)
      (diagonal_edge w a r i (add hm _) (add hd _) (.conjL h))

theorem to_graph {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a r : Fin m)
    (hm : Derives Γ (indexMap w r a a)) (hd : Derives Γ (diagonal r)) :
    Derives Γ (graph a r) := by
  apply Derives.conjI (.conjL (.conjR hm))
  simp only [RelationGraphSyntax.edgeLaw, matrix_rel]
  apply Derives.allI
  apply Derives.allI
  let Δ := Context.image Formula.raise (Context.image Formula.raise Γ)
  have hm2 : Derives Δ (indexMap w.castSucc.castSucc r.castSucc.castSucc a.castSucc.castSucc a.castSucc.castSucc) := by
    simpa only [Formula.raise, indexMap_rename] using Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hm)
  have hd2 : Derives Δ (diagonal r.castSucc.castSucc) := by
    simpa only [Formula.raise, diagonal_rename] using Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hd)
  exact edge_iff (ZFContext.rename (ZFContext.rename hZ Fin.castSucc) Fin.castSucc)
    w.castSucc.castSucc a.castSucc.castSucc r.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) hm2 hd2

theorem map_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a r s : Fin m)
    (hr : Derives Γ (identityMap w a r)) (hs : Derives Γ (identityMap w a s)) :
    Derives Γ (.equal r s) :=
  SyntaxIdentityGraph.unique_graph hZ a r s (to_graph hZ w a r (.conjL hr) (.conjR hr))
    (to_graph hZ w a s (.conjL hs) (.conjR hs))

theorem code_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a R T : Fin m)
    (hw : Derives Γ (omega w)) (hR : Derives Γ (identityCode w a R)) (hT : Derives Γ (identityCode w a T)) :
    Derives Γ (.equal R T) := by
  let G := (encoded w.castSucc (Fin.last m) a.castSucc a.castSucc R.castSucc).conj
    (diagonal (Fin.last m))
  let Ξ := Context.add G (Context.image Formula.raise Γ)
  apply Derives.exE (p := G) hR
  have ht1 : Derives Ξ (identityCode w.castSucc a.castSucc T.castSucc) :=
    of_eq (identityCode_rename w a T Fin.castSucc) (under hT G)
  let H := (encoded w.castSucc.castSucc (Fin.last (m+1)) a.castSucc.castSucc a.castSucc.castSucc T.castSucc.castSucc).conj
    (diagonal (Fin.last (m+1)))
  let Δ := Context.add H (Context.image Formula.raise Ξ)
  apply Derives.exE (p := H) ht1
  have hZ2 := ZFContext.under (ZFContext.under hZ G) H
  have hw2 : Derives Δ (omega w.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise, omega_rename]) (under (under hw G) H)
  have hG : Derives Ξ G := .hyp (Or.inl rfl)
  have hg2 : Derives Δ ((encoded w.castSucc.castSucc (Fin.last m).castSucc a.castSucc.castSucc a.castSucc.castSucc R.castSucc.castSucc).conj
      (diagonal (Fin.last m).castSucc)) :=
    of_eq (by simp only [G, Formula.raise, Formula.rename, encoded_rename, diagonal_rename]) (under hG H)
  have hH : Derives Δ H := .hyp (Or.inl rfl)
  have he := map_unique hZ2 w.castSucc.castSucc a.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
    (.conjI (.conjR (.conjL hg2)) (.conjR hg2)) (.conjI (.conjR (.conjL hH)) (.conjR hH))
  have hr2 := SyntaxMapCodeSyntax.graph_subst _ _ _ _ _ _ he (.conjL hg2)
  exact SyntaxMapCode.unique_code hZ2 _ _ _ _ _ _ hw2 hr2 (.conjL hH)
end PPAC.Migration.Internal.SyntaxIdentityUnique
