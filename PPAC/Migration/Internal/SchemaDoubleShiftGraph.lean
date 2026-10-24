import PPAC.Migration.Internal.SchemaDoubleShiftPoint

/-! Complete double-shift graph, with all intermediate maps object-eliminated. -/
namespace PPAC.Migration.Internal.SchemaDoubleShiftGraph
open Source SourceAlgebra SourceLogic OmegaSyntax GraphSyntax HornBinderSyntax SchemaDoubleShiftSyntax
open SyntaxRenameQuerySyntax (of_eq)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem index_map {m} {Γ : Context m} (w n b c g : Fin m) (hg : Derives Γ (SchemaDoubleShiftSyntax.map w n b c g)) :
    Derives Γ (SyntaxIndexMapSyntax.indexMap w g n c) := by
  let B := body w n b c g
  let Δ := Context.add B (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 B _ hg
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  exact of_eq (SyntaxIndexMapSyntax.indexMap_rename w g n c (old 2)).symm
    (SyntaxComposeGraph.target_map (old 2 w) (slot 2 0) (slot 2 1) (old 2 n) (old 2 b) (old 2 c) (old 2 g) (.conjR (.conjR hB)))

theorem edge_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n b c g i j : Fin m)
    (hg : Derives Γ (SchemaDoubleShiftSyntax.map w n b c g)) :
    Derives Γ ((edge g i j).iff ((Formula.mem i n).conj (displacement i j))) := by
  let B := body w n b c g
  let Δ := Context.add B (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 B _ hg
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have ho := SchemaDoubleShiftPoint.matrix_edge_iff (HornBinderRules.zf_body 2 hZ B) (old 2 w) (old 2 n) (old 2 b) (old 2 c)
    (old 2 g) (old 2 i) (old 2 j) (slot 2) hB
  exact of_eq (by simp only [Formula.iff, Formula.rename, edge_rename, displacement_rename]) ho

def displacementMatrix : Formula 2 := displacement 0 1

theorem displacementMatrix_rel {m} (ρ : Fin 0 → Fin m) (i j : Fin m) :
    ReplacementPredicates.rel displacementMatrix ρ i j = displacement i j := by
  simp only [ReplacementPredicates.rel, Source.SetLanguage.relation, displacementMatrix, displacement_rename]
  rfl

theorem to_graph {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n b c g : Fin m)
    (hg : Derives Γ (SchemaDoubleShiftSyntax.map w n b c g)) :
    Derives Γ (RelationGraphSyntax.functionGraph displacementMatrix (Fin.elim0 : Fin 0 → Fin m) n g) := by
  apply Derives.conjI
  · exact .conjL (.conjR (index_map w n b c g hg))
  · simp only [RelationGraphSyntax.edgeLaw, displacementMatrix_rel]
    apply Derives.allI
    apply Derives.allI
    have hZ2 := ZFContext.rename (ZFContext.rename hZ Fin.castSucc) Fin.castSucc
    have hg2 : Derives (raisedContext 2 Γ) (SchemaDoubleShiftSyntax.map w.castSucc.castSucc n.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc g.castSucc.castSucc) :=
      of_eq (by simp only [map_rename]) (Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hg))
    exact edge_iff hZ2 w.castSucc.castSucc n.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc
      g.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) hg2

theorem unique_map {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n b c g h : Fin m)
    (hg : Derives Γ (SchemaDoubleShiftSyntax.map w n b c g)) (hh : Derives Γ (SchemaDoubleShiftSyntax.map w n b c h)) : Derives Γ (.equal g h) :=
  RelationGraph.unique_graph hZ displacementMatrix (Fin.elim0 : Fin 0 → Fin m) n g h (to_graph hZ w n b c g hg) (to_graph hZ w n b c h hh)

theorem exists_map {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n b c : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (.mem n w))
    (hb : Derives Γ (successor b n)) (hc : Derives Γ (successor c b)) : Derives Γ (existsMap w n b c) := by
  let R := SyntaxFreeShiftSyntax.shiftMap w.castSucc n.castSucc b.castSucc (Fin.last m)
  let Γ1 := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) (SyntaxFreeShiftGraph.exists_map hZ w n b hw hn hb)
  have hZ1 := ZFContext.under hZ R
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw R)
  have hbW := OmegaStructureAlgebra.successor_member w b n (ZFContext.arithmetic hZ).base.extensionality hw hn hb
  have hc1 := of_eq (successor_rename c b Fin.castSucc) (under hc R)
  let T := SyntaxFreeShiftSyntax.shiftMap w.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc (Fin.last (m+1))
  let Γ2 := Context.add T (Context.image Formula.raise Γ1)
  apply Derives.exE (p := T) (SyntaxFreeShiftGraph.exists_map hZ1 w.castSucc b.castSucc c.castSucc hw1 (under hbW R) hc1)
  have hZ2 := ZFContext.under hZ1 T
  have hR : Derives Γ1 R := .hyp (Or.inl rfl)
  have hR2 : Derives Γ2 (SyntaxFreeShiftSyntax.shiftMap w.castSucc.castSucc n.castSucc.castSucc b.castSucc.castSucc (Fin.last m).castSucc) :=
    of_eq (by simp only [R, Formula.raise, SyntaxFreeShiftSyntax.shiftMap_rename]) (under hR T)
  have hT : Derives Γ2 T := .hyp (Or.inl rfl)
  let G := SyntaxComposeSyntax.composed w.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc
    n.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc (Fin.last (m+2))
  let Γ3 := Context.add G (Context.image Formula.raise Γ2)
  apply Derives.exE (p := G) (SyntaxComposeGraph.exists_graph hZ2 w.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
    n.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc (.conjL (.conjR hR2)) (.conjL (.conjR hT)))
  have hR3 := of_eq (SyntaxFreeShiftSyntax.shiftMap_rename w.castSucc.castSucc n.castSucc.castSucc b.castSucc.castSucc (Fin.last m).castSucc Fin.castSucc) (under hR2 G)
  have hT3 : Derives Γ3 (SyntaxFreeShiftSyntax.shiftMap w.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc) := of_eq (by simp only [T, Formula.raise, SyntaxFreeShiftSyntax.shiftMap_rename]) (under hT G)
  have hG : Derives Γ3 G := .hyp (Or.inl rfl)
  have ho := intro_exists w.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc (Fin.last (m+2))
    (intro_map w.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc (Fin.last (m+2))
      (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc hR3 hT3 hG)
  exact of_eq (by simp only [Formula.raise, existsMap_rename]) ho

end PPAC.Migration.Internal.SchemaDoubleShiftGraph
