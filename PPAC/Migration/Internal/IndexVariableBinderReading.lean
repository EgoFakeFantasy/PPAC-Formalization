import PPAC.Migration.Internal.IndexVariableBinderEdges

/-! 原索引提升的全部内部边在新bound/free项像图上保持准确变量码读取。 -/
namespace PPAC.Migration.Internal.IndexVariableBinderReading
open Source SourceAlgebra SourceLogic OmegaSyntax GraphSyntax IndexVariableImageReadingSyntax
open SyntaxRenameQuerySyntax (of_eq)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem bound_at_edge {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r f g a b c d A C L K H U V z n i j q : Fin m)
    (hw : Derives Γ (omega w)) (hm : Derives Γ (SyntaxVariableImageSyntax.mapped true w r a c d f))
    (hl : Derives Γ (SyntaxIndexLiftSyntax.lifted w r a c A C L))
    (hn : Derives Γ (SyntaxMixedImageBinderSyntax.ready w f g a b c d A C K H U V z n))
    (he : Derives Γ (edge L i j)) : Derives Γ ((edge K i q).iff (SyntaxVariableSyntax.code true w j q)) := by
  have hv := Derives.impE (.conjL (SyntaxIndexLift.edge_iff hZ w r a c A C L i j hw hl)) he
  apply Derives.disjE hv
  · let Z := (empty i).conj (empty j)
    have hZs : Derives (Context.add Z Γ) Z := .hyp (Or.inl rfl)
    have hReady := add hn Z
    exact IndexVariableBinderEdges.zero_read (ZFContext.add hZ Z) w U V f g a b c d A C n K H z i j q (add hw Z)
      (.conjR (.conjR (.conjR hReady))) (.conjL (.conjR (.conjR hReady))) (.conjL hZs) (.conjR hZs)
  · let P := SyntaxIndexLiftSyntax.shifted r a i j
    let B := SyntaxIndexLiftSyntax.shiftBody r a i j
    let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise (Context.add P Γ)))
    apply SyntaxRenameBinders.eliminate_2 B _ (.hyp (Or.inl rfl))
    have hZ2 := SyntaxRenameBinders.zf_under_2 (ZFContext.add hZ P) B
    have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxRenameBinders.under_2 (add hw P) B)
    have hm2 : Derives Δ (SyntaxVariableImageSyntax.mapped true w.castSucc.castSucc r.castSucc.castSucc a.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc f.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxVariableImageSyntax.mapped_rename]) (SyntaxRenameBinders.under_2 (add hm P) B)
    have hn2 : Derives Δ (SyntaxMixedImageBinderSyntax.ready w.castSucc.castSucc f.castSucc.castSucc g.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc A.castSucc.castSucc C.castSucc.castSucc K.castSucc.castSucc H.castSucc.castSucc U.castSucc.castSucc V.castSucc.castSucc z.castSucc.castSucc n.castSucc.castSucc) :=
      of_eq (by simp only [Formula.raise, SyntaxMixedImageBinderSyntax.ready_rename]) (SyntaxRenameBinders.under_2 (add hn P) B)
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have ho := IndexVariableBinderEdges.bound_read hZ2 w.castSucc.castSucc r.castSucc.castSucc f.castSucc.castSucc g.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc A.castSucc.castSucc C.castSucc.castSucc n.castSucc.castSucc K.castSucc.castSucc H.castSucc.castSucc U.castSucc.castSucc V.castSucc.castSucc i.castSucc.castSucc j.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) q.castSucc.castSucc hw2 hm2
      (.conjR (.conjR (.conjR hn2))) (.conjL hn2) (.conjL (.conjR hn2)) (.conjR (.conjL hB)) (.conjL (.conjR hB)) (.conjR (.conjR hB))
    exact of_eq (by simp only [Formula.raise, Formula.iff, Formula.rename, edge_rename, SyntaxVariableSyntax.code_rename]) ho

theorem bound_reads {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r f g a b c d A C L K H U V z n : Fin m)
    (hw : Derives Γ (omega w)) (hm : Derives Γ (SyntaxVariableImageSyntax.mapped true w r a c d f))
    (hl : Derives Γ (SyntaxIndexLiftSyntax.lifted w r a c A C L))
    (hn : Derives Γ (SyntaxMixedImageBinderSyntax.ready w f g a b c d A C K H U V z n)) :
    Derives Γ (reads true w L K) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  let E := edge L.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc
  let Δ := Context.add E (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise Γ)))
  have hZ1 := ZFContext.rename hZ Fin.castSucc
  have hw1 := Derives.rename Fin.castSucc hw
  have hm1 := Derives.rename Fin.castSucc hm
  have hn1 := Derives.rename Fin.castSucc hn
  have hl1 := Derives.rename Fin.castSucc hl
  have hZ2 := ZFContext.rename hZ1 Fin.castSucc
  have hw2 := Derives.rename Fin.castSucc hw1
  have hm2 := Derives.rename Fin.castSucc hm1
  have hn2 := Derives.rename Fin.castSucc hn1
  have hl2 := Derives.rename Fin.castSucc hl1
  have hZ3 := ZFContext.rename hZ2 Fin.castSucc
  have hw3 := Derives.rename Fin.castSucc hw2
  have hm3 := Derives.rename Fin.castSucc hm2
  have hn3 := Derives.rename Fin.castSucc hn2
  have hl3 := Derives.rename Fin.castSucc hl2
  have hReady : Derives Δ (SyntaxMixedImageBinderSyntax.ready w.castSucc.castSucc.castSucc f.castSucc.castSucc.castSucc g.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc A.castSucc.castSucc.castSucc C.castSucc.castSucc.castSucc K.castSucc.castSucc.castSucc H.castSucc.castSucc.castSucc U.castSucc.castSucc.castSucc V.castSucc.castSucc.castSucc z.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc) := of_eq (by simp only [SyntaxMixedImageBinderSyntax.ready_rename]) (add hn3 E)
  exact bound_at_edge (ZFContext.add hZ3 E) w.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc f.castSucc.castSucc.castSucc g.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc A.castSucc.castSucc.castSucc C.castSucc.castSucc.castSucc L.castSucc.castSucc.castSucc K.castSucc.castSucc.castSucc H.castSucc.castSucc.castSucc U.castSucc.castSucc.castSucc V.castSucc.castSucc.castSucc z.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc (Fin.last (m+2)) (of_eq (by simp only [omega_rename]) (add hw3 E)) (of_eq (by simp only [SyntaxVariableImageSyntax.mapped_rename]) (add hm3 E)) (of_eq (by simp only [SyntaxIndexLiftSyntax.lifted_rename]) (add hl3 E)) hReady (.hyp (Or.inl rfl))

theorem free_reads {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w s f g a b c d A C K H U V z n : Fin m)
    (hw : Derives Γ (omega w)) (hm : Derives Γ (SyntaxVariableImageSyntax.mapped false w s b c d g))
    (hn : Derives Γ (SyntaxMixedImageBinderSyntax.ready w f g a b c d A C K H U V z n)) :
    Derives Γ (reads false w s H) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  let E := edge s.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc
  let Δ := Context.add E (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise Γ)))
  have hZ1 := ZFContext.rename hZ Fin.castSucc
  have hw1 := Derives.rename Fin.castSucc hw
  have hm1 := Derives.rename Fin.castSucc hm
  have hn1 := Derives.rename Fin.castSucc hn
  have hZ2 := ZFContext.rename hZ1 Fin.castSucc
  have hw2 := Derives.rename Fin.castSucc hw1
  have hm2 := Derives.rename Fin.castSucc hm1
  have hn2 := Derives.rename Fin.castSucc hn1
  have hZ3 := ZFContext.rename hZ2 Fin.castSucc
  have hw3 := Derives.rename Fin.castSucc hw2
  have hm3 := Derives.rename Fin.castSucc hm2
  have hn3 := Derives.rename Fin.castSucc hn2
  have hReady : Derives Δ (SyntaxMixedImageBinderSyntax.ready w.castSucc.castSucc.castSucc f.castSucc.castSucc.castSucc g.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc A.castSucc.castSucc.castSucc C.castSucc.castSucc.castSucc K.castSucc.castSucc.castSucc H.castSucc.castSucc.castSucc U.castSucc.castSucc.castSucc V.castSucc.castSucc.castSucc z.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc) := of_eq (by simp only [SyntaxMixedImageBinderSyntax.ready_rename]) (add hn3 E)
  exact IndexVariableBinderEdges.free_read (ZFContext.add hZ3 E) w.castSucc.castSucc.castSucc s.castSucc.castSucc.castSucc f.castSucc.castSucc.castSucc g.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc A.castSucc.castSucc.castSucc C.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc K.castSucc.castSucc.castSucc H.castSucc.castSucc.castSucc U.castSucc.castSucc.castSucc V.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc (Fin.last (m+2)) (of_eq (by simp only [omega_rename]) (add hw3 E)) (of_eq (by simp only [SyntaxVariableImageSyntax.mapped_rename]) (add hm3 E)) (.conjR (.conjR (.conjR hReady))) (.conjL hReady) (.conjL (.conjR hReady)) (.hyp (Or.inl rfl))

end PPAC.Migration.Internal.IndexVariableBinderReading
