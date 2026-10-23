import PPAC.Migration.Internal.SyntaxMixedImageCodeFiber

/-! 两张混合项像表的实际原码对及实际解码图对；所有见证仍在对象量词内。 -/
namespace PPAC.Migration.Internal.SyntaxMixedImageCodePairs
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxRenameQuerySyntax SyntaxMixedImageCodeSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

def graphBody {m} (w a b c d R S : Fin m) : Formula (m+2) :=
  encodings w.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc

def existsGraphs {m} (w a b c d R S : Fin m) : Formula m := .ex (.ex (graphBody w a b c d R S))

def codeBody {m} (w r s a b c d : Fin m) : Formula (m+2) :=
  encodings w.castSucc.castSucc r.castSucc.castSucc s.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))

def existsCodes {m} (w r s a b c d : Fin m) : Formula m := .ex (.ex (codeBody w r s a b c d))

theorem existsGraphs_rename {m k} (w a b c d R S : Fin m) (ρ : Fin m → Fin k) :
    (existsGraphs w a b c d R S).rename ρ = existsGraphs (ρ w) (ρ a) (ρ b) (ρ c) (ρ d) (ρ R) (ρ S) := by
  simp only [existsGraphs, graphBody, Formula.rename, encodings_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem existsCodes_rename {m k} (w r s a b c d : Fin m) (ρ : Fin m → Fin k) :
    (existsCodes w r s a b c d).rename ρ = existsCodes (ρ w) (ρ r) (ρ s) (ρ a) (ρ b) (ρ c) (ρ d) := by
  simp only [existsCodes, codeBody, Formula.rename, encodings_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem intro_graphs {m} {Γ : Context m} (w r s a b c d R S : Fin m)
    (he : Derives Γ (encodings w r s a b c d R S)) : Derives Γ (existsGraphs w a b c d R S) := by
  apply Derives.exI r
  apply Derives.exI s
  exact of_eq (by simp only [graphBody, Formula.instantiate, encodings_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) he

theorem intro_codes {m} {Γ : Context m} (w r s a b c d R S : Fin m)
    (he : Derives Γ (encodings w r s a b c d R S)) : Derives Γ (existsCodes w r s a b c d) := by
  apply Derives.exI R
  apply Derives.exI S
  exact of_eq (by simp only [codeBody, Formula.instantiate, encodings_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) he

theorem image_maps {m} {Γ : Context m} (w r s a b c d R S : Fin m)
    (he : Derives Γ (encodings w r s a b c d R S)) : Derives Γ (SyntaxTermImageSyntax.maps w r s a b c d) :=
  .conjI (.conjL (.conjL he)) (.conjL (.conjR he))

theorem term_lists {m} {Γ : Context m} (w r s a b c d R S : Fin m)
    (he : Derives Γ (encodings w r s a b c d R S)) : Derives Γ (termLists w a b c d R S) :=
  .conjI (SyntaxMixedImageCodeFields.term_list w r a c d R (.conjL he))
    (SyntaxMixedImageCodeFields.term_list w s b c d S (.conjR he))

theorem exists_graphs {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b c d R S : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (termLists w a b c d R S)) : Derives Γ (existsGraphs w a b c d R S) := by
  let B := encoded w.castSucc (Fin.last m) a.castSucc c.castSucc d.castSucc R.castSucc
  let Ξ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) (SyntaxMixedImageCodeExistence.exists_graph hZ w a c d R hw (.conjL hi))
  have hw1 : Derives Ξ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw B)
  have hs1 : Derives Ξ (termList w.castSucc b.castSucc c.castSucc d.castSucc S.castSucc) := of_eq (termList_rename w b c d S Fin.castSucc) (under (.conjR hi) B)
  let D := encoded w.castSucc.castSucc (Fin.last (m+1)) b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc S.castSucc.castSucc
  let Δ := Context.add D (Context.image Formula.raise Ξ)
  apply Derives.exE (p := D) (SyntaxMixedImageCodeExistence.exists_graph (ZFContext.under hZ B) w.castSucc b.castSucc c.castSucc d.castSucc S.castSucc hw1 hs1)
  have hB : Derives Ξ B := .hyp (Or.inl rfl)
  have hb2 : Derives Δ (encoded w.castSucc.castSucc (Fin.last m).castSucc a.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc R.castSucc.castSucc) := of_eq (by simp only [B, Formula.raise, encoded_rename]) (under hB D)
  have hD : Derives Δ D := .hyp (Or.inl rfl)
  have ho := intro_graphs w.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc (.conjI hb2 hD)
  exact of_eq (by simp only [Formula.raise, existsGraphs_rename]) ho

theorem exists_codes {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r s a b c d : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (SyntaxTermImageSyntax.maps w r s a b c d)) : Derives Γ (existsCodes w r s a b c d) := by
  let B := encoded w.castSucc r.castSucc a.castSucc c.castSucc d.castSucc (Fin.last m)
  let Ξ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) (SyntaxMixedImageCodeExistence.exists_code hZ w r a c d hw (.conjL hi))
  have hw1 : Derives Ξ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw B)
  have hs1 : Derives Ξ (SyntaxTermImageSyntax.imageMap w.castSucc s.castSucc b.castSucc c.castSucc d.castSucc) := of_eq (SyntaxTermImageSyntax.imageMap_rename w s b c d Fin.castSucc) (under (.conjR hi) B)
  let D := encoded w.castSucc.castSucc s.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc (Fin.last (m+1))
  let Δ := Context.add D (Context.image Formula.raise Ξ)
  apply Derives.exE (p := D) (SyntaxMixedImageCodeExistence.exists_code (ZFContext.under hZ B) w.castSucc s.castSucc b.castSucc c.castSucc d.castSucc hw1 hs1)
  have hB : Derives Ξ B := .hyp (Or.inl rfl)
  have hb2 : Derives Δ (encoded w.castSucc.castSucc r.castSucc.castSucc a.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc (Fin.last m).castSucc) := of_eq (by simp only [B, Formula.raise, encoded_rename]) (under hB D)
  have hD : Derives Δ D := .hyp (Or.inl rfl)
  have ho := intro_codes w.castSucc.castSucc r.castSucc.castSucc s.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) (.conjI hb2 hD)
  exact of_eq (by simp only [Formula.raise, existsCodes_rename]) ho

theorem graphs_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r s a b c d R S u v : Fin m)
    (hr : Derives Γ (encodings w r s a b c d R S)) (hu : Derives Γ (encodings w u v a b c d R S)) :
    Derives Γ ((Formula.equal r u).conj (Formula.equal s v)) :=
  .conjI (SyntaxMixedImageCodeUnique.unique_graph hZ w r u a c d R (.conjL hr) (.conjL hu))
    (SyntaxMixedImageCodeUnique.unique_graph hZ w s v b c d S (.conjR hr) (.conjR hu))

theorem codes_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r s a b c d R S U V : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (encodings w r s a b c d R S))
    (hu : Derives Γ (encodings w r s a b c d U V)) : Derives Γ ((Formula.equal R U).conj (Formula.equal S V)) :=
  .conjI (SyntaxMixedImageCodeUnique.unique_code hZ w r a c d R U hw (.conjL hr) (.conjL hu))
    (SyntaxMixedImageCodeUnique.unique_code hZ w s b c d S V hw (.conjR hr) (.conjR hu))

end PPAC.Migration.Internal.SyntaxMixedImageCodePairs
