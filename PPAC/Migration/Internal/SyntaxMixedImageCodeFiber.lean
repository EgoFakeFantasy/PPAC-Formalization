import PPAC.Migration.Internal.SyntaxMixedImageCodeUnique

/-! 混合项像编码/解码的实际唯一纤维与精确合法输入双条件。 -/
namespace PPAC.Migration.Internal.SyntaxMixedImageCodeFiber
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxRenameQuerySyntax SyntaxMixedImageCodeSyntax
open SyntaxTermImageSyntax (imageMap imageMap_rename)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem code_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w f a c d L : Fin m)
    (hw : Derives Γ (omega w)) (he : Derives Γ (encoded w f a c d L)) : Derives Γ (codeUnique w f a c d L) := by
  apply Derives.allI
  apply Derives.impI
  let V := encoded w.castSucc f.castSucc a.castSucc c.castSucc d.castSucc (Fin.last m)
  let Δ := Context.add V (Context.image Formula.raise Γ)
  have he1 : Derives Δ (encoded w.castSucc f.castSucc a.castSucc c.castSucc d.castSucc L.castSucc) := of_eq (encoded_rename w f a c d L Fin.castSucc) (under he V)
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw V)
  exact SyntaxMixedImageCodeUnique.unique_code (ZFContext.under hZ V) w.castSucc f.castSucc a.castSucc c.castSucc d.castSucc (Fin.last m) L.castSucc hw1 (.hyp (Or.inl rfl)) he1

theorem graph_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w f a c d L : Fin m) (he : Derives Γ (encoded w f a c d L)) : Derives Γ (graphUnique w f a c d L) := by
  apply Derives.allI
  apply Derives.impI
  let V := encoded w.castSucc (Fin.last m) a.castSucc c.castSucc d.castSucc L.castSucc
  let Δ := Context.add V (Context.image Formula.raise Γ)
  have he1 : Derives Δ (encoded w.castSucc f.castSucc a.castSucc c.castSucc d.castSucc L.castSucc) := of_eq (encoded_rename w f a c d L Fin.castSucc) (under he V)
  exact SyntaxMixedImageCodeUnique.unique_graph (ZFContext.under hZ V) w.castSucc (Fin.last m) f.castSucc a.castSucc c.castSucc d.castSucc L.castSucc (.hyp (Or.inl rfl)) he1

theorem code_fiber {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w f a c d : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (imageMap w f a c d)) : Derives Γ (codeFiber w f a c d) := by
  let B := encoded w.castSucc f.castSucc a.castSucc c.castSucc d.castSucc (Fin.last m)
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) (SyntaxMixedImageCodeExistence.exists_code hZ w f a c d hw hi)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw B)
  have hu := code_unique (ZFContext.under hZ B) w.castSucc f.castSucc a.castSucc c.castSucc d.castSucc (Fin.last m) hw1 hB
  have ho := intro_code_fiber w.castSucc f.castSucc a.castSucc c.castSucc d.castSucc (Fin.last m) (.conjI hB hu)
  exact of_eq (codeFiber_rename w f a c d Fin.castSucc).symm ho

theorem code_fiber_iff_input {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w f a c d : Fin m)
    (hw : Derives Γ (omega w)) : Derives Γ ((codeFiber w f a c d).iff (imageMap w f a c d)) := by
  apply Derives.conjI
  · apply Derives.impI
    let E := codeFiber w f a c d
    let B := (encoded w.castSucc f.castSucc a.castSucc c.castSucc d.castSucc (Fin.last m)).conj (codeUnique w.castSucc f.castSucc a.castSucc c.castSucc d.castSucc (Fin.last m))
    let Δ := Context.add B (Context.image Formula.raise (Context.add E Γ))
    apply Derives.exE (p := B) (.hyp (Or.inl rfl))
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    exact of_eq (imageMap_rename w f a c d Fin.castSucc).symm (Derives.conjL (.conjL hB))
  · apply Derives.impI
    exact code_fiber (ZFContext.add hZ _) w f a c d (add hw _) (.hyp (Or.inl rfl))

theorem graph_fiber {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a c d L : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (termList w a c d L)) : Derives Γ (graphFiber w a c d L) := by
  let B := encoded w.castSucc (Fin.last m) a.castSucc c.castSucc d.castSucc L.castSucc
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) (SyntaxMixedImageCodeExistence.exists_graph hZ w a c d L hw hi)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hu := graph_unique (ZFContext.under hZ B) w.castSucc (Fin.last m) a.castSucc c.castSucc d.castSucc L.castSucc hB
  have ho := intro_graph_fiber w.castSucc (Fin.last m) a.castSucc c.castSucc d.castSucc L.castSucc (.conjI hB hu)
  exact of_eq (graphFiber_rename w a c d L Fin.castSucc).symm ho

theorem graph_fiber_iff_input {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a c d L : Fin m)
    (hw : Derives Γ (omega w)) : Derives Γ ((graphFiber w a c d L).iff (termList w a c d L)) := by
  apply Derives.conjI
  · apply Derives.impI
    let E := graphFiber w a c d L
    let B := (encoded w.castSucc (Fin.last m) a.castSucc c.castSucc d.castSucc L.castSucc).conj (graphUnique w.castSucc (Fin.last m) a.castSucc c.castSucc d.castSucc L.castSucc)
    let Δ := Context.add B (Context.image Formula.raise (Context.add E Γ))
    apply Derives.exE (p := B) (.hyp (Or.inl rfl))
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have ho := SyntaxMixedImageCodeFields.term_list w.castSucc (Fin.last m) a.castSucc c.castSucc d.castSucc L.castSucc (.conjL hB)
    exact of_eq (termList_rename w a c d L Fin.castSucc).symm ho
  · apply Derives.impI
    exact graph_fiber (ZFContext.add hZ _) w a c d L (add hw _) (.hyp (Or.inl rfl))

end PPAC.Migration.Internal.SyntaxMixedImageCodeFiber
