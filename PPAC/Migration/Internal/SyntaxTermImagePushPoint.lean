import PPAC.Migration.Internal.SyntaxTermImagePushSyntax

/-! 实际项像表逐值变换的存在、唯一性和准确目标类型；所有旧值均为对象见证。 -/
namespace PPAC.Migration.Internal.SyntaxTermImagePushPoint
open Source SourceAlgebra SourceLogic OmegaSyntax GraphSyntax SyntaxRenameQuerySyntax SyntaxTermImagePushSyntax
open SyntaxTermImageSyntax (imageMap imageMap_rename)
open SyntaxRenameTermSyntax (renamed renamed_rename)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem renamed_subst_input {m} {Γ : Context m} (w R S c d C D t u q : Fin m)
    (he : Derives Γ (.equal t u)) (hq : Derives Γ (renamed w R S c d C D t q)) : Derives Γ (renamed w R S c d C D u q) := by
  let P := renamed w.castSucc R.castSucc S.castSucc c.castSucc d.castSucc C.castSucc D.castSucc (Fin.last m) q.castSucc
  have e0 : P.instantiate t = renamed w R S c d C D t q := by
    simp only [P, Formula.instantiate, renamed_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have e1 : P.instantiate u = renamed w R S c d C D u q := by
    simp only [P, Formula.instantiate, renamed_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact of_eq e1 (Derives.eqSubst P he (of_eq e0.symm hq))

theorem target_type {m} {Γ : Context m} (w R S c d C D f i q : Fin m)
    (hv : Derives Γ (value w R S c d C D f i q)) : Derives Γ (SyntaxTermSyntax.term w C D q) := by
  let B := (edge f.castSucc i.castSucc (Fin.last m)).conj
    (renamed w.castSucc R.castSucc S.castSucc c.castSucc d.castSucc C.castSucc D.castSucc (Fin.last m) q.castSucc)
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) hv
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have ho := SyntaxRenameTermTyping.target_term _ _ _ _ _ _ _ _ _ (.conjR hB)
  exact of_eq (SyntaxTermSyntax.term_rename w C D q Fin.castSucc).symm ho

theorem unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w R S c d C D f a i q v : Fin m)
    (hw : Derives Γ (omega w)) (hf : Derives Γ (functionOn f a))
    (hq : Derives Γ (value w R S c d C D f i q)) (hv : Derives Γ (value w R S c d C D f i v)) : Derives Γ (.equal q v) := by
  let B := (edge f.castSucc i.castSucc (Fin.last m)).conj
    (renamed w.castSucc R.castSucc S.castSucc c.castSucc d.castSucc C.castSucc D.castSucc (Fin.last m) q.castSucc)
  let Ξ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) hq
  have hv1 : Derives Ξ (value w.castSucc R.castSucc S.castSucc c.castSucc d.castSucc C.castSucc D.castSucc f.castSucc i.castSucc v.castSucc) :=
    of_eq (value_rename w R S c d C D f i v Fin.castSucc) (under hv B)
  let A := (edge f.castSucc.castSucc i.castSucc.castSucc (Fin.last (m+1))).conj
    (renamed w.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc C.castSucc.castSucc D.castSucc.castSucc (Fin.last (m+1)) v.castSucc.castSucc)
  let Δ := Context.add A (Context.image Formula.raise Ξ)
  apply Derives.exE (p := A) hv1
  have hZ2 := ZFContext.under (ZFContext.under hZ B) A
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (under (under hw B) A)
  have hf2 : Derives Δ (functionOn f.castSucc.castSucc a.castSucc.castSucc) := of_eq (by simp only [Formula.raise, functionOn_rename]) (under (under hf B) A)
  have hB : Derives Ξ B := .hyp (Or.inl rfl)
  have hb2 : Derives Δ ((edge f.castSucc.castSucc i.castSucc.castSucc (Fin.last m).castSucc).conj
      (renamed w.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc C.castSucc.castSucc D.castSucc.castSucc (Fin.last m).castSucc q.castSucc.castSucc)) :=
    of_eq (by simp only [B, Formula.raise, Formula.rename, edge_rename, renamed_rename]) (under hB A)
  have hA : Derives Δ A := .hyp (Or.inl rfl)
  have he := GraphProperties.single_valued _ _ _ _ _ (ZFContext.arithmetic hZ2).base.extensionality hf2 (.conjL hb2) (.conjL hA)
  have hr := renamed_subst_input _ _ _ _ _ _ _ _ _ _ he (.conjR hb2)
  exact SyntaxRenameTermUnique.unique hZ2 _ _ _ _ _ _ _ _ _ _ hw2 hr (.conjR hA)

theorem exists_value {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w R S c d C D f a i : Fin m)
    (hw : Derives Γ (omega w)) (hf : Derives Γ (imageMap w f a c d))
    (hm : Derives Γ (SyntaxIndexMapSyntax.maps w R S c d C D)) (hi : Derives Γ (.mem i a)) :
    Derives Γ (.ex (value w.castSucc R.castSucc S.castSucc c.castSucc d.castSucc C.castSucc D.castSucc f.castSucc i.castSucc (Fin.last m))) := by
  let T := edge f.castSucc i.castSucc (Fin.last m)
  let Ξ := Context.add T (Context.image Formula.raise Γ)
  apply Derives.exE (p := T) (GraphProperties.output_exists f a i (SyntaxTermImageSyntax.image_function w f a c d hf) hi)
  have hZ1 := ZFContext.under hZ T
  have hw1 : Derives Ξ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw T)
  have hf1 : Derives Ξ (imageMap w.castSucc f.castSucc a.castSucc c.castSucc d.castSucc) := of_eq (imageMap_rename w f a c d Fin.castSucc) (under hf T)
  have hm1 : Derives Ξ (SyntaxIndexMapSyntax.maps w.castSucc R.castSucc S.castSucc c.castSucc d.castSucc C.castSucc D.castSucc) := of_eq (SyntaxIndexMapSyntax.maps_rename w R S c d C D Fin.castSucc) (under hm T)
  have hT : Derives Ξ T := .hyp (Or.inl rfl)
  have ht := SyntaxTermImageSyntax.image_type w.castSucc f.castSucc a.castSucc c.castSucc d.castSucc i.castSucc (Fin.last m) hf1 hT
  let Q := (Formula.mem (Fin.last (m+1)) w.castSucc.castSucc).conj
    (renamed w.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc C.castSucc.castSucc D.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)))
  let Δ := Context.add Q (Context.image Formula.raise Ξ)
  apply Derives.exE (p := Q) (SyntaxRenameTermExistence.for_term hZ1 w.castSucc R.castSucc S.castSucc c.castSucc d.castSucc C.castSucc D.castSucc (Fin.last m) hw1 hm1 ht)
  have he2 : Derives Δ (edge f.castSucc.castSucc i.castSucc.castSucc (Fin.last m).castSucc) :=
    of_eq (by simp only [T, Formula.raise, edge_rename]) (under hT Q)
  have hQ : Derives Δ Q := .hyp (Or.inl rfl)
  have hv := intro_value w.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc C.castSucc.castSucc D.castSucc.castSucc f.castSucc.castSucc i.castSucc.castSucc (Fin.last (m+1)) (Fin.last m).castSucc he2 (.conjR hQ)
  have ho : Derives Δ (.ex (value w.castSucc.castSucc.castSucc R.castSucc.castSucc.castSucc S.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc C.castSucc.castSucc.castSucc D.castSucc.castSucc.castSucc f.castSucc.castSucc.castSucc i.castSucc.castSucc.castSucc (Fin.last (m+2)))) := by
    apply Derives.exI (Fin.last (m+1))
    exact of_eq (by simp only [Formula.instantiate, value_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hv
  exact of_eq (by simp only [Formula.raise, Formula.rename, value_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]) ho

theorem source_member {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w R S c d C D f a i q : Fin m)
    (hf : Derives Γ (imageMap w f a c d)) (hv : Derives Γ (value w R S c d C D f i q)) : Derives Γ (.mem i a) := by
  let B := (edge f.castSucc i.castSucc (Fin.last m)).conj
    (renamed w.castSucc R.castSucc S.castSucc c.castSucc d.castSucc C.castSucc D.castSucc (Fin.last m) q.castSucc)
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) hv
  have hf1 : Derives Δ (imageMap w.castSucc f.castSucc a.castSucc c.castSucc d.castSucc) := of_eq (imageMap_rename w f a c d Fin.castSucc) (under hf B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  exact GraphProperties.domain_of_edge _ _ _ _ (ZFContext.arithmetic (ZFContext.under hZ B)).base.extensionality
    (SyntaxTermImageSyntax.image_function _ _ _ _ _ hf1) (.conjL hB)

end PPAC.Migration.Internal.SyntaxTermImagePushPoint
