import PPAC.Migration.ReplacementInstances

/-! Collection与分离推出原始源Replacement的实质对象证明。 -/
namespace PPAC.Migration.ReplacementFromCollection
open Source SourceAlgebra SourceLogic ReplacementPredicates ReplacementInstances

theorem fiber_value {n m} {Γ : Context m} (p : Formula (n+2)) (ρ : Fin n → Fin m)
    (x : Fin m) (hf : Derives Γ (fiber p ρ x)) : Derives Γ (hasValue p ρ x) := by
  let U : Formula (m+1) := (rel p (paramsUp ρ) x.castSucc (Fin.last m)).conj
    (unique p (paramsUp ρ) x.castSucc (Fin.last m))
  let Γu := Context.add U (Context.image Formula.raise Γ)
  change Derives Γ (.ex U) at hf
  apply Derives.exE (p := U) hf
  have hr : Derives Γu (rel p (paramsUp ρ) x.castSucc (Fin.last m)) := .conjL (.hyp (Or.inl rfl))
  have hv : Derives Γu (hasValue p (paramsUp ρ) x.castSucc) := by
    apply Derives.exI (Fin.last m)
    simpa only [Formula.instantiate, rel_rename, paramsUp, Fin.lastCases_last,
      Fin.lastCases_castSucc, id_eq] using hr
  simpa only [Formula.raise, hasValue_rename] using hv

theorem total_relation {n m} {Γ : Context m} (p : Formula (n+2)) (ρ : Fin n → Fin m)
    (a : Fin m) (ht : Derives Γ (total p ρ a)) : Derives Γ (totalRelation p ρ a) := by
  apply Derives.allI
  have ht' : Derives (Context.image Formula.raise Γ) (total p (paramsUp ρ) a.castSucc) := by
    simpa only [Formula.raise, total_rename] using Derives.rename Fin.castSucc ht
  apply Derives.impI
  apply fiber_value
  exact .impE (add (specialize_total p (paramsUp ρ) a.castSucc (Fin.last m) ht') _) (.hyp (Or.inl rfl))

/-- 从两个实际闭模式实例，构造存在的精确像集合。 -/
theorem image_exists {n m} {Γ : Context m} (p : Formula (n+2)) (ρ : Fin n → Fin m) (a : Fin m)
    (hc : Derives Γ ((CollectionSyntax.collection p).rename Fin.elim0))
    (hs : Derives Γ ((Source.SetLanguage.separation (imageMatrix p)).rename Fin.elim0))
    (ht : Derives Γ (total p ρ a)) : Derives Γ (imageExists p ρ a) := by
  have hcol : Derives Γ (collects p ρ a) :=
    .impE (collection_instance p ρ a hc) (total_relation p ρ a ht)
  let W : Formula (m+1) := covered p (paramsUp ρ) a.castSucc (Fin.last m)
  let Γw := Context.add W (Context.image Formula.raise Γ)
  change Derives Γ (.ex W) at hcol
  apply Derives.exE (p := W) hcol
  have hcase : Derives Γw (imageExists p (paramsUp ρ) a.castSucc) := by
    have ht' : Derives Γw (total p (paramsUp ρ) a.castSucc) := by
      simpa only [Formula.raise, total_rename] using under ht W
    have hb : Derives Γw W := .hyp (Or.inl rfl)
    have hs' : Derives Γw ((Source.SetLanguage.separation (imageMatrix p)).rename Fin.elim0) := by
      simpa only [Formula.raise, closed_rename] using under hs W
    have hsep := separation_instance p (paramsUp ρ) a.castSucc (Fin.last m) hs'
    let C : Formula (m+2) := separated p (paramsUp (paramsUp ρ)) a.castSucc.castSucc
      (Fin.last m).castSucc (Fin.last (m+1))
    let Γc := Context.add C (Context.image Formula.raise Γw)
    change Derives Γw (.ex C) at hsep
    apply Derives.exE (p := C) hsep
    have ht'' : Derives Γc (total p (paramsUp (paramsUp ρ)) a.castSucc.castSucc) := by
      simpa only [Formula.raise, total_rename] using under ht' C
    have hb' : Derives Γc (covered p (paramsUp (paramsUp ρ)) a.castSucc.castSucc (Fin.last m).castSucc) := by
      simpa only [Formula.raise, W, covered_rename] using under hb C
    have hs'' : Derives Γc C := .hyp (Or.inl rfl)
    have hexact := ExactImage.exact_image p (paramsUp (paramsUp ρ)) a.castSucc.castSucc
      (Fin.last m).castSucc (Fin.last (m+1)) ht'' hb' hs''
    have himage : Derives Γc (imageExists p (paramsUp (paramsUp ρ)) a.castSucc.castSucc) := by
      apply Derives.exI (Fin.last (m+1))
      simpa only [Formula.instantiate, exactImage_rename, paramsUp,
        Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hexact
    simpa only [Formula.raise, imageExists_rename] using himage
  simpa only [Formula.raise, imageExists_rename] using hcase

def assumptions {n} (p : Formula (n+2)) : Theory := fun q =>
  q = CollectionSyntax.collection p ∨ q = Source.SetLanguage.separation (imageMatrix p)

/-- 原19规则中的完整闭句证书，只用一个Collection实例与一个Separation实例。 -/
theorem source_replacement {n} (p : Formula (n+2)) :
    Derives ((assumptions p).at 0) (Source.SetLanguage.replacement p) := by
  rw [replacement_original]
  apply close_derives
  apply Derives.allI
  rw [theory_at_raise]
  apply Derives.impI
  have hc : Derives ((assumptions p).at (n+1)) ((CollectionSyntax.collection p).rename Fin.elim0) :=
    .hyp ⟨_, Or.inl rfl, rfl⟩
  have hs : Derives ((assumptions p).at (n+1))
      ((Source.SetLanguage.separation (imageMatrix p)).rename Fin.elim0) :=
    .hyp ⟨_, Or.inr rfl, rfl⟩
  exact image_exists p Fin.castSucc (Fin.last n) (add hc _) (add hs _) (.hyp (Or.inl rfl))

/-- 两个闭模式实例已足够；这是不依赖原ZF固定句子证书的原核逻辑证书。 -/
theorem kernel_certificate {n} (p : Formula (n+2)) :
    YesMetaZFC.Logic.FirstOrder.Derives (TheoryTransport.theory (assumptions p)) []
      (Translation.sentence (Source.SetLanguage.replacement p)) :=
  TheoryTransport.sentence (source_replacement p)

/-- 最终输出原Hilbert核对象推导；没有将Replacement作为输入公理。 -/
theorem native_replacement {n} (p : Formula (n+2)) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (Source.SetLanguage.replacement p)) := by
  apply YesMetaZFC.Logic.FirstOrder.Derives.theory_cut (hFormula := kernel_certificate p)
  rintro q ⟨r, hr, rfl⟩
  rcases hr with rfl | rfl
  · exact CollectionSyntax.source_collection p
  · exact SeparationSyntax.source_separation (imageMatrix p)
end PPAC.Migration.ReplacementFromCollection
