import PPAC.Migration.Internal.SyntaxAtomSyntax

/-! 原子式见证的原exE消去、三槽提升及对象等词传输。 -/
namespace PPAC.Migration.Internal.SyntaxAtomLogic
open Source SourceAlgebra SourceLogic SyntaxAtomSyntax SyntaxTermSyntax

theorem under_three {m} {Γ : Context m} {p : Formula m} (hp : Derives Γ p) (q : Formula (m+3)) :
    Derives (Context.add q (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise Γ)))) p.raise.raise.raise :=
  .weaken (fun _ h => Or.inr h) (.rename Fin.castSucc (.rename Fin.castSucc (.rename Fin.castSucc hp)))

theorem zf_under_three {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (q : Formula (m+3)) :
    ZFContext.Evidence (Context.add q (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise Γ)))) :=
  ZFContext.add (ZFContext.rename (ZFContext.rename (ZFContext.rename hZ Fin.castSucc) Fin.castSucc) Fin.castSucc) q

theorem term_output_subst {m} {Γ : Context m} (w b f x y : Fin m) (he : Derives Γ (.equal x y))
    (ht : Derives Γ (term w b f x)) : Derives Γ (term w b f y) := by
  have hi : Derives Γ ((term w.castSucc b.castSucc f.castSucc (Fin.last m)).instantiate x) := by
    simpa only [Formula.instantiate, term_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using ht
  have ho := Derives.eqSubst (term w.castSucc b.castSucc f.castSucc (Fin.last m)) he hi
  simpa only [Formula.instantiate, term_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using ho

theorem zeroScalar_output_subst {m} {Γ : Context m} (w x y : Fin m) (he : Derives Γ (.equal x y))
    (ht : Derives Γ (zeroScalar w x)) : Derives Γ (zeroScalar w y) := by
  have hi : Derives Γ ((zeroScalar w.castSucc (Fin.last m)).instantiate x) := by
    simpa only [Formula.instantiate, zeroScalar_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using ht
  have ho := Derives.eqSubst (zeroScalar w.castSucc (Fin.last m)) he hi
  simpa only [Formula.instantiate, zeroScalar_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using ho

theorem intro_member {m} {Γ : Context m} (w b f s x y n : Fin m) (hd : Derives Γ (memberAt w b f s x y n)) : Derives Γ (membership w b f n) := by
  have hx : Derives Γ (term w b f x) := .conjL (.conjR (.conjL hd))
  apply Derives.conjI (Derives.conjL hx)
  apply Derives.exI s
  apply Derives.exI x
  apply Derives.exI y
  simpa only [memberBody, Formula.instantiate, memberAt_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hd

theorem intro_equality {m} {Γ : Context m} (w b f x y n : Fin m) (hd : Derives Γ (equalAt w b f x y n)) : Derives Γ (equality w b f n) := by
  have hx : Derives Γ (term w b f x) := .conjL (.conjL hd)
  apply Derives.conjI (Derives.conjL hx)
  apply Derives.exI x
  apply Derives.exI y
  simpa only [equalBody, Formula.instantiate, equalAt_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hd

theorem eliminate_member {m} {Γ : Context m} (w b f n : Fin m) (q : Formula m) (hm : Derives Γ (membership w b f n))
    (hc : Derives (Context.add (memberBody w b f n) (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise Γ)))) q.raise.raise.raise) : Derives Γ q := by
  apply Derives.exE (Derives.conjR hm)
  apply Derives.exE (.hyp (Or.inl rfl))
  apply Derives.exE (.hyp (Or.inl rfl))
  refine Derives.weaken ?_ hc
  rintro q (hq | ⟨s, ⟨t, ht, h1⟩, h2⟩)
  · exact Or.inl hq
  · exact Or.inr ⟨s, Or.inr ⟨t, Or.inr ht, h1⟩, h2⟩

theorem eliminate_equality {m} {Γ : Context m} (w b f n : Fin m) (q : Formula m) (hm : Derives Γ (equality w b f n))
    (hc : Derives (Context.add (equalBody w b f n) (Context.image Formula.raise (Context.image Formula.raise Γ))) q.raise.raise) : Derives Γ q := by
  apply Derives.exE (Derives.conjR hm)
  apply Derives.exE (.hyp (Or.inl rfl))
  refine Derives.weaken ?_ hc
  rintro q (hq | ⟨s, hs, he⟩)
  · exact Or.inl hq
  · exact Or.inr ⟨s, Or.inr hs, he⟩
end PPAC.Migration.Internal.SyntaxAtomLogic
