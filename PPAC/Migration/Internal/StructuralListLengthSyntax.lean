import PPAC.Migration.Internal.ObjectStructuralListTrace

/-! 长度关系仍有实际完整轨迹见证；比较性质只量化两个对象候选长度。 -/
namespace PPAC.Migration.Internal.StructuralListLengthSyntax
open Source SourceAlgebra SourceLogic OmegaSyntax StructuralListTraceSyntax

def lengthBody {m} (w n l : Fin m) : Formula (m+4) := trace w.castSucc.castSucc.castSucc.castSucc
  (Fin.last m).castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc l.castSucc.castSucc.castSucc.castSucc
  (Fin.last (m+2)).castSucc (Fin.last (m+3)) n.castSucc.castSucc.castSucc.castSucc
def hasLength {m} (w n l : Fin m) : Formula m := .ex (.ex (.ex (.ex (lengthBody w n l))))
def predecessorLength {m} (w t l : Fin m) : Formula m := .ex
  (((Formula.mem (Fin.last m) w.castSucc).conj (successor l.castSucc (Fin.last m))).conj (hasLength w.castSucc t.castSucc (Fin.last m)))
def property {m} (w n : Fin m) : Formula m := .all (.all
  ((hasLength w.castSucc.castSucc n.castSucc.castSucc (Fin.last m).castSucc).imp
    ((hasLength w.castSucc.castSucc n.castSucc.castSucc (Fin.last (m+1))).imp (.equal (Fin.last m).castSucc (Fin.last (m+1))))))
def matrix : Formula 2 := property 0 1
def existsLength {m} (w n : Fin m) : Formula m := .ex
  ((Formula.mem (Fin.last m) w.castSucc).conj (hasLength w.castSucc n.castSucc (Fin.last m)))
def fiber {m} (w n : Fin m) : Formula m := .ex
  (((Formula.mem (Fin.last m) w.castSucc).conj (hasLength w.castSucc n.castSucc (Fin.last m))).conj (.all
    ((hasLength w.castSucc.castSucc n.castSucc.castSucc (Fin.last (m+1))).imp (.equal (Fin.last (m+1)) (Fin.last m).castSucc))))

theorem hasLength_rename {m k} (w n l : Fin m) (r : Fin m → Fin k) : (hasLength w n l).rename r = hasLength (r w) (r n) (r l) := by
  simp only [hasLength, lengthBody, Formula.rename, trace_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]
theorem predecessorLength_rename {m k} (w t l : Fin m) (r : Fin m → Fin k) :
    (predecessorLength w t l).rename r = predecessorLength (r w) (r t) (r l) := by
  simp only [predecessorLength, Formula.rename, successor_rename, hasLength_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]
theorem property_rename {m k} (w n : Fin m) (r : Fin m → Fin k) : (property w n).rename r = property (r w) (r n) := by
  simp only [property, Formula.rename, hasLength_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]
theorem existsLength_rename {m k} (w n : Fin m) (r : Fin m → Fin k) : (existsLength w n).rename r = existsLength (r w) (r n) := by
  simp only [existsLength, Formula.rename, hasLength_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]
theorem fiber_rename {m k} (w n : Fin m) (r : Fin m → Fin k) : (fiber w n).rename r = fiber (r w) (r n) := by
  simp only [fiber, Formula.rename, hasLength_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]
theorem matrix_pred {m} (ρ : Fin 1 → Fin m) (x : Fin m) : MinimalPredicates.pred matrix ρ x = property (ρ 0) x := by
  have h0 : Fin.lastCases x ρ (0 : Fin 2) = ρ 0 := by
    change Fin.lastCases x ρ (0 : Fin 1).castSucc = ρ 0
    exact Fin.lastCases_castSucc _
  have h1 : Fin.lastCases x ρ (1 : Fin 2) = x := by
    change Fin.lastCases x ρ (Fin.last 1) = x
    exact Fin.lastCases_last
  simp only [MinimalPredicates.pred, matrix, property_rename, h0, h1]

theorem intro_length {m} {Γ : Context m} (w n l z e d f : Fin m) (ht : Derives Γ (trace w z e l d f n)) : Derives Γ (hasLength w n l) := by
  apply Derives.exI z
  apply Derives.exI e
  apply Derives.exI d
  apply Derives.exI f
  simpa only [Formula.instantiate, lengthBody, Formula.rename, trace_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using ht

theorem eliminate_length {m} {Γ : Context m} (w n l : Fin m) (r : Formula m) (hl : Derives Γ (hasLength w n l))
    (hc : Derives (Context.add (lengthBody w n l) (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise Γ))))) r.raise.raise.raise.raise) : Derives Γ r := by
  change Derives Γ (.ex (.ex (.ex (.ex _)))) at hl
  apply Derives.exE hl
  apply Derives.exE (.hyp (Or.inl rfl))
  apply Derives.exE (.hyp (Or.inl rfl))
  apply Derives.exE (.hyp (Or.inl rfl))
  refine Derives.weaken ?_ hc
  rintro r (hr | ⟨s, ⟨t, ⟨u, hu, h1⟩, h2⟩, h3⟩)
  · exact Or.inl hr
  · exact Or.inr ⟨s, Or.inr ⟨t, Or.inr ⟨u, Or.inr hu, h1⟩, h2⟩, h3⟩

theorem under_four {m} {Γ : Context m} {r : Formula m} (hr : Derives Γ r) (b : Formula (m+4)) :
    Derives (Context.add b (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise Γ))))) r.raise.raise.raise.raise :=
  add (Derives.rename Fin.castSucc (Derives.rename Fin.castSucc (Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hr)))) b

theorem zf_under_four {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (b : Formula (m+4)) :
    ZFContext.Evidence (Context.add b (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise Γ))))) :=
  ZFContext.add (ZFContext.rename (ZFContext.rename (ZFContext.rename (ZFContext.rename hZ Fin.castSucc) Fin.castSucc) Fin.castSucc) Fin.castSucc) b

theorem intro_predecessor {m} {Γ : Context m} (w t l p : Fin m) (hp : Derives Γ (.mem p w))
    (hs : Derives Γ (successor l p)) (hl : Derives Γ (hasLength w t p)) : Derives Γ (predecessorLength w t l) := by
  apply Derives.exI p
  simp only [Formula.instantiate, Formula.rename, successor_rename, hasLength_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact .conjI (.conjI hp hs) hl

theorem property_at {m} {Γ : Context m} (w n l k : Fin m) (hp : Derives Γ (property w n))
    (hl : Derives Γ (hasLength w n l)) (hk : Derives Γ (hasLength w n k)) : Derives Γ (.equal l k) := by
  have h1 : Derives Γ (.all ((hasLength w.castSucc n.castSucc l.castSucc).imp
      ((hasLength w.castSucc n.castSucc (Fin.last m)).imp (.equal l.castSucc (Fin.last m))))) := by
    simpa only [property, Formula.instantiate, Formula.rename, hasLength_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using Derives.allE l hp
  have h2 : Derives Γ ((hasLength w n l).imp ((hasLength w n k).imp (.equal l k))) := by
    simpa only [Formula.instantiate, Formula.rename, hasLength_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using Derives.allE k h1
  exact .impE (.impE h2 hl) hk
end PPAC.Migration.Internal.StructuralListLengthSyntax
