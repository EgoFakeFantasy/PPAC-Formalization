import PPAC.Migration.Internal.NaturalMultiplicationStep

/-! 乘法实际存在量化内部零初值和递推图，不固定宿主零对象。 -/
namespace PPAC.Migration.Internal.NaturalMultiplicationSyntax
open Source SourceAlgebra SourceLogic GraphSyntax OmegaSyntax ReplacementPredicates

def params {m} (w a : Fin m) : Fin 2 → Fin m := Source.SetLanguage.args2 w a

theorem params_0 {m} (w a : Fin m) : params w a 0 = w := rfl
theorem params_1 {m} (w a : Fin m) : params w a 1 = a := rfl
theorem params_rename {m k} (w a : Fin m) (r : Fin m → Fin k) : (fun i => r (params w a i)) = params (r w) (r a) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · have hj : j = 0 := Subsingleton.elim _ _
    subst j
    rfl

def product {m} (w a n y : Fin m) : Formula m := .ex
  ((empty (Fin.last m)).conj (NaturalEvaluationSyntax.evaluation NaturalMultiplicationStep.matrix (fun i => (params w a i).castSucc)
    w.castSucc (Fin.last m) n.castSucc y.castSucc))
def existsProduct {m} (w a n : Fin m) : Formula m := .ex
  ((Formula.mem (Fin.last m) w.castSucc).conj (product w.castSucc a.castSucc n.castSucc (Fin.last m)))
def fiber {m} (w a n : Fin m) : Formula m := .ex
  (((Formula.mem (Fin.last m) w.castSucc).conj (product w.castSucc a.castSucc n.castSucc (Fin.last m))).conj (.all
    ((product w.castSucc.castSucc a.castSucc.castSucc n.castSucc.castSucc (Fin.last (m+1))).imp
      (.equal (Fin.last (m+1)) (Fin.last m).castSucc))))

theorem product_rename {m k} (w a n y : Fin m) (r : Fin m → Fin k) :
    (product w a n y).rename r = product (r w) (r a) (r n) (r y) := by
  simp only [product, Formula.rename, empty_rename, NaturalEvaluationSyntax.evaluation_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]
  rw [← params_rename w a r]

theorem existsProduct_rename {m k} (w a n : Fin m) (r : Fin m → Fin k) :
    (existsProduct w a n).rename r = existsProduct (r w) (r a) (r n) := by
  simp only [existsProduct, Formula.rename, product_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem fiber_rename {m k} (w a n : Fin m) (r : Fin m → Fin k) :
    (fiber w a n).rename r = fiber (r w) (r a) (r n) := by
  simp only [fiber, Formula.rename, product_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem intro_product {m} {Γ : Context m} (w a n y e : Fin m) (he : Derives Γ (empty e))
    (hy : Derives Γ (NaturalEvaluationSyntax.evaluation NaturalMultiplicationStep.matrix (params w a) w e n y)) : Derives Γ (product w a n y) := by
  apply Derives.exI e
  simp only [Formula.instantiate, Formula.rename, empty_rename, NaturalEvaluationSyntax.evaluation_rename,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact .conjI he hy

theorem output_subst {m} {Γ : Context m} (w a n y z : Fin m)
    (he : Derives Γ (.equal y z)) (hy : Derives Γ (product w a n y)) : Derives Γ (product w a n z) := by
  have hi : Derives Γ ((product w.castSucc a.castSucc n.castSucc (Fin.last m)).instantiate y) := by
    simpa only [Formula.instantiate, product_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hy
  have hout := Derives.eqSubst (product w.castSucc a.castSucc n.castSucc (Fin.last m)) he hi
  simpa only [Formula.instantiate, product_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hout

theorem intro_exists {m} {Γ : Context m} (w a n y : Fin m) (hw : Derives Γ (.mem y w))
    (hy : Derives Γ (product w a n y)) : Derives Γ (existsProduct w a n) := by
  apply Derives.exI y
  simp only [Formula.instantiate, Formula.rename, product_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact .conjI hw hy

theorem initial_subst {n m} {Γ : Context m} (p : Formula (n+2)) (ρ : Fin n → Fin m) (w e f r y : Fin m)
    (he : Derives Γ (.equal e f)) (hy : Derives Γ (NaturalEvaluationSyntax.evaluation p ρ w e r y)) :
    Derives Γ (NaturalEvaluationSyntax.evaluation p ρ w f r y) := by
  have hi : Derives Γ ((NaturalEvaluationSyntax.evaluation p (paramsUp ρ) w.castSucc (Fin.last m) r.castSucc y.castSucc).instantiate e) := by
    simpa only [Formula.instantiate, NaturalEvaluationSyntax.evaluation_rename, paramsUp,
      Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hy
  have hout := Derives.eqSubst (NaturalEvaluationSyntax.evaluation p (paramsUp ρ) w.castSucc (Fin.last m) r.castSucc y.castSucc) he hi
  simpa only [Formula.instantiate, NaturalEvaluationSyntax.evaluation_rename, paramsUp,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hout
end PPAC.Migration.Internal.NaturalMultiplicationSyntax
