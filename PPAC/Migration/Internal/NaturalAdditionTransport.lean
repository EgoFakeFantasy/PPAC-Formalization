import PPAC.Migration.Internal.ObjectNaturalMultiplication

/-! 算术等词传输及有限参数映射；均由原eqSubst/rename构造证书。 -/
namespace PPAC.Migration.Internal.NaturalAdditionTransport
open Source SourceAlgebra SourceLogic OmegaSyntax NaturalAdditionSyntax

def params3 {m} (w a b : Fin m) : Fin 3 → Fin m := Fin.lastCases b (Source.SetLanguage.args2 w a)
theorem params3_0 {m} (w a b : Fin m) : params3 w a b 0 = w := by
  change Fin.lastCases b (Source.SetLanguage.args2 w a) (0 : Fin 2).castSucc = w
  simp only [Fin.lastCases_castSucc, PairSyntax.args2_first]
theorem params3_1 {m} (w a b : Fin m) : params3 w a b 1 = a := by
  change Fin.lastCases b (Source.SetLanguage.args2 w a) (1 : Fin 2).castSucc = a
  simp only [Fin.lastCases_castSucc, PairSyntax.args2_second]
theorem params3_2 {m} (w a b : Fin m) : params3 w a b 2 = b := by
  change Fin.lastCases b (Source.SetLanguage.args2 w a) (Fin.last 2) = b
  exact Fin.lastCases_last

theorem left_subst {m} {Γ : Context m} (w a b n y : Fin m) (he : Derives Γ (.equal a b))
    (hy : Derives Γ (sum w a n y)) : Derives Γ (sum w b n y) := by
  have hi : Derives Γ ((sum w.castSucc (Fin.last m) n.castSucc y.castSucc).instantiate a) := by
    simpa only [Formula.instantiate, sum_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hy
  have ho := Derives.eqSubst (sum w.castSucc (Fin.last m) n.castSucc y.castSucc) he hi
  simpa only [Formula.instantiate, sum_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using ho

theorem index_subst {m} {Γ : Context m} (w a n s y : Fin m) (he : Derives Γ (.equal n s))
    (hy : Derives Γ (sum w a n y)) : Derives Γ (sum w a s y) := by
  have hi : Derives Γ ((sum w.castSucc a.castSucc (Fin.last m) y.castSucc).instantiate n) := by
    simpa only [Formula.instantiate, sum_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hy
  have ho := Derives.eqSubst (sum w.castSucc a.castSucc (Fin.last m) y.castSucc) he hi
  simpa only [Formula.instantiate, sum_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using ho

theorem successor_input_subst {m} {Γ : Context m} (z x y : Fin m) (he : Derives Γ (.equal x y))
    (hz : Derives Γ (successor z x)) : Derives Γ (successor z y) := by
  have hi : Derives Γ ((successor z.castSucc (Fin.last m)).instantiate x) := by
    simpa only [Formula.instantiate, successor_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hz
  have ho := Derives.eqSubst (successor z.castSucc (Fin.last m)) he hi
  simpa only [Formula.instantiate, successor_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using ho

def params4 {m} (w a b u : Fin m) : Fin 4 → Fin m := Fin.lastCases u (params3 w a b)
theorem params4_0 {m} (w a b u : Fin m) : params4 w a b u 0 = w := by
  change Fin.lastCases u (params3 w a b) (0 : Fin 3).castSucc = w
  simp only [Fin.lastCases_castSucc, params3_0]
theorem params4_1 {m} (w a b u : Fin m) : params4 w a b u 1 = a := by
  change Fin.lastCases u (params3 w a b) (1 : Fin 3).castSucc = a
  simp only [Fin.lastCases_castSucc, params3_1]
theorem params4_2 {m} (w a b u : Fin m) : params4 w a b u 2 = b := by
  change Fin.lastCases u (params3 w a b) (2 : Fin 3).castSucc = b
  simp only [Fin.lastCases_castSucc, params3_2]
theorem params4_3 {m} (w a b u : Fin m) : params4 w a b u 3 = u := by
  change Fin.lastCases u (params3 w a b) (Fin.last 3) = u
  exact Fin.lastCases_last
end PPAC.Migration.Internal.NaturalAdditionTransport
