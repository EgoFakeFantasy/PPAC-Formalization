import PPAC.Migration.Internal.PacketAffineSyntax

/-! Pure object equality transport for the affine packet arithmetic. -/
namespace PPAC.Migration.Internal.PacketAffineTransport
open Source SourceAlgebra SourceLogic PacketAffineSyntax

theorem sum_right {m} {Γ : Context m} (w a b n u : Fin m) (he : Derives Γ (.equal b u))
    (hc : Derives Γ (NaturalAdditionSyntax.sum w a b n)) : Derives Γ (NaturalAdditionSyntax.sum w a u n) := by
  have hi : Derives Γ ((NaturalAdditionSyntax.sum w.castSucc a.castSucc (Fin.last m) n.castSucc).instantiate b) := by
    simpa only [Formula.instantiate, NaturalAdditionSyntax.sum_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hc
  have ho := Derives.eqSubst (NaturalAdditionSyntax.sum w.castSucc a.castSucc (Fin.last m) n.castSucc) he hi
  simpa only [Formula.instantiate, NaturalAdditionSyntax.sum_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using ho

theorem radix {m} {Γ : Context m} (w B d t n u : Fin m) (he : Derives Γ (.equal B u))
    (hc : Derives Γ (affine w B d t n)) : Derives Γ (affine w u d t n) := by
  have hi : Derives Γ ((affine w.castSucc (Fin.last m) d.castSucc t.castSucc n.castSucc).instantiate B) := by
    simpa only [Formula.instantiate, affine_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hc
  have ho := Derives.eqSubst (affine w.castSucc (Fin.last m) d.castSucc t.castSucc n.castSucc) he hi
  simpa only [Formula.instantiate, affine_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using ho

theorem digit {m} {Γ : Context m} (w B d t n u : Fin m) (he : Derives Γ (.equal d u))
    (hc : Derives Γ (affine w B d t n)) : Derives Γ (affine w B u t n) := by
  have hi : Derives Γ ((affine w.castSucc B.castSucc (Fin.last m) t.castSucc n.castSucc).instantiate d) := by
    simpa only [Formula.instantiate, affine_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hc
  have ho := Derives.eqSubst (affine w.castSucc B.castSucc (Fin.last m) t.castSucc n.castSucc) he hi
  simpa only [Formula.instantiate, affine_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using ho

theorem tail {m} {Γ : Context m} (w B d t n u : Fin m) (he : Derives Γ (.equal t u))
    (hc : Derives Γ (affine w B d t n)) : Derives Γ (affine w B d u n) := by
  have hi : Derives Γ ((affine w.castSucc B.castSucc d.castSucc (Fin.last m) n.castSucc).instantiate t) := by
    simpa only [Formula.instantiate, affine_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hc
  have ho := Derives.eqSubst (affine w.castSucc B.castSucc d.castSucc (Fin.last m) n.castSucc) he hi
  simpa only [Formula.instantiate, affine_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using ho

theorem output {m} {Γ : Context m} (w B d t n u : Fin m) (he : Derives Γ (.equal n u))
    (hc : Derives Γ (affine w B d t n)) : Derives Γ (affine w B d t u) := by
  have hi : Derives Γ ((affine w.castSucc B.castSucc d.castSucc t.castSucc (Fin.last m)).instantiate n) := by
    simpa only [Formula.instantiate, affine_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hc
  have ho := Derives.eqSubst (affine w.castSucc B.castSucc d.castSucc t.castSucc (Fin.last m)) he hi
  simpa only [Formula.instantiate, affine_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using ho

end PPAC.Migration.Internal.PacketAffineTransport
