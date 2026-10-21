import PPAC.Migration.OmegaCut

/-! 原Infinity见证及实际分离取得最小归纳集ω，输出对象存在句子。 -/
namespace PPAC.Migration.OmegaExistence
open Source SourceAlgebra SourceLogic OmegaSyntax

theorem exists_omega {m} {Γ : Context m}
    (hi : Derives Γ (Source.SetLanguage.infinity.rename Fin.elim0))
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hs : Derives Γ ((Source.SetLanguage.separation matrix).rename Fin.elim0)) :
    Derives Γ (omegaExists.rename Fin.elim0) := by
  have hI := infinity_at hi
  let I := isInductive (Fin.last m)
  let Γi := Context.add I (Context.image Formula.raise Γ)
  change Derives Γ (.ex I) at hI
  apply Derives.exE (p := I) hI
  have resultI : Derives Γi (omegaExists.rename Fin.elim0) := by
    have hiI : Derives Γi I := .hyp (Or.inl rfl)
    have heI : Derives Γi (Source.SetLanguage.extensionality.rename Fin.elim0) := by
      simpa only [Formula.raise, closed_rename] using under he I
    have hsI : Derives Γi ((Source.SetLanguage.separation matrix).rename Fin.elim0) := by
      simpa only [Formula.raise, closed_rename] using under hs I
    have hW := separate_cut (Fin.last m) hsI
    let W := cut (Fin.last (m+1)) (Fin.last m).castSucc
    let Γw := Context.add W (Context.image Formula.raise Γi)
    change Derives Γi (.ex W) at hW
    apply Derives.exE (p := W) hW
    have heW : Derives Γw (Source.SetLanguage.extensionality.rename Fin.elim0) := by
      simpa only [Formula.raise, closed_rename] using under heI W
    have hiW : Derives Γw (isInductive (Fin.last m).castSucc) := by
      simpa only [Formula.raise, I, isInductive_rename] using under hiI W
    have hcW : Derives Γw W := .hyp (Or.inl rfl)
    have hw := OmegaCut.from_cut (Fin.last (m+1)) (Fin.last m).castSucc heW hiW hcW
    have ho : Derives Γw (omegaExists.rename Fin.elim0) := by
      rw [omegaExists_at]
      apply Derives.exI (Fin.last (m+1))
      simpa only [Formula.instantiate, omega_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hw
    simpa only [Formula.raise, closed_rename] using ho
  simpa only [Formula.raise, closed_rename] using resultI
end PPAC.Migration.OmegaExistence
