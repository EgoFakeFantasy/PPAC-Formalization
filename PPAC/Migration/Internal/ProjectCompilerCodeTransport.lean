import PPAC.Migration.Internal.ProjectCompilerCodeSyntax

/-! Actual compiler set recursion or guarded output relation; output correctness and functionality remain unproved. -/
namespace PPAC.Migration.Internal.ProjectCompilerCodeTransport
open Source SourceAlgebra SourceLogic ProjectCompilerJudgmentSyntax ProjectCompilerCodeSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem atCarrier_omega {m} {Γ : Context m} (w c n b f t : Fin m) (he : Derives Γ (.equal w t))
    (ht : Derives Γ (atCarrier w c n b f)) : Derives Γ (atCarrier t c n b f) := by
  have hi : Derives Γ ((atCarrier (Fin.last m) c.castSucc n.castSucc b.castSucc f.castSucc).instantiate w) := by
    simpa only [Formula.instantiate, atCarrier_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using ht
  have ho := Derives.eqSubst (atCarrier (Fin.last m) c.castSucc n.castSucc b.castSucc f.castSucc) he hi
  simpa only [Formula.instantiate, atCarrier_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using ho

theorem atCarrier_carrier {m} {Γ : Context m} (w c n b f t : Fin m) (he : Derives Γ (.equal c t))
    (ht : Derives Γ (atCarrier w c n b f)) : Derives Γ (atCarrier w t n b f) := by
  have hi : Derives Γ ((atCarrier w.castSucc (Fin.last m) n.castSucc b.castSucc f.castSucc).instantiate c) := by
    simpa only [Formula.instantiate, atCarrier_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using ht
  have ho := Derives.eqSubst (atCarrier w.castSucc (Fin.last m) n.castSucc b.castSucc f.castSucc) he hi
  simpa only [Formula.instantiate, atCarrier_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using ho

theorem atCarrier_root {m} {Γ : Context m} (w c n b f t : Fin m) (he : Derives Γ (.equal n t))
    (ht : Derives Γ (atCarrier w c n b f)) : Derives Γ (atCarrier w c t b f) := by
  have hi : Derives Γ ((atCarrier w.castSucc c.castSucc (Fin.last m) b.castSucc f.castSucc).instantiate n) := by
    simpa only [Formula.instantiate, atCarrier_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using ht
  have ho := Derives.eqSubst (atCarrier w.castSucc c.castSucc (Fin.last m) b.castSucc f.castSucc) he hi
  simpa only [Formula.instantiate, atCarrier_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using ho

theorem atCarrier_bound {m} {Γ : Context m} (w c n b f t : Fin m) (he : Derives Γ (.equal b t))
    (ht : Derives Γ (atCarrier w c n b f)) : Derives Γ (atCarrier w c n t f) := by
  have hi : Derives Γ ((atCarrier w.castSucc c.castSucc n.castSucc (Fin.last m) f.castSucc).instantiate b) := by
    simpa only [Formula.instantiate, atCarrier_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using ht
  have ho := Derives.eqSubst (atCarrier w.castSucc c.castSucc n.castSucc (Fin.last m) f.castSucc) he hi
  simpa only [Formula.instantiate, atCarrier_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using ho

theorem atCarrier_free {m} {Γ : Context m} (w c n b f t : Fin m) (he : Derives Γ (.equal f t))
    (ht : Derives Γ (atCarrier w c n b f)) : Derives Γ (atCarrier w c n b t) := by
  have hi : Derives Γ ((atCarrier w.castSucc c.castSucc n.castSucc b.castSucc (Fin.last m)).instantiate f) := by
    simpa only [Formula.instantiate, atCarrier_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using ht
  have ho := Derives.eqSubst (atCarrier w.castSucc c.castSucc n.castSucc b.castSucc (Fin.last m)) he hi
  simpa only [Formula.instantiate, atCarrier_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using ho

theorem code_omega {m} {Γ : Context m} (w n b f t : Fin m) (he : Derives Γ (.equal w t))
    (ht : Derives Γ (compiled w n b f)) : Derives Γ (compiled t n b f) := by
  have hi : Derives Γ ((compiled (Fin.last m) n.castSucc b.castSucc f.castSucc).instantiate w) := by
    simpa only [Formula.instantiate, compiled_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using ht
  have ho := Derives.eqSubst (compiled (Fin.last m) n.castSucc b.castSucc f.castSucc) he hi
  simpa only [Formula.instantiate, compiled_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using ho

theorem code_root {m} {Γ : Context m} (w n b f t : Fin m) (he : Derives Γ (.equal n t))
    (ht : Derives Γ (compiled w n b f)) : Derives Γ (compiled w t b f) := by
  have hi : Derives Γ ((compiled w.castSucc (Fin.last m) b.castSucc f.castSucc).instantiate n) := by
    simpa only [Formula.instantiate, compiled_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using ht
  have ho := Derives.eqSubst (compiled w.castSucc (Fin.last m) b.castSucc f.castSucc) he hi
  simpa only [Formula.instantiate, compiled_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using ho

theorem code_bound {m} {Γ : Context m} (w n b f t : Fin m) (he : Derives Γ (.equal b t))
    (ht : Derives Γ (compiled w n b f)) : Derives Γ (compiled w n t f) := by
  have hi : Derives Γ ((compiled w.castSucc n.castSucc (Fin.last m) f.castSucc).instantiate b) := by
    simpa only [Formula.instantiate, compiled_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using ht
  have ho := Derives.eqSubst (compiled w.castSucc n.castSucc (Fin.last m) f.castSucc) he hi
  simpa only [Formula.instantiate, compiled_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using ho

theorem code_free {m} {Γ : Context m} (w n b f t : Fin m) (he : Derives Γ (.equal f t))
    (ht : Derives Γ (compiled w n b f)) : Derives Γ (compiled w n b t) := by
  have hi : Derives Γ ((compiled w.castSucc n.castSucc b.castSucc (Fin.last m)).instantiate f) := by
    simpa only [Formula.instantiate, compiled_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using ht
  have ho := Derives.eqSubst (compiled w.castSucc n.castSucc b.castSucc (Fin.last m)) he hi
  simpa only [Formula.instantiate, compiled_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using ho
end PPAC.Migration.Internal.ProjectCompilerCodeTransport
