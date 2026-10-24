import PPAC.Migration.Internal.ProjectSourceCodeSyntax

/-! Typed的对象等词参数传输；不以宿主定义相等或选择改写内部载体。 -/
namespace PPAC.Migration.Internal.ProjectSourceCodeTransport
open Source SourceAlgebra SourceLogic ProjectSourceTypeJudgmentSyntax ProjectSourceCodeSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem typed_omega {m} {Γ : Context m} (w c n b f t : Fin m) (he : Derives Γ (.equal w t))
    (ht : Derives Γ (typed w c n b f)) : Derives Γ (typed t c n b f) := by
  have hi : Derives Γ ((typed (Fin.last m) c.castSucc n.castSucc b.castSucc f.castSucc).instantiate w) := by
    simpa only [Formula.instantiate, typed_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using ht
  have ho := Derives.eqSubst (typed (Fin.last m) c.castSucc n.castSucc b.castSucc f.castSucc) he hi
  simpa only [Formula.instantiate, typed_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using ho

theorem typed_carrier {m} {Γ : Context m} (w c n b f t : Fin m) (he : Derives Γ (.equal c t))
    (ht : Derives Γ (typed w c n b f)) : Derives Γ (typed w t n b f) := by
  have hi : Derives Γ ((typed w.castSucc (Fin.last m) n.castSucc b.castSucc f.castSucc).instantiate c) := by
    simpa only [Formula.instantiate, typed_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using ht
  have ho := Derives.eqSubst (typed w.castSucc (Fin.last m) n.castSucc b.castSucc f.castSucc) he hi
  simpa only [Formula.instantiate, typed_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using ho

theorem typed_root {m} {Γ : Context m} (w c n b f t : Fin m) (he : Derives Γ (.equal n t))
    (ht : Derives Γ (typed w c n b f)) : Derives Γ (typed w c t b f) := by
  have hi : Derives Γ ((typed w.castSucc c.castSucc (Fin.last m) b.castSucc f.castSucc).instantiate n) := by
    simpa only [Formula.instantiate, typed_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using ht
  have ho := Derives.eqSubst (typed w.castSucc c.castSucc (Fin.last m) b.castSucc f.castSucc) he hi
  simpa only [Formula.instantiate, typed_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using ho

theorem typed_bound {m} {Γ : Context m} (w c n b f t : Fin m) (he : Derives Γ (.equal b t))
    (ht : Derives Γ (typed w c n b f)) : Derives Γ (typed w c n t f) := by
  have hi : Derives Γ ((typed w.castSucc c.castSucc n.castSucc (Fin.last m) f.castSucc).instantiate b) := by
    simpa only [Formula.instantiate, typed_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using ht
  have ho := Derives.eqSubst (typed w.castSucc c.castSucc n.castSucc (Fin.last m) f.castSucc) he hi
  simpa only [Formula.instantiate, typed_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using ho

theorem typed_free {m} {Γ : Context m} (w c n b f t : Fin m) (he : Derives Γ (.equal f t))
    (ht : Derives Γ (typed w c n b f)) : Derives Γ (typed w c n b t) := by
  have hi : Derives Γ ((typed w.castSucc c.castSucc n.castSucc b.castSucc (Fin.last m)).instantiate f) := by
    simpa only [Formula.instantiate, typed_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using ht
  have ho := Derives.eqSubst (typed w.castSucc c.castSucc n.castSucc b.castSucc (Fin.last m)) he hi
  simpa only [Formula.instantiate, typed_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using ho

theorem code_omega {m} {Γ : Context m} (w n b f t : Fin m) (he : Derives Γ (.equal w t))
    (ht : Derives Γ (sourceCode w n b f)) : Derives Γ (sourceCode t n b f) := by
  have hi : Derives Γ ((sourceCode (Fin.last m) n.castSucc b.castSucc f.castSucc).instantiate w) := by
    simpa only [Formula.instantiate, sourceCode_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using ht
  have ho := Derives.eqSubst (sourceCode (Fin.last m) n.castSucc b.castSucc f.castSucc) he hi
  simpa only [Formula.instantiate, sourceCode_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using ho

theorem code_root {m} {Γ : Context m} (w n b f t : Fin m) (he : Derives Γ (.equal n t))
    (ht : Derives Γ (sourceCode w n b f)) : Derives Γ (sourceCode w t b f) := by
  have hi : Derives Γ ((sourceCode w.castSucc (Fin.last m) b.castSucc f.castSucc).instantiate n) := by
    simpa only [Formula.instantiate, sourceCode_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using ht
  have ho := Derives.eqSubst (sourceCode w.castSucc (Fin.last m) b.castSucc f.castSucc) he hi
  simpa only [Formula.instantiate, sourceCode_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using ho

theorem code_bound {m} {Γ : Context m} (w n b f t : Fin m) (he : Derives Γ (.equal b t))
    (ht : Derives Γ (sourceCode w n b f)) : Derives Γ (sourceCode w n t f) := by
  have hi : Derives Γ ((sourceCode w.castSucc n.castSucc (Fin.last m) f.castSucc).instantiate b) := by
    simpa only [Formula.instantiate, sourceCode_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using ht
  have ho := Derives.eqSubst (sourceCode w.castSucc n.castSucc (Fin.last m) f.castSucc) he hi
  simpa only [Formula.instantiate, sourceCode_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using ho

theorem code_free {m} {Γ : Context m} (w n b f t : Fin m) (he : Derives Γ (.equal f t))
    (ht : Derives Γ (sourceCode w n b f)) : Derives Γ (sourceCode w n b t) := by
  have hi : Derives Γ ((sourceCode w.castSucc n.castSucc b.castSucc (Fin.last m)).instantiate f) := by
    simpa only [Formula.instantiate, sourceCode_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using ht
  have ho := Derives.eqSubst (sourceCode w.castSucc n.castSucc b.castSucc (Fin.last m)) he hi
  simpa only [Formula.instantiate, sourceCode_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using ho
end PPAC.Migration.Internal.ProjectSourceCodeTransport
