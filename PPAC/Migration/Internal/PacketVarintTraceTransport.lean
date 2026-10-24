import PPAC.Migration.Internal.PacketVarintTraceProperties

/-! Original equality substitution transports the independent fold graph. -/
namespace PPAC.Migration.Internal.PacketVarintTraceTransport
open Source SourceAlgebra SourceLogic PacketVarintTraceSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem input_subst {m} {Γ : Context m} (w C n t a x : Fin m) (he : Derives Γ (.equal n x))
    (hf : Derives Γ (foldAt w C n t a)) : Derives Γ (foldAt w C x t a) := by
  let P := foldAt w.castSucc C.castSucc (Fin.last m) t.castSucc a.castSucc
  have h0 : P.instantiate n = foldAt w C n t a := by simp only [P,Formula.instantiate,foldAt_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  have h1 : P.instantiate x = foldAt w C x t a := by simp only [P,Formula.instantiate,foldAt_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  exact of_eq h1 (Derives.eqSubst P he (of_eq h0.symm hf))

theorem output_subst {m} {Γ : Context m} (w C n t a x : Fin m) (he : Derives Γ (.equal a x))
    (hf : Derives Γ (foldAt w C n t a)) : Derives Γ (foldAt w C n t x) := by
  let P := foldAt w.castSucc C.castSucc n.castSucc t.castSucc (Fin.last m)
  have h0 : P.instantiate a = foldAt w C n t a := by simp only [P,Formula.instantiate,foldAt_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  have h1 : P.instantiate x = foldAt w C n t x := by simp only [P,Formula.instantiate,foldAt_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  exact of_eq h1 (Derives.eqSubst P he (of_eq h0.symm hf))

theorem radix_subst {m} {Γ : Context m} (w C n t a x : Fin m) (he : Derives Γ (.equal C x))
    (hf : Derives Γ (foldAt w C n t a)) : Derives Γ (foldAt w x n t a) := by
  let P := foldAt w.castSucc (Fin.last m) n.castSucc t.castSucc a.castSucc
  have h0 : P.instantiate C = foldAt w C n t a := by simp only [P,Formula.instantiate,foldAt_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  have h1 : P.instantiate x = foldAt w x n t a := by simp only [P,Formula.instantiate,foldAt_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  exact of_eq h1 (Derives.eqSubst P he (of_eq h0.symm hf))

end PPAC.Migration.Internal.PacketVarintTraceTransport
