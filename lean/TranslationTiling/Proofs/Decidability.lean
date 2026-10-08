import TranslationTiling.Proofs.FiniteSearch

namespace TranslationTiling

/-- Effective positive certificates and finite obstruction search give a
total decision procedure. Planar certificates are constructed in
`Proofs.PeriodicCertificates`. -/
theorem decidability_of_certificates {d : ℕ} (certificate : Tile d → ℕ → Prop)
    (hc : ComputablePred fun z : Tile d × ℕ => certificate z.1 z.2)
    (correct : ∀ F, Tiles F ↔ ∃ n, certificate F n) : ComputablePred (@Tiles d) := by
  apply ComputablePred.computable_iff_re_compl_re'.mpr
  exact ⟨(LeanWang.REPred.exists_nat hc).of_eq (fun F => (correct F).symm), tiles_coRE d⟩

end TranslationTiling
