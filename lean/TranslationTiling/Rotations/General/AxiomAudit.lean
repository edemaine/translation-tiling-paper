import TranslationTiling.Rotations.General.Main
import Lean.Util.CollectAxioms

/-! Audit every declaration in the dimension-generic development, including
its transitive dependencies. No proof placeholders or extra axioms are allowed. -/
run_cmd do
  for (name, _) in (← Lean.getEnv).constants.toList do
    if name.toString.startsWith "TranslationTiling.Rotations.General." then
      let axioms ← Lean.collectAxioms name
      let extra := axioms.filter fun ax =>
        ax != ``propext && ax != ``Classical.choice && ax != ``Quot.sound
      unless extra.isEmpty do
        throwError "{name} depends on unexpected axioms: {extra}"
