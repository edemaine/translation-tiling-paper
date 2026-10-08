def Connected (P : Prototile) : Prop :=
  ∀ p ∈ P, ∀ q ∈ P, Relation.ReflTransGen (fun a b => a ∈ P ∧ b ∈ P ∧ Adjacent a b) p q
