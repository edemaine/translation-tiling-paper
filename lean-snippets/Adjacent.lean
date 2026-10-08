def Adjacent (a b : Point) : Prop :=
  |a.1 - b.1| + |a.2.1 - b.2.1| + |a.2.2 - b.2.2| = 1
