Exists
: ∀(A: *) ∀(B: ∀(a: A) *) *
= λA λB
  $self
  ∀(P: ∀(s: (Exists A B)) *)
  ∀(i: ∀(a: A) ∀(b: (B a)) (P (indeed A B a b)))
  (P self)
