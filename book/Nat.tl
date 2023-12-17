Nat
: *
= $self
  ∀(P: ∀(n: Nat) *)
  ∀(s: ∀(i: Nat) (P (succ i)))
  ∀(z: (P zero))
  (P self)
