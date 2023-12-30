cong
: ∀(A: *)
  ∀(B: *)
  ∀(a: A)
  ∀(b: A)
  ∀(f: ∀(x: A) B)
  ∀(e: (Equal A a b))
  (Equal B (f a) (f b))
= λA λB λa λb λf λe
  (e λx∀(P:∀(x:B) *)∀(h:(P (f a)))(P (f x)) λP λr r)

//- A = {a:*}
//- B = {b:*}
//- a = {c:a}
//- b = {d:a}
//- f = {e:∀(g:a) b}
//- e = {f:(Equal a c d)}
//NOTE: (?T) = ∀(g:∀(g:b) *) ∀(h:(g (e c))) (g (e d))
