module Dreadbury

abstract sig Person {
  killed: set Person,
  hates: set Person,
  richer: set Person
}

one sig Agatha, Butler, Charles extends Person {}

pred encoding {
  some killed.Agatha
  killed in hates and no (killed & richer)
  no (Charles.hates & Agatha.hates)
  (Person - Butler) in Agatha.hates
  (Person - richer.Agatha) in Butler.hates
  Agatha.hates in Butler.hates
  all x : Person | Person != x.hates
}

pred encoding_ALT {
  some x : Person | Agatha in x.killed
  all x, y : Person | y in x.killed implies (y in x.hates and y not in x.richer)
  all x : Person | x in Agatha.hates implies x not in Charles.hates
  Agatha in Agatha.hates and Charles in Agatha.hates
  all x : Person | Agatha not in x.richer implies x in Butler.hates
  all x : Person | x in Agatha.hates implies x in  Butler.hates
  all x : Person | some y : Person | y not in x.hates
}

run encoding for 3
run encoding_ALT for 3
