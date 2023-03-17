module Dreadbury

abstract sig Person {
    killed: set Person,
    hates: set Person,
    richer: set Person
}

one sig Agatha, Butler, Charles extends Person {}

fact someoneKilledAgatha {
    some killed.Agatha
}

fact someoneKilledAgatha_ALT {
    Agatha in Person.killed
}

run {} for 3
