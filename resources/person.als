module Dreadbury

abstract sig Person {
    killed: set Person,
    hates: set Person,
    richer: set Person
}

one sig Agatha, Butler, Charles extends Person {}

pred someoneKilledAgatha {
    some killed.Agatha
}

pred someoneKilledAgatha_ALT {
    Agatha in Person.killed
}

run {not (someoneKilledAgatha iff someoneKilledAgatha_ALT)} for 3
