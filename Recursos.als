/*
Tipos de relação

    some: pelo menos 1
    one: exatamente 1
    lone: 0 ou 1
    set: conjunto ilimitado
*/

sig Local {
    recursos: set Recurso,
    usuarios: set Usuario
}

sig Recurso {
    superior: lone Recurso
}

sig Usuario {
    acessa: set Recurso
}

fact "restricoes" {
    // Para todo usuário, existe somente um local no qual ele está
    all u: Usuario | one l: Local | u in l.usuarios

    // Para todo recurso existe somente um local no qual ele está
    all r: Recurso | one l: Local | r in l.recursos

    // Para todo recurso r, r não é superior de si nem de nenhum superior a ele
    all r: Recurso | r not in r.^superior

    // Todo usuario que acessa um recurso, acessa também os seus inferiores
    all u: Usuario, r: Recurso | r in u.acessa implies inferiores[r] in u.acessa
}

fun inferiores[r: Recurso]: set Recurso {
    {r1: Recurso | r1.*superior = r}
}

assert recursoNaoCompartilha {
    !(some r: Recurso | #(recursos.r) > 1)
}

check recursoNaoCompartilha

// for 5: define que todos os conjuntos têm no máximo 5 objetos
run{} for 5 but exactly 2 Local