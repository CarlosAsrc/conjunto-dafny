class {:autocontracts} Conjunto
{
    //Abstração
    ghost var Elementos: array<nat>;
    //Implementação
    var elementos: array<nat>;

    constructor ()
    ensures Elementos == []
    {
        elementos := new nat[5];
        Elementos := [];
    }


   method Adicionar(x:nat) returns (r:bool)
    {

    }

    method Remover(x:nat) returns (r:bool)
    {

    }

    method Pertence(x:nat) returns (r:bool)
    {

    }

    method Tamanho() returns (r:nat)
    {

    }

    method Vazio() returns (r:bool)
    {

    }
}




method main()
{

}