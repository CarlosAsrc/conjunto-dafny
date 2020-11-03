/* TRABALHO 1: METODOS FORMAIS */
/*  INTEGRANTES
    * Carlos Rodrigues
    * Thiago Nitschke
*/


class {:autocontracts} Conjunto
{
    // Abstração do conjunto através de sequencia de naturais
    ghost var Conteudo: seq<nat>;
    // Implementação concreta do conjunto com array de naturais
    var elementos: array<nat>;
    // Variável que representa indice do ultimo elemento
    var tail: nat;

    // Invariante de classe para validar que em todos os cenários
    // os elementos da implementação concreta em array serão os mesmos
    // do conjunto abstrato representado por sequencia de naturais
    // bem como evita repetição no conjunto.
    predicate Valid()
    {
        // Garante que o tamanho alocado do array seja sempre maior que 0
        elementos.Length != 0
        // Garante que o indice do array esteja dentre as limitações do array
        && 0 <= tail <= elementos.Length
        // Garante que os elementos da implementação concreta seja igual aos
        // elementos da representação abstrata Conteudo
        && elementos[0..tail] == Conteudo
        // Garante que não há elementos repetidos na implementação concreta de array.
        && forall i,j :: 0 <= i < j < tail ==> elementos[i] != elementos[j]
    }

    // Construtor que recebe como parâmetro o tamanho inicial do
    // array de implementação concreta.
    // Garante a inicialização do conjunto vazio.
    constructor (tamanho:nat)
    requires tamanho > 0
    ensures elementos.Length == tamanho
    ensures Conteudo == []
    {
        elementos := new nat[tamanho];
        Conteudo := [];
        tail := 0;
    }

    // Adiciona elemento no conjunto
    method Adicionar(x:nat) returns (r:bool)
    // Garante que se o elemento não existia antes, o novo Conteudo
    // será acrescido com x, o tamanho de Conteudo acrescido em 1
    // a variavel tail acrescida em 1, e garante a resposta positiva
    // de adição do novo elemento.
    ensures !(x in old(Conteudo)) ==> (Conteudo == old(Conteudo) + [x])
                                       && |Conteudo| == |old(Conteudo)| + 1
                                       && tail == old(tail) + 1
                                       && r == true
    // Garante que se o elemento já existia antes, o novo Conteudo
    // será igual ao Conteudo antigo, e garante a resposta negativa
    // de adição do novo elemento.
    ensures x in old(Conteudo) ==> (Conteudo == old(Conteudo))
                                    && |Conteudo| == |old(Conteudo)|
                                    && r == false
    {

        var pertence := Pertence(x);
        if(pertence)
        {
            // Valor ja pertence ao conjunto, negativa na adição.
            r := false;
        } else {
            //Verifica tamanho atual do array e o expande caso seja necessário
            if (tail == elementos.Length)
            {
                var novoArrayExpandido := new nat[2 * elementos.Length];
                forall(i | 0 <= i < elementos.Length)
                {
                    novoArrayExpandido[i] := elementos[i];
                }
                elementos := novoArrayExpandido;
            }
            // Adição do novo elemento
            elementos[tail] := x;
            tail := tail + 1;
            Conteudo := Conteudo + [x];
            r := true;
        }
    }

    // method Remover(x:nat) returns (r:bool)
    // requires Conteudo != []
    // ensures Conteudo == old(Conteudo)[1..]
    // ensures |Conteudo| == |old(Conteudo)| - 1
    // {

    // }

    method Pertence(x:nat) returns (r:bool)
    ensures r <==> x in Conteudo
    {
        var indice := 0;
        r := false;
        while indice < tail
        invariant 0 <= indice <= tail
        invariant (indice > 0) ==> r == (x in Conteudo[0..indice])
        invariant (indice == 0) ==> !r
        decreases tail - indice
        {
            if (elementos[indice] == x)
            {
                r := true;
            }
            indice := indice + 1;
        }
        
        return r;
    }

    // Retorna natural representando o tamanho do conjunto através da
    // variavel concreta tail.
    // Garante que a resposta (r) seja exatamente o tamanho do 
    // conjunto abstrato Conteudo.
    method Tamanho() returns (r:nat)
    ensures r == |Conteudo|
    {
        return tail;
    }

    // Retorna verdadeiro se Conjunto é vazio e falso caso contenha elementos.
    // Garante que resposta (r) seja exatamente o mesmo valor booleano resultante
    // da verificação de que Conteudo é vazio ou não.
    // Implementação concreta utiliza verificação de tail igual a 0.
    method Vazio() returns (r:bool)
    ensures r <==> Conteudo == []
    {
        return tail == 0;
    }
}




method main()
{
    // Cria conjunto de exemplo
    var conjunto := new Conjunto(5);

    // Verificação que conjunto está vazio
    var resultadoVazio := conjunto.Vazio();
    assert resultadoVazio == true;

    // Verificação do tamanho vazio do conjunto
    var resultadoTamanho := conjunto.Tamanho();
    assert resultadoTamanho == 0;

    // Adição de elemento no conjunto
    var resultadoAdicao := conjunto.Adicionar(1);
    assert resultadoAdicao == true;

    // Verificação se elemento pertence ao conjunto
    var resultadoPertence := conjunto.Pertence(1);
    assert resultadoPertence == true;

    // Adição de elemento repetido no conjunto
    var resultadoAdicaoRepetida := conjunto.Adicionar(1);
    assert resultadoAdicaoRepetida == false;

    // Adição de segundo elemento no conjunto
    var resultadoSegundaAdicao := conjunto.Adicionar(2);
    assert resultadoSegundaAdicao == true;

    // Verificação do tamanho do conjunto com 2 elementos
    var resultadoTamanho2 := conjunto.Tamanho();
    assert resultadoTamanho2 == 2;


}