/* METODOS FORMAIS: TRABALHO 1 */
/* ALUNOS:
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

    method Remover(x:nat) returns (r:bool)
    requires Conteudo != []
    ensures !(x in old(Conteudo)) ==> (Conteudo == old(Conteudo))
                                       && |Conteudo| == |old(Conteudo)|
                                       && tail == old(tail)
                                       && r == false

    ensures x in old(Conteudo) ==> Conteudo == old(Conteudo)[1..]
                                    && |Conteudo| == |old(Conteudo)| - 1
                                    && tail == old(tail) - 1
                                    && r == true
    
    {
        var pertence := Pertence(x);
        if(!pertence)
        {
            r := false;
        }
        else
        {
            r := true;
        }
    }

    method Pertence(x:nat) returns (r:bool)
    ensures r <==> x in Conteudo
    {
        var indice := 0;
        r := false;

        // Iteração para identificar se o elemento existe
        while indice < tail
        // Garante indice do laço dentro das delimitações do array
        invariant 0 <= indice <= tail
        invariant (indice > 0) ==> r == (x in Conteudo[0..indice])
        // Determina que se o conjunto tiver menos que 1 elemento, 
        // o resultado so pode ser o inverso de pertencer ao conjunto
        invariant (indice < 1) ==> !r
        // Para provar a terminação do loop
        decreases tail - indice
        {
            if (x == elementos[indice])
            {
                r := true;
            }
            indice := indice + 1;
        }
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

    // Faz a união de um conjunto introduzido como parâmetro e o conjunto atual,
    // e retorna o resultado com "novo"
    method Uniao(conj: Conjunto) returns (novo: Conjunto)
    // Pré-condição que garante que o tamanho do conjunto original é maior ou igual a zero
    requires |Conteudo| >= 0
    // Garante que o conjunto parâmetro é maior o igual a zero
    requires |conj.Conteudo| >= 0
    // Assegura que a variável novo será recriada
    ensures fresh(novo)
    // Averigua se o tamanho do conjunto de saída é maior ou igual a zero, e também
    // no máximo igual ou menor que a soma dos dois conjuntos
    ensures 0 <= |novo.Conteudo| <= |Conteudo| + |conj.Conteudo|
    // Todo elemento que estava no conjunto original também deve estar no conjunto novo
    ensures forall i :: (0 <= i < |Conteudo|) ==> Conteudo[i] in novo.Conteudo
    // Assim como todo elemento do conjunto dado como parâmetro deve pertencer ao conjunto novo
    ensures forall j :: (0 <= j < |conj.Conteudo|) ==> conj.Conteudo[j] in novo.Conteudo
    {
        // Cria novo conjunto de tamanho máximo igual a soma dos doi conjuntos base
        novo := new Conjunto(elementos.Length + conj.elementos.Length);
        
        // Variáveis auxiliares dos loops
        var i := 0;
        var j := 0;

        // Percorre todos elementos do conjunto base e adiciona ao novo
        while (i < tail)
        invariant 0 <= i <= tail
        decreases tail - i
        {
            var flag := novo.Adicionar(elementos[i]);
            i := i + 1;
        }

        // Mesma lógica do loop anterior, mas para conjunto do parâmetro
        while(j < conj.tail)
        invariant 0 <= j <= conj.tail
        decreases conj.tail - j
        {
            // Caso o elemento já pertença ao conjunto novo, ele não é inserido
            var flag := novo.Adicionar(conj.elementos[j]);
        }
    }

    // Faz a interseçao de um conjunto introduzido como parâmetro e o conjunto atual,
    // e retorna o resultado com "novo"
    method Intersecao(conj: Conjunto) returns (novo: Conjunto)
    // Mesmas condições iniciais do método anterior
    requires |Conteudo| >= 0
    requires |conj.Conteudo| >= 0
    ensures fresh(novo)
    // Tamanho do conjunto de interseção deve ser maior ou igual a zero
    ensures |novo.Conteudo| >= 0
    // Garante que cada elemento igual que pertencer a ambos conjuntos pertencerá ao novo
    ensures forall i, j :: 0 <= i < |Conteudo|
                        && 0 <= j < |conj.Conteudo|
                        && Conteudo[i] == conj.Conteudo[j]
                        ==> Conteudo[i] in novo.Conteudo
    {
        novo := new Conjunto(elementos.Length + conj.elementos.Length);
        
        var i := 0;

        // Para todo elemento que pertencer ao conjunto original e ao conjunto
        // dado com parâmetro, então adiciona-se o mesmo ao novo conjunto
        while(i < tail)
        invariant 0 <= i <= tail
        decreases tail - i
        {
            var teste := conj.Pertence(elementos[i]);
            if (teste)
            {
                var flag := novo.Adicionar(elementos[i]);
            }
            i := i + 1;
        }
    }

    // Faz a diferença de um conjunto introduzido como parâmetro e o conjunto atual,
    // e retorna o resultado com "novo"
    method Diferenca(conj: Conjunto) returns (novo: Conjunto)
    // Mesmas condições iniciais do método anterior
    requires |Conteudo| >= 0
    requires |conj.Conteudo| >= 0
    ensures fresh(novo)
    // Tamanho do conjunto de diferença deve ser maior ou igual a zero
    ensures |novo.Conteudo| >= 0
    // Garante que cada elemento igual que pertencer a ambos conjuntos não pertencerá ao novo conjunto
    ensures forall i, j :: 0 <= i < |Conteudo|
                        && 0 <= j < |conj.Conteudo|
                        && Conteudo[i] == conj.Conteudo[j]
                        ==> Conteudo[i] !in novo.Conteudo
    // E todos elementos diferentes, somente os do conjunto base pertencerão ao novo conjunto
    ensures forall i, j :: 0 <= i < |Conteudo|
                        && 0 <= j < |conj.Conteudo|
                        && Conteudo[i] != conj.Conteudo[j]
                        ==> Conteudo[i] in novo.Conteudo
    {
        novo := new Conjunto(elementos.Length + conj.elementos.Length);

        var i := 0;
        
        // Para todo elemento que não pertencer ao conjunto original e ao conjunto
        // dado com parâmetro, então adiciona-se o mesmo ao novo conjunto
        while(i < tail)
        invariant 0 <= i <= tail
        decreases tail - i
        {
            var teste := conj.Pertence(elementos[i]);
            if (!teste)
            {
                var flag := novo.Adicionar(elementos[i]);
            }
            i := i + 1;
        }
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

    var conjunto2 := new Conjunto(5);
    var dummy := conjunto2.Adicionar(3);
    dummy := conjunto2.Adicionar(4);
    dummy := conjunto2.Adicionar(5);
    var resultadoUniao := conjunto.Uniao(conjunto2);
    var testeUniao := resultadoUniao.elementos.Length;
    assert testeUniao == 5;
}
