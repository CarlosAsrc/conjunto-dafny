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
    // Garante que se o elemento não existe, o novo Conteudo
    // será igual ao Conteudo antigo, e garante a resposta negativa
    // de remoção do elemento.
    ensures !(x in old(Conteudo)) ==> (Conteudo == old(Conteudo))
                                       && |Conteudo| == |old(Conteudo)|
                                       && tail == old(tail)
                                       && r == false
    // Garante que se o elemento existe, do novo Conteudo
    // será descrescido o elemento x, o tamanho de Conteudo decrescido em 1
    // a variavel tail decrescida em 1, e garante a resposta positiva
    // de remoção do elemento.
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
            var indice := 0;
            // Iteração para identificar se o elemento existe
            while indice < tail
            // Garante indice do laço dentro das delimitações do array
            invariant 0 <= indice <= tail
            // Para provar a terminação do loop
            decreases tail - indice
            {   
                // Verifica se a posição atual da iteração no array corresponde ao elemento x
                if (x == elementos[indice])
                {
                    // Laço para remover elemento do array e trazer elementos do final para inicio (shift)
                    tail := tail - 1;
                    forall(i | indice <= i < tail)
                    {
                        elementos[i] := elementos[i+1];
                    }
                    // Declaração da abstração Conteudo de acordo com os novos elementos da implementação concreta.
                    Conteudo := elementos[0..tail];
                    r := true;
                }
                indice := indice + 1;
            }
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
    // 
    requires |Conteudo| >= 0
    requires |conj.Conteudo| >= 0
    ensures fresh(novo)
    ensures |novo.Conteudo| >= 0
    ensures |novo.Conteudo| <= |Conteudo| + |conj.Conteudo|
    ensures forall i :: (0 <= i < |Conteudo|) ==> Conteudo[i] in novo.Conteudo
    ensures forall j :: (0 <= j < |conj.Conteudo|) ==> conj.Conteudo[j] in novo.Conteudo
    {
        novo := new Conjunto(elementos.Length + conj.elementos.Length);
        
        var i := 0;
        var j := 0;
        while (i < tail)
        invariant 0 <= i <= tail
        decreases tail - i
        {
            var flag := novo.Adicionar(elementos[i]);
            i := i + 1;
        }

        while(j < conj.tail)
        invariant 0 <= j <= conj.tail
        decreases conj.tail - j
        {
            var flag := novo.Adicionar(conj.elementos[j]);
        }
    }

    method Intersecao(conj: Conjunto) returns (novo: Conjunto)
    requires |Conteudo| >= 0
    requires |conj.Conteudo| >= 0
    ensures fresh(novo)
    ensures |novo.Conteudo| >= 0
    ensures forall i :: (0 <= i < |Conteudo|) ==> Conteudo[i] in novo.Conteudo
    ensures forall j :: (0 <= j < |conj.Conteudo|) ==> conj.Conteudo[j] in novo.Conteudo
    ensures forall i, j :: (0 <= i < |novo.Conteudo|)
                        && (0 <= j < |novo.Conteudo|)
                        && (i != j) ==> novo.Conteudo[i]
                        != novo.Conteudo[j]
    {
        novo := new Conjunto(elementos.Length + conj.elementos.Length);
        
        var i := 0;
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

    method Diferenca(conj: Conjunto) returns (novo: Conjunto)
    requires |Conteudo| >= 0
    requires |conj.Conteudo| >= 0
    ensures fresh(novo)
    ensures |novo.Conteudo| >= 0
    ensures forall i :: (0 <= i < |novo.Conteudo|) ==> ((novo.Conteudo[i] in Conteudo) && !(novo.Conteudo[i] in conj.Conteudo))
                    || (novo.Conteudo[i] in conj.Conteudo && !(novo.Conteudo[i] in Conteudo))
    {
        novo := new Conjunto(elementos.Length + conj.elementos.Length);

        var i := 0;
        var j := 0;
        while(i < tail)
        invariant 0 <= i <= tail
        decreases tail - i
        {
            var teste := Pertence(elementos[i]);
            if(!teste)
            {
                var flag := novo.Adicionar(elementos[i]);
            }
            i := i + 1;
        }

        while(j < conj.tail)
        invariant 0 <= j <= conj.tail
        decreases conj.tail - j
        {
            var teste := Pertence(conj.elementos[j]);
            if(!teste)
            {
                var flag := novo.Adicionar(conj.elementos[j]);
            }
            j := j + 1;
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

    // Teste de união de conjunto
    var conjunto2 := new Conjunto(5);
    var dummy := conjunto2.Adicionar(3);
    dummy := conjunto2.Adicionar(4);
    dummy := conjunto2.Adicionar(5);
    var resultadoUniao := conjunto.Uniao(conjunto2);
    var testeUniao := resultadoUniao.elementos.Length;
    assert testeUniao == 5;

    // Teste de interseção de conjunto
    var conjunto3 := new Conjunto(5);
    dummy := conjunto3.Adicionar(2);
    dummy := conjunto3.Adicionar(4);
    dummy := conjunto3.Adicionar(5);
    var resultadoIntersecao := conjunto.Intersecao(conjunto3);
    assert resultadoIntersecao.elementos[0] == 2;

    // Teste de diferença de conjunto
    var conjunto4 := new Conjunto(5);
    dummy := conjunto4.Adicionar(2);
    dummy := conjunto4.Adicionar(4);
    dummy := conjunto4.Adicionar(5);
    var resultadoDiferenca := conjunto.Diferenca(conjunto4);
    assert resultadoDiferenca.elementos[0] == 2;
}
