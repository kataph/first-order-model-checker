## Model Checker For First-Order Logic
Per adesso semplicente eseguire check.py  (e.g. `>python check.py`).
Alcuni test in `tests.py`

## TODOS
1-parserare intera teoria ✔
2-parserare intero modello ✔
3-estrarre le variabili da una formula ✔
4-valuate una formula dato un modello parserato ✔
5-scrivere intero modello ✔

## NOTA BENE/ APPUNTI
6-ricordare che: no "=" in modello -> tutte costanti diverse
7-ricordare che: uguaglianza è dunque valutata semplicemente in base a nome delle costanti
8-ricordare che: quantificatori in eccesso rallenteranno esecuzione ma non cambiano valore risultato
9-ricordare che: metodo è abbastanza sciocco, eg all X0 all X1 all X2 ... all X100 \Phi | - \Phi fa numero di costanti alla 100 anche se è tautologia!
10-ricordare che: non serve enumerare le costanti all'inizio del modello: saranno inferite dalle affermazioni del modello. QUanid tutte e sole le costanti devono apparire in questo    
11-ricordare che: no definizioni in assiomi, o se date i definiti devono essere tutti specificati nel modo corretto nel modello
12-ricordare che: il modello è completamente specificato nel modo seguente: tutti e soli i fatti veri sono scritti. Tutti e soli quelli falsi sono taciuti. Unica eccezione sono le uguaglianze: costanti con nomi diversi si assumono diverse
13-eliminato sd con suo definiente: compare in singolo assioma (Ad71), oltre che nella sua definizione (Dd69). Inoltre risulterebbe (all X all Y -ab(X) & -ab(Y) -> sd(X,Y)).
14-eliminate tutti i predicati owl: è un'estensione definizionale di DOLCE; quindi se DOLCE è consistente anche DOLCE + definizioni owl è consistente; inoltre la non-vuotezza dei predicati definiti (oltre che ovvia dalla non vuotezza dei predicati di DOLCE) è presentata più volte negli use case in owl, non so se tecnicamente questo implichi la non vuotezza della corrispondente teoria FOL, però direi che è abbastanza. In caso si possono aggiungere anche quelli, o magari, più semplicemente, verificare assiomi del tipo (all X all Y (constantlySpatiallyLocatedAt(c1,c2) <-> ((ped(c1) | nped(c1) | pd(c1) | pq(c1)) & s(c2) & (all T (pre(c1,T) -> tql(c1,c2,T)))))) per una data coppia c1,c2, verificando così la non-vuotezza, senza dover enumerare tutte le occorrenze di constantlySpatiallyLocatedAt, e analogamente per le altre relazioni owl definite.
14.errata-In realtà, il punto 14 è errato: la parte temporale ha enduranti come argomenti... Ho sostituito con una somma di due NAPO
14.errata.errata-In realtà, AS è sottocategoria di ED, quindi non ci dovrebbe essere un problema. 
14.errata.errata.errata-In realtà, tsum per definizione è tra PED o NPED, quindi il problema c'è -> ripristinati i tre NAPO. 
15-riguardo l'istanziazione della somma temporalizzata: ho scelto di sommare tra loro 2 somme arbitrarie, perché questo cagiona il minimo numero di asserzioni. Chiaramente si può fare anche per e.g. dei physical objects, ma non è stato mai richiesto specificatamente e il modello diventerebbe più grande
16-similmente, ho sommato due regioni temporali tra di loro (sommare due e.g. perduranti attiverebbe la definizione di temporalPart; inoltre c'è assioma achievemants_non_atomic_Ad76 che deve essere rispettato)
17-non è richiesta l'istanziazione della relazione di costituzione, quindi potrebbe essere lasciata "disattivata". Però siccome è un modulo importante l'ho attivata
18-definire versioni irriflessive dei predicati semplificherebbe questo approccio (e.g. per come è definita sum, sum è riflessiva sul suo dominio).


## Alcuni esempi di spiegazioni della falsità di un assioma
Qui mancava un pt che non era stato asserito.

```
valuating >>>(all X ((ab(X) | ed(X) | pd(X) | q(X)) <-> pt(X))).<<< against given model...
...evaluation result is >>>[False]<<<
Evaluation of axiom >>>(all X ((ab(X) | ed(X) | pd(X) | q(X)) <-> pt(X))).<<< is False! Generating explanation...       
node predicate with presentation
 predicate
  ab
  X
 --> False with {'X': 'pro1'}
node predicate with presentation
 predicate
  ed
  X
 --> False with {'X': 'pro1'}
node disjunction with presentation
 disjunction
  predicate
    ab
    X
  predicate
    ed
    X
 --> False with {'X': 'pro1'}
node predicate with presentation
 predicate
  pd
  X
 --> True with {'X': 'pro1'}
node disjunction with presentation
 disjunction
  disjunction
    predicate
      ab
      X
    predicate
      ed
      X
  predicate
    pd
    X
 --> True with {'X': 'pro1'}
node predicate with presentation
 predicate
  q
  X
 --> False with {'X': 'pro1'}
node disjunction with presentation
 disjunction
  disjunction
    disjunction
      predicate
        ab
        X
      predicate
        ed
        X
    predicate
      pd
      X
  predicate
    q
    X
 --> True with {'X': 'pro1'}
node predicate with presentation
 predicate
  pt
  X
 --> False with {'X': 'pro1'}
node equivalence_entailment with presentation
 equivalence_entailment
  disjunction
    disjunction
      disjunction
        predicate
          ab
          X
        predicate
          ed
          X
      predicate
        pd
        X
    predicate
      q
      X
  predicate
    pt
    X
 --> False with {'X': 'pro1'}
node universal_quantification with presentation
 universal_quantification
  X
  equivalence_entailment
    disjunction
      disjunction
        disjunction
          predicate
            ab
            X
          predicate
            ed
            X
        predicate
          pd
          X
      predicate
        q
        X
    predicate
      pt
      X
 --> False with {'X': 'pro1'}
```




Qui invece mi ero dimenticato che tsum(z,x,z) se z = x+y
```
 node universal_quantification with presentation
 universal_quantification
  Z
  equivalence_entailment
    predicate
      dif
      Z
      X
      Y
    conjunction
      disjunction
        conjunction
          conjunction
            predicate
              ab
              Z
            predicate
              ab
              X
          predicate
            ab
            Y
        conjunction
          conjunction
            predicate
              pd
              Z
            predicate
              pd
              X
          predicate
            pd
            Y
      universal_quantification
        W
        equivalence_entailment
          predicate
            p
            W
            Z
          conjunction
            predicate
              p
              W
              X
            negation
              predicate
                ov
                W
                Y
 --> False with {'X': 't1', 'Y': 't2', 'Z': 't1'}
 ```