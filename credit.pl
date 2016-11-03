% Author: Petr Geiger
% Date: 6. 5. 2015

%*******************************************************************************
%Uzivatelska dokumentace:
%*******************************************************************************
%Regularni vyrazy jsou repreznetovany pomoci termu v prologu, stejne tak i automat.
%Presny format vstupu/vystupu viz. programatorska dokumentace. Program obsahuje
% dva zakladni predikaty:
%          auToRex(+Automat, -Regex) - prevod automatu na regularni vyraz
%          rexToAut(+Regex, -Automat) - prevod regularniho vyrazu na automat
%
%Dale pro testovaci ucely existuje predikat getAn(-Aut), ktery vraci nedeterministicky
%nekolik automatu, ktere jsem pouzil jako testovaci vstup. Dale pro stejny ucel
%existuje pro testovaci regularni vyrazi predikat getReg(-Reg). Vsechny tyto vstupy
%jsou overeny a mel by na ne program vratit korektni vysledek. Konecne pro davkove
%spocitani vsech vysledku pro vstupni testy existuje predikat auToRexTest(-Rex)
%resp. predikat rexToAutTest(-Aut). (Vstupy jsou na konci souboru)
%
%*******************************************************************************
%Programatorska dokumentace:
%*******************************************************************************
%format pouzivaneho automatu
%an(N, Nx, d, q0, F)
%automat obsahuje stavy [1,...,N]
%abeceda obsahuje pismena [1,...,Nx]
%d = [q-x-qOut, ...] prechodova fce, hrana: ze stavu q pismenem x do stavu qOut
%q0 pocatecni stav
%F=[f0, f1, ...]  vystupni stavy

%reg vyrazy tvaru:
%empty - prazdna mnozina
%lambda - prazdne slovo
%x - kde x je prirozene cislo, pismena
%+ - sjednoceni
%* - iterace
%` - konkatenace
% predchozi operatory jsou predefinovany tak, aby tvorily spravnu strukturu
%termu regularniho vyrazu

%*******************************************************************************
%Prevod automat->regularni vyraz
%K prevodu se pouziva induktivni predpis z Kleeneho vety "Lij + LiI`(LII)*`LIj".
%Mame matici L regularnich vyrazu rozmeru N*N, kde N je pocet stavu automatu.
%Kdyz L je v iteraci I, pak prvek na pozici i,j v L je regularni vyraz odpovidajici
%automatu se vstupnim stavem i a vystupnim j, a pouzitimy vrcholy 1,...,I. Takze
%Pro N-tou iteraci prvky matice L odpovidaji regularnim vyrazum odpovidajci celemu
%automatu. Z teto matice pak vysledny regularni vyraz vzninke sjednocnim regulanich
%vyrazu na pozicich Lij, takove ze i je vstupni stav a j vystupny stav automatu.
%V kazde iteraci se navic vyraz "Lij + LiIt`(LitIt)*`Litj" pokousi zjednodusit
%podle nasledujicich pravidel.:
%  ba*(lambda + a) = ba*
% (lambda + a)a*b = a*b
% (lambda + a + X) + a* = X + a*
% (b + X) + a*b = X + a*b
% (b + X) + ba* = X + ba*
% (b + X) + aa*b = a*b
% (b + X) + ba*a = ba*
% konkatenace jsou vynechany a X odpovida nejakemu dalsimu sjednoceni
%Na konci se navic provede optimalizace typu:
%(lambda + X + A`(A*)) => (X + A*) , kde X = A1 + ... + An

%*******************************************************************************
%Prevod regularni vyraz-> automat
%Z regularniho vyrazu jsou nejprve odstraneny prebytecne lambda v konkatenaci.
%(tj. napr.: a.lambda.b = a.b ) Pote se k regexpu konkatenuje zepredu pismeno 0,
% to zapricini vytvoreni vychoziho stavu. Dale se prochazi dohloubky struktura
%regularniho vyrazu. Kdyz se dojde k pismenum, vytvori  elementarni
%automat s jednym stavem pro dane pismeno. Ma jednu prechodovou funkci ze zatim
%nespecifikovaneho stavu, pres dane pismenou do toho jedineho stavu. Stav je nastaven
%jako vystupni. Elementarni automat pro lambda je automat, ktery ma nastaveno pouze
% ve vystupni fci lambda. Dale pri vynorovani se tyto elementarni automaty sjednocuji,
% konkatenuji ci iteruji.
%Sjednoceni 2 automatu:
%           - prejmenovani stavu 2. automatu tak aby nekolidovaly s 1.(v prechodove fci)
%           (odpovida sjednoceni stavu, protoze stavy jsou pouze cislovany)
%           - prechodova fce vznikne sjednocenim prechod. fci obou automatu
%           - vystupni stavy vzniknou sjednocenim vystupnich stavu obou  automatu.
%           Navic pokud alespon jeden z automatu ma ve vystupni fci lambda,
%           bude mit i vysledny automat ve vystupni fci prave jednu lambdu.
%konkatenace 2 automatu:
%           - prejmenovani stavu 2. automatu tak, aby nekolidovaly s 1.(v prechodove fci)
%           - sjednoceni prechodovych funkci. Nenastavene vychozi stavy prechodove
%           fce druheho automatu se napoji na vystupni stavy prvniho automatu.
%           - vystupni stavy jsou stavy 2. automatu. Pokud navic vystupni stavy
%           2. automatu obsahuji lambda, jsou pridany i vsechny vystupni stavy
%           1.automatu (lambdy jsou odstraneny)
%iterace automatu:
%           - kazda iterace a* je explicitne zmenena na(a + lambda)*, coz zpusobi
%           spravne fungovani i pro iteraci delky 0.
%           - iterace vznikne pridanim, prechodovych fci z vystupnich stavu zpet
%           do stavu, do kterych vede prechodova fce s nedefinovanym pocatecnim
%           stavem.
%
%Z vysledneho automatu se odstrani jedina nedefinovana prechodova fce do vstupniho
%stavu, projitim prechodovych funci se nalezne nejvetsi Index abecedy automatu.
%Vysledny automat odpovida regularnimu vyrazu.

%*******************************************************************************
%SOURCE
%*******************************************************************************

%odstraneni prednastavenych operatoru
:- op( 0, fy, [+]).
:- op( 0, yfx,[*,+]).

%nastaveni operatoru tak, aby odpovidali operatorum regularnich vyrazu
:- op( 1, xf, * ).
:- op( 2, yfx, ` ).
:- op( 3, xfy, + ).

%Init***************************************************************************
%er(+Q1, +Q2, +Ds, -Xs) :- nalezne prechodova pismena ze stavu Q1 do Q2
% v prechodove fci Ds a vrati je jako seznam Xs.
er(_, _, [], []).
er(Q1, Q2, [H|Ds], [X|Ys]) :- H=Q1-X-Q2, er(Q1, Q2, Ds,Ys).
er(Q1, Q2, [H|Ds], Ys) :- H\=Q1-_-Q2, er(Q1, Q2, Ds,Ys).

%addLbda(+Q1,+Q2, +RegList, -Ys) :- prida do seznamu pismen prazdne slovo,
%pokud tam ma byt a vysledek ulozi do Ys
addLbda(Q, Q, RegList, [lambda|RegList]).
addLbda(Q1, Q2, RegList, RegList) :- Q1 \= Q2.

%toRex(+Xs,-Y) :- prevede seznam regexu Xs na reg. vyraz Y sjednocenim, (pripadne prazdnou mn.)
toRex([], empty).
toRex([X], X).
toRex([X,Y|Xs], X+Ys) :- toRex([Y|Xs], Ys).

%elemReg(+AN, +Q1, +Q2, -Reg) :- z AN automatu najde mezi stav Q1 a Q2
%odpovidajici reg. vyraz, ktery ulozi do Req
elemReg(an(_, _, D, _, _), Q1, Q2, Reg) :- er(Q1, Q2, D, Xs), addLbda(Q1,Q2,Xs,Ys), toRex(Ys,Reg).

%makeTable(+N, -Table) :- vytvori matici NxN plnou volnych promencch a ulozi do Table
makeTable(N, Table) :- length(Rows, N), fillRows(N, Rows, Table).

%fillRows(+N, +Rows, -Table) :- kazdy prvek seznamu Rows naplni seznamem s
%volnymi promenymi delky N a vysledek vrati v Table
fillRows(_, [], []).
fillRows(N, [_|Xs], [Row|Rows]) :- length(Row, N), fillRows(N, Xs, Rows).

%setRow(+AN, +RowIndex, +Row) :- Nastavi kazdy prvek Row, na odpovidajici regex
% dle automatu AN a RowIndex.
setRow(AN, R, Xs) :- setRow1(AN, R, 1, Xs).
%setRow1(+AN, +RowIndex, curColumn, +Row)
setRow1(_, _, _, []).
setRow1(AN, R, C, [X|Xs]) :- Cn is C + 1, elemReg(AN, R, C, X), setRow1(AN, R, Cn, Xs).

%initTable(+NA, +Table, -Table) :- inicializuje Tabulku req. vyrazu dle
%atomatu NA(normalized automaton) initTable(NA, Table, Table)
initTable(NA, Xs) :- initTable1(NA, 1, Xs).
initTable1(_, _, []).
initTable1(NA, R, [X|Xs]) :- Rn is R+1, setRow(NA, R, X), initTable1(NA, Rn, Xs).

%Kleene_alg*********************************************************************
%getElem(+I, +Xs, -X) :- Do X ulozi I-ty prvek seznamu Xs
getElem(I, Xs, X) :- getElem1(I, 1, Xs, X).
getElem1(I, I, [X|_], X).
getElem1(I, J, [_|Xs], Y):- I > J, K is J + 1, getElem1(I, K, Xs, Y).

%getReg(+I,+J,+Table,-Reg) :- Z matice Table ulozi do Reg, prvek na pozici [I,J]
getReg(I,J, Xs, X) :- getElem(I, Xs, Ys), getElem(J, Ys, X).

%setKleenRow(+RowIndex, +CurColumn, +PrevTable, +CurIteration, +CurRow, +RowPTable, +LiIt, +Litit) :-
%Nastavi Radek matice CurRow na spravne hodnoty, tj regex tvaru "Lij + LiIt`(LitIt)*`Litj" . Kde LiIt a LitIt
% jsou pro kazdy radek stejny, takze se predpocitaji a fce je bere jako parametr. Zbyle 2 se pro kazdou
%bunku vyhleda primo v PrevTable(tabluky z predchozi iterace alg). Pokud je alespon jeden z tri LiIt`(LitIt)*`Litj
%empty, v bunce bude pouze Lij (2,3,5 pravidlo). Jinak se vyraz prida cely, pricemz se pokusi alespon trochu zjednodusit.
setKleenRow(_, _, _, _, [], [], _, _).
setKleenRow(I, J, T, It, [Lij|Xs],[Lij|Ys], empty, L) :- L\=empty, Jn is J + 1, setKleenRow(I, Jn, T, It, Xs, Ys, empty, L). %prvni z trojice empty
setKleenRow(I, J, T, It, [Lij|Xs],[Lij|Ys], L, empty) :- Jn is J + 1, setKleenRow(I, Jn, T, It, Xs, Ys, L, empty).           %(prvni a )druhy z trojice empty
setKleenRow(I, J, T, It, [LijNew|Xs],[Lij|Ys], L, K) :- L\=empty, K\=empty, Jn is J + 1, getReg(It, J, T,  X), X\=empty, !, simplify(Lij, L, K, X, LijNew), setKleenRow(I, Jn, T, It, Xs, Ys, L, K). %zadny empty -> LijNew=Lij+L`(K*)`X,
setKleenRow(I, J, T, It, [Lij|Xs],[Lij|Ys], L, K) :- L\=empty, K\=empty, Jn is J + 1, setKleenRow(I, Jn, T, It, Xs, Ys, L, K). %posledni z trojice empty

%setKleen(+Iteration, +PrevTable, +Table) :- Provede Iteraci algoritmu, novou tabulku ulozi do Table
setKleen(It, TP, T) :- getReg(It, It, TP, Litit1), rmPattNoRoot(Litit1, lambda, Litit), setKleen1(It, Litit, 1, T, TP, TP).%rmPatt vraci empty, pritom bychom chteli lambdu nechat
setKleen1(_, _, _, [], [], _).
setKleen1(It, Litit, I, [X|Xs], [Y|Ys], TP) :- getReg(I, It, TP, LiIt), setKleenRow(I, 1, TP, It, X, Y, LiIt, Litit), In is I +1, setKleen1(It, Litit, In, Xs, Ys, TP).

%iterKleen(+Automat, -Table) :- provede N iteraci alg. a Tabulku z poslendi iterace ulozi to Table.
iterKleen(AN,  Y) :- an(N, _, _, _, _)=AN, makeTable(N, X), initTable(AN, X), iterKleen1(X, 1, N, Y).
iterKleen1(T, I, N, Y) :- I =< N, In is I + 1, makeTable(N, Tnew), setKleen(I, T, Tnew), iterKleen1(Tnew, In, N, Y ).
iterKleen1(T, K, N, T) :- K is N+1.

%auToRex(+Automat, -Regex):- Prevede automat na odpovidajci Regex.
auToRex(AN, Rex) :- AN=an(_,_,_,Q0,Xout), iterKleen(AN, Y), auToRex1(Y, Q0, Xout, RexList), toRex(RexList, Rex1), optimize(Rex1, Rex).
auToRex1(_,_,[], []).
auToRex1(Xt, Q0, [X|Xout], [Y|Ys]) :- getReg(Q0, X, Xt, Y), auToRex1(Xt, Q0, Xout, Ys).

%Simplify_rex*******************************************************************

%rmPattNoRoot(+Regex, +Pattern, -Result) :- odstrani z Regex tvaru ( a+b+..+z) casti
%odpovidajici Patternu a vysledek vrati v Result. Pokud cely pater matchuje
% presne, vrati lambda.
rmPattNoRoot(I,I,lambda) :- !.
rmPattNoRoot(I,P,O) :- rmPatt(I, P, O).

%rmPatt(+Regex, +Pattern, -Result) :- odstrani z Regex tvaru ( a+b+..+z) casti
%odpovidajici Patternu a vysledek vrati v Result. Pokud cely pater matchuje
% presne, vrati empty.
rmPatt(I,I,empty) :- !.
rmPatt(I,P,O) :- rmPatt1(I, O, R, P), var(R), !.
rmPatt(I,P,O) :- rmPatt1(I, Ot, R, P), R=P, rmPatt(Ot, P, O).
%
rmPatt1(P+P,P , P, P). %novy prvek k odmazany vyplyne o uroven vys -> znova se zavola rmPatt1
rmPatt1(P+B, T, R, P) :- B \= P, rmPatt1(B, T, R, P).
rmPatt1(A+P, T, R, P) :- A \= P, rmPatt1(A, T, R, P).
rmPatt1(A+B, T, R, P) :- A \= P, B \= P, rmPatt1(A , T1, R, P), rmPatt1(B, T2, R2, P), T=T1+T2, R=R2 .
rmPatt1(A`B, A`B, _, _).
rmPatt1(A*, A*, _, _).%added
rmPatt1(A,A, _, _) :- atomic(A).

%contain(+Regex, +Pattern) :- uspeje pokud Regex typu ( a+b+..+z) obsahuje cast odpovidajici Patternu.
contain(Pat, Pat).
contain(Pat+_, Pat).
contain(L+Pat, Pat) :- L \= Pat.
contain(L+_, Pat) :- L \= Pat, contain(L, Pat), !.
contain(_+R, Pat) :-R\= Pat, contain(R, Pat).

%rmSub(+a, +b, -Y) :- zjednodusi vyraz pokud je tvaru (lambda + a).a*b = a*b a ulozi ho do Y
rmSub(L,K,Y) :- contain(L, lambda), contain(L, K),!, rmPattNoRoot(L, K, Y). % (lambda + a).a*b = a*b
rmSub(L,_,L).

%simFinal1(+Reg1, +Reg2, -Y) :- pokusi se slozit Reg1 a Reg2, pokud to jde, a vysledek vrati v Y.
simFinal1(empty, It, Y) :- clean(It, Y).
simFinal1(Lij, It, Y) :- Lij \= empty, clean(Lij+It, Y).

%simFinal("+Lij, +LiIt, +LitIt, +Litj, -Y) :- Pokusi se zjednodusit regex tvaru "Lij + LiIt`(LitIt)*`Litj" a vysledek ulozi do Y.

simFinal(lambda,lambda,lambda, lambda, lambda) :- !.
simFinal(Lij,lambda,K, lambda, Y) :- rmPatt(Lij, lambda, Lij1), rmPatt(Lij1, K, Lij2), simFinal1(Lij2, K*, Y). % (lambda + a + X) + a* = X + a*

simFinal(Lij,lambda,K, R, Y) :- R\=lambda, rmPatt(Lij, R, Lij1), simFinal1(Lij1, (K*)`R, Y).                   % (b + X) + a*b = X + a*b
simFinal(Lij,L,K, lambda, Y) :- L\=lambda, rmPatt(Lij, L, Lij1), simFinal1(Lij1, L`(K*), Y).                   % (b + X) + ba* = X + ba*
simFinal(Lij,L,L, R, Y) :- L\=lambda,R\=lambda, contain(Lij, R), !,  rmPatt(Lij, L`R, Lij1), rmPatt(Lij1, R, Lij2) , simFinal1(Lij2, (L*)`R, Y).     % (b + X) + aa*b = a*b
simFinal(Lij,L,R, R, Y) :- L\=lambda,R\=lambda, contain(Lij, L), !,  rmPatt(Lij, L`R, Lij1), rmPatt(Lij1, L, Lij2) , simFinal1(Lij2, L`(R*), Y).     % (b + X) + ba*a = ba*
simFinal(Lij,L,K, R, Y) :- L\=lambda,R\=lambda, rmPatt(Lij, L`R, Lij1), simFinal1(Lij1, L`(K*)`R, Y). %odstrani jen pripadnou iteraci velikosti 1

%simplify("+Lij, +LiIt, +LitIt, +Litj, -Y) :- Pokusi se zjednodusit regex tvaru "Lij + LiIt`(LitIt)*`Litj" a vysledek ulozi do Y.
simplify(Lij, L, K, R, Y) :- rmSub(L,K, Y1), rmSub(R, K, Y2), !, simFinal(Lij, Y1, K, Y2, Y).
simplify(Lij, L, K, R, Y) :- simFinal(Lij, L, K, R, Y).

%optPlus(+A1, -T) :- Uci zda lze provest nasledujici optimalizace. Pokud ano, provede ji.
optPlus(A, T) :- contain(A, lambda), !, optIter(A, T1), rmLbdaCond(A, T1, T).
optPlus(A, A).

%rmLbdaCond(+A, +B, -C) :- pokud A a B jsou ruzne, odstrani lambda ze sjednoceni
rmLbdaCond(A, A, A) :- !.
rmLbdaCond(A, B, C) :- A\=B, rmPattNoRoot(B, lambda, C).


%optIter(+A1, -T) :- provede optimalizaci (lambda + X + A`(A*)) => (X + A*) , kde X = A1 + ... + An
% a vysledek ulozi do T
optIter(A+B, A1+B1) :- !, optIter(A, A1), optIter(B, B1).
optIter(A`(A*), A*) :- !.
optIter(A, T) :- optimize(A, T).

%optimize(+Q, -T) :- Odstrani v reqexu nadbytecne casti nasl. typu a vysledek ulozi do T:
%(lambda + X + A`(A*)) => (X + A*) , kde X = A1 + ... + An
optimize(A+B, T) :- optPlus(A+B, T).
optimize(B*, B1*) :- optimize(B , B1).
optimize(A`B, A1`B1) :- optimize(A, A1), optimize(B, B1).
optimize(A, A) :- atomic(A).


%RegexToAutomat*****************************************************************
%elemAuto(+Letter, -Automat) :- vytvori Automat prijimajici Letter s neurcenym vstupnim stavem
elemAuto(A, an(1, _, [_-A-1], _, [1])) :- A\=lambda.
elemAuto(lambda, an(0, _, [], _, [lambda])).

%updateStates(+N, +PuvodiPrechodovaFce, -NovaPrechodovaFce) :- prejmenuje stavy o N
updateStates(_, [], []).
updateStates(N, [A-X-B|Xs], [C-X-D|Ys]) :- nonvar(A), nonvar(B),!, C is N+A, D is N+B, updateStates(N, Xs, Ys).
updateStates(N, [A-X-B|Xs], [C-X-_|Ys]) :- nonvar(A), var(B),!, C is N+A, updateStates(N, Xs, Ys).
updateStates(N, [A-X-B|Xs], [_-X-D|Ys]) :- var(A), nonvar(B),!, D is N+B, updateStates(N, Xs, Ys).
updateStates(N, [A-X-B|Xs], [_-X-_|Ys]) :- nonvar(A), nonvar(B),!, updateStates(N, Xs, Ys).

%updateFinal(+N, +PuvoidniStavy, -Lambda, -PrejmenovaneStavy) :- prejmenuje stavy o N.
%Vyhodi stavy typu lambda a pokud se tak stalo alespon jednou do Lambda ulozi lambda, jinak empty.
updateFinal(_, [], empty, []) :- !.
updateFinal(_, [], lambda, []).
updateFinal(N, [X|Xs], F1, [Y|Ys]) :- X\=lambda, Y is N+X, updateFinal(N, Xs, F1, Ys).
updateFinal(N, [lambda|Xs], lambda, Ys) :- updateFinal(N, Xs, lambda, Ys).

%finalLbda(+Lambda, +F1, +F2, -F3) :- Pokud Lambda obsahuje lambda spiji seznamy F1 a F2
%ktere vrati v F3. Pokud Lambda obsahuje empty vrati v F3 pouze F2.
finalLbda(lambda, F1, F2, Y) :- !, append(F1, F2, Y).
finalLbda(empty, _, F2, F2).

%mkEdges(+FinalStates, +EdgePattern, -EdgeList, -ListEnd) :- vytvori seznam hran, ktery ulozi
%do EdgeList a jeho konec do ListEnd. Pro kazdy stav F z FinalStates se vytvori odpovidajici
%hrana dle vzoru EdgePattern -> F-B-C.
mkEdges([], _, Ys, Ys).
mkEdges([lambda|Fs], Exp, Ys, YsEnd) :- mkEdges(Fs, Exp, Ys, YsEnd ). %preskoci lambdy (kvuli iteraci je treba)
mkEdges([F|Fs], _-B-C, [F-B-C|Ys], YsEnd) :- F\=lambda, mkEdges(Fs, _-B-C, Ys, YsEnd).

%con(+FinalStates, +Edges, -FinalEdges) :- Uplne hrany prida do FinalEdges. Z neuplnych hran
%vytvori hrany, napojujici se na kazdy prvek FinelStates, ktere take prida do FinalEdges.
%Na konci neni v FinalEdges zadna neuplna hrana.
con(_, [], []).
con(F, [A-B-C|Xs], [A-B-C|Ys]) :- nonvar(A),!, con(F, Xs, Ys). %hotova funkce(vnitrek automatu)
con(F, [A-B-C|Xs], Ys) :-  mkEdges(F, A-B-C, Ys, YsEnd), con(F, Xs, YsEnd). %napojeni


%con(+FinalStates, +Edges, -FinalEdges) :- Uplne hrany prida do FinalEdges. Z neuplnych hran
%vytvori hrany, napojujici se na kazdy prvek FinelStates, ktere take prida do FinalEdges.
%Navic do FinalEdges prida nuplne vzory.
cyc(_, [], []).
cyc(F, [A-B-C|Xs], [A-B-C|Ys]) :- nonvar(A),!, cyc(F, Xs, Ys). %hotova funkce
cyc(F, [A-B-C|Xs], [A-B-C|Ys]) :- mkEdges(F, A-B-C, Ys, YsEnd), cyc(F, Xs, YsEnd). %napojeni + nechani vstupu

%addLbda(+Lambda1, +Lambda2, +F1, +F2, -Final) :- Spoji seznamy F1 a F2 a ulozi do Final,
%pokud alespon jeden z parametru +Lambda1, +Lambda2 je lambda, prida do Final i lambda.
addLbda(lambda, _,  F1F, F, [lambda|Ffinal]) :- !, append(F1F, F, Ffinal).
addLbda(_, lambda,  F1F, F, [lambda|Ffinal]) :- !, append(F1F, F, Ffinal).
addLbda(_, _,  F1F, F, Ffinal) :- append(F1F, F, Ffinal).

%connect(+Automat1, +Automat2, -Automat3) :- Provede konkatenaci automatu Automat1`Automat2 a
% vysledny automat ulozi do Automat3. Tzn. Napoji neuplne hrany z Automat2 na Finalni stavy z
%Automat1. Po tomto v Automatu3 nejsou vystupni stavy lambda, pouze konkretni stavy!
connect(an(N1, _, X1s, _, F1), an(N2, _, X2s, _, F2), an(N, _, XsFinal, _, F) ) :- N is N1+N2,
                                                                            updateStates(N1, X2s, Xss ),
                                                                            updateFinal(N1, F2, Lbda, FF),
                                                                            finalLbda(Lbda, F1, FF, F),
                                                                            con(F1, Xss, Xs),
                                                                            append(X1s, Xs, XsFinal).

%unify(+Automat1, +Automat2, -Automat3) :- Provede sjednoceni automatu Automat1+Automat2 a
% vysledny automat ulozi do Automat3. Vystupni fce Automatu3 muze obsahovat lambda!
unify(an(N1, _, X1s, _, F1), an(N2, _, X2s, _, F2), an(N, _, XsFinal, _, Ffinal) ) :- N is N1+N2,
                                                                            updateStates(N1, X2s, Xss ),
                                                                            updateFinal(N1, F2, Lbda1, F),
                                                                            updateFinal(0, F1, Lbda2, F1F),
                                                                            addLbda(Lbda1, Lbda2, F1F, F, Ffinal),
                                                                            append(X1s, Xss, XsFinal).

%cycle(+Automat1, -Automat2) :- Provede iteraci automatu Automat1* a vysledny
%automat ulzodi do Automat2. Tzn. napoji vystupni stavy na vstupni.
cycle(an(N, _, Xs, _, F), an(N, _, XsFinal, _, F) ) :- cyc(F, Xs, XsFinal).

%through(+Regex, -Automat) :- Projde struktury Regexu a skladanim elemntarnich automatu
% vytvori vysledny Automat odpovidajci Regexu. S neurcenou abecedou a neuplnymi hranami
%vedouciho do prvniho stavu. Na vstupu predpoklada regex bez zbytecnych lambda
%napr misto -> lambda`1`lambda`lambda`2`lambda -> ocekava 1`2
through(A`B, Y) :- through(A, Y1), through(B, Y2), connect(Y1, Y2, Y).
through(A+B, Y) :- through(A, Y1), through(B, Y2), unify(Y1, Y2, Y).
through(A*, Y) :- through(A+lambda, Y1), cycle(Y1, Y).
through(A, Y) :- atomic(A), elemAuto(A, Y).

%combine(+Regex1, +Regex2, -Regex) :- Provede konkatenaci Regex1`Regex2, pricemz
%vynecha nadbytecne lambdy.
combine(lambda, A, A) :- A\=lambda, !.
combine(A, lambda, A) :- A\=lambda, !.
combine(lambda, lambda, lambda) :- !.
combine(A, B, A`B).

%combineM(+Regex1, -Regex) :- Pokud Regex1 je lambda vrati v Regex lambda, jinak
%vrati iteraci Regexu1.
combineM(lambda, lambda).
combineM(A, A*) :- A\=lambda.

%clean(+Regex1, -Regex) :- odstrani z Regex1 nadbytecne konkatenace lambda
%(viz through) a upravene regex vrati v Regex.
clean(A`B, Y) :- clean(A, Y1), clean(B, Y2), combine(Y1,Y2, Y).
clean(A+B, Y1+Y2) :- clean(A, Y1), clean(B, Y2).
clean(A*, Y) :- clean(A, Y1), combineM(Y1, Y).
clean(A, A) :- atomic(A).

%maxletter(+PrechodovaFce, +Akumulator, -NejvyssiPismeno) :- projde vstupni fci
% a nalezne nejvyssi pismeno ktere vrati v  NejvyssiPismeno
maxletter([],L, L).
maxletter([_-X-_|Xs], L, FL) :- L1 is max(L,X), maxletter(Xs, L1, FL).

%rexToAut(+Regex, -Automat) :- Prevede Regex na odpovidajici Automat.
rexToAut(Rex, an(N, Nx, Xs, 1, F)) :- clean(0`Rex, Rexx), through(Rexx, an(N, _, [_|Xs], _, F)), maxletter(Xs, 0, Nx).

%TESTS**************************************************************************
testInit(Table, N) :- getAn(AN), an(N,_,_,_,_)=AN, makeTable(N, Table), initTable(AN, Table).
testER(Q1,Q2,Res) :- getAn(AN), elemReg(AN, Q1, Q2, Res).
testKlRow(TP, Row, T) :- testInit(TP, _),  getElem(Row, TP, TPRow), getElem(Row, T, TRow), getReg(Row,1,TP,LiIt), getReg(1,1,TP,Litit),  setKleenRow(1, 1, TP, 1, TRow, TPRow, LiIt, Litit ).
testSetKleen(X, T) :-  testInit(X, N),  makeTable(N,T), setKleen(1, X, T).
testCont(X) :- contain(lambda+a, a), X=a.
testIter2Kleen(T0, T1, T2) :- testSetKleen(T0, T1), makeTable(3,T2), setKleen(2, T1, T2).
testIterKleen(X) :- getAn(AN), iterKleen(AN,X).

auToRexTest(Rex) :- getAn(AN), auToRex(AN, Rex).
rexToAutTest(Aut) :- getReg(Reg), rexToAut(Reg, Aut).

optTest(Q) :- getReg(A), optimizeTest(Q, A).
optimizeTest(Q, Reg) :- rexToAut(Reg, A) , auToRex(A, Q).

%TestInput**********************************************************************
%getAn(-Automat) :- vrati prednastaveny automat.
getAn( an(2, 1,[2-1-1], 1, [2]) ).
getAn( an(1, 123,[], 1, [1]) ).
getAn( an(1, 123,[], 1, []) ).
getAn( an(3,2,[1-1-2,2-1-3,2-2-1,3-1-3,3-2-3,3-2-1], 1, [1]) ).
getAn( an(7,1,[1-1-2,2-1-3,3-1-4,4-1-5,5-1-6,6-1-7,7-1-5], 1, [2,4,6]) ).
getAn( an(3,2,[1-1-1, 1-2-2, 2-2-2, 2-1-3, 3-2-2, 3-1-1], 1, [2,3]) ).
getAn( an(3,2,[1-2-1,1-1-2,2-1-2,2-2-3,3-1-3,3-2-3], 1, [3]) ).
getAn( an(2,2,[1-1-1,1-2-2,2-1-1,2-2-2], 1, [2]) ).
getAn( an(3,2,[1-1-2,2-1-2,2-2-2,3-1-2,3-2-2,3-2-1], 1, [2]) ).

getReg( lambda).
getReg( lambda*).
getReg( 1*).
getReg( 1* + 2).
getReg( 1* + 2*).
getReg((1+2)`(1+2)*).
getReg((1`(1+2)*)+2`(1+2)*).
getReg( (((1`2+3)*)`1`((2`3)*) + 2)* ).
getReg( 1+2*).
getReg( (1`2 + 3)*).

