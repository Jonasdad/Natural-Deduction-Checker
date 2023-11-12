%indata i format ([Premiss],Slutsats,[[radnr,sats,regel]]).
%goal 1 test([p],p,[[1,p,premiss]]).
%goal 2, OR elimination verify(and(a,b),b,).
:-discontiguous(validproof/4).
verify(InputFileName) :- see(InputFileName), read(Prems), read(Goal), read(Proof), seen, valid_proof(Prems, Goal, Proof).

getLast([A],A).
getLast([_|Tail], A):-getLast(Tail,A).

find(X, [X|_]).
find(X, [_|Tail]):-find(X,Tail).

valid_proof(Prems, Goal, Proof):- getLast(Proof, Last), nth0(1,Last,Goal),!, validproof(Prems, Goal, Proof, List).
validproof(Prems, Goal,[], List):-!.

%PREMISE
validproof(Prems, Goal, [[Num,X,premise]|Next], List):- find(X,Prems), 
                                                        append(List, [[Num,X,premise]], NewList),!,
                                                        write(NewList),nl,
                                                        write('Trying to call validproof again'),nl,
                                                        write('Prems is: '),write(Prems),nl,
                                                        write('Goal is: '),write(Goal),nl,
                                                        write('NewList is: '),write(NewList),nl,
                                                        write('Next is: '),write(Next),nl,
                                                        write('validproof('),write(Prems),write(','),write(Goal),write(','),write(Next),write(','),write(NewList),write(')'),nl,
                                                        validproof(Prems, Goal, Next, NewList).

%ANDEL1
validproof(Prems,Goal,[[LineNr,X,andel1(Num)]|Next],List):-find([Num, and(X,_), _], List), 
                                                        append(List, [[LineNr, X, andel1(Num)]], NewList),!,
                                                        write(NewList),nl,
                                                        validproof(Prems, Goal, Next, NewList).
%ANDEL2
validproof(Prems,Goal,[[LineNr,X,andel2(Num)]|Next],List):-find([Num, and(_,X), _], List), 
                                                        append(List, [[LineNr, X, andel2(Num)]], NewList),!,
                                                        write(NewList),nl,
                                                        validproof(Prems, Goal, Next, NewList).
%OREL

%IMPEL
%validproof(_,[_,X,impel(Num1,Num2)],[Num1, Y, _],[Num2, Z, _]):-impel_valid(Num1,Num2,X,Y,Z).
%NEGEL

%NEGNEGEL

%ANDINT

%ORINT1

%ORINT2

%IMPINT

%NEGINT

%MT

%PBC

%LEM