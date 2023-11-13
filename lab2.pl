:-discontiguous(validproof/4).
verify(InputFileName) :- see(InputFileName), read(Prems), read(Goal), read(Proof), seen, valid_proof(Prems, Goal, Proof).

getLast([A],A).
getLast([_|Tail], A):-getLast(Tail,A).

find(X, [X|_]).
find(X, [_|Tail]):-find(X,Tail).


valid_proof(Prems, Goal, Proof):- getLast(Proof, Last), nth0(1,Last,Goal),!, validproof(Prems, Goal, Proof, List).
validproof(Prems, Goal,[], List):-!.

%ASSUMPTION

validproof(Prems, Goal, [[[LineNr, X, assumption]|Next]|Rest], List):-append(List, [[LineNr, X, assumption]], NewList),!,
                                                                      write('Box Found.'),nl,
                                                                      write('next:'),nl,
                                                                      write(Next),nl,
                                                                      write('rest:'),nl,
                                                                      write(Rest),nl,
                                                                      validproof(Prems, Goal, Next, NewList),
                                                                      append(NewList, List, FinalList),
                                                                      validproof(Prems, Goal, Rest, FinalList).
                                                                      
%NEGINT
validproof(Prems, Goal, [[LineNr, neg(X), negint(Num1, Num2)]|Next], List):-find([Num1, X, _], List),
                                                                            find([Num2, cont, _], List),
                                                                            append(List, [[LineNr, neg(X), negint(Num1, Num2)]], NewList),!,
                                                                            write(NewList),nl,
                                                                            validproof(Prems, Goal, Next, NewList).
%IMPINT
%PREMISE
validproof(Prems, Goal, [[Num,X,premise]|Next], List):- find(X,Prems), 
                                                        append(List, [[Num,X,premise]], NewList),!,
                                                        write(NewList),nl,
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
%ORINT1
validproof(Prems,Goal,[[LineNr,X,orint1(Num)]|Next],List):-or(A,B)=X,find([Num, A, _], List), 
                                                        append(List, [[LineNr, X, orint1(Num)]], NewList),!,
                                                        write(NewList),nl,
                                                        validproof(Prems, Goal, Next, NewList).
%ORINT2
validproof(Prems,Goal,[[LineNr,X,orint2(Num)]|Next],List):-or(A,B)=X,find([Num, B, _], List), 
                                                        append(List, [[LineNr, X, orint2(Num)]], NewList),!,
                                                        write(NewList),nl,
                                                        validproof(Prems, Goal, Next, NewList).
%ANDINT
validproof(Prems,Goal,[[LineNr,X,andint(Num1,Num2)]|Next],List):-and(A,B)=X,find([Num1, A, _], List),
                                                                  find([Num2, B, _], List),
                                                                  append(List, [[LineNr, X,Y, andint(Num1,Num2)]], NewList),!,
                                                                  write(NewList),nl,
                                                                  validproof(Prems, Goal, Next, NewList).
%IMPEL
validproof(Prems, Goal, [[LineNr, X, impel(Num1, Num2)]|Next], List):-find([Num1, imp(Y, X), _], List),
                                                                      find([Num2, Y, _], List),
                                                                      append(List, [[LineNr, X, impel(Num1, Num2)]], NewList),!,
                                                                      write(NewList),nl,
                                                                      validproof(Prems, Goal, Next, NewList).
%NEGEL
validproof(Prems, Goal, [[LineNr, cont, negel(Num1, Num2)]|Next], List):-find([Num1, X, _], List),
                                                                    find([Num2, neg(X), _], List),
                                                                    append(List, [[LineNr, cont, negel(Num1, Num2)]], NewList),!,
                                                                    write(NewList),nl,
                                                                    validproof(Prems, Goal, Next, NewList).
%CONTEL
validproof(Prems, Goal, [[LineNr, X, contel(Num)]|Next], List):-find([Num, cont, _], List),
                                                                append(List, [[LineNr, X, contel(Num)]], NewList),!,
                                                                write(NewList),nl,
                                                                validproof(Prems, Goal, Next, NewList).
%COPY
validproof(Prems, Goal, [[LineNr, X, copy(Num)]|Next], List):-find([Num, X, _], List),
                                                              append(List, [[LineNr, X, copy(Num)]], NewList),!,
                                                              write(NewList),nl,
                                                              validproof(Prems, Goal, Next, NewList).
%NEGNEGEL
validproof(Prems, Goal, [[LineNr, X, negnegel(Num)]|Next], List):-find([Num, neg(neg(X)), _], List),
                                                                append(List, [[LineNr, X, negnegel(Num)]], NewList),!,
                                                                write(NewList),nl,
                                                                validproof(Prems, Goal, Next, NewList).
%LEM - Fråga om detta behöver verifieras.
validproof(Prems, Goal, [[LineNr, or(X, neg(X)), lem]|Next], List):-append(List, [[LineNr, X, lem]], NewList),!,
                                                                    write(NewList),nl,
                                                                    validproof(Prems, Goal, Next, NewList).
%MT
validproof(Prems, Goal, [[LineNr, neg(X), mt(Num1, Num2)]|Next], List):-find([Num1, imp(X, Y), _], List),
                                                                        find([Num2, neg(Y), _], List),
                                                                        append(List, [[LineNr, X, neg(X), mt(Num1, Num2)]], NewList),!,
                                                                        write(NewList),nl,
                                                                        validproof(Prems, Goal, Next, NewList).
%OREL



%PBC
