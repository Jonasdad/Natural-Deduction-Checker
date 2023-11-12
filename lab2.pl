%indata i format ([Premiss],Slutsats,[[radnr,sats,regel]]).
%goal 1 test([p],p,[[1,p,premiss]]).
%goal 2, OR elimination verify(and(a,b),b,).

verify(InputFileName) :- see(InputFileName), read(Prems), read(Goal), read(Proof), seen, valid_proof(Prems, Goal, Proof).

%validproof([Prem|Rest],Goal,[[,X,premise]|Next]):- member(X,Prems), valid_proof(Rest,Goal, Next). %check if premise is in prems
%valid_proof(Prems, Goal, [[Proof]|[]]):- nth0(1,last(Proof,Goal),Goal). %check if last element in proof is goal
getLast([A],A).
getLast([_|Tail], A):-getLast(Tail,A).

find(Expr, [Expr]).
find(Expr, [Head|Tail]):-find(Expr, Tail).

valid_proof(Prems, Goal, Proof):- getLast(Proof, Last), nth0(1,Last,Goal), validproof(Prems, Goal, Proof, Proof).
validproof(Prems, Goal,Proof, []).

%PREMISE
validproof(Prems, Goal, Proof,[[_,X,premise]|Next]):-!, find(X,Prems), write('added premise'), validproof(Prems, Goal, Proof,Next).

%ANDEL1
validproof(Prems, Goal,Proof, [[_,X,andel1(Num)|Next]]):- !,find((Num, (and(X,_)), _), Proof) ,validproof(Prems, Goal, Proof,Next).

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